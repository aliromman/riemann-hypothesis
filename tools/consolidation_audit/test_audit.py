import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent


class ConsolidationAuditTest(unittest.TestCase):
    def test_compiled_capture_alias_private_name_and_missing_artifact(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            before, after = root / 'before', root / 'after'
            before.mkdir()
            source = before / 'src/Fixture'
            source.mkdir(parents=True)
            (before / '.gitignore').write_text('/.lake/\n')
            (before / 'lakefile.toml').write_text('name = "audit_fixture"\nsrcDir = "src"\n[[lean_lib]]\nname = "Fixture"\nglobs = ["Fixture.+"]\n')
            toolchain = os.environ.get('AUDIT_TEST_TOOLCHAIN', 'leanprover/lean4:v4.36.0')
            (before / 'lean-toolchain').write_text(toolchain + '\n')
            (source / 'Base.lean').write_text('''module
@[expose] public section
namespace AuditExample

theorem left : True := True.intro
theorem right : True := True.intro
abbrev IsTrue := True
theorem chooseProof (x _ : True) : True := x
def one : Nat := 1
def two : Nat := 2
end AuditExample
''')
            (source / 'Removed.lean').write_text('''module
public import Fixture.Base
@[expose] public section

def AuditExample.otherExport : Nat := 22
theorem _root_.AuditExample.wrapper : AuditExample.IsTrue := by
  exact AuditExample.left
''')
            (source / 'Middle.lean').write_text('''module
public import Fixture.Removed
@[expose] public section
def AuditExample.chainExport : Nat := 23
theorem _root_.AuditExample.middle : AuditExample.IsTrue := by
  exact AuditExample.wrapper
''')
            body = '''namespace AuditExample
private theorem secret : True := left
theorem usesPrivate : True := secret
theorem usesAlias : True := middle
theorem switched : True := left
theorem sameReferenceSet : True := chooseProof left right
def value : Nat := one
def argument (x : Nat) : Nat := x
end AuditExample
'''
            (source / 'Member.lean').write_text('module\npublic import Fixture.Middle\n@[expose] public section\n' + body)

            def run(cwd, *args, check=True):
                result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
                if check and result.returncode:
                    self.fail(f'{args}: {result.stdout}{result.stderr}')
                return result

            run(before, 'git', 'init', '-q')
            run(before, 'git', 'add', '.')
            def commit(cwd):
                run(cwd, 'git', '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.invalid',
                    'commit', '-qm', 'fixture')
                return run(cwd, 'git', 'rev-parse', 'HEAD').stdout.strip()
            base = commit(before)
            run(before, 'lake', 'build', 'Fixture')
            run(root, 'git', 'clone', '-q', str(before), str(after))
            current = after / 'src/Fixture'
            (current / 'Removed.lean').unlink()
            (current / 'Middle.lean').unlink()
            (current / 'Member.lean').unlink()
            changes = body.replace(':= middle', ':= left').replace('switched : True := left', 'switched : True := right')
            changes = changes.replace('chooseProof left right', 'chooseProof right left').replace(':= one', ':= two')
            changes = changes.replace('argument (x : Nat)', 'argument {x : Nat}')
            (current / 'Bundle.lean').write_text('module\npublic import Fixture.Base\n@[expose] public section\n-- bundled from Fixture.Member\nsection\n' + changes + 'end\n')
            run(after, 'git', 'add', '-A')
            head = commit(after)
            run(after, 'lake', 'build', 'Fixture')
            command = [sys.executable, str(HERE / 'audit.py'), '--before', str(before), '--after', str(after),
                       '--base', base, '--head', head]
            if worker := os.environ.get('AUDIT_WORKER'):
                command.extend(['--worker', worker])

            report = root / 'report'
            result = run(after, *command, '--out', str(report), check=False)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            summary = json.loads((report / 'summary.json').read_text())
            self.assertEqual((summary['compared'], summary['pending'], summary['unverifiedSubstitutions']), (2, 0, 0))
            self.assertEqual(summary['otherRemovedPublicNames'], 2)
            self.assertEqual(summary['exportsWithoutDestination'], 0)
            aliases = {r['name']: r for r in map(json.loads, (report / 'removed-declarations.jsonl').read_text().splitlines())}
            self.assertEqual(aliases['AuditExample.wrapper']['event'], 'conversion-required')
            self.assertEqual(aliases['AuditExample.middle']['event'], 'alias')
            self.assertEqual((report / 'substitutions.tsv').read_text().splitlines(),
                             ['AuditExample.middle\tAuditExample.left', 'AuditExample.wrapper\tAuditExample.left'])
            self.assertTrue((report / 'conversions/ConsolidationWitness0.olean').is_file())
            differences = [(row['declaration'], row['field']) for row in map(json.loads, (report / 'comparisons.jsonl').read_text().splitlines()) if row['event'] == 'difference']
            for pair in [('switched', 'body-references'), ('sameReferenceSet', 'proof-term'),
                         ('value', 'body'), ('argument', 'type'), ('otherExport', 'missing-declaration'),
                         ('chainExport', 'missing-declaration')]:
                self.assertIn(('AuditExample.' + pair[0], pair[1]), differences)
            self.assertNotIn(('AuditExample.sameReferenceSet', 'body-references'), differences)
            self.assertFalse(any(name.endswith(('usesAlias', 'usesPrivate', 'secret')) for name, _ in differences))

            (after / '.lake/build/lib/lean/Fixture/Bundle.olean.private').write_bytes(b'invalid artifact')
            damaged = root / 'damaged'
            result = run(after, *command, '--out', str(damaged), check=False)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertEqual((damaged / 'pending-targets.txt').read_text(), 'Fixture.Bundle\n')

            with (current / 'Base.lean').open('a') as out:
                out.write('def AuditExample.otherExport : Nat := 22\ndef AuditExample.chainExport : Nat := 23\n')
            (current / 'Bundle.lean').write_text((current / 'Bundle.lean').read_text().replace(changes, body.replace(':= middle', ':= left')))
            run(after, 'git', 'add', '-A')
            fixed = commit(after)
            run(after, 'lake', 'build', 'Fixture')
            command[command.index('--head') + 1] = fixed
            clean = root / 'clean'
            result = run(after, *command, '--out', str(clean))
            final = json.loads((clean / 'summary.json').read_text())
            self.assertEqual((final['compared'], final['pending'], final['withFindings']), (2, 0, 0))


if __name__ == '__main__':
    unittest.main()
