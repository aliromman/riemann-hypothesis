"""Check the actual structural PR with its normal clump reader, writer and focused tests."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
from manifest import read_request, sha
from native import Blobs, file_sha, git, ls

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'import-screen'))
from prepare import load, source_path
from structural_gate import header, tooling

RECIPE = {'context_fusion.py': '322c0ac892bff0bdf808f1ca5b5ee7376bb3d3ee6cef17ab289311ac21fe04ab',
          'compact_scope.py': '9e0f5633f64a44157bc837790d3b21b58c0f098211c00c1590b9a9ea318e7d70'}


def check(req, inputs, parent, candidate, recipe):
    if req.get('source_mode') != 'clump-scopes':
        raise ValueError('unrecognized structural root request')
    base, head = req['base'], req['head']
    if (git(parent, 'rev-parse', 'HEAD').decode().strip(), git(candidate, 'rev-parse', 'HEAD').decode().strip()) != (base, head):
        raise ValueError('the clump tools have a different Git parent or candidate')
    extra = set(req['tooling'])
    if tooling(candidate, base, head, extra) != req['tooling']:
        raise ValueError('incorrect committed normal tool')
    for p in extra:
        left, right = req['tooling'][p]
        if (left is not None and file_sha(parent / p) != left['sha256']) or file_sha(candidate / p) != right['sha256']:
            raise ValueError('the normal clump tool differs from the Git file')
    for name, digest in RECIPE.items():
        if file_sha(recipe / name) != digest:
            raise ValueError('the reference source-level section fusion changed')
    sys.path.insert(0, str(recipe))
    fuse = load(recipe / 'context_fusion.py', 'reference_fusion').fuse
    prior = load(parent / 'scripts/clump.py', 'preceding_clumper')
    proposal = load(candidate / 'scripts/clump.py', 'proposed_clumper')
    old, new = ls(candidate, base), ls(candidate, head)
    reader = Blobs(candidate)
    members = changed_members = original_bytes = 0
    planner_modules = protected_modules = 0
    try:
        selected = {str(source_path(n)) for n in inputs}
        if old.keys() != new.keys():
            raise ValueError('the planning domain changed')
        for path in sorted(old):
            if not path.endswith('.lean'):
                continue
            name = path[4:-5].replace('/', '.')
            original = reader.read(old[path]).decode()
            proposed = original if old[path] == new[path] else reader.read(new[path]).decode()
            before = prior.is_clump_file(prior.Module(name, path, original))
            after = proposal.is_clump_file(proposal.Module(name, path, proposed))
            if before != after or (path in selected and not after):
                raise ValueError('the normal planner changed clump protection: ' + name)
            planner_modules += 1
            protected_modules += int(after)
        for name, row in sorted(inputs.items()):
            path = str(source_path(name))
            a, b = reader.read(old[path]), reader.read(new[path])
            if (sha(a), sha(b)) != (row['parent_source'], row['head_source']):
                raise ValueError('round-trip source hashes differ: ' + name)
            header(a, b)
            original = prior.unclump_text(a.decode())
            restored = proposal.unclump_text(b.decode())
            if original.keys() != restored.keys() or list(original) != list(restored) or not original:
                raise ValueError('the normal unclumper changed member names or order: ' + name)
            modules = {}
            for n, text in original.items():
                parts = prior.Module(n, '', text)
                code, _ = fuse(parts.body.removesuffix('\n').split('\n'))
                expected = parts.header + '\n'.join(code) + ('\n' if parts.body.endswith('\n') else '')
                if restored[n] != expected:
                    raise ValueError('restored member has a change outside the indicated section fusion: ' + n)
                modules[n] = proposal.Module(n, '', restored[n])
                members += 1
                changed_members += int(text != expected)
                original_bytes += len(text.encode())
            mark = proposal.CLUMP_MARK
            rendered = proposal.render(str(candidate), list(original), modules)
            if rendered.partition(mark)[2] != b.decode().partition(mark)[2]:
                raise ValueError('the normal clump renderer does not recreate the exact selected body: ' + name)
    finally:
        reader.close()
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', str(candidate / 'scripts'),
                            '-p', 'test_clump_scopes.py'], capture_output=True, text=True, check=True)
    return {'parent': base, 'head': head, 'source_tree': req['head_src'], 'source_files': len(inputs),
            'members': members, 'member_bodies_with_verified_scope_fusion': changed_members,
            'planner_modules_compared': planner_modules, 'planner_modules_protected': protected_modules,
            'bytes_in_original_member_sources': original_bytes, 'candidate_tools': req['tooling'],
            'focused_test_output': (tests.stdout + tests.stderr).strip()}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for key in ('request', 'parent', 'candidate', 'out'):
        p.add_argument('--' + key, type=Path, required=True)
    p.add_argument('--recipe', type=Path, default=HERE.parent / 'structural-screen/recipe')
    args = p.parse_args()
    req, rows = read_request(args.request)
    record = check(req, rows, args.parent.resolve(), args.candidate.resolve(), args.recipe.resolve())
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record))
