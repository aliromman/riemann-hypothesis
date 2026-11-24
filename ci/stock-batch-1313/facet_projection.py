"""Check real stock outputs against the signed parent with the new private import header."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


def sha(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def main():
    work = Path(sys.argv[1]).resolve()
    suite = Path(__file__).resolve().parent
    panel = json.loads((suite / 'panel.json').read_bytes())
    original = json.loads((work / 'parent-facets.json').read_bytes())
    source_root = Path.cwd()
    trusted = source_root.parent / 'parent'
    facets = ('.olean', '.ir.sig', '.ir')
    result = {}
    with tempfile.TemporaryDirectory(dir=work) as scratch:
        scratch = Path(scratch)
        names = sorted(panel['changed_sources'])
        for offset in range(0, len(names), 24):
            specs = []
            headers = []
            for name in names[offset:offset+24]:
                rel = Path(*name.split('.'))
                before, after = [(root/'src'/rel).with_suffix('.lean') for root in (trusted, source_root)]
                declared = panel['changed_sources'][name]
                if (sha(before), sha(after)) != (declared['parent'], declared['candidate']):
                    raise ValueError('unexpected sources for ' + name)
                old, new = (p.read_bytes().splitlines(keepends=True) for p in (before, after))
                removed, added = [], []
                for op, i, j, lo, hi in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
                    if op != 'equal':
                        removed.extend(old[i:j]); added.extend(new[lo:hi])
                if (not removed or (len(removed), len(added)) != (declared['removed_imports'], declared['added_imports'])
                        or any(not re.fullmatch(rb"import Mathlib\.[\w.']+\n", item) for item in removed + added)):
                    raise ValueError('unexpected changed source lines for ' + name)
                inputs = [work/'parent'/(name+ext) for ext in facets]
                outputs = [scratch/(name+ext) for ext in facets]
                actual = [(source_root/'.lake/build/lib/lean'/rel).with_suffix(ext) for ext in facets]
                for ext, src in zip(facets, inputs):
                    if sha(src) != original[name][ext]:
                        raise ValueError('the parent input bytes changed in ' + name + ext)
                spec = [name, inputs[0], before, after, outputs[0], inputs[1], inputs[2], outputs[1], outputs[2]]
                specs.append('\t'.join(map(str, spec)))
                headers.append('\t'.join(map(str, [*spec, *actual[1:]])))
                result[name] = dict(source_sha256={'parent':declared['parent'], 'candidate':declared['candidate']},
                                    removed=[s[7:-1].decode() for s in removed], added=[s[7:-1].decode() for s in added],
                                    parent_sha256={s:sha(p) for s,p in zip(facets,inputs)},
                                    parent_bytes={s:p.stat().st_size for s,p in zip(facets,inputs)},
                                    actual_sha256={s:sha(p) for s,p in zip(facets,actual)},
                                    actual_bytes={s:p.stat().st_size for s,p in zip(facets,actual)})
            spec_path = scratch/'project.tsv'
            spec_path.write_text('\n'.join(specs)+'\n')
            subprocess.run([work/'build-public', spec_path], check=True)
            header_path = scratch/'headers.tsv'
            header_path.write_text('\n'.join(headers)+'\n')
            raw = subprocess.check_output([work/'ir-headers', header_path])
            observed = {record['module']:record['parts'] for line in raw.splitlines() if (record:=json.loads(line))}
            if set(observed) != set(names[offset:offset+24]):
                raise ValueError('missing direct IR-header observations')
            for name in names[offset:offset+24]:
                row = result[name]
                row['ir_headers'] = observed[name]
                row['expected_sha256'] = {ext:sha(scratch/(name+ext)) for ext in facets}
                row['expected_bytes'] = {ext:(scratch/(name+ext)).stat().st_size for ext in facets}
                if row['expected_sha256'] != row['actual_sha256'] or row['expected_bytes'] != row['actual_bytes']:
                    raise ValueError('a stock output differs from the fully reserialized parent payload for ' + name)
    (work/'import-projection.json').write_text(json.dumps(result, separators=(',',':'))+'\n')


if __name__ == '__main__':
    main()
