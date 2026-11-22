#!/usr/bin/env python3
"""Compare Lean declarations across a wrapper collapse and module consolidation."""

import argparse
import gzip
import hashlib
import itertools
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path

from aliases import prepare
from conversions import check_conversions


def git(root, *args):
    return subprocess.check_output(['git', '-C', root, *args])


def tree(repo, rev):
    modules = {}
    for entry in git(repo, 'ls-tree', '-rz', rev, '--', 'src').split(b'\0'):
        if not entry:
            continue
        fields, path = entry.split(b'\t', 1)
        if path.endswith(b'.lean'):
            name = path.decode()[4:-5].replace('/', '.')
            if name in modules:
                raise ValueError(f'ambiguous module path for {name}')
            modules[name] = (fields.split()[-1].decode(), path.decode())
    return modules


def constituents(repo, rev):
    command = ['git', '-C', repo, 'grep', '-z', '-e', '^-- bundled from ', rev, '--', 'src']
    found = subprocess.run(command, stdout=subprocess.PIPE)
    if found.returncode not in (0, 1):
        found.check_returncode()
    parts = defaultdict(list)
    for row in found.stdout.splitlines():
        path, line = row.split(b'\0', 1)
        name = path.split(b':', 1)[1].decode()[4:-5].replace('/', '.')
        parts[name].append(line.removeprefix(b'-- bundled from ').decode())
    return parts


def published(index, repo, rev):
    if index is None:
        return {}
    with gzip.open(index, 'rt') as rows:
        header = json.loads(next(rows))
        expected = {'source_tree': git(repo, 'rev-parse', rev + ':src').decode().strip(),
                    'toolchain': git(repo, 'show', rev + ':lean-toolchain').decode().strip()}
        for key, path in [('lakefile_sha256', 'lakefile.toml'), ('manifest_sha256', 'lake-manifest.json')]:
            expected[key] = hashlib.sha256(git(repo, 'show', rev + ':' + path)).hexdigest()
        if any(header.get(key) != value for key, value in expected.items()):
            raise ValueError('cache index does not match the revision and build configuration')
        result = {name: dep for name, dep, *_ in map(json.loads, rows)}
        if len(result) != header['modules']:
            raise ValueError('incomplete revision cache index')
        return result


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def make_reader(root, files, hashes, overlay=None):
    @lru_cache(maxsize=16384)
    def read(name):
        blob, relative_source = files[name]
        relative_module = Path(*name.split('.')).with_suffix('.olean')
        obj = root / '.lake/build/lib/lean' / relative_module
        if overlay is not None and (overlay / relative_module.with_suffix('.trace')).is_file():
            obj = overlay / relative_module
        trace = json.loads(obj.with_suffix('.trace').read_bytes())
        outputs = trace['outputs']
        tokens = outputs['o']
        if isinstance(tokens, str):
            tokens = [tokens]
        suffixes = ['.olean', '.olean.server', '.olean.private'] if outputs.get('m') else ['.olean']
        if len(tokens) != len(suffixes) or not all(re.fullmatch('[0-9a-f]{16}' + re.escape(s), t) for t, s in zip(tokens, suffixes)):
            raise ValueError(f'incomplete Lake artifact list for {name}')
        item = {'name': name, 'path': str(obj), 'hashes': [t.split('.')[0] for t in tokens]}
        if name in hashes:
            if hashes[name] != trace['depHash']:
                raise ValueError(f'Lake dependency hash differs from the revision index for {name}')
            return item
        source = root / relative_source
        if not source.is_file() or git_blob(source.read_bytes()) != blob:
            raise ValueError(f'working source differs from the audited revision for {name}')
        candidates = [value for label, value in trace.get('inputs', [])
                      if label == relative_source or label.endswith('/' + relative_source)]
        if len(candidates) != 1 or not isinstance(candidates[0], str):
            raise ValueError(f'no revision-bound source trace for {name}')
        return dict(item, source=str(source), sourceHash=candidates[0])
    return read


def run_worker(command, arguments, inputs, output):
    # Start a new process after each batch so one damaged artifact cannot retain
    # compacted regions for the remainder of a full-tree run.
    chunk = output.with_suffix('.input')
    try:
        with inputs.open() as stream, output.open('w') as results:
            while True:
                rows = list(itertools.islice(stream, 256))
                if not rows:
                    break
                chunk.write_text(''.join(rows))
                subprocess.run([*command, *arguments, str(chunk)], stdout=results, check=True)
    finally:
        chunk.unlink(missing_ok=True)


def certify_deleted(args, old_files, deleted, read_original, output, worker, destinations):
    prepare(args.after, old_files, deleted, read_original, output)
    evidence = output / 'removed-declarations.jsonl'
    run_worker(worker, ['certify'], output / 'alias-pairs.jsonl', evidence)
    records = [json.loads(line) for line in evidence.read_text().splitlines()]
    unpaired = {json.loads(line)['module'] for line in (output / 'unresolved-removals.jsonl').read_text().splitlines()}
    modules = {row['module'] for row in records}
    if len(modules) != len(records) or modules & unpaired or modules | unpaired != deleted:
        raise ValueError('incomplete removal inventory')
    accepted = {row['name'] for row in records if row['event'] == 'alias'}
    conversions = [row for row in records if row['event'] == 'conversion-required']
    if not args.skip_conversion_checks:
        accepted.update(check_conversions(args.before, args.base_overlay, conversions, output))
    aliases = {}
    providers = {}
    by_name = defaultdict(list)
    for row in records:
        if 'name' in row:
            by_name[row['name']].append(row)
    for name, copies in by_name.items():
        if len(copies) != 1 or name not in accepted:
            continue
        current = copies[0]
        visited = {name}
        while current['target'] in by_name:
            target = current['target']
            if target in visited or target not in accepted or len(by_name[target]) != 1:
                break
            visited.add(target)
            current = by_name[target][0]
        else:
            if current['provider'] in destinations:
                aliases[name] = current['target']
                providers[name] = destinations[current['provider']]
    substitutions = output / 'substitutions.tsv'
    substitutions.write_text(''.join(f'{name}\t{target}\n' for name, target in sorted(aliases.items())))
    extras = defaultdict(list)
    for row in records:
        if not row.get('otherPublicNames'):
            continue
        destination = providers.get(row['name'], destinations.get(row['provider']))
        extras[destination].append(dict(read_original(row['module']), selected=row['otherPublicNames']))
    return substitutions, extras, len(deleted) - len(aliases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before', type=Path, required=True, help='checkout with original artifacts')
    parser.add_argument('--after', type=Path, required=True, help='checkout with consolidated artifacts')
    parser.add_argument('--base', required=True, help='original Git revision')
    parser.add_argument('--head', required=True, help='consolidated Git revision')
    parser.add_argument('--base-index', type=Path, help='trusted published modules.jsonl.gz for the original cache')
    parser.add_argument('--head-index', type=Path, help='trusted published modules.jsonl.gz for the new cache')
    parser.add_argument('--base-overlay', type=Path, help='lib/lean directory containing restored original artifacts')
    parser.add_argument('--skip-conversion-checks', action='store_true', help='leave nonstructural wrapper conversions pending')
    parser.add_argument('--targets', type=Path, help='one consolidated module per line; defaults to the full tree')
    parser.add_argument('--out', required=True, type=Path, help='new output directory')
    parser.add_argument('--worker', type=Path, help='native Compare executable; default is lean --run')
    args = parser.parse_args()
    args.before, args.after = args.before.resolve(), args.after.resolve()
    if args.base_overlay is not None:
        args.base_overlay = args.base_overlay.resolve()
    base, head = [git(args.after, 'rev-parse', v + '^{commit}').decode().strip() for v in (args.base, args.head)]
    old, new = tree(args.after, base), tree(args.after, head)
    origins = constituents(args.after, head)
    destinations = {}
    for name in new:
        for origin in origins.get(name, [name] if name in old else []):
            if origin not in old:
                raise ValueError(f'unknown original constituent {origin}')
            if origin in destinations:
                raise ValueError(f'duplicate constituent {origin}')
            destinations[origin] = name
    deleted = set(old) - destinations.keys()
    targets = sorted(new if args.targets is None else set(args.targets.read_text().split()))
    if set(targets) - new.keys():
        raise ValueError('target not tracked in the consolidated revision')
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    scope = {'base': base, 'head': head, 'beforeModules': len(old), 'afterModules': len(new),
             'requested': len(targets), 'oldModulesWithoutConstituent': len(deleted)}
    (output / 'scope.json').write_text(json.dumps(scope, indent=2) + '\n')
    before = make_reader(args.before, old, published(args.base_index, args.after, base), args.base_overlay)
    after = make_reader(args.after, new, published(args.head_index, args.after, head))
    worker = [str(args.worker.resolve())] if args.worker else ['lean', '--run', str(Path(__file__).with_name('Compare.lean'))]
    substitutions, extras, unresolved = certify_deleted(args, old, deleted, before, output, worker, destinations)
    pairs = output / 'pairs.jsonl'
    eligible = set()
    with pairs.open('w') as queue, (output / 'unavailable.jsonl').open('w') as missing:
        for name in targets:
            try:
                current = after(name)
                original = [before(module) for module in origins.get(name, [name] if name in old else [])]
                original.extend(extras.get(name, []))
            except (OSError, ValueError, KeyError) as error:
                print(json.dumps({'module': name, 'reason': str(error)}), file=missing)
                continue
            print(json.dumps({'current': current, 'originals': original}), file=queue)
            eligible.add(name)
    print(f'{len(eligible)} of {len(targets)} requested modules have paired inputs', file=sys.stderr, flush=True)
    raw = output / 'comparisons.jsonl'
    run_worker(worker, ['compare', str(substitutions)], pairs, raw)
    modules, unavailable, fields = {}, set(), Counter()
    with raw.open() as stream:
        for line in stream:
            row = json.loads(line)
            name = row['module']
            if row['event'] == 'module':
                if name in modules:
                    raise ValueError(f'duplicate result for {name}')
                modules[name] = row
            elif row['event'] == 'unavailable':
                unavailable.add(name)
            elif row['event'] == 'difference':
                fields[row['field']] += 1
            else:
                raise ValueError(f'unexpected record: {row}')
    if set(modules) | unavailable != eligible or set(modules) & unavailable:
        raise ValueError('incomplete module comparisons')
    pending = sorted(set(targets) - modules.keys())
    (output / 'pending-targets.txt').write_text(''.join(name + '\n' for name in pending))
    summary = {'requested': len(targets), 'pending': len(pending), 'compared': len(modules),
               'alignedDeclarations': sum(m['aligned'] for m in modules.values()),
               'comparedAxiomSets': sum(m['comparedAxiomSets'] for m in modules.values()),
               'withFindings': sum(m['findings'] > 0 for m in modules.values()), 'fields': dict(fields),
               'removedModules': len(deleted), 'unverifiedSubstitutions': unresolved,
               'otherRemovedPublicNames': sum(len(part['selected']) for group in extras.values() for part in group),
               'exportsWithoutDestination': sum(len(part['selected']) for part in extras.get(None, []))}
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)
    return int(bool(pending or summary['withFindings'] or unresolved or summary['exportsWithoutDestination']))


if __name__ == '__main__':
    sys.exit(main())
