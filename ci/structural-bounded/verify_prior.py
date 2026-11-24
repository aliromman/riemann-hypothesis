"""Identify which previously measured sources have any changed compiled input in this PR."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import zipfile

here = Path(__file__).resolve().parent


def git(repo, *args):
    return subprocess.check_output(['git', '-C', repo, *args], text=True).strip()


def main():
    candidate, parent, out = (Path(s).resolve() for s in sys.argv[1:])
    panel = json.loads((here / 'panel.json').read_bytes())
    record = panel['timing_predecessor']
    archive = here / record['artifact_path']
    if hashlib.sha256(archive.read_bytes()).hexdigest() != record['sha256']:
        raise ValueError('the permanent original Actions ZIP differs from its digest')
    with zipfile.ZipFile(archive) as payload:
        identity = json.loads(payload.read('pr-source.json'))
        measurements = json.loads(payload.read('benchmark.json'))
        lake = json.loads(payload.read('lake-benchmark.json'))
    if identity['checked_commit'] != record['checked_commit'] or measurements['status'] != lake['status'] or lake['status'] != 'complete':
        raise ValueError('the predecessor proof and timing record does not match')
    if git(parent, 'rev-parse', 'HEAD:src') != identity['parent_source_tree']:
        raise ValueError('the original parent source differs from the current comparison parent')
    git(candidate, 'fetch', '--quiet', '--no-tags', '--filter=tree:0', 'https://github.com/aliromman/riemann-hypothesis.git', identity['checked_commit'])
    files = [x[1:] for x in (here / 'bounded-paths.txt').read_text().splitlines()]
    observed = git(candidate, 'diff', '--name-only', '--no-renames', identity['checked_commit'], 'HEAD', '--', *files)
    changed = {f[4:-5].replace('/', '.') for f in observed.splitlines()}
    if sorted(changed) != sorted(panel['revised_cone_sources']):
        raise ValueError('the exact source changes differ from the declared current revision')
    reader_spec = importlib.util.spec_from_file_location('current_quick', parent / 'scripts/quick-check.py')
    reader = importlib.util.module_from_spec(reader_spec)
    reader_spec.loader.exec_module(reader)
    names = [r['module'] for r in panel['benchmark']]
    if set(names) != set(measurements['modules']):
        raise ValueError('the predeclared timing roots changed')
    affected = [n for n in names if changed.intersection(reader.dependency_closure(candidate, [n]))]
    if set(affected) != set(panel['repeat_timing']):
        raise ValueError('the repeat set omits an affected input or adds an unchanged root')
    lake_affected = sorted(changed.intersection(lake['modules']))
    summary = dict(original=status_record(identity, record), changed_files_in_previous_cone=sorted(changed),
                   repeated=affected, unaffected=[n for n in names if n not in affected],
                   files_changed_in_four_module_stock_workload=lake_affected,
                   original_single_root_timings=measurements['modules'], original_whole_lake_timings=lake['metrics'])
    (out / 'original-timing-scope.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if not k.startswith('original_')}, indent=2))


def status_record(identity, record):
    return dict(checked_commit=identity['checked_commit'], workflow=identity['workflow_head'],
                run=record['run'], artifact_sha256=record['sha256'])


if __name__ == '__main__':
    main()
