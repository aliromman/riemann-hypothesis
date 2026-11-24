"""Check the exact inputs of a completed stock Lake and Comparator run on a newer PR."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

FORK = 'https://github.com/aliromman/riemann-hypothesis.git'
UPSTREAM = 'https://github.com/leanprover-community/riemann-hypothesis.git'
PINS = ('.gitattributes', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'comparator.json', 'export-targets.txt')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def git(repo, *args, data=None):
    return subprocess.check_output(['git', '-C', repo, *args], input=data)


def oid(repo, name):
    return git(repo, 'rev-parse', name).decode().strip()


def check(value, expected, description):
    if value != expected:
        raise ValueError(description)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def actions_api(route, *, binary=False):
    result = subprocess.check_output(['gh', 'api', 'repos/aliromman/riemann-hypothesis/actions/' + route])
    return result if binary else json.loads(result)


def verify_run(request):
    run = actions_api(f'runs/{request["run"]}')
    check((run['conclusion'], run['name'], run['head_sha'], run['head_branch'], run['run_attempt']),
          ('success', 'Build structural clumps in stock Lake', request['old_workflow'],
           'ci/clump-scopes/bounded', request['attempt']), 'unexpected completed verification run')
    artifacts = actions_api(f'runs/{request["run"]}/artifacts')['artifacts']
    matches = [a for a in artifacts if a['id'] == request['artifact_id']]
    check(len(matches), 1, 'the immutable verification artifact is unavailable')
    check(matches[0]['digest'], 'sha256:' + request['artifact_sha256'], 'incorrect ZIP digest on GitHub')
    raw = actions_api(f'artifacts/{matches[0]["id"]}/zip', binary=True)
    check(digest(raw), request['artifact_sha256'], 'incorrect downloaded ZIP')
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        def read(name):
            return json.loads(archive.read(name))
        identity, scope, receipt = (read(n) for n in ('pr-source.json', 'report.json', 'receipt.json'))
        theorem = read('scoped-comparator/summary.json')
        check(theorem['status'], 'accepted', 'the external proof check failed')
        check((identity['workflow_head'], scope['candidate_head'], scope['source_tree'], scope['manifest']),
              (run['head_sha'], identity['checked_commit'], identity['parent_source_tree'], request['manifest']),
              'the original source record disagrees with its compiled scope')
        rows = {}
        for line in archive.read('comparisons.tsv').decode().splitlines():
            name, text = line.split('\t', 1)
            row = json.loads(text)
            if (name in rows or not all(row[key] for key in ('kernelImage', 'publicImage', 'publicImports'))
                    or row['parentNames'] != row['candidateNames'] or row['different'] or row['proofChanges']):
                raise ValueError('the original run contains a declaration mismatch')
            rows[name] = row['candidateNames']
        for member in theorem['theorems']:
            check(member['exports']['parent']['sha256'], member['exports']['candidate']['sha256'],
                  'the exported proof data differ')
            check(member['kernels'], {k: 'success' for k in ('Lean default', 'Lean paranoid', 'nanoda')},
                  'an external kernel did not accept a theorem')
        timings = {}
        for key, name in [('compiler', 'benchmark.json'), ('stock_lake', 'lake-benchmark.json')]:
            result = read(name) if name in archive.namelist() else {'status': 'unavailable'}
            timings[key] = {k: result[k] for k in ('status', 'totals', 'metrics') if k in result}
    return identity, scope, receipt, theorem, rows, timings


def verify_archives(root, request, old_receipt):
    check(oid(root, 'HEAD'), request['new_parent'], 'unexpected cache-client revision')
    cache = load_module('official_cache', root / 'scripts/ci-cache-get.py')
    identity = cache.current_identity(root)
    raw = cache.fetch(f'ci/revisions/{request["new_parent"]}.json', cache.MAX_RECEIPT)
    if not raw:
        raise ValueError('the current community parent has no official successful build receipt')
    check(digest(raw), request['new_parent_receipt_sha256'], 'incorrect current official receipt')
    record = cache.matching_record(raw, identity)
    if not record:
        raise ValueError('the official receipt does not cover the declared source and pins')
    check(record['candidate_head'], request['new_parent'], 'the receipt names another commit')
    check(record['module_manifest_sha256'], request['manifest'], 'the parent module manifest changed')
    check(record['input_fingerprint'], old_receipt['input_fingerprint'], 'the official build inputs changed')
    check(record['module_manifest_sha256'], old_receipt['module_manifest_sha256'], 'the official archives changed')
    _, _, manifest = cache.validated_blobs(record, identity)
    return {row[0] for row in manifest}


def worktree(repo, dest, ref, patterns):
    git(repo, 'worktree', 'add', '--quiet', '--no-checkout', dest, ref)
    git(dest, 'sparse-checkout', 'init', '--no-cone')
    git(dest, 'sparse-checkout', 'set', '--no-cone', '--stdin', data=('\n'.join(patterns) + '\n').encode())
    git(dest, 'checkout', '--quiet', '--detach', ref)


def compare_dependencies(repo, tmp, latest_checkout, paths, roots, project_names, expected):
    """Run both versions of the community import reader and closure on each measured source set."""
    previous = tmp / 'comparison-parent'
    current = tmp / 'present-candidate'
    worktree(repo, previous, 'previous', [*paths, '/scripts/'])
    worktree(repo, current, 'current', paths)
    parsers = [load_module('old_quick', previous / 'scripts/quick-check.py'),
               load_module('new_quick', latest_checkout / 'scripts/quick-check.py')]
    observed = None
    for source in (previous, current):
        for parser in parsers:
            check(set(parser.dependency_closure(source, roots, len(expected))), expected,
                  'the actual trusted import reader found a different project closure')
            imports = {name: parser.imports(source / 'src' / (name.replace('.', '/') + '.lean'))
                       for name in sorted(expected)}
            required = {value for edges in imports.values() for value in edges}
            if required & (project_names - expected):
                raise ValueError('a published project dependency is missing from the source checkout')
            if observed is None:
                observed = imports
            else:
                check(imports, observed, 'the ordered project or package imports changed')
    all_imports = {name for values in observed.values() for name in values}
    canonical = json.dumps(observed, sort_keys=True, separators=(',', ':')).encode()
    return dict(ordered_import_lists_sha256=digest(canonical), checked_source_versions=2,
                checked_upstream_readers=2, distinct_external_imports=len(all_imports - project_names))


def verify_published(request, identity, scope, rows, parent_path, project_names):
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory).resolve()
        repo = tmp / 'public.git'
        subprocess.run(['git', 'init', '--quiet', '--bare', repo], check=True)
        git(repo, 'remote', 'add', 'fork', FORK)
        git(repo, 'remote', 'add', 'upstream', UPSTREAM)
        git(repo, 'fetch', '--quiet', '--filter=tree:0', '--no-tags', 'fork',
            request['source_ref'] + ':refs/heads/current', request['old_workflow'] + ':refs/heads/harness',
            identity['checked_commit'] + ':refs/heads/checked')
        git(repo, 'fetch', '--quiet', '--filter=tree:0', '--no-tags', 'upstream',
            'refs/heads/main:refs/heads/live', request['new_parent'] + ':refs/heads/latest',
            identity['comparison_parent'] + ':refs/heads/previous')
        check(oid(repo, 'current'), request['new_head'], 'the public source branch has moved')
        check(oid(repo, 'current:src'), request['new_source_tree'], 'the published source tree differs')
        check(oid(repo, 'checked:src'), identity['source_tree'], 'the measured source tree differs')
        for ref in ('previous', 'latest', 'live'):
            check(oid(repo, ref + ':src'), scope['source_tree'], 'the community source changed in ' + ref)
        check(git(repo, 'merge-base', 'current', 'latest').decode().strip(), request['new_parent'],
              'the candidate does not include the recorded community parent')
        check(git(repo, 'merge-base', 'current', 'checked').decode().strip(), identity['checked_commit'],
              'the previously measured candidate is not an ancestor of the published revision')
        pins = {name: oid(repo, 'checked:' + name) for name in PINS}
        for name, value in pins.items():
            for ref in ('current', 'previous', 'latest', 'live'):
                check(oid(repo, ref + ':' + name), value, f'different {ref} pin {name}')
        prefix = 'harness:ci/structural-bounded/'
        paths = git(repo, 'show', prefix + 'bounded-paths.txt').decode().splitlines()
        path_by_module = {p[5:-5].replace('/', '.'): p[1:] for p in paths}
        check(set(path_by_module), set(rows), 'the immutable job and its published source manifest differ')
        roots = git(repo, 'show', prefix + 'bounded-roots.txt').decode().splitlines()
        check(set(roots), set(scope['roots']), 'different stock-Lake roots')
        changes = git(repo, 'diff', '--name-status', '--no-renames', 'checked', 'current', '--', 'src').decode().splitlines()
        outside = []
        for line in changes:
            kind, path = line.split('\t', 1)
            if kind != 'M' or not path.endswith('.lean') or path in path_by_module.values():
                raise ValueError('a checked source or a project module identity changed: ' + path)
            outside.append(path)
        graph = compare_dependencies(repo, tmp, parent_path, paths, roots, project_names, set(rows))
        if request.get('pull_number'):
            n = request['pull_number']
            git(repo, 'fetch', '--quiet', '--filter=tree:0', '--no-tags', 'upstream', f'refs/pull/{n}/head:refs/heads/pull')
            check(oid(repo, 'pull'), request['new_head'], 'the community PR points to a different source')
        return dict(observed_upstream_main=oid(repo, 'live'), complete_candidate_src=oid(repo, 'current:src'),
                    complete_parent_src=scope['source_tree'], pins=pins, different_source_paths_outside_check=outside,
                    complete_candidate_src_equal=not outside, checked_project_modules=len(rows), dependency_graph=graph)


def main():
    request_file, parent_path, dest = (Path(p).resolve() for p in sys.argv[1:])
    request = json.loads(request_file.read_bytes())
    identity, scope, old_receipt, theorem, rows, timings = verify_run(request)
    project_names = verify_archives(parent_path, request, old_receipt)
    public = verify_published(request, identity, scope, rows, parent_path, project_names)
    result = dict(status='same bounded sources, dependencies and compiler inputs',
                  original_run=request['run'], original_workflow=request['old_workflow'],
                  original_artifact_id=request['artifact_id'], original_artifact_sha256=request['artifact_sha256'],
                  original_candidate=identity['checked_commit'], original_candidate_src=identity['source_tree'],
                  published_source=request['new_head'], previous_parent=identity['comparison_parent'],
                  current_parent=request['new_parent'], official_current_receipt_sha256=request['new_parent_receipt_sha256'],
                  module_manifest=request['manifest'], authenticated_parent_modules=len(project_names),
                  changed_clumps=len(scope['changed']), declaration_instances=sum(rows.values()),
                  theorems={t['theorem']: t['exports']['parent']['sha256'] for t in theorem['theorems']},
                  timings_computed_by_original_run=request['run'], timing=timings, pull_number=request.get('pull_number'), **public)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
