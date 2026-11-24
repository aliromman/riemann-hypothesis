"""Verify source-bound native results across the community batch merged in #896."""
from collections import defaultdict
from functools import cache
import gzip
import io
import json
from pathlib import Path
import urllib.request
import zipfile

from current_reuse import GRAPH as OLD_GRAPH, MANIFEST as OLD_MANIFEST, TREE as OLD_TREE
from current_reuse import SCREENED as OLD_PARENT, VERIFICATION_INPUTS, compare_archives, parent_index, vetted_helpers
from manifest import FACETS, SHA256, rows, sha
from native import git, tree
from native_artifacts import COMPILER, api as github, one_file, read_group
from prepare import canonical, load
from reuse_gate import source_blobs
import structural_gate as structural

BASE = 'c9883164b0b3d762cee21f889d03d59a53b3ba3b'
TREE = '6e972745429bd501b15e5daa9db46c8a9feb85db'
MANIFEST = 'a6cfc0b330c9b2d25551163316b4ae66dbd1b9006439c8f42621c177ec684463'
GRAPH = '48b7623709bb346e3e358747896b17c0e11933018855d0bcd3d461d25dc728f5'
HELPERS = '783e1a86c3f9153e3fbe4e5f77c481460f2b350951ad10d0b814c150a02611a1'
WORKFLOW = '.github/workflows/fork-parent-refresh.yml'
PRIOR_BASE = '64970dc64f26807fe87a1d50514bf9bec905058f'
PRIOR_HEAD = '0f8b7e6fde3d0c8c78425f023539ddddcafd014e'
PRIOR_REQUEST = '9078dbaa7c6b7781a1feb25bc6c18c15d8eb9c7b'
PRIOR_TABLE = '1210b4b4d03478bc433ff6eb906d1170dc7a5b72500c5f9442dec31871477009'
PRIOR_BUNDLE = '744d2a63ea8f407c04a2c989e2f0a3508cbe64d222e21433032557b835468173'
PRIOR_WORKFLOW = 'd0ae1c75be22b5daba75bb8f917780e452247dbc'
HERE = Path(__file__).resolve().parent


def current_checks(original, current):
    """Permit removal of the old submission's manual pin comparison in #1016."""
    if current == original:
        return
    start = original.index(b'          # The toolchain and dependency pins are still')
    end = original.index(b'  # The second Comparator setup')
    if sha(original[start:end]) != '92317093ffcf2ebdc6e2f84f8284838c25ea5acd9303ada292d35aa4371a2bb3' or original[:start] + original[end:] != current:
        raise ValueError('the current proof workflow differs from its reviewed configuration')


def current_inputs(repo, revision):
    git(repo, 'merge-base', '--is-ancestor', BASE, revision)
    checks = '.github/workflows/checks.yml'
    pinned = [path for path in VERIFICATION_INPUTS if path != checks]
    git(repo, 'diff', '--quiet', BASE, revision, '--', *pinned, 'comparator')
    current_checks(git(repo, 'show', BASE + ':' + checks), git(repo, 'show', revision + ':' + checks))


def published_parent(repo, state, req):
    if git(repo, 'rev-parse', 'HEAD').decode().strip() != req['base'] or req['base_src'] != TREE:
        raise ValueError('current checkout differs from its requested parent')
    current_inputs(repo, req['base'])
    api = load(vetted_helpers(repo, state) / 'ci-cache-get.py', 'root_cache')
    identity = api.current_identity(repo)
    if identity['source_tree'] != TREE:
        raise ValueError('current parent source identity changed')
    index, hashes = parent_index(repo, state, api, req['base'], identity, MANIFEST)
    return api, index, hashes


def current_group(raw, report, ref, mode, *, authority=None):
    base, source, graph, manifest = authority or (BASE, TREE, GRAPH, MANIFEST)
    scope = report['scope']
    if (scope['parent'], scope['tree'], scope['donor'], scope['graph'], scope['manifest'], scope['task'], scope['group']) != (
            base, source, base, graph, manifest, mode, ref['group']):
        raise ValueError('fresh native job has a different source or compiler parent')
    if (scope['source_head'], scope['candidate_tree'], scope['source_transitions_sha256']) != (
            ref['source_head'], ref['candidate_tree'], ref['source_transitions_sha256']):
        raise ValueError('fresh native job has different reviewed candidate sources')
    if (sha(canonical(report['helpers'])) != HELPERS or COMPILER not in report['compiler'] or report['workflow_sha'] != ref['workflow_sha'] or
            report['result_sha'] != sha(raw) or report['pending'] != 0):
        raise ValueError('fresh native job has different producer, compiler, digest or coverage')
    parsed = [json.loads(line) for line in raw.splitlines()]
    exact = {r['module']: r for r in parsed}
    if len(parsed) != len(exact) or len(parsed) != report['checked'] or report['checked'] != scope['roots']:
        raise ValueError('native job has duplicate or missing results')
    return exact


def current_record(row, origin, mode, *, parent=TREE):
    if row['status'] != 'pass':
        raise ValueError('selected native result did not pass: ' + row['module'])
    if mode == 'structural':
        return structural.receipt(row, origin) | {'parent': parent}
    digests = [*row['parent_public_ir'].values(), *row['projected_public_ir'].values(),
               *row['facets'].values(), row['parent_ltar_sha256'], row['old_warning_sha256']]
    if (set(row['parent_public_ir']) != set(structural.ORDINARY) or set(row['projected_public_ir']) != set(structural.ORDINARY) or
            set(row['facets']) != FACETS or not all(SHA256.fullmatch(v) for v in digests) or
            row['projection_differences'] or any(row['projected_public_ir'][s] != row['facets'][s] for s in structural.ORDINARY) or
            row['kernelImage'] is not True or row['publicImage'] is not True or row['publicImports'] is not True or
            row['different'] != 0 or row['proofChanges'] != 0 or type(row['parentNames']) is not int or
            row['candidateNames'] != row['parentNames'] or row['old_warnings'] != row['new_warnings'] or
            row['old_warning_sha256'] != row['new_warning_sha256']):
        raise ValueError('native private-import declaration or raw output differences: ' + row['module'])
    return {'module': row['module'], 'kind': 'fresh', 'parent': parent, 'origin': origin,
            'parent_source': row['source'], 'head_source': row['candidate'], 'facets': row['facets'],
            'parent_blob': row['parent_blob'], 'candidate_blob': row['candidate_blob'],
            'parent_ltar_sha256': row['parent_ltar_sha256'], 'parent_public_ir': row['parent_public_ir'],
            'local_declarations': row['parentNames'], 'warning_sha256': row['old_warning_sha256']}


def prior_import_records(state, req):
    """Require the published full previous root check as well as its immutable per-module native table."""
    ref = req['preceding_root']
    run, number, aid = ref['run_id'], ref['run_attempt'], ref['artifact_id']
    job = json.loads(github(f'runs/{run}/attempts/{number}'))
    if (job['id'], job['run_attempt'], job['head_sha'], job['path'], job['conclusion']) != (
            run, number, PRIOR_WORKFLOW, '.github/workflows/fork-root-replay.yml', 'success'):
        raise ValueError('the preceding full source-bound root check did not pass')
    metadata = json.loads(github(f'artifacts/{aid}'))
    digest = ref['container_sha256']
    if (metadata['id'], metadata['name'], metadata['digest'], metadata['workflow_run']['id'], metadata['workflow_run']['head_sha']) != (
            aid, f'five-roots-{PRIOR_HEAD}-{number}', 'sha256:' + digest, run, PRIOR_WORKFLOW):
        raise ValueError('the preceding root archive has another origin or digest')
    content = github(f'artifacts/{aid}/zip')
    if sha(content) != digest:
        raise ValueError('the preceding root archive changed')
    with zipfile.ZipFile(io.BytesIO(content)) as evidence:
        bound = json.loads(one_file(evidence, 'bound.json'))
        passed = json.loads(one_file(evidence, 'verified.json'))
    if (bound['head'], bound['parent'], bound['input_sha256'], bound['changed'], bound['ir_signature_and_body_matches'],
        bound['module_manifest'], passed['head'], passed['changed']) != (PRIOR_HEAD, PRIOR_BASE, PRIOR_TABLE, 40481, 40481,
        OLD_MANIFEST, PRIOR_HEAD, 40481):
        raise ValueError('the passing previous root check and its recorded source evidence disagree')
    p = state / 'metadata' / (PRIOR_BUNDLE + '.jsonl.gz')
    if not p.is_file():
        url = f'https://raw.githubusercontent.com/aliromman/riemann-hypothesis/{PRIOR_REQUEST}/ci/root-replay/request/native.jsonl.gz'
        with urllib.request.urlopen(url, timeout=90) as response:
            p.write_bytes(response.read(24 << 20))
    compressed = p.read_bytes()
    if sha(compressed) != PRIOR_BUNDLE:
        raise ValueError('incorrect preceding native records')
    raw = gzip.decompress(compressed)
    if sha(raw) != PRIOR_TABLE:
        raise ValueError('incorrect preceding native record digest')
    return rows(raw)


def historical_actions(req, selected):
    previous = {}
    by_origin = defaultdict(set)
    for n, row in selected.items():
        by_origin[row['origin']].add(n)
    refs = req['previous_native_artifacts']
    if by_origin.keys() != refs.keys():
        raise ValueError('missing earlier strict structural source report')
    for digest, ref in refs.items():
        raw, report = read_group(ref, 'structural-native', structural.WORKFLOW)
        if sha(raw) != digest:
            raise ValueError('the historical structural result table has a different digest')
        group = structural.group(report, raw, ref, ref['source_trial_sha256'])
        for n in by_origin[digest]:
            previous[n] = structural.receipt(group[n], digest)
            if n in req.get('fusion_refinements', {}) and ref['source_trial_sha256'] != structural.FUSION_BLANK_TRIAL:
                raise ValueError('the historical source includes an unverified clump scope refinement: ' + n)
    return previous


def transferred(old, witness, archive):
    return old | {'kind': 'reused', 'transfer_896': {'previous_record': sha(canonical(old)), 'previous_tree': OLD_TREE,
                  'owner_archive_sha256': archive, 'effective_inputs_sha256': witness}}


def transfers(repo, state, api, graph, index, shas, selected, req, leantar, dl, mode):
    old_identity = api.current_identity(repo) | {'source_tree': OLD_TREE}
    if tree(repo, PRIOR_BASE) != OLD_TREE or tree(repo, OLD_PARENT) != OLD_TREE:
        raise ValueError('previous parent is missing its authenticated source')
    for path in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        git(repo, 'diff', '--quiet', PRIOR_BASE, req['base'], '--', path)
    old, old_sha = parent_index(repo, state, api, PRIOR_BASE, old_identity, OLD_MANIFEST)
    old_graph = graph.copy()
    for n, edges in json.loads(gzip.decompress((HERE / 'preceding-896-edges.json.gz').read_bytes())).items():
        if edges is None:
            old_graph.pop(n)
        else:
            old_graph[n] = edges
    if sha(canonical(old_graph)) != OLD_GRAPH or old_graph.keys() != old.keys():
        raise ValueError('incorrect previous compiler import graph')
    if any(t for g in (graph, old_graph) for edges in g.values() for _, _, t, _ in edges):
        raise ValueError('project contains a meta import')
    sources = source_blobs(repo, PRIOR_BASE)
    current = source_blobs(repo, req['base'])
    candidate = source_blobs(repo, req['head'])
    if mode == 'private':
        history = prior_import_records(state, req)
        before = source_blobs(repo, PRIOR_HEAD)
    else:
        history = historical_actions(req, selected)
        before = {n: r['candidate_blob'] for n,r in history.items()}
    seen = set()
    required = {}

    def archives(n):
        return old_sha[old[n][2]], shas[index[n][2]]

    def visit(n, deep):
        if (n, deep) in seen:
            return
        if n not in old or n not in index or old_graph[n] != graph[n]:
            raise ValueError('an effective source import graph changed: ' + n)
        seen.add((n, deep))
        if len(set(archives(n))) != 1:
            required[n] = required.get(n, False) or deep
        for dep, public, _, all_ in graph[n]:
            if deep or public:
                visit(dep, deep and all_)

    for n in selected:
        if n not in old or n not in index or sources.get(n) != current[n] or before.get(n) != candidate[n] or old_graph[n] != graph[n]:
            raise ValueError('a transferred owner or candidate source changed: ' + n)
        if len(set(archives(n))) != 1:
            raise ValueError('a transferred owning archive changed: ' + n)
        for dep, _, _, deep in graph[n]:
            visit(dep, deep)
    compared = compare_archives(required, old, index, old_sha, shas, state, dl, leantar)

    @cache
    def witness(n, deep):
        a, b = archives(n)
        facets = [a] if a == b else compared[n][:5 if deep else 1]
        children = [witness(dep, deep and all_) for dep, public, _, all_ in graph[n] if deep or public]
        return sha(canonical([n, int(deep), facets, children]))

    for n, current_row in selected.items():
        root = sha(canonical([witness(dep, deep) for dep, _, _, deep in graph[n]]))
        if transferred(history[n], root, archives(n)[0]) != current_row:
            raise ValueError('transferred result differs from its signed source, compiler evidence or inputs: ' + n)
    return {'previous_tree': OLD_TREE, 'transferred': len(selected), 'unique_transferred_imports': len({n for n, _ in seen}),
            'compared_changed_archives': len(compared), 'compared_deep_imports': sum(required.values())}


def certify(repo, state, api, graph, index, shas, inputs, req, leantar, dl, mode):
    fresh = defaultdict(dict)
    retained = {}
    for n, row in inputs.items():
        if row['kind'] == 'fresh':
            fresh[row['origin']][n] = row
        else:
            retained[n] = row
    refs = req.get('native_artifacts', {})
    if refs.keys() != fresh.keys():
        raise ValueError('new native sources and the published group references differ')
    orig = source_blobs(repo, req['base'])
    cand = source_blobs(repo, req['head'])
    for digest, ref in refs.items():
        raw, report = read_group(ref, 'reviewed-native', WORKFLOW)
        if sha(raw) != digest:
            raise ValueError('current native table differs from the GitHub artifact')
        group = current_group(raw, report, ref, mode)
        for n, row in fresh[digest].items():
            checked = current_record(group[n], digest, mode)
            if (checked != row or row['parent_ltar_sha256'] != shas[index[n][2]] or
                (row['parent_blob'], row['candidate_blob']) != (orig[n], cand[n])):
                raise ValueError('new native proof does not match its parent and final candidate: ' + n)
    earlier = transfers(repo, state, api, graph, index, shas, retained, req, leantar, dl, mode) if retained else {}
    return earlier | {'fresh': len(inputs) - len(retained), 'new_workflow_artifacts': len(refs)}
