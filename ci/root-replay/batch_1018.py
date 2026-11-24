"""Check native results for batch 1018 against signed current inputs and the last two verified PR heads."""
from collections import defaultdict
from functools import cache
import gzip
import io
import json
from pathlib import Path
import urllib.request
import zipfile

from current_reuse import CACHE_HELPERS, VERIFICATION_INPUTS, compare_archives, parent_index
from manifest import rows, sha
from native import git, tree
from native_artifacts import api as github, one_file, read_group
from prepare import canonical, load
from reuse_gate import source_blobs
import refresh

BASE = 'bb9476b875a219608a9068f8f18d8c56b4e7f1ca'
TREE = 'fd6cca42e515165d98659a81ff24b5c84b71ece6'
GRAPH = '35bbb99855f7a28a66fbb2d66d862325e02a630cbae1f341c3263647b7ea2307'
MANIFEST = '79edef3a77b0086faf52d4f0df0a9b26b58e45826de20a57def3d5559d6ebe89'
OLD_BASE = 'cb4dc6e23a6187db392c96664295415c55b6b01e'
OLD_TREE, OLD_GRAPH, OLD_MANIFEST = refresh.TREE, refresh.GRAPH, refresh.MANIFEST
HERE = Path(__file__).resolve().parent
HISTORY = {
    879: {
        'head': 'c2c7fc890448cf0c8eab464f115e5e370129697a',
        'workflow': '8886bf57e48a601d75e7847f794b0340750235b5',
        'request': 'request', 'run': 45382775628, 'artifact': 14916660212,
        'zip': 'ea12fb149e155b1bfa0e56a98f2deb456112d8409eb8d97126a9658d78468710',
        'audit': '483a3943297235b6aa8e79c562d62019e0f9e505da64ca8ce36c967d0a4d128a',
        'evidence': '4ff4a916dea1434b564f83253d729595fcd019d6', 'count': 39137,
        'bundle': '3391b477dbd0c7f8202d8a2a74b5d6d8fc646d4483b22f3bccf00c94bfa4329a',
        'table': '88e45d13dbe699fb9534654a44ba8ea8ee0207c272153041e40a1d5110af69ba',
    },
    977: {
        'head': 'afa44208210943a202ad969173b6317d06c37420',
        'workflow': 'd5f33aadf72f0ec93318a4cd2b0f95413196a304',
        'request': 'structural-request', 'run': 45382937704, 'artifact': 14916130747,
        'zip': '2d7f574672b51af1444bac02b699cb5300d7984435d7adf8d18ccf9326d62f26',
        'audit': 'babcbd1785567fa2964356130bd6ae34bb87c4f8c7726f9bd988debcb733394a',
        'evidence': '5b88a3c949953a5769d22b8c09ba3b8130b26558', 'count': 11579,
        'bundle': '615ecf1ff2468d082eddfecbd1a1273dc6470bce8387f3930df3b65cfa9110fd',
        'table': 'a5c2297a51736c6ce7ecae5178ec9aaf2a1de14679f3293a4045f55479ce2905',
    },
}


def current_inputs(repo, revision):
    git(repo, 'merge-base', '--is-ancestor', BASE, revision)
    git(repo, 'diff', '--quiet', BASE, revision, '--', *VERIFICATION_INPUTS, 'comparator',
        *(f'scripts/{name}' for name in CACHE_HELPERS))
    for path in [name for name in VERIFICATION_INPUTS if name != 'src'] + ['src/Challenge.lean', 'src/Main.lean', 'src/Statements.lean']:
        git(repo, 'diff', '--quiet', OLD_BASE, BASE, '--', path)


def published_parent(repo, state, req):
    if git(repo, 'rev-parse', 'HEAD').decode().strip() != req['base'] or req['base_src'] != TREE:
        raise ValueError('the current stock checkout differs from the reviewed input')
    current_inputs(repo, req['base'])
    api = load(repo / 'scripts/ci-cache-get.py', 'official_current_cache')
    identity = api.current_identity(repo)
    if identity['source_tree'] != TREE:
        raise ValueError('the source identity differs from the new batch')
    index, shas = parent_index(repo, state, api, req['base'], identity, MANIFEST)
    return api, index, shas


def durable(state, commit, path, expected):
    target = state / 'metadata' / expected
    if not target.is_file():
        url = f'https://raw.githubusercontent.com/aliromman/riemann-hypothesis/{commit}/{path}'
        with urllib.request.urlopen(url, timeout=120) as response:
            data = response.read(32 << 20)
        if sha(data) != expected:
            raise ValueError('incorrect published evidence: ' + path)
        target.write_bytes(data)
    data = target.read_bytes()
    if sha(data) != expected:
        raise ValueError('incorrect local copy of the published evidence: ' + path)
    return data


def prior_rows(state, number):
    h = HISTORY[number]
    run = json.loads(github(f'runs/{h["run"]}/attempts/1'))
    workflow = '.github/workflows/fork-' + ('structural-' if number == 977 else '') + 'root-replay.yml'
    if (run['id'], run['head_sha'], run['path'], run['conclusion']) != (h['run'], h['workflow'], workflow, 'success'):
        raise ValueError('the prior complete native and root verification did not pass')
    audit = json.loads(durable(state, h['evidence'], 'verified/five-theorems/audit.json', h['audit']))
    if (audit['run_id'], audit['run_attempt'], audit['workflow_commit'], audit['artifact_id'],
            audit['container_sha256'], audit['source_index_sha256'], audit['checked_pr_head']) != (
            h['run'], 1, h['workflow'], h['artifact'], h['zip'], h['table'], h['head']):
        raise ValueError('the audited original GitHub archive has a different owner or source binding')
    record = durable(state, h['evidence'], f'verified/five-theorems/five-roots-{h["head"]}-1.zip', h['zip'])
    with zipfile.ZipFile(io.BytesIO(record)) as z:
        b = json.loads(one_file(z, 'bound.json'))
        v = json.loads(one_file(z, 'verified.json'))
    if (b['head'], b['parent'], b['parent_source_tree'], b['module_manifest'], b['input_sha256'], b['changed'],
        b['ir_signature_and_body_matches'], v['head'], v['changed'], len(v['kernel_accepted']), v['decls']['proofChanges']) != (
            h['head'], OLD_BASE, OLD_TREE, OLD_MANIFEST, h['table'], h['count'], h['count'], h['head'], h['count'], 5, 0):
        raise ValueError('the preceding complete proof and its native source table disagree')
    packed = durable(state, h['workflow'], f'ci/root-replay/{h["request"]}/native.jsonl.gz', h['bundle'])
    raw = gzip.decompress(packed)
    if sha(raw) != h['table']:
        raise ValueError('the preceding native source table differs')
    return rows(raw)


def transferred(previous, owner, inputs):
    return previous | {'kind': 'reused', 'transfer_1018': {
        'previous_record': sha(canonical(previous)), 'owner': owner, 'effective_inputs_sha256': inputs}}


def transfers(repo, state, api, graph, index, shas, selected, req, leantar, dl):
    number = req['pull_request']
    h = HISTORY[number]
    if req.get('preceding_root') != {'run_id': h['run'], 'run_attempt': 1, 'artifact_id': h['artifact'], 'container_sha256': h['zip']}:
        raise ValueError('the request identifies a different previous original GitHub proof')
    history = prior_rows(state, number)
    old_identity = api.current_identity(repo) | {'source_tree': OLD_TREE}
    if tree(repo, OLD_BASE) != OLD_TREE:
        raise ValueError('the previous complete parent source is unavailable')
    old, old_shas = parent_index(repo, state, api, OLD_BASE, old_identity, OLD_MANIFEST)
    prior_graph = graph.copy()
    for n, edges in json.loads(gzip.decompress((HERE/'preceding-1018-edges.json.gz').read_bytes())).items():
        if edges is None:
            prior_graph.pop(n)
        else:
            prior_graph[n] = edges
    if sha(canonical(prior_graph)) != OLD_GRAPH or prior_graph.keys() != old.keys():
        raise ValueError('the previous full import graph differs from its validated source')
    if any(meta for g in (prior_graph, graph) for edges in g.values() for _,_,meta,_ in edges):
        raise ValueError('the current transfer does not support meta project imports')
    original, current = source_blobs(repo, OLD_BASE), source_blobs(repo, req['base'])
    before, after = source_blobs(repo, HISTORY[number]['head']), source_blobs(repo, req['head'])
    required, visited = {}, set()

    def archives(n):
        return old_shas[old[n][2]], shas[index[n][2]]

    def need(n, deep):
        if (n, deep) in visited:
            return
        if n not in old or n not in index or prior_graph[n] != graph[n]:
            raise ValueError('the loaded project import graph changed: ' + n)
        visited.add((n, deep))
        if len(set(archives(n))) != 1:
            required[n] = required.get(n, False) or deep
        for dep, public, _, all_ in graph[n]:
            if deep or public:
                need(dep, deep and all_)

    for n in selected:
        if n not in history or original.get(n) != current[n] or before.get(n) != after[n] or prior_graph[n] != graph[n]:
            raise ValueError('a transferred owner or candidate source changed: ' + n)
        if len(set(archives(n))) != 1:
            raise ValueError('the transferred owning archive changed: ' + n)
        for dep, _, _, deep in graph[n]:
            need(dep, deep)
    compared = compare_archives(required, old, index, old_shas, shas, state, dl, leantar)

    @cache
    def witness(n, deep):
        a,b = archives(n)
        values = [a] if a == b else compared[n][:5 if deep else 1]
        children = [witness(dep,deep and all_) for dep,public,_,all_ in graph[n] if deep or public]
        return sha(canonical([n,int(deep),values,children]))
    for n, row in selected.items():
        anchor = sha(canonical([witness(dep,deep) for dep,_,_,deep in graph[n]]))
        if row != transferred(history[n], ['archive', archives(n)[1]], anchor):
            raise ValueError('a historical record differs from the actual earlier compiler proof or current inputs: ' + n)
    return {'preceding_proof_run': HISTORY[number]['run'], 'preceding_proof_zip': HISTORY[number]['zip'],
            'transferred': len(selected), 'unique_transferred_imports': len({n for n,_ in visited}),
            'compared_changed_import_archives': len(compared), 'compared_deep_imports': sum(required.values())}


def certify(repo, state, api, graph, index, shas, inputs, req, leantar, dl, mode):
    fresh, kept = defaultdict(dict), {}
    for n,r in inputs.items():
        if r['kind'] == 'fresh':
            fresh[r['origin']][n] = r
        else:
            kept[n] = r
    refs = req.get('native_artifacts', {})
    if refs.keys() != fresh.keys():
        raise ValueError('fresh native references differ from the included results')
    original, candidate = source_blobs(repo, req['base']), source_blobs(repo, req['head'])
    for digest, ref in refs.items():
        raw, report = read_group(ref, 'reviewed-native', refresh.WORKFLOW)
        if sha(raw) != digest:
            raise ValueError('a native group differs from its stated digest')
        group = refresh.current_group(raw,report,ref,mode,authority=(BASE,TREE,GRAPH,MANIFEST))
        for n,row in fresh[digest].items():
            expected = refresh.current_record(group[n],digest,mode,parent=TREE)
            if row != expected or row['parent_ltar_sha256'] != shas[index[n][2]] or (row['parent_blob'],row['candidate_blob']) != (original[n],candidate[n]):
                raise ValueError('a new native row differs from its source, owner or accepted compiler output: ' + n)
    carried = transfers(repo,state,api,graph,index,shas,kept,req,leantar,dl) if kept else {}
    return carried | {'fresh':len(inputs)-len(kept),'new_workflow_artifacts':len(refs)}
