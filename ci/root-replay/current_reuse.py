"""Bind earlier native results to the effective inputs of the current Lean compiler."""
from functools import cache
import gzip
import json
from pathlib import Path
import tempfile
import urllib.request

from native import file_sha, git, tree
from manifest import rows, sha
from prepare import GRAPH as OLD_GRAPH, MANIFEST as OLD_MANIFEST, PARENT as OLD, SOURCE_TREE as OLD_TREE
from prepare import canonical, load
from reuse_gate import source_blobs
from runtime.decode import unpack

HERE = Path(__file__).resolve().parent
SCREENED = '343b1de38bbe4c5c66f1c1c0afd7c34e8645acdf'
TREE = '70327238ca7c4189479eee72f3c22812f1922329'
MANIFEST = '18bf99f19a3357168a83dd5bb70bfb1836134646fb27bac2419611778c15bb2a'
GRAPH = '1eea63e656493b1d5f30ab34bd8b913ab3edadc2d615e2313e471196749941a4'
OLD_CANDIDATE = '4fc7348e335c0c93eece5d0183bfc64f52081b84'
OLD_REQUEST = '6872aac85dcae34dd47b24fb651b13224b36d101'
OLD_BUNDLE = '5d85a0bfcd9c23775d0ebf743b8c660eb0816e4202e8894f834784e59261da8c'
OLD_TABLE = '4c2d2362c890283d4f6f08185c262f87a0830bb1674beeae38c5d51f6d8714f7'
FACETS = ['.olean', '.olean.server', '.ir.sig', '.ir', '.olean.private']
VERIFICATION_INPUTS = ('src', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                       'comparator.json', 'export-targets.txt', '.github/workflows/checks.yml',
                       'scripts/clump.py')
CACHE_HELPERS = ('ci-cache-get.py', 'ci-prepare.py', 'cache-settings.py', 'cache-baselines.json',
                 'publish-ci-cache.py', 'publish-lake-cache.py')


def parent_index(repo, state, api, rev, identity, manifest):
    meta = state / 'metadata'
    meta.mkdir(parents=True, exist_ok=True)

    def read(key, limit):
        path = meta / Path(key).name
        if key.startswith('ci/revisions/') or not path.is_file():
            value = api.fetch(key, limit)
            if value is None:
                raise ValueError('absent official cache metadata: ' + key)
            path.write_bytes(value)
        return path.read_bytes()

    raw = read('ci/revisions/' + rev + '.json', api.MAX_RECEIPT)
    record = api.matching_record(raw, identity)
    commit_tree = git(repo, 'rev-parse', rev + '^{tree}').decode().strip()
    if not record or (record['candidate_head'], record['candidate_tree'], record['module_manifest_sha256']) != (rev, commit_tree, manifest):
        raise ValueError('the official receipt differs from the Git revision or pinned content manifest')
    _, hashes, inventory = api.validated_blobs(record, identity, fetcher=read)
    return {r[0]: r for r in inventory}, hashes


def check_parent_files(repo, req):
    if git(repo, 'rev-parse', 'HEAD').decode().strip() != req['base'] or req['base_src'] != TREE:
        raise ValueError('current parent checkout differs from the source binding')
    git(repo, 'merge-base', '--is-ancestor', SCREENED, req['base'])
    git(repo, 'diff', '--quiet', SCREENED, req['base'], '--', *VERIFICATION_INPUTS)


def vetted_helpers(repo, state):
    folder = state / ('community-cache-tools-' + SCREENED)
    folder.mkdir(parents=True, exist_ok=True)
    for name in CACHE_HELPERS:
        path = folder / name
        source = git(repo, 'show', SCREENED + ':scripts/' + name)
        if not path.is_file() or path.read_bytes() != source:
            path.write_bytes(source)
    return folder


def current_parent(repo, state, req):
    check_parent_files(repo, req)
    api = load(vetted_helpers(repo, state) / 'ci-cache-get.py', 'root_cache')
    identity = api.current_identity(repo)
    if identity['source_tree'] != TREE:
        raise ValueError('current source identity differs')
    index, hashes = parent_index(repo, state, api, req['base'], identity, MANIFEST)
    return api, index, hashes


def historical_rows(state):
    path = state / 'metadata' / (OLD_BUNDLE + '.jsonl.gz')
    if not path.is_file():
        url = ('https://raw.githubusercontent.com/aliromman/riemann-hypothesis/' +
               OLD_REQUEST + '/ci/root-replay/request/native.jsonl.gz')
        with urllib.request.urlopen(url, timeout=120) as response:
            path.write_bytes(response.read(20 << 20))
    packed = path.read_bytes()
    if sha(packed) != OLD_BUNDLE:
        raise ValueError('previous native bundle differs from its published digest')
    data = gzip.decompress(packed)
    if sha(data) != OLD_TABLE:
        raise ValueError('the historical native record table has the wrong digest')
    return rows(data)


def compare_archives(required, old, current, old_shas, new_shas, state, dl, leantar):
    values = {}
    names = sorted(required)
    for offset in range(0, len(names), 16):
        with tempfile.TemporaryDirectory(dir=state) as tmp:
            temp = Path(tmp)
            jobs = []
            batch = names[offset:offset + 16]
            for side, (index, shas) in enumerate(((old, old_shas), (current, new_shas))):
                chosen = [index[n] for n in batch]
                dl.downloads(state, {key: arc for _, key, arc in chosen}, shas)
                for k, (_, key, arc) in enumerate(chosen):
                    source = state / 'artifacts' / arc
                    if source.is_symlink() or file_sha(source) != shas[arc]:
                        raise ValueError('wrong project archive for comparison')
                    folder = temp / f'{side}-{k}'
                    folder.mkdir()
                    jobs.append({'file': str(source), 'hash': key, 'base': [str(folder), str(folder)]})
            unpack(leantar, ['--jobs', '2', '-f', '-x', '-j', '-'], jobs)
            for k, name in enumerate(batch):
                suffixes = FACETS if required[name] else FACETS[:1]
                basename = name.rsplit('.', 1)[-1]
                left, right = ([file_sha(temp / f'{side}-{k}' / (basename + ext)) for ext in suffixes]
                               for side in (0, 1))
                if left != right:
                    raise ValueError('an effective project import differs: ' + name)
                values[name] = left
    return values


def check(repo, state, api, graph, index, shas, reused, head, leantar, dl):
    old_identity = api.current_identity(repo) | {'source_tree': OLD_TREE}
    if tree(repo, OLD) != OLD_TREE:
        raise ValueError('historical source unavailable')
    for path in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        if git(repo, 'show', OLD + ':' + path) != (repo / path).read_bytes():
            raise ValueError('a native compiler or configuration pin changed')
    old, old_shas = parent_index(repo, state, api, OLD, old_identity, OLD_MANIFEST)
    old_graph = graph.copy()
    for n, edges in json.loads((HERE / 'parent-delta.json').read_bytes()).items():
        if edges is None:
            old_graph.pop(n)
        else:
            old_graph[n] = edges
    if sha(canonical(old_graph)) != OLD_GRAPH or old_graph.keys() != old.keys():
        raise ValueError('previous compiler import graph differs')
    if any(meta for g in (old_graph, graph) for edges in g.values() for _, _, meta, _ in edges):
        raise ValueError('the project now has a meta import')
    original, current = source_blobs(repo, OLD), source_blobs(repo, 'HEAD')
    before, after = source_blobs(repo, OLD_CANDIDATE), source_blobs(repo, head)
    history = historical_rows(state)
    required = {}
    seen = set()

    def hashes(n):
        return old_shas[old[n][2]], shas[index[n][2]]

    def require(n, deep):
        if (n, deep) in seen:
            return
        if n not in old or n not in index or old_graph[n] != graph[n]:
            raise ValueError('effective project graph differs: ' + n)
        seen.add((n, deep))
        left, right = hashes(n)
        if left != right:
            required[n] = required.get(n, False) or deep
        for child, public, _, all_ in graph[n]:
            if deep or public:
                require(child, deep and all_)

    for n, record in reused.items():
        prior = history[n]
        if original.get(n) != current[n] or before.get(n) != after[n] or old_graph[n] != graph[n]:
            raise ValueError('the candidate source, owning source or header changed: ' + n)
        if [record[k] for k in ('module', 'parent', 'origin', 'parent_source', 'head_source', 'facets')] != [
            prior[k] for k in ('module', 'parent', 'origin', 'parent_source', 'head_source', 'facets')]:
            raise ValueError('a compiler receipt differs from its historical publication: ' + n)
        if (record['input_via_tree'], record['input_origin_tree'], record['input_origin_kind']) != (OLD_TREE, prior['parent'], prior['kind']):
            raise ValueError('a compiler provenance chain lost its original source tree: ' + n)
        left, right = hashes(n)
        if left != right or record['owner_archives'] != [left, right]:
            raise ValueError('the owning parent archive changed: ' + n)
        for dep, _, _, deep in graph[n]:
            require(dep, deep)
    values = compare_archives(required, old, index, old_shas, shas, state, dl, leantar)

    @cache
    def witness(n, deep):
        left, right = hashes(n)
        facets = [left] if left == right else values[n][:5 if deep else 1]
        children = [witness(dep, deep and all_) for dep, public, _, all_ in graph[n] if deep or public]
        return sha(canonical([n, int(deep), facets, children]))

    for n, record in reused.items():
        ids = [witness(dep, deep) for dep, _, _, deep in graph[n]]
        if sha(canonical(ids)) != record['effective_inputs_sha256']:
            raise ValueError('an effective input witness differs from the transferred result: ' + n)
    return {'roots': len(reused), 'dependencies': len({n for n, _ in seen}),
            'compared_different_archives': len(required), 'private_archive_comparisons': sum(required.values()),
            'previous_native_table': OLD_TABLE, 'previous_source_tree': OLD_TREE}
