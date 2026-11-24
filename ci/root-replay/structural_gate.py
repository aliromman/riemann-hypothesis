"""Check exact native rows for the structural clump refactor."""
from collections import defaultdict
import json
from pathlib import Path
import re

from current_reuse import GRAPH, MANIFEST, SCREENED, TREE
from manifest import FACETS, SHA256, sha
from native import git
from native_artifacts import CHECKER, COMPILER, read_group
from prepare import stripped

MODE = 'clump-scopes'
WORKFLOW = '.github/workflows/fork-structural-check.yml'
FUSION_BLANK_TRIAL = '0f6ae68c01e2367dabdb858c0106626ae9fabb4e91ca1106797458eefda2439b'
FUSION_BLANK_PRODUCTION = '7432b368d339b0e775698a0a6672472ed1dc2400a703ce11f1bf1eebabfa3c4f'
REVIEWED = 'd27f71347abceb76cd37dc8a5fccbe556ec2be90'
WORKER = '16edfc6e7902ab0eed9b4cbb143807d4561fb47052f6ec69ae26ab0e3a71e12f'
RUNNER = '6fe6cfbf9d8d186a81fdafb3e034a9fc830f84a2cfeed2d5400c1c9424ff9d26'
REPAIR_WORKER = 'b987f66ad297de8a9210cd7e1c9e7e73c546b62655fdcc3668da24fa7b648c22'
REPAIR_RUNNER = '74a6311978e07e3a98cb2e0a2adc682c72cd9e1fae1301db7007d5cc1b12b52d'
ORDINARY = ('.olean', '.ir.sig', '.ir')
TOOLS = {'scripts/clump.py', 'scripts/test_clump_scopes.py'}
MARK = b'\n-- This file was produced by scripts/clump.py from the modules listed below.\n'
IMPORT = re.compile(rb'(?:(?:public|private|meta) )*import (?:all )?\S+')


def import_header(data):
    lines = data.splitlines(keepends=True)
    depth = last = 0
    modern = False
    for i, line in enumerate(lines):
        code, depth = stripped(line.decode(), depth)
        if not code:
            continue
        if code == 'module':
            modern = True
        elif code != 'prelude' and not IMPORT.fullmatch(code.encode()):
            break
        last = i + 1
    if not modern:
        raise ValueError('expected an explicit Lean module')
    return b''.join(lines[:last])


def header(old, candidate):
    before, mark, _ = old.partition(MARK)
    after, mark2, _ = candidate.partition(MARK)
    if not mark or mark2 != mark or before != after or import_header(old) != import_header(candidate):
        raise ValueError('the actual clump source import header or original preamble changed')


def tooling(repo, parent, head, paths):
    if paths - TOOLS or 'scripts/clump.py' not in paths:
        raise ValueError('the structural refactor has an unrecognized tooling change')
    data = {}
    for path in sorted(paths):
        sides = []
        for rev in (parent, head):
            row = git(repo, 'ls-tree', '-z', rev, '--', path)
            if not row:
                sides.append(None)
                continue
            meta, name = row.rstrip(b'\0').split(b'\t')
            mode, object_type, oid = meta.split()
            if name.decode() != path or object_type != b'blob' or mode not in (b'100644', b'100755'):
                raise ValueError('the changed clump tool is not a regular file')
            sides.append({'mode': mode.decode(), 'blob': oid.decode(), 'sha256': sha(git(repo, 'cat-file', 'blob', oid.decode()))})
        if sides[1] is None:
            raise ValueError('a structural clump tool was removed')
        data[path] = sides
    return data


def group(report, raw, ref, trial):
    digest = sha(raw)
    scope, helpers = report['scope'], report['helpers']
    if (scope['parent'], scope['donor'], scope['tree'], scope['manifest'], scope['graph'],
        scope['source_manifest_sha256'], scope['group']) != (REVIEWED, SCREENED, TREE, MANIFEST, GRAPH, trial, ref['group']):
        raise ValueError('the structural native report does not have the reviewed inputs')
    engine = helpers['check.py'], helpers['run.py']
    if engine not in ((WORKER, RUNNER), (REPAIR_WORKER, REPAIR_RUNNER)) or helpers['CheckInterface.lean'] != CHECKER:
        raise ValueError('the structural worker or exact declaration checker changed')
    if scope.get('input_mode'):
        if (scope['input_mode'] != 'exact-source-bytes' or engine != (REPAIR_WORKER, REPAIR_RUNNER) or
                scope['production_source_manifest_sha256'] != ref['production_source_manifest_sha256']):
            raise ValueError('the exact-source correction lacks its verified producer and production trial')
    if COMPILER not in report['compiler'] or report['workflow_sha'] != ref['workflow_sha'] or report['result_sha'] != digest:
        raise ValueError('the structural compiler or native results disagree')
    parsed = [json.loads(line) for line in raw.splitlines()]
    by_name = {r['module']: r for r in parsed}
    if len(by_name) != len(parsed) or len(parsed) != report['checked']:
        raise ValueError('the structural result table is incomplete or has duplicate rows')
    return by_name


def accepted(row):
    if row['status'] != 'pass':
        return False
    original, candidate = row['parent_facets'], row['facets']
    warning = row['old_warning_sha256']
    if (set(original) != FACETS or set(candidate) != FACETS or
        any(not SHA256.fullmatch(d) for d in [*original.values(), *candidate.values(), row['parent_ltar_sha256'], warning]) or
        row['kernelImage'] is not True or row['publicImage'] is not True or row['publicImports'] is not True or
        row['different'] != 0 or row['proofChanges'] != 0 or type(row['parentNames']) is not int or
        row['parentNames'] != row['candidateNames'] or row['old_warnings'] != row['new_warnings'] or
        warning != row['new_warning_sha256'] or row['import_all_or_meta_consumer'] is not False or
        any(original[suffix] != candidate[suffix] for suffix in ORDINARY) or
        set(row['raw_different']) != {k for k in original if original[k] != candidate[k]}):
        raise ValueError('inconsistent structural source certification: ' + row['module'])
    return True


def receipt(row, digest):
    if not accepted(row):
        raise ValueError('the selected structural compiler result failed: ' + row['module'])
    return {'module': row['module'], 'kind': 'fresh', 'parent': TREE, 'origin': digest,
            'parent_source': row['source'], 'head_source': row['candidate'], 'facets': row['facets'],
            'parent_blob': row['parent_blob'], 'candidate_blob': row['candidate_blob'],
            'parent_facets': row['parent_facets'], 'parent_ltar_sha256': row['parent_ltar_sha256'],
            'local_declarations': row['parentNames'], 'warning_sha256': row['old_warning_sha256']}


def check_actions(req, inputs):
    wanted = defaultdict(dict)
    for name, row in inputs.items():
        if row['kind'] != 'fresh':
            raise ValueError('structural candidates require a native compilation for their exact source')
        wanted[row['origin']][name] = row
    refs = req.get('native_artifacts', {})
    if refs.keys() != wanted.keys():
        raise ValueError('structural selection contains an unsigned native result table')
    for digest, ref in refs.items():
        raw, report = read_group(ref, 'structural-native', WORKFLOW)
        if sha(raw) != digest:
            raise ValueError('published structural native table differs from the expected digest')
        rows = group(report, raw, ref, ref['source_trial_sha256'])
        for name, expected in wanted[digest].items():
            if name in req.get('fusion_refinements', {}) and (
                ref['source_trial_sha256'] != FUSION_BLANK_TRIAL or
                ref.get('production_source_manifest_sha256') != FUSION_BLANK_PRODUCTION or
                report['scope'].get('input_mode') != 'exact-source-bytes'
            ):
                raise ValueError('the refined source lacks its original exact-source native trial: ' + name)
            if receipt(rows[name], digest) != expected:
                raise ValueError('structural source, declaration or artifact differs from its original native record: ' + name)
    return {'actions_structural_rows': len(inputs), 'actions_artifacts': len(refs)}
