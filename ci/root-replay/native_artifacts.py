"""Check a compiler record against its originating GitHub Actions artifact."""
from collections import defaultdict
from functools import cache
import io
import json
import re
import subprocess
import zipfile

from current_reuse import GRAPH, MANIFEST, SCREENED, TREE
from manifest import sha

REPO = 'aliromman/riemann-hypothesis'
WORKFLOW = '.github/workflows/fork-current-recheck.yml'
COMPILER = '0b77e12952ad39077d80d8bd6b66d601f225c321'
WORKER = 'fa923200a1602046cb971e6dfe7bb35a057d10a1fb1226675043cf9a0c81bff3'
RUNNER = '2f9882c5a4d0233aa26e05072e008131a21527eade137d34ddac0c510e73f88e'
CHECKER = 'd42ab8acf8d953f321c501b0e479f7b92c6ab51484f4fae63f745a57deaa0af3'


def positive(value):
    if type(value) is not int or value <= 0:
        raise ValueError('invalid GitHub run, attempt or artifact ID')
    return value


def api(path):
    return subprocess.check_output(['gh', 'api', 'repos/' + REPO + '/actions/' + path])


def one_file(archive, name):
    matches = [e for e in archive.infolist() if e.filename.rsplit('/', 1)[-1] == name]
    if len(matches) != 1 or matches[0].file_size > (75 << 20):
        raise ValueError('invalid report contents for ' + name)
    return archive.read(matches[0])


@cache
def attempt(run, number):
    return json.loads(api(f'runs/{run}/attempts/{number}'))


def read_group(ref, prefix, workflow):
    run, number, aid = map(positive, (ref['run_id'], ref['run_attempt'], ref['artifact_id']))
    group = ref['group']
    if not re.fullmatch(r'[a-zA-Z0-9_-]+', group):
        raise ValueError('invalid native group')
    job = attempt(run, number)
    if (job['id'], job['run_attempt'], job['head_sha'], job['path']) != (run, number, ref['workflow_sha'], workflow):
        raise ValueError('native compiler workflow revision differs')
    meta = json.loads(api(f'artifacts/{aid}'))
    scope = meta['workflow_run']
    if (meta['id'], meta['name'], meta.get('digest'), scope['id'], scope['head_sha']) != (
            aid, f'{prefix}-{group}-{run}-{number}', 'sha256:' + ref['container_sha256'], run, ref['workflow_sha']):
        raise ValueError('wrong official GitHub artifact name, run or SHA-256')
    data = api(f'artifacts/{aid}/zip')
    if sha(data) != ref['container_sha256']:
        raise ValueError('downloaded workflow artifact differs from its supplied and GitHub digests')
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        raw = one_file(archive, 'results.jsonl')
        report = json.loads(one_file(archive, 'report.json'))
    return raw, report


def check(request, inputs):
    native = defaultdict(dict)
    for module, row in inputs.items():
        if row['kind'] == 'fresh':
            native[row['origin']][module] = row
    references = request.get('native_artifacts', {})
    if references.keys() != native.keys():
        raise ValueError('current native records and originating Actions reports differ')

    checked = 0
    for digest, ref in references.items():
        group = ref['group']
        raw, report = read_group(ref, 'current-native', WORKFLOW)
        if sha(raw) != digest or report['result_sha'] != digest:
            raise ValueError('native result does not match its supplied and archived digest')
        sc = report['scope']
        if (sc['parent'], sc['tree'], sc['manifest'], sc['graph'], sc['donor'], sc['group']) != (
                SCREENED, TREE, MANIFEST, GRAPH, SCREENED, group):
            raise ValueError('parent scope changed in the archived native checks')
        if (report['workflow_sha'], report['worker_source_sha'], report['runner_source_sha'], report['checker_source_sha']) != (
                ref['workflow_sha'], WORKER, RUNNER, CHECKER) or COMPILER not in report['toolchain']:
            raise ValueError('the archived native report ran different compiler checks')
        results = [json.loads(line) for line in raw.splitlines()]
        exact = {r['module']: r for r in results}
        if len(exact) != len(results) or len(results) != report['candidate_modules']:
            raise ValueError('native compiler report is incomplete or contains duplicated modules')
        for name, row in native[digest].items():
            actual = exact[name]
            if (actual['source'], actual['candidate'], actual['facets']) != (
                    row['parent_source'], row['head_source'], row['facets']):
                raise ValueError('Git sources or raw compiler outputs differ from the published artifact: ' + name)
            if (actual['status'] != 'pass' or actual['kernelImage'] is not True or actual['different'] != 0 or
                    actual['proofChanges'] != 0 or actual['publicImage'] is not True or actual['publicImports'] is not True or
                    actual['parentNames'] != actual['candidateNames'] or actual['old_warnings'] != actual['new_warnings']):
                raise ValueError('native declaration, proof, public import or diagnostic check failed: ' + name)
            checked += 1
    return {'actions_compiler_rows': checked, 'actions_artifacts': len(references)}
