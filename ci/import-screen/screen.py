"""Run the local candidate screen in two independent stock Lean processes."""
from __future__ import annotations
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import time
from types import SimpleNamespace

from prepare import GRAPH, HERE, MANIFEST, PARENT, SOURCE_TREE
from lake_imports import project_artifacts
from verify_retained import Check, sha

FACETS = ('.olean','.olean.server','.olean.private','.ir','.ir.sig')

class Runner(Check):
    def __init__(self, options):
        super().__init__(options)
        self.header_graph = json.loads(options.headers.read_bytes())

    def setup(self, module):
        setup = super().setup(module)
        setup['importArts'] = project_artifacts(module, self.header_graph, self.art)
        return setup

    def run(self, module):
        result = super().run(module)
        if result['status'] == 'pass':
            packed = self.o.work/'certified'/Path(*module.split('.')).with_suffix('.tar.xz')
            packed.unlink()
        return result

def comparison(results, expected):
    differing = {}
    for module, before in expected.items():
        after = results[module]
        differences = [k for k in ['source','candidate','status','n','removed','publicImage','publicImports',
                                   'parentNames','candidateNames','different','proofChanges','old_warnings','new_warnings']
                       if before.get(k) != after.get(k)]
        differences += [k for k in FACETS if before.get('facets',{}).get(k) != after.get('facets',{}).get(k)]
        if differences:
            differing[module] = differences
    return differing

def main():
    p=argparse.ArgumentParser()
    for name in ('parent','state','work','bin','judge'):
        p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args()
    parent,state,work,bin_,judge=(getattr(args,n).resolve() for n in ('parent','state','work','bin','judge'))
    scope=json.loads((work/'scope.json').read_bytes())
    for k,v in [('parent',PARENT),('tree',SOURCE_TREE),('manifest',MANIFEST),('graph',GRAPH)]:
        if scope[k]!=v:raise ValueError(f'invalid scope {k}')
    roots=(work/'roots.txt').read_text().splitlines()
    if len(roots)!=scope['roots'] or len(roots)!=len(set(roots)):
        raise ValueError('invalid roots list')
    opts=SimpleNamespace(repo=parent,work=work,headers=state/'metadata/headers.json',
                         targets=HERE/'targets.txt',index=work/'index.json',archives=state/'artifacts',
                         baseline=parent/'.lake/build/lib/lean',packages=parent/'.lake/packages',bin=bin_,
                         judge=judge,timeout=180)
    (work/'tmp').mkdir(exist_ok=True)
    soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft<2400:
        resource.setrlimit(resource.RLIMIT_NOFILE,(2400 if hard==-1 else min(2400,hard),hard))
    checker=Runner(opts)
    cert_file=work/'results.jsonl'
    result_rows={}
    counts=Counter()
    started=time.monotonic()
    with cert_file.open('w') as output, ThreadPoolExecutor(max_workers=2) as pool:
        for row in pool.map(checker.run,roots):
            result_rows[row['module']]=row
            counts[row['status']]+=1
            output.write(json.dumps(row,ensure_ascii=False,separators=(',',':'))+'\n')
            output.flush()
            if len(result_rows) % 100 == 0:
                print(len(result_rows),dict(counts),round(time.monotonic()-started,1),flush=True)
    matched={}
    if scope['group']=='pilot':
        matched=comparison(result_rows,json.loads((HERE/'pilot-expected.json').read_bytes()))
    report=dict(scope=scope,statuses=dict(counts),lines=sum(v['n'] for v in result_rows.values() if v['status']=='pass'),
                exact_private_proof_modules=sum(r['status']=='pass' and r['proofChanges']==0 for r in result_rows.values()),
                exact_private_proof_lines=sum(r['n'] for r in result_rows.values() if r['status']=='pass' and r['proofChanges']==0),
                candidate_modules=len(result_rows),seconds=round(time.monotonic()-started,2),
                machine=platform.platform(),toolchain=subprocess.check_output([bin_/'lean','--version'],text=True).strip(),
                workflow_sha=os.environ.get('GITHUB_SHA'),workers=2,lean_threads=1,
                worker_source_sha=sha((HERE/'verify_retained.py').read_bytes()),
                checker_source_sha=sha((HERE/'CheckInterface.lean').read_bytes()),result_sha=sha(cert_file.read_bytes()),
                target_sha=sha((HERE/'targets.txt').read_bytes()),pilot_cross_host_differences=matched)
    print(report,flush=True)
    (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if not counts['pass'] or counts['missing-dependency'] or counts['infrastructure']:
        raise SystemExit('parent restoration or verification infrastructure failed')
    if scope['group']=='pilot' and (counts['pass']!=len(roots) or matched):
        raise SystemExit('pilot did not reproduce its local certificates')
if __name__=='__main__':
    main()
