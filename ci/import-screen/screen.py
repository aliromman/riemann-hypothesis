"""Run the local candidate screen in two independent stock Lean processes."""
from __future__ import annotations
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import time
import tomllib
from types import SimpleNamespace

from prepare import GRAPH, HERE, MANIFEST, PARENT, SOURCE_TREE
from lake_imports import project_artifacts
from verify_retained import Check, sha
from receipts import domain, run_panel, TRANSIENT

FACETS = ('.olean','.olean.server','.olean.private','.ir','.ir.sig')

class Runner(Check):
    def __init__(self, options):
        super().__init__(options)
        self.header_graph = json.loads(options.headers.read_bytes())
        config = tomllib.loads((options.repo/'lakefile.toml').read_text())
        self.package = config['name']
        self.lean_options = {}
        def flatten(prefix, table):
            for part,value in table.items():
                key = f'{prefix}.{part}' if prefix else part
                if isinstance(value,dict):
                    flatten(key,value)
                else:
                    self.lean_options[key] = value
        flatten('',config['leanOptions'])

    def setup(self, module):
        # This screen covers the Development library. Its options are the package defaults.
        if not module.startswith('Development.'):
            raise ValueError('unexpected library')
        return dict(name=module,isModule=True,package=self.package,options=self.lean_options,
                    plugins=[],dynlibs=[],importArts=project_artifacts(module,self.header_graph,self.art))

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
                                   'parentNames','candidateNames','different','proofChanges','old_warnings','new_warnings','kernelImage']
                       if before.get(k) != after.get(k)]
        differences += [k for k in FACETS if before.get('facets',{}).get(k) != after.get('facets',{}).get(k)]
        if differences:
            differing[module] = differences
    return differing

def main():
    p=argparse.ArgumentParser()
    for name in ('parent','state','work','bin','judge'):
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--resume',type=Path,required=True)
    p.add_argument('--budget-minutes',type=int,default=225)
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
                         judge=judge,timeout=540 if scope['group'].startswith('rest-100000-') else 240)
    (work/'tmp').mkdir(exist_ok=True)
    soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft<2400:
        resource.setrlimit(resource.RLIMIT_NOFILE,(2400 if hard==-1 else min(2400,hard),hard))
    checker=Runner(opts)
    cert_file=work/'results.jsonl'
    started=time.monotonic()
    # Only one native process enters the largest closures on a 16 GiB VM.
    workers=1 if scope['group'].startswith('rest-100000-') else 2
    version=subprocess.check_output([bin_/'lean','--version'],text=True).strip()
    identity=domain(scope,roots,version)
    result_rows,reused=run_panel(checker,roots,work,args.resume.resolve()/'receipt.json.gz',
                                  identity,workers,args.budget_minutes*60)
    counts=Counter(row['status'] for row in result_rows.values())
    matched={}
    if scope['group']=='pilot' and len(result_rows)==len(roots):
        matched=comparison(result_rows,json.loads((HERE/'pilot-expected.json').read_bytes()))
    # These raw partitions also contain server and private environment data.
    # Record their bytes. The exact kernel payload has a separate native comparison.
    gate_differences = {n: [k for k in keys if k not in ('.olean.server','.olean.private')]
                        for n,keys in matched.items()}
    gate_differences = {n:keys for n,keys in gate_differences.items() if keys}
    report=dict(scope=scope,statuses=dict(counts),lines=sum(v['n'] for v in result_rows.values() if v['status']=='pass'),
                exact_private_proof_modules=sum(r['status']=='pass' and r['proofChanges']==0 and r['kernelImage'] for r in result_rows.values()),
                exact_private_proof_lines=sum(r['n'] for r in result_rows.values() if r['status']=='pass' and r['proofChanges']==0 and r['kernelImage']),
                candidate_modules=len(result_rows),resumed_modules=reused,pending=len(roots)-len(result_rows),seconds=round(time.monotonic()-started,2),
                machine=platform.platform(),toolchain=version,
                workflow_sha=os.environ.get('GITHUB_SHA'),workers=workers,lean_threads=1,
                worker_source_sha=sha((HERE/'verify_retained.py').read_bytes()),
                checker_source_sha=sha((HERE/'CheckInterface.lean').read_bytes()),result_sha=sha(cert_file.read_bytes()),
                target_sha=sha((HERE/'targets.txt').read_bytes()),pilot_cross_host_differences=matched,
                pilot_cross_host_gate_differences=gate_differences)
    print(report,flush=True)
    (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if len(result_rows)!=len(roots) or not counts['pass'] or any(counts[status] for status in TRANSIENT):
        raise SystemExit('routine ended with pending work or an inconclusive native invocation; checkpoint saved')
    if scope['group']=='pilot' and (counts['pass']!=len(roots) or gate_differences):
        raise SystemExit('pilot did not reproduce its local certificates')
if __name__=='__main__':
    main()
