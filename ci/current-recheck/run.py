"""Run one exact source group and keep a restartable record of native evidence."""
import argparse
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
from collections import Counter
import gzip
import os
from pathlib import Path
import platform
import resource
import subprocess
import time
from types import SimpleNamespace
from parent import BASE,TREE,GRAPH,MANIFEST,HERE,SCREEN,canonical,restore,sha,json
from native_candidate import Exact
from receipts import checkpoint,TRANSIENT,CERT

def load_plan(group,folder):
    plan=json.loads((folder/'request.json').read_bytes())
    if (plan['base'],plan['parent_tree'],plan['manifest'],plan['graph'])!=(BASE,TREE,MANIFEST,GRAPH):
        raise ValueError('job uses an incorrect current parent')
    g=plan['groups'][group]
    raw=gzip.decompress((folder/'groups'/(group+'.jsonl.gz')).read_bytes())
    if sha(raw)!=g['sha256']:raise ValueError('candidate selection digest mismatch')
    variants={}
    for line in raw.splitlines():
        n,v=json.loads(line)
        if n in variants:raise ValueError('duplicate source transition')
        variants[n]=v
    if len(variants)!=g['count']:raise ValueError('candidate group count differs')
    return plan,g,variants

def private_variant_matches(row, variant):
    return [row['source'],row['candidate'],row['removed'],row['added_imports']]==[variant[2],variant[3],variant[5],variant[6]]

def run_group(checker,group,variants,work,resume,domain,seconds,workers,variant_matches=private_variant_matches):
    saved={};path=resume/'results.json.gz'
    if path.exists():
        data=json.loads(gzip.decompress(path.read_bytes()))
        if data['domain']!=domain or sha(canonical(data['rows']))!=data['sha']:raise ValueError('wrong native checkpoint identity')
        for row in data['rows']:
            n=row['module'];v=variants[n]
            if n in saved or not variant_matches(row,v):
                raise ValueError('checkpoint differs from the exact candidate header')
            if row['status']=='pass' and (type(row.get('kernelImage')) is not bool or set(row['facets'])!=set(CERT) or row['different']!=0):
                raise ValueError('incomplete passed record')
            if row['status'] not in TRANSIENT:saved[n]=row
    restored=len(saved)
    it=iter(n for n in variants if n not in saved);started=time.monotonic();next_save=started+100
    with (work/'results.jsonl').open('w') as f,ThreadPoolExecutor(workers) as pool:
        def write(row):f.write(json.dumps(row,ensure_ascii=False,separators=(',',':'))+'\n')
        for row in saved.values():write(row)
        active={}
        def fill():
            while len(active)<workers and time.monotonic()-started<seconds:
                n=next(it,None)
                if n is None:return
                active[pool.submit(checker.run,n)]=n
        fill()
        while active:
            done,_=wait(active,return_when=FIRST_COMPLETED)
            for a in done:
                n=active.pop(a);row=a.result()
                if row['module']!=n:raise ValueError('incorrect module result')
                if row['status']=='elaboration' and not row.get('error'):
                    row={**row,'native_status':'elaboration','status':'process-failure'}
                row.update(origin_run=os.environ.get('GITHUB_RUN_ID'),origin_attempt=os.environ.get('GITHUB_RUN_ATTEMPT'))
                saved[n]=row;write(row)
            f.flush()
            if time.monotonic()>=next_save:
                checkpoint(path,domain,saved);next_save=time.monotonic()+100
                print('checked',len(saved),'/',len(variants),'modules',flush=True)
            fill()
    checkpoint(path,domain,saved)
    return saved,restored,time.monotonic()-started

def main():
    p=argparse.ArgumentParser();p.add_argument('--group',required=True);p.add_argument('--budget-minutes',type=int,default=235)
    for flag in ('parent','cache','work','resume','bin','judge','request'):
        p.add_argument('--'+flag,type=Path,required=True)
    o=p.parse_args()
    for k,v in vars(o).items():
        if isinstance(v,Path):setattr(o,k,v.resolve())
    plan,g,variants=load_plan(o.group,o.request)
    o.work.mkdir(parents=True,exist_ok=True);(o.work/'tmp').mkdir(exist_ok=True)
    directories=restore(o.parent,o.cache,o.work,variants,o.bin/'leantar')
    scope=dict(parent=BASE,tree=TREE,donor=BASE,manifest=MANIFEST,graph=GRAPH,group=o.group,roots=len(variants),
               archives=directories,candidate_tree=plan['candidate_tree'],source_transitions_sha256=g['sha256'])
    (o.work/'scope.json').write_text(json.dumps(scope,indent=2)+'\n')
    opts=SimpleNamespace(repo=o.parent,work=o.work,headers=o.cache/'metadata/current-headers.json',targets=SCREEN/'targets.txt',
        index=o.work/'index.json',archives=o.cache/'artifacts',baseline=o.parent/'.lake/build/lib/lean',
        packages=o.parent/'.lake/packages',bin=o.bin,judge=o.judge,timeout=g['timeout'])
    version=subprocess.check_output([o.bin/'lean','--version'],text=True).strip()
    if 'commit 0b77e12952ad39077d80d8bd6b66d601f225c321' not in version:raise ValueError('incorrect native compiler')
    soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft<2400:resource.setrlimit(resource.RLIMIT_NOFILE,(2400 if hard==resource.RLIM_INFINITY else min(hard,2400),hard))
    domain=dict(scope=scope,toolchain=version,checks={f.name:sha(f.read_bytes()) for f in
        (HERE/'run.py',HERE/'native_candidate.py',HERE/'parent.py',SCREEN/'CheckInterface.lean',SCREEN/'screen.py',SCREEN/'verify_retained.py',SCREEN/'lake_imports.py')})
    checked,resumed,elapsed=run_group(Exact(opts,variants),o.group,variants,o.work,o.resume,domain,o.budget_minutes*60,g['workers'])
    counts=Counter(r['status'] for r in checked.values())
    strict=[r for r in checked.values() if r['status']=='pass' and r['kernelImage'] and r['proofChanges']==0]
    report=dict(scope=scope,statuses=counts,lines=sum(r['n'] for r in checked.values() if r['status']=='pass'),
        exact_private_proof_modules=len(strict),exact_private_proof_lines=sum(r['n'] for r in strict),candidate_modules=len(checked),
        resumed_modules=resumed,pending=len(variants)-len(checked),seconds=round(elapsed,3),machine=platform.platform(),toolchain=version,
        workflow_sha=os.environ.get('GITHUB_SHA'),workers=g['workers'],lean_threads=1,checker_source_sha=domain['checks']['CheckInterface.lean'],
        worker_source_sha=domain['checks']['native_candidate.py'],target_sha=sha((SCREEN/'targets.txt').read_bytes()),
        runner_source_sha=domain['checks']['run.py'],result_sha=sha((o.work/'results.jsonl').read_bytes()))
    (o.work/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
    if report['pending'] or any(counts[x] for x in TRANSIENT):raise SystemExit('incomplete native verification')
if __name__=='__main__':main()
