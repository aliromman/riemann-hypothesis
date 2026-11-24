"""Save and verify a partial group result before GitHub recycles the runner."""
from __future__ import annotations
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import gzip
import hashlib
import json
import os
from pathlib import Path
import time
from prepare import canonical, HERE
from verify_retained import prune, sha

CERT = ('.olean','.olean.server','.olean.private','.ir','.ir.sig')
TRANSIENT = {'missing-dependency','infrastructure','timeout','process-failure'}
CLOSED = {'pass','none','private-use','elaboration','diagnostics','declarations'}

def domain(scope, roots, version):
    files=['CheckInterface.lean','verify_retained.py','screen.py','receipts.py','lake_imports.py','targets.txt']
    project={k:scope[k] for k in ['parent','tree','donor','manifest','graph','group','roots']}
    return dict(scope=project,roots_sha=sha(canonical(roots)),toolchain=version,
                scripts={f:sha((HERE/f).read_bytes()) for f in files})

def checkpoint(path, identity, rows):
    data=list(rows.values())
    record=dict(domain=identity,rows=data,sha=sha(canonical(data)))
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix('.partial')
    with gzip.open(tmp,'wb',compresslevel=1) as f:
        f.write(canonical(record))
    tmp.replace(path)

def recover(path, identity, checker, roots):
    if not path.exists():
        return {}
    with gzip.open(path,'rb') as f:
        raw=f.read(64*1024*1024+1)
    if len(raw)>64*1024*1024:
        raise ValueError('oversized checkpoint')
    rec=json.loads(raw)
    if rec['domain']!=identity or sha(canonical(rec['rows']))!=rec['sha']:
        raise ValueError('checkpoint scope or rows changed')
    wanted=set(roots)
    recovered={}
    seen=set()
    for row in rec['rows']:
        name=row['module']
        if name in seen or name not in wanted:
            raise ValueError('checkpoint has an unexpected or duplicate root')
        seen.add(name)
        source=(checker.o.repo/checker.paths[name]).read_bytes()
        candidate,removed=prune(source,checker.raw_targets)
        if (row['source'],row['candidate'],row['n'],row['removed'])!=(sha(source),sha(candidate),len(removed),removed):
            raise ValueError('checkpoint candidate differs from current source')
        if row['status'] in TRANSIENT:
            continue
        if row['status'] not in CLOSED:
            raise ValueError('unknown checkpoint result')
        if row['status']=='pass':
            if not (row['publicImage'] and row['publicImports'] and row['different']==0 and
                    row['parentNames']==row['candidateNames'] and row['old_warnings']==row['new_warnings'] and
                    type(row['kernelImage']) is bool and row['proofChanges']>=0 and
                    set(row['facets'])==set(CERT) and
                    all(isinstance(x,str) and len(x)==64 and set(x)<=set('0123456789abcdef') for x in row['facets'].values())):
                raise ValueError('checkpoint lacks complete native evidence')
        recovered[name]=row
    return recovered

def run_panel(checker, roots, work, resume, identity, workers, budget_seconds):
    rows=recover(resume,identity,checker,roots)
    reused=len(rows)
    todo=iter(n for n in roots if n not in rows)
    start=time.monotonic()
    deadline=start+budget_seconds
    next_save=start+90
    with (work/'results.jsonl').open('w') as out, ThreadPoolExecutor(workers) as pool:
        for row in rows.values():
            out.write(json.dumps(row,ensure_ascii=False,separators=(',',':'))+'\n')
        out.flush()
        active={}
        def top_up():
            while len(active)<workers and time.monotonic()<deadline:
                name=next(todo,None)
                if name is None:return
                active[pool.submit(checker.run,name)]=name
        top_up()
        while active:
            completed,_=wait(active,return_when=FIRST_COMPLETED)
            for task in completed:
                name=active.pop(task);row=task.result()
                if row['module']!=name:
                    raise ValueError('result belongs to a different module')
                if row['status']=='elaboration' and not row.get('error'):
                    row={**row,'native_status':'elaboration','status':'process-failure'}
                row['origin_run']=os.environ.get('GITHUB_RUN_ID')
                row['origin_attempt']=os.environ.get('GITHUB_RUN_ATTEMPT')
                rows[name]=row
                out.write(json.dumps(row,ensure_ascii=False,separators=(',',':'))+'\n')
            out.flush()
            now=time.monotonic()
            if now>=next_save:
                checkpoint(resume,identity,rows);next_save=now+90
                print(f'{len(rows)}/{len(roots)} results in {now-start:.0f}s ({reused} resumed)',flush=True)
            top_up()
    checkpoint(resume,identity,rows)
    return rows,reused
