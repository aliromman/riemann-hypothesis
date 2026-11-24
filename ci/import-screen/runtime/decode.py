#!/usr/bin/env python3
"""Run stock leantar with enough stack and identify a failing archive."""
import gzip
import json
import os
from pathlib import Path
import resource
import subprocess
import sys

MIB=1<<20

def stock(exe,args,jobs,stack):
    soft,hard=resource.getrlimit(resource.RLIMIT_STACK)
    want=stack if hard==resource.RLIM_INFINITY else min(hard,stack)
    if sys.platform.startswith('linux') and soft!=resource.RLIM_INFINITY and soft<want:
        try:
            resource.setrlimit(resource.RLIMIT_STACK,(want,hard))
        except (ValueError,OSError) as exc:
            print('OS stack limit:',soft,hard,exc,file=sys.stderr)
    env=dict(os.environ)
    env['RUST_MIN_STACK']=str(max(int(env.get('RUST_MIN_STACK','0')),stack))
    return subprocess.run([exe,*args],input=json.dumps(jobs),text=True,env=env).returncode

def describe(jobs):
    by_archive={Path(job['file']).name:{'archive':Path(job['file']).name,'input':job['hash']} for job in jobs}
    manifest=os.environ.get('RH_LTAR_MANIFEST')
    if manifest and Path(manifest).is_file():
        with gzip.open(manifest,'rt') as rows:
            next(rows)
            for line in rows:
                name,_,archive,digest=json.loads(line)
                if archive in by_archive:by_archive[archive].update(module=name,sha256=digest)
    return by_archive

def record(message):
    print(json.dumps(message,separators=(',',':')),file=sys.stderr,flush=True)
    where=os.environ.get('RH_LTAR_DIAGNOSTICS')
    if where:
        path=Path(where)
        path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('a') as f:f.write(json.dumps(message,separators=(',',':'))+'\n')

def unpack(exe,args,jobs):
    code=stock(exe,args,jobs,32*MIB)
    if not code:return
    members=describe(jobs)
    record({'event':'batch_failure','status':code,'rust_min_stack':32*MIB,
            'os_stack_limits':resource.getrlimit(resource.RLIMIT_STACK),'archives':list(members.values())})
    single=list(args)
    index=single.index('--jobs')
    single[index+1]='1'
    failed=[]
    for job in jobs:
        code=stock(exe,single,[job],64*MIB)
        if code:failed.append({'status':code,**members[Path(job['file']).name]})
    record({'event':'single_archive_results','checked':len(jobs),'failed':failed})
    if failed:raise RuntimeError('stock leantar failed on individual authenticated archives')

if __name__=='__main__':
    unpack(os.environ['RH_STOCK_LEANTAR'],sys.argv[1:],json.load(sys.stdin))
