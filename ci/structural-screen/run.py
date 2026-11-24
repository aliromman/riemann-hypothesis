"""Run and checkpoint one exact group of source transformations."""
import argparse,collections,gzip,json,os,platform,resource,subprocess,time
from concurrent.futures import FIRST_COMPLETED,ThreadPoolExecutor,wait
from pathlib import Path
from types import SimpleNamespace
from check import BASE,TREE,GRAPH,MANIFEST,HERE,SCREEN,CURRENT,TRANSIENT,Scope,canonical,import_clump,load_request,request_folder,restore,sha
from receipts import checkpoint

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--group',required=True)
    for name in ('parent','cache','work','resume','bin','judge'):ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--budget-minutes',type=int,default=235);o=ap.parse_args()
    for key,value in vars(o).items():
        if isinstance(value,Path):setattr(o,key,value.resolve())
    req,spec,variants=load_request(o.group)
    o.work.mkdir(exist_ok=True,parents=True);(o.work/'tmp').mkdir(exist_ok=True)
    upstream=import_clump(o.parent/'scripts/clump.py',req['upstream_clump_blob'])
    narchives=restore(o.parent,o.cache,o.work,variants,o.bin/'leantar')
    version=subprocess.check_output([o.bin/'lean','--version'],text=True).strip()
    if 'commit 0b77e12952ad39077d80d8bd6b66d601f225c321' not in version:raise ValueError('incorrect Lean build')
    scope={'group':o.group,'roots':len(variants),'restored':narchives,'parent':req['base'],'donor':BASE,'tree':TREE,
           'graph':GRAPH,'manifest':MANIFEST,'source_manifest_sha256':req['source_manifest_sha256'],'group_sha256':spec['sha256'],
           'recipe':req['recipe'],'official_clump_blob':req['upstream_clump_blob']}
    if 'production_source_manifest_sha256' in req:
        scope['production_source_manifest_sha256']=req['production_source_manifest_sha256']
        scope['input_mode']='exact-source-bytes'
    (o.work/'scope.json').write_bytes(canonical(scope))
    helpers={p.name:sha(p.read_bytes()) for p in (HERE/'check.py',HERE/'run.py',SCREEN/'CheckInterface.lean',SCREEN/'lake_imports.py',
                  SCREEN/'screen.py',SCREEN/'verify_retained.py',SCREEN/'receipts.py',CURRENT/'parent.py')}
    domain={'scope':scope,'compiler':version,'helpers':helpers}
    local=SimpleNamespace(repo=o.parent,work=o.work,headers=o.cache/'metadata/current-headers.json',targets=SCREEN/'targets.txt',
                    index=o.work/'index.json',archives=o.cache/'artifacts',baseline=o.parent/'.lake/build/lib/lean',
                    packages=o.parent/'.lake/packages',bin=o.bin,judge=o.judge,timeout=spec['timeout'])
    s,h=resource.getrlimit(resource.RLIMIT_NOFILE)
    if s<2400:resource.setrlimit(resource.RLIMIT_NOFILE,(2400 if h==resource.RLIM_INFINITY else min(h,2400),h))
    sources=request_folder(o.group)/'blobs' if req.get('input_mode')=='exact-source-bytes' else None
    checker=Scope(local,variants,upstream,sources)
    rows={};resume=o.resume/'results.gz'
    if resume.is_file():
        data=json.loads(gzip.decompress(resume.read_bytes()))
        if data['domain']!=domain or data['sha']!=sha(canonical(data['rows'])):raise ValueError('incorrect checkpoint domain')
        for row in data['rows']:
            n=row['module']
            if n in rows or [row[k] for k in ('source','candidate','net','code')]!=list(variants[n]):raise ValueError('unexpected cached row')
            if row['status'] not in TRANSIENT:rows[n]=row
    restored=len(rows);todo=iter(n for n in variants if n not in rows)
    start=time.monotonic();save_at=start+95
    report_path=o.work/'results.jsonl'
    with report_path.open('w') as out,ThreadPoolExecutor(spec['workers']) as pool:
        def write(row):out.write(json.dumps(row,ensure_ascii=False,separators=(',',':'))+'\n')
        for row in rows.values():write(row)
        jobs={}
        def fill():
            while len(jobs)<spec['workers'] and time.monotonic()-start<o.budget_minutes*60:
                n=next(todo,None)
                if n is None:return
                jobs[pool.submit(checker.compare,n)]=n
        fill()
        while jobs:
            finished,_=wait(jobs,return_when=FIRST_COMPLETED)
            for future in finished:
                n=jobs.pop(future);row=future.result()
                if n!=row['module']:raise ValueError('incorrect module result')
                row.update(origin_run=os.environ.get('GITHUB_RUN_ID'),origin_attempt=os.environ.get('GITHUB_RUN_ATTEMPT'))
                rows[n]=row;write(row)
            out.flush()
            if time.monotonic()>=save_at:
                checkpoint(resume,domain,rows);save_at=time.monotonic()+95
                print('checked',len(rows),'/',len(variants),flush=True)
            fill()
    checkpoint(resume,domain,rows)
    good=[r for r in rows.values() if r['status']=='pass'];counts=collections.Counter(r['status'] for r in rows.values())
    report={'scope':scope,'checked':len(rows),'pending':len(variants)-len(rows),'resumed':restored,'statuses':counts,
            'accepted':len(good),'accepted_net':sum(r['net'] for r in good),'accepted_code':sum(r['code'] for r in good),
            'seconds':round(time.monotonic()-start,3),'compiler':version,'workers':spec['workers'],'native_threads':1,
            'machine':platform.platform(),'workflow_sha':os.environ.get('GITHUB_SHA'),'helpers':helpers,'result_sha':sha(report_path.read_bytes())}
    (o.work/'report.json').write_bytes(canonical(report));print(report,flush=True)
    if report['pending'] or TRANSIENT&set(counts):raise SystemExit('incomplete native group')
    if o.group.startswith('canary-') and len(good)!=len(variants):raise SystemExit('canary found negative evidence')

if __name__=='__main__':main()
