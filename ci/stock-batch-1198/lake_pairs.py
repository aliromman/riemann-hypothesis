"""Time the complete compiled project cone of two predeclared theorems in stock Lake."""
import collections,hashlib,json,os,platform,re,resource,shutil,statistics,subprocess,sys,tempfile,time
from pathlib import Path
here=Path(__file__).resolve().parent
def sha(data):return hashlib.sha256(data).hexdigest()
def usage():
    u=resource.getrusage(resource.RUSAGE_CHILDREN)
    return u.ru_utime,u.ru_stime
def main():
    w,parent=(Path(s).resolve()for s in sys.argv[1:]);candidate=Path.cwd()
    panel=json.loads((here/'panel.json').read_bytes());pool=panel['integration_timing'];names=pool['modules'];roots=pool['roots']
    reference=json.loads((w/'parent-facets.json').read_bytes());compiled=json.loads((w/'report.json').read_bytes())
    if not set(names)<=set(reference) or not set(roots)<=set(panel['roots']):raise ValueError('invalid stock workload')
    bins={k:shutil.which(k) for k in ('lake','lean')}
    versions={k:subprocess.check_output([v,'--version'],text=True).strip()for k,v in bins.items()}
    snaps={};files={n:Path('src')/Path(*n.split('.')).with_suffix('.lean')for n in names}
    for key,origin in (('parent',parent),('candidate',candidate)):
        snaps[key]={n:(origin/file).read_bytes() for n,file in files.items()}
    for n in names:
        a,b=(snaps[s][n] for s in ('parent','candidate'))
        if n in panel['changed_sources']:
            r=panel['changed_sources'][n]
            if (sha(a),sha(b))!=(r['parent'],r['candidate']):raise ValueError('incorrect source transition '+n)
        elif a!=b:raise ValueError('unstated source edit '+n)
    samples=collections.defaultdict(list)
    with tempfile.TemporaryDirectory(dir=w)as root,(w/'lake-pairs.jsonl').open('w')as log:
        tmp=Path(root)
        for config in ('lakefile.toml','lake-manifest.json','lean-toolchain'):
            shutil.copyfile(candidate/config,tmp/config)
        (tmp/'.lake').mkdir();(tmp/'.lake/packages').symlink_to(candidate/'.lake/packages',target_is_directory=True)
        # Lake controls compiler imports. Remove the enclosing lake-env path
        # so neither revision can fall back to the previously built RH project.
        env=dict(os.environ);env.pop('LEAN_PATH',None);env['LEAN_NUM_THREADS']='1'
        command=[bins['lake'],'--no-cache','--fail-fast','build',*['+'+n+':olean' for n in roots]]
        for rep in range(6):
            order=('parent','candidate') if rep%2==0 else ('candidate','parent')
            for side in order:
                build=tmp/'.lake/build'
                if build.exists():shutil.rmtree(build)
                for n,rel in files.items():
                    src=tmp/rel;src.parent.mkdir(parents=True,exist_ok=True);src.write_bytes(snaps[side][n])
                cpu=usage();clock=time.monotonic()
                proc=subprocess.run(command,cwd=tmp,env=env,capture_output=True,text=True,timeout=270)
                seconds=time.monotonic()-clock;u,s=(b-a for a,b in zip(cpu,usage()))
                if proc.returncode:raise RuntimeError((proc.stdout+proc.stderr)[-2600:])
                actual={str(p.relative_to(build/'lib/lean').with_suffix('')).replace('/','.') for p in (build/'lib/lean').rglob('*.olean')}
                if actual!=set(names):raise ValueError(f'the stock compiler produced an unexpected module set: {actual ^ set(names)}')
                logtext=proc.stdout+proc.stderr
                built={n for n in re.findall(r'\bBuilt ([\w.\u0080-\uffff]+)(?=[ (]|$)',logtext,re.MULTILINE)}
                if set(names)!=built:raise ValueError(f'not all stock project compilations were observed: {built ^ set(names)}')
                for n in names:
                    out=build/'lib/lean'/Path(*n.split('.'))
                    if any(sha(out.with_suffix(ext).read_bytes())!=reference[n][ext] for ext in ('.olean','.ir.sig','.ir')):
                        raise ValueError('compiled bytes differ from the authenticated parent '+n)
                    completed=subprocess.run([w/'check-interface',n,w/'parent'/(n+'.olean'),out.with_suffix('.olean'),w/'comparison'],capture_output=True,text=True,check=True)
                    cmp=json.loads(completed.stdout)
                    if cmp['proofChanges'] or not cmp['kernelImage']:raise ValueError('stock proof mismatch '+n)
                row=dict(pair=rep,side=side,warmup=rep==0,user_seconds=u,system_seconds=s,cpu_seconds=u+s,elapsed_seconds=seconds,built=sorted(built))
                print(json.dumps(row),file=log,flush=True)
                if rep:samples[side].append(row)
    out=dict(status='complete',method='Stock lake --no-cache build of the entire fixed project cone. Each side starts with no project outputs and the same authenticated pinned package cache. One warm-up pair and five measured pairs alternate order; each pair compiles and checks the complete set. Timers cover Lake scheduling and compilation. Project source staging and post-run declaration and byte comparisons occur outside the timer.',roots=roots,modules=names,changed_modules=sorted(set(names)&set(compiled['changed'])),cpu_definition='child user plus system seconds',versions=versions,system=platform.platform(),metrics={})
    for metric in ('elapsed_seconds','cpu_seconds'):
        b,c=([r[metric]for r in samples[x]]for x in ('parent','candidate'));bm,cm=statistics.median(b),statistics.median(c)
        out['metrics'][metric]=dict(parent_median=bm,candidate_median=cm,change_percent=100*(cm/bm-1),parent_range=[min(b),max(b)],candidate_range=[min(c),max(c)],slower_pairs=[i+1 for i,(x,y)in enumerate(zip(b,c))if y>x])
    (w/'lake-benchmark.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out['metrics']))
if __name__=='__main__':
    try:main()
    except Exception as error:
        (Path(sys.argv[1])/'lake-benchmark.json').write_text(json.dumps(dict(status='unavailable',reason=str(error)),indent=2)+'\n');raise
