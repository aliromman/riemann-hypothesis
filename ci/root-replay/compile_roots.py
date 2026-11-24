"""Re-elaborate the five final theorems using candidate images for changed modules."""
from __future__ import annotations
import argparse, gc, gzip, hashlib, json, os, resource, sqlite3, subprocess, time
from pathlib import Path

def digest(p):
    with p.open('rb') as f: return hashlib.file_digest(f, 'sha256').hexdigest()

def stock(cmd,cwd,env,log):
    start = time.monotonic()
    with log.open('w') as dest:
        status = subprocess.run(cmd, cwd=cwd, env=env, stdout=dest, stderr=subprocess.STDOUT, timeout=900)
    return {'code': status.returncode,'seconds': round(time.monotonic()-start,3)}

def main():
    p=argparse.ArgumentParser()
    for key in ['repo','baseline','packages','bin','source-graph','images','work','judge','kernel']:
        p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--challenge',type=Path)
    p.add_argument('--parent-bindings',type=Path)
    p.add_argument('--provider-originals',type=Path)
    args=p.parse_args()
    for k,v in vars(args).items():
        if v is not None:setattr(args,k,v.resolve())
    args.work.mkdir(parents=True,exist_ok=True)
    soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft<2000:resource.setrlimit(resource.RLIMIT_NOFILE,(2400 if hard==-1 else min(2400,hard),hard))
    subprocess.run(['git','diff','--no-ext-diff','--quiet','HEAD','--','src/Main.lean','src/Statements.lean','src/Challenge.lean',
                    'lean-toolchain','lakefile.toml','lake-manifest.json','comparator.json'],cwd=args.repo,check=True)
    paths=set(x[4:-5].replace('/','.') for x in subprocess.check_output(['git','ls-tree','-r','--name-only','-z','HEAD','src'],cwd=args.repo,text=True).split('\0') if x.endswith('.lean'))
    graph=json.loads(args.source_graph.read_bytes())
    all_special=[(m,k) for m,edges in graph.items() for k,_,meta,deep in edges if k in paths and (meta or deep)]
    assert not [(m,k) for m,edges in graph.items() for k,_,meta,_ in edges if meta and k in paths]
    todo=[(k,deep) for k,_,_,deep in graph['Main'] if k in paths]; visible=set()
    while todo:
        mod,deep=todo.pop()
        if (mod,deep) in visible:continue
        visible.add((mod,deep))
        todo.extend((k,deep and d) for k,pub,_,d in graph[mod] if k in paths and (pub or deep))
    assert all(not deep for _,deep in visible)
    roots={n for n,_ in visible}
    candidates={}
    checked={}
    for line in args.images.read_text().splitlines():
        if not line:continue
        m,name,sha=line.split('\t');p=Path(name)
        if not p.is_file() or digest(p)!=sha:raise ValueError('candidate public SHA mismatch: '+m)
        if m in candidates or any(m==k for _,k in all_special): raise ValueError('ineligible candidate module: '+m)
        candidates[m]=p
        checked[m]=sha
    required = set(roots)
    if args.provider_originals:
        from providers import PROVIDERS, public_inputs, rebuild
        for provider in PROVIDERS:
            required.update(public_inputs(provider,graph))
    native={m:str(candidates.get(m,args.baseline.joinpath(*m.split('.')).with_suffix('.olean'))) for m in required}
    verified_parent={}
    if args.parent_bindings:
        with sqlite3.connect(f'file:{args.parent_bindings}?mode=ro',uri=True) as db:
            expected=dict(db.execute('select module, public from result'))
        ordinary_main=roots-candidates.keys()
        provider_only=(required-roots)-candidates.keys()
        for m in [*sorted(provider_only),*sorted(ordinary_main)]:
            p=Path(native[m]);stat=p.stat()
            if digest(p)!=expected.get(m):raise ValueError('parent public image differs from the authenticated archive: '+m)
            verified_parent[p]=(stat.st_ino,stat.st_size,stat.st_mtime_ns,expected[m])
            checked[m]=expected[m]
        del expected
    setup={'name':'Main','isModule':True,'package':'tree',
        'options':{'relaxedAutoImplicit':False,'autoImplicit':False,'pp.unicode.fun':True,'maxSynthPendingDepth':3,'maxHeartbeats':4000000},
        'plugins':[],'dynlibs':[],'importArts':{m:[[native[m]],[]] for m in roots}}
    cert=args.work/'setup.json';cert.write_text(json.dumps(setup,separators=(',',':')))
    # Omit all project directories from the usual search path so an unforeseen project lookup fails.
    prefixes=args.work/'prefixes'
    for n in {m.split('.')[0] for m in paths}: (prefixes/n).mkdir(parents=True,exist_ok=True)
    env=os.environ|{'PATH':str(args.bin)+os.pathsep+os.environ['PATH'],
        'LEAN_PATH':os.pathsep.join([str(prefixes),*[str(p/'.lake/build/lib/lean') for p in args.packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]]),
        'LEAN_NUM_THREADS':'1','LEAN_ABORT_ON_PANIC':'1','LAKE_ARTIFACT_CACHE':'false'}
    n=(args.work/'Main.olean'); names=json.loads((args.repo/'comparator.json').read_bytes())['theorem_names']
    res={'projects':len(roots),'candidate_all':len(candidates),'candidate_visible':len(roots&candidates.keys()),
         'sources':digest(args.images),'targets':names,'parent_main_public':digest(args.baseline/'Main.olean')}
    binding=args.images.parent/'bound.json'
    if binding.exists():
        bound=json.loads(binding.read_bytes())
        checkout=subprocess.check_output(['git','rev-parse','HEAD:src'],cwd=args.repo,text=True).strip()
        if bound['after_src_tree']!=checkout or bound['manifest_sha256']!=digest(args.images):
            raise ValueError('source checkout or compiled artifact manifest differs from its recorded tree')
        if len(candidates)!=bound['changed']:raise ValueError('incomplete manifest')
        res['source_binding']=bound
    if args.provider_originals:
        if not args.parent_bindings or not required <= checked.keys():
            raise ValueError('the root compilation requires an authenticated image for every project input')
        parent=res.get('source_binding',{}).get('parent') or 'HEAD'
        providers=rebuild(args.repo,parent,args.provider_originals,args.work/'providers',args.bin,args.judge,
                          graph,setup,native,checked,candidates,env)
        for m,r in providers.items():
            actual=Path(r['public_output'])
            if m not in native or digest(actual)!=checked[m]:
                raise ValueError('fresh provider differs from the certified Main input: '+m)
            setup['importArts'][m]=[[str(actual)],[]]
        raw=json.dumps(setup,separators=(',',':')).encode()
        cert.write_bytes(raw)
        exported=args.work/'providers/main-setup.json.gz'
        with exported.open('wb') as dest:
            with gzip.GzipFile(filename='',fileobj=dest,mode='wb',mtime=0,compresslevel=4) as stream:
                stream.write(raw)
        res['direct_providers']={'providers':providers,'actual_main_setup_sha256':digest(cert),
                                 'compressed_main_setup_sha256':digest(exported)}
    res['fresh_parent_digests']=sum(Path(native[m]) in verified_parent for m in roots)
    res['provider_only_inputs']=sorted(required-roots)
    del graph,paths,visible,roots,required,candidates,native,setup
    gc.collect()
    steps=[
      ('compile',[args.bin/'lean','-j1','--tstack=400000','--setup='+str(cert),'--root='+str(args.repo/'src'),'-o',n,args.repo/'src/Main.lean']),
      ('decls',[args.judge,'Main',args.baseline/'Main.olean',n,args.work]),
      ('replay',[args.bin/'lean','-j1','--tstack=400000','--run',args.kernel,n,cert,*names]),
      ('axioms',[args.bin/'lean','--run',Path(__file__).with_name('RootAxioms.lean').resolve(),n,*names])]
    if args.challenge:
        steps.append(('challenge',[args.bin/'lean','--run',Path(__file__).with_name('CompareChallenge.lean').resolve(),n,args.challenge,args.baseline/'Statements.olean',*names]))
    for name,cmd in steps:
        res[name]=stock(cmd,args.work,env,args.work/(name+'.log'));print(name,res[name],flush=True)
        (args.work/'report.json').write_text(json.dumps(res))
        if res[name]['code']:raise SystemExit(res[name]['code'])
    for p,(ino,size,mtime,want) in verified_parent.items():
        s=p.stat()
        if (s.st_ino,s.st_size,s.st_mtime_ns)!=(ino,size,mtime) and digest(p)!=want:raise ValueError('a parent input changed during recheck')
    res['public_sha']=digest(n)
    res['stable_facets']={suffix:digest(Path(str(n)+suffix))==digest(Path(str(args.baseline/'Main.olean')+suffix)) for suffix in ('','.server','.private')}
    (args.work/'report.json').write_text(json.dumps(res))
if __name__=='__main__':main()
