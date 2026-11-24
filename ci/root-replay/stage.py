"""Construct the exact candidate public inputs from the published project archives."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
from types import SimpleNamespace

from manifest import read_request,sha
from native import Blobs,file_sha,git,header,hosted_batch,ls,tree
from providers import FACETS,PROVIDERS,public_inputs

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'import-screen'))
from lake_imports import import_levels
from runtime.decode import unpack
from prepare import GRAPH,MANIFEST,PARENT,SOURCE_TREE,canonical,graph_from_source,load,metadata,pin,source_path
from reuse_gate import check as check_reuse

PLAIN=re.compile(rb'import Mathlib\.[^\s]+\n')

def check_edits(a,b,module):
    pre_a,body_a=header(a.splitlines(keepends=True))
    pre_b,body_b=header(b.splitlines(keepends=True))
    if body_a!=body_b or [x for x in pre_a if not PLAIN.fullmatch(x)]!=[x for x in pre_b if not PLAIN.fullmatch(x)]:
        raise ValueError('a change outside plain Mathlib header imports: '+module)
    if b'module\n' not in pre_a:
        raise ValueError('expected a source with explicit module visibility: '+module)

def actual_diff(candidate, request, inputs):
    parent,head=request['base'],request['head']
    if git(candidate,'rev-parse','HEAD').decode().strip()!=head or tree(candidate,parent)!=request['base_src'] or tree(candidate,head)!=request['head_src']:
        raise ValueError('checked-out PR or either source tree differs')
    subprocess.run(['git','merge-base','--is-ancestor',parent,head],cwd=candidate,check=True)
    old=ls(candidate,parent)
    new=ls(candidate,head)
    raw=git(candidate,'diff','--no-renames','--name-only','-z',parent,head)
    paths={os.fsdecode(v) for v in raw.split(b'\0') if v}
    wanted={str(source_path(m)) for m in inputs}
    if request.get('source_mode')=='clump-scopes':
        from structural_gate import tooling
        extra=paths-wanted
        if tooling(candidate,parent,head,extra)!=request['tooling']:
            raise ValueError('the proposed clump tool files differ from their exact Git and SHA-256 records')
        for path in extra:
            if file_sha(candidate/path)!=request['tooling'][path][1]['sha256']:
                raise ValueError('the actual clump tool differs from the committed source: '+path)
    else:extra=set()
    if paths!=wanted|extra or not wanted<=old.keys() or not wanted<=new.keys() or wanted&{'src/Main.lean','src/Statements.lean','src/Challenge.lean'}:
        raise ValueError('the complete Git diff is outside the supplied source-bound candidate set')
    total=0
    count=0
    for path,oid in new.items():
        if not path.endswith('.lean'):continue
        file=candidate/path
        if file.is_symlink():raise ValueError('symlinked candidate source: '+path)
        data=file.read_bytes()
        if hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()!=oid:
            raise ValueError('candidate worktree differs from its Git blob: '+path)
        total+=len(data)
        count+=1
    for path in ['comparator.json','export-targets.txt','lake-manifest.json','lean-toolchain','lakefile.toml']:
        if (candidate/path).read_bytes()!=git(candidate,'show',head+':'+path):
            raise ValueError('candidate configuration differs from its Git blob: '+path)
    return {m:old[str(source_path(m))] for m in inputs},count,total

class BatchParents:
    def __init__(self,directories):
        self.directories=directories
    def inputs(self,module,_):
        public=self.directories[module]/(module.rsplit('.',1)[-1]+'.olean')
        return [public,public.with_suffix('.ir.sig'),public.with_suffix('.ir')]

def restore_batch(names,index,shas,cache,leantar,rebuilder,baseline,images,reader,old_blobs,candidate,inputs,bindings,batchdir,structural=False):
    jobs=[]
    directories={}
    for i,n in enumerate(names):
        _,key,archive=index[n]
        tar=cache/'artifacts'/archive
        if tar.is_symlink() or not tar.is_file():
            raise ValueError('unsafe or missing project archive: '+archive)
        # The downloader must already have validated this same immutable archive.
        if file_sha(tar)!=shas[archive]:raise ValueError('published archive digest differs: '+n)
        folder=batchdir/str(i)
        folder.mkdir()
        directories[n]=folder
        jobs.append({'file':str(tar),'hash':key,'base':[str(folder),str(folder)]})
    unpack(leantar,['--jobs','2','-f','-x','-j','-'],jobs)
    parents=BatchParents(directories)
    opt=SimpleNamespace(out=batchdir,rebuilder=rebuilder,audit_ir=True,plan_only=False,ir_results={})
    new_jobs=[]
    result=[]
    parent_bytes=identity_bytes=0
    for n in names:
        public=parents.inputs(n,None)[0]
        if n in inputs:
            old=reader.read(old_blobs[n])
            current=(candidate/source_path(n)).read_bytes()
            r=inputs[n]
            if sha(old)!=r['parent_source'] or sha(current)!=r['head_source']:
                raise ValueError('native compiler receipt differs from the old or proposed source: '+n)
            dst=images/'public'/Path(*n.split('.')).with_suffix('.olean')
            if structural:
                from structural_gate import ORDINARY,header as structural_header
                structural_header(old,current)
                candidate_oid=hashlib.sha1(b'blob '+str(len(current)).encode()+b'\0'+current).hexdigest()
                if (r['parent_blob'],r['candidate_blob'],r['parent_ltar_sha256'])!=(old_blobs[n],candidate_oid,shas[index[n][2]]):
                    raise ValueError('structural compiler row differs from its Git source or full archive: '+n)
                for suffix in r['parent_facets']:
                    if file_sha(public.with_suffix(suffix))!=r['parent_facets'][suffix]:
                        raise ValueError('the structural parent compiler facet differs from its official archive: '+n)
                if any(r['parent_facets'][s]!=r['facets'][s] for s in ORDINARY):
                    raise ValueError('the ordinary structural compiler outputs changed: '+n)
                identity_bytes+=public.stat().st_size
                dst.parent.mkdir(parents=True,exist_ok=True)
                public.replace(dst)
            else:
                if 'parent_public_ir' in r:
                    for ext,asset in zip(('.olean','.ir.sig','.ir'),parents.inputs(n,None)):
                        if file_sha(asset)!=r['parent_public_ir'][ext]:
                            raise ValueError('the fresh compiler parent differs from the authenticated archive: '+n)
                check_edits(old,current,n)
                new_jobs.append((n,old,current,dst,r['facets']))
            result.append((n,str(dst),r['facets']['.olean']))
        else:
            dst=baseline.joinpath(*n.split('.')).with_suffix('.olean')
            dst.parent.mkdir(parents=True,exist_ok=True)
            digest=file_sha(public)
            if n=='Main':
                for ext in ('.server','.private'):
                    Path(str(public)+ext).replace(Path(str(dst)+ext))
            if n in PROVIDERS:
                for ext in (*FACETS[1:],'.trace'):
                    public.with_suffix(ext).replace(dst.with_suffix(ext))
                _,key,archive=index[n]
                owner={'module':n,'lake_key':key,'archive':archive,'sha256':shas[archive]}
                dst.with_suffix('.owner.json').write_bytes(canonical(owner))
            parent_bytes+=public.stat().st_size
            public.replace(dst)
            bindings.append((n,digest))
    byte_count=hosted_batch(new_jobs,parents,opt)
    if len(opt.ir_results)!=len(new_jobs) or any(a!=b or c!=d for a,b,c,d in opt.ir_results.values()):
        raise ValueError('the reconstructed stock IR differs from the genuine native compiler output')
    return result,parent_bytes,byte_count+identity_bytes

def main():
    p=argparse.ArgumentParser()
    for key in ('request','parent','candidate','cache','work','bin','rebuilder'):
        p.add_argument('--'+key,type=Path,required=True)
    args=p.parse_args()
    for k,v in vars(args).items():setattr(args,k,v.resolve())
    req,inputs=read_request(args.request)
    import current_reuse, refresh, verified_batch
    newest = verified_batch.BATCHES.get(req['base_src'])
    refreshed=req['base_src']==refresh.TREE
    latest=req['base_src']==current_reuse.TREE
    structural=req.get('source_mode')=='clump-scopes'
    if structural and not (latest or refreshed or newest):raise ValueError('the structural source refactor has a different compiler baseline')
    if not (latest or refreshed or newest) and (req['base']!=PARENT or req['base_src']!=SOURCE_TREE):
        raise ValueError('this cache does not certify the approved base revision')
    args.work.mkdir(parents=True,exist_ok=True)
    baseline=args.work/'baseline';images=args.work/'images'
    if baseline.exists() or images.exists():raise ValueError('use a fresh root staging directory')
    candidate=args.candidate
    old_sources,source_count,source_bytes=actual_diff(candidate,req,inputs)
    if newest:
        api,index,shas=verified_batch.published_parent(newest,args.parent,args.cache,req)
        graph_digest,manifest=newest['graph'],newest['manifest']
        graph_file=args.cache/'metadata/current-headers.json'
    elif refreshed:
        api,index,shas=refresh.published_parent(args.parent,args.cache,req)
        graph_digest,manifest=refresh.GRAPH,refresh.MANIFEST
        graph_file=args.cache/'metadata/current-headers.json'
    elif latest:
        api,index,shas=current_reuse.current_parent(args.parent,args.cache,req)
        graph_digest,manifest=current_reuse.GRAPH,current_reuse.MANIFEST
        graph_file=args.cache/'metadata/current-headers.json'
    else:
        api=load(args.parent/'scripts/ci-cache-get.py','root_cache')
        index,shas=metadata(api,pin(args.parent,api),args.cache,True)
        graph_digest,manifest=GRAPH,MANIFEST
        graph_file=args.cache/'metadata/headers.json'
    os.environ['RH_LTAR_MANIFEST']=str(args.cache/'metadata'/(manifest+'.jsonl.gz'))
    if not graph_file.is_file() or file_sha(graph_file)!=graph_digest:
        graph_file.write_bytes(canonical(graph_from_source(args.parent,index)))
    g=graph_file.read_bytes()
    if sha(g)!=graph_digest:raise ValueError('parent import graph digest differs from the stock screen')
    (args.work/'graph.json').write_bytes(g)
    graph=json.loads(g)
    if graph.keys()!=index.keys():raise ValueError('the project graph differs from the official archive index')
    if not inputs.keys()<=graph.keys():raise ValueError('a candidate module is outside the official project graph')
    reused={n:r for n,r in inputs.items() if r['kind']=='reused'}
    if any(r['parent']!=req['base_src'] for r in inputs.values() if r['kind']=='fresh'):
        raise ValueError('current-base records claim a different source tree')
    validation={}
    cache_tools=current_reuse.vetted_helpers(args.parent,args.cache) if latest else args.parent/'scripts'
    dl=load(cache_tools/'ci-prepare.py','root_download')
    if refreshed or newest:
        mode='structural' if structural else 'private'
        arguments = (args.parent,args.cache,api,graph,index,shas,inputs,req,args.bin/'leantar',dl,mode)
        status = verified_batch.certify(newest,*arguments) if newest else refresh.certify(*arguments)
        validation.update(status)
    elif structural:
        from structural_gate import check_actions
        validation.update(check_actions(req,inputs))
    elif latest:
        from native_artifacts import check as check_artifacts
        validation.update(check_artifacts(req,inputs))
    if reused and latest:
        validation.update(current_reuse.check(args.parent,args.cache,api,graph,index,shas,reused,req['head'],args.bin/'leantar',dl))
    elif reused and not refreshed and not newest:
        from csv import DictReader
        check_reuse(args.parent,args.cache,HERE.parent/'import-screen',api,graph,index,shas,source_path,canonical)
        meta=json.loads((HERE.parent/'import-screen/reuse-meta.json').read_bytes())
        with (HERE.parent/'import-screen/reuse.tsv').open() as f:
            eligible={r['module']:r['source_sha256'] for r in DictReader(f,delimiter='\t')}
        if any(r['parent']!=meta['old']['source_tree'] or eligible.get(n)!=r['parent_source'] for n,r in reused.items()):
            raise ValueError('an original compiler result has no current input-equivalence witness')
    levels=import_levels('Main',graph)
    if any(levels.values()):raise ValueError('the final roots now need private or meta project inputs')
    special={dep for edges in graph.values() for dep,_,meta,deep in edges if meta or deep}
    if special & inputs.keys():
        raise ValueError('a candidate has a private or meta project consumer')
    provider_inputs=set().union(*(public_inputs(m,graph) for m in PROVIDERS))
    modules=sorted(levels.keys() | provider_inputs | inputs.keys() | {'Main','Statements'})
    baseline.mkdir();images.mkdir()
    result=[];bindings=[];parent_bytes=candidate_bytes=initial_cached=0
    reader=Blobs(candidate)
    try:
        for offset in range(0,len(modules),32):
            if shutil.disk_usage(args.work).free < 3*(1<<30):
                raise OSError('less than 3 GiB remains before the next stock leantar batch')
            names=modules[offset:offset+32]
            batch=[index[n] for n in names]
            initial_cached+=sum((args.cache/'artifacts'/arc).is_file() for _,_,arc in batch)
            dl.downloads(args.cache,{key:arc for _,key,arc in batch},shas)
            with tempfile.TemporaryDirectory(dir=args.work) as folder:
                rows,unchanged,changed=restore_batch(names,index,shas,args.cache,args.bin/'leantar',args.rebuilder,
                    baseline,images,reader,old_sources,candidate,inputs,bindings,Path(folder),structural)
            result.extend(rows);parent_bytes+=unchanged;candidate_bytes+=changed
            if offset%3200==0:print('source-bound project modules:',offset+len(names),'/',len(modules),flush=True)
    finally:reader.close()
    if {r[0] for r in result}!=inputs.keys():raise ValueError('missing reconstructed images')
    with sqlite3.connect(args.work/'bindings.sqlite') as db:
        db.execute('CREATE TABLE result(module TEXT PRIMARY KEY,public TEXT NOT NULL)')
        db.executemany('INSERT INTO result VALUES(?,?)',bindings)
    table=images/'images.tsv'
    table.write_text(''.join('\t'.join(r)+'\n' for r in sorted(result)))
    report={'source_mode':req.get('source_mode','private-imports'),'parent':req['base'],'parent_source_tree':req['base_src'],'native_reuse':validation,'head':req['head'],'after_src_tree':req['head_src'],'changed':len(inputs),
        'manifest_sha256':file_sha(table),'input_sha256':req['source_provenance_sha256'],'module_manifest':manifest,
        'provider_only_inputs':sorted(provider_inputs-levels.keys()),'visible':len(levels),'candidate_visible':len(inputs.keys()&levels.keys()),'archives':len(modules),
        'complete_candidate_source_blobs':source_count,'complete_candidate_source_bytes':source_bytes,
        'shared_cache_available':initial_cached,'parent_public_bytes':parent_bytes,'candidate_public_bytes':candidate_bytes,
        'ir_signature_and_body_matches':len(result),'remaining_disk_bytes':shutil.disk_usage(args.work).free}
    (images/'bound.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()
