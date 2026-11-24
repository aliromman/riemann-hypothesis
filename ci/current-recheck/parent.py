"""Bind the stock parent archives to the source and package pins."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
HERE=Path(__file__).resolve().parent
SCREEN=HERE.parent/'import-screen'
sys.path.insert(0,str(SCREEN))
from prepare import load,canonical,graph_from_source
from lake_imports import import_levels
from runtime.decode import unpack
BASE='343b1de38bbe4c5c66f1c1c0afd7c34e8645acdf'
TREE='70327238ca7c4189479eee72f3c22812f1922329'
MANIFEST='18bf99f19a3357168a83dd5bb70bfb1836134646fb27bac2419611778c15bb2a'
GRAPH='1eea63e656493b1d5f30ab34bd8b913ab3edadc2d615e2313e471196749941a4'
def sha(data):return hashlib.sha256(data).hexdigest()
def published(parent,cache,remote):
    api=load(parent/'scripts/ci-cache-get.py','community')
    if api.git(parent,'rev-parse','HEAD')!=BASE:raise ValueError('incorrect parent revision')
    identity=api.current_identity(parent)
    if identity['source_tree']!=TREE or identity['toolchain']!='leanprover/lean4:v4.37.0-rc1':
        raise ValueError('parent source or toolchain differs')
    meta=cache/'metadata';meta.mkdir(exist_ok=True,parents=True)
    def get(key,limit):
        path=meta/Path(key).name
        if remote:
            data=api.fetch(key,limit)
            if data is None:raise ValueError('missing official cache input: '+key)
            path.write_bytes(data)
        return path.read_bytes()
    receipt=get('ci/revisions/'+BASE+'.json',api.MAX_RECEIPT)
    record=api.matching_record(receipt,identity)
    if not record or record['candidate_head']!=BASE or record['module_manifest_sha256']!=MANIFEST:
        raise ValueError('published manifest does not certify the stock parent')
    _,hashes,rows=api.validated_blobs(record,identity,fetcher=get)
    return api,{r[0]:r for r in rows},hashes

def seed(parent,cache):
    api,rows,hashes=published(parent,cache,True)
    graph=canonical(graph_from_source(parent,rows))
    if sha(graph)!=GRAPH:raise ValueError('stock source graph differs')
    (cache/'metadata/current-headers.json').write_bytes(graph)
    accepted={r[2] for r in rows.values()}
    archives=cache/'artifacts';archives.mkdir(exist_ok=True)
    for path in archives.iterdir():
        if path.name.endswith('.ltar') and path.name not in accepted:path.unlink()
    ready=sum((archives/n).is_file() for n in accepted)
    print('parent modules',len(rows),'existing named archives',ready,'missing',len(accepted)-ready,flush=True)
    upstream=load(parent/'scripts/ci-prepare.py','upstream_download')
    latest=list(rows.values())
    for off in range(0,len(latest),32):
        batch=latest[off:off+32]
        upstream.downloads(cache,{key:archive for _,key,archive in batch},hashes)
    print('verified full parent archive set',len(accepted),flush=True)

def restore(parent,cache,work,roots,leantar):
    api,rows,hashes=published(parent,cache,False)
    data=(cache/'metadata/current-headers.json').read_bytes()
    if sha(data)!=GRAPH:raise ValueError('invalid authenticated project graph')
    graph=json.loads(data)
    parents=set(roots);deep=set()
    for root in roots:
        flags=import_levels(root,graph);parents.update(flags);deep.update(n for n,f in flags.items() if f&1)
    names=sorted(parents)
    src=lambda n:'src/'+n.replace('.','/')+'.lean'
    sparse=['/scripts/','/lakefile.toml','/lake-manifest.json','/lean-toolchain']+['/'+src(n) for n in names]
    subprocess.run(['git','-C',parent,'sparse-checkout','set','--no-cone','--stdin'],input='\n'.join(sparse)+'\n',text=True,check=True)
    build=parent/'.lake/build'
    if any((build/'lib/lean').rglob('*.olean')):raise ValueError('parent already has project sources built')
    selected=[rows[n] for n in names]
    for _,_,a in selected:
        p=cache/'artifacts'/a
        if p.is_symlink() or not p.is_file():raise ValueError('missing stock LTAR: '+a)
        with p.open('rb') as f:
            if hashlib.file_digest(f,'sha256').hexdigest()!=hashes[a]:raise ValueError('incorrect stock LTAR: '+a)
    jobs=api.unpack_jobs(parent,cache,selected)
    for off in range(0,len(jobs),32):
        if shutil.disk_usage(work).free<2*(1<<30):raise OSError('insufficient scratch for the next leantar batch')
        unpack(leantar,['--jobs','2','-f','-x','-j','-'],jobs[off:off+32])
        for n in names[off:off+32]:
            stem=Path(*n.split('.'));pub=build/'lib/lean'/stem
            for ext in ('.c','.bc'):(build/'ir'/stem).with_suffix(ext).unlink(missing_ok=True)
            for ext in ('.ilean','.trace'):pub.with_suffix(ext).unlink(missing_ok=True)
            if n not in deep:pub.with_suffix('.olean.private').unlink(missing_ok=True)
    (work/'index.json').write_bytes(canonical([[n,k,a,hashes[a]] for n,k,a in selected]))
    return len(names)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--parent',type=Path,required=True);p.add_argument('--cache',type=Path,required=True)
    a=p.parse_args();seed(a.parent.resolve(),a.cache.resolve())
