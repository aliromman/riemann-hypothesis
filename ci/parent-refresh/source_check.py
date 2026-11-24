"""Compile exact Git sources against one official Lean and Mathlib parent."""
import argparse
from collections import Counter
import gzip
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import tempfile
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
CURRENT = HERE.parent / 'current-recheck'
STRUCT = HERE.parent / 'structural-screen'
SCREEN = HERE.parent / 'import-screen'
ROOT = HERE.parent / 'root-replay'
sys.path[:0] = [str(CURRENT), str(STRUCT), str(ROOT), str(SCREEN)]
from parent import Authority, canonical, restore, sha
from native import git, header, ls, tree
from native_candidate import Exact, git_blob
from check import Scope, import_clump
from run import run_group
from receipts import TRANSIENT

COMPILER = '0b77e12952ad39077d80d8bd6b66d601f225c321'
ORDINARY = ('.olean', '.ir.sig', '.ir')

def checks():
    tools=(Path(__file__), CURRENT/'parent.py', CURRENT/'native_candidate.py', CURRENT/'run.py',
           STRUCT/'check.py', ROOT/'BuildPublic.lean', ROOT/'native.py', SCREEN/'CheckInterface.lean', SCREEN/'lake_imports.py',
           SCREEN/'screen.py', SCREEN/'verify_retained.py', SCREEN/'receipts.py')
    return {str(p.relative_to(HERE.parent)):sha(p.read_bytes()) for p in tools}

def source_path(name):
    return Path('src', *name.split('.')).with_suffix('.lean')

def source_sparse(repo, modules):
    rules=['/lean-toolchain','/lake-manifest.json','/lakefile.toml']+['/'+str(source_path(n)) for n in modules]
    subprocess.run(['git','-C',repo,'sparse-checkout','set','--no-cone','--stdin'],text=True,input='\n'.join(rules)+'\n',check=True)

def validate_git(parent, reviewed, auth, task, modules):
    if git(parent,'rev-parse','HEAD').decode().strip()!=auth.base or tree(parent,auth.base)!=auth.tree:
        raise ValueError('parent checkout differs from its official source')
    head=task['head']
    if git(reviewed,'rev-parse','HEAD').decode().strip()!=head or tree(reviewed,head)!=task['src']:
        raise ValueError('candidate does not match its reviewed Git source')
    git(reviewed,'merge-base','--is-ancestor',auth.base,head)
    for path in ('lean-toolchain','lakefile.toml','lake-manifest.json'):
        if git(parent,'rev-parse',auth.base+':'+path)!=git(reviewed,'rev-parse',head+':'+path):
            raise ValueError('candidate changed its compiler inputs '+path)
    old=ls(parent,auth.base)
    new=ls(reviewed,head)
    for n,r in modules.items():
        p=str(source_path(n))
        if tuple(r[:2])!=(old.get(p),new.get(p)) or r[0]==r[1]:
            raise ValueError('candidate Git blob binding differs at '+n)

def actual_variants(o, modules, mode):
    store=o.work/'candidate-blobs'
    if mode=='structural':store.mkdir(exist_ok=True)
    result={}
    for n,row in modules.items():
        p=source_path(n)
        before=(o.parent/p).read_bytes();after=(o.reviewed/p).read_bytes()
        if [git_blob(before),git_blob(after),sha(before),sha(after)]!=row[:4]:
            raise ValueError('source bytes differ from the reviewed Git objects: '+n)
        if mode=='structural':
            (store/(row[3]+'.lean.gz')).write_bytes(gzip.compress(after,compresslevel=1,mtime=0))
            result[n]=[row[2],row[3],row[4],row[5]]
        else:
            old_h,old_body=header(before.splitlines(keepends=True));new_h,new_body=header(after.splitlines(keepends=True))
            if old_body!=new_body: raise ValueError('body changed outside private imports: '+n)
            removed=Exact.difference(old_h,new_h,0);added=Exact.difference(old_h,new_h,1)
            if [len(removed),len(added)]!=row[4:]:raise ValueError('private import counts do not match the exact file: '+n)
            result[n]=[*row[:4],b''.join(new_h).decode(),removed,added]
    return result,store

class PrivateOutputs:
    def __init__(self, checker, options, variants):
        self.checker=checker
        self.options=options
        self.variants=variants

    def run(self,n):
        row=self.checker.run(n)
        row['parent_blob'],row['candidate_blob']=self.variants[n][:2]
        if row['status']!='pass':
            return row
        o=self.options
        root=o.parent/'.lake/build/lib/lean'/Path(*n.split('.'))
        actual=row['facets']
        with tempfile.TemporaryDirectory(dir=o.work/'tmp') as temp:
            tmp=Path(temp)
            paths=[tmp/('projected'+suffix) for suffix in ORDINARY]
            binding=[n,root.with_suffix('.olean'),o.parent/source_path(n),o.reviewed/source_path(n),paths[0],
                     root.with_suffix('.ir.sig'),root.with_suffix('.ir'),*paths[1:]]
            jobs=tmp/'sources.tsv';jobs.write_text('\t'.join(map(str,binding))+'\n')
            run=subprocess.run([o.rebuilder,jobs],capture_output=True,text=True)
            if run.returncode:
                return row|{'status':'infrastructure','error':'private import serializer: '+run.stderr[-700:]}
            expected={s:sha(p.read_bytes()) for s,p in zip(ORDINARY,paths)}
        row['parent_ltar_sha256']=self.checker.index[n][3]
        row['parent_public_ir']={s:sha(root.with_suffix(s).read_bytes()) for s in ORDINARY}
        row['projected_public_ir']=expected
        row['projection_differences']=[s for s in ORDINARY if actual[s]!=expected[s]]
        if row['projection_differences'] or not row['kernelImage'] or row['proofChanges']:
            row['status']='difference'
        return row

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--group',required=True)
    parser.add_argument('--request',required=True,type=Path)
    for flag in ('parent','reviewed','cache','work','resume','bin','judge','rebuilder'):
        parser.add_argument('--'+flag,type=Path,required=True)
    parser.add_argument('--budget-minutes',type=int,default=242)
    o=parser.parse_args()
    for key,value in vars(o).items():
        if isinstance(value,Path):setattr(o,key,value.resolve())
    o.work.mkdir(exist_ok=True,parents=True);(o.work/'tmp').mkdir(exist_ok=True)
    auth=Authority.read(HERE/'authority.json')
    req=json.loads((o.request/'request.json').read_bytes())
    if req['authority']!=dict(auth._asdict()):raise ValueError('request changed its authenticated parent')
    group=req['groups'][o.group];kind=group['task'];task=req['tasks'][kind]
    raw=gzip.decompress((o.request/'groups'/(o.group+'.jsonl.gz')).read_bytes())
    modules=dict(map(json.loads,raw.splitlines()))
    if sha(raw)!=group['sha256'] or len(modules)!=group['count'] or len(modules)!=len(raw.splitlines()):
        raise ValueError('native group has incorrect source bindings')
    validate_git(o.parent,o.reviewed,auth,task,modules)
    source_sparse(o.reviewed,modules)
    consumed=restore(o.parent,o.cache,o.work,modules,o.bin/'leantar',auth)
    variants,store=actual_variants(o,modules,kind)
    local=SimpleNamespace(repo=o.parent,work=o.work,headers=o.cache/'metadata/current-headers.json',targets=SCREEN/'targets.txt',
                          index=o.work/'index.json',archives=o.cache/'artifacts',baseline=o.parent/'.lake/build/lib/lean',
                          packages=o.parent/'.lake/packages',bin=o.bin,judge=o.judge,timeout=group['timeout'])
    if kind=='private':
        checker=PrivateOutputs(Exact(local,variants),o,variants)
    elif kind=='structural':
        clump=import_clump(o.parent/'scripts/clump.py',task['upstream_clump_blob'])
        check=Scope(local,variants,clump,store)
        checker=SimpleNamespace(run=check.compare)
    else:raise ValueError('unknown proposal kind')
    def match(z,_):
        r=modules[z['module']]
        return [z['parent_blob'],z['candidate_blob'],z['source'],z['candidate']]==r[:4]
    version=subprocess.check_output([o.bin/'lean','--version'],text=True).strip()
    if COMPILER not in version:raise ValueError('incorrect native compiler')
    scope={'group':o.group,'task':kind,'roots':len(modules),'parent':auth.base,'donor':auth.base,'tree':auth.tree,
           'graph':auth.graph,'manifest':auth.manifest,'source_head':task['head'],'candidate_tree':task['src'],
           'source_transitions_sha256':group['sha256'],'project_inputs':consumed}
    (o.work/'scope.json').write_bytes(canonical(scope))
    domain={'scope':scope,'helpers':checks(),'compiler':version}
    soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft<2400:resource.setrlimit(resource.RLIMIT_NOFILE,(2400 if hard==resource.RLIM_INFINITY else min(hard,2400),hard))
    rows,resumed,elapsed=run_group(checker,o.group,variants,o.work,o.resume,domain,o.budget_minutes*60,group['workers'],match)
    statuses=Counter(r['status'] for r in rows.values())
    report=domain|dict(checked=len(rows),pending=len(modules)-len(rows),resumed=resumed,statuses=statuses,
                       seconds=round(elapsed,3),workers=group['workers'],native_threads=1,machine=platform.platform(),
                       workflow_sha=os.environ.get('GITHUB_SHA'),result_sha=sha((o.work/'results.jsonl').read_bytes()))
    (o.work/'report.json').write_bytes(canonical(report));print(report,flush=True)
    if report['pending'] or set(statuses)&TRANSIENT:raise SystemExit('incomplete checked source group')

if __name__=='__main__':main()
