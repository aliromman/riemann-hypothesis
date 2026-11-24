"""Compile an exact source transformation and compare all observable parent outputs."""
from __future__ import annotations
import collections, gzip, hashlib, importlib.util, json, os, resource, subprocess, sys, tempfile, time, tomllib
from pathlib import Path
from types import SimpleNamespace
HERE=Path(__file__).resolve().parent
CURRENT=HERE.parent/'current-recheck'
SCREEN=HERE.parent/'import-screen'
sys.path.insert(0,str(CURRENT))
from parent import BASE,TREE,GRAPH,MANIFEST,canonical,restore,sha
from screen import Runner
from lake_imports import project_artifacts
from verify_retained import source_warnings,trace_warnings,run_command
sys.path.insert(0,str(HERE/'recipe'))
from combined import convert,live_counts

FACETS=('.olean','.olean.server','.olean.private','.ir.sig','.ir')
ORDINARY=('.olean','.ir.sig','.ir')
TRANSIENT={'timeout','process-failure','infrastructure','missing-dependency'}

def blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def request_folder(group):
    return HERE/'repairs' if group.startswith('repair-') else HERE

def load_request(group):
    folder=request_folder(group)
    req=json.loads((folder/'request.json').read_bytes())
    if (req['donor'],req['tree'],req['manifest'],req['graph'])!=(BASE,TREE,MANIFEST,GRAPH):
        raise ValueError('parent identity differs')
    for name,digest in req['recipe'].items():
        if sha((HERE/'recipe'/name).read_bytes())!=digest:raise ValueError('source recipe differs: '+name)
    spec=req['groups'][group];raw=gzip.decompress((folder/'groups'/(group+'.jsonl.gz')).read_bytes())
    members={m:(a,b,n,c) for m,a,b,n,c in map(json.loads,raw.splitlines())}
    if sha(raw)!=spec['sha256'] or len(members)!=spec['count'] or len(raw.splitlines())!=len(members):raise ValueError('invalid group manifest')
    return req,spec,members

def import_clump(path,expected):
    if blob(path.read_bytes())!=expected:raise ValueError('unexpected upstream clump reader')
    spec=importlib.util.spec_from_file_location('upstream_clump',path)
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m

def flat(table,prefix=''):
    for key,value in table.items():
        name=prefix+'.'+key if prefix else key
        if isinstance(value,dict):yield from flat(value,name)
        else:yield name,value

class Scope(Runner):
    def __init__(self,o,variants,upstream,exact_sources=None):
        super().__init__(o)
        self.variants=variants
        self.clump=upstream
        self.exact_sources=exact_sources
        config=tomllib.loads((o.repo/'lakefile.toml').read_text())
        self.libraries={lib['name']:dict(flat(lib.get('leanOptions',{}))) for lib in config['lean_lib']}
    def setup(self,m):
        name=self.clump.lib_of(m)
        return dict(name=m,isModule=True,package=self.package,options=self.lean_options|self.libraries[name],plugins=[],dynlibs=[],
                    importArts=project_artifacts(m,self.header_graph,self.art))
    def compare(self,m):
        start=time.monotonic();o=self.o
        before=(o.repo/self.paths[m]).read_bytes()
        src,cand,net,code=self.variants[m]
        if self.exact_sources is None:
            transformed=convert(before.decode(),self.clump)
            if transformed is None:raise ValueError('unrecognized source '+m)
            text,metrics=transformed
            after=text.encode()
        else:
            if len(cand)!=64 or not set(cand)<=set('0123456789abcdef'):raise ValueError('invalid candidate digest')
            after=gzip.decompress((self.exact_sources/(cand+'.lean.gz')).read_bytes())
            old_net,old_code=live_counts(before.decode());new_net,new_code=live_counts(after.decode())
            metrics={'net':old_net-new_net,'code':old_code-new_code}
        if (sha(before),sha(after),metrics['net'],metrics['code'])!=(src,cand,net,code):raise ValueError('transformation differs from exact source manifest: '+m)
        row={'module':m,'source':src,'candidate':cand,'parent_blob':blob(before),'candidate_blob':blob(after),'net':net,'code':code,
             'import_all_or_meta_consumer':m in self.private_users}
        try:
            with tempfile.TemporaryDirectory(dir=o.work/'tmp') as t:
                tmp=Path(t);f=tmp/self.paths[m];f.parent.mkdir(parents=True);f.write_bytes(after)
                setup=tmp/'setup.json';setup.write_bytes(canonical(self.setup(m)));new=tmp/'new.olean'
                cmd=[o.bin/'lean','-j1','--tstack=400000','--root='+str(tmp/'src'),'--setup='+str(setup),'-o',new,'--json',f]
                res=run_command(cmd,self.env,o.timeout,tmp)
                if res.returncode:
                    errors=[]
                    for line in (res.stdout+'\n'+res.stderr).splitlines():
                        if line.startswith('{'):
                            value=json.loads(line)
                            if value.get('severity')=='error':errors.append(value.get('data','')[:800])
                        elif line.strip():errors.append(line[:300])
                    kind='elaboration' if errors else 'process-failure'
                    if any('failed to open file' in s or 'object file' in s and 'does not exist' in s for s in errors):kind='missing-dependency'
                    row.update(status=kind,error=errors[:3],exit=res.returncode)
                else:
                    _,dep,name,digest=self.index[m];archive=o.archives/name
                    if sha(archive.read_bytes())!=digest:raise ValueError('incorrect parent LTAR '+m)
                    row['parent_ltar_sha256']=digest
                    ref=tmp/'old';ir=tmp/'ir';ref.mkdir();ir.mkdir()
                    job={'file':str(archive),'hash':dep,'base':[str(ref),str(ir)]}
                    extract=run_command([o.bin/'leantar','--jobs','1','-f','-x','-j','-'],self.env,90,tmp,json.dumps([job]))
                    if extract.returncode:raise ValueError('stock leantar: '+extract.stderr[-500:])
                    stem=m.rsplit('.',1)[-1];old=ref/(stem+'.olean')
                    judge=run_command([o.judge,m,old,new,tmp],self.env,145,tmp)
                    if judge.returncode not in (0,2):raise ValueError('declaration comparer: '+judge.stderr[-500:])
                    row.update(json.loads(judge.stdout))
                    old_w=trace_warnings(json.loads((ref/(stem+'.trace')).read_bytes()))
                    new_w=source_warnings(res.stdout)
                    row.update(old_warnings=sum(old_w.values()),new_warnings=sum(new_w.values()),
                               old_warning_sha256=sha(canonical(sorted(old_w.items()))),new_warning_sha256=sha(canonical(sorted(new_w.items()))))
                    if old_w!=new_w:row.update(lost=list((old_w-new_w).elements())[:1],added=list((new_w-old_w).elements())[:1])
                    def old_art(ext):
                        ps=[p for p in (ref/(stem+ext),ir/(stem+ext)) if p.is_file()]
                        if len(ps)!=1:raise ValueError('missing or repeated parent facet '+ext)
                        return ps[0]
                    row['parent_facets']={ext:sha(old_art(ext).read_bytes()) for ext in FACETS}
                    row['facets']={ext:sha((tmp/('new'+ext)).read_bytes()) for ext in FACETS}
                    row['raw_different']=[e for e in FACETS if row['parent_facets'][e]!=row['facets'][e]]
                    gate=FACETS if row['import_all_or_meta_consumer'] else ORDINARY
                    passed=(judge.returncode==0 and row['publicImage'] and row['publicImports'] and row['kernelImage'] and
                            row['parentNames']==row['candidateNames'] and row['different']==0 and row['proofChanges']==0 and
                            old_w==new_w and not set(gate).intersection(row['raw_different']))
                    row['status']='pass' if passed else 'difference'
        except subprocess.TimeoutExpired as err:row.update(status='timeout',error=str(err.timeout))
        except (OSError,KeyError,ValueError) as err:row.update(status='infrastructure',error=str(err)[:650])
        row['seconds']=round(time.monotonic()-start,3)
        return row
