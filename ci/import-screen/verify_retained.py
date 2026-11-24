"""Re-elaborate each proposed header with stock Lean and compare the compiled module."""
from __future__ import annotations
import argparse, collections, concurrent.futures, functools, hashlib, json, os, re, resource
import io, lzma, sqlite3, subprocess, tarfile, tempfile, time
from pathlib import Path


def args():
    p = argparse.ArgumentParser()
    for name in ('repo', 'work', 'headers', 'targets', 'index', 'archives', 'baseline', 'packages', 'bin', 'judge'):
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--namespace', default='Development')
    p.add_argument('--workers', type=int, default=8)
    p.add_argument('--limit', type=int)
    p.add_argument('--timeout', type=int, default=180)
    p.add_argument('--modules', type=Path)
    p.add_argument('--shard', type=int, default=0)
    p.add_argument('--shards', type=int, default=1)
    p.add_argument('--retry', action='store_true')
    return p.parse_args()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def project_paths(repo):
    raw = subprocess.check_output(['git', 'ls-files', '-z', 'src/*.lean'], cwd=repo)
    return {p[4:-5].replace('/', '.'): Path(p) for p in os.fsdecode(raw).split('\0') if p}


def prune(source, targets):
    lines = source.splitlines(keepends=True)
    removed = []
    header = []
    for i, line in enumerate(lines):
        if not line.strip() or line in (b'module\n', b'prelude\n'):
            header.append(line)
        elif line.startswith((b'import ', b'public import ', b'meta import ', b'public meta import ')):
            if line in targets:
                removed.append(line[7:-1].decode())
            else:
                header.append(line)
        else:
            return b''.join(header + lines[i:]), removed
    return b''.join(header), removed


def normalized_warning(message):
    return re.sub(r'^(?:.*?\.lean:)?[0-9]+:[0-9]+:\s*', '', message.strip())


def source_warnings(log):
    msgs = []
    for ln in log.splitlines():
        if not ln.startswith('{'):
            continue
        rec = json.loads(ln)
        if rec.get('severity') == 'warning':
            msgs.append(normalized_warning(rec['data']))
    return collections.Counter(msgs)


def trace_warnings(trace):
    return collections.Counter(normalized_warning(r['message']) for r in trace.get('log', []) if r['level'] == 'warning')


def run_command(command, env, timeout, cwd, stdin=None):
    return subprocess.run(command, input=stdin, env=env, cwd=cwd, capture_output=True,
                          text=True, errors='replace', timeout=timeout)


class Check:
    def __init__(self, opt):
        self.o = opt
        self.paths = project_paths(opt.repo)
        self.raw_targets = {b'import ' + x.encode() + b'\n' for x in opt.targets.read_text().splitlines()}
        graph = json.loads(opt.headers.read_bytes())
        self.graph = {m: [(n, meta, all_) for n, _, meta, all_ in graph.get(m, ()) if n in self.paths] for m in self.paths}
        self.private_users = {n for edges in self.graph.values() for n, meta, all_ in edges if meta or all_}
        self.index = {r[0]: r for r in json.loads(opt.index.read_bytes())}
        self.art = {}
        for m, path in self.paths.items():
            stem = str(opt.baseline / Path(*path.parts[1:]).with_suffix(''))
            self.art[m] = [[stem + '.olean', stem + '.olean.server'], [stem + '.ir.sig', stem + '.ir']]
        packages = [p/'.lake/build/lib/lean' for p in opt.packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
        self.env = os.environ | {'PATH': str(opt.bin)+os.pathsep+os.environ['PATH'],
            'LEAN_PATH': os.pathsep.join(map(str, [opt.baseline, *packages, opt.bin.parent/'lib/lean'])),
            'LEAN_NUM_THREADS': '1', 'LEAN_ABORT_ON_PANIC': '1', 'LAKE_ARTIFACT_CACHE': 'false'}

    def setup(self, m):
        # This supplies the same public project facets used by Lake for an ordinary import.
        # Direct import-all chains also need the private facet.
        seen = {}; todo = [k for k, _, _ in self.graph[m]]
        while todo:
            n = todo.pop()
            if n in seen: continue
            seen[n] = self.art[n]
            todo.extend(k for k, _, _ in self.graph[n] if k not in seen)
        todo = [k for k, _, all_ in self.graph[m] if all_]; private = set()
        while todo:
            n = todo.pop()
            if n in private: continue
            private.add(n); public, ir = seen[n]
            seen[n] = [public + [public[0]+'.private'], ir]
            todo.extend(k for k, _, all_ in self.graph[n] if all_)
        opts={'relaxedAutoImplicit':False,'autoImplicit':False,'pp.unicode.fun':True,'maxSynthPendingDepth':3,'maxHeartbeats':4000000}
        if m.startswith(('GroundTheory.LocalFields.','GroundTheory.GlobalFields.')):opts['synthInstance.maxHeartbeats']=400000
        return dict(name=m,isModule=True,package='tree',options=opts,plugins=[],dynlibs=[],importArts=seen)

    def run(self, m):
        start=time.monotonic(); o=self.o; orig=(o.repo/self.paths[m]).read_bytes(); proposed,removed=prune(orig,self.raw_targets)
        r={'module':m,'source':sha(orig),'candidate':sha(proposed),'n':len(removed),'removed':removed}
        if not removed: return r|{'status':'none'}
        if m in self.private_users: return r|{'status':'private-use'}
        try:
            with tempfile.TemporaryDirectory(dir=o.work/'tmp') as tmp_name:
                tmp=Path(tmp_name); src=tmp/self.paths[m];src.parent.mkdir(parents=True);src.write_bytes(proposed)
                setup=tmp/'module.setup.json';setup.write_text(json.dumps(self.setup(m),separators=(',',':')))
                fresh=tmp/'new.olean';cmd=[o.bin/'lean','-j1','--tstack=400000','--root='+str(tmp/'src'),'--setup='+str(setup),'-o',fresh,'--json',src]
                result=run_command(cmd,self.env,o.timeout,tmp)
                if result.returncode:
                    messages=[]
                    for ln in (result.stdout+'\n'+result.stderr).splitlines():
                        if ln.startswith('{'):
                            entry=json.loads(ln)
                            if entry.get('severity')=='error':messages.append(entry.get('data','')[:450])
                        elif ln.strip():messages.append(ln[:360])
                    kind='missing-dependency' if any('failed to open file' in l or 'object file' in l and 'does not exist' in l for l in messages) else 'elaboration'
                    return r|{'status':kind,'error':messages[:2],'seconds':round(time.monotonic()-start,3)}
                _,dep,name,digest=self.index[m]; archive=o.archives/name
                if sha(archive.read_bytes())!=digest:raise ValueError('parent archive digest mismatch '+name)
                ref=tmp/'parent';ir=tmp/'ir';ref.mkdir();ir.mkdir()
                job={'file':str(archive),'hash':dep,'base':[str(ref),str(ir)]}
                extract=run_command([o.bin/'leantar','--jobs','1','-f','-x','-j','-'],self.env,60,tmp,json.dumps([job]))
                if extract.returncode:raise ValueError('leantar: '+extract.stderr[:350])
                stem=m.rsplit('.',1)[-1];parent=ref/(stem+'.olean');trace=json.loads((ref/(stem+'.trace')).read_bytes());after=source_warnings(result.stdout);before=trace_warnings(trace)
                out=run_command([o.judge,m,parent,fresh,tmp],self.env,55,tmp)
                if out.returncode not in (0,2):raise ValueError('interface checker: '+out.stderr[-400:])
                cert=json.loads(out.stdout.strip());r.update(cert)
                status='pass' if not out.returncode else 'declarations'
                if after!=before:status='diagnostics'
                r.update(status=status,old_warnings=sum(before.values()),new_warnings=sum(after.values()),seconds=round(time.monotonic()-start,3))
                if after!=before:r.update(added=list((after-before).elements())[:1],lost=list((before-after).elements())[:1])
                if status == 'pass':
                    packed = o.work/'certified'/Path(*m.split('.')).with_suffix('.tar.xz')
                    packed.parent.mkdir(parents=True, exist_ok=True)
                    partial = packed.with_suffix('.partial')
                    digests = {}
                    with lzma.open(partial, 'wb', preset=0) as zipped, tarfile.open(fileobj=zipped, mode='w|') as tar:
                        for suffix in ('.olean','.olean.server','.olean.private','.ir','.ir.sig'):
                            raw = (tmp/('new'+suffix)).read_bytes()
                            digests[suffix] = sha(raw)
                            info = tarfile.TarInfo('module'+suffix)
                            info.size = len(raw)
                            tar.addfile(info, io.BytesIO(raw))
                    partial.replace(packed)
                    r.update(facets=digests, packed_bytes=packed.stat().st_size)
                return r
        except subprocess.TimeoutExpired as error:
            return r|{'status':'timeout','seconds':round(time.monotonic()-start,3),'error':str(error.timeout)}
        except (OSError,ValueError,KeyError) as error:
            return r|{'status':'infrastructure','error':str(error)[:520],'seconds':round(time.monotonic()-start,3)}


def main():
    o=args()
    for key in ('repo','work','headers','targets','index','archives','baseline','packages','bin','judge'):
        setattr(o,key,getattr(o,key).resolve())
    o.work.mkdir(parents=True,exist_ok=True);(o.work/'tmp').mkdir(exist_ok=True)
    soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft<1600:resource.setrlimit(resource.RLIMIT_NOFILE,(min(2400,hard) if hard!=-1 else 2400,hard))
    checker=Check(o);db=sqlite3.connect(o.work/'results.sqlite');db.execute('PRAGMA journal_mode=WAL');db.execute('CREATE TABLE IF NOT EXISTS results(module TEXT PRIMARY KEY, status TEXT, n INTEGER, data TEXT)');db.execute('CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY,value TEXT)')
    spec={'tree':subprocess.check_output(['git','rev-parse','HEAD:src'],cwd=o.repo,text=True).strip(),'targets':sha(o.targets.read_bytes()),'worker':sha(Path(__file__).read_bytes()),'toolchain':subprocess.check_output([o.bin/'lean','--version'],text=True).strip(),'index':sha(o.index.read_bytes()),'judge':sha(o.judge.read_bytes())};val=json.dumps(spec,sort_keys=True)
    got=db.execute("SELECT value FROM meta WHERE key='scope'").fetchone()
    if got and got[0]!=val:raise RuntimeError('work directory contains results for different proof inputs')
    db.execute("INSERT OR IGNORE INTO meta VALUES('scope',?)",(val,));db.commit()
    done={m for (m,) in db.execute('SELECT module FROM results' + (" WHERE status IN ('pass','none','private-use')" if o.retry else ''))}
    modules=o.modules.read_text().splitlines() if o.modules else [m for m in checker.paths if m.startswith(o.namespace+'.')]
    modules=sorted(modules,key=lambda m:hashlib.sha256(m.encode()).digest());modules=modules[o.shard::o.shards]
    if o.limit:modules=modules[:o.limit]
    modules=[m for m in modules if m not in done];print('modules',len(modules),'already checked',len(done),'workers',o.workers,flush=True)
    stats=collections.Counter();saved=0;start=time.monotonic();count=0
    with concurrent.futures.ThreadPoolExecutor(o.workers) as pool:
        remaining=iter(modules);running={}
        def refill():
            while len(running)<2*o.workers:
                m=next(remaining,None)
                if m is None:break
                running[pool.submit(checker.run,m)]=m
        refill()
        while running:
            active,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in active:
                m=running.pop(future);r=future.result();stats[r['status']]+=1;count+=1
                if r['status']=='pass':saved+=r['n']
                db.execute('INSERT OR REPLACE INTO results VALUES(?,?,?,?)',(m,r['status'],r['n'],json.dumps(r,ensure_ascii=False)))
            db.commit();refill()
            if count//100!=(count-len(active))//100 or count==len(modules):print(count,dict(stats),'accepted import lines',saved,'elapsed seconds',round(time.monotonic()-start),flush=True)
    db.close()

if __name__=='__main__':main()
