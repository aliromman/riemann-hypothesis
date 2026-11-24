"""Fresh stock Lean comparison of the exact reviewed candidate source bytes."""
from __future__ import annotations
import difflib,hashlib,json,os,subprocess,tempfile,time
from pathlib import Path
from parent import HERE,SCREEN,canonical
import sys
sys.path.insert(0,str(HERE.parent/'root-replay'))
from native import header
from screen import Runner
from verify_retained import run_command,sha,source_warnings,trace_warnings

def git_blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

class Exact(Runner):
    def __init__(self,opt,variants):
        super().__init__(opt)
        self.variants=variants

    @staticmethod
    def difference(before,after,which):
        edits=[]
        for op,a,b,c,d in difflib.SequenceMatcher(None,before,after,autojunk=False).get_opcodes():
            if op=='equal':continue
            for line in (before[a:b],after[c:d])[which]:
                if not line.startswith(b'import Mathlib.') or not line.endswith(b'\n'):
                    raise ValueError('unsupported source change')
                edits.append(line[7:-1].decode())
        return edits

    def run(self, m):
        start=time.monotonic();o=self.o
        orig=(o.repo/self.paths[m]).read_bytes()
        old_blob,new_blob,old_sha,new_sha,new_header,removed,added=self.variants[m]
        before,body=header(orig.splitlines(keepends=True))
        proposed=new_header.encode()+b''.join(body)
        if (sha(orig)!=old_sha or sha(proposed)!=new_sha or git_blob(orig)!=old_blob or git_blob(proposed)!=new_blob):
            raise ValueError('the actual parent source or generated candidate differs from its Git blob: '+m)
        if removed!=self.difference(before,new_header.encode().splitlines(keepends=True),0) or added!=self.difference(before,new_header.encode().splitlines(keepends=True),1):
            raise ValueError('the native input does not implement the approved private Mathlib header edits: '+m)
        r={'module':m,'source':old_sha,'candidate':new_sha,'n':len(removed),'removed':removed,'added_imports':added}
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
                r.update(old_warning_sha256=sha(canonical(sorted(before.items()))),new_warning_sha256=sha(canonical(sorted(after.items()))))
                if after!=before:r.update(added=list((after-before).elements())[:1],lost=list((before-after).elements())[:1])
                if status == 'pass':
                    r['facets']={ext:sha((tmp/('new'+ext)).read_bytes())
                                 for ext in ('.olean','.olean.server','.olean.private','.ir','.ir.sig')}
                return r
        except subprocess.TimeoutExpired as error:
            return r|{'status':'timeout','seconds':round(time.monotonic()-start,3),'error':str(error.timeout)}
        except (OSError,ValueError,KeyError) as error:
            return r|{'status':'infrastructure','error':str(error)[:520],'seconds':round(time.monotonic()-start,3)}
