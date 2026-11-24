"""Stock artifact reconstruction functions used by the local source-bound verifier."""
from __future__ import annotations
import hashlib, os, subprocess, tempfile
from pathlib import Path

def digest(raw):return hashlib.sha256(raw).hexdigest()

def file_sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def git(repo,*cmd):
    return subprocess.check_output(['git','-C',repo,*cmd])

def tree(repo,rev):return git(repo,'rev-parse',rev+':src').decode().strip()

def ls(repo,rev):
    result={}
    for row in git(repo,'ls-tree','-r','-z',rev,'src').split(b'\0'):
        if row:
            meta,path=row.split(b'\t',1);result[os.fsdecode(path)]=meta.split(b' ')[-1].decode()
    return result

class Blobs:
    def __init__(self,repo):
        self.p=subprocess.Popen(['git','-C',repo,'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def read(self,oid):
        self.p.stdin.write((oid+'\n').encode());self.p.stdin.flush()
        found,kind,size=self.p.stdout.readline().split()
        if found.decode()!=oid or kind!=b'blob':raise ValueError('unexpected Git object for '+oid)
        data=self.p.stdout.read(int(size))
        if len(data)!=int(size) or self.p.stdout.read(1)!=b'\n':raise ValueError('incomplete Git blob')
        return data
    def close(self):
        self.p.stdin.close()
        if self.p.wait():raise RuntimeError('Git object reader failed')

def header(lines):
    for i,line in enumerate(lines):
        if line.strip() and line not in (b'module\n',b'prelude\n') and not line.startswith((b'import ',b'public import ',b'meta import ',b'public meta import ')):
            return lines[:i],lines[i:]
    return lines,[]

def hosted_batch(jobs,parents,opt):
    nbytes=0
    if not jobs:return nbytes
    with tempfile.TemporaryDirectory(dir=opt.out) as wd:
        tmp=Path(wd);tsv=[];outputs=[]
        for i,(m,old,new,dst,facets) in enumerate(jobs):
            parent,*ir=parents.inputs(m,tmp/(str(i)+'-parent'))
            a=tmp/(str(i)+'.orig.lean');b=tmp/(str(i)+'.new.lean');out=tmp/(str(i)+'.olean')
            a.write_bytes(old);b.write_bytes(new)
            sig=tmp/(str(i)+'.ir.sig');body=tmp/(str(i)+'.ir')
            extra=[*ir,sig,body] if opt.audit_ir else []
            tsv.append('\t'.join(map(str,[m,parent,a,b,out,*extra])));outputs.append((m,out,sig,body,dst,facets))
        f=tmp/'rows';f.write_text('\n'.join(tsv)+'\n')
        p=subprocess.run([opt.rebuilder,f],capture_output=True,text=True)
        if p.returncode:raise ValueError('pinned parser/serializer failed: '+p.stderr[:1500])
        for m,out,sig,body,dst,facets in outputs:
            if file_sha(out)!=facets['.olean']:raise ValueError('reconstructed image does not match the actual hosted compiler image: '+m)
            if opt.audit_ir:
                actual_sig=file_sha(sig);actual_ir=file_sha(body)
                opt.ir_results[m]=(facets['.ir.sig'],actual_sig,facets['.ir'],actual_ir)
            nbytes+=out.stat().st_size
            if not opt.plan_only:
                dst.parent.mkdir(parents=True,exist_ok=True);out.replace(dst)
    return nbytes
