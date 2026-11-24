"""Bind all selected before and after Git blobs to the upstream pull merge."""
import argparse
import gzip
import json
import os
from pathlib import Path
import subprocess
from parent import BASE,sha

def git(repo,*cmd):
    return subprocess.check_output(['git','-C',repo,*cmd])

def check(repo,folder):
    req=json.loads((folder/'request.json').read_bytes())
    commit=req['pull_merge']
    if git(repo,'rev-parse','HEAD').decode().strip()!=commit:
        raise ValueError('unexpected upstream merge checkout')
    if git(repo,'show','-s','--format=%P',commit).decode().strip().split()!=[BASE,req['pull_head']]:
        raise ValueError('the pull merge has different parents')
    if git(repo,'rev-parse',commit+'^{tree}').decode().strip()!=req['candidate_tree'] or git(repo,'rev-parse',commit+':src').decode().strip()!=req['candidate_src_tree']:
        raise ValueError('the native request describes a different candidate tree')
    def blobs(rev):
        data=git(repo,'ls-tree','-rz',rev,'src')
        return {os.fsdecode(path)[4:-5].replace('/','.'):meta.split()[-1].decode()
            for entry in data.split(b'\0') if entry for meta,path in [entry.split(b'\t',1)] if path.endswith(b'.lean')}
    before=blobs(BASE);after=blobs(commit)
    checked=set()
    for name,group in req['groups'].items():
        raw=gzip.decompress((folder/'groups'/(name+'.jsonl.gz')).read_bytes())
        if sha(raw)!=group['sha256']:raise ValueError('the group differs from the reviewed native request')
        members=set()
        for line in raw.splitlines():
            m,row=json.loads(line)
            if m in members or m in checked or [before[m],after[m]]!=row[:2] or row[0]==row[1]:
                raise ValueError('a native input does not bind the exact changed upstream module: '+m)
            members.add(m)
        if len(members)!=group['count']:raise ValueError('wrong group count')
        checked.update(members)
    return {'base':BASE,'merge':commit,'head':req['pull_head'],'source_tree':req['candidate_src_tree'],'different_source_files_checked':len(checked),'groups':len(req['groups'])}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--request',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True);o=p.parse_args()
    report=check(o.repo,o.request);o.out.write_text(json.dumps(report,indent=2)+'\n');print(report)
