"""Bind the stock source checkout to the live upstream pull request."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
from manifest import read_request

UPSTREAM='leanprover-community/riemann-hypothesis'
def actual_base(number,main,head):
    with tempfile.TemporaryDirectory() as temporary:
        repo=Path(temporary)/'ancestry.git'
        subprocess.run(['git','init','--quiet','--bare',repo],check=True)
        def git(*args):
            return subprocess.check_output(['git','-C',repo,*args],text=True).strip()
        git('fetch','--quiet','--no-tags','--filter=tree:0','https://github.com/'+UPSTREAM+'.git',
            'refs/heads/main:refs/heads/main',f'refs/pull/{number}/head:refs/heads/candidate')
        if (git('rev-parse','refs/heads/main'),git('rev-parse','refs/heads/candidate'))!=(main,head):
            raise ValueError('a live Git revision changed during the ancestry check')
        return git('merge-base','refs/heads/main','refs/heads/candidate')

def snapshot(folder):
    req,_=read_request(folder)
    def get(path):
        return json.loads(subprocess.check_output(['gh','api','-H','Cache-Control: no-cache','repos/'+UPSTREAM+'/'+path]))
    pr=get('pulls/'+str(req['pull_request']))
    base=pr['base']
    current=get('branches/main')['commit']['sha']
    live=pr['head']['sha']
    if base['repo']['full_name']!=UPSTREAM or base['ref']!='main' or pr['head']['repo']['full_name']!='aliromman/riemann-hypothesis':
        raise ValueError('the live upstream pull request differs from the reviewed request')
    mode=req.get('revision','current head')
    if mode=='first published commit':
        first,=get('pulls/'+str(pr['number'])+'/commits?per_page=1')
        if first['sha']!=req['head'] or [p['sha'] for p in first['parents']]!=[req['base']]:
            raise ValueError('the first published commit differs from the request or its upstream parent')
    elif live!=req['head']:
        raise ValueError('the live head differs from the reviewed commit')
    parent=current if current==req['base'] and current==base['sha'] else actual_base(pr['number'],current,live)
    if parent!=req['base']:raise ValueError('the actual pull request merge base differs from the attested parent')
    return {'number':pr['number'],'url':pr['html_url'],'base':parent,'main_at_check':current,'head':req['head'],
            'live_pull_head':live,'revision':mode,
            'head_repository':pr['head']['repo']['full_name'],'head_ref':pr['head']['ref'],'state':pr['state']}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--request',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--step-output',action='store_true')
    o=p.parse_args()
    info=snapshot(o.request)
    o.out.parent.mkdir(exist_ok=True,parents=True)
    o.out.write_text(json.dumps(info,indent=2)+'\n')
    if o.step_output:
        with open(os.environ['GITHUB_OUTPUT'],'a') as f:
            for key in ('number','base','head'):print(key+'='+str(info[key]),file=f)
    print(info)
