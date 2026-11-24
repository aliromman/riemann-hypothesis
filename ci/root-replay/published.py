"""Bind the stock source checkout to the live upstream pull request."""
import argparse
import json
import os
from pathlib import Path
import subprocess
from manifest import read_request

UPSTREAM='leanprover-community/riemann-hypothesis'
def snapshot(folder):
    req,_=read_request(folder)
    def get(path):
        return json.loads(subprocess.check_output(['gh','api','-H','Cache-Control: no-cache','repos/'+UPSTREAM+'/'+path]))
    pr=get('pulls/'+str(req['pull_request']))
    base=pr['base']
    current=get('branches/main')['commit']['sha']
    if base['repo']['full_name']!=UPSTREAM or base['ref']!='main' or pr['head']['sha']!=req['head'] or base['sha']!=req['base'] or current!=req['base']:
        raise ValueError('the live upstream pull head or latest community main differs from the reviewed request')
    return {'number':pr['number'],'url':pr['html_url'],'base':current,'head':pr['head']['sha'],
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
