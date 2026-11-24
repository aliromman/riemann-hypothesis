"""Bind the scoped check to the published source branch, parent and dependency pins."""
import json,os,re,subprocess,sys,tempfile
from pathlib import Path
def git(root,*args):return subprocess.check_output(['git','-C',root,*args],text=True).strip()
def bind(candidate,parent,work,request):
    req=json.loads(request.read_bytes())
    comparison=req['parent'];head=req['source_head'];checked=req['checked_commit']
    if req['source_repository']!='aliromman/riemann-hypothesis' or not re.fullmatch('refs/heads/[a-zA-Z0-9._/-]+',req['source_ref']):
        raise ValueError('unexpected source fork or branch')
    upstream='https://github.com/leanprover-community/riemann-hypothesis.git';fork='https://github.com/aliromman/riemann-hypothesis.git'
    if git(candidate,'rev-parse','HEAD')!=checked or git(parent,'rev-parse','HEAD')!=comparison:
        raise ValueError('the runner did not check out the requested immutable objects')
    for repo,typ in ((candidate,'candidate'),(parent,'parent')):
        for rev in ('src','lean-toolchain','lakefile.toml','lake-manifest.json'):
            want=req[typ+'_source_tree'] if rev=='src' else req['pins'][rev]
            if git(repo,'rev-parse','HEAD:'+rev)!=want:raise ValueError(typ+' '+rev+' does not match')
    if git(candidate,'rev-parse','HEAD^{tree}')!=req['git_tree']:
        raise ValueError('the checked Git tree differs from the located public commit')
    with tempfile.TemporaryDirectory()as wd:
        repo=Path(wd)/'refs.git';subprocess.run(['git','init','--quiet','--bare',repo],check=True)
        git(repo,'fetch','--quiet','--filter=tree:0','--no-tags',fork,req['source_ref']+':refs/heads/source')
        git(repo,'fetch','--quiet','--filter=tree:0','--no-tags',upstream,comparison+':refs/heads/base','refs/heads/main:refs/heads/main')
        public_head=git(repo,'rev-parse','source'); live_main=git(repo,'rev-parse','main')
        if public_head!=head:raise ValueError('the public solution branch has advanced')
        if req['mode']=='github-pull-merge':
            num=req['pull_number']
            if type(num) is not int or num<1:raise ValueError('invalid pull request')
            git(repo,'fetch','--quiet','--filter=tree:0','--no-tags',upstream,f'refs/pull/{num}/head:refs/heads/pull',f'refs/pull/{num}/merge:refs/heads/merge')
            git(repo,'fetch','--quiet','--filter=tree:0','--no-tags',upstream,checked+':refs/heads/tested')
            published_merge = git(repo,'rev-parse','merge')
            if git(repo,'rev-parse','pull')!=head or git(repo,'show','-s','--format=%P','tested').split()!=[comparison,head]:
                raise ValueError('the immutable GitHub merge has different submitted parents')
            if published_merge!=checked:
                later=git(repo,'show','-s','--format=%P','merge').split()
                if len(later)!=2 or later[1]!=head or git(repo,'rev-parse','merge:src')!=req['candidate_source_tree']:
                    raise ValueError('the latest public GitHub merge has different proof inputs')
                for file in ('.gitattributes','comparator.json','export-targets.txt',*req['pins']):
                    if git(repo,'rev-parse','tested:'+file)!=git(repo,'rev-parse','merge:'+file):
                        raise ValueError('the GitHub merge changed '+file)
        elif req['mode']=='public-fork-head':
            if checked!=head or git(repo,'merge-base','base','source')!=comparison:
                raise ValueError('the source branch does not contain the recorded comparison parent')
        else:raise ValueError('unknown verification mode')
        live_src=git(repo,'rev-parse','main:src');live_pins={key:git(repo,'rev-parse','main:'+key)for key in req['pins']}
        if live_src!=req['parent_source_tree'] or live_pins!=req['pins']:
            raise ValueError('upstream main has changed the source or compiler inputs')
    out=dict(req,upstream_main_observed=live_main,pr_head=head,comparison_parent=comparison,source_mode=req['mode'],source_tree=req['candidate_source_tree'],ci_head=checked,workflow_head=os.environ.get('GITHUB_SHA'))
    if req['mode']=='github-pull-merge':
        out['observed_github_test_merge']=published_merge
    out['pull_request']='https://github.com/leanprover-community/riemann-hypothesis/pull/'+str(req['pull_number']) if req.get('pull_number') else None
    work.mkdir(exist_ok=True,parents=True);(work/'pr-source.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':bind(*(Path(p).resolve() for p in sys.argv[1:]))
