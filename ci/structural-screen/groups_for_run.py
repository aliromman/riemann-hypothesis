"""Verify all candidate groups and the source identity of the public donor."""
from pathlib import Path
import collections,gzip,hashlib,json,os,subprocess
HERE=Path(__file__).resolve().parent

def sha(data):return hashlib.sha256(data).hexdigest()
def main():
    dispatch=json.loads((HERE/'dispatch.json').read_bytes())
    domain=dispatch.get('input','original')
    if domain not in ('original','repairs'):raise ValueError('unknown source domain')
    folder=HERE if domain=='original' else HERE/'repairs'
    req=json.loads((folder/'request.json').read_bytes())
    def tree(rev):
        dat=json.loads(subprocess.check_output(['gh','api','repos/leanprover-community/riemann-hypothesis/git/trees/'+rev]))
        return {f['path']:f['sha'] for f in dat['tree']}
    current=tree(req['base']);stock=tree(req['donor'])
    binding={k:(current[k],stock[k]) for k in ('src','lakefile.toml','lake-manifest.json','lean-toolchain')}
    if binding['src'][0]!=req['tree'] or any(a!=b for a,b in binding.values()):raise ValueError('named community source differs from the cache donor')
    for name,digest in req['recipe'].items():
        if sha((HERE/'recipe'/name).read_bytes())!=digest:raise ValueError('unexpected conversion code')
    discovered={};all_net=all_code=0
    for name,spec in req['groups'].items():
        data=gzip.decompress((folder/'groups'/(name+'.jsonl.gz')).read_bytes())
        records=[json.loads(line) for line in data.splitlines()]
        if sha(data)!=spec['sha256'] or len(records)!=spec['count']:raise ValueError('group digest differs '+name)
        for n,a,b,net,code in records:
            if n in discovered or a==b or len(a)!=64 or len(b)!=64:raise ValueError('invalid duplicate or unchanged module '+n)
            if domain=='repairs' and sha(gzip.decompress((folder/'blobs'/(b+'.lean.gz')).read_bytes()))!=b:raise ValueError('incorrect corrected source '+n)
            discovered[n]=name;all_net+=net;all_code+=code
        if sum(r[3] for r in records)!=spec['net'] or sum(r[4] for r in records)!=spec['code']:raise ValueError('line counts differ '+name)
    if (len(discovered),all_net,all_code)!=(req['files'],req['net'],req['code']):raise ValueError('incomplete request')
    groups=dispatch['groups']
    if not groups or len(groups)!=len(set(groups)) or not set(groups)<=req['groups'].keys():raise ValueError('unknown or repeated group')
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'],'a') as f:print('groups='+json.dumps(groups),file=f)
    print(json.dumps({'source_binding':binding,'files':len(discovered),'net':all_net,'code':all_code,'groups':groups,'source_manifest_sha256':req['source_manifest_sha256']}),flush=True)
if __name__=='__main__':main()
