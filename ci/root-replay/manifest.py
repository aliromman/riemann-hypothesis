"""Package source-bound native digests for the independent public root job."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import re
from pathlib import Path

FACETS = {'.olean','.olean.server','.olean.private','.ir.sig','.ir'}
SHA256 = re.compile(r'[0-9a-f]{64}')
COMMIT = re.compile(r'[0-9a-f]{40}')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def rows(raw):
    result={}
    for line in raw.splitlines():
        row=json.loads(line)
        module=row['module']
        if module in result or row['kind'] not in {'fresh','reused'} or not COMMIT.fullmatch(row['parent']):
            raise ValueError('duplicate or invalid compiler record: '+module)
        if row['origin']!='retained' and not SHA256.fullmatch(row['origin']):
            raise ValueError('invalid compiler provenance: '+module)
        if set(row['facets'])!=FACETS or not all(SHA256.fullmatch(h) for h in [row['parent_source'],row['head_source'],*row['facets'].values()]):
            raise ValueError('incomplete native source or output digests: '+module)
        result[module]=row
    if not result:raise ValueError('empty compiler record table')
    return result

def read_request(folder):
    req=json.loads((folder/'request.json').read_bytes())
    if req['schema']!=1 or type(req['pull_request']) is not int or req['pull_request']<=0:
        raise ValueError('invalid pull request identity')
    if req.get('revision','current head') not in {'current head','first published commit'}:
        raise ValueError('invalid pull request revision')
    if any(not COMMIT.fullmatch(req[k]) for k in ('base','head','base_src','head_src')):
        raise ValueError('invalid reviewed Git identity')
    if req.get('source_mode','private-imports') not in ('private-imports','clump-scopes'):
        raise ValueError('unrecognized source verification mode')
    if req.get('source_mode')=='clump-scopes' and (not SHA256.fullmatch(req['source_trial_sha256']) or not isinstance(req['tooling'],dict)):
        raise ValueError('incomplete structural source or tooling identity')
    packed=(folder/'native.jsonl.gz').read_bytes()
    if sha(packed)!=req['bundle_sha256']:
        raise ValueError('native input bundle digest mismatch')
    data=gzip.decompress(packed)
    if sha(data)!=req['source_provenance_sha256']:
        raise ValueError('native input table digest mismatch')
    inputs=rows(data)
    if len(inputs)!=req['changed']:
        raise ValueError('native input table size mismatch')
    return req,inputs

def package(stage, number, out, first_commit=False):
    summary=stage/'bound.json'
    if not summary.is_file():summary=stage/'plan.json'
    bound=json.loads(summary.read_bytes())
    data=(stage/'source-provenance.jsonl').read_bytes()
    inputs=rows(data)
    audit=(stage/'ir-audit.tsv').read_bytes()
    checks=bound['ir_audit']
    if sha(data)!=bound['source_provenance_sha256'] or sha(audit)!=checks['raw_table_sha256']:
        raise ValueError('staging report does not bind its native inputs and IR audit')
    if checks['signature_mismatches'] or checks['body_mismatches'] or len(inputs)!=checks['modules'] or len(inputs)!=bound['changed']:
        raise ValueError('incomplete or failed native output audit')
    observed={}
    for line in audit.decode().splitlines():
        name,expected_sig,actual_sig,expected_body,actual_body=line.split('\t')
        if name in observed:raise ValueError('duplicate IR audit row: '+name)
        observed[name]=(expected_sig,actual_sig,expected_body,actual_body)
    expected={n:(r['facets']['.ir.sig'],)*2+(r['facets']['.ir'],)*2 for n,r in inputs.items()}
    if observed!=expected:raise ValueError('native IR records and their audit disagree')
    packed=gzip.compress(data,compresslevel=6,mtime=0)
    request=dict(schema=1,pull_request=number,base=bound['before'],head=bound['after'],
        base_src=bound['before_src_tree'],head_src=bound['after_src_tree'],changed=len(inputs),
        bundle_sha256=sha(packed),source_provenance_sha256=sha(data),ir_table_sha256=sha(audit),
        stage_report_sha256=sha(summary.read_bytes()))
    request['revision']='first published commit' if first_commit else 'current head'
    if bound.get('source_mode')=='clump-scopes':
        for key in ('source_mode','source_trial_sha256','tooling'):
            request[key]=bound[key]
        if bound.get('fusion_refinements'):
            request['fusion_refinements']=bound['fusion_refinements']
    for key in ('previous_native_artifacts','preceding_root','structural_dispositions'):
        if key in bound:request[key]=bound[key]
    new_reports=bound.get('new_reports',{})
    native={r['origin'] for r in inputs.values() if r['kind']=='fresh'}
    if new_reports:
        request['native_artifacts']={h:new_reports[h]['artifact'] for h in sorted(native) if 'artifact' in new_reports[h]}

    out.mkdir(parents=True,exist_ok=True)
    (out/'native.jsonl.gz').write_bytes(packed)
    (out/'request.json').write_text(json.dumps(request,indent=2)+'\n')
    read_request(out)
    return request

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--stage',type=Path,required=True)
    p.add_argument('--pr',type=int,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--first-commit',action='store_true')
    opts=p.parse_args()
    print(json.dumps(package(opts.stage,opts.pr,opts.out,opts.first_commit),indent=2))
