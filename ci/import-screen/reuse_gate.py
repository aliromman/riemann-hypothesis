"""Recompute the input equivalence used to carry a previous native certificate."""
from __future__ import annotations
import csv
import gzip
import hashlib
import json
import subprocess

from lake_imports import import_levels
from verify_retained import prune,sha


def source_blobs(repo, rev):
    raw = subprocess.check_output(['git','-C',str(repo),'ls-tree','-rz',rev,'--','src'])
    blobs = {}
    for line in raw.split(b'\0'):
        if not line:
            continue
        obj, path = line.split(b'\t',1)
        if path.endswith(b'.lean'):
            module = path.decode()[4:-5].replace('/','.')
            blobs[module] = obj.split()[-1].decode()
    return blobs


def check(repo, state, helper, api, graph, new_rows, new_shas, source_path, canonical):
    facts = json.loads((helper/'reuse-meta.json').read_bytes())
    old,new = facts['old'],facts['new']
    current = api.current_identity(repo)
    for key in ('lakefile_sha256','manifest_sha256','toolchain'):
        if old[key] != new[key] or new[key] != current[key]:
            raise ValueError('compiler or project configuration differs across parents')
    if current['source_tree'] != new['source_tree'] or api.git(repo,'rev-parse',old['base']+':src') != old['source_tree']:
        raise ValueError('current or previous source tree is absent')
    for filename, field in [('reuse.tsv','reuse_tsv_sha256'),('reuse-witness.jsonl.gz','witness_gzip_sha256'),
                            ('targets.txt','targets_sha256'),('verify_retained.py','worker_sha256'),
                            ('CheckInterface.lean','exact_checker_sha256')]:
        if sha((helper/filename).read_bytes()) != facts[field]:
            raise ValueError(f'reuse input digest differs: {filename}')
    target_lines={b'import '+t+b'\n' for t in (helper/'targets.txt').read_bytes().splitlines()}
    old_identity={k:old[k] for k in ('source_tree','lakefile_sha256','manifest_sha256','toolchain')}
    old_identity['build_roots']={}
    receipt_path = state/'metadata'/('reuse-'+old['candidate_head']+'.json')
    if not receipt_path.is_file():
        raw = api.fetch('ci/revisions/'+old['candidate_head']+'.json',api.MAX_RECEIPT)
        if raw is None:raise ValueError('previous successful cache receipt missing')
        receipt_path.write_bytes(raw)
    record=api.matching_record(receipt_path.read_bytes(),old_identity)
    if not record or record['module_manifest_sha256']!=old['module_manifest_sha256']:
        raise ValueError('previous parent receipt does not match its source tree')
    def blob(key, limit):
        path=state/'metadata'/key.rsplit('/',1)[-1]
        if not path.is_file():
            data=api.fetch(key,limit)
            if data is None:raise ValueError('previous parent metadata missing')
            path.write_bytes(data)
        return path.read_bytes()
    _,old_shas,old_items=api.validated_blobs(record,old_identity,fetcher=blob)
    prior={n:archive for n,_,archive in old_items}
    if not prior.keys()<=new_rows.keys():
        raise ValueError('this reuse proof requires that the new module-name set contains the previous one')
    old_src=source_blobs(repo,old['base']);new_src=source_blobs(repo,new['base'])
    with (helper/'reuse.tsv').open() as data:
        rows=list(csv.DictReader(data,delimiter='\t'))
    lookup={r['module']:r for r in rows}
    if len(lookup)!=len(rows) or len(rows)!=facts['modules']:
        raise ValueError('duplicate or missing crossover roots')
    with gzip.open(helper/'reuse-witness.jsonl.gz','rt') as stream:
        witnesses={entry['module']:entry['inputs'] for entry in map(json.loads,stream)}
    if set(witnesses)!=set(lookup):
        raise ValueError('missing or extra input witness')
    owners=set(lookup);deps={x[0] for z in witnesses.values() for x in z}
    for n in owners|deps:
        if n not in prior or old_src.get(n)!=new_src.get(n):
            raise ValueError('source blob changed in a claimed shared input: '+n)
    # Only source-identical modules are read while verifying an old witness.
    # Filtering out novel module names recovers its original project edge set.
    before_graph={n:[e for e in graph[n] if e[0] in prior] for n in owners|deps}
    for n,row in lookup.items():
        root_bytes=(repo/source_path(n)).read_bytes()
        candidate,_=prune(root_bytes,target_lines)
        if (new_src[n],sha(root_bytes),sha(candidate)) != (row['git_blob'],row['source_sha256'],row['catalog_candidate_sha256']):
            raise ValueError('reused root or candidate source mismatch: '+n)
        if old_shas[prior[n]]!=new_shas[new_rows[n][2]] or new_shas[new_rows[n][2]]!=row['parent_ltar_sha256']:
            raise ValueError('owning parent archive mismatch: '+n)
        left=import_levels(n,before_graph);right=import_levels(n,graph)
        if left!=right:
            raise ValueError('effective project import flags differ: '+n)
        expected=[]
        for dep,flags in sorted(right.items()):
            old_id=old_shas[prior[dep]];new_id=new_shas[new_rows[dep][2]]
            if old_id!=new_id:raise ValueError('exposed parent archive differs: '+dep)
            expected.append([dep,flags,new_id])
        if expected!=witnesses[n] or len(expected)!=int(row['inputs']) or sha(canonical(expected))!=row['inputs_sha256']:
            raise ValueError('effective input witness mismatch: '+n)
    report=dict(roots=len(owners),distinct_exposed_dependencies=len(deps),root_or_dependency_source_blobs=len(owners|deps),
                old_tree=old['source_tree'],new_tree=new['source_tree'],old_manifest=old['module_manifest_sha256'],
                new_manifest=new['module_manifest_sha256'],witness_sha256=facts['witness_gzip_sha256'],
                rows_sha256=facts['reuse_tsv_sha256'])
    (state/'metadata/reuse-check.json').write_text(json.dumps(report,indent=2)+'\n')
    print('recomputed old/current source and effective artifact identity:',report,flush=True)
