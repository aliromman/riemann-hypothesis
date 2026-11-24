"""Hash the frozen challenge export and check the actual five-root replay outputs."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

FROZEN_EXPORT='bb37c4bb518fe68a13f12aa3929dd62dfecb663f0c063ad8c338e39601f28a60'

def challenge(parent,out):
    expected=FROZEN_EXPORT
    needles=re.findall(r'\b([0-9a-f]{64})\s+challenge\.export\b',(parent/'.github/workflows/checks.yml').read_text())
    if needles!=[expected]:raise ValueError('upstream challenge export pin differs')
    targets=(parent/'export-targets.txt').read_text().split()
    start=time.monotonic()
    subprocess.run(['lake','build','Challenge'],cwd=parent,check=True)
    h=hashlib.sha256();n=0
    with subprocess.Popen(['lake','env','leanexport','Challenge','--',*targets],cwd=parent,stdout=subprocess.PIPE) as proc:
        for buf in iter(lambda:proc.stdout.read(1<<20),b''):
            h.update(buf);n+=len(buf)
        if proc.wait():raise ValueError('official challenge export failed')
    if h.hexdigest()!=expected:raise ValueError('frozen challenge export digest differs')
    out.write_text(json.dumps({'expected':expected,'sha256':h.hexdigest(),'bytes':n,
                               'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')

def verify(roots, config, frozen):
    conf=json.loads(config.read_bytes())
    names=conf['theorem_names']
    axs=set(conf['permitted_axioms'])
    if len(names)!=5 or len(set(names))!=5 or axs!={'Classical.choice','propext','Quot.sound'}:
        raise ValueError('unexpected Comparator targets or allowed axioms')
    report=json.loads((roots/'report.json').read_bytes())
    if report['targets']!=names or any(report[n]['code']!=0 for n in ('compile','decls','replay','axioms','challenge')):
        raise ValueError('an expected native proof step is missing or failed')
    decls=json.loads((roots/'decls.log').read_bytes())
    if (not decls['kernelImage'] or not decls['publicImage'] or not decls['publicImports'] or decls['proofChanges']!=0
        or decls['different']!=0 or decls['parentNames']!=5 or decls['candidateNames']!=5):
        raise ValueError('the rebuilt Main differs from the five complete parent declarations')
    replay=(roots/'replay.log').read_text().splitlines()
    if not any(l.startswith('negative control:') for l in replay):
        raise ValueError('the kernel negative control has no recorded rejection')
    if [l.removeprefix('kernel accepted ') for l in replay if l.startswith('kernel accepted ')]!=names:
        raise ValueError('the kernel did not report acceptance of all five theorem bodies')
    atom={}
    for line in (roots/'axioms.log').read_text().splitlines()[1:]:
        name,raw=line.split('\t')
        if name in atom or not raw.startswith('#[') or not raw.endswith(']'):raise ValueError('invalid axiom report')
        atom[name]=[a.strip() for a in raw[2:-1].split(',')]
    if set(atom)!=set(names) or any(len(v)!=3 or set(v)!=axs for v in atom.values()):raise ValueError('axiom sets differ')
    lines=(roots/'challenge.log').read_text().splitlines()
    if [x[6:] for x in lines if x.startswith('claim ')]!=names:
        raise ValueError('the five compiled statements differ from the frozen challenge')
    definitions=('RiemannZetaZerosOnLine','DirichletLNonvanishingRightOfHalf','DirichletLZerosOnLine','PrimitiveDirichletLZerosOnLine')
    if [x.split()[1] for x in lines if x.startswith('definition ') and x.endswith('alphaEquivalent=true')]!=list(definitions):
        raise ValueError('the proposition definitions differ from the frozen challenge')
    frozen_report=json.loads(frozen.read_bytes())
    if frozen_report['sha256']!=FROZEN_EXPORT or frozen_report['expected']!=FROZEN_EXPORT or frozen_report['bytes']<=0:
        raise ValueError('missing authenticated frozen challenge export')
    bound=report['source_binding']
    if report['projects']!=report['fresh_parent_digests']+report['candidate_visible'] or report['candidate_all']!=bound['changed']:
        raise ValueError('root input coverage is incomplete')
    # The original staging report calls these commits "before" and "after".
    base=bound.get('parent') or bound['before']
    head=bound.get('head') or bound['after']
    return dict(base=base,head=head,head_source=bound['after_src_tree'],changed=bound['changed'],
        checked_parent_public=report['fresh_parent_digests'],changed_visible_to_Main=report['candidate_visible'],
        candidate_visible_and_parent=report['projects'],decls=decls,kernel_accepted=names,negative_control=replay[0],
        axioms=atom,challenge=frozen_report,challenge_statement_and_definition_results=lines)
if __name__=='__main__':
    p=argparse.ArgumentParser()
    sp=p.add_subparsers(dest='action',required=True)
    c=sp.add_parser('export')
    c.add_argument('--parent',type=Path,required=True);c.add_argument('--out',type=Path,required=True)
    v=sp.add_parser('verify')
    v.add_argument('--roots',type=Path,required=True);v.add_argument('--config',type=Path,required=True)
    v.add_argument('--challenge',type=Path,required=True);v.add_argument('--out',type=Path,required=True)
    o=p.parse_args()
    if o.action=='export':challenge(o.parent,o.out)
    else:
        report=verify(o.roots,o.config,o.challenge)
        o.out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
