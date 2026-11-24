"""Compare integrated compiler outputs and diagnostic multisets with the official parent."""
import hashlib,json,re,sys
from pathlib import Path
w=Path(sys.argv[1]);suite=Path(__file__).resolve().parent
panel=json.loads((suite/'panel.json').read_bytes());ref=json.loads((w/'parent-facets.json').read_bytes());warnings=json.loads((w/'parent-warnings.json').read_bytes());report=json.loads((w/'report.json').read_bytes())
out=Path('.lake/build/lib/lean');diffs={};ordinary={'.olean','.ir.sig','.ir'}
with (w/'facet-comparisons.jsonl').open('w') as f:
    for n,pinned in sorted(ref.items()):
        stem=out/Path(*n.split('.'));before=warnings[n];candidate={}
        for ext in pinned:
            with stem.with_suffix(ext).open('rb') as stream:candidate[ext]=hashlib.file_digest(stream,'sha256').hexdigest()
        trace=json.loads(stem.with_suffix('.trace').read_bytes())
        after=sorted(re.sub(r'^(?:.*?\.lean:)?[0-9]+:[0-9]+:\s*','',r['message'].strip())for r in trace.get('log',[]) if r['level']=='warning')
        changed=[ext for ext,h in candidate.items() if pinned[ext]!=h]
        required=set(pinned) if n in panel['strict_private'] else ordinary
        if n in panel['changed_sources'] and n not in panel['strict_private']:
            required=required-{'.olean','.ir'}
        bad=sorted(required.intersection(changed))
        print(json.dumps(dict(module=n,fresh=n in report['fresh'],raw_different=changed,required=sorted(required),required_different=bad,old_warning_count=len(before),new_warning_count=len(after),equal_warnings=before==after,parent_sha256=pinned,candidate_sha256=candidate,parent_bytes={s:(w/'parent'/(n+s)).stat().st_size for s in pinned},candidate_bytes={s:stem.with_suffix(s).stat().st_size for s in pinned}),separators=(',',':')),file=f)
        if bad or before!=after:diffs[n]=dict(required_different=bad,old_warnings=before,new_warnings=after)
if diffs:
    raise ValueError('integrated compiler differences '+json.dumps(diffs)[:1300])
