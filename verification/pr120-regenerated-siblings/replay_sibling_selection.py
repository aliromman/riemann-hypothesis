"""Regenerate previously tested sibling groups from the current upstream sources."""
import argparse
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace

from regenerate_siblings import module, ownership, plan, verify_headers
from render_sibling_projection import git, load_clump, run


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for k in ("repo","headers","selection","out","lean"):
        ap.add_argument("--"+k,required=True,type=Path)
    ap.add_argument("author")
    a = ap.parse_args()
    with a.headers.open() as f:
        head=json.loads(next(f))
        headers={module(p):(active,tuple(map(tuple,imports))) for p,_,active,imports in map(json.loads,f)}
    base=head["revision"]
    author=git(a.repo,"rev-parse",a.author+"^{commit}").decode().strip()
    groups=json.loads(a.selection.read_bytes())["groups"]
    # Check exact sibling headers and adjacency at every current import site.
    owners=ownership(a.repo,base,author)
    group_members={m for members in groups.values() for m in members}
    owners={n:[m for m in members if m in group_members] for n,members in owners.items()}
    eligible={tuple(row["members"]):row for row in plan(headers,owners,None)}
    pairs=[(x,y) for group in groups.values() for x,y in zip(group,group[1:])]
    missing=[pair for pair in pairs if pair not in eligible]
    if missing:raise ValueError(("These groups no longer meet the selection criteria",missing))
    if a.out.exists() and any(a.out.iterdir()):raise ValueError("Use an empty output directory.")
    with tempfile.TemporaryDirectory() as d:
        run(SimpleNamespace(repo=a.repo,out=a.out,base=base,author=author,cohort=None),
            load_clump(a.repo,base,Path(d)),[eligible[p] for p in pairs])
    manifest=json.loads((a.out/"projection.json").read_bytes())
    if manifest["groups"]!=groups:raise ValueError("The output contains different groups.")
    audit=verify_headers(a.lean,a.out,headers,manifest)
    (a.out/"header-check.json").write_text(json.dumps(audit,indent=2)+"\n")
    print(audit,flush=True)


if __name__=="__main__":
    main()
