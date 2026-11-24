"""Count tracked Lean paths and check the protected inputs on the specified Git revisions."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("historical")
    parser.add_argument("initial")
    parser.add_argument("main")
    parser.add_argument("integration")
    args = parser.parse_args()
    def git(*argv):
        return subprocess.check_output(["git", "-C", args.repo, *argv])
    refs = {label:git("rev-parse","--verify",getattr(args,label)+"^{commit}").decode().strip()
            for label in ("historical","initial","main","integration")}
    trusted = ["src/Challenge.lean", "src/Statements.lean", "export-targets.txt", "comparator.json"]
    trees = {}
    result = {"trees": {}, "comparisons": {}, "merge_base":git("merge-base",refs["main"],refs["integration"]).decode().strip()}
    for label, commit in refs.items():
        entries = {}
        for row in git("ls-tree","-rz",commit).split(b"\0"):
            if row:
                meta,path = row.split(b"\t",1)
                entries[path] = meta.split()[2].decode()
        lean = {p for p in entries if p.endswith(b".lean")}
        project = {p for p in lean if p.startswith(b"src/")}
        trees[label] = lean,project
        result["trees"][label] = dict(commit=commit, all_lean=len(lean), src_lean=len(project),
                                      protected_blobs={p:entries[p.encode()] for p in trusted},
                                      lean_toolchain=git("show",commit+":lean-toolchain").decode().strip())
    for a,b in [("historical","initial"),("historical","integration"),("main","integration")]:
        fields=git("diff","--no-renames","--name-status","-z",refs[a],refs[b]).split(b"\0")
        counts={}
        for index,scope in enumerate(("all_lean","src_lean")):
            old,new=trees[a][index],trees[b][index]
            actions=Counter(status for status,path in zip(fields[::2],fields[1::2]) if path.endswith(b".lean") and (index==0 or path.startswith(b"src/")))
            deleted,added=len(old-new),len(new-old)
            if (deleted,added)!=(actions[b"D"],actions[b"A"]):raise ValueError("tree and diff disagree")
            counts[scope]=dict(base=len(old),candidate=len(new),removed_paths=deleted,added_paths=added,
                               net_reduction=deleted-added,percentage=round((deleted-added)*100/len(old),4))
        result["comparisons"][a+".."+b]=counts
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
