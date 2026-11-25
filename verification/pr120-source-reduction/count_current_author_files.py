"""Count the Lean sources on a #120 author revision against its original base."""
import argparse
import json
from collections import Counter
from pathlib import Path
import subprocess

cli = argparse.ArgumentParser(description=__doc__)
cli.add_argument("repo", type=Path)
cli.add_argument("revision")
cli.add_argument("output", type=Path)
args = cli.parse_args()
repo = args.repo.resolve()
base = "c7791603122c0328f79e49f6be5d7d4402effc53"
head = args.revision


def git(*args):
    return subprocess.check_output(["git", "-C", repo, *args])


def files(revision):
    return {p for p in git("ls-tree", "-r", "-z", "--name-only", revision, "--", "src").split(b"\0") if p.endswith(b".lean")}


before, after = files(base), files(head)
changes = git("diff", "--no-renames", "--name-status", "-z", base, head, "--", "src").split(b"\0")[:-1]
counts = Counter(s.decode() for s, f in zip(changes[::2], changes[1::2]) if f.endswith(b".lean"))
if counts["D"] != len(before-after) or counts["A"] != len(after-before):
    raise ValueError("Git counts differ")
protected = {}
for name in ("src/Challenge.lean", "comparator.json", "export-targets.txt", "lean-toolchain"):
    old, new = [git("rev-parse", r+":"+name).decode().strip() for r in (base, head)]
    if old != new:
        raise ValueError("Protected input differs: " + name)
    protected[name] = new
result = dict(base=base, head=git("rev-parse", head + "^{commit}").decode().strip(),
              src_lean_before=len(before), src_lean_after=len(after), difference=len(before) - len(after),
              added=counts["A"], deleted=counts["D"], protected_git_blobs=protected)
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
