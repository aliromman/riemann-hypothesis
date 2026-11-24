"""Check the complete generated change set against a candidate commit."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

repo, generated = map(Path, sys.argv[1:3])
candidate = sys.argv[3]
data = json.loads((generated / "projection.json").read_bytes())
paths = {"src/" + n.replace(".", "/") + ".lean": sha for n, sha in data["source_sha256"].items()}
git = ["git", "-C", repo]
diff = subprocess.check_output([*git, "diff", "--no-renames", "--name-only", "-z", data["head"], candidate])
if {p.decode() for p in diff.split(b"\0") if p} != set(paths):
    raise ValueError("The changed file set differs.")
for name, expected in paths.items():
    content = (generated / name).read_bytes()
    published = subprocess.check_output([*git, "show", candidate + ":" + name])
    if content != published or hashlib.sha256(content).hexdigest() != expected:
        raise ValueError("The generated file differs at " + name)
print("Verified generated sources:", len(paths))
