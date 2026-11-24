"""Compile the physical consumers with the IsCD instance available in both class forms."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

project, out = map(Path, sys.argv[1:3])
name = sys.argv[3]
prefix = "Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization."
ref = "UpperTheory.V.Pr.IsCD."
out.mkdir(parents=True, exist_ok=True)
for short in sys.argv[4:]:
    module = prefix + short
    rel = Path(*module.split(".")).with_suffix(".lean")
    original = (project / "src" / rel).read_text()
    # These complete attribute commands refer only to the five IsCD projections.
    pattern = re.compile(r"(?m)^attribute \[-instance\] " + re.escape(ref)
                         + r"\w+(?:(?: |\n  )+" + re.escape(ref) + r"\w+)*\n")
    changed, count = pattern.subn("", original)
    if count != 1 or any(ref in s for s in changed.splitlines() if "[-instance]" in s):
        raise ValueError((module, count))
    root = out / name
    file = root / rel
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(changed)
    flags = ["--json", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3",
             "-DmaxHeartbeats=4000000", f"--root={root}"]
    p = subprocess.run(["lean", *flags, file], cwd=project, env={**os.environ, "LEAN_NUM_THREADS": "1"},
                       capture_output=True, text=True)
    file.with_suffix(".log").write_text(p.stdout + p.stderr)
    errs = [m for ln in p.stdout.splitlines() if ln.startswith("{") and (m:=json.loads(ln)).get("severity")=="error"]
    print(json.dumps(dict(arm=name, module=module, source_sha256=hashlib.sha256(file.read_bytes()).hexdigest(),
                          exit=p.returncode, errors=[{"pos":e["pos"],"first":e["data"].splitlines()[0]} for e in errs],
                          timeouts=sum("timeout" in e["data"] for e in errs))), flush=True)
