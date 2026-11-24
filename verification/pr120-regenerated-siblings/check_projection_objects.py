from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

stock, overlay, tools, judge = map(Path, sys.argv[1:])
plan = json.loads((overlay / "projection.json").read_bytes())
rows = []
def object_path(arm, name):
    return stock / arm / ".lake/build/lib/lean" / Path(*name.split(".")).with_suffix(".olean")
for name, sources in list(plan["groups"].items()) + [(n, [n]) for n in plan["consumers"]]:
    paths = [object_path("after", name), *(object_path("before", old) for old in sources)]
    result = subprocess.run([tools / "lean", "--run", judge, *paths], capture_output=True, text=True)
    row = dict(module=name, original_sources=sources, interface_exit=result.returncode)
    if result.returncode:
        row["interface_error"] = (result.stdout + result.stderr).strip()
    else:
        stats = [int(i) for i in result.stdout.strip().split("\t")]
        if len(stats) != 6:
            raise ValueError("Invalid interface result for " + name)
        row.update(public_names=stats[0], identical_raw_types=stats[1], definitions=stats[2],
                   theorems=stats[3], matching_proof_terms=stats[4], axiom_records=stats[5])
    replay = subprocess.run([tools / "lake", "--no-cache", "env", "leanchecker", "-v", name],
                            cwd=stock/"after", capture_output=True, text=True)
    (stock / (name + ".kernel.log")).write_text(replay.stdout + replay.stderr)
    row["kernel_exit"] = replay.returncode
    rows.append(row)
    (stock/"interface-and-kernel.json").write_text(json.dumps(rows, indent=2)+"\n")
    print(name, row.get("interface_error", row.get("public_names")), "kernel", replay.returncode, flush=True)
if any(r["kernel_exit"] or r["interface_exit"] for r in rows):
    raise SystemExit(1)
