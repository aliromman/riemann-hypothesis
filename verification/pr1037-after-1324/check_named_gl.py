"""Run the named GL controls on both sides and kernel replay on the candidate."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("before", "after", "bin", "fixture", "modules", "output"):
        parser.add_argument("--" + arg, type=Path, required=True)
    a = parser.parse_args()
    before, after, binary, fixture, modules, out = (path.resolve() for path in
        (a.before, a.after, a.bin, a.fixture, a.modules, a.output))
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2")
    out.mkdir(parents=True, exist_ok=True)
    def lake(project, *args):
        return subprocess.run([binary / "lake", "--no-cache", "env", *args],
                              cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    scopes = {}
    for side, project in (("parent", before), ("candidate", after)):
        result = lake(project, binary / "lean", "--json", fixture)
        rows = [json.loads(line) for line in result.stdout.splitlines() if line.startswith(b"{")]
        names = [row["data"].strip() for row in rows if row.get("severity") == "information"]
        (out / (side + "-gl.log")).write_bytes(result.stdout)
        if result.returncode or any(row.get("severity") == "error" for row in rows) or names != [
                "Formalism.DoubleCosetMeasures.instMeasGL 2", "Formalism.DoubleCosetMeasures.instBorelGL 2"]:
            raise ValueError((side, result.returncode, names))
        scopes[side] = dict(exit=result.returncode, selected=names)
    def replay(name):
        result = lake(after, binary / "leanchecker", "-v", name)
        (out / (name + ".log")).write_bytes(result.stdout)
        if result.returncode or name.encode() not in result.stdout:
            raise ValueError((name, result.returncode, result.stdout[-600:]))
        return name, result.returncode
    with ThreadPoolExecutor(max_workers=2) as pool:
        kernels = dict(pool.map(replay, modules.read_text().split()))
    receipt = dict(gl=scopes, kernel_exits=kernels, fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest())
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("kernel replays", len(kernels), "named GL controls", len(scopes))

if __name__ == "__main__":
    main()
