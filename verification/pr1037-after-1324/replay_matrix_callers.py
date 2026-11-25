"""Check the named matrix instances and replay their two callers on both revisions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from replay_matrix_selection import OPTIONS, PROOF


PROVIDERS = (
    "GlobalTheory.SplitWeil.matrixMeasurableSpace",
    "GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix",
    "Formalism.DoubleCosetMeasures.instMeasMat",
)
GL_INSTANCES = (
    "Formalism.DoubleCosetMeasures.instMeasGL 2",
    "Formalism.DoubleCosetMeasures.instBorelGL 2",
)
GL_CALLER = "GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("before", "after", "bin", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    binary = args.bin.resolve()
    probes = Path(__file__).resolve().parent
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"],
               LEAN_NUM_THREADS="2", LAKE_ARTIFACT_CACHE="false", LEAN_ABORT_ON_PANIC="1")
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_CONFIG"):
        env.pop(key, None)
    prefix = [binary / "lake", "--no-cache", "env"]
    results = {}
    for side, project in (("before", args.before), ("after", args.after)):
        for name in ("ScopedGL", "NamedMatrixEqualities"):
            source = probes / (name + ".lean")
            cmd = [*prefix, binary / "lean", *OPTIONS, "--root", probes, source]
            run = subprocess.run(cmd, cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (out / f"{side}-{name}.jsonl").write_bytes(run.stdout)
            messages = [json.loads(line) for line in run.stdout.splitlines() if line.startswith(b"{")]
            errors = [m["data"] for m in messages if m.get("severity") == "error"]
            info = [m["data"].strip() for m in messages if m.get("severity") == "information"]
            results[side + "/" + name] = dict(exit=run.returncode, errors=errors, info=info,
                 source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
            if name == "ScopedGL":
                passed = run.returncode == 0 and not errors and sorted(info) == sorted(GL_INSTANCES)
            elif side == "before":
                passed = run.returncode == 1 and len(errors) == len(PROVIDERS) and all(
                    sum(p in error and "not definitionally equal" in error for error in errors) == 1
                    for p in PROVIDERS)
            else:
                passed = run.returncode == 0 and not errors
            if not passed:
                raise RuntimeError(f"Unexpected result in {side}-{name}.jsonl")
        for module in (PROOF, GL_CALLER):
            run = subprocess.run([*prefix, binary / "leanchecker", "-v", module], cwd=project,
                                 env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = out / (side + "-" + module.rsplit(".", 1)[-1] + ".log")
            log.write_bytes(run.stdout)
            if run.returncode or ("replaying " + module) not in run.stdout.decode().splitlines():
                raise RuntimeError(f"Kernel replay failed. See {log}")
            results[side + "/" + module] = dict(exit=run.returncode,
                                                 log_sha256=hashlib.sha256(run.stdout).hexdigest())
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print("Both scoped GL tests and all four kernel replays passed.")
    print("The named matrix equalities gave three errors on the parent and zero on the candidate.")


if __name__ == "__main__":
    main()
