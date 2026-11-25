"""Check the existing Satake proof and the intended AdmLoc caller with both provider policies."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PROVIDER = "Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle"
CALLER = "Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight"
INTENDED = "Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound"
FLAGS = ["--json", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("repo", "before", "after", "bin", "output"):
        parser.add_argument("--" + arg, required=True, type=Path)
    for arg in ("parent", "candidate"):
        parser.add_argument("--" + arg, required=True)
    args = parser.parse_args()
    repo, before, after, binary, out = (p.resolve() for p in (args.repo, args.before, args.after, args.bin, args.output))
    out.mkdir(parents=True, exist_ok=True)
    path = Path(*CALLER.split(".")).with_suffix(".lean")
    system = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2")
    version = subprocess.check_output([binary / "lean", "--version"], text=True).strip()
    sides = dict(parent=(args.parent, before), candidate=(args.candidate, after))
    for revision, project in sides.values():
        for module in (PROVIDER, CALLER, INTENDED):
            source = "src/" + module.replace(".", "/") + ".lean"
            wanted = subprocess.check_output(["git", "-C", repo, "show", revision + ":" + source])
            if (project / source).read_bytes() != wanted:
                raise ValueError(f"Source differs at {revision}: {module}")
    caller = (before / "src" / path).read_text()
    marker = re.compile(r"^(?:(?:public|private|meta) )*import (\S+)\s*$", re.M)
    imports = list(marker.finditer(caller))
    if caller != (after / "src" / path).read_text() or not imports or PROVIDER in {m[1] for m in imports}:
        raise ValueError("The proof or its original imports have changed.")
    extra = "public import " + PROVIDER
    first = imports[0].start()
    last = imports[-1].end()
    fixtures = {"first": caller[:first] + extra + "\n" + caller[first:],
                "last": caller[:last] + "\n" + extra + "\n" + caller[last:]}
    def compile_case(job):
        side, order = job
        project = sides[side][1]
        root = out / (side + "-" + order)
        source = root / path
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(fixtures[order])
        child = subprocess.run([binary/"lake", "--no-cache", "env", binary/"lean", *FLAGS, "--root", root, source],
                               cwd=project, env=system, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (root/"compile.log").write_bytes(child.stdout)
        messages = [json.loads(line) for line in child.stdout.splitlines() if line.startswith(b"{")]
        errors = [dict(pos=row["pos"], message=row["data"]) for row in messages if row.get("severity")=="error"]
        if child.returncode != int(bool(errors)):
            raise ValueError((side, order, child.returncode, child.stdout[-500:]))
        return side + "-" + order, dict(exit=child.returncode, errors=errors,
                                        source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
    with ThreadPoolExecutor(max_workers=2) as pool:
        cases = dict(pool.map(compile_case, ((side, order) for side in sides for order in fixtures)))
    kernel = {}
    for side, (_, project) in sides.items():
        child = subprocess.run([binary/"lake", "--no-cache", "env", binary/"leanchecker", "-v", INTENDED],
                               cwd=project, env=system, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out/(side+"-intended.log")).write_bytes(child.stdout)
        if child.returncode or INTENDED.encode() not in child.stdout:
            raise ValueError((side, child.stdout[-500:]))
        kernel[side] = child.returncode
    receipt = dict(compiler=version, parent=args.parent, candidate=args.candidate, caller=CALLER,
                   provider=PROVIDER, intended=INTENDED, intended_kernel_exits=kernel, cases=cases)
    (out/"results.json").write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n")
    print({name: len(row["errors"]) for name, row in cases.items()}, "ResBound kernel exits", kernel)
    for order in fixtures:
        parent_errors = cases["parent-" + order]["errors"]
        if not parent_errors or "Function expected at\n  mulB P V" not in parent_errors[0]["message"]:
            raise ValueError("The original Satake elaboration error did not recur: " + order)
        if cases["candidate-" + order]["exit"]:
            raise ValueError("The candidate failed to elaborate the Satake proof: " + order)


if __name__ == "__main__":
    main()
