"""Replay the PR #120 matrix-space regression on the original Lean 4.36 package lock."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ORIGINAL = "c7791603122c0328f79e49f6be5d7d4402effc53"
BASE = "21f32da2751f7db09c38ef6d1dfb1cf961eb3c3b"
START = "@[expose] public section"
DOUBLE = "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue"
TWIST = "Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero"
SPLIT = "Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace"
COS = "Formalism.DoubleCosetMeasures.StatementZ"
GJ = "GroundTheory.AutomorphicForms.GL2.GJMatrixCoord"
OWNERS = [
    "Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq",
    "Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup",
    "Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL",
]
OPTIONS = ["--json", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
           "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000"]

def path(module):
    return Path(*module.split(".")).with_suffix(".lean")

def source(repo, revision, module):
    return subprocess.check_output(["git", "-C", repo, "show", revision + ":src/" + str(path(module))]).decode()

def include_library(original, overlay):
    for item in original.iterdir():
        dest = overlay / item.name
        if not dest.exists():
            dest.symlink_to(item, target_is_directory=item.is_dir())
        elif item.is_dir() and not dest.is_symlink():
            include_library(item, dest)

def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", required=True, type=Path)
    cli.add_argument("--stock-lib", required=True, type=Path)
    cli.add_argument("--output", required=True, type=Path)
    cli.add_argument("--patch", required=True)
    a = cli.parse_args()
    repo, stock, output = (p.resolve() for p in (a.repo, a.stock_lib, a.output))
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("Use an empty output directory.")
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "version 4.36.0," not in version and "version 4.36.0 " not in version:
        raise ValueError(version)
    pkg = [p for p in os.environ["LEAN_PATH"].split(os.pathsep) if "/.lake/packages/" in p]
    required = [DOUBLE, TWIST, SPLIT, COS, GJ, *OWNERS]
    for mod in required:
        if not (stock / path(mod).with_suffix(".olean")).is_file():
            raise ValueError("Build the original module " + mod)
    patch = subprocess.check_output(["git", "-C", repo, "rev-parse", a.patch + "^{commit}"], text=True).strip()
    def run(folder, module, text, library):
        f = folder / path(module)
        f.parent.mkdir(exist_ok=True, parents=True)
        f.write_text(text)
        env = {**os.environ, "LEAN_PATH":os.pathsep.join([str(library), *pkg])}
        command = ["lean", *OPTIONS, "--root", str(folder), "-o", str(f.with_suffix(".olean")), str(f)]
        proc = subprocess.run(command, env=env, cwd=folder, capture_output=True)
        log = proc.stdout + proc.stderr
        (folder / (module.rsplit(".",1)[-1] + ".jsonl")).write_bytes(log)
        errors = []
        for line in log.splitlines():
            try:
                msg = json.loads(line)
            except ValueError:
                continue
            if msg.get("severity") == "error":
                errors.append(dict(pos=msg["pos"], message=msg["data"]))
        return dict(module=module, sourceSHA256=hashlib.sha256(text.encode()).hexdigest(),
                    exit=proc.returncode, errors=errors)
    lib = output / "candidate"
    for mod in [SPLIT, COS, GJ]:
        entry = run(lib, mod, source(repo, patch, mod), stock)
        if entry["exit"]:
            raise RuntimeError((mod, entry["errors"]))
    include_library(stock, lib)
    head, _, _ = source(repo, ORIGINAL, DOUBLE).partition(START)
    body = source(repo, BASE, DOUBLE).split(START, 1)[1]
    header = "module\n\npublic import Mathlib\n" + head.split("module",1)[1].strip() + "\n"
    double_text = header + "".join("public import " + n + "\n" for n in OWNERS) + "\n" + START + "\n" + body
    old = source(repo, ORIGINAL, TWIST)
    reverse, _, reverse_body = old.partition(START)
    cases = [("doubling", DOUBLE, double_text, 8)]
    for tag, pair in [("coset-last",[GJ,COS]),("coordinate-last",[COS,GJ])]:
        text = reverse.rstrip() + "\n" + "".join("public import " + n + "\n" for n in pair) + "\n" + START + reverse_body
        cases.append((tag, TWIST, text, 2))
    results = dict(compiler=version, patch=patch, base=BASE, original=ORIGINAL, cases={})
    for tag, mod, text, expected in cases:
        results["cases"][tag]={}
        for label, libraries, errors in [("original-providers",stock,expected),("patched-providers",lib,0)]:
            result=run(output / (tag+"-"+label), mod, text, libraries)
            results["cases"][tag][label] = result
            (output/"result.json").write_text(json.dumps(results,indent=2)+"\n")
            print(tag, label, result["exit"], len(result["errors"]), flush=True)
            if len(result["errors"]) != errors or result["exit"] != int(errors != 0):
                raise RuntimeError("Unexpected compiler result in "+tag+" "+label)
    original_header = output / "original-header"
    proof = run(original_header, DOUBLE, source(repo, ORIGINAL, DOUBLE), lib)
    if proof["exit"] or proof["errors"]:
        raise RuntimeError("The doubling integral failed with its original imports.")
    include_library(lib, original_header)
    results["originalHeader"] = proof
    (output/"result.json").write_text(json.dumps(results,indent=2)+"\n")

if __name__=="__main__":
    main()
