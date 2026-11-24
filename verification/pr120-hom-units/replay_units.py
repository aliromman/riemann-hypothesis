"""Compile and compare two repaired proofs against their original Lean 4.36 interfaces."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

cli = argparse.ArgumentParser(description=__doc__)
cli.add_argument("--repo", type=Path, required=True)
cli.add_argument("--original-lib", type=Path, required=True)
cli.add_argument("--out", type=Path, required=True)
cli.add_argument("--helpers", type=Path, default=Path(__file__).resolve().parent.parent / "pr120-admloc-priority")
args = cli.parse_args()
repo, stock, out = [path.resolve() for path in (args.repo, args.original_lib, args.out)]
sys.path.insert(0, str(args.helpers.resolve()))
from check_priorities import ORIGINAL, OPTIONS, PUBLIC, fill_library, invoke, path_of, source

base = "2d20aa9035becfe380b9fe619e3d3fc968cf3400"
repair = "75dd653aaa59d745e7f4794cfb4c6da5d1f73455"
integration = "92e91959e3fbd8a3533172cffdb6272143341d1f"
prefix = "Development.AbelianVarietyTheory.Proofs.DivisorProofs."
modules = {"Bundle1269": "FiniteEtalePointOfExt", "Bundle1447": "DivisibleAlgClosureOfKillsTorsionSepClosed"}
version = subprocess.check_output(["lean", "--version"], text=True).strip()
if "version 4.36.0," not in version:
    raise ValueError("Run the check with the pinned Lean 4.36.0 toolchain.")
packages = [str(Path(p).resolve()) for p in os.environ["LEAN_PATH"].split(os.pathsep) if "packages" in Path(p).parts]
if not packages:
    raise ValueError("Run this command through lake env in the original checkout.")
if out.exists() and any(out.iterdir()):
    raise ValueError("Select an empty output directory.")
out.mkdir(parents=True, exist_ok=True)
results = dict(lean=version, original=ORIGINAL, before=base, repair=repair, integration=integration, modules={})


def extract_member(rev, bundle, member):
    text = source(repo, rev, bundle)
    section = text.split("-- bundled from " + member + "\nsection\n", 1)[1].split("\n-- bundled from ", 1)[0].rstrip()
    if not section.endswith("\nend"):
        raise ValueError("The member has no closing section in " + rev)
    return section.removesuffix("\nend") + "\n"


for short, logical in modules.items():
    bundle, member = prefix + short, prefix + logical
    original = source(repo, ORIGINAL, member)
    header, marker, _ = original.partition(PUBLIC)
    if not marker:
        raise ValueError("Missing original public section in " + member)
    if extract_member(repair, bundle, member) != extract_member(integration, bundle, member):
        raise ValueError("The integrated proof differs from the repair.")
    old_object = stock / path_of(member).with_suffix(".olean")
    if not old_object.is_file():
        raise FileNotFoundError(old_object)
    results["modules"][bundle] = {}
    for name, rev in [("before", base), ("after", repair)]:
        folder = out / short / name
        src = folder / path_of(member)
        src.parent.mkdir(parents=True)
        text = header + PUBLIC + "\n" + extract_member(rev, bundle, member)
        src.write_text(text)
        obj = src.with_suffix(".olean")
        built = invoke(["lean", *OPTIONS, "--root", folder, "-o", obj, src], folder, [stock, *packages], folder / "compile.jsonl")
        if built["exit"]:
            raise ValueError((name, member, built))
        fill_library(stock, folder)
        replay = invoke(["leanchecker", "-v", member], folder, [folder, *packages], folder / "kernel.log")
        check = subprocess.run(["lean", "--run", args.helpers.resolve() / "Interface.lean", obj, old_object],
                               cwd=folder, capture_output=True, text=True)
        (folder / "interface.log").write_text(check.stdout + check.stderr)
        if replay["exit"] or check.returncode:
            raise ValueError((name, member, replay, check.stdout, check.stderr))
        metrics = [int(s) for s in check.stdout.strip().split("\t")]
        if len(metrics) != 6:
            raise ValueError("Unexpected interface result.")
        record = dict(sourceSHA256=hashlib.sha256(text.encode()).hexdigest(), compile=built, kernel=replay,
                      interface=dict(zip(("public", "identicalStoredTypes", "definitions", "theorems", "matchingProofs", "axiomRecords"), metrics)))
        results["modules"][bundle][name] = record
        (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(short, name, record["interface"], flush=True)
