"""Reproduce the Lean 4.36 adelic-group searches with the original 4.36 module objects."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "pr120-admloc-priority"))
from check_priorities import ORIGINAL, OPTIONS, PUBLIC, fill_library, invoke, path_of, source

HUB = "GroundTheory.AutomorphicForms.AdelicGLn"
PROOF = "Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal"
PROVIDERS = [
    "Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup",
    "Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq",
]
PARENT = "2d20aa9035becfe380b9fe619e3d3fc968cf3400"
PORT = "2cc9602ef874fbdf9f913545c8bc895c3e9cb812"
UPSTREAM = "f6d5ee4d401a2f52932d71426854f0110ada926b"

def ported_source(repo):
    base = source(repo, UPSTREAM + "^", HUB)
    changed = source(repo, UPSTREAM, HUB)
    end = "\ndef det : AdelicGL K n"
    old = base[base.index("theorem locallyCompactSpace :"):base.index(end)]
    new = changed[changed.index("instance (priority := high) locallyCompactSpace :"):changed.index(end)]
    if base.replace(old, new, 1) != changed or source(repo, PARENT, HUB).replace(old, new, 1) != source(repo, PORT, HUB):
        raise ValueError("The source hunk differs between the two pull requests.")
    stock = source(repo, ORIGINAL, HUB)
    if stock.count(old) != 1:
        raise ValueError("The declaration block is missing in the original layout.")
    return stock.replace(old, new, 1)

def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", required=True, type=Path)
    cli.add_argument("--original-lib", type=Path, required=True, help="lib/lean from the original Lean 4.36 build")
    cli.add_argument("--out", required=True, type=Path)
    a = cli.parse_args()
    repo, lib, out = (path.resolve() for path in (a.repo, a.original_lib, a.out))
    if not re.search(r"version 4\.36\.0[, ]", subprocess.check_output(["lean", "--version"], text=True)):
        raise ValueError("Select the pinned Lean 4.36.0 toolchain.")
    if out.exists() and any(out.iterdir()):
        raise ValueError("Use an empty output directory.")
    out.mkdir(parents=True, exist_ok=True)
    packages = [Path(x) for x in os.environ["LEAN_PATH"].split(os.pathsep) if "/.lake/packages/" in x]
    if not packages:
        raise ValueError("Run this command with lake env in the pinned 4.36 project.")
    for mod in (HUB, PROOF, *PROVIDERS):
        if not (lib / path_of(mod).with_suffix(".olean")).is_file():
            raise ValueError("Build the original module " + mod)
    receipts = {}
    def compile_one(label, name, text, library, errors):
        root = out / label
        f = root / path_of(name)
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)
        row = invoke(["lean", *OPTIONS, "--root", root, "-o", f.with_suffix(".olean"), f],
                     root, [library, *packages], root / "compile.jsonl")
        row["sourceSha256"] = hashlib.sha256(f.read_bytes()).hexdigest()
        if row["exit"] != int(errors != 0) or row["error_count"] != errors:
            raise ValueError((label, row))
        if errors == 0:
            fill_library(library, root)
            row["kernel"] = invoke(["leanchecker", "-v", name], root, [root, *packages], root / "kernel.log")
            if row["kernel"]["exit"]:
                raise ValueError((label, row["kernel"]))
        receipts[label] = row
        (out / "receipts.json").write_text(json.dumps(receipts, indent=2) + "\n")
        return root
    patched = compile_one("provider", HUB, ported_source(repo), lib, 0)
    stock = source(repo, ORIGINAL, PROOF)
    header, mark, body = stock.partition(PUBLIC)
    if not mark:
        raise ValueError("The original source has no public section.")
    exposed = header + "".join("public import " + m + "\n" for m in PROVIDERS) + "\n" + mark + body
    compile_one("original-proof", PROOF, stock, lib, 0)
    compile_one("exposed-proof", PROOF, exposed, lib, 7)
    compile_one("ported-proof", PROOF, exposed, patched, 0)
    for file, errors in (("AdelicSearch", 4), ("SplitFlipField", 0), ("LGrpField", 0)):
        body = (HERE / (file + ".lean")).read_text()
        compile_one("stock-" + file, file, body, lib, errors)
        compile_one("port-" + file, file, body, patched, 0)
    print("The complete source, five searches, two field controls and successful kernels passed.")

if __name__ == "__main__":
    main()
