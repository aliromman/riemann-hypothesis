"""Repeat the finite level group tests using stock Lean 4.36.0 and the original compiled modules."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "pr120-admloc-priority"))
from check_priorities import ORIGINAL, OPTIONS, PUBLIC, fill_library, invoke, path_of, source

HEAD = "376bacf238f6f3a7a4f120aeb01c89d124ea7a66"
GROUP = "Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds."
PROVIDER = "Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership"
WSF = "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat"
TARGETS = {"Ea": GROUP + "Bundle0041", "Kpp": GROUP + "AllRowsKpp",
           "Flag": "Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0381"}

def source_data(repo):
    bodies = {k:source(repo, HEAD, n) for k,n in TARGETS.items()}
    members = {k:re.findall(r"(?m)^-- bundled from (\S+)$", body) or [TARGETS[k]] for k,body in bodies.items()}
    return bodies, members

def control(repo, bodies, members, key, exposed):
    imports = []
    for member in members[key]:
        header, mark, _ = source(repo, ORIGINAL, member).partition(PUBLIC)
        if not mark:
            raise ValueError("Missing public section in " + member)
        for line in header.splitlines():
            if line.strip() and line != "module" and line not in imports:
                if not line.startswith("public import "):
                    raise ValueError("Unexpected header in " + member)
                imports.append(line)
    if key == "Flag":
        imports.insert(0, "public import " + WSF)
    if exposed:
        imports.append("public import " + PROVIDER)
    return "module\n\n"+"\n".join(imports)+"\n\n"+PUBLIC+bodies[key].split(PUBLIC,1)[1]

def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", type=Path, required=True)
    cli.add_argument("--original-lib", type=Path)
    cli.add_argument("--out", type=Path)
    cli.add_argument("--list-targets", action="store_true")
    args = cli.parse_args()
    bodies, members = source_data(args.repo)
    if args.list_targets:
        print("\n".join(sorted({PROVIDER,WSF,*(n for group in members.values() for n in group)})))
        return
    if args.out is None or args.original_lib is None:
        cli.error("supply --original-lib and --out")
    if not re.search(r"version 4\.36\.0[, )]", subprocess.check_output(["lean","--version"],text=True)):
        raise ValueError("Select the stock Lean 4.36.0 toolchain.")
    lib, out = args.original_lib.resolve(), args.out.resolve()
    out.mkdir(exist_ok=True,parents=True)
    if any(out.iterdir()):
        raise ValueError("Use an empty output directory.")
    packages = [Path(x) for x in os.environ["LEAN_PATH"].split(os.pathsep) if "/.lake/packages/" in x]
    def compile_file(file, root, search, log):
        return invoke(["lean",*OPTIONS,"--root",str(root),"-o",str(file.with_suffix(".olean")),str(file)],root,[search,*packages],log)
    raw = source(args.repo,ORIGINAL,PROVIDER)
    if raw.count("  Fintype.ofFinite _") != 1:
        raise ValueError("The provider differs.")
    fixed = out/"provider"
    f = fixed/path_of(PROVIDER)
    f.parent.mkdir(parents=True)
    f.write_text(raw.replace("  Fintype.ofFinite _","  by classical infer_instance"))
    build = compile_file(f,fixed,lib,out/"provider.jsonl")
    if build["exit"]:
        raise ValueError("Cannot build the provider")
    fill_library(lib,fixed)
    rows = {"provider":build,"providerKernel":invoke(["leanchecker","-v",PROVIDER],out,[fixed,*packages],out/"provider-kernel.log")}
    for key in TARGETS:
        for arm in ("original","exposed","canonical"):
            d = out/(key+"-"+arm)
            d.mkdir()
            f = d/"Consumer.lean"
            f.write_text(control(args.repo,bodies,members,key,arm!="original"))
            search = fixed if arm=="canonical" else lib
            result = compile_file(f,d,search,d/"build.jsonl")
            result["source_sha256"] = hashlib.sha256(f.read_bytes()).hexdigest()
            if result["exit"]==0:
                result["kernel"] = invoke(["leanchecker","-v","Consumer"],d,[d,search,*packages],d/"kernel.log")
            rows[key+"-"+arm] = result
            print(key,arm,result["exit"],result["error_count"],result.get("kernel",{}).get("exit"),flush=True)
    equality = Path(__file__).with_name("FiniteEnumerationEquality.lean")
    for label,search in (("stock",lib),("canonical",fixed)):
        rows["equality-"+label]=invoke(["lean",*OPTIONS,str(equality)],out,[search,*packages],out/("equality-"+label+".jsonl"))
    (out/"results.json").write_text(json.dumps(rows,indent=2)+"\n")
    for key in TARGETS:
        for arm in ("original","exposed","canonical"):
            row=rows[key+"-"+arm]
            if arm=="exposed":
                if row["exit"]!=1 or row["error_count"]!=1:raise ValueError(key+" did not reproduce the failure")
            elif row["exit"] or row["kernel"]["exit"]:
                raise ValueError(key+" did not pass "+arm)
    if rows["providerKernel"]["exit"] or rows["equality-stock"]["error_count"]!=1 or rows["equality-canonical"]["exit"]:
        raise ValueError("The provider checks did not match the published results.")

if __name__=="__main__":
    main()
