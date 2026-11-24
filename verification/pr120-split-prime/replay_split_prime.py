"""Compile the two split-prime interfaces and their unchanged caller on Lean 4.36."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


PREFIX = "Development.AbelianVarietyTheory.Proofs.SatakeParameters."
PRODUCER = PREFIX + "DualSplitLabelOperatorMulScalarOperator"
CALLER = PREFIX + "LiftSplitHeckePolysEqTransferResidualPolys"
EXTRA = "Formalism.LocalToGlobal.Divisibility.DefGroupLemmas"
SECTION = "@[expose] public section"
ORIGINAL = "c7791603122c0328f79e49f6be5d7d4402effc53"
BEFORE = "1c5f0accc9a1e44d4166867f5452c8bc68440979"
AFTER = "09bdea3c122fc06907a3d0559c42012e75ffca3d"


def module_path(name):
    return Path(*name.split("."))


def read(repo, commit, module):
    path = module_path(module).with_suffix(".lean")
    return subprocess.check_output(["git", "-C", repo, "show", f"{commit}:src/{path}"]).decode()


def split_section(text):
    before, after = text.split(SECTION)
    return before, SECTION + after


def link_dependencies(original, target, outputs):
    """Keep the two compiled modules private to this run. Share all other objects."""
    target.mkdir()
    for item in original.iterdir():
        remaining = [p for p in outputs if p.parts[0] == item.name]
        if remaining and item.is_dir():
            link_dependencies(item, target / item.name, [Path(*p.parts[1:]) for p in remaining])
        elif not any(len(p.parts) == 1 and item.name.startswith(p.name + ".") for p in outputs):
            (target / item.name).symlink_to(item, target_is_directory=item.is_dir())


def compile_module(root, lib, env, module, source):
    rel = module_path(module)
    file = root / rel.with_suffix(".lean")
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(source)
    output = lib / rel
    cmd = ["lean", "--json", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
           "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000", f"--root={root}",
           "-o", output.with_suffix(".olean"), "-i", output.with_suffix(".ilean"), file]
    run = subprocess.run(cmd, cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    messages = [json.loads(s) for s in run.stdout.splitlines() if s.strip()]
    errors = [m["data"] for m in messages if m["severity"] == "error"]
    if (run.returncode == 0) != (not errors):
        raise RuntimeError(run.stdout)
    return {"exit": run.returncode, "errors": errors, "sha256": hashlib.sha256(source.encode()).hexdigest()}


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", type=Path, required=True)
    cli.add_argument("--original-lib", type=Path, required=True)
    opts = cli.parse_args()
    prod_header, _ = split_section(read(opts.repo, ORIGINAL, PRODUCER))
    pos = prod_header.rindex("\n", 0, len(prod_header.rstrip())) + 1
    last = prod_header.index("\n", pos) + 1
    prod_header = prod_header[:last] + f"public import {EXTRA}\n" + prod_header[last:]
    call_header, _ = split_section(read(opts.repo, ORIGINAL, CALLER))
    call_header += f"public import {EXTRA}\npublic import {PRODUCER}\n\n"
    bundle = read(opts.repo, BEFORE, PREFIX + "Bundle0184")
    if bundle != read(opts.repo, AFTER, PREFIX + "Bundle0184"):
        raise ValueError("caller changed between the two commits")
    marker = f"-- bundled from {CALLER}\nsection\n"
    member = bundle.split(marker)[1].split("-- bundled from ")[0].rstrip()
    if not member.endswith("\nend\nend"):
        raise ValueError("unexpected member boundary")
    caller = call_header + SECTION + "\n\n" + member[:-4] + "\n"
    for revision in [BEFORE, AFTER]:
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            lib = root / "lib"
            link_dependencies(opts.original_lib.resolve(), lib, list(map(module_path, (PRODUCER, CALLER))))
            env = {**os.environ, "LEAN_PATH": str(lib) + os.pathsep + os.environ["LEAN_PATH"], "LEAN_NUM_THREADS": "1"}
            _, body = split_section(read(opts.repo, revision, PRODUCER))
            for module, source in [(PRODUCER, prod_header + body), (CALLER, caller)]:
                result = compile_module(root, lib, env, module, source)
                print(json.dumps({"revision": revision, "module": module, **result}), flush=True)
                expected_error = revision == BEFORE and module == CALLER
                if expected_error:
                    if (len(result["errors"]) != 1 or not all(s in result["errors"][0] for s in
                            ["Application type mismatch", "Formalism.DivisionValues.conjPl", "Formalism.L2.DIV.conjPl", "DualSplitRel.dual_rel V P hP"])):
                        raise RuntimeError("the original caller failure did not reproduce")
                elif result["exit"]:
                    raise RuntimeError(f"compilation failed for {module} on {revision}")
            if revision == AFTER:
                for module in [PRODUCER, CALLER]:
                    check = subprocess.run(["leanchecker", "-v", module], cwd=root, env=env,
                                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                    print(json.dumps({"revision": revision, "kernel_module": module, "exit": check.returncode,
                                      "last_lines": check.stdout.splitlines()[-3:]}), flush=True)
                    if check.returncode:
                        raise RuntimeError(check.stdout)


if __name__ == "__main__":
    main()
