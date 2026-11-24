"""Test the two AdmLoc instance priorities against the complete Satake bundle on Lean 4.36."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ORIGINAL = "c7791603122c0328f79e49f6be5d7d4402effc53"
DIAGNOSTIC = "8feebfa6747502c29909a193b5a67df585e46571"
PROVIDER = "Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle"
TARGET = "Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200"
PUBLIC = "@[expose] public section"
OPTIONS = ["--json", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
           "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000"]


def path_of(module):
    return Path(*module.split(".")).with_suffix(".lean")


def source(repo, revision, module):
    return subprocess.check_output(["git", "-C", repo, "show", revision + ":src/" + path_of(module).as_posix()]).decode()


def declarations(repo):
    text = source(repo, DIAGNOSTIC, TARGET)
    members = re.findall(r"^-- bundled from ([^\s]+)$", text, re.M)
    if len(set(members)) != 6 or len(members) != 6:
        raise ValueError("The six expected source sections have changed.")
    return text, members


def control_source(repo, bundle, members, expose):
    imports = []
    for member in members:
        header, sep, _ = source(repo, ORIGINAL, member).partition(PUBLIC)
        if not sep:
            raise ValueError("Missing public section in " + member)
        for line in header.splitlines():
            if line.strip() and line != "module" and line not in imports:
                if not line.startswith("public import "):
                    raise ValueError("Unexpected header command in " + member)
                imports.append(line)
    if expose:
        imports.append("public import " + PROVIDER)
    _, sep, body = bundle.partition(PUBLIC)
    if not sep:
        raise ValueError("Missing bundle declarations.")
    return "module\n\n" + "\n".join(imports) + "\n\n" + sep + body


def fill_library(source_dir, output):
    for item in source_dir.iterdir():
        target = output / item.name
        if not target.exists():
            target.symlink_to(item, target_is_directory=item.is_dir())
        elif item.is_dir() and not target.is_symlink():
            fill_library(item, target)


def invoke(command, folder, library, log):
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(str(p) for p in library)}
    proc = subprocess.run(command, cwd=folder, env=env, capture_output=True)
    data = proc.stdout + proc.stderr
    log.write_bytes(data)
    diagnostics = []
    for line in data.splitlines():
        try:
            row = json.loads(line)
        except (UnicodeDecodeError, ValueError):
            continue
        if row.get("severity") == "error":
            diagnostics.append([row["pos"], row["data"]])
    return {"exit": proc.returncode, "error_count": len(diagnostics), "first_error": diagnostics[:1],
            "log_sha256": hashlib.sha256(data).hexdigest()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--list-targets", action="store_true")
    ap.add_argument("--original-lib", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    bundle, members = declarations(args.repo)
    if args.list_targets:
        print("\n".join([*members, PROVIDER]))
        return
    if args.original_lib is None or args.output is None:
        ap.error("set --original-lib and --output")
    if not re.search(r"version 4\.36\.0[, )]", subprocess.check_output(["lean", "--version"], text=True)):
        raise ValueError("Select the stock Lean 4.36.0 toolchain.")
    original_lib, output = args.original_lib.resolve(), args.output.resolve()
    if not (original_lib / path_of(PROVIDER).with_suffix(".olean")).is_file():
        raise ValueError("Build the original modules from --list-targets first.")
    if output.exists() and any(output.iterdir()):
        raise ValueError("Select an empty output directory.")
    output.mkdir(parents=True, exist_ok=True)
    target_text = control_source(args.repo, bundle, members, expose=True)
    original = source(args.repo, ORIGINAL, PROVIDER)
    if original.split(PUBLIC, 1)[1] != source(args.repo, DIAGNOSTIC, PROVIDER).split(PUBLIC, 1)[1]:
        raise ValueError("The provider bodies differ across the original and integrated layouts.")
    packages = [Path(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if "/.lake/packages/" in p]
    variants = {"high": "instance (priority := high)", "default": "instance",
                "low": "instance (priority := low)", "reducible": "@[reducible] instance (priority := high)"}
    results = {}
    def compile_source(file, root, library, log):
        return invoke(["lean", *OPTIONS, "--root", str(root), "-o", str(file.with_suffix(".olean")), str(file)],
                      root, library, log)
    baseline = output / "original"
    baseline.mkdir()
    control = baseline / "SatakeProof.lean"
    control.write_text(control_source(args.repo, bundle, members, expose=False))
    results["original"] = compile_source(control, baseline, [original_lib, *packages], baseline / "target.jsonl")
    if results["original"]["exit"]:
        raise ValueError("The six source sections failed on their original imports.")
    for label, replacement in variants.items():
        folder = output / label
        lib = folder / "provider"
        file = lib / path_of(PROVIDER)
        file.parent.mkdir(parents=True)
        text, count = re.subn(r"(?m)^instance \(priority := high\) (?=modTens\b|modFun\b)", replacement + " ", original)
        if count != 2:
            raise ValueError("The two registered instances have changed.")
        file.write_text(text)
        provider = compile_source(file, lib, [original_lib, *packages], lib / "build.jsonl")
        if provider["exit"]:
            raise ValueError("The provider failed in the " + label + " test.")
        fill_library(original_lib, lib)
        test = folder / "SatakeProof.lean"
        test.write_text(target_text)
        target = compile_source(test, folder, [lib, *packages], folder / "target.jsonl")
        row = results[label] = {"provider": provider, "target": target,
                                "provider_body_sha256": hashlib.sha256(text.split(PUBLIC, 1)[1].encode()).hexdigest()}
        if target["exit"] == 0:
            row["kernel"] = invoke(["leanchecker", "-v", "SatakeProof"], folder,
                                   [folder, lib, *packages], folder / "kernel.log")
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(label, "provider", provider["exit"], "source errors", target["error_count"],
              "target exit", target["exit"], "kernel", row.get("kernel", {}).get("exit"), flush=True)
    if any(results[n]["target"]["exit"] != 1 or results[n]["target"]["error_count"] != 51
           for n in ("high", "default", "reducible")) or results["low"]["target"]["exit"] or results["low"]["kernel"]["exit"]:
        raise SystemExit("The observed results differ from the published experiment.")
    judge = Path(__file__).with_name("Interface.lean")
    result = {}
    for name, after, before in (
        ("Satake", output / "low/SatakeProof.olean", baseline / "SatakeProof.olean"),
        ("provider", output / "low/provider" / path_of(PROVIDER).with_suffix(".olean"),
         output / "high/provider" / path_of(PROVIDER).with_suffix(".olean")),
    ):
        check = subprocess.run(["lean", "--run", judge, after, before], cwd=output, capture_output=True, text=True)
        (output / (name + "-interface.log")).write_text(check.stdout + check.stderr)
        check.check_returncode()
        counts = [int(x) for x in check.stdout.strip().split("\t")]
        if len(counts) != 6 or counts[0] != counts[1] or counts[3] != counts[4] or counts[0] != counts[5]:
            raise ValueError("The " + name + " interface or proof terms changed.")
        result[name] = counts
        print(name, "interface", counts, flush=True)
    (output / "interfaces.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
