"""Verify independent private-import variants against released Lean artifacts."""
import argparse
from collections import Counter
import gzip
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import tempfile
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
CURRENT = HERE.parent / "current-recheck"
sys.path.insert(0, str(CURRENT))
from parent import BASE, TREE, MANIFEST, GRAPH, SCREEN, restore, sha
from native_candidate import Exact, header
from run import run_group
from lake_imports import project_artifacts
from receipts import TRANSIENT


LIBRARIES = {
    "Formalism": "Formalism",
    "ReciprocityTheory": "ReciprocityTheory",
    "GroundTheory": "GroundTheory.ArithmeticGeometry",
    "GroundTheoryFields": "GroundTheory.LocalFields",
}


def library(module):
    if module.startswith(("GroundTheory.LocalFields.", "GroundTheory.GlobalFields.")):
        return "GroundTheoryFields"
    key = module.split(".", 1)[0]
    if key not in LIBRARIES:
        raise ValueError("module outside the selected libraries: " + module)
    return key


def stock_options(parent, names, work):
    roots = {key: prefix + ".RHImportValidationOptionsProbe" for key, prefix in LIBRARIES.items()
             if key in {library(n) for n in names}}
    paths = []
    try:
        for module in roots.values():
            source = (parent / "src" / Path(*module.split("."))).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            with source.open("x") as f:
                f.write("module\n")
            paths.append(source)
        subprocess.run(["lake", "--no-cache", "build", *["+" + n + ":olean" for n in roots.values()]],
                       cwd=parent, check=True)
        options = {}
        for key, module in roots.items():
            path = (parent / ".lake/build/ir" / Path(*module.split("."))).with_suffix(".setup.json")
            setup = json.loads(path.read_bytes())
            if (setup["name"] != module or not setup["isModule"] or setup["package"] != "tree"
                    or setup["plugins"] or setup["dynlibs"]):
                raise ValueError("unexpected stock Lake compiler options for " + module)
            options[key] = {part: setup[part] for part in ("package", "isModule", "plugins", "dynlibs", "options")}
        (work / "library-options.json").write_text(json.dumps(options, indent=2) + "\n")
        return options
    finally:
        for path in paths:
            path.unlink()


class CheckedSource(Exact):
    def __init__(self, opt, variants, options):
        super().__init__(opt, variants)
        self.stock_options = options

    def setup(self, module):
        return dict(self.stock_options[library(module)], name=module,
                    importArts=project_artifacts(module, self.header_graph, self.art))

    def run(self, module):
        row = super().run(module)
        if row["status"] == "pass":
            with tempfile.TemporaryDirectory(dir=self.o.work / "tmp") as d:
                tmp = Path(d)
                parent = self.o.baseline / Path(*module.split("."))
                original = self.o.repo / self.paths[module]
                _, body = header(original.read_bytes().splitlines(keepends=True))
                candidate = tmp / "candidate.lean"
                candidate.write_bytes(self.variants[module][4].encode() + b"".join(body))
                parts = [".olean", ".ir.sig", ".ir"]
                inputs = [parent.with_suffix(ext) for ext in parts]
                outputs = [tmp / ("expected" + ext) for ext in parts]
                args = [module, inputs[0], original, candidate, outputs[0], *inputs[1:], *outputs[1:]]
                job = tmp / "inputs.tsv"
                job.write_text("\t".join(map(str, args)) + "\n")
                subprocess.run([self.o.rebuilder, job], check=True, capture_output=True, timeout=60)
                expected = {ext: sha(path.read_bytes()) for ext, path in zip(parts, outputs)}
                row["expected_facets"] = expected
                row["publicBytes"] = row["facets"][".olean"] == expected[".olean"]
                row["irImage"] = all(row["facets"][ext] == expected[ext] for ext in parts[1:])
                row["raw_parent_ir"] = {ext: sha(path.read_bytes()) for ext, path in zip(parts[1:], inputs[1:])}
        return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("group")
    for key in ("parent", "cache", "work", "resume", "bin", "judge", "rebuilder"):
        parser.add_argument(key, type=Path)
    args = parser.parse_args()
    for k, v in vars(args).items():
        if isinstance(v, Path):
            setattr(args, k, v.resolve())
    plan = json.loads((HERE / "dispatch.json").read_bytes())
    if (plan["src"], plan["donor"], plan["manifest"], plan["graph"]) != (TREE, BASE, MANIFEST, GRAPH):
        raise ValueError("the reviewed sources and published artifacts have different inputs")
    group = plan["groups"][args.group]
    raw = gzip.decompress((HERE / "groups" / (args.group + ".jsonl.gz")).read_bytes())
    if sha(raw) != group["sha256"]:
        raise ValueError("the exact source selection has changed")
    variants = dict(json.loads(line) for line in raw.splitlines())
    if len(variants) != group["count"]:
        raise ValueError("duplicate or missing variant")
    args.work.mkdir(parents=True, exist_ok=True)
    (args.work / "tmp").mkdir(exist_ok=True)
    args.resume.mkdir(parents=True, exist_ok=True)
    count = restore(args.parent, args.cache, args.work, variants, args.bin / "leantar")
    options = stock_options(args.parent, variants, args.work)
    key_files = [Path(__file__), CURRENT / "run.py", CURRENT / "parent.py", CURRENT / "native_candidate.py",
                 SCREEN / "screen.py", SCREEN / "verify_retained.py", SCREEN / "CheckInterface.lean",
                 SCREEN / "lake_imports.py", SCREEN / "targets.txt", CURRENT.parent / "root-replay/BuildPublic.lean"]
    mode = json.loads((args.work / "library-options.json").read_bytes())
    scope = {"parent": BASE, "reviewed_head": plan["reviewed_head"], "tree": TREE, "donor": BASE,
             "manifest": MANIFEST, "graph": GRAPH, "group": args.group, "roots": len(variants),
             "archives": count, "source_transitions_sha256": group["sha256"], "library_options": mode}
    (args.work / "scope.json").write_text(json.dumps(scope, indent=2) + "\n")
    opt = SimpleNamespace(repo=args.parent, work=args.work, headers=args.cache / "metadata/current-headers.json",
                          targets=SCREEN / "targets.txt", index=args.work / "index.json", archives=args.cache / "artifacts",
                          baseline=args.parent / ".lake/build/lib/lean", packages=args.parent / ".lake/packages",
                          bin=args.bin, judge=args.judge, rebuilder=args.rebuilder, timeout=240)
    version = subprocess.check_output([args.bin / "lean", "--version"], text=True).strip()
    if "0b77e12952ad39077d80d8bd6b66d601f225c321" not in version:
        raise ValueError("unexpected Lean build")
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft < 2400:
        resource.setrlimit(resource.RLIMIT_NOFILE, (min(2400, hard) if hard != resource.RLIM_INFINITY else 2400, hard))
    domain = {"scope": scope, "toolchain": version, "checks": {p.name: sha(p.read_bytes()) for p in key_files}}
    rows, resumed, seconds = run_group(CheckedSource(opt, variants, options), args.group, variants,
                                       args.work, args.resume, domain, 240*60, group["workers"])
    strict = [r for r in rows.values() if r["status"] == "pass" and r["kernelImage"]
              and r["proofChanges"] == 0 and r["publicBytes"] and r["irImage"]]
    statuses = Counter(r["status"] for r in rows.values())
    report = dict(scope=scope, statuses=statuses, exact_private_proof_modules=len(strict),
                  exact_private_proof_lines=sum(r["n"] for r in strict), resumed_modules=resumed,
                  pending=len(variants)-len(rows), candidate_modules=len(rows), seconds=round(seconds, 3),
                  machine=platform.platform(), toolchain=version, workflow_sha=os.getenv("GITHUB_SHA"),
                  checker_source_sha=domain["checks"]["CheckInterface.lean"], runner_source_sha=domain["checks"]["check.py"],
                  worker_source_sha=domain["checks"]["native_candidate.py"], target_sha=domain["checks"]["targets.txt"],
                  result_sha=sha((args.work / "results.jsonl").read_bytes()), workers=group["workers"])
    (args.work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report), flush=True)
    if report["pending"] or any(statuses[x] for x in TRANSIENT):
        raise SystemExit("incomplete native coverage")


if __name__ == "__main__":
    main()
