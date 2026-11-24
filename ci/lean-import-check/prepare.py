#!/usr/bin/env python3
"""Restore the published parent cone for an isolated fork verification job."""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

PARENT = "362d9476fbd4548dead48ed7b6a54600879e1e17"
SOURCE_TREE = "40e3cf4d94bd95ec57949a01b570b2ece95e4ceb"
DONOR = "f82babb107b166beffa76844bbc2c64c8296d247"
MANIFEST = "db681d77faedbe9dd13afdd6e0a4076e63539302dba3ee98d48f6e072e103855"

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trusted", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("work", type=Path)
    parser.add_argument("roots", type=Path)
    parser.add_argument("--maximum", type=int, default=2000)
    parser.add_argument("--max-roots", type=int, default=8)
    parser.add_argument("--leantar", required=True)
    args = parser.parse_args()
    base, candidate, work = map(Path.resolve, (args.trusted, args.candidate, args.work))
    api = load("parent_cache", base/"scripts/ci-cache-get.py")
    quick = load("quick", base/"scripts/quick-check.py")
    if api.git(base, "rev-parse", "HEAD") != PARENT:
        raise ValueError("unexpected upstream scripts revision")
    ident = api.current_identity(base)
    if ident["source_tree"] != SOURCE_TREE:
        raise ValueError("unexpected parent source tree")
    for file in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        if (base/file).read_bytes() != (candidate/file).read_bytes():
            raise ValueError(f"candidate configuration differs: {file}")
    roots = args.roots.read_text().splitlines()
    if not 1 <= len(roots) <= args.max_roots or len(roots) != len(set(roots)):
        raise ValueError("invalid root count")
    cone = quick.dependency_closure(candidate, roots, args.maximum)
    if cone != quick.dependency_closure(base, roots, args.maximum):
        raise ValueError("project dependencies changed in the selected cone")
    if not set(roots) <= set(cone):
        raise ValueError("missing candidate source")
    work.mkdir(exist_ok=True, parents=True)
    raw = api.fetch(f"ci/revisions/{DONOR}.json", api.MAX_RECEIPT)
    if raw is None:
        raise ValueError("successful parent receipt unavailable")
    receipt = api.matching_record(raw, ident)
    if not receipt or receipt["candidate_head"] != DONOR or receipt["module_manifest_sha256"] != MANIFEST:
        raise ValueError("parent receipt differs from the pinned source or manifest")
    _, shas, rows = api.validated_blobs(receipt, ident)
    by_name = {row[0]: row for row in rows}
    chosen = [by_name[n] for n in cone]
    def source(root, name):
        return root/"src"/Path(*name.split(".")).with_suffix(".lean")
    outside = set()
    for checkout in (base, candidate):
        external = {i for n in cone for i in quick.imports(source(checkout, n))} - set(cone)
        missing = sorted(set(by_name) & external)
        if missing:
            raise ValueError(f"sparse checkout lacks published project dependencies: {missing}")
        if checkout == candidate:
            outside = external
    # Lean and Std are in the toolchain. These families are present in the
    # pinned Mathlib cache implementation (Cache/IO.lean).
    families = {"Mathlib", "Aesop", "Batteries", "Qq", "Cli", "ImportGraph",
                "LeanSearchClient", "Plausible", "ProofWidgets"}
    deps = sorted(n for n in outside if n.split(".")[0] in families)
    if not deps:
        raise ValueError("the requested project cone has no Mathlib cache inputs")
    if "Mathlib" in deps:
        deps = [n for n in deps if n == "Mathlib" or not n.startswith("Mathlib.")]
    (work/"mathlib-inputs.txt").write_text("\n".join(deps)+"\n")
    changed = [n for n in cone if source(candidate,n).read_bytes() != source(base,n).read_bytes()]
    if not changed:
        raise ValueError("none of the selected ancestors contains modified source")
    rebuild = sorted(set(roots) | set(changed))
    (work/"fresh.txt").write_text("\n".join(rebuild)+"\n")
    cache = work/"cache"
    cache.mkdir(exist_ok=True)
    # The upstream downloader validates each archive digest on each call.
    # Small groups also bound concurrent reads at the public cache.
    for i in range(0, len(chosen), 16):
        quick.prep.downloads(cache, {key: name for _, key, name in chosen[i:i+16]}, shas)
    jobs = api.unpack_jobs(candidate, cache, chosen)
    root_outputs = candidate/".lake/build"
    if root_outputs.exists():
        raise ValueError("use an empty project build directory")
    subprocess.run([args.leantar, "--jobs", "2", "-f", "-x", "-j", "-"],
                   input=json.dumps(jobs), text=True, check=True)
    compressed = sum((cache/"artifacts"/name).stat().st_size for _, _, name in chosen)
    expanded = sum(p.stat().st_size for p in root_outputs.rglob("*") if p.is_file())
    # Save all three parent images and force stock Lake to rebuild every
    # modified ancestor and requested root from the candidate checkout.
    baseline = work/"parent"
    baseline.mkdir(exist_ok=True)
    for root in rebuild:
        path = root_outputs/"lib/lean"/Path(*root.split("."))
        for ext in (".olean", ".olean.server", ".olean.private"):
            shutil.copyfile(path.with_suffix(ext), baseline/(root+ext))
        path.with_suffix(".trace").unlink()
        path.with_suffix(".olean").unlink()
    alloc = shutil.disk_usage(work)
    report = dict(parent=PARENT, donor=DONOR, source_tree=SOURCE_TREE, manifest=MANIFEST,
                  roots=roots, changed=changed, fresh=rebuild, package_cache_inputs=len(deps),
                  project_archives=len(chosen), compressed_bytes=compressed,
                  expanded_bytes=expanded, free_bytes=alloc.free)
    print(json.dumps(report), flush=True)
    (work/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    (work/"receipt.json").write_bytes(raw)

if __name__ == "__main__":
    main()
