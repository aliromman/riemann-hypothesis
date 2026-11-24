"""Rebuild the two project modules referenced by proof terms in Main."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "import-screen"))
from lake_imports import import_levels
from verify_retained import source_warnings, trace_warnings

PROVIDERS = (
    "Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip",
    "Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion",
)
FACETS = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def stable(data):
    return json.dumps(data, sort_keys=True, separators=(",", ":")).encode()


def digest(file):
    with file.open("rb") as reader:
        return hashlib.file_digest(reader, "sha256").hexdigest()


def public_inputs(name, graph):
    levels = import_levels(name, graph)
    if any(levels.values()):
        raise ValueError("the provider has a private or meta compiler input: " + name)
    return set(levels)


def rebuild(repo, parent, originals, out, toolchain, judge, graph, setup, native, checked, changed, env):
    """Return the actual rebuilt provider outputs that Main must import."""
    out.mkdir(parents=True, exist_ok=True)
    candidates = set(changed)
    results = {}
    for name in PROVIDERS:
        module = Path(*name.split("."))
        source = Path("src") / module.with_suffix(".lean")
        data = (repo / source).read_bytes()
        for revision in (parent, "HEAD"):
            if subprocess.check_output(["git", "show", revision + ":" + str(source)], cwd=repo) != data:
                raise ValueError("provider source differs from its reviewed revision: " + name)
        if name in candidates:
            raise ValueError("the direct provider must have its original source: " + name)
        levels = public_inputs(name, graph)
        if not levels <= checked.keys():
            raise ValueError("a provider input has no verified public image: " + name)
        work = out / module.name
        work.mkdir(exist_ok=True)
        inputs = sorted(levels)
        file = work / "inputs.jsonl.gz"
        with file.open("wb") as compressed:
            with gzip.GzipFile(filename="", fileobj=compressed, mode="wb", compresslevel=4, mtime=0) as stream:
                for n in inputs:
                    stream.write(stable([n, checked[n], "candidate" if n in candidates else "official"]) + b"\n")
        arts = {n: [[native[n]], []] for n in inputs}
        current = dict(setup, name=name, importArts=arts)
        spec = work / "setup.json"
        setup_bytes = stable(current)
        spec.write_bytes(setup_bytes)
        packed_setup = work / "setup.json.gz"
        packed_setup.write_bytes(gzip.compress(setup_bytes, compresslevel=4, mtime=0))
        before = originals / module.with_suffix(".olean")
        owner = json.loads(before.with_suffix(".owner.json").read_bytes())
        if owner["module"] != name or digest(before) != checked[name]:
            raise ValueError("the provider archive is not the verified Main input: " + name)
        recorded = json.loads(subprocess.check_output(
            [toolchain / "lean", "--run", HERE / "ProviderFilename.lean", before], cwd=work, env=env))
        labels = recorded["paths"]
        if len(labels) > 1 or (labels and Path(labels[0]).parts[-len(source.parts):] != source.parts):
            raise ValueError("unexpected source filename in the official provider lint log: " + name)
        display = labels[0] if labels else str(source)
        actual = work / module.with_suffix(".olean")
        actual.parent.mkdir(parents=True, exist_ok=True)
        cmd = [toolchain / "lean", "-j1", "--tstack=400000", "--root=" + str(repo / "src"),
               "--setup=" + str(spec), "--json", "-o", actual, "--stdin", display]
        build = work / "compiler.log"
        with build.open("w") as log:
            subprocess.run(cmd, input=data, cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT,
                           timeout=1000, check=True)
        original_warnings = trace_warnings(json.loads(before.with_suffix(".trace").read_bytes()))
        warnings = source_warnings(build.read_text())
        if warnings != original_warnings:
            raise ValueError("the provider warning multiset changed: " + name)
        with (work / "declarations.json").open("wb") as log:
            subprocess.run([judge, name, before, actual, work], env=env, stdout=log, check=True)
        terms = json.loads((work / "declarations.json").read_bytes())
        if not (terms["kernelImage"] and terms["publicImage"] and terms["publicImports"] and
                terms["different"] == terms["proofChanges"] == 0 and terms["parentNames"] == terms["candidateNames"]):
            raise ValueError("the provider's complete declaration table changed: " + name)
        facets = {}
        for ext in FACETS:
            original, rebuilt = before.with_suffix(ext), actual.with_suffix(ext)
            facets[ext] = {"official": digest(original), "rebuilt": digest(rebuilt), "bytes": rebuilt.stat().st_size}
            if facets[ext]["official"] != facets[ext]["rebuilt"]:
                raise ValueError("the provider raw output differs: " + name + ext)
        results[name] = {
            "module": name, "source_sha256": sha(data), "archive": owner,
            "source_filename": display, "embedded_lint_messages": recorded["messages"],
            "effective_inputs": len(inputs), "edited_inputs": len(candidates.intersection(inputs)),
            "input_manifest": str(file.relative_to(out)), "input_manifest_sha256": digest(file),
            "setup_sha256": digest(spec), "compressed_setup_sha256": digest(packed_setup), "compiler_log_sha256": digest(build),
            "warnings": sum(warnings.values()), "warnings_sha256": sha(stable(sorted(warnings.items()))),
            "facets": facets, "declarations": terms, "public_output": str(actual),
        }
    return results
