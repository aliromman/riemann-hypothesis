"""Check the public declarations that survive the retirement of the four matrix instances."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from audit_cone import verified_closure
from compare_providers import OWNERS


def object_path(project, module):
    return project / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")


def write_rows(path, rows):
    path.write_text("".join("\t".join(map(str, row)) + "\n" for row in rows))


def scan(binary, audit, project, env, manifest):
    result = subprocess.check_output([binary / "lake", "--no-cache", "env", binary / "lean",
                                      "--run", audit, "scan-proofs", manifest], cwd=project, env=env)
    rows = list(map(json.loads, result.splitlines()))
    by_module = {row["module"]: row for row in rows}
    if len(by_module) != len(rows):
        raise ValueError("Duplicate module in object scan")
    return result, by_module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "before", "after", "bin", "targets", "audit", "compare", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--parent", required=True)
    parser.add_argument("--candidate", required=True)
    args = parser.parse_args()
    repo, before, after, binary, targets, audit, compare, output = (p.resolve() for p in
        (args.repo, args.before, args.after, args.bin, args.targets, args.audit, args.compare, args.output))
    parent, candidate = (subprocess.check_output(["git", "-C", repo, "rev-parse", "--verify", "--end-of-options",
                         rev + "^{commit}"], text=True).strip() for rev in (args.parent, args.candidate))
    roots = targets.read_text().split()
    modules = verified_closure(repo, parent, before, binary, roots)
    if verified_closure(repo, candidate, after, binary, roots) != modules:
        raise ValueError("The source import closures differ")
    removed = {module: [name] for module, name in OWNERS.items()}
    removed["GroundTheory.AutomorphicForms.GL2.GJMatrixCoord"].append("GroundTheory.Automorphic.GJMatrix.borelSpace_matrix")
    if not removed.keys() <= modules:
        raise ValueError("The targets must include each instance provider")
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="1")
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)
        paths = [(m, object_path(before, m), object_path(after, m)) for m in sorted(modules)]
        manifest = tmp / "modules.tsv"
        write_rows(manifest, paths)
        forward_raw, forward = scan(binary, audit, before, env, manifest)
        write_rows(manifest, ((m, new, old) for m, old, new in paths))
        reverse_raw, reverse = scan(binary, audit, after, env, manifest)
        if forward.keys() != modules or reverse.keys() != modules:
            raise ValueError("Incomplete object scan")
        (output / "interfaces.jsonl.gz").write_bytes(gzip.compress(forward_raw, mtime=0))
        (output / "reverse.jsonl.gz").write_bytes(gzip.compress(reverse_raw, mtime=0))
        declarations = [(name, old, new) for m, old, new in paths for name in removed.get(m, [])]
        write_rows(tmp / "removed.tsv", declarations)
        counts = Counter()
        checks = []
        failures = []
        for module, old, new in paths:
            source, target = forward[module], reverse[module]
            names = removed.get(module, [])
            expected = {"exported declaration set changed"} if names else set()
            missing = {"missing candidate " + name for name in names}
            if set(source["structural"]) != expected | missing or set(target["structural"]) != expected:
                raise ValueError(f"Unexpected public declarations, metadata or axioms in {module}")
            if target["axiomRecords"] != target["public"] or source["axiomRecords"] != target["public"]:
                raise ValueError(f"Incomplete surviving axiom records in {module}")
            if source["public"] != target["public"] + len(names):
                raise ValueError(f"Unexpected declaration count in {module}")
            counts["public_before"] += source["public"]
            counts["surviving_public"] += target["public"]
            counts["raw_types"] += source["rawTypes"]
            counts["raw_definitions"] += source["rawDefinitions"]
            counts["raw_proofs"] += source["rawProofs"]
            fields = [(term["declaration"], term["field"]) for term in source["terms"]]
            if sorted(fields) != sorted((t["declaration"], t["field"]) for t in target["terms"]):
                raise ValueError(f"The forward and reverse field lists differ in {module}")
            field_counts = Counter(field for _, field in fields)
            if (source["rawTypes"] + field_counts["type"] != target["public"] or
                    source["rawDefinitions"] + field_counts["definition"] != source["definitions"] or
                    source["rawProofs"] + field_counts["proof"] != source["theorems"]):
                raise ValueError(f"Missing changed field in {module}")
            counts.update(field_counts)
            if not fields:
                continue
            for owner, project in (("stock", before), ("candidate", after)):
                command = [binary / "lake", "--no-cache", "env", binary / "lean", "--run", compare,
                           "--unfold-removed", tmp / "removed.tsv", owner, module, old, new,
                           *("\t".join(item) for item in fields)]
                run = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True)
                records = [json.loads(line) for line in run.stdout.splitlines() if line.startswith("{")]
                actual = [(row["declaration"], row["field"]) for row in records]
                if run.returncode or actual != fields or any(row["environment"] != owner or
                        row["module"] != module or row["originalToExpanded"] != "defeq" or
                        row["expandedConversion"] != "defeq" for row in records):
                    failures.append(dict(module=module, side=owner, exit=run.returncode,
                                         expected=len(fields), returned=len(records), stderr=run.stderr))
                checks.extend(records)
                print(owner, module, len(records), run.returncode, flush=True)
    (output / "kernel.jsonl.gz").write_bytes(gzip.compress(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in checks).encode(), mtime=0))
    result = dict(parent=parent, candidate=candidate, targets=roots, modules=len(modules), removed=removed,
                  counts=dict(counts), kernel_fields=len(checks), failures=failures,
                  scan_sha256=hashlib.sha256(forward_raw).hexdigest(),
                  reverse_scan_sha256=hashlib.sha256(reverse_raw).hexdigest(),
                  audit_sha256=hashlib.sha256(audit.read_bytes()).hexdigest(),
                  compare_sha256=hashlib.sha256(compare.read_bytes()).hexdigest())
    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    if failures:
        raise SystemExit("See result.json for the failed kernel comparisons.")
    print(dict(counts), len(checks), "kernel checks", flush=True)


if __name__ == "__main__":
    main()
