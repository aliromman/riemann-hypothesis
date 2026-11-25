"""Check the public interfaces of every project module needed by the listed Lake targets."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from compare_providers import OWNERS


def source_path(module):
    return Path("src", *module.split(".")).with_suffix(".lean")


def verified_closure(repo, revision, project, binary, targets):
    tree = subprocess.check_output(["git", "-C", repo, "ls-tree", "-r", "-z", revision, "--",
                                    "src", "lean-toolchain", "lake-manifest.json", "lakefile.toml"])
    blobs = {}
    for row in tree.split(b"\0"):
        if row:
            metadata, name = row.split(b"\t", 1)
            blobs[Path(os.fsdecode(name))] = metadata.split()[2]

    def check(path):
        data = (project / path).read_bytes()
        oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest().encode()
        if oid != blobs[path]:
            raise ValueError(f"Source differs from {revision}: {path}")

    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        check(Path(name))
    pending, seen = set(targets), set()
    while pending:
        batch = sorted(pending)[:192]
        pending.difference_update(batch)
        paths = [source_path(n) for n in batch]
        for path in paths:
            check(path)
        records = json.loads(subprocess.check_output([binary / "lean", "--deps-json",
                             *(project / p for p in paths)]))["imports"]
        if len(records) != len(paths):
            raise ValueError("Incomplete header data")
        seen.update(batch)
        for record in records:
            if record["errors"]:
                raise ValueError(record["errors"])
            for dep in record["result"]["imports"]:
                n = dep["module"]
                if n not in seen and source_path(n) in blobs:
                    pending.add(n)
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "before", "after", "bin", "targets", "checker", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--parent", required=True, help="Git commit of the control build")
    parser.add_argument("--candidate", required=True, help="Git commit of the candidate build")
    a = parser.parse_args()
    repo, before, after, binary, targets, checker, out = (p.resolve() for p in
        (a.repo, a.before, a.after, a.bin, a.targets, a.checker, a.output))
    parent, candidate = (subprocess.check_output(
        ["git", "-C", repo, "rev-parse", "--verify", "--end-of-options", ref + "^{commit}"],
        text=True).strip() for ref in (a.parent, a.candidate))
    roots = targets.read_text().split()
    names = verified_closure(repo, parent, before, binary, roots)
    if names != verified_closure(repo, candidate, after, binary, roots):
        raise ValueError("The two source import closures differ")
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2")
    with tempfile.TemporaryDirectory() as directory:
        manifest = Path(directory, "objects.tsv")
        with manifest.open("w") as file:
            for n in sorted(names):
                path = Path(".lake/build/lib/lean", *n.split(".")).with_suffix(".olean")
                print(n, before / path, after / path, sep="\t", file=file)
        data = subprocess.check_output([binary / "lake", "--no-cache", "env", binary / "lean",
                                       "--run", checker, "scan", manifest], cwd=before, env=env)
    rows = [json.loads(line) for line in data.splitlines()]
    if len(rows) != len(names) or {row["module"] for row in rows} != names:
        raise ValueError("The object audit did not cover the source closure")
    fields = ("public", "axiomRecords", "rawTypes", "theorems", "rawProofs", "definitions", "rawDefinitions")
    counts = {k: sum(row[k] for row in rows) for k in fields}
    for row in rows:
        if row["public"] != row["rawTypes"] or row["public"] != row["axiomRecords"] or row["theorems"] != row["rawProofs"]:
            raise ValueError("Public interface, axiom record, or proof differs: " + row["module"])
        provider = OWNERS.get(row["module"])
        metadata = ["kind, universe parameters, binders or declaration metadata changed: " + provider] if provider else []
        terms = [dict(conversion="pending", declaration=provider, field="definition")] if provider else []
        if row["structural"] != metadata or row["terms"] != terms:
            raise ValueError(f"Unexpected difference in {row['module']}: {row}")
    changed_definitions = sorted(OWNERS[n] for n in names if n in OWNERS)
    if counts["definitions"] - counts["rawDefinitions"] != len(changed_definitions):
        raise ValueError("Unexpected number of changed definitions")
    out.mkdir(parents=True, exist_ok=True)
    (out / "interfaces.jsonl.gz").write_bytes(gzip.compress(data, mtime=0))
    result = dict(parent=parent, candidate=candidate, modules=len(names), counts=counts,
                  checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),
                  uncompressed_sha256=hashlib.sha256(data).hexdigest(), changed_definitions=changed_definitions)
    (out / "interfaces.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
