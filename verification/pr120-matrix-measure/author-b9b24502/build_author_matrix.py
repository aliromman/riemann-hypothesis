"""Build the physical 4.36 matrix providers and their lattice caller from two Git commits."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


ROOTS = [
    "Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace",
    "Formalism.DoubleCosetMeasures.StatementZ",
    "GroundTheory.AutomorphicForms.GL2.GJMatrixCoord",
    "Formalism.DoubleCosetMeasures.LatticeCoset",
]
CONFIG = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")


def source(module):
    return Path("src", *module.split(".")).with_suffix(".lean")


def prepare(repo, rev, binary, directory, packages):
    def git(*args):
        return subprocess.check_output(["git", "-C", repo, *args])
    tracked = {}
    for row in git("ls-tree", "-rz", rev, "--", "src").split(b"\0"):
        if row.endswith(b".lean"):
            header, path = row.split(b"\t")
            tracked[path.decode()[4:-5].replace("/", ".")] = header.split()[2].decode()
    directory.mkdir(parents=True, exist_ok=True)
    for name in CONFIG:
        (directory / name).write_bytes(git("show", rev + ":" + name))
    pins = json.loads((directory / "lake-manifest.json").read_bytes())["packages"]
    for pkg in pins:
        checkout = packages / pkg["name"]
        actual = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
        if actual != pkg["rev"]:
            raise ValueError("Incorrect package revision for " + pkg["name"])
    lake = directory / ".lake"
    lake.mkdir(exist_ok=True)
    link = lake / "packages"
    if not link.is_symlink():
        link.symlink_to(packages, target_is_directory=True)
    if link.resolve() != packages:
        raise ValueError("The package directory differs from the verified input.")
    queue = set(ROOTS)
    blobs = {}
    while queue:
        group = sorted(queue)
        queue.clear()
        paths = []
        for module in group:
            path = directory / source(module)
            blob = tracked[module]
            data = git("cat-file", "blob", blob)
            check = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            if check != blob:
                raise ValueError("Source blob mismatch for " + module)
            if path.exists() and path.read_bytes() != data:
                raise ValueError("This output directory contains different source inputs.")
            if not path.exists():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            blobs[module] = blob
            paths.append(path)
        rows = json.loads(subprocess.check_output([binary / "lean", "--deps-json", *paths]))["imports"]
        for row in rows:
            if row["errors"]:
                raise ValueError(row["errors"])
            queue.update(x["module"] for x in row["result"]["imports"] if x["module"] in tracked)
        queue.difference_update(blobs)
    return blobs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("repo", "bin", "packages", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    for key in ("parent", "candidate"):
        parser.add_argument("--" + key, required=True)
    args = parser.parse_args()
    repo, binary, packages, out = (path.resolve() for path in (args.repo, args.bin, args.packages, args.output))
    if out.exists() and any(out.iterdir()):
        raise ValueError("Use an empty output directory for the two native builds.")
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2",
               LEAN_ABORT_ON_PANIC="1", LAKE_ARTIFACT_CACHE="false")
    version = subprocess.check_output([binary / "lean", "--version"], text=True).strip()
    if "version 4.36.0," not in version:
        raise ValueError(version)
    changes = subprocess.check_output(["git", "-C", repo, "diff", "-z", "--name-only", args.parent, args.candidate])
    if set(changes.decode().strip("\0").split("\0")) != {str(source(n)) for n in ROOTS[:3]}:
        raise ValueError("The diff must contain exactly the three provider files.")
    report = dict(lean=version, roots=ROOTS, builds={})
    inputs = {}
    for label, ref in (("parent", args.parent), ("candidate", args.candidate)):
        revision = subprocess.check_output(["git", "-C", repo, "rev-parse", ref + "^{commit}"], text=True).strip()
        directory = out / label
        sources = prepare(repo, revision, binary, directory, packages)
        inputs[label] = sources
        if label == "candidate":
            if sources.keys() != inputs["parent"].keys() or {
                    name for name in sources if sources[name] != inputs["parent"][name]} != set(ROOTS[:3]):
                raise ValueError("The two complete project dependency cones differ outside the providers.")
        with (directory / "build.log").open("wb") as log:
            proc = subprocess.run([binary / "lake", "--no-cache", "build", *ROOTS], cwd=directory,
                                  env=env, stdout=log, stderr=subprocess.STDOUT)
        item = dict(revision=revision, source_blobs=sources, lake_exit=proc.returncode, kernels={})
        report["builds"][label] = item
        path = out / "results.json"
        path.write_text(json.dumps(report, indent=2) + "\n")
        proc.check_returncode()
        print(label, revision, len(sources), "physical project modules built", flush=True)
        for n in ROOTS:
            with (directory / (n + ".kernel.log")).open("wb") as log:
                proc = subprocess.run([binary / "lake", "--no-cache", "env", binary / "leanchecker", "-v", n],
                                      cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT)
            item["kernels"][n] = proc.returncode
            path.write_text(json.dumps(report, indent=2) + "\n")
            proc.check_returncode()
        print(label, "kernels", len(item["kernels"]), flush=True)


if __name__ == "__main__":
    main()
