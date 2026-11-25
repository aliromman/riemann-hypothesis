"""Build and hash the upstream five-statement challenge on a trusted base and a proposed merge."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

CONFIG = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json", "export-targets.txt")
PROTECTED = ("src/Main.lean", "src/Challenge.lean", "comparator/FormalConjecturesChallenge.lean",
             "comparator/formal-conjectures.json", "comparator/formal-conjectures-export-targets.txt")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "bin", "packages", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--base", required=True)
    parser.add_argument("--merge", required=True)
    a = parser.parse_args()
    repo, binary, packages, out = (x.resolve() for x in (a.repo, a.bin, a.packages, a.output))
    def git(*args):
        return subprocess.check_output(["git", "-C", repo, *args])
    revisions = {side: git("rev-parse", "--verify", "--end-of-options", rev + "^{commit}").decode().strip()
                 for side, rev in (("base", a.base), ("merge", a.merge))}
    git("merge-base", "--is-ancestor", revisions["base"], revisions["merge"])
    def inputs(rev):
        return {p: git("show", rev + ":" + p) for p in (*CONFIG, *PROTECTED)}
    trusted = inputs(revisions["base"])
    if inputs(revisions["merge"]) != trusted:
        raise ValueError("The protected source or build inputs differ.")
    cfg = json.loads(trusted["comparator.json"])
    names, axioms = cfg["theorem_names"], cfg["permitted_axioms"]
    targets = trusted["export-targets.txt"].decode().split()
    if (len(set(names)) != 5 or set(axioms) != {"propext", "Quot.sound", "Classical.choice"}
            or not set(names + axioms) <= set(targets)):
        raise ValueError("Unexpected Comparator settings.")
    for pkg in json.loads(trusted["lake-manifest.json"])["packages"]:
        if subprocess.check_output(["git", "-C", packages / pkg["name"], "rev-parse", "HEAD"], text=True).strip() != pkg["rev"]:
            raise ValueError("Installed package differs from the lock: " + pkg["name"])
    version = subprocess.check_output([binary / "lean", "--version"], text=True).strip()
    if "version " + trusted["lean-toolchain"].decode().strip().split(":v")[-1] + "," not in version:
        raise ValueError("The Lean version differs from the pin.")
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2",
               LEAN_ABORT_ON_PANIC="1", LAKE_ARTIFACT_CACHE="false")
    out.mkdir(parents=True, exist_ok=True)
    results = {}
    for side, rev in revisions.items():
        with tempfile.TemporaryDirectory(dir=out) as scratch:
            project = Path(scratch)
            for path in (*CONFIG, "src/Challenge.lean"):
                f = project / path
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_bytes(git("show", rev + ":" + path))
            (project / ".lake").mkdir()
            (project / ".lake/packages").symlink_to(packages, target_is_directory=True)
            with (out / (side + "-build.log")).open("wb") as log:
                build = subprocess.run([binary / "lake", "--no-cache", "build", "Challenge"],
                                       cwd=project, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
            digest, size = hashlib.sha256(), 0
            with (out / (side + "-export.log")).open("wb") as log:
                with subprocess.Popen([binary / "lake", "--no-cache", "env", binary / "leanexport",
                                       "Challenge", "--", *targets], cwd=project, env=env,
                                      stdout=subprocess.PIPE, stderr=log) as exp:
                    for chunk in iter(lambda: exp.stdout.read(1024 * 1024), b""):
                        digest.update(chunk)
                        size += len(chunk)
                    if exp.wait() or size == 0:
                        raise ValueError("Challenge export failed on " + side)
                    results[side] = dict(build_exit=build.returncode, export_exit=exp.returncode,
                                         bytes=size, sha256=digest.hexdigest())
            print(side, rev, size, digest.hexdigest(), flush=True)
    if results["base"] != results["merge"]:
        raise ValueError("The two exports differ.")
    record = dict(revisions=revisions, lean=version, theorem_names=names, permitted_axioms=axioms,
                  source_sha256={p: hashlib.sha256(data).hexdigest() for p, data in trusted.items()},
                  results=results)
    (out / "receipt.json").write_text(json.dumps(record, indent=2) + "\n")

if __name__ == "__main__":
    main()
