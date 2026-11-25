"""Advance two completed matrix test builds to new Git trees and rehash all inputs."""
import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from audit_cone import source_path, verified_closure


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "prior", "out", "bin"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--base", required=True)
    parser.add_argument("--candidate", required=True)
    args = parser.parse_args()
    repo, prior, out, binary = [p.resolve() for p in (args.repo, args.prior, args.out, args.bin)]
    if prior == out:
        raise ValueError("Use separate directories for the old and new builds.")
    out.mkdir(exist_ok=True)
    locks = [(root / "advance.lock").open("a") for root in (prior, out)]
    for lock in locks:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    if (out / "builds.json").exists():
        raise ValueError("This output already contains a completed build.")
    attempt = out / datetime.now(timezone.utc).strftime("attempt-%Y%m%dT%H%M%S.%fZ")
    attempt.mkdir()
    config = ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2",
               LEAN_ABORT_ON_PANIC="1", LAKE_ARTIFACT_CACHE="false")
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_CONFIG", "LAKE_CACHE_DIR", "LAKE_RESTORE_ARTIFACTS"):
        env.pop(key, None)
    version = subprocess.check_output([binary / "lean", "--version"], text=True).strip()
    if version != json.loads((prior / "builds.json").read_bytes())["lean"]:
        raise ValueError("The compiler differs from the earlier build.")
    prepared = []
    for side, rev in (("main", args.base), ("candidate", args.candidate)):
        old = prior / side
        project = out / side
        receipt = json.loads((prior / (side + "-build.json")).read_bytes())
        runs = receipt["runs"]
        for label, run in zip(("build", "check"), runs, strict=True):
            prior_log = prior / run.get("log", side + "-" + label + ".log")
            if run["exit"] or digest(prior_log) != run["log_sha256"]:
                raise ValueError("The earlier build receipt or log is incomplete.")
        roots = receipt["targets"]
        members = verified_closure(repo, receipt["revision"], old, binary, roots)
        inputs = sorted(source_path(n) for n in members)
        if not project.exists():
            temp = attempt / (side + "-sources")
            temp.mkdir()
            archive = subprocess.check_output(["git", "-C", repo, "archive", rev, "--", *config, *inputs])
            subprocess.run(["tar", "-xf", "-", "-C", temp], input=archive, check=True)
            temp.rename(project)
        if verified_closure(repo, rev, project, binary, roots) != members:
            raise ValueError("The new dependency set differs from the retained build.")
        if any((old / p).read_bytes() != (project / p).read_bytes() for p in config):
            raise ValueError("The compiler, packages or Lake configuration changed.")
        packages = (old / ".lake/packages").resolve(strict=True)
        for pkg in json.loads((project / "lake-manifest.json").read_bytes())["packages"]:
            checkout = packages / pkg["name"]
            head = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
            if pkg["rev"] != head:
                raise ValueError("Incorrect package revision: " + pkg["name"])
            subprocess.run(["git", "-C", checkout, "diff", "--quiet", "HEAD", "--"], check=True)
        (project / ".lake").mkdir(exist_ok=True)
        link = project / ".lake/packages"
        if not link.exists():
            link.symlink_to(packages, target_is_directory=True)
        if link.resolve(strict=True) != packages:
            raise ValueError("The destination uses different packages.")
        old_build, new_build = (p / ".lake/build" for p in (old, project))
        if old_build.is_symlink() or new_build.is_symlink():
            raise ValueError("Use private build directories for " + side)
        if old_build.is_dir() == new_build.is_dir():
            raise ValueError("There must be one retained build for " + side)
        lib = (old_build if old_build.is_dir() else new_build) / "lib/lean"
        names = {p.relative_to(lib).with_suffix("").as_posix().replace("/", ".") for p in lib.rglob("*.olean")}
        if names - members or (old_build.is_dir() and names != members):
            raise ValueError("The retained module set differs from the verified closure.")
        changes = [p.as_posix() for p in inputs if (old / p).read_bytes() != (project / p).read_bytes()]
        result = dict(revision=rev, previous=receipt["revision"], targets=roots, modules=len(members),
                      changed_sources=changes, runs=[])
        prepared.append((side, old, project, result))

    results = {}
    for side, old, project, result in prepared:
        if (old / ".lake/build").is_dir():
            (old / ".lake/build").rename(project / ".lake/build")
        target_receipt = attempt / (side + "-build.json")
        target_receipt.write_text(json.dumps(result, indent=2) + "\n")
        for label, options in (("build", []), ("check", ["--no-build"])):
            cmd = ["lake", "--no-cache", "--rehash", "build", *options, *result["targets"]]
            log = attempt / (side + "-" + label + ".log")
            with log.open("wb") as stream:
                run = subprocess.run(cmd, cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT)
            lines = log.read_text(errors="replace").splitlines()
            completion = [s for s in lines if s.startswith(("Build completed successfully", "All targets up-to-date"))]
            built = re.findall(r"^[✔⚠] \[\d+/\d+\] Built (\S+) \(", "\n".join(lines), re.M)
            result["runs"].append(dict(command=cmd, exit=run.returncode, completion=completion,
                                       log=log.relative_to(out).as_posix(), log_sha256=digest(log),
                                       freshly_compiled=built))
            target_receipt.write_text(json.dumps(result, indent=2) + "\n")
            print(side, label, run.returncode, completion, flush=True)
            if run.returncode or not completion:
                raise SystemExit("See " + str(log))
        (out / (side + "-build.json")).write_bytes(target_receipt.read_bytes())
        results[side] = result
    (out / "builds.json").write_text(json.dumps(dict(lean=version, results=results), indent=2) + "\n")


if __name__ == "__main__":
    main()
