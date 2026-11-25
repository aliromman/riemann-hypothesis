"""Check the fc_conj_k source failure or its fix with the pinned Lean compiler."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from audit_cone import source_path, verified_closure


MODULE = "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IndepDomK"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "project", "bin", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--expect-no-goals", action="store_true")
    args = parser.parse_args()
    repo, project, binary, out = [p.resolve() for p in (args.repo, args.project, args.bin, args.output)]
    revision = subprocess.check_output(
        ["git", "-C", repo, "rev-parse", "--verify", "--end-of-options", args.revision + "^{commit}"],
        text=True,
    ).strip()
    members = verified_closure(repo, revision, project, binary, [MODULE])
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_CONFIG", "LAKE_CACHE_DIR", "LAKE_RESTORE_ARTIFACTS"):
        env.pop(key, None)
    env.update(PATH=str(binary) + os.pathsep + env["PATH"], LAKE_ARTIFACT_CACHE="false", LEAN_ABORT_ON_PANIC="1")
    env.setdefault("LEAN_NUM_THREADS", "2")
    version = subprocess.check_output([binary / "lean", "--version"], env=env, text=True).strip()
    release = (project / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
    if "version " + release + "," not in version:
        raise ValueError("Use the toolchain in lean-toolchain.")
    packages = project / ".lake/packages"
    for package in json.loads((project / "lake-manifest.json").read_bytes())["packages"]:
        checkout = packages / package["name"]
        actual = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise ValueError("Incorrect package revision for " + package["name"])
        subprocess.run(["git", "-C", checkout, "diff", "--quiet", "HEAD", "--"], check=True)
    out.mkdir(parents=True, exist_ok=False)
    path = source_path(MODULE)
    record = dict(revision=revision, lean=version, module=MODULE, project_modules=len(members),
                  source_sha256=hashlib.sha256((project / path).read_bytes()).hexdigest(), runs={})

    def run(label, command):
        log = out / (label + ".log")
        with log.open("wb") as fp:
            result = subprocess.run(command, cwd=project, env=env, stdout=fp, stderr=subprocess.STDOUT)
        data = log.read_bytes()
        lines = data.decode(errors="replace").splitlines()
        errors = [s for s in lines if s.startswith("error:") and s != "error: build failed"]
        record["runs"][label] = dict(command=[Path(command[0]).name, *command[1:]], exit=result.returncode,
                                     source_errors=errors, log_sha256=hashlib.sha256(data).hexdigest())
        (out / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        return result.returncode, lines, errors

    lake = [str(binary / "lake"), "--no-cache"]
    code, lines, errors = run("build", [*lake, "--rehash", "build", MODULE])
    if args.expect_no_goals:
        error = re.compile(r"error: (?:\./)?" + re.escape(path.as_posix()) + r":\d+:\d+: No goals to be solved")
        if code != 1 or len(errors) != 1 or not error.fullmatch(errors[0]):
            raise RuntimeError("Expected one trailing-tactic error. See build.log.")
        return
    if code or errors or not any(s.startswith("Build completed successfully") for s in lines):
        raise RuntimeError("The module failed its build. See build.log.")
    code, lines, _ = run("check", [*lake, "--rehash", "build", "--no-build", MODULE])
    if code or not any(s.startswith("All targets up-to-date") for s in lines):
        raise RuntimeError("The module failed its up-to-date check. See check.log.")
    code, lines, _ = run("kernel", [*lake, "env", "leanchecker", "-v", MODULE])
    if code or "replaying " + MODULE not in lines:
        raise RuntimeError("The module failed kernel replay. See kernel.log.")


if __name__ == "__main__":
    main()
