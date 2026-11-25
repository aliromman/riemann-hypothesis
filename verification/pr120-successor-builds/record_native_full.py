"""Record a stock Lake build and its subsequent up-to-date check on a pinned merge."""
import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("project","out","bin"):
        parser.add_argument("--"+arg, required=True, type=Path)
    parser.add_argument("--stage", required=True)
    parser.add_argument("--jobs", required=True, type=int)
    parser.add_argument("--rehash", action="store_true", help="Recompute file hashes in a previously built checkout.")
    parser.add_argument("targets", nargs="*")
    a = parser.parse_args()
    project, out, binary = [d.resolve() for d in (a.project,a.out,a.bin)]
    lock = (out/"restore.lock").open("a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    plan = json.loads((out/(a.stage+"-restored.json")).read_bytes())
    def git(*args):
        return subprocess.check_output(["git","-C",project,*args],text=True).strip()
    def identity():
        if git("rev-parse","HEAD") != plan["merge"] or git("rev-parse","HEAD:src") != plan["source_tree"]:
            raise ValueError("The build tree changed.")
        git("diff","--quiet","HEAD","--")
        if git("ls-files","--others","--exclude-standard","--","src"):
            raise ValueError("Untracked source files in the build tree.")
    identity()
    if a.targets != plan["targets"] or a.jobs < 1:
        raise ValueError("The build options differ from the verified restore plan.")
    env = {k:v for k,v in os.environ.items() if k not in
           {"LEAN_PATH","LEAN_SRC_PATH","LEAN_SYSROOT","LAKE_CONFIG","LAKE_CACHE_DIR","LAKE_RESTORE_ARTIFACTS"}}
    env.update(PATH=str(binary)+os.pathsep+env["PATH"], LEAN_NUM_THREADS=str(a.jobs),
               LEAN_ABORT_ON_PANIC="1", LAKE_ARTIFACT_CACHE="false", RUST_MIN_STACK="8388608")
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    cap = 65536 if hard == resource.RLIM_INFINITY else min(65536,hard)
    resource.setrlimit(resource.RLIMIT_NOFILE,(max(soft,cap),hard))
    version = subprocess.check_output([binary/"lean","--version"],env=env,text=True).strip()
    if version != plan["lean"]:
        raise ValueError("The compiler changed.")
    attempt = out/(a.stage+"-"+datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
    attempt.mkdir()
    receipt = dict(merge=plan["merge"], head=git("rev-parse","HEAD^2"), base=plan["base"],
                   tree=git("rev-parse","HEAD^{tree}"), source_tree=plan["source_tree"],
                   lean=version, targets=a.targets, closure=plan["closure"], affected_in_closure=plan["affected_in_closure"],
                   cache_manifest=plan["manifest"], cache_donor=plan["donor"], jobs=a.jobs, rehash=a.rehash,
                   started=timestamp(), runs=[])
    def save():
        f=attempt/"result.tmp"
        f.write_text(json.dumps(receipt,indent=2)+"\n")
        f.replace(attempt/"result.json")
    save()
    for label, args in (("build", [*a.targets]),("check", ["--no-build",*a.targets])):
        logfile = attempt/(label+".log")
        options = ["--no-cache"]
        if a.rehash:
            options.append("--rehash")
        command = [str(binary/"lake"),*options,"build",*args]
        with logfile.open("wb") as stream:
            job=subprocess.run(command,cwd=project,env=env,stdout=stream,stderr=subprocess.STDOUT)
        with logfile.open(errors="replace") as stream:
            errors = [line.rstrip()[:1500] for line in stream if re.search(r"(error:|uncaught exception|PANIC)",line,re.I)]
        receipt["runs"].append(dict(command=["lake",*command[1:]],exit=job.returncode,
                                    log_sha256=digest(logfile),errors=errors[:24],finished=timestamp()))
        save()
        print(a.stage,label,job.returncode, "first error",errors[:1],flush=True)
        if job.returncode:
            return job.returncode
    identity()
    facets = {}
    for name in a.targets or ["Main"]:
        path = (project/".lake/build/lib/lean").joinpath(*name.split(".")).with_suffix(".olean")
        facets[name] = dict(bytes=path.stat().st_size,sha256=digest(path))
    receipt["target_oleans"]=facets
    receipt["completed"]=timestamp()
    save()
    (out/(a.stage+"-passed.json")).write_bytes((attempt/"result.json").read_bytes())
    return 0


if __name__ == "__main__":
    sys.exit(main())
