"""Warm an isolated Lake build with verified, unaffected modules from its base revision."""
import argparse
from collections import defaultdict
import errno
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def closure(graph, roots):
    seen = set(roots)
    todo = list(roots)
    while todo:
        for child in graph.get(todo.pop(), ()):
            if child not in seen:
                seen.add(child)
                todo.append(child)
    return seen


def module(path):
    return path.removeprefix("src/").removesuffix(".lean").replace("/", ".")


def file_digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def base_manifest(ci, project, directory, base, source_tree):
    identity = dict(ci.current_identity(project), source_tree=source_tree)
    receipt_path = directory / "identity.json"
    if receipt_path.exists():
        metadata = json.loads(receipt_path.read_bytes())
        if metadata["requested"] != base or metadata["identity"] != identity:
            raise ValueError("The saved cache metadata belongs to different build inputs.")
        record = ci.matching_record(json.dumps(metadata["receipt"]).encode(), identity)
        def fetch(key, limit):
            return (directory / Path(key).name).read_bytes()
    else:
        directory.mkdir(parents=True, exist_ok=True)
        fingerprint = ci.fingerprint(identity)
        record = None
        for key in (f"ci/inputs/{fingerprint}.json", f"ci/revisions/{base}.json"):
            data = ci.fetch(key, ci.MAX_RECEIPT)
            if data is not None:
                record = ci.matching_record(data, identity)
                if record:
                    break
        def fetch(key, limit):
            data = ci.fetch(key, limit)
            if data is not None:
                (directory / Path(key).name).write_bytes(data)
            return data
    if not record:
        raise ValueError("The upstream cache has no successful build for the base inputs.")
    _, hashes, entries = ci.validated_blobs(record, identity, fetch)
    if not receipt_path.exists():
        receipt_path.write_text(json.dumps(dict(requested=base, identity=identity,
                                                fingerprint=ci.fingerprint(identity), receipt=record), indent=2) + "\n")
    return identity, record, hashes, entries


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for arg in ("project", "headers", "metadata", "out", "bin"):
        ap.add_argument("--" + arg, type=Path, required=True)
    ap.add_argument("--donor", type=Path, action="append", default=[])
    ap.add_argument("--base", required=True)
    ap.add_argument("--head", required=True)
    ap.add_argument("--stage", required=True)
    ap.add_argument("targets", nargs="*")
    a = ap.parse_args()
    project, out = a.project.resolve(), a.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    lock = (out/"restore.lock").open("a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def git(*args):
        return subprocess.check_output(["git", "-C", project, *args])
    def ref(name):
        return git("rev-parse", "--verify", name).decode().strip()
    def tree(rev):
        result = {}
        for row in git("ls-tree", "-rz", rev, "--", "src").split(b"\0"):
            if row.endswith(b".lean"):
                meta, name = row.split(b"\t", 1)
                result[module(name.decode())] = meta.split()[2].decode()
        return result
    def save(path, payload):
        tmp = path.with_suffix(".writing")
        tmp.write_text(json.dumps(payload, indent=2) + "\n")
        tmp.replace(path)

    if ref("HEAD") != a.head or ref("HEAD^1") != a.base:
        raise ValueError("The worktree or first parent differs from the requested merge.")
    git("diff", "--quiet", "HEAD", "--")
    if git("ls-files", "--others", "--exclude-standard", "--", "src"):
        raise ValueError("The source tree has untracked inputs.")
    parent, head = tree(a.base), tree(a.head)
    changed = {n for n in head if parent.get(n) != head[n]}
    paths = set(git("diff", "--name-only", "-z", a.base, a.head).decode().strip("\0").split("\0"))
    if set(parent) != set(head) or paths != {"src/" + n.replace(".", "/") + ".lean" for n in changed}:
        raise ValueError("The reuse proof requires a source-only change with the same module paths.")
    graph = {}
    with a.headers.open() as stream:
        info = json.loads(next(stream))
        if info["revision"] != a.head or info["src"] != ref("HEAD:src"):
            raise ValueError("Native headers belong to another tree.")
        for path, oid, _, imports in map(json.loads, stream):
            n = module(path)
            if oid != head[n] or n in graph:
                raise ValueError("Native source identity differs for " + n)
            graph[n] = [imp[0] for imp in imports if imp[0] in head]
    if graph.keys() != head.keys():
        raise ValueError("Incomplete native import graph.")
    consumers = defaultdict(list)
    for name, deps in graph.items():
        for dep in deps:
            consumers[dep].append(name)
    affected = closure(consumers, changed)
    if any(n not in graph for n in a.targets):
        raise ValueError("A target is missing from the dependency graph.")
    selected = closure(graph, a.targets) if a.targets else set(graph)

    spec = importlib.util.spec_from_file_location("rh_ci_cache", project/"scripts/ci-cache-get.py")
    ci = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ci)
    identity, record, hashes, entries = base_manifest(ci, project, a.metadata, a.base, ref(a.base + ":src"))
    pin = (project/"lean-toolchain").read_text().strip()
    version = subprocess.check_output([a.bin/"lean","--version"],text=True).strip()
    if identity["toolchain"] != pin or "version " + pin.split(":v")[-1] + "," not in version:
        raise ValueError("The cache and native compiler releases differ.")
    index = {r[0]: r for r in entries}
    if set(graph) - set(index) - {"Challenge"} or set(index) - set(graph):
        raise ValueError("Base manifest and project modules differ.")
    ledger = out/"restored.tsv"
    prior = {}
    if ledger.exists():
        for row in ledger.read_text().splitlines():
            name, digest = row.split("\t")
            if name in affected or hashes[index[name][2]] != digest:
                raise ValueError("The existing ledger contains an ineligible module.")
            prior[name] = digest
    plan = dict(merge=a.head, base=a.base, source_tree=info["src"], lean=version,
                donor=record["candidate_head"], manifest=record["module_manifest_sha256"], changed=sorted(changed),
                total_modules=len(head), all_affected=len(affected), targets=a.targets,
                closure=len(selected), affected_in_closure=len(selected & affected))
    wanted = sorted((selected - affected) & index.keys() - prior.keys())
    save(out/(a.stage+"-plan.json"),plan)
    print(a.stage, "planned",plan["closure"],"affected",plan["affected_in_closure"],
          "unaffected to restore",len(wanted),flush=True)
    added = fetched = reused = 0
    with ledger.open("a") as log:
        for start in range(0,len(wanted),96):
            rows = [index[n] for n in wanted[start:start+96]]
            with tempfile.TemporaryDirectory(dir=out) as temp:
                stage = Path(temp)
                artifacts = stage/"artifacts"
                artifacts.mkdir()
                missing = {}
                for _, key, name in rows:
                    target = artifacts/name
                    if target.exists() or name in missing:
                        continue
                    for donor in a.donor:
                        candidate = donor/name
                        if candidate.is_symlink():
                            continue
                        try:
                            os.link(candidate, target)
                        except FileNotFoundError:
                            continue
                        except OSError as exc:
                            if exc.errno != errno.EXDEV:
                                raise
                            shutil.copyfile(candidate, target)
                        if file_digest(target) != hashes[name]:
                            target.unlink()
                            continue
                        reused += 1
                        break
                    else:
                        missing[name] = key
                if missing:
                    ci.write_map(stage/"map.jsonl", [(key,name) for name,key in missing.items()])
                    (stage/"hashes.json").write_text(json.dumps({name:hashes[name] for name in missing}))
                    subprocess.run([sys.executable, "-I", ci.FETCH_ARTIFACTS, stage/"map.jsonl", stage,
                                    "--sha256",stage/"hashes.json","--verify-existing","--user-agent",ci.USER_AGENT],
                                   cwd=project, check=True)
                    fetched += len(missing)
                jobs = ci.unpack_jobs(project, stage, rows)
                for job in jobs:
                    for dest in job["base"]:
                        Path(dest).mkdir(parents=True, exist_ok=True)
                ci.clear_output_hashes(project, rows)
                subprocess.run([a.bin/"leantar","--jobs","3","-f","-x","-j","-"],
                               cwd=project, input=json.dumps(jobs), text=True, check=True)
                for n, _, name in rows:
                    log.write(n+"\t"+hashes[name]+"\n")
                log.flush()
                added += len(rows)
            if start % 960 == 0 or added == len(wanted):
                print(a.stage,added,"/",len(wanted),"existing archives",reused,"downloads",fetched,flush=True)
    save(out/(a.stage+"-restored.json"), dict(**plan, newly_restored=added, reused_archives=reused,
                                              downloads=fetched, previously_restored=len(prior)))


if __name__ == "__main__":
    main()
