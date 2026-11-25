"""Build one pair of pinned source trees with the published community cache."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def git(*args):
    return command_output("git", *args)


def command_output(*args):
    return subprocess.check_output(args, text=True).strip()


def load_script(name):
    spec = importlib.util.spec_from_file_location(name, Path("scripts", name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def digest(names):
    return hashlib.sha256(("\n".join(sorted(names)) + "\n").encode()).hexdigest()


def source(name):
    return Path("src", *name.split(".")).with_suffix(".lean")


def dependencies(roots):
    graph, external, pending = {}, set(), set(roots)
    while pending:
        layer = sorted(pending)
        pending.clear()
        for start in range(0, len(layer), 128):
            group = layer[start:start + 128]
            data = subprocess.check_output(["lean", "--deps-json", *map(source, group)])
            rows = json.loads(data)["imports"]
            for name, row in zip(group, rows, strict=True):
                if row["errors"]:
                    raise ValueError((name, row["errors"]))
                deps = {entry["module"] for entry in row["result"]["imports"]}
                graph[name] = {dep for dep in deps if source(dep).is_file()}
                external.update(deps - graph[name])
                pending.update(graph[name] - graph.keys())
        pending.difference_update(graph)
    return graph, external


def affected(graph, changed):
    reverse = {name: [] for name in graph}
    for name, dependencies_ in graph.items():
        for dep in dependencies_:
            reverse[dep].append(name)
    visited, remaining = set(), list(changed)
    while remaining:
        name = remaining.pop()
        if name not in visited:
            visited.add(name)
            remaining.extend(reverse[name])
    return visited


def restore(root, cache, plan, graph):
    ci = load_script("ci-cache-get")
    prep = load_script("ci-prepare")
    identity = ci.current_identity(root)
    if identity != plan["identity"]:
        raise ValueError("The community source and package identity changed.")
    raw = ci.fetch("ci/revisions/" + plan["donor"] + ".json", ci.MAX_RECEIPT)
    record = ci.matching_record(raw, identity) if raw else None
    if not record or (record["candidate_head"], record["module_manifest_sha256"]) != (
            plan["donor"], plan["manifest"]):
        raise ValueError("The parent receipt does not match the pinned manifest.")
    _, hashes, rows = ci.validated_blobs(record, identity)
    by_name = {row[0]: row for row in rows}
    chosen = [by_name[n] for n in sorted(graph)]
    leantar = Path(command_output("elan", "which", "lean")).with_name("leantar")
    cache.mkdir()
    compressed = 0
    for start in range(0, len(chosen), 48):
        batch = chosen[start:start + 48]
        prep.downloads(cache, {key: name for _, key, name in batch}, hashes)
        jobs = ci.unpack_jobs(root, cache, batch)
        subprocess.run([leantar, "--jobs", "2", "-f", "-x", "-j", "-"],
                       input=json.dumps(jobs), text=True, check=True)
        for archive in {archive for _, _, archive in batch}:
            entry = cache / "artifacts" / archive
            compressed += entry.stat().st_size
            entry.unlink()
        if start % (48 * 20) == 0:
            print("Restored", start + len(batch), "of", len(chosen), flush=True)
    return compressed


def logged(command, path):
    with path.open("w") as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        with path.open(errors="replace") as lines:
            errors = (line.rstrip() for line in lines if "error:" in line)
            for _, error in zip(range(12), errors):
                print(error, flush=True)
        with path.open("rb") as output:
            output.seek(max(0, path.stat().st_size - 12000))
            print(output.read().decode(errors="replace"), flush=True)
        result.check_returncode()


def packages(externals):
    families = {"Mathlib", "Aesop", "Batteries", "Qq", "Cli", "ImportGraph",
                "LeanSearchClient", "Plausible", "ProofWidgets"}
    modules = {d for d in externals if d.partition(".")[0] in families}
    if "Mathlib" in modules:
        modules = {d for d in modules if not d.startswith("Mathlib.")}
    return modules


def run():
    plan = json.loads(Path(sys.argv[1]).read_bytes())
    job = plan["jobs"][sys.argv[2]]
    root = Path.cwd()
    parent, candidate = plan["base"], job["candidate"]
    if (root / ".lake/build").exists():
        raise ValueError("Use a fresh checkout for this comparison. It replaces project compiler outputs.")
    if git("rev-parse", "HEAD") != parent:
        raise ValueError("The checkout does not match the comparison parent.")
    subprocess.run(["git", "fetch", "--no-tags", "--depth=1",
                    "https://github.com/aliromman/riemann-hypothesis.git", candidate], check=True)
    if git("rev-parse", candidate + "^{tree}") != job["tree"]:
        raise ValueError("The candidate tree differs from the request.")
    names = subprocess.check_output(["git", "diff", "--name-only", "-z", parent, candidate])
    files = sorted(name.decode() for name in names.split(b"\0") if name)
    changed = set(job["changed"])
    if files != sorted(str(source(name)) for name in changed):
        raise ValueError("The Git diff and the declared source changes differ.")
    roots = job["roots"]
    if not changed <= set(roots):
        raise ValueError("Some changed sources are outside the target list.")
    receipt = dict(base=parent, candidate=candidate, tree=job["tree"], targets=roots,
                   lean=command_output("lean", "--version"), donor=plan["donor"],
                   module_manifest_sha256=plan["manifest"], runs=[])
    previous = set()
    with tempfile.TemporaryDirectory(prefix="rh-successor-", dir=os.environ.get("RUNNER_TEMP")) as tmp:
        work = Path(tmp)
        for revision in (parent, candidate):
            if revision == candidate:
                subprocess.run(["git", "switch", "--detach", candidate], check=True)
            graph, ext = dependencies(roots)
            rebuild = affected(graph, changed)
            if (len(graph), digest(graph), digest(rebuild)) != (
                    job["cone_count"], job["cone_sha256"], job["affected_sha256"]):
                raise ValueError("The native import graph differs from the declared graph.")
            needed = packages(ext)
            if needed - previous:
                logged(["lake", "exe", "mathlib/cache", "get", *sorted(needed - previous)],
                       work / (revision + "-mathlib.log"))
                previous.update(needed)
            if revision == parent:
                receipt["archive_bytes"] = restore(root, work / "cache", plan, graph)
            fresh = set(roots) if revision == parent else rebuild | set(roots)
            for name in fresh:
                path = root / ".lake/build/lib/lean" / Path(*name.split("."))
                for ext_ in (".trace", ".olean", ".olean.hash"):
                    path.with_suffix(ext_).unlink(missing_ok=True)
            print("Building", revision, "targets", len(roots), "project modules", len(graph),
                  "forced", len(fresh), "free bytes", shutil.disk_usage(work).free, flush=True)
            logged(["lake", "--no-cache", "build", *roots], work / (revision + "-build.log"))
            for index, name in enumerate(job["kernel"]):
                logged(["lake", "--no-cache", "env", "leanchecker", "-v", name],
                       work / (revision + f"-kernel-{index}.log"))
            if git("status", "--porcelain", "--untracked-files=no"):
                raise ValueError("The build changed tracked files.")
            result = dict(revision=revision, build_exit=0, kernel_exit=0, kernels=job["kernel"],
                          project_modules=len(graph), cone_sha256=digest(graph), rebuilt=len(fresh))
            receipt["runs"].append(result)
            print("RH_TARGET_SIDE", json.dumps(result), flush=True)
    print("RH_TARGET_RESULT", json.dumps(receipt, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    run()
