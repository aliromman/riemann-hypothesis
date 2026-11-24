"""Measure the stock plan and apply commands on one complete checkout.

Usage: python cli_trials.py CHECKOUT TOOLS OUTPUT
TOOLS contains community.py, published.py, and proposed.py at the pinned digests below.
Each measurement uses a fresh Python process.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time

TOOL_SHA = {
    "community": "56992181fe3454c03e8e90fc771aff482dfdc4b39bf58ac3d8f191f42466ca44",
    "published": "01a81b1a58da622db0427e99139e3b399aa12fae43cde2d59aa709795c3bcade",
    "proposed": "532a111c35fb0a3fc26cecc28e97dd7d9b19d0d2d63a3a36b59e20d20bad3dcf",
}
HEADS = ("f6177155e8e440c0a831d4c15de4c74341de0a93", "e7127ce8136d8ed36e610884d8578de1cffadd19")
SOURCE = "a908624cdba9bc8f9a5ce5268f6947a8ba2cd505"
PLAN = "7f008f70f550f162cba7e1b23b8b15309086d8efd3ff8c0c4a2ff9ed4521a175"
STREAMS = {
    "community": "9566483e9bd36d62c63a22a9413f1f21cf646a4863922b457dba85ec54e2529a",
    "published": "6c6ae23dbf326a53cb168c6014c86f27ece96f6da66dd046dfdb3e1b11c161d0",
    "proposed": "6c6ae23dbf326a53cb168c6014c86f27ece96f6da66dd046dfdb3e1b11c161d0",
}
def digest(data):
    return hashlib.sha256(data).hexdigest()

def canonical(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()

def git(project, *args):
    return subprocess.check_output(["git", "-c", "core.commitGraph=false", *args], cwd=project)

def path(name):
    return "src/" + name.replace(".", "/") + ".lean"

def load_tool(name, script):
    spec = importlib.util.spec_from_file_location("measure_" + name, script)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def source_census(project):
    tree = git(project, "ls-tree", "-rz", "HEAD", "--", "src").split(b"\0")
    checked = hashlib.sha256()
    files = {}
    for entry in tree:
        if not entry:
            continue
        desc, name = entry.split(b"\t", 1)
        if not name.endswith(b".lean"):
            continue
        mode, kind, oid = desc.split()
        assert mode == b"100644" and kind == b"blob"
        data = (project / name.decode()).read_bytes()
        got = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        assert got.encode() == oid, name
        checked.update(name + b"\0" + oid + b"\n")
        files[name.decode()] = oid.decode()
    assert len(files) == 59909
    return files, checked.hexdigest()

def run_cli(project, command, log):
    with log.open("wb") as output:
        start = time.perf_counter_ns()
        proc = subprocess.Popen(command, cwd=project, stdout=output, stderr=output)
        _, status, usage = os.wait4(proc.pid, 0)
        proc.returncode = os.waitstatus_to_exitcode(status)
        elapsed = (time.perf_counter_ns() - start) / 1e9
    if proc.returncode:
        raise RuntimeError(log.read_text(errors="replace")[-3000:])
    rss_unit = 1 if sys.platform == "darwin" else 1024
    return dict(wall_s=elapsed, cpu_s=usage.ru_utime + usage.ru_stime,
                user_s=usage.ru_utime, system_s=usage.ru_stime,
                peak_rss_bytes=usage.ru_maxrss * rss_unit)

def order(labels, trial):
    first = trial % len(labels)
    values = labels[first:] + labels[:first]
    if len(values) > 2 and trial % 2:
        values.reverse()
    return values

def medians(rows):
    groups = {}
    for command in ("plan", "apply"):
        groups[command] = {}
        for label in TOOL_SHA:
            measured = [r for r in rows if r["trial"] and (r["command"], r["tool"]) == (command, label)]
            if measured:
                assert len(measured) == 5
                groups[command][label] = {k: statistics.median(r[k] for r in measured)
                                         for k in ("wall_s", "cpu_s", "peak_rss_bytes")}
    return groups

def main():
    parser = argparse.ArgumentParser()
    for name in ("project", "tools", "output"):
        parser.add_argument(name, type=Path)
    parsed = parser.parse_args()
    project, tool_dir, result = (p.resolve() for p in (parsed.project, parsed.tools, parsed.output))
    result.mkdir(parents=True, exist_ok=True)
    scripts = {k: tool_dir / (k + ".py") for k in TOOL_SHA}
    assert all(digest(file.read_bytes()) == TOOL_SHA[label] for label, file in scripts.items())
    header = git(project, "rev-parse", "HEAD").decode().strip()
    assert header in HEADS and git(project, "rev-parse", "HEAD:src").decode().strip() == SOURCE
    git(project, "diff", "--exit-code", "--", "src")
    start_files, census = source_census(project)
    tracked = {n.decode() for n in git(project, "ls-files", "-z", "src/*.lean").split(b"\0") if n}
    assert tracked == start_files.keys()
    modules = {k: load_tool(k, p) for k, p in scripts.items()}
    rows = []
    plan_file = result / "saved-plan.json"
    child_log = result / "last-cli.log"
    observations = result / "observations.jsonl"
    def record(command, label, trial, stats, **extra):
        row = {"command": command, "tool": label, "trial": trial, **stats, **extra}
        rows.append(row)
        with observations.open("a", encoding="utf-8") as out:
            print(json.dumps(row, separators=(",", ":")), file=out)
        print(command, trial, label, f"{stats['wall_s']:.3f}", stats["peak_rss_bytes"], flush=True)
    observations.write_text("")
    for trial in range(6):
        for label in order(["published", "proposed"], trial):
            command = [sys.executable, "-B", scripts[label], "plan", project, "--out", plan_file,
                       "--exclude", project / "scripts/clump-exclude.txt"]
            stats = run_cli(project, command, child_log)
            sha = digest(plan_file.read_bytes())
            assert sha == PLAN
            record("plan", label, trial, stats, plan_sha256=sha)
    saved = json.loads(plan_file.read_bytes())
    if len(saved) != 199:
        raise ValueError("unexpected number of clumps")
    names = sorted({m for values in saved.values() for m in values})
    assert len(names) == sum(map(len, saved.values())) == 656 and saved.keys() <= set(names)
    originals = {name: (project / path(name)).read_bytes() for name in names}
    def restore():
        for name, data in originals.items():
            f = project / path(name)
            if not f.exists() or f.read_bytes() != data:
                f.write_bytes(data)
    for trial in range(6):
        for label in order(list(TOOL_SHA), trial):
            assert all((project / path(name)).read_bytes() == body for name, body in originals.items())
            try:
                stats = run_cli(project, [sys.executable, "-B", scripts[label], "apply", project, plan_file], child_log)
                outputs = {}
                for root, members in saved.items():
                    body = (project / path(root)).read_bytes()
                    recovered = modules[label].unclump_text(body.decode())
                    assert list(recovered) == members
                    assert all(recovered[n].encode() == originals[n] for n in members)
                    assert all(not (project / path(n)).exists() for n in members if n != root)
                    outputs[root] = digest(body)
                stream = digest(canonical(sorted(outputs.items())))
                assert stream == STREAMS[label]
                record("apply", label, trial, stats, output_root_stream_sha256=stream)
            finally:
                restore()
    end_files, after = source_census(project)
    assert end_files == start_files and after == census and len(rows) == 30
    git(project, "diff", "--exit-code", "--", "src")
    report = {"source_checkout": header, "source_tree": SOURCE, "members": len(names), "plan_roots": len(saved),
              "original_and_restored_tracked_files": len(start_files), "source_census_sha256": census,
              "tool_sha256": TOOL_SHA, "saved_plan_sha256": PLAN, "generated_root_streams": STREAMS,
              "order": "One warm-up per tool. Five scored rounds rotate the first tool. The plan uses two tools and apply uses three.",
              "python": sys.version, "platform": platform.platform(), "medians": medians(rows),
              "observations_sha256": digest(observations.read_bytes())}
    (result / "summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["medians"]), flush=True)
if __name__ == "__main__":
    main()

