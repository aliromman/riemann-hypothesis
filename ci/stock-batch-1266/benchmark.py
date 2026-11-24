"""Compare fresh serial Lean compilations of the predeclared changed roots on one runner."""
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import resource
import statistics
import subprocess
import sys
import tempfile
import time

WORK = Path(sys.argv[1]).resolve()
PARENT = Path(sys.argv[2]).resolve()
CANDIDATE = Path.cwd()
METRICS = ("cpu_seconds", "elapsed_seconds")
STATS = ("number of imported modules", "number of imported bytes", "number of imported consts")


def output(command, **kwargs):
    return subprocess.check_output(command, text=True, **kwargs)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def usage():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime, r.ru_stime


def header(path):
    entry, = json.loads(output(["lean", "--deps-json", path]))["imports"]
    if entry["errors"]:
        raise ValueError(f"Lean could not parse {path}")
    return entry["result"]


def sources(module, expected):
    relative = Path("src", *module.split(".")).with_suffix(".lean")
    paths = {k: root/relative for k, root in (("parent", PARENT), ("candidate", CANDIDATE))}
    data = {k: path.read_bytes() for k, path in paths.items()}
    if data["parent"] == data["candidate"] or any(digest(content) != expected[side] for side, content in data.items()):
        raise ValueError(f"the benchmark inputs differ from the declared source transition for {module}")
    headers = {side: header(path) for side, path in paths.items()}
    if not headers["parent"]["isModule"] or headers["parent"] != headers["candidate"]:
        raise ValueError(f"the structural source rewrite changed the actual import header for {module}")
    return relative, data, headers["parent"]


def compile_sample(module, source, setup, scratch, warmup):
    with tempfile.TemporaryDirectory(dir=scratch) as out:
        dest = Path(out)
        command = ["lean", "-j1", "--tstack=400000", f"--root={scratch/'src'}", f"--setup={setup}",
                   "-o", dest/"out.olean", "-i", dest/"out.ilean", "-c", dest/"out.c", "--json"]
        if warmup:
            command.append("--stats")
        before = usage()
        start = time.perf_counter()
        event = subprocess.run([*command, source], capture_output=True, text=True, timeout=350)
        elapsed = time.perf_counter() - start
        after = usage()
        if event.returncode:
            raise ValueError(f"{module} failed in Lean: {(event.stderr + event.stdout)[-3000:]}")
        if not all((dest/f"out.{ext}").is_file() for ext in ("olean", "ilean", "c")):
            raise ValueError(f"{module} did not generate all requested outputs")
        checked = json.loads(output([WORK/"check-interface", module, WORK/"parent"/(module+".olean"),
                                     dest/"out.olean", dest]))
        user, system = (y-x for x, y in zip(before, after))
        row = dict(cpu_seconds=user+system, elapsed_seconds=elapsed, user_seconds=user,
                   system_seconds=system, declarations=checked["candidateNames"], proof_changes=checked["proofChanges"])
        if warmup:
            for key in STATS:
                match = re.search(re.escape(key) + r":\s*(\d+)", event.stdout)
                if not match:
                    raise ValueError(f"Lean omitted {key} for {module}")
                row[key] = int(match[1])
        return row


def main():
    scope = json.loads((WORK/"report.json").read_bytes())
    panel = json.loads(Path(__file__).with_name("panel.json").read_bytes())
    names = [r["module"] for r in panel["benchmark"]]
    if len(names) != 6 or len(set(names)) != 6 or not set(names) <= set(scope["fresh"]) & set(scope["changed"]):
        raise ValueError("the six affected predeclared timing sources is not in the fresh integrated build")
    eligible = set(scope["changed"]) & set(scope["roots"])
    summary = dict(status="complete", method="Six roots from the original twelve-source panel have changed input closures. Warm-up and five serial matched pairs alternate parent-first and candidate-first order. Both revisions compile with the same unmodified stock Lake setup from the integrated tree, with one Lean thread. CPU is user plus system. Elapsed includes process launch and olean, ilean and C output. Hydration, dependency scheduling and declaration checks are outside the timer.",
                   eligible_changed_roots=len(eligible), candidate_source_tree=scope.get("candidate_source_tree"),
                   parent_source_tree=scope.get("source_tree"), lean=output(["lean", "--version"]).strip(),
                   system=platform.platform(), runner_image=os.environ.get("ImageVersion"),
                   logical_cpus=os.cpu_count(), initial_load_averages=os.getloadavg(), modules={}, totals={})
    with (WORK/"benchmark-samples.jsonl").open("w") as log, tempfile.TemporaryDirectory(dir=WORK) as temp:
        scratch = Path(temp)
        for k, name in enumerate(names):
            expected = panel["changed_sources"][name]
            relative, bodies, actual_header = sources(name, expected)
            actual = CANDIDATE/".lake/build/ir"/Path(*name.split(".")).with_suffix(".setup.json")
            compiler = json.loads(actual.read_bytes())
            if compiler["name"] != name or not compiler["isModule"] or not actual_header["isModule"]:
                raise ValueError(f"Lake set up a different module for {name}")
            setup = scratch/"module.setup.json"
            setup.write_text(json.dumps(compiler))
            source = scratch/relative
            source.parent.mkdir(parents=True, exist_ok=True)
            samples = {side: [] for side in bodies}
            for rep in range(6):
                order = ("parent", "candidate") if (k+rep) % 2 == 0 else ("candidate", "parent")
                for side in order:
                    source.write_bytes(bodies[side])
                    row = compile_sample(name, source, setup, scratch, rep == 0)
                    print(json.dumps(dict(module=name, side=side, pair=rep, warmup=rep==0, **row)), file=log, flush=True)
                    samples[side].append(row)
            result = dict(sample=panel["benchmark"][k], source_sha256={s: digest(b) for s,b in bodies.items()})
            for metric in METRICS:
                sides = {s: [r[metric] for r in samples[s][1:]] for s in bodies}
                parent, candidate = (statistics.median(v) for v in sides.values())
                result[metric] = dict(parent=parent, candidate=candidate, change_percent=100*(candidate/parent-1),
                                      ranges={s:[min(v), max(v)] for s,v in sides.items()},
                                      slower_pairs=[i+1 for i,(a,b) in enumerate(zip(*sides.values())) if b>a])
            for metric in STATS:
                result[metric] = {s: rows[0][metric] for s,rows in samples.items()}
            summary["modules"][name] = result
    for metric in METRICS:
        values = summary["modules"]
        parent, candidate = [sum(j[metric][s] for j in values.values()) for s in ("parent","candidate")]
        summary["totals"][metric] = dict(parent_sum_medians=parent, candidate_sum_medians=candidate,
            change_percent=100*(candidate/parent-1), slower_modules=[n for n,j in values.items() if j[metric]["candidate"]>j[metric]["parent"]])
    summary["final_load_averages"] = os.getloadavg()
    (WORK/"benchmark.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps(summary["totals"], indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        samples = WORK/"benchmark-samples.jsonl"
        count = len(samples.read_text().splitlines()) if samples.exists() else 0
        (WORK/"benchmark.json").write_text(json.dumps(dict(status="unavailable", reason=str(error),
                                                           completed_samples=count), indent=2)+"\n")
        raise
