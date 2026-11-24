"""Judge up to two edited panel theorems against their published parent exports."""

import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import tempfile
import time

EXPORT_LIMIT = 96 * 1024**2
KERNELS = ("Lean default", "Lean paranoid", "nanoda")


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2) + "\n")


def limited_process(command, cwd, env, outfile, errfile, seconds, *, is_export=False):
    def cap():
        resource.setrlimit(resource.RLIMIT_FSIZE, (EXPORT_LIMIT, EXPORT_LIMIT))

    with outfile.open("wb") as out, errfile.open("wb") as err:
        with subprocess.Popen(
            command,
            cwd=cwd,
            env=env,
            stdout=out,
            stderr=err,
            start_new_session=True,
            preexec_fn=cap if is_export else None,
        ) as proc:
            try:
                return proc.wait(timeout=seconds)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                raise


def inspect_export(path, target):
    # Follow the target's name prefixes in Lean's JSONL export. A theorem
    # record must carry a proof expression index on both sides.
    prefixes = {0: ""}
    index = None
    proof = None
    digest = hashlib.sha256()
    with path.open("rb") as f:
        for line in f:
            digest.update(line)
            if line.startswith(b'{"in":'):
                obj = json.loads(line)
                part = obj.get("str")
                if not part or part["pre"] not in prefixes:
                    continue
                name = (prefixes[part["pre"]] + "." + part["str"]).lstrip(".")
                if target == name or target.startswith(name + "."):
                    prefixes[obj["in"]] = name
                if name == target:
                    index = obj["in"]
            elif index is not None and line.startswith(b'{"thm":'):
                decl = json.loads(line)["thm"]
                if decl["name"] == index:
                    proof = decl["value"]
    if not isinstance(proof, int) or proof < 0:
        raise ValueError(f"{target} has no theorem proof in {path.name}")
    return dict(bytes=path.stat().st_size, sha256=digest.hexdigest(), theorem_proof_expr_index=proof)


def source_evidence(parent, candidate, local_name, transition):
    name = re.escape(local_name.encode())
    source_declaration = rb"(?m)^\s*(?:theorem|lemma) " + name + rb"(?:[ {(]|$)"
    for side, body in (("parent", parent), ("candidate", candidate)):
        if hashlib.sha256(body).hexdigest() != transition[side] or not re.search(source_declaration, body):
            raise ValueError(f"{side} source does not match the declared theorem and structural transition")
    if parent == candidate:
        raise ValueError("the chosen theorem module has identical source")


def run(work, trusted, report, summary, directory):
    candidate = Path.cwd()
    candidate_lib = candidate / ".lake/build/lib/lean"
    cone = (work / "compare.txt").read_text().splitlines()
    shared = [Path(x).resolve() for x in os.environ["LEAN_PATH"].split(os.pathsep) if x]
    if candidate_lib not in shared:
        raise ValueError("run inside the candidate's Lake environment")
    shared = [p for p in shared if p != candidate_lib]
    rels = [Path(*m.split(".")) for m in cone]
    for lib in shared:
        if any((lib / rel).with_suffix(".olean").is_file() for rel in rels):
            raise ValueError("a second project build appears on the dependency search path")
    changed = set(report["changed"]) & set(report["roots"])
    panel = json.loads(Path(__file__).with_name("panel.json").read_bytes())
    chosen = panel["theorems"]
    if len(chosen) != 2 or len({r["module"] for r in chosen} & changed) != 2:
        raise ValueError("both predeclared theorems must belong to edited panel roots")

    def git_file(name):
        return subprocess.check_output(["git", "-C", trusted, "show", f"HEAD:{name}"], text=True)

    parent_commit = subprocess.check_output(["git", "-C", trusted, "rev-parse", "HEAD"], text=True).strip()
    if parent_commit != report["parent"]:
        raise ValueError("the parent checkout does not match the verified manifest source")
    pr_path = work / "pr-source.json"
    if pr_path.exists():
        pr = json.loads(pr_path.read_bytes())
        if (pr["ci_head"], pr["source_tree"], pr["comparison_parent"]) != (
            report["candidate_head"],
            report["candidate_source_tree"],
            report["parent"],
        ):
            raise ValueError("the published PR and cone have different source identities")
        summary["pull_request"] = pr["pull_request"]
        summary["pr_head"] = pr["pr_head"]
        summary["checked_commit"] = pr["checked_commit"]
        summary["source_mode"] = pr["source_mode"]
    policy = json.loads(git_file("comparator.json"))
    if set(policy["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("the upstream axiom policy has changed")
    if set(policy["external_kernels"]) != set(KERNELS[1:]):
        raise ValueError("the upstream external kernel configuration has changed")
    support = [n for n in git_file("export-targets.txt").split() if n not in policy["theorem_names"]]
    summary["permitted_axioms"] = policy["permitted_axioms"]
    with tempfile.TemporaryDirectory(dir=work) as temp:
        scratch = Path(temp)
        parent_lib = scratch / "parent"
        # The flat reference copies predate all fresh builds. Give only those
        # modules to the parent exporter and only integrated outputs to the candidate.
        for m, rel in zip(cone, rels):
            for ext in (".olean", ".olean.server", ".olean.private"):
                dest = (parent_lib / rel).with_suffix(ext)
                dest.parent.mkdir(parents=True, exist_ok=True)
                os.link(work / "parent" / (m + ext), dest)
        for target in chosen:
            m, name, local = target["module"], target["name"], target["local"]
            rel = Path("src", *m.split(".")).with_suffix(".lean")
            before, after = (trusted / rel).read_bytes(), (candidate / rel).read_bytes()
            source_evidence(before, after, local, panel["changed_sources"][m])
            result = dict(
                module=m,
                theorem=name,
                status="running",
                clump_members=panel["changed_sources"][m]["members"],
                parent_source_sha256=hashlib.sha256(before).hexdigest(),
                candidate_source_sha256=hashlib.sha256(after).hexdigest(),
                exports={},
            )
            imports = re.findall(rb"(?m)^(?:public )?import (?:all )?([\w.]+)$", after)
            result["changed_direct_project_imports"] = sorted(
                {m.decode() for m in imports} & set(report["changed"])
            )
            summary["theorems"].append(result)
            stem = m.rsplit(".", 1)[1]
            with tempfile.TemporaryDirectory(dir=scratch) as out:
                out = Path(out)
                for side, lib in (("parent", parent_lib), ("candidate", candidate_lib)):
                    env = os.environ | {"LEAN_PATH": os.pathsep.join(str(x) for x in [lib, *shared])}
                    export = out / (side + ".jsonl")
                    log = directory / (stem + "-" + side + ".stderr")
                    start = time.monotonic()
                    code = limited_process(
                        ["leanexport", m, "--", *support, name], out, env, export, log, 180, is_export=True
                    )
                    elapsed = time.monotonic() - start
                    if code:
                        raise ValueError(
                            f"{m} {side} export stopped with status {code} ({export.stat().st_size} bytes)"
                        )
                    result["exports"][side] = inspect_export(export, name)
                    result["exports"][side]["elapsed_seconds"] = round(elapsed, 3)
                if (result["exports"]["parent"]["sha256"] != target["sha256"]
                    or result["exports"]["candidate"]["sha256"] != target["sha256"]):
                    raise ValueError(f"the two genuine theorem proof exports differ from the authenticated {name} preflight")
                config = policy | dict(challenge_module=m, solution_module=m, theorem_names=[name])
                cfg, native = directory / (stem + "-config.json"), directory / (stem + "-report.json")
                write_json(cfg, config)
                start = time.monotonic()
                code = limited_process(
                    [
                        "lake",
                        "comparator",
                        "--config",
                        cfg,
                        "--challenge-from-export",
                        out / "parent.jsonl",
                        "--solution-from-export",
                        out / "candidate.jsonl",
                        "--inadvisably-no-sandbox",
                        "--json",
                    ],
                    out,
                    os.environ,
                    native,
                    directory / (stem + "-judge.stderr"),
                    300,
                )
                result["comparator_seconds"] = round(time.monotonic() - start, 3)
                result["returncode"] = code
                verdict = json.loads(native.read_bytes())
                checks = verdict["report"]
                result.update(
                    judgement=verdict["judgement"],
                    sandboxed=verdict["sandboxed"],
                    compare_statements=checks["compare_statements"]["judgement"],
                    check_axioms=checks["check_axioms"]["judgement"],
                    kernels={
                        k: checks.get("kernel_reports", {}).get(k, {}).get("judgement", "skipped")
                        for k in KERNELS
                    },
                )
                if (
                    code
                    or result["judgement"] != "accepted"
                    or any(
                        v != "success"
                        for v in (
                            result["compare_statements"],
                            result["check_axioms"],
                            *result["kernels"].values(),
                        )
                    )
                ):
                    result["status"] = "rejected"
                    raise ValueError(f"Comparator rejected {name}")
                result["status"] = "accepted"
                write_json(directory / "summary.json", summary)


def main():
    work, trusted = (Path(s).resolve() for s in sys.argv[1:])
    report = json.loads((work / "report.json").read_bytes())
    directory = work / "scoped-comparator"
    directory.mkdir(exist_ok=True)
    summary = dict(
        status="running",
        parent=report["parent"],
        donor=report["donor"],
        manifest=report["manifest"],
        candidate_head=report.get("candidate_head"),
        candidate_source_tree=report.get("candidate_source_tree"),
        export_byte_limit=EXPORT_LIMIT,
        theorems=[],
    )
    write_json(directory / "summary.json", summary)
    try:
        run(work, trusted, report, summary, directory)
        summary["status"] = "accepted"
    except Exception as error:
        for result in summary["theorems"]:
            if result["status"] == "running":
                result["status"] = "incomplete"
        summary["status"] = (
            "rejected" if any(r["status"] == "rejected" for r in summary["theorems"]) else "incomplete"
        )
        summary["reason"] = str(error)
        raise
    finally:
        write_json(directory / "summary.json", summary)
        print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
