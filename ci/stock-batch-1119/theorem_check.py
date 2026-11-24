"""Judge up to two edited panel theorems against their published parent exports."""

import difflib
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

PREFIX = "Development.AbelianVarietyTheory.Definitions.Divisors."
# Each entry gives the module, the exported name, and the theorem name in its namespace.
THEOREMS = (
    (
        "CommAlgFunctorCoboundaryZeroMemCocyclesOne",
        "GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne",
        "commAlgFunctorCoboundaryZero_mem_cocyclesOne",
    ),
    (
        "ExistsAlgHomOfIsBaseChange",
        "GlobalTheory.TopForm.isBaseChange_exteriorPower",
        "isBaseChange_exteriorPower",
    ),
    ("HasQIff", "GlobalTheory.QFam.IsRAct.actBij", "IsRAct.actBij"),
    (
        "LeTwoMulOfForallScale",
        "GlobalTheory.HermFrame.le_two_mul_of_forall_scale",
        "le_two_mul_of_forall_scale",
    ),
)
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


def source_edits(parent, candidate, local_name):
    marker = b"@[expose] public section\n"
    a, sep, old_body = parent.partition(marker)
    b, _, new_body = candidate.partition(marker)
    if (
        not sep
        or old_body != new_body
        or not re.search(rb"(?m)^theorem " + re.escape(local_name.encode()) + rb"[ {(]", old_body)
    ):
        raise ValueError(f"the original source does not supply the same theorem body for {local_name}")
    removed = []
    original, revised = a.splitlines(keepends=True), b.splitlines(keepends=True)
    for tag, i, j, _, _ in difflib.SequenceMatcher(None, original, revised, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        if tag != "delete" or any(
            not re.fullmatch(rb"import Mathlib\.[\w.']+\n", line) for line in original[i:j]
        ):
            raise ValueError(f"unexpected source changes before {local_name}")
        removed.extend(line[7:-1].decode() for line in original[i:j])
    if not removed:
        raise ValueError(f"{local_name} has no private import edits")
    return removed


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
    chosen = [(q["module"],q["name"],q["local"]) for q in panel["theorems"]]
    if len(chosen) != 2 or not {m for m,_,_ in chosen} <= changed:
        raise ValueError("the two original theorem names must belong to actual changed roots")
    if not chosen:
        raise ValueError("no named theorem lies in an edited panel root")

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
        for m, name, local in chosen:
            rel = Path("src", *m.split(".")).with_suffix(".lean")
            before, after = (trusted / rel).read_bytes(), (candidate / rel).read_bytes()
            result = dict(
                module=m,
                theorem=name,
                status="running",
                removed_imports=source_edits(before, after, local),
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
