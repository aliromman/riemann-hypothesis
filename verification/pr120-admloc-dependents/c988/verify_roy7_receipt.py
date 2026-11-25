"""Verify Roy7's two published sets of #911 build and kernel results against the affected modules."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess

REVISION = "84d61140ee7235dce6fa95681fa0e1b03ab2c363"
SECOND = "7c9efe437e47a110ff7039f446135a75a2509f3f"
META = "kind, universe parameters, binders or declaration metadata changed: "


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(repo, revision, name):
    return subprocess.check_output(["git", "-C", repo, "show", revision + ":" + name], text=True)


def unique(items):
    indexed = {}
    for key, value in items:
        require(key not in indexed, f"Duplicate record: {key}")
        indexed[key] = value
    return indexed


def flags(diagnostic, structurals, first):
    expected = {(row["module"], message[len(META):]) for row in structurals for message in row["structural"]}
    seen = {}
    if first:
        module = None
        for line in diagnostic.splitlines():
            if line.startswith("## "):
                module = line[3:]
            if line.startswith(("stock ", "candidate ")):
                side, entry = line.split(" ", 1)
                name, fields = entry.split(": ", 1)
                key = (module, name, side)
                require(key not in seen, f"Duplicate structural diagnostic: {key}")
                seen[key] = fields
    else:
        require(len(expected) == 1, "The second diagnostic identifies one declaration")
        module, name = next(iter(expected))
        side = None
        for line in diagnostic.splitlines():
            if line in ("== rh", "== cand"):
                side = "stock" if line == "== rh" else "candidate"
            elif line.strip():
                require(side and line.startswith(name + ": "), "Unexpected diagnostic line")
                key = (module, name, side)
                require(key not in seen, f"Duplicate structural diagnostic: {key}")
                seen[key] = line.removeprefix(name + ": ")
    require(set(seen) == {(m, n, side) for m, n in expected for side in ("stock", "candidate")},
            "Incomplete structural diagnostics")
    for module, name in expected:
        old = seen[module, name, "stock"]
        require(old.startswith("def hints=regular 9 ") and
                old.replace("def hints=regular 9 ", "def hints=regular 8 ", 1) == seen[module, name, "candidate"],
                f"Additional metadata differs: {module}, {name}")
    return sorted([module, name] for module, name in expected)


def verify(repo, revision, selection_file, plan):
    def artifact(name):
        return read(repo, revision, name)

    def records(name):
        return [json.loads(line) for line in artifact(name).splitlines()]

    selected = artifact(selection_file).splitlines()
    result = json.loads(artifact("result.json"))
    public = records("public.jsonl")
    require(result["stock"] == plan["base"] and result["candidate"] == plan["candidate"], "Wrong revisions")
    require(selected == result["targets"] == [r["module"] for r in public], "Selections or public rows differ")
    require(len(set(selected)) == len(selected) == result["modules"], "Invalid selection")
    require(result["fullModules"] == len(plan["modules"]), "Invalid dependency set")
    totals = {k: sum(r[k] for r in public) for k in result["totals"]}
    require(totals == result["totals"] and totals["public"] == totals["axiomRecords"], "Invalid totals")
    require(all(r["public"] == r["axiomRecords"] for r in public), "Incomplete axiom records")
    structural = [r for r in public if r["structural"]]
    require(sorted(r["module"] for r in structural) == result["failedModules"], "Unexpected flagged modules")
    require(all(s.startswith(META) for r in structural for s in r["structural"]), "Axiom or declaration-set change")
    hints = flags(artifact("diag-structural.txt"), structural, revision == REVISION)
    by_module = {r["module"]: r for r in public}
    fields = unique(((r["module"], t["declaration"], t["field"]), t["conversion"]) for r in public for t in r["terms"])
    require(set(fields.values()) == {"pending"}, "Unexpected source field status")
    expected_modules = {k[0] for k in fields}
    require(len(expected_modules) == result["kernelComparisonModules"], "Wrong number of kernel comparisons")
    fallback = set()
    for side in ("old", "new"):
        checked_rows = records(side + "-conversion.jsonl")
        require(len(checked_rows) == len(expected_modules) and {r["module"] for r in checked_rows} == expected_modules,
                "Incomplete kernel module list")
        for row in checked_rows:
            original = by_module[row["module"]]
            require({key: value for key, value in row.items() if key != "terms"} ==
                    {key: value for key, value in original.items() if key != "terms"}, "Kernel object summaries differ")
        checked = unique(((r["module"], t["declaration"], t["field"]), t["conversion"])
                         for r in checked_rows for t in r["terms"])
        require(checked.keys() == fields.keys(), "Kernel field sets differ")
        fallback.update(key for key, status in checked.items() if status != "defeq")
    require(len(fallback) == result["expandedProofFields"], "Wrong count of expanded fields")
    jobs = {}
    for side in ("stock", "candidate"):
        helpers = records(side + "-proof-helpers.jsonl")
        got = unique(((r["module"], r["declaration"], r["field"]), r) for r in helpers)
        require(got.keys() == fallback, "Incomplete proof-helper coverage")
        require(all(r["environment"] == side and r["originalToExpanded"] == r["expandedConversion"] == "defeq"
                    for r in helpers), "A proof-helper conversion failed")
        end = artifact(side + "-build.log").splitlines()[-1]
        match = re.fullmatch(r"Build completed successfully \((\d+) jobs\)\.", end)
        require(match, "Missing successful Lake build: " + side)
        jobs[side] = int(match.group(1))
    return set(selected), dict(gist_revision=revision, modules=len(selected), build_jobs=jobs, totals=totals,
                               kernel_comparison_modules=len(expected_modules), fields=len(fields),
                               direct_fields=len(fields) - len(fallback), proof_helpers=len(fallback),
                               hint_changes=hints)


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("gist", type=Path, help="Git clone of Roy7's db4def455fe93b5b7d58c87e86635b26 gist")
    args.add_argument("plan", type=Path, help="c988/dependents.json")
    args.add_argument("--remaining-gist", type=Path, help="Git clone of Roy7's bd5c8c21e7bbfa1db274ca07b234ebc7 gist")
    inputs = args.parse_args()
    plan = json.loads(inputs.plan.read_bytes())
    full = set(plan["modules"])
    require(len(full) == len(plan["modules"]) == 1587, "Invalid dependency plan")
    first, a = verify(inputs.gist, REVISION, "sel.txt", plan)
    require(first <= full and (len(first), a["fields"], a["proof_helpers"], len(a["hint_changes"])) ==
            (1000, 872, 3, 12), "Unexpected first-run coverage")
    aut_iso = ("Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument."
               "SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.AutIso")
    require(set(plan["targets"]) - first == {"Main", aut_iso}, "Unexpected remaining terminal targets")
    if inputs.remaining_gist is None:
        print("\n".join(module for module in plan["modules"] if module not in first))
        return
    second, b = verify(inputs.remaining_gist, SECOND, "modules.txt", plan)
    require((len(second), b["fields"], b["proof_helpers"], len(b["hint_changes"])) ==
            (587, 551, 4, 1), "Unexpected second-run coverage")
    require(first.isdisjoint(second) and first | second == full, "Selections do not partition the dependency graph")
    require(set(plan["targets"]) <= full and "Main" in second, "Incomplete terminal targets")
    combined = Counter(a["totals"]) + Counter(b["totals"])
    print(json.dumps(dict(stock=plan["base"], candidate=plan["candidate"], modules=len(full),
                          terminal_targets=len(plan["targets"]), totals=dict(combined), runs=[a, b],
                          checked_fields=a["fields"] + b["fields"], direct_fields=a["direct_fields"] + b["direct_fields"],
                          expanded_fields=a["proof_helpers"] + b["proof_helpers"]), indent=2))


if __name__ == "__main__":
    main()
