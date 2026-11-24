"""Check Roy7's pinned PR #911 receipts and print the remaining modules for run_dependents.py."""
import argparse
import json
from pathlib import Path
import subprocess


REVISION = "84d61140ee7235dce6fa95681fa0e1b03ab2c363"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("gist", type=Path, help="Git clone of Roy7's db4def455fe93b5b7d58c87e86635b26 gist")
    cli.add_argument("plan", type=Path, help="c988/dependents.json")
    args = cli.parse_args()

    def read(name):
        return subprocess.check_output(["git", "-C", args.gist, "show", f"{REVISION}:{name}"], text=True)

    def rows(name):
        return [json.loads(line) for line in read(name).splitlines()]

    plan = json.loads(args.plan.read_bytes())
    result = json.loads(read("result.json"))
    selected = read("sel.txt").splitlines()
    public = rows("public.jsonl")
    require((plan["base"], plan["candidate"]) == (result["stock"], result["candidate"]), "Wrong revisions")
    require(result["targets"] == selected == [row["module"] for row in public], "Different module lists")
    full, built = set(plan["modules"]), set(selected)
    require(len(plan["modules"]) == len(full) == result["fullModules"] == 1587, "Invalid dependency set")
    require(built <= full and len(built) == len(selected) == result["modules"] == 1000, "Invalid build selection")
    require(all(sum(row[key] for row in public) == value for key, value in result["totals"].items()), "Invalid totals")

    expected = {}
    metadata = {}
    for row in public:
        module = row["module"]
        for term in row["terms"]:
            expected[module, term["declaration"], term["field"]] = term["conversion"]
        for message in row["structural"]:
            prefix = "kind, universe parameters, binders or declaration metadata changed: "
            require(message.startswith(prefix), message)
            metadata[module, message[len(prefix):]] = {}
    require(len(expected) == 872 and len(metadata) == 12, "Different field or metadata count")
    require(sorted({module for module, _ in metadata}) == result["failedModules"], "Different failed modules")

    expanded = set()
    for side in ("old", "new"):
        checked = {(row["module"], t["declaration"], t["field"]): t["conversion"]
                   for row in rows(f"{side}-conversion.jsonl") for t in row["terms"]}
        require(checked.keys() == expected.keys(), f"Incomplete {side} conversions")
        expanded.update(k for k, conversion in checked.items() if conversion != "defeq")
    require(len(expanded) == result["expandedProofFields"] == 3, "Different proof-helper coverage")
    for side in ("stock", "candidate"):
        helpers = rows(f"{side}-proof-helpers.jsonl")
        require({(r["module"], r["declaration"], r["field"]) for r in helpers} == expanded, "Incomplete helper set")
        require(all(r["environment"] == side and r["originalToExpanded"] == r["expandedConversion"] == "defeq"
                    for r in helpers), f"Failed proof-helper comparison in {side}")

    for line in read("diag-structural.txt").splitlines():
        if line.startswith("## "):
            module = line[3:]
        elif line.startswith(("stock ", "candidate ")):
            side, entry = line.split(" ", 1)
            name, fields = entry.split(": ", 1)
            metadata[module, name][side] = fields
    for key, pair in metadata.items():
        stock = pair["stock"]
        require(stock.startswith("def hints=regular 9 ") and
                stock.replace("def hints=regular 9 ", "def hints=regular 8 ", 1) == pair["candidate"],
                f"Other printed metadata changed for {key}")

    remaining = [module for module in plan["modules"] if module not in built]
    remaining_tips = set(plan["targets"]) - built
    aut_iso = ("Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument."
               "SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.AutIso")
    require(len(remaining) == 587 and remaining_tips == {"Main", aut_iso}, "Different remaining targets")
    print("\n".join(remaining))


if __name__ == "__main__":
    main()
