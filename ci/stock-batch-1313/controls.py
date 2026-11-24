"""Exercise native acceptance and rejection with three small proof changes."""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

KERNELS = ("Lean default", "Lean paranoid", "nanoda")
CASES = {
    "parent": "theorem original (n : Nat) : n + 0 = n := Nat.add_zero n",
    "alternative-proof": "theorem original (n : Nat) : n + 0 = n := by rfl",
    "other-statement": "theorem original (n : Nat) : n * 1 = n := Nat.mul_one n",
    "extra-axiom": "axiom extra (n : Nat) : n + 0 = n\n"
                  "theorem original (n : Nat) : n + 0 = n := extra n",
}


def main():
    work, trusted = map(lambda p: Path(p).resolve(), sys.argv[1:])
    result_dir = work / "control-reports"
    result_dir.mkdir(exist_ok=True, parents=True)
    config = json.loads((trusted / "comparator.json").read_bytes())
    support = [name for name in (trusted / "export-targets.txt").read_text().split()
               if name not in config["theorem_names"]]
    name = "ComparisonControl.original"
    config.update(challenge_module="Control", solution_module="Control", theorem_names=[name])
    cfg = result_dir / "config.json"
    cfg.write_text(json.dumps(config, indent=2) + "\n")
    expected = {
        "alternative-proof": ("accepted", "success", "success", "success"),
        "other-statement": ("failure", "failure", "skipped", "skipped"),
        "extra-axiom": ("failure", "success", "failure", "skipped"),
    }
    with tempfile.TemporaryDirectory(dir=work) as tmp:
        temp = Path(tmp)
        for label, body in CASES.items():
            module = temp / label
            module.mkdir()
            (module / "Control.lean").write_text(
                "module\n@[expose] public section\nnamespace ComparisonControl\n" + body + "\nend ComparisonControl\n")
            env = os.environ | {"LEAN_PATH": str(module)}
            subprocess.run(["lean", "-o", "Control.olean", "Control.lean"], cwd=module, env=env, check=True)
            with (module / "proof.jsonl").open("wb") as output:
                subprocess.run(["leanexport", "Control", "--", *support, name], cwd=module, env=env,
                               stdout=output, check=True)
        for label, (verdict, statements, axioms, kernels) in expected.items():
            cmd = ["lake", "comparator", "--config", cfg, "--challenge-from-export", temp / "parent/proof.jsonl",
                   "--solution-from-export", temp / label / "proof.jsonl", "--inadvisably-no-sandbox", "--json"]
            process = subprocess.run(cmd, cwd=temp, capture_output=True, timeout=120)
            (result_dir / (label + ".json")).write_bytes(process.stdout)
            (result_dir / (label + ".stderr")).write_bytes(process.stderr)
            response = json.loads(process.stdout)
            report = response["report"]
            checks = {k: report["kernel_reports"][k]["judgement"] for k in KERNELS}
            if ((process.returncode == 0) != (verdict == "accepted") or response["judgement"] != verdict
                    or report["compare_statements"]["judgement"] != statements
                    or report["check_axioms"]["judgement"] != axioms or set(checks.values()) != {kernels}):
                raise ValueError(f"the native Comparator gave an unexpected result for {label}")
            print(label, verdict, "statement", statements, "axioms", axioms, "kernels", checks, flush=True)
            if label == "extra-axiom" and "ComparisonControl.extra" not in str(report["check_axioms"]["output"]):
                raise ValueError("the extra axiom was not identified by name")


if __name__ == "__main__":
    main()
