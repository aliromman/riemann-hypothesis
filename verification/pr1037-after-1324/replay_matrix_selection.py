"""Replay matrix instance selection and a widened project proof in two built checkouts."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

FOUNDATION = "Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace"
DOUBLE = "Formalism.DoubleCosetMeasures.StatementZ"
COORD = "GroundTheory.AutomorphicForms.GL2.GJMatrixCoord"
MATHLIB = "Mathlib.Analysis.Matrix.MeasurableSpace"
PROOF = "Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero"
IMPORT = re.compile(r"^(?:public )?(?:meta )?import ")
OPTIONS = ["--json", "--tstack=400000", "-DautoImplicit=false",
           "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("before", "after", "bin", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--open-double-coset-scope", action="store_true",
                        help="Test the GL scope introduced by community PR #1324.")
    parser.add_argument("--require-canonical-borel", action="store_true",
                        help="Require the same selected Borel witness as a Mathlib-only import.")
    parser.add_argument("--expect-project-borel-on-parent", action="store_true",
                        help="Check the project Borel witness on an already buildable parent.")
    args = parser.parse_args()
    baseline, candidate, binary, out = (p.resolve() for p in (args.before, args.after, args.bin, args.output))
    out.mkdir(parents=True, exist_ok=True)
    path = Path("src", *PROOF.split(".")).with_suffix(".lean")
    original = (baseline / path).read_bytes()
    if original != (candidate / path).read_bytes():
        raise ValueError("The control and candidate proof bodies differ.")
    scope = "open scoped Formalism.DoubleCosetMeasures\n" if args.open_double_coset_scope else ""
    cases = {}
    for tag, owners, activate in (("mathlib-only", [], False), ("foundation", [FOUNDATION], False), ("coordinates", [COORD], False),
                                  ("double", [DOUBLE], True), ("combined", [FOUNDATION, COORD, DOUBLE], True)):
        imports = "".join("public import " + n + "\n" for n in [MATHLIB, *owners])
        cases[tag] = ("MatrixSelection", "module\n" + imports + "\n@[expose] public section\n" +
                      (scope if activate else "") +
                      "variable {m n X : Type} [MeasurableSpace X]\n" +
                      "example : (inferInstance : MeasurableSpace (Matrix m n X)) = " +
                      "Matrix.instMeasurableSpace := by with_reducible rfl\n" +
                      "#synth BorelSpace (Matrix (Fin 2) (Fin 3) ℝ)\n")
    for tag, owners in (("proof-forward", [DOUBLE, COORD]), ("proof-reverse", [COORD, DOUBLE])):
        lines = original.decode().splitlines(keepends=True)
        i = max(i for i, line in enumerate(lines) if IMPORT.match(line)) + 1
        lines[i:i] = ["public import " + n + "\n" for n in owners]
        if scope:
            marker = lines.index("@[expose] public section\n") + 1
            lines.insert(marker, scope)
        cases[tag] = (PROOF, "".join(lines))

    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2")
    version = subprocess.check_output([binary / "lean", "--version"], env=env, text=True).strip()
    def run(job):
        side, project, tag, (module, source) = job
        root = out / side / tag
        f = root.joinpath(*module.split(".")).with_suffix(".lean")
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(source)
        result = subprocess.run([binary / "lake", "--no-cache", "env", binary / "lean", *OPTIONS,
                                 "--root", root, "-o", f.with_suffix(".olean"), f],
                                cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (root / "compile.jsonl").write_bytes(result.stdout)
        messages = []
        for line in result.stdout.splitlines():
            try:
                row = json.loads(line)
            except ValueError:
                continue
            if isinstance(row, dict) and row.get("severity") in ("error", "information"):
                messages.append({"severity": row["severity"], "line": row["pos"]["line"], "message": row["data"]})
        errors = [r for r in messages if r["severity"] == "error"]
        if result.returncode and not errors:
            raise RuntimeError(f"{side}/{tag}: {result.stdout.decode(errors='replace')[-800:]}")
        borel = [x["message"].strip() for x in messages if x["severity"] == "information"] if not tag.startswith("proof-") else []
        print(side, tag, "exit", result.returncode, "errors", len(errors), "Borel", borel, flush=True)
        return (side + "/" + tag, dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                                       exit=result.returncode, errors=errors, borel=borel))

    jobs = [(side, project, tag, case) for side, project in (("before", baseline), ("after", candidate))
            for tag, case in cases.items()]
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = dict(pool.map(run, jobs))
    report = dict(lean=version, proof=PROOF, proof_sha256=hashlib.sha256(original).hexdigest(),
                  opened_double_coset_scope=args.open_double_coset_scope, cases=results)
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    for tag in cases:
        after = results["after/" + tag]
        if results["before/" + tag]["source_sha256"] != after["source_sha256"]:
            raise ValueError("The probe changed between runs: " + tag)
        if after["exit"] or (not tag.startswith("proof-") and (not after["borel"] or
                args.require_canonical_borel and after["borel"] != results["after/mathlib-only"]["borel"])):
            raise ValueError("The candidate did not select the Mathlib instances: " + tag)
    if args.expect_project_borel_on_parent:
        if any(results["before/" + tag]["exit"] for tag in cases):
            raise ValueError("A proof failed on the buildable parent.")
        for tag in ("coordinates", "combined"):
            if results["before/" + tag]["borel"] != ["GroundTheory.Automorphic.GJMatrix.borelSpace_matrix"]:
                raise ValueError("The parent did not select the project Borel witness: " + tag)
            if results["after/" + tag]["borel"] != results["after/mathlib-only"]["borel"]:
                raise ValueError("The candidate did not select the canonical Borel witness: " + tag)
    elif not any(results["before/" + tag]["errors"] for tag in cases):
        raise ValueError("The control did not reproduce an error.")


if __name__ == "__main__":
    main()
