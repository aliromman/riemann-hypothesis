"""Check four definitions with the kernels from the stock and candidate builds."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess


DEFINITIONS = {
    "Formalism.DoubleCosetMeasures.StatementZ": "Formalism.DoubleCosetMeasures.instMeasMat",
    "GroundTheory.AutomorphicForms.GL2.GJMatrixCoord": "GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix",
    "Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace": "GlobalTheory.SplitWeil.matrixMeasurableSpace",
    "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue": "GlobalTheory.Mem.SingleQ.rowEqM",
}


def object_path(search_path, module):
    name = Path(*module.split(".")).with_suffix(".olean")
    for root in search_path.split(os.pathsep):
        path = Path(root) / name
        if path.is_file():
            return path.resolve()
    raise FileNotFoundError(name)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--lean", default="lean", help="Lean executable for both builds")
    cli.add_argument("--stock-path", required=True, help="absolute LEAN_PATH for the stock build")
    cli.add_argument("--candidate-path", required=True, help="absolute LEAN_PATH for the candidate build")
    cli.add_argument("--expected", type=Path, required=True, help="published definition comparison for this toolchain")
    args = cli.parse_args()
    executable = shutil.which(args.lean)
    if executable is None:
        cli.error(f"Cannot find Lean at {args.lean}.")
    lean = Path(executable).absolute()
    env = {**os.environ, "PATH": str(lean.parent) + os.pathsep + os.environ["PATH"]}
    paths = {"stock": args.stock_path, "candidate": args.candidate_path}
    for path in paths.values():
        if any(not Path(root).is_absolute() for root in path.split(os.pathsep)):
            cli.error("Use absolute paths for the compiled modules.")

    checker = Path(__file__).with_name("CompareMatrixDefinitions.lean")
    results = {}
    for module, declaration in DEFINITIONS.items():
        old = object_path(paths["stock"], module)
        new = object_path(paths["candidate"], module)
        for side, search_path in paths.items():
            command = [lean, "--run", checker, side, module, declaration, old, new]
            output = subprocess.check_output(command, env={**env, "LEAN_PATH": search_path}, text=True)
            row = json.loads(output)
            if (row["side"], row["declaration"], row["definitionallyEqual"]) != (side, declaration, True):
                raise ValueError(f"Unexpected kernel result for {side} {declaration}: {row}")
            results[side, declaration] = row

    expected = json.loads(args.expected.read_bytes())
    keys = [(row["side"], row["declaration"]) for row in expected]
    if len(keys) != len(results) or set(keys) != results.keys():
        raise ValueError("The receipt must contain both results for each of the four definitions.")
    ordered = [results[key] for key in keys]
    if ordered != expected:
        raise ValueError(f"The kernel results differ from {args.expected}: {ordered}")
    print(json.dumps(ordered, indent=2))


if __name__ == "__main__":
    main()
