"""Check the three provider definitions in the parent and the candidate kernels."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess

OWNERS = {
    "Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace": "GlobalTheory.SplitWeil.matrixMeasurableSpace",
    "Formalism.DoubleCosetMeasures.StatementZ": "Formalism.DoubleCosetMeasures.instMeasMat",
    "GroundTheory.AutomorphicForms.GL2.GJMatrixCoord": "GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("before", "after", "bin", "checker", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    a = parser.parse_args()
    before, after, binary, checker, out = (p.resolve() for p in (a.before, a.after, a.bin, a.checker, a.output))
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2")

    def run(job):
        side, project, module, name = job
        path = Path(".lake/build/lib/lean", *module.split(".")).with_suffix(".olean")
        line = subprocess.check_output([binary / "lake", "--no-cache", "env", binary / "lean", "--run",
                                        checker, side, module, name, before / path, after / path],
                                       env=env, cwd=project, text=True)
        row = json.loads(line)
        if (row["side"], row["declaration"], row["definitionallyEqual"]) != (side, name, True):
            raise ValueError(row)
        return row

    jobs = [(side, project, module, name) for module, name in OWNERS.items()
            for side, project in (("stock", before), ("candidate", after))]
    with ThreadPoolExecutor(max_workers=2) as pool:
        records = list(pool.map(run, jobs))
    out.write_text(json.dumps(records, indent=2) + "\n")
    print(len(records), "kernel conversions passed")


if __name__ == "__main__":
    main()
