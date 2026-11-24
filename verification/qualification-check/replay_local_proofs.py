"""Replay the three local-hypothesis controls under the original Lean 4.36 environment."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import tempfile

ORIGINAL = "c7791603122c0328f79e49f6be5d7d4402effc53"
CASES = [
    ("Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentRankOne",
     "Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]",
     "Formalism.FourierDecayAlt.P.JCTx6.gInt, _root_.Formalism.REAL.hs, hZ]", 1),
    ("Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta",
     "rw [hval x.1 x.2 hux,", "rw [_root_.GlobalTheory.SW.hval x.1 x.2 hux,", 2),
    ("Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstOrtho",
     "rw [hval x.1 x.2 A ϑ", "rw [_root_.GlobalTheory.SW.hval x.1 x.2 A ϑ", 2),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path, help="repository containing the original commit")
    args = parser.parse_args()
    version = subprocess.check_output(["lean", "--version"], text=True)
    if "version 4.36.0," not in version:
        raise SystemExit("The controls require Lean 4.36.0. Got " + version.strip())
    results = Counter()
    with tempfile.TemporaryDirectory() as tmp:
        for name, local, global_name, expected in CASES:
            rel = Path(*name.split(".")).with_suffix(".lean")
            original = subprocess.check_output(["git", "-C", args.repo, "show",
                                                f"{ORIGINAL}:src/{rel}"]).decode()
            if original.count(local) != 1:
                raise SystemExit("Expected one edit site in " + name)
            for arm, source, expected_errors in [("local", original, 0),
                                                  ("global", original.replace(local, global_name), expected)]:
                root = Path(tmp) / arm
                f = root / rel
                f.parent.mkdir(exist_ok=True, parents=True)
                f.write_text(source)
                proc = subprocess.run(["lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                                       "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000",
                                       f"--root={root}", f], text=True, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT)
                errors = [s.replace(str(f), str(rel)) for s in proc.stdout.splitlines() if ": error:" in s]
                valid = (proc.returncode == (1 if expected_errors else 0) and len(errors) == expected_errors
                         and all("unsolved goals" in x or "Application type mismatch" in x for x in errors))
                results["pass" if valid else "fail"] += 1
                print(json.dumps(dict(module=name, arm=arm, exit=proc.returncode, errors=errors,
                                      expected=expected_errors, reproduced=valid)), flush=True)
                if not valid:
                    print(proc.stdout)
    return int(results["fail"] != 0)


if __name__ == "__main__":
    raise SystemExit(main())
