"""Check three namespace selections and two rewrite terms from the original Lean sources."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--ilean-dir", type=Path, required=True)
    args = ap.parse_args()
    original = "c7791603122c0328f79e49f6be5d7d4402effc53"
    cases = {
        "Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable":
            ("GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.logNorm_ofWeight_one", [(36, 25), (223, 6), (223, 28)]),
        "GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral":
            ("ReciprocityTheory.ChartRestriction.G.Geo.fibre", [(21, 29)]),
        "GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralProjIndep":
            ("ReciprocityTheory.ChartRestriction.G.Geo.fibre", [(20, 2)]),
    }
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        def git(*argv):
            return subprocess.check_output(["git", "-C", root, "-c", "user.name=Selector check",
                                            "-c", "user.email=test@example.invalid", *argv])
        git("init", "-q")
        edits = {}
        for module, (constant, spans) in cases.items():
            rel = Path("src", *module.split(".")).with_suffix(".lean")
            data = subprocess.check_output(["git", "-C", args.repo, "show", f"{original}:{rel}"])
            target = root / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            lines = data.decode().splitlines(keepends=True)
            bare = constant.rsplit(".", 1)[-1]
            for number, col in sorted(spans, reverse=True):
                line = lines[number - 1]
                assert line[col:col + len(bare)] == bare
                lines[number - 1] = line[:col] + "_root_." + constant + line[col + len(bare):]
            edits[target] = "".join(lines)
        git("add", "src")
        git("commit", "-qm", "Original sources")
        for path, edited in edits.items():
            path.write_text(edited)
        git("commit", "-qam", "Qualify the namespace entries and rewrite terms")
        checker = Path(__file__).with_name("check_qualifications.py")
        for options, expected in [([], ["matches"] * 5), (["--check-syntax"], ["manual: namespace syntax, open"] * 3 + ["matches"] * 2)]:
            cmd = [sys.executable, checker, "--repo", root, "--ilean-dir", args.ilean_dir.resolve(),
                   "--original", "HEAD^", *options, "HEAD^", "HEAD"]
            run = subprocess.run(cmd, capture_output=True, text=True)
            rows = [json.loads(s) for s in run.stdout.splitlines()]
            if sorted(r["status"] for r in rows) != sorted(expected) or run.returncode != bool(options):
                raise RuntimeError(run.stdout + run.stderr)
            print(json.dumps({"options": options, "sites": rows}, ensure_ascii=False))


if __name__ == "__main__":
    main()
