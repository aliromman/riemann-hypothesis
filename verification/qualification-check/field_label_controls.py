"""Check two real Lean field assignments against the compiler-reference checker."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--ilean-dir", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    args = parser.parse_args()
    original = "c7791603122c0328f79e49f6be5d7d4402effc53"
    cases = {
        "Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands":
            ("twist := H.twist", "GlobalTheory.LocLanglands.LawsLit.twist"),
        "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral":
            ("twist := L.twist", "GlobalTheory.LocLanglands.Laws.twist"),
    }
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        def git(*argv):
            return subprocess.check_output(["git", "-C", root, "-c", "user.name=Compiler reference test",
                                            "-c", "user.email=test@example.invalid", *argv], text=True)
        git("init", "-q")
        changes = {}
        for member, (site, projection) in cases.items():
            path = Path("src") / Path(*member.split(".")).with_suffix(".lean")
            text = subprocess.check_output(["git", "-C", args.repo, "show", f"{original}:{path}"]).decode()
            if text.count(site) != 1:
                raise ValueError(f"unexpected source at {member}")
            f = root / path
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(text)
            changes[f] = text.replace(site, site.replace("twist :=", f"_root_.{projection} :=", 1))
        git("add", "src")
        git("commit", "-qm", "Original field assignments")
        for f, changed in changes.items():
            f.write_text(changed)
        git("commit", "-qam", "Qualify both field labels with the recorded projections")
        run = subprocess.run([sys.executable, args.checker.resolve(), "--repo", root, "--ilean-dir",
                              args.ilean_dir.resolve(), "--original", "HEAD^", "HEAD^", "HEAD"],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        rows = list(map(json.loads, run.stdout.splitlines()))
        print(json.dumps({"tool_exit": run.returncode, "sites": [
            {"member": r["member"], "original_line": r["original_line"], "recorded": r["original_constants"],
             "verdict": r["status"]} for r in rows]}, indent=2))
        if (len(rows) != 2 or run.returncode != 1
                or any(r["status"] != "manual: name before := can be a field label" for r in rows)):
            raise SystemExit(1)


if __name__ == "__main__":
    main()
