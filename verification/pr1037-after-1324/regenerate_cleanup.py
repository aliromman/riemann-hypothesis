"""Regenerate the matrix cleanup from a Git tree and verify every output against a published revision."""
import argparse
from collections import Counter
from pathlib import Path
import re
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--repo", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--base", required=True)
parser.add_argument("--expected", required=True)
args = parser.parse_args()
repo, dest = args.repo.resolve(), args.output.resolve()

def git(*command):
    return subprocess.check_output(["git", "-C", repo, *command])

def commit(revision):
    return git("rev-parse", "--verify", "--end-of-options", revision + "^{commit}").decode().strip()

base, expected = commit(args.base), commit(args.expected)
names = ("instMeasMat", "matrixMeasurableSpace", "measurableSpace_matrix", "borelSpace_matrix")
qualified = {"Formalism.DoubleCosetMeasures.instMeasMat", "GlobalTheory.SplitWeil.matrixMeasurableSpace",
             "GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix", "GroundTheory.Automorphic.GJMatrix.borelSpace_matrix"}
identifier = re.compile(r"\b(?:" + "|".join(names) + r")\b")
records = git("grep", "-z", "-l", "-w", "-E", "(" + "|".join(names) + ")", base, "--", "src/*.lean")
prefix = base.encode() + b":"
paths = [row for row in records.split(b"\0") if row]
if any(not row.startswith(prefix) for row in paths):
    raise ValueError("Unexpected Git path")
source_files = sorted(row[len(prefix):].decode() for row in paths)
changed = git("diff", "--name-only", "-z", base, expected).split(b"\0")
if source_files != sorted(path.decode() for path in changed if path):
    raise ValueError("The expected revision has a different set of changed files")
counts = Counter()
generated = {}
comment_starts = ("-- The statements used here (`CoefData`", "-- The clump also imports `GJMatrixCoord`",
                  "-- See the note in `linRedC_k`", "-- Mathlib's `Matrix.instMeasurableSpace`",
                  "-- The `KFinAvg` statements", "-- Two defeq-but-not-reducibly-equal matrix")
provider = {"StatementZ": ("instMeasMat",), "MatrixMeasurableSpace": ("matrixMeasurableSpace",),
            "GJMatrixCoord": ("measurableSpace_matrix", "borelSpace_matrix")}
for f in source_files:
    original = git("show", base + ":" + f).decode()
    lines = original.splitlines(keepends=True)
    out = []
    i = 0
    stem = Path(f).stem
    while i < len(lines):
        line = lines[i]
        s = line.strip()
        if s.startswith(comment_starts):
            while i < len(lines) and lines[i].startswith("--"):
                i += 1
            assert "attribute [" in lines[i] and identifier.search(lines[i]), (f, lines[i])
            continue
        if stem in provider and any(re.match(r"^(?:@\[reducible\] )?(?:scoped )?instance " + name + r"\b", line) for name in provider[stem]):
            i += 1
            while i < len(lines) and lines[i].startswith(" "):
                i += 1
            if i < len(lines) and not lines[i].strip():
                i += 1
            counts["declarations"] += 1
            continue
        if s.startswith("attribute [") and identifier.search(s):
            prefix, tail = line.rstrip("\n").split("] ", 1)
            args = tail.split()
            trailing_in = args[-1] == "in"
            if trailing_in:
                args.pop()
            keep = [name for name in args if name not in qualified]
            assert len(keep) < len(args), (f, line)
            if keep:
                out.append(prefix + "] " + " ".join(keep) + (" in" if trailing_in else "") + "\n")
                counts["mixed attributes"] += 1
            else:
                if out and not out[-1].strip() and i + 1 < len(lines) and not lines[i + 1].strip():
                    i += 1
                counts["removed attributes"] += 1
            i += 1
            continue
        if s.startswith("letI : MeasurableSpace (Matrix ") and s.split(" := ")[-1] in qualified:
            i += 1
            if stem == "ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement":
                assert lines[i].strip() == "haveI : BorelSpace (Matrix (Fin n) (Fin r) k) := inferInstanceAs (BorelSpace (Fin n → Fin r → k))"
                i += 1
                counts["redundant local Borel witness"] += 1
            counts["local measurable witnesses"] += 1
            continue
        if stem in ("GJFEInducedLevi", "GJFELevi") and s.startswith("have hM : ") and identifier.search(s):
            dimension = "n" if stem == "GJFEInducedLevi" else "m"
            assert "BorelSpace.measurable_eq" in lines[i + 1]
            assert lines[i + 2].strip() == "show MeasurableSpace.comap Units.val _ = _"
            old_start = "  rw [hM, ← borel_comap, "
            assert lines[i + 3].startswith(old_start)
            out.append(lines[i + 2])
            out.append(f"  rw [BorelSpace.measurable_eq (α := Matrix (Fin {dimension}) (Fin {dimension}) F), ← borel_comap,\n")
            out.append("    " + lines[i + 3].removeprefix(old_start))
            i += 4
            counts["GL proofs"] += 1
            continue
        if stem == "LocalZetaFunctionalUniqueness" and "MeasurableSpace.comap Units.val GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix" in line:
            line = line.replace("GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix", "inferInstance")
            counts["explicit comap argument"] += 1
        assert not identifier.search(line), (f, line)
        out.append(line)
        i += 1
    if stem in provider:
        canonical = "public import Mathlib.Analysis.Matrix.MeasurableSpace\n"
        # Use the canonical import at the position of its first alphabetical successor.
        if stem == "GJMatrixCoord":
            out.remove("public import Mathlib.Topology.Instances.Matrix\n")
        if canonical not in out:
            pos = next(j for j, line in enumerate(out) if line.startswith("public import Mathlib.") and line > canonical)
            out.insert(pos, canonical)
    result = "".join(out)
    assert result != original and not identifier.search(result)
    if result.encode() != git("show", expected + ":" + f):
        raise ValueError("Regenerated source differs from the expected Git blob: " + f)
    generated[f] = result.encode()
assert counts["declarations"] == 4 and counts["GL proofs"] == 2
if dest.exists() and any(dest.iterdir()):
    if any(not (dest / name).is_file() or (dest / name).read_bytes() != data for name, data in generated.items()):
        raise ValueError("The output directory contains different files")
else:
    dest.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=dest.parent) as temporary:
        output = Path(temporary, "output")
        for name, data in generated.items():
            file = output / name
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_bytes(data)
        output.rename(dest)
print(len(source_files), "files", dict(counts))
