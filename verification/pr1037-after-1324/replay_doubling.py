"""Replay the retired doubling proof against the current providers in both import orders."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ARCHIVE = "cb4dc6e23a6187db392c96664295415c55b6b01e"
PREFIX = "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition."
ROOT = PREFIX + "SingleBlockDoublingIntegralValue"
SUPPORT = {PREFIX + n for n in (
    "CardResidueRingCompletionChosenUniformiser", "ExistsAddHaarCompletionIntegralMatricesVolOne",
    "ExistsHaarGLCompletionIntegersVolOne", "ExistsIsNrm", "IsLocalAtCompletionIntegersChosenUniformiser")}
FOUNDATION = "Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace"
DOUBLE = "Formalism.DoubleCosetMeasures.StatementZ"
IMPORT = re.compile(r"^(?:public )?(?:meta )?import (\S+)\s*$", re.M)
PUBLIC = "@[expose] public section"
OPTIONS = ["--json", "--tstack=400000", "-DautoImplicit=false",
           "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "before", "after", "output", "bin"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--full", action="store_true",
                        help="Also compile the five retired imports and the unchanged complete proof body.")
    a = parser.parse_args()
    repo, before, after, out, binary = (p.resolve() for p in (a.repo, a.before, a.after, a.output, a.bin))
    out.mkdir(parents=True, exist_ok=True)

    def path(module):
        return Path(*module.split(".")).with_suffix(".lean")

    def source(module):
        return subprocess.check_output(["git", "-C", repo, "show", f"{ARCHIVE}:src/{path(module)}"]).decode()

    original = source(ROOT)
    row = original[original.index("def rowEq "):original.index("theorem phiQ_rowEq ")]
    local = original[original.index("def rowEqM "):original.index("\nend Tr\n")]
    reduced = (PUBLIC + "\n\nopen MeasureTheory Matrix Formalism.DoubleCosetMeasures\n"
               "noncomputable section\nnamespace GlobalTheory.Mem.SingleQ\n"
               "section Gen\nvariable {F : Type} [Field F]\n" + row +
               "end Gen\nsection Tr\nvariable {F : Type} [Field F] [MeasurableSpace F]\n" + local +
               "\nend Tr\nend GlobalTheory.Mem.SingleQ\n")
    fixture = "HistoricalQLoc"
    restored = {n: source(n) for n in sorted(SUPPORT)} if a.full else {}
    supports = {}
    if a.full:
        owner = "Formalism.LocalToGlobal.Divisibility.QLocTied"
        old = source(owner)
        prefix = old[:old.index("\nend QLoc\n")]
        start = prefix.index("def piP ")
        end = prefix.index("def qP ", start)
        # The live module still supplies piP. All other QLoc declarations in
        # this historical section were removed with the doubling proof.
        supports[fixture] = (prefix[:start] + prefix[end:] + "\nend QLoc\nend Formalism.L2.DIV\n").replace(
            "module\n", "module\npublic import " + owner + "\n", 1)
        for n, text in restored.items():
            supports[n] = text.replace("module\n", "module\npublic import " + fixture + "\n", 1)
        gl_owner = "Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni"
        gl_path = Path("src") / path(gl_owner)
        gl_open = "\ntheorem glR_open "
        has_gl_open = [gl_open in (project / gl_path).read_text() for project in (before, after)]
        if has_gl_open[0] != has_gl_open[1]:
            raise ValueError("The two controls have different historical GL interfaces.")
        if not has_gl_open[0]:
            # Restore the archived forwarding theorem for the retired Haar proof.
            gl = source(gl_owner)
            supports["HistoricalGLOpen"] = (
                "module\npublic import " + gl_owner + "\n\n" + PUBLIC + "\n\n"
                + gl[gl.index("namespace Formalism.DoubleCosetMeasures.P"):gl.index("section Alg")]
                + gl[gl.index("section Top"):gl.index("\ntheorem glR_compact ")]
                + "\nend Top\nend GeneralLinearIntegersOpenCompact\nend Formalism.DoubleCosetMeasures.P\n"
            )
            haar = PREFIX + "ExistsHaarGLCompletionIntegersVolOne"
            supports[haar] = supports[haar].replace("module\n", "module\npublic import HistoricalGLOpen\n", 1)
    order = list(TopologicalSorter({n: sorted(supports.keys() & set(IMPORT.findall(text)))
                                   for n, text in supports.items()}).static_order())
    system = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_NUM_THREADS="2")
    version = subprocess.check_output([binary / "lean", "--version"], env=system, text=True).strip()

    def compile_side(item):
        label, project = item
        root = out / label
        library = root / "historical-support"
        library.mkdir(parents=True, exist_ok=True)
        # Lean selects a library by the first component of the module name.
        # Keep live and retired modules in one search root for this fixture.
        live = project / ".lake/build/lib/lean"
        for n in supports:
            obj = path(n).with_suffix(".olean")
            if (live / obj).exists():
                raise ValueError("A historical module is present in the live build: " + n)
            (library / obj).parent.mkdir(parents=True, exist_ok=True)
        def link_live(src, dest):
            for item in src.iterdir():
                target = dest / item.name
                if target.is_symlink():
                    if target.resolve() != item.resolve():
                        raise ValueError("Test output belongs to a different build: " + str(target))
                elif not target.exists():
                    target.symlink_to(item, target_is_directory=item.is_dir())
                elif item.is_dir() and target.is_dir():
                    link_live(item, target)
        if supports:
            link_live(live, library)
        from_lake = subprocess.check_output([binary / "lake", "--no-cache", "env", "printenv", "LEAN_PATH"],
                                            cwd=project, env=system, text=True).strip()
        env = dict(system, LEAN_PATH=str(library) + os.pathsep + from_lake)

        def compile_one(tag, module, text, build_dir):
            f = build_dir / path(module)
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(text)
            result = subprocess.run([binary / "lean", *OPTIONS, "--root", build_dir, "-o", f.with_suffix(".olean"), f],
                                    cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (root / (tag + ".jsonl")).write_bytes(result.stdout)
            errors = []
            for line in result.stdout.splitlines():
                try:
                    record = json.loads(line)
                except ValueError:
                    continue
                if isinstance(record, dict) and record.get("severity") == "error":
                    errors.append(dict(line=record["pos"]["line"], message=record["data"]))
            if result.returncode and not errors:
                raise RuntimeError(result.stdout.decode(errors="replace")[-900:])
            print(label, tag, "exit", result.returncode, "errors", len(errors), flush=True)
            return dict(exit=result.returncode, errors=errors, source_sha256=hashlib.sha256(text.encode()).hexdigest())

        runs = {}
        for n in order:
            tag = n.rsplit(".", 1)[-1]
            runs[tag] = compile_one(tag, n, supports[n], library)
            if runs[tag]["exit"]:
                break
        support_ok = len(runs) == len(order) and all(not r["exit"] for r in runs.values())
        for tag, modules in (("foundation-first", [FOUNDATION, DOUBLE]), ("double-first", [DOUBLE, FOUNDATION])):
            header = "".join("public import " + n + "\n" for n in modules)
            runs["localZ_map-" + tag] = compile_one("localZ_map-" + tag, "LocalZMap", "module\n" + header + reduced, root / ("localZ-" + tag))
            if a.full and support_ok:
                text = original.replace("module\n", "module\n" + header + "public import " + fixture + "\n", 1)
                assert text.split(PUBLIC, 1)[1] == original.split(PUBLIC, 1)[1]
                runs["whole-" + tag] = compile_one("whole-" + tag, ROOT, text, root / ("whole-" + tag))
        if a.full and support_ok:
            # This is the widening used by the original 4.37 regression test.
            # Preserve the existing import order and add the foundation last.
            lines = original.splitlines(keepends=True)
            end = max(i for i, line in enumerate(lines) if IMPORT.match(line)) + 1
            lines[end:end] = ["public import " + fixture + "\n", "public import " + FOUNDATION + "\n"]
            text = "".join(lines)
            assert text.split(PUBLIC, 1)[1] == original.split(PUBLIC, 1)[1]
            runs["whole-original-widening"] = compile_one("whole-original-widening", ROOT, text, root/"original-widening")
        return label, runs

    with ThreadPoolExecutor(max_workers=2) as pool:
        report = dict(pool.map(compile_side, [("before", before), ("after", after)]))
    (out / "report.json").write_text(json.dumps(dict(archive=ARCHIVE, module=ROOT, lean=version,
        archived_source_sha256=hashlib.sha256(original.encode()).hexdigest(), historical_support=order, results=report), indent=2) + "\n")
    support_tags = {n.rsplit(".", 1)[-1] for n in order}
    required = {*support_tags, "localZ_map-foundation-first", "localZ_map-double-first"}
    if a.full:
        required.update(("whole-foundation-first", "whole-double-first", "whole-original-widening"))
    for side, rows in report.items():
        if set(rows) != required or any(rows[n]["exit"] for n in support_tags):
            raise ValueError("The historical prerequisites did not compile on the " + side + " side.")
    for tag, status in report["after"].items():
        if status["exit"]:
            raise ValueError("Candidate failure at " + tag)
        if status["source_sha256"] != report["before"][tag]["source_sha256"]:
            raise ValueError("Probe input differs between builds: " + tag)


if __name__ == "__main__":
    main()
