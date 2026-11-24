"""Check clump blame with actual errors from the pinned Lean compiler."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


REVISIONS = {
    "initial": ("2b481024a8665bd5b24ca40d28fe90cb4fb86ce0", "d346751f04fc9b6773cc53cd50bd2dea115db88a9df4dc3b8466499403ea9128"),
    "previous": ("989ea9c41e8400a6fe894fe365298c219f8c7e1d", "a4f1990726580a924d4cf95ecd7a76bcb00099a1e28756c06e9c91c47b5abcdf"),
    "candidate": ("e7127ce8136d8ed36e610884d8578de1cffadd19", "532a111c35fb0a3fc26cecc28e97dd7d9b19d0d2d63a3a36b59e20d20bad3dcf"),
}
BANNER = "-- This file was produced by scripts/clump.py from the modules listed below."
LITERAL = "-- clump member: note\n"
PREFACE = LITERAL + "-- ===== clump member: other =====\nexample : False := True.intro\n"


def output(cmd, cwd):
    return subprocess.check_output(cmd, cwd=cwd, stderr=subprocess.PIPE, timeout=90)


def main(repo, logs):
    logs.mkdir(parents=True, exist_ok=True)
    head = REVISIONS["candidate"][0]
    def blob(rev, path):
        return output(["git", "show", rev + ":" + path], repo)
    roles = {}
    results = {}
    with tempfile.TemporaryDirectory() as temp:
        scratch = Path(temp)
        for label, (rev, digest) in REVISIONS.items():
            script = scratch / (label + ".py")
            data = blob(rev, "scripts/clump.py")
            assert hashlib.sha256(data).hexdigest() == digest
            script.write_bytes(data)
            roles[label] = script
        (scratch / "clump-exclude.txt").write_bytes(blob(head, "scripts/clump-exclude.txt"))
        for case in ("ordinary", "above-banner", "compact-member", "legacy-literal"):
            root = scratch / case
            src = root / "src/Examples"
            src.mkdir(parents=True)
            def clump(label, command, *args):
                return output([sys.executable, "-B", roles[label], command, root, *args], root).decode()
            (root / "lean-toolchain").write_bytes(blob(head, "lean-toolchain"))
            (root / "lakefile.toml").write_text('name = "Diagnostic"\nsrcDir = "src"\n[[lean_lib]]\nname = "Examples"\n')
            hdr = "module\npublic import Init\n\n@[expose] public section\n"
            main_file = src / "Main.lean"
            if case == "ordinary":
                members = {"Main": hdr + PREFACE}
            else:
                leaf = ("True" if case == "above-banner" else "False")
                marker = LITERAL if case == "legacy-literal" else ""
                members = {"Leaf": hdr + marker + f"theorem leaf : {leaf} := True.intro\n",
                           "Main": hdr.replace("import Init", "import Examples.Leaf") + "theorem root : True := True.intro\n"}
            for n, text in members.items():
                (src / (n + ".lean")).write_text(text)
            output(["git", "init", "--quiet"], root)
            output(["git", "add", "src"], root)
            if case != "ordinary":
                plan = root / "plan.json"
                clump("candidate", "plan", "--out", plan)
                assert json.loads(plan.read_bytes()) == {"Examples.Main": ["Examples.Leaf", "Examples.Main"]}
                clump("candidate", "apply", plan)
                archive = main_file.read_text()
                assert archive.count(BANNER) == 1
                if case == "above-banner":
                    main_file.write_text(archive.replace(BANNER, PREFACE + BANNER))
            version = output(["lake", "--version"], root).decode().strip()
            assert "Lean version 4.37.0-rc1" in version
            result = subprocess.run(["lake", "--no-cache", "build", "+Examples.Main"], cwd=root, capture_output=True, timeout=90)
            build = result.stdout + result.stderr
            log = logs / (case + "-stock-lake.log")
            log.write_bytes(build)
            diagnostics = re.findall(rb"(?m)^error: src/Examples/Main\.lean:(\d+):\d+: Type mismatch", build)
            assert result.returncode == 1 and len(diagnostics) == 1 and b"True.intro" in build, build[-1800:]
            actual_source = main_file.read_text()
            source_line = actual_source.splitlines()[int(diagnostics[0])-1]
            assert ": False := True.intro" in source_line
            owners = {k: clump(k, "blame", log).strip().splitlines() for k in roles}
            if case in ("ordinary", "above-banner"):
                assert owners["previous"] == ["note"] and owners["candidate"] == [], owners
            elif case == "legacy-literal":
                assert owners == {"initial":["note"],"previous":["Examples.Leaf"],"candidate":["Examples.Leaf"]}, owners
            else:
                assert owners == {k:["Examples.Leaf"] for k in roles}, owners
            clump("candidate", "unclump")
            recovered = {p.stem:p.read_text() for p in src.glob("*.lean")}
            assert recovered == members
            results[case] = dict(owners=owners, compiler=version, stock_exit=result.returncode,
                                 line=int(diagnostics[0]), source_line=source_line, build_log_sha256=hashlib.sha256(build).hexdigest(),
                                 input_sources=members, source_compiled=actual_source, exact_unclump=True)
    (logs / "diagnostic-control.json").write_text(json.dumps(dict(source=head, scripts=REVISIONS, cases=results), indent=2) + "\n")
    for case, row in results.items():
        print(case, "previous", row["owners"]["previous"], "candidate", row["owners"]["candidate"], flush=True)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve())
