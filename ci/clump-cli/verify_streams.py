"""Compare the CLI byte streams and restore the real checkout after each apply."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile


project, tools, results = map(Path, sys.argv[1:])
labels = ("community", "published", "proposed")
golden_plan = "7f008f70f550f162cba7e1b23b8b15309086d8efd3ff8c0c4a2ff9ed4521a175"


def digest(data):
    return sha256(data).hexdigest()


def plan(label, output, combine=False):
    stderr = subprocess.STDOUT if combine else subprocess.PIPE
    return subprocess.run(
        [sys.executable, "-B", tools / (label + ".py"), "plan", project,
         "--out", output, "--exclude", project / "scripts/clump-exclude.txt"],
        cwd=project, stdout=subprocess.PIPE, stderr=stderr, check=True,
    )


with tempfile.TemporaryDirectory() as work:
    saved = Path(work) / "plan.json"
    plan_digests = {}
    separate = {}
    for label in ("published", "proposed"):
        result = plan(label, saved)
        raw = saved.read_bytes()
        assert digest(raw) == golden_plan
        plan_digests[label] = digest(raw)
        separate[label] = (result.stdout, result.stderr)
        (results / (label + "-plan.stdout")).write_bytes(result.stdout)
        (results / (label + "-plan.stderr")).write_bytes(result.stderr)
    assert separate["published"] == separate["proposed"]
    stdout, stderr = separate["proposed"]
    assert stdout and stderr
    combined = plan("proposed", saved, combine=True).stdout
    assert combined == stderr + stdout
    raw = saved.read_bytes()
    assert digest(raw) == golden_plan
    (results / "plan.combined").write_bytes(combined)
    (results / "saved-plan.json").write_bytes(raw)
    groups = json.loads(raw)
    paths = ["src/" + m.replace(".", "/") + ".lean" for group in groups.values() for m in group]
    assert len(groups) == 199 and len(paths) == len(set(paths)) == 656
    pathspec = Path(work) / "paths"
    pathspec.write_bytes(b"\0".join(s.encode() for s in paths) + b"\0")
    apply_results = {}
    for label in labels:
        try:
            result = subprocess.run(
                [sys.executable, "-B", tools / (label + ".py"), "apply", project, saved],
                cwd=project, capture_output=True, check=True,
            )
            apply_results[label] = (result.stdout, result.stderr)
            (results / (label + "-apply.stdout")).write_bytes(result.stdout)
            (results / (label + "-apply.stderr")).write_bytes(result.stderr)
        finally:
            subprocess.run(["git", "restore", "--source=HEAD", "--worktree",
                            "--pathspec-from-file=" + str(pathspec), "--pathspec-file-nul"],
                           cwd=project, check=True)
            subprocess.run(["git", "diff", "--exit-code", "--", "src"], cwd=project, check=True)
    assert len(set(apply_results.values())) == 1

report = {
    "plan_files_sha256": plan_digests,
    "plan_stdout_sha256": digest(stdout),
    "plan_stderr_sha256": digest(stderr),
    "plan_combined_sha256": digest(combined),
    "apply_stdout_stderr_sha256": {k: [digest(s) for s in v] for k, v in apply_results.items()},
    "restored_each_apply": True,
}
(results / "standard-streams.json").write_text(json.dumps(report, indent=2) + "\n")
