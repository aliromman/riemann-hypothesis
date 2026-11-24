"""Bind a bounded check to the public PR and the current community main."""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

UPSTREAM = "https://github.com/leanprover-community/riemann-hypothesis"
PR = 879


def git(repository, *args):
    return subprocess.check_output(["git", "-C", repository, *args], text=True).strip()


def snapshot(temp, base, head, expected_mode=None):
    history = Path(temp) / "community.git"
    subprocess.run(["git", "init", "--quiet", "--bare", history], check=True)
    git(history, "remote", "add", "upstream", UPSTREAM + ".git")
    git(history, "fetch", "--quiet", "--no-tags", "--filter=tree:0", "upstream",
        "refs/heads/main:refs/heads/base", f"refs/pull/{PR}/head:refs/heads/pr")
    if git(history, "rev-parse", "base") != base or git(history, "rev-parse", "pr") != head:
        raise ValueError("the published PR head or community main has changed")
    source_merge = None
    remote_merge = f"refs/pull/{PR}/merge"
    if git(history, "ls-remote", "--refs", "upstream", remote_merge):
        git(history, "fetch", "--quiet", "--no-tags", "--filter=tree:0", "upstream",
            f"{remote_merge}:refs/heads/merge")
        parents = git(history, "show", "-s", "--format=%P", "merge").split()
        if parents == [base, head]:
            source_merge = git(history, "rev-parse", "merge")
    common = git(history, "merge-base", "base", "pr")
    if source_merge and expected_mode != "fast-forward":
        checked, mode = source_merge, "github-test-merge"
    elif common == base and expected_mode != "github-test-merge":
        checked, mode = head, "fast-forward"
    else:
        raise ValueError("the PR has no published merge against this main")
    tree = git(history, "rev-parse", checked + ":src")
    if common == base and source_merge and git(history, "rev-parse", source_merge + ":src") != git(history, "rev-parse", head + ":src"):
        raise ValueError("the test merge differs from the fast-forward source tree")
    return {"pull_request": f"{UPSTREAM}/pull/{PR}", "pr_head": head, "comparison_parent": base,
            "upstream_main": base, "merge_base": common, "source_mode": mode, "checked_commit": checked,
            "source_tree": tree, "observed_github_merge": source_merge}


def main():
    candidate, trusted, work = map(Path, sys.argv[1:])
    request = json.loads(Path(__file__).with_name("merge-request.json").read_bytes())
    head = git(candidate, "rev-parse", "HEAD")
    if git(candidate, "rev-parse", "HEAD^1") != request["checked_commit"]:
        raise ValueError("the workflow commit does not match the checked merge")
    if git(trusted, "rev-parse", "HEAD") != request["comparison_parent"]:
        raise ValueError("the community checkout does not match the comparison parent")
    with tempfile.TemporaryDirectory() as temp:
        current = snapshot(temp, request["comparison_parent"], request["pr_head"], request["source_mode"])
    for key in ("source_mode", "checked_commit", "source_tree", "merge_base"):
        if current[key] != request[key]:
            raise ValueError(f"the published {key} differs from the requested check")
    if git(candidate, "rev-parse", "HEAD:src") != current["source_tree"]:
        raise ValueError("the runner checked out another source tree")
    git(candidate, "diff", "--exit-code", current["checked_commit"], head, "--", "src",
        "lean-toolchain", "lakefile.toml", "lake-manifest.json")
    current["ci_head"] = head
    work.mkdir(exist_ok=True, parents=True)
    result = json.dumps(current, indent=2) + "\n"
    (work / "pr-source.json").write_text(result)
    print(result)


if __name__ == "__main__":
    main()
