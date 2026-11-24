"""Measure a trial Git merge and the direct Mathlib imports in each source tree."""
import argparse
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("main")
    parser.add_argument("candidate")
    args = parser.parse_args()

    def git(*argv, env=None, allowed=(0,)):
        result = subprocess.run(
            ["git", "-C", args.repo, *argv], capture_output=True, env=env
        )
        if result.returncode not in allowed:
            raise RuntimeError(result.stderr.decode(errors="replace"))
        return result

    def revision(name):
        return git("rev-parse", "--verify", name + "^{commit}").stdout.decode().strip()

    main_ref, head = revision(args.main), revision(args.candidate)
    objects = git("rev-parse", "--path-format=absolute", "--git-path", "objects")
    with tempfile.TemporaryDirectory() as scratch:
        env = dict(os.environ, GIT_OBJECT_DIRECTORY=scratch,
                   GIT_ALTERNATE_OBJECT_DIRECTORIES=os.fsdecode(objects.stdout.rstrip(b"\n")))
        merge = ["merge-tree", "--write-tree", "--no-messages", "-z"]
        names_run = git(*merge, "--name-only", main_ref, head, env=env, allowed=(0, 1))
        stages_run = git(*merge, main_ref, head, env=env, allowed=(0, 1))
        names = names_run.stdout.rstrip(b"\0").split(b"\0")
        records = stages_run.stdout.rstrip(b"\0").split(b"\0")
        if names_run.returncode != stages_run.returncode or names[0] != records[0]:
            raise ValueError("the two trial merges disagree")
        by_path = defaultdict(set)
        for record in records[1:]:
            meta, path = record.split(b"\t", 1)
            by_path[path].add(int(meta.split()[2]))
        if len(names[1:]) != len(by_path) or set(names[1:]) != set(by_path):
            raise ValueError("the two conflict path inventories disagree")
        if (names_run.returncode == 0) != (len(by_path) == 0):
            raise ValueError("merge status and conflict path count disagree")
    stages = Counter(",".join(str(n) for n in sorted(values)) for values in by_path.values())
    direct_import = (r"^[[:blank:]]*((public|private|meta)[[:blank:]]+)*"
                     r"import[[:blank:]]+(all[[:blank:]]+)?Mathlib[[:blank:]]*(--.*)?$")
    broad = {}
    for sha in (main_ref, head):
        found = git("grep", "-I", "-l", "-z", "-E", direct_import, sha, "--", "src/*.lean",
                    allowed=(0, 1))
        broad[sha] = found.stdout.count(b"\0")
    print(json.dumps({
        "main": main_ref, "candidate": head,
        "merge_base": git("merge-base", main_ref, head).stdout.decode().strip(),
        "git_version": git("--version").stdout.decode().strip(),
        "merge_exit": names_run.returncode, "conflicting_paths": len(by_path),
        "stage_patterns": dict(sorted(stages.items())),
        "src_conflicts": sum(path.startswith(b"src/") for path in by_path),
        "non_src_conflicts": sorted(os.fsdecode(p) for p in by_path if not p.startswith(b"src/")),
        "git_warnings": list(dict.fromkeys(
            (names_run.stderr + stages_run.stderr).decode(errors="replace").splitlines())),
        "files_with_direct_Mathlib_import_line": broad
    }, indent=2))


if __name__ == "__main__":
    main()
