"""Repeat the comparison between the terminal M4 run and the first closure of PR #120."""
import argparse
from collections import Counter
from difflib import SequenceMatcher
import hashlib
import json
from pathlib import Path
import re
import subprocess


PIN = "2d20aa9035becfe380b9fe619e3d3fc968cf3400"
CLOSING = "fbb0941754dee95d15639f3d4d5596a3f508648b"
GIST_REVISION = "5e431652188c0c9b498e6b0284b830da7da8cde5"
CHECKSUMS = {
    "final-all-errors-2d20.txt": "70e54d1115387387361373a323602b2c32e6d03d993c139433db5e2161dfecf0",
    "final-first-clean-2d20.txt": "dec230dfbb40ca3d6ba064e85a296cd5b9b68202054f6bf630f4fa47f28411bd",
}
DIAGNOSTIC = re.compile(r"^error: (src/[^\n]+?\.lean):(\d+):(\d+): (.*)$", re.MULTILINE)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", required=True, type=Path, help="Git repository with both commits")
    cli.add_argument("--gist-json", required=True, type=Path, help="gist revision from the GitHub API")
    cli.add_argument("--operator-report", required=True, type=Path, help="body of issue comment 7129630352")
    args = cli.parse_args()
    files = json.loads(args.gist_json.read_bytes())["files"]
    logs = {}
    for name, checksum in CHECKSUMS.items():
        data = files[name]["content"].encode()
        if hashlib.sha256(data).hexdigest() != checksum:
            raise ValueError(f"Incomplete or changed diagnostic file: {name}")
        logs[name] = DIAGNOSTIC.findall(data.decode())
    all_errors = logs["final-all-errors-2d20.txt"]
    first_errors = logs["final-first-clean-2d20.txt"]
    counts = Counter(path for path, *_ in all_errors)
    listed = re.findall(r"^- `([^`\n]+\.lean):(\d+)` —", args.operator_report.read_text(), re.MULTILINE)
    if (len(all_errors), len(counts), len(first_errors), len(listed)) != (67, 16, 16, 16):
        raise ValueError("The diagnostic counts differ from the terminal receipt.")
    if {path for path, *_ in first_errors} != counts.keys() or not set(first_errors) <= set(all_errors):
        raise ValueError("The first-error log and the full diagnostic log disagree.")
    if {(path.removeprefix("src/"), line) for path, line, *_ in first_errors} != set(listed):
        raise ValueError("The operator's inventory and the first-error log disagree.")

    def git(*command):
        return subprocess.check_output(["git", "-C", args.repo, *command], text=True)

    rows = []
    for path, line, column, message in first_errors:
        objects = [git("rev-parse", f"{rev}:{path}").strip() for rev in (PIN, CLOSING)]
        old, new = [git("cat-file", "blob", oid).splitlines() for oid in objects]
        index = int(line) - 1
        if not 0 <= index < len(old):
            raise ValueError(f"Invalid location: {path}:{line}")
        mapped = None
        for tag, start, stop, new_start, _ in SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
            if start <= index < stop and tag == "equal":
                mapped = new_start + index - start + 1
                break
        commits = git("log", "--no-merges", "--abbrev=11", "--format=%h %s", f"{PIN}..{CLOSING}", "--", path)
        rows.append(dict(path=path, errors=counts[path], first=[int(line), int(column), message],
                         oldBlob=objects[0], closingBlob=objects[1], sameSource=objects[0] == objects[1],
                         unchangedLineAt=mapped, sourceCommits=commits.splitlines()))
    report = dict(pin=PIN, closing=CLOSING, gist=GIST_REVISION, logSHA256=CHECKSUMS, errors=len(all_errors),
                  files=len(rows), sameSource=sum(row["sameSource"] for row in rows), rows=rows)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
