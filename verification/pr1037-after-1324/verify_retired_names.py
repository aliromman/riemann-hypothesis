"""Check all project Lean sources for the four retired matrix instance names."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

NAMES = ("instMeasMat", "matrixMeasurableSpace", "measurableSpace_matrix", "borelSpace_matrix")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--output", type=Path, required=True)
    a = parser.parse_args()
    git = ["git", "-C", a.repo]
    rev = subprocess.check_output([*git, "rev-parse", "--verify", "--end-of-options",
                                     a.revision + "^{commit}"], text=True).strip()
    names = "(" + "|".join(NAMES) + ")"
    search = subprocess.run([*git, "grep", "-n", "-w", "-E", names, rev, "--", "src/*.lean"],
                            stdout=subprocess.PIPE)
    if search.returncode != 1 or search.stdout:
        raise ValueError("git grep did not confirm the removal of all four names")
    pattern = re.compile(rb"(?<![A-Za-z0-9_])" + names.encode() + rb"(?![A-Za-z0-9_])")
    tree = subprocess.check_output([*git, "ls-tree", "-rz", rev, "--", "src"])
    sources = 0
    size = 0
    with subprocess.Popen([*git, "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE) as cat:
        for row in tree.split(b"\0"):
            if not row.endswith(b".lean"):
                continue
            header, name = row.split(b"\t", 1)
            oid = header.split()[2]
            cat.stdin.write(oid + b"\n")
            cat.stdin.flush()
            actual, kind, length = cat.stdout.readline().split()
            data = cat.stdout.read(int(length))
            blob = hashlib.sha1(b"blob " + length + b"\0" + data).hexdigest().encode()
            if cat.stdout.read(1) != b"\n" or kind != b"blob" or actual != oid or blob != oid:
                raise ValueError(("Git source mismatch", name))
            if pattern.search(data):
                raise ValueError(("A retired name remains", name))
            sources += 1
            size += len(data)
        cat.stdin.close()
        if cat.wait():
            raise ValueError("The Git blob reader failed")
    receipt = dict(revision=rev, source_files=sources, source_bytes=size, hits=0,
                   git_grep_exit=search.returncode, git_blob_sha1_checked=sources, pattern=pattern.pattern.decode())
    a.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(sources, "verified source blobs", flush=True)

if __name__ == "__main__":
    main()
