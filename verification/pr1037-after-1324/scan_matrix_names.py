"""Find source lines that contain a spelling of the three matrix provider names."""
import argparse
import json
from pathlib import Path
import subprocess

NAMES = ("instMeasMat", "matrixMeasurableSpace", "measurableSpace_matrix")


def grep_lines(repo, tree, whole_words=False):
    args = ["git", "-C", repo, "grep", "-I", "-n", "-z", "-F"]
    if whole_words:
        args.append("-w")
    for name in NAMES:
        args.extend(["-e", name])
    proc = subprocess.run([*args, tree, "--", "src"], stdout=subprocess.PIPE)
    if proc.returncode not in (0, 1):
        proc.check_returncode()
    data = proc.stdout
    prefix = tree.encode() + b":"
    rows = []
    pos = 0
    while pos < len(data):
        end_path = data.index(b"\0", pos)
        end_number = data.index(b"\0", end_path + 1)
        end_line = data.index(b"\n", end_number + 1)
        path = data[pos:end_path]
        if not path.startswith(prefix):
            raise ValueError("Unexpected git grep path")
        if path.endswith(b".lean"):
            rows.append((path[len(prefix):].decode(), int(data[end_path + 1:end_number]),
                         data[end_number + 1:end_line].decode()))
        pos = end_line + 1
    return sorted(rows)


def scan_blobs(repo, tree):
    listing = subprocess.check_output(["git", "-C", repo, "ls-tree", "-rz", tree, "--", "src"])
    needles = [n.encode() for n in NAMES]
    rows = []
    count = 0
    with subprocess.Popen(["git", "-C", repo, "cat-file", "--batch"],
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as cat:
        for entry in listing.split(b"\0"):
            if not entry.endswith(b".lean"):
                continue
            info, path = entry.split(b"\t", 1)
            oid = info.split()[2]
            cat.stdin.write(oid + b"\n")
            cat.stdin.flush()
            actual, typ, size = cat.stdout.readline().split()
            if actual != oid or typ != b"blob":
                raise ValueError("Could not read " + path.decode())
            data = cat.stdout.read(int(size))
            if len(data) != int(size) or cat.stdout.read(1) != b"\n":
                raise ValueError("Incomplete Git blob " + oid.decode())
            count += 1
            if any(n in data for n in needles):
                for number, line in enumerate(data.split(b"\n"), start=1):
                    if any(n in line for n in needles):
                        rows.append((path.decode(), number, line.decode()))
        cat.stdin.close()
        if cat.wait():
            raise RuntimeError("git cat-file failed")
    return count, sorted(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    tree = subprocess.check_output(["git", "-C", args.repo, "rev-parse", "--verify",
                                    "--end-of-options", args.revision + "^{tree}"], text=True).strip()
    count, rows = scan_blobs(args.repo, tree)
    if grep_lines(args.repo, tree) != rows:
        raise ValueError("Git grep and the independent source scan differ")
    words = set(grep_lines(args.repo, tree, whole_words=True))
    if not words.issubset(rows):
        raise ValueError("Whole-word matches are missing from the source scan")
    record = dict(revision=args.revision, tree=tree, source_files=count, names=NAMES,
                  matching_files=len({r[0] for r in rows}), whole_word_lines=len(words),
                  lines=[dict(path=p, line=n, text=line, whole_word=(p, n, line) in words)
                         for p, n, line in rows])
    args.output.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
    print(count, "source files,", len(rows), "matching lines in", record["matching_files"], "files")


if __name__ == "__main__":
    main()
