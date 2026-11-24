"""Count source lines and commands in complete Git trees."""
import argparse
import collections
import json
from pathlib import Path

from audit_source import GitBlobs, git


def line_class(line):
    text = line.strip()
    if not text:
        return "blank"
    if text.startswith(b"--"):
        return "comment"
    if text == b"end" or text.startswith(b"end "):
        return "end"
    if text == b"section" or text.startswith(b"section "):
        return "section"
    if text.startswith(b"@[expose] public "):
        return "public"
    if text == b"noncomputable section":
        return "noncomputable"
    if text.startswith(b"open "):
        return "open"
    return "other"


def inventory(repo, refs):
    reader = GitBlobs(repo)
    counts_by_blob = {}
    result = {}
    try:
        for ref in refs:
            groups = collections.defaultdict(collections.Counter)
            for item in git(repo, "ls-tree", "-rz", ref).split(b"\0"):
                if not item:
                    continue
                entry, raw_path = item.split(b"\t", 1)
                if not raw_path.endswith(b".lean"):
                    continue
                path = raw_path.decode()
                blob = entry.split()[2]
                if blob not in counts_by_blob:
                    data = reader.read(ref, path)
                    lines = data.splitlines()
                    counts = collections.Counter(line_class(line) for line in lines)
                    counts.update(modules=1, bytes=len(data), lines=len(lines),
                                  nonblank=len(lines) - counts["blank"])
                    counts_by_blob[blob] = counts
                group = "src" if path.startswith("src/") else "other_lean"
                groups[group].update(counts_by_blob[blob])
            result[ref] = dict(groups)
    finally:
        reader.close()
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ref", nargs="+")
    parser.add_argument("--repo", type=Path, default=Path("."))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(inventory(args.repo, args.ref), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
