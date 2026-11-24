"""Check a qualification-only commit against pre-consolidation Lean 4.36 editor data."""
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import json
from pathlib import Path
import re
import subprocess
import sys

NAME = re.compile(r"[\w'₀-₉]+(?:\.[\w'₀-₉]+)*")
MARKER = "-- bundled from "


def shape(text):
    return NAME.sub(lambda token: token[0].rsplit(".", 1)[-1], text)


def utf16(text):
    return len(text.encode("utf-16-le")) // 2


def followed_by_assignment(lines, index, stop):
    """Check the first token after an occurrence, across Lean comments and line breaks."""
    depth = 0
    for i in range(index, len(lines)):
        line = lines[i]
        pos = stop if i == index else 0
        while pos < len(line):
            if line.startswith("/-", pos):
                depth += 1
                pos += 2
            elif depth and line.startswith("-/", pos):
                depth -= 1
                pos += 2
            elif depth or line[pos].isspace():
                pos += 1
            elif line.startswith("--", pos):
                break
            else:
                return line.startswith(":=", pos)
    return False


def member_ranges(lines, physical):
    starts = [(index, line[len(MARKER):]) for index, line in enumerate(lines)
              if line.startswith(MARKER)]
    if not starts:
        return [(physical, 0, len(lines))]
    ends = [index for index, _ in starts[1:]] + [len(lines)]
    return [(name, start + 1, end) for (start, name), end in zip(starts, ends)]


def original_position(before, index, historical, by_shape):
    """Use a unique line, or distinguish repeated lines by unchanged neighbours."""
    possible = by_shape.get(before[index], [])
    if len(possible) == 1:
        return possible[0]
    for distance in range(1, max(index + 1, len(before) - index)):
        for offset in [-distance, distance]:
            neighbour = index + offset
            if 0 <= neighbour < len(before):
                possible = [n for n in possible if 0 <= n + offset < len(historical)
                            and historical[n + offset] == before[neighbour]]
        if len(possible) <= 1:
            break
    return possible[0] if len(possible) == 1 else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--original", required=True, help="Git revision of the original Lean sources")
    parser.add_argument("--list-members", action="store_true", help="print original Lake targets for these edits")
    parser.add_argument("--ilean-dir", type=Path,
                        help="lib/lean from a trusted 4.36 build of that original revision")
    parser.add_argument("before", help="Git revision immediately before the qualifications")
    parser.add_argument("after", help="Git revision immediately after the qualifications")
    args = parser.parse_args()
    if not args.list_members and args.ilean_dir is None:
        parser.error("supply --ilean-dir or --list-members")

    def git(*argv):
        return subprocess.check_output(["git", "-C", args.repo, *argv])

    original, base, tip = [git("rev-parse", "--verify", rev + "^{commit}").decode().strip()
                           for rev in [args.original, args.before, args.after]]

    @lru_cache(maxsize=64)
    def original_module(module):
        stem = Path(*module.split("."))
        old = git("show", f"{original}:src/{stem}.lean").decode().splitlines()
        dump = json.loads((args.ilean_dir / stem).with_suffix(".ilean").read_bytes())
        if dump["module"].removeprefix("src.") != module or not isinstance(dump["references"], dict):
            raise ValueError(f"unexpected .ilean module or format for {module}")
        uses = defaultdict(set)
        for identifier, refs in dump["references"].items():
            const = json.loads(identifier).get("c")
            if const:
                for ln, start, end, stop, *_ in refs["usages"]:
                    if ln == end:
                        uses[ln, start, stop].add(const["n"])
        shapes = list(map(shape, old))
        by_shape = defaultdict(list)
        for i, line in enumerate(shapes):
            by_shape[line].append(i)
        return old, shapes, by_shape, uses

    counts = Counter()
    members = set()

    def report(status, path, line=None, **extra):
        counts[status] += 1
        print(json.dumps(dict(status=status, path=path, line=line, **extra), ensure_ascii=False),
              file=sys.stderr if args.list_members else sys.stdout)

    fields = git("diff", "--name-status", "-z", "--no-renames", base, tip).split(b"\0")
    for operation, rawpath in zip(fields[::2], fields[1::2]):
        path = rawpath.decode()
        if operation != b"M" or not path.startswith("src/") or not path.endswith(".lean"):
            report("manual: file change", path)
            continue
        left, right = [git("show", f"{rev}:{path}").decode().splitlines(keepends=True)
                       for rev in [base, tip]]
        physical = path[4:-5].replace("/", ".")
        clean_left, clean_right = [[s.rstrip("\r\n") for s in lines] for lines in (left, right)]
        groups = member_ranges(clean_left, physical)
        if len(left) != len(right) or groups != member_ranges(clean_right, physical):
            report("manual: module layout changed", path)
            continue
        owned = set()
        for member, lo, hi in groups:
            changed = [i for i in range(lo, hi) if left[i] != right[i]]
            if not changed:
                continue
            owned.update(changed)
            members.add(member)
            if args.list_members:
                continue
            baseline = list(map(shape, clean_left[lo:hi]))
            try:
                old, old_shapes, by_shape, uses = original_module(member)
            except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
                report("manual: missing original evidence", path, member=member, detail=str(exc))
                continue
            for i in changed:
                before, after = left[i], right[i]
                if shape(before) != shape(after):
                    report("manual: other text changed", path, i + 1)
                    continue
                n = original_position(baseline, i - lo, old_shapes, by_shape)
                if n is None:
                    report("manual: no unique original line", path, i + 1, member=member)
                    continue
                tokens = [list(NAME.finditer(text)) for text in (before, after, old[n])]
                if len({len(part) for part in tokens}) != 1:
                    report("manual: token alignment changed", path, i + 1)
                    continue
                for former, proposed, site in zip(*tokens):
                    token = proposed[0]
                    if former[0] == token:
                        continue
                    start, stop = site.span()
                    names = uses[n, utf16(old[n][:start]), utf16(old[n][:stop])]
                    if not token.startswith("_root_.") or token.rsplit(".", 1)[-1] != former[0].rsplit(".", 1)[-1]:
                        verdict = "manual: edit is not an absolute qualification"
                    elif names != {token.removeprefix("_root_.")}:
                        verdict = "manual: missing or different original constant"
                    elif followed_by_assignment(old, n, stop):
                        verdict = "manual: name before := can be a field label"
                    else:
                        verdict = "matches"
                    report(verdict, path, i + 1, column=proposed.start() + 1, member=member,
                           original_line=n + 1, original_utf16_column=utf16(old[n][:start]),
                           previous=former[0], token=token, original_token=site[0],
                           original_constants=sorted(names))
        for i, (before, after) in enumerate(zip(left, right)):
            if before != after and i not in owned:
                report("manual: bundle header changed", path, i + 1)
    if args.list_members:
        for member in sorted(members):
            print(member)
    else:
        print(json.dumps(dict(original=original, before=base, after=tip, counts=counts)), file=sys.stderr)
    return int(any(key != "matches" for key in counts))


if __name__ == "__main__":
    sys.exit(main())
