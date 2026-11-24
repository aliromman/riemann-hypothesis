"""Compare a clump refactor against its parent with both versions of the project clumper."""
import argparse
import collections
import gzip
import hashlib
import importlib.util
import io
import json
import re
import subprocess
import tempfile
from pathlib import Path


def git(repo, *args):
    return subprocess.check_output(["git", "-c", "core.quotepath=false", *args], cwd=repo)


class GitBlobs:
    def __init__(self, repo):
        self.process = subprocess.Popen(["git", "cat-file", "--batch"], cwd=repo,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def read(self, ref, path):
        request = (ref + ":" + path + "\n").encode()
        self.process.stdin.write(request)
        self.process.stdin.flush()
        response = self.process.stdout.readline().split()
        if len(response) != 3 or response[1] != b"blob":
            raise ValueError(f"cannot read {ref}:{path}")
        data = self.process.stdout.read(int(response[2]))
        if self.process.stdout.read(1) != b"\n":
            raise ValueError("incomplete Git blob")
        return data

    def close(self):
        self.process.stdin.close()
        if self.process.wait() != 0:
            raise ValueError("git cat-file failed")


def clumper(reader, rev, folder, name):
    path = folder / (name + ".py")
    path.write_bytes(reader.read(rev, "scripts/clump.py"))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fused_body(old, new):
    """Recognize the change to an original member without using the migration algorithm."""
    before, after = old.split("\n"), new.split("\n")
    if not before or not after or before[0] != "@[expose] public section":
        return None
    if after[0] != "@[expose] public noncomputable section":
        return None
    try:
        start = before.index("noncomputable section")
    except ValueError:
        return None
    adjoining_blanks = start > 0 and start + 1 < len(before) and before[start - 1] == before[start + 1] == ""
    before[0] = after[0]
    del before[start]
    candidates = [(before, False)]
    if adjoining_blanks:
        candidates.append((before[:start - 1] + before[start:], True))
    for candidate, tidied in candidates:
        if candidate == after:
            return tidied
        if len(candidate) != len(after) + 1:
            continue
        stop = next((i for i, pair in enumerate(zip(candidate, after)) if pair[0] != pair[1]), len(after))
        if (stop >= start - int(tidied) and re.fullmatch(r"end\s*(?:--.*)?", candidate[stop]) and
                candidate[stop + 1:] == after[stop:]):
            return tidied
    return None


def line_kind(line):
    text = line.strip()
    if not text:
        return "blank"
    if text.startswith("--"):
        return "line_comment"
    if text == "end" or text.startswith("end "):
        return "end"
    if text == "section" or text.startswith("section "):
        return "section"
    if text.startswith("@[expose] public "):
        return "public_section"
    if text == "noncomputable section":
        return "noncomputable_section"
    if text.startswith("open "):
        return "open"
    return "other"


def compare(reader, base, head, path, previous_tool, new_tool):
    original = reader.read(base, path)
    proposed = reader.read(head, path)
    old, new = original.decode(), proposed.decode()
    name = path.removeprefix("src/").removesuffix(".lean").replace("/", ".")
    if not new_tool.is_clump_file(new_tool.Module(name, path, new)):
        raise ValueError("the planner would treat an existing clump as a new candidate")
    prefix, marker, body = new.partition(new_tool.CLUMP_MARK)
    if not marker or old.partition(previous_tool.CLUMP_MARK)[0] != prefix:
        raise ValueError("file preamble changed")
    old_members = previous_tool.unclump_text(old)
    new_members = new_tool.unclump_text(new)
    if list(old_members) != list(new_members):
        raise ValueError("original member names or order changed")
    member_modules = {}
    fusions = 0
    tidied = 0
    for name, text in old_members.items():
        former = previous_tool.Module(name, "", text)
        updated = new_members[name]
        if updated != text:
            if not updated.startswith(former.header):
                raise ValueError("original import header changed in " + name)
            seam = fused_body(former.body, updated[len(former.header):])
            if seam is None:
                raise ValueError("unexpected source difference in " + name)
            fusions += 1
            tidied += int(seam)
        member_modules[name] = new_tool.Module(name, "", updated)
    rendered = new_tool.render("", list(member_modules), member_modules)
    if rendered.partition(new_tool.CLUMP_MARK)[2] != body:
        raise ValueError("the normal renderer produced a different file body")
    old_lines = old.splitlines()
    new_lines = new.splitlines()
    ordinary = lambda lines: [line for line in lines if line_kind(line) == "other"]
    if ordinary(old_lines) != ordinary(new_lines):
        raise ValueError("ordinary mathematical source changed")
    delta = collections.Counter(map(line_kind, old_lines))
    delta.subtract(map(line_kind, new_lines))
    commands = sum(delta[k] for k in ("section", "end", "open", "public_section", "noncomputable_section"))
    return dict(path=path, parent_sha256=hashlib.sha256(original).hexdigest(),
                candidate_sha256=hashlib.sha256(proposed).hexdigest(), members=len(old_members),
                fusions=fusions, tidied_members=tidied, fewer_commands=commands,
                fewer_nonblank=commands + delta["line_comment"],
                fewer_bytes=len(original) - len(proposed), categories=dict(sorted(delta.items())))


def audit(repo, base, head, output):
    changed = git(repo, "diff", "--no-renames", "--name-status", "-z", base, head, "--", "src")
    fields = changed.split(b"\0")[:-1]
    if any(status != b"M" for status in fields[::2]):
        raise ValueError("expected edits to existing modules")
    paths = [p.decode() for p in fields[1::2]]
    reader = GitBlobs(repo)
    totals = collections.Counter()
    try:
        with (tempfile.TemporaryDirectory() as tmp, output.open("wb") as raw,
              gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as packed,
              io.TextIOWrapper(packed, encoding="utf-8") as log):
            old = clumper(reader, base, Path(tmp), "base_clump")
            new = clumper(reader, head, Path(tmp), "head_clump")
            for path in paths:
                try:
                    row = compare(reader, base, head, path, old, new)
                except ValueError as error:
                    raise ValueError(f"{path}: {error}") from error
                print(json.dumps(row, ensure_ascii=False, separators=(",", ":")), file=log)
                totals.update({key: row[key] for key in
                               ("members", "fusions", "tidied_members", "fewer_commands",
                                "fewer_nonblank", "fewer_bytes")})
    finally:
        reader.close()
    print(json.dumps(dict(modules=len(paths), **totals), indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base")
    parser.add_argument("head")
    parser.add_argument("--repo", type=Path, default=Path("."))
    parser.add_argument("--output", type=Path, default=Path("clump-source-rows.jsonl.gz"))
    args = parser.parse_args()
    audit(args.repo, args.base, args.head, args.output)
