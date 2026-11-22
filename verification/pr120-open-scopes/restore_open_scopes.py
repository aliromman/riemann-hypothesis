#!/usr/bin/env python3
"""Reproduce the namespace corrections for the submitted RH consolidation and author PR 16."""
import argparse
import difflib
import gzip
import hashlib
import json
import re
import subprocess
import tempfile
from collections import defaultdict
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def filename(module):
    return "src/" + module.replace(".", "/") + ".lean"


def read_blobs(repo, requests):
    result = {}
    with subprocess.Popen(
        ["git", "-C", str(repo), "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE
    ) as child:
        for request, expected in requests.items():
            child.stdin.write((request + "\n").encode())
            child.stdin.flush()
            header = child.stdout.readline().decode().rstrip().split()
            require(len(header) == 3 and header[1] == "blob", "Cannot read " + request)
            require(expected is None or header[0] == expected, "Incorrect Git blob for " + request)
            data = child.stdout.read(int(header[2]))
            require(child.stdout.read(1) == b"\n", "Incomplete Git output for " + request)
            result[request] = data.decode().splitlines()
        child.stdin.close()
        require(child.wait() == 0, "git cat-file failed")
    return result


def check_archive(path, evidence):
    require(sha256(path.read_bytes()) == evidence["archiveManifestSha256"], "Incorrect archive manifest")
    members = evidence["members"]
    found = set()
    with gzip.open(path, "rt") as source:
        require(json.loads(next(source))["source_tree"] == evidence["originalSourceTree"], "Incorrect source tree")
        for row in source:
            name, dep, archive, digest = json.loads(row)
            if name in members:
                item = members[name]
                require([dep, archive, digest] == [item["depHash"], item["archive"], item["archiveSha256"]], name)
                found.add(name)
    require(found == set(members), "The archive does not cover all historical members")


def check_selected(roots, rows, members):
    by_member = defaultdict(list)
    for row in rows:
        by_member[row["member"]].extend(row["selected"])
    count = 0
    for member, references in by_member.items():
        if not references:
            continue
        path = Path(*member.split(".")).with_suffix(".ilean")
        expected = members[member]["ileanSha256"]
        data = next((raw for root in roots if (root / path).is_file()
                     and sha256(raw := (root / path).read_bytes()) == expected), None)
        require(data is not None, "Missing original compiler reference index for " + member)
        actual = set()
        for key, entries in json.loads(data)["references"].items():
            declaration = json.loads(key).get("c")
            if declaration:
                for line, start, end_line, end, *_ in entries["usages"]:
                    if line == end_line:
                        actual.add((line, start, end, declaration["n"], declaration["m"]))
        for ref in references:
            identity = (ref["line"], ref["start"], ref["end"], ref["constant"], ref["provider"])
            require(identity in actual, "Incorrect selected declaration in " + member)
            count += 1
    return count


def verify_native(lean, folder, rows):
    version = subprocess.check_output([lean, "--version"], text=True)
    require(re.search(r"\bversion 4\.36\.0\b", version), "Lean 4.36.0 is required")
    with tempfile.TemporaryDirectory() as temp:
        cases = Path(temp) / "cases.jsonl"
        cases.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))
        proc = subprocess.run([lean, "--run", str(folder / "VerifyOpenScopes.lean"), str(cases)],
                              text=True, check=True, stdout=subprocess.PIPE)
    require(proc.stdout.strip() == "verified " + str(len(rows)), proc.stdout)


def put(lines, row, offset=0):
    i = row["line"]
    start, end = row["start"] + offset, row["end"] + offset
    require(lines[i][start:end] == row["token"], "Incorrect selector in " + row["bundle"])
    lines[i] = lines[i][:start] + row["correction"] + lines[i][end:]


def make_patch(repo, evidence, incremental):
    rows = evidence["rows"]
    original = evidence["original"]
    submitted = evidence["submitted"]
    parent = evidence["author16"] if incremental else submitted
    requests = {original + ":" + filename(n): x["source"] for n, x in evidence["members"].items()}
    for n, oid in evidence["submittedBlobs"].items():
        name = filename(n)
        requests[submitted + ":" + name] = oid
        if incremental:
            requests[parent + ":" + name] = None
    for name, oid in evidence["protected"].items():
        requests[submitted + ":" + name] = oid
        requests[parent + ":" + name] = oid
    blobs = read_blobs(repo, requests)
    grouped = defaultdict(list)
    for row in rows:
        source = blobs[original + ":" + filename(row["member"])]
        require(source[row["originalLine"]][row["start"]:row["end"]] == row["token"], row["member"])
        grouped[row["bundle"]].append(row)
    patch, changed, files = [], 0, 0
    for n, entries in sorted(grouped.items()):
        name = filename(n)
        require(name not in evidence["protected"], "Protected file in selector evidence")
        original_lines = blobs[submitted + ":" + name]
        base = blobs[parent + ":" + name]
        sort_key = lambda r: (r["line"], r["start"])
        prior = [r for r in entries if incremental and r["credit"] == 16]
        expected_base = original_lines.copy()
        for row in sorted(prior, key=sort_key, reverse=True):
            put(expected_base, row)
        require(expected_base == base, "Unrecorded parent change in " + name)
        edits = [r for r in entries if not incremental or r["credit"] is None]
        if not edits:
            continue
        result = base.copy()
        for row in sorted(edits, key=sort_key, reverse=True):
            shift = sum(len(r["correction"]) - len(r["token"]) for r in prior
                        if r["line"] == row["line"] and r["end"] <= row["start"])
            put(result, row, shift)
        patch.extend(difflib.unified_diff([s + "\n" for s in base], [s + "\n" for s in result],
                                          "a/" + name, "b/" + name))
        changed += len(edits)
        files += 1
    data = "".join(patch).encode()
    digest = evidence["incrementalPatchSha256" if incremental else "cumulativePatchSha256"]
    require(sha256(data) == digest, "The regenerated patch digest does not match the evidence")
    return data, changed, files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--variant", choices=["cumulative", "incremental"], required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--verify-lean", metavar="LEAN")
    parser.add_argument("--archive-manifest", type=Path)
    parser.add_argument("--original-library", type=Path, action="append", default=[])
    args = parser.parse_args()
    folder = Path(__file__).resolve().parent
    evidence = json.loads(gzip.decompress((folder / "evidence.json.gz").read_bytes()))
    require(evidence["schema"] == 1, "Unsupported evidence format")
    if args.archive_manifest:
        check_archive(args.archive_manifest, evidence)
    if args.original_library:
        print("Verified selected compiler references", check_selected(args.original_library, evidence["rows"], evidence["members"]))
    if args.verify_lean:
        verify_native(args.verify_lean, folder, evidence["rows"])
        print("Verified native Lean namespace resolutions", len(evidence["rows"]))
    data, changed, files = make_patch(args.repo, evidence, args.variant == "incremental")
    args.output.write_bytes(data)
    print("Generated", changed, "selector corrections in", files, "files")
    print("SHA-256", sha256(data))


if __name__ == "__main__":
    main()
