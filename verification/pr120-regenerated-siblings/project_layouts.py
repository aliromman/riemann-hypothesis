"""Join the logical member inventories from the upstream and author file layouts."""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import subprocess

MARKERS = {
    "main": ("-- ===== clump member: ", " ====="),
    "author": ("-- bundled from ", ""),
}


def git(repo, *args, allowed=(0,)):
    p = subprocess.run(["git", "-C", repo, *args], capture_output=True)
    if p.returncode not in allowed:
        raise RuntimeError(p.stderr.decode())
    return p.stdout


def members(repo, ref, marker):
    paths = git(repo, "ls-tree", "-rz", "--name-only", ref, "--", "src").decode().split("\0")
    files = {p: [] for p in paths if p.endswith(".lean")}
    prefix, suffix = marker
    lines = git(repo, "grep", "-I", "-z", "-e", "^" + prefix, ref, "--", "src/*.lean",
                allowed=(0, 1))
    for record in lines.decode().splitlines():
        physical, body = record.split("\0", 1)
        p = physical.split(":", 1)[1]
        if not body.startswith(prefix) or not body.endswith(suffix):
            raise ValueError((p, body))
        name = body[len(prefix):].removesuffix(suffix)
        if not name or any(c.isspace() for c in name):
            raise ValueError((p, name))
        files[p].append(name)
    logical = {}
    for p, group in files.items():
        if not group:
            group.append(p[4:-5].replace("/", "."))
        for member in group:
            if member in logical:
                raise ValueError(("duplicate logical owner", member, logical[member], p))
            logical[member] = p
    return files, logical


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("main")
    ap.add_argument("author")
    a = ap.parse_args()
    refs = [git(a.repo, "rev-parse", "--verify", v + "^{commit}").decode().strip() for v in (a.main, a.author)]
    (main_files, main_logical), (author_files, author_logical) = [
        members(a.repo, ref, MARKERS[kind]) for ref, kind in zip(refs, ("main", "author"))]
    buckets = defaultdict(list)
    categories = Counter()
    for path, group in main_files.items():
        owners = {author_logical.get(member) for member in group}
        if owners == {None}:
            categories["no author member"] += 1
        elif None in owners:
            categories["mixture with new main member"] += 1
        elif len(owners) > 1:
            categories["multiple author owners"] += 1
        else:
            owner, = owners
            buckets[owner].append(path)
            categories["one author owner"] += 1
    joins = {owner: sorted(paths) for owner, paths in sorted(buckets.items()) if len(paths) > 1}
    a.out.mkdir(exist_ok=True, parents=True)
    (a.out / "whole-main-owners.json").write_text(json.dumps(joins, ensure_ascii=False, indent=2) + "\n")
    result = {
        "main": refs[0], "author": refs[1], "main_physical": len(main_files), "author_physical": len(author_files),
        "main_logical": len(main_logical), "author_logical": len(author_logical),
        "shared_logical": len(main_logical.keys() & author_logical.keys()),
        "only_main_logical": len(main_logical.keys() - author_logical.keys()),
        "only_author_logical": len(author_logical.keys() - main_logical.keys()),
        "main_file_disposition": dict(categories), "author_buckets_with_multiple_whole_main_files": len(joins),
        "potential_file_difference_before_graph_and_semantic_checks": sum(len(v) - 1 for v in joins.values()),
    }
    (a.out / "layout-overlap.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
