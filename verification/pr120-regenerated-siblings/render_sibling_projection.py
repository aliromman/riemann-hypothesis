"""Render one projection of a verified same-import sibling plan with the upstream clump format."""
import argparse
from collections import defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile


def git(repo, *args):
    return subprocess.check_output(["git", "-C", repo, *args])


def as_path(module):
    return Path("src", *module.split(".")).with_suffix(".lean")


def load_clump(repo, revision, directory):
    path = directory / "clump.py"
    path.write_bytes(git(repo, "show", revision + ":scripts/clump.py"))
    spec = importlib.util.spec_from_file_location("pinned_clump", path)
    clump = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(clump)
    return clump


def run(args, clump, rows=None):
    if rows is None:
        rows = json.loads(args.pairs.read_bytes())
    if args.cohort is not None:
        rows = [r for r in rows if r["original_owner"] == args.cohort]
    if not rows:
        raise ValueError("no matching sibling set")
    exclude = set()
    for line in git(args.repo, "show", args.base + ":scripts/clump-exclude.txt").decode().splitlines():
        name = line.split("#", 1)[0].strip()
        if name:
            exclude.add(name)
    successors, prev, users = {}, {}, {}
    for row in rows:
        x, y = row["members"]
        if x in successors or y in prev:
            raise ValueError("the sibling ordering branches")
        successors[x], prev[y] = y, x
        for m in (x, y):
            new = tuple(row["consumers"])
            if m in users and users[m] != new:
                raise ValueError("unequal direct importers")
            users[m] = new
    groups = []
    for first in sorted(successors.keys() - prev.keys()):
        group = [first]
        while group[-1] in successors:
            group.append(successors[group[-1]])
        groups.append(group)
    if sum(len(g) - 1 for g in groups) != len(rows):
        raise ValueError("unplaced sibling pair")
    originals, result, rewrites, refused = {}, {}, defaultdict(dict), []
    def original(module):
        if module not in originals:
            originals[module] = git(args.repo, "show", args.base + ":" + as_path(module).as_posix()).decode()
        return originals[module]
    def split(module):
        return clump.Module(module, str(as_path(module)), original(module))
    def expanded(module, raw):
        return clump.unclump_text(raw) if clump.CLUMP_MARK in raw else {module: raw}
    def seams(module, raw):
        if clump.CLUMP_MARK not in raw:
            raw = clump.render(module, [module], {module: split(module)})
        _, mark, body = raw.partition(clump.SEAM_BEGIN)
        if not mark:
            raise ValueError("missing member marker in " + module)
        return mark + body
    joined = {}
    for group in groups:
        root = group[-1]
        mods = {m: split(m) for m in group}
        if len({clump.lib_of(m) for m in group}) != 1:
            refused.append([group, "different Lake libraries"])
            continue
        if any(m in exclude or clump.lib_of(m) in clump.PROTECTED_LIBS or mods[m].exotic for m in group):
            refused.append([group, "protected, excluded, or special import"])
            continue
        if any(mods[m].imports != mods[root].imports for m in group):
            raise ValueError("different ordered imports: " + root)
        names = set()
        duplicates = set()
        for member in group:
            duplicates.update(names.intersection(mods[member].decls))
            names.update(mods[member].decls)
        if duplicates:
            refused.append([group, "same declaration name"])
            continue
        logical = [k for m in group for k in expanded(m, original(m))]
        prefix = mods[root].header + clump.CLUMP_MARK + "\n-- Members: " + ", ".join(logical) + "\n\n"
        result[root] = prefix + "\n".join(seams(m, original(m)) for m in group)
        joined[root] = group
        for old in group[:-1]:
            result[old] = None
            for user in users[old]:
                rewrites[user][old] = root
    for user, retired in rewrites.items():
        if user in result:
            raise ValueError("a sibling is also a direct consumer: " + user)
        raw = original(user)
        if clump.CLUMP_MARK not in raw:
            raw = split(user).header + clump.CLUMP_MARK + "\n-- Members: " + user + "\n\n" + seams(user, raw)
        head, mark, rest = raw.partition(clump.CLUMP_MARK)
        if not mark:
            raise ValueError("missing consumer header")
        seen, kept = set(), []
        for line in head.splitlines(keepends=True):
            match = clump.IMPORT_RE.fullmatch(line.strip())
            if match and match[3] in retired:
                if match[3] in seen:
                    raise ValueError("duplicate import")
                seen.add(match[3])
            else:
                kept.append(line)
        if seen != retired.keys():
            raise ValueError("failed to remove an expected outer import from " + user)
        result[user] = "".join(kept) + mark + rest
    def recover(files):
        combined = {}
        for m, text in files.items():
            if text is None:
                continue
            members = expanded(m, text)
            if combined.keys() & members.keys():
                raise ValueError("multiple owners in expanded sources")
            combined.update(members)
        return combined
    before = {m: original(m) for m in result}
    if recover(before) != recover(result):
        raise ValueError("upstream unclump does not reproduce the original sources")
    args.out.mkdir(exist_ok=True, parents=True)
    for name, raw in result.items():
        if raw is not None:
            p = args.out / as_path(name)
            p.parent.mkdir(exist_ok=True, parents=True)
            p.write_bytes(raw.encode())
    info = dict(main=args.base, groups=joined, consumers=sorted(rewrites), refused=refused,
                deleted=sorted(k for k,v in result.items() if v is None),
                sources={m: hashlib.sha256(raw.encode()).hexdigest() for m,raw in result.items() if raw is not None},
                recovered_logical_sources=len(recover(result)))
    if getattr(args, "author", None):
        info["author"] = args.author
    (args.out / "projection.json").write_text(json.dumps(info, indent=2) + "\n")
    print(len(joined), "groups,", len(info["deleted"]), "fewer files,", len(rewrites), "direct importers,",
          info["recovered_logical_sources"], "restored logical sources,", len(refused), "refused groups")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--pairs", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--cohort")
    ap.add_argument("base")
    args = ap.parse_args()
    args.base = git(args.repo, "rev-parse", "--verify", args.base + "^{commit}").decode().strip()
    with tempfile.TemporaryDirectory() as temp:
        run(args, load_clump(args.repo, args.base, Path(temp)))


if __name__ == "__main__":
    main()
