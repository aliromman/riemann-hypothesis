"""Apply an author's sibling groups to the narrowed imports of a fixed upstream commit."""
import argparse
from collections import defaultdict
from graphlib import TopologicalSorter
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from project_layouts import MARKERS, members
from render_sibling_projection import as_path, git, load_clump, run


def module(path):
    return path[4:-5].replace("/", ".")


def read_headers(parser, repo, base, lean, temp):
    path = temp / "main-headers.jsonl"
    subprocess.run([sys.executable, parser, "--repo", repo, "--lean", lean, "--out", path, base], check=True)
    with path.open() as stream:
        metadata = json.loads(next(stream))
        if metadata["revision"] != base:
            raise ValueError("source header revision differs from base")
        return {module(path): (active, tuple(map(tuple, imports)))
                for path, _, active, imports in map(json.loads, stream)}


def ownership(repo, base, author):
    physical, _ = members(repo, base, MARKERS["main"])
    _, original = members(repo, author, MARKERS["author"])
    buckets = defaultdict(list)
    for path, logical in physical.items():
        destinations = {original.get(name) for name in logical}
        if None not in destinations and len(destinations) == 1:
            owner, = destinations
            buckets[owner].append(module(path))
    return buckets


def graph_of(headers):
    roots = {m.split(".")[0] for m in headers}
    graph = {}
    for name, (_, imports) in headers.items():
        graph[name] = []
        for dep, *_ in imports:
            if dep.split(".")[0] in roots:
                if dep not in headers:
                    raise ValueError("missing project import " + dep + " in " + name)
                graph[name].append(dep)
    tuple(TopologicalSorter(graph).static_order())
    return graph


def cone(graph, targets):
    reached, todo = set(), list(targets)
    while todo:
        m = todo.pop()
        if m not in reached:
            reached.add(m)
            todo.extend(graph[m])
    return reached


def plan(headers, owners, max_inputs):
    graph = graph_of(headers)
    reverse = defaultdict(lambda: defaultdict(list))
    for user, (_, imports) in headers.items():
        for pos, (name, *mode) in enumerate(imports):
            if name in headers:
                reverse[name][user].append((pos, tuple(mode)))
    rows = []
    for owner, files in sorted(owners.items()):
        for x, y in combinations(sorted(files), 2):
            if headers[x] != headers[y] or not reverse[x] or reverse[x].keys() != reverse[y].keys():
                continue
            order = set()
            for client, left in reverse[x].items():
                right = reverse[y][client]
                if len(left) != 1 or len(right) != 1 or left[0][1] != right[0][1]:
                    break
                order.add(right[0][0] - left[0][0])
            else:
                if order not in ({1}, {-1}):
                    continue
                pair = [x, y] if order == {1} else [y, x]
                consumers = sorted(reverse[x])
                if max_inputs is not None and len(cone(graph, pair + consumers)) > max_inputs:
                    continue
                rows.append(dict(original_owner=owner, members=pair, consumers=consumers))
    return rows


def verify_headers(lean, output, headers, manifest):
    retired = {m: root for root, group in manifest["groups"].items() for m in group[:-1]}
    changed = sorted(manifest["sources"])
    files = [output / as_path(name) for name in changed]
    parsed = json.loads(subprocess.check_output([lean, "--deps-json", *files]))["imports"]
    if len(changed) != len(parsed):
        raise ValueError("missing generated header")
    projected = {name: header for name, header in headers.items() if name not in retired}
    for name, row in zip(changed, parsed):
        if row["errors"]:
            raise ValueError((name, row["errors"]))
        result = row["result"]
        imports = [(i["module"], i["isExported"], i["isMeta"], i["importAll"]) for i in result["imports"]]
        projected[name] = (result["isModule"], tuple(imports))
    for name, (active, original) in headers.items():
        kept = []
        for dep, *mode in original:
            if dep not in retired:
                kept.append((dep, *mode))
        root = retired.get(name, name)
        if projected[root] != (active, tuple(kept)):
            raise ValueError("generated header differs from the ordered source imports for " + name)
        # Every removed import has an adjacent survivor with the same import mode.
        # Check the order independently of the group selection.
        for i, (dep, *mode) in enumerate(original):
            if dep in retired:
                owner = retired[dep]
                j = i + 1
                while j < len(original) and original[j][0] in retired and retired[original[j][0]] == owner:
                    if original[j][1:] != tuple(mode):
                        raise ValueError("different import modes in " + name)
                    j += 1
                if j == len(original) or original[j] != (owner, *mode):
                    raise ValueError("missing adjacent surviving import in " + name)
    graph = graph_of(projected)
    return dict(input_headers=len(headers), output_headers=len(projected), removed=len(retired),
                initial_main_modules=len(cone(graph_of(headers), ["Main"])), final_main_modules=len(cone(graph, ["Main"])))


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    for flag in ("repo", "out", "lean"):
        cli.add_argument("--" + flag, type=Path, required=True)
    cli.add_argument("--max-project-inputs", type=int)
    cli.add_argument("base")
    cli.add_argument("author")
    args = cli.parse_args()
    args.base, args.author = (git(args.repo, "rev-parse", "--verify", rev + "^{commit}").decode().strip()
                              for rev in (args.base, args.author))
    args.cohort = None
    if args.out.exists() and any(args.out.iterdir()):
        raise SystemExit("select an empty output directory")
    with tempfile.TemporaryDirectory() as d:
        temp = Path(d)
        headers = read_headers(Path(__file__).with_name("git_lean_headers.py"), args.repo, args.base, args.lean, temp)
        owners = ownership(args.repo, args.base, args.author)
        rows = plan(headers, owners, args.max_project_inputs)
        run(args, load_clump(args.repo, args.base, temp), rows)
        manifest = json.loads((args.out / "projection.json").read_bytes())
        audit = verify_headers(args.lean, args.out, headers, manifest)
        (args.out / "header-check.json").write_text(json.dumps(audit, indent=2) + "\n")
        print(json.dumps(audit), flush=True)


if __name__ == "__main__":
    main()
