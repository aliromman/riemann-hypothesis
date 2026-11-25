"""Find the project build targets that cover all users of the three matrix providers."""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path

from compare_providers import OWNERS

def reachable(edges, start):
    seen = set()
    todo = list(start)
    while todo:
        module = todo.pop()
        if module not in seen:
            seen.add(module)
            todo.extend(edges[module])
    return seen

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("headers", type=Path, help="Output from git_lean_headers.py for the revision")
    args = p.parse_args()
    with args.headers.open() as stream:
        metadata = json.loads(next(stream))
        imports = {}
        for path, _, _, deps in map(json.loads, stream):
            module = path.removeprefix("src/").removesuffix(".lean").replace("/", ".")
            if module in imports:
                raise ValueError("Duplicate project module: " + module)
            imports[module] = [d[0] for d in deps]
    graph = {n: tuple(d for d in deps if d in imports) for n, deps in imports.items()}
    users = defaultdict(set)
    for n, deps in graph.items():
        for d in deps:
            users[d].add(n)
    affected = reachable(users, OWNERS)
    in_main = reachable(graph, ["Main"])
    outside = affected - in_main
    extra = sorted(n for n in outside if not users[n].intersection(outside))
    targets = ["Main", *extra]
    if not set(OWNERS) <= graph.keys() or not affected <= reachable(graph, targets):
        raise ValueError("The targets do not cover all three providers and their users")
    digest = hashlib.sha256(("\n".join(sorted(affected)) + "\n").encode()).hexdigest()
    result = dict(revision=metadata["revision"], source_tree=metadata["src"], toolchain=metadata["toolchain"],
                  project_modules=len(graph), main_closure=len(in_main), affected=len(affected),
                  inside_main=len(affected & in_main), outside_main=sorted(outside),
                  targets=targets, affected_list_sha256=digest)
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
