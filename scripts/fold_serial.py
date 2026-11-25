#!/usr/bin/env python3
"""Recreate the serial proof folds on a batch branch.

Run `python3 scripts/fold_serial.py . | git apply` from the project root.
Each line of serial-folds.txt names a helper and its sole importer. The
importer keeps its path. The patch uses the sources in the checkout.
"""

import argparse
from collections import defaultdict
import difflib
from io import StringIO
import json
from pathlib import Path
import subprocess
import sys

import clump


def project_imports(root):
    """Include tracked Lean tools and Comparator bridges when looking for importers."""
    raw = subprocess.check_output(["git", "ls-files", "-z", "*.lean"], cwd=root)
    paths = [Path(s.decode()) for s in raw.split(b"\0") if s]
    data = subprocess.check_output(["lean", "--deps-json", "--stdin"], cwd=root,
                                   input="".join(f"{p}\n" for p in paths).encode())
    results = json.loads(data)["imports"]
    if len(results) != len(paths):
        raise ValueError("Lean did not return one header for each source")
    graph = {}
    for path, result in zip(paths, results):
        if result["errors"]:
            raise ValueError(f"{path}: {result['errors']}")
        name = path.as_posix()
        if path.parts[0] == "src":
            name = ".".join(path.relative_to("src").with_suffix("").parts)
        graph[name] = result["result"]["imports"]
    return graph


def reaches(start, needed, edges):
    todo = list(start)
    seen = set()
    missing = set(needed)
    while todo and missing:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            missing.discard(name)
            todo.extend(edges.get(name, ()))
    return not missing


def originals(module):
    """Keep current proof bodies, including edits made after the first clump."""
    if not clump.is_clump_file(module):
        return {module.name: module}
    try:
        texts = clump.unclump_text(module.body)
    except (AssertionError, IndexError, KeyError, ValueError) as error:
        raise ValueError(f"{module.name}: invalid clump records") from error
    parts = {name: clump.Module(name, "", text) for name, text in texts.items()}
    if module.name not in parts or any(clump.is_clump_file(m) for m in parts.values()):
        raise ValueError(f"{module.name}: invalid or nested clump")
    rebuilt = clump.render(module.name, list(parts), parts)
    if clump.Module(module.name, "", rebuilt).body != module.body:
        raise ValueError(f"{module.name}: the member records do not reproduce the current body")
    if "--" in module.header or "/-" in module.header:
        raise ValueError(f"{module.name}: the physical import header contains a comment")
    return parts


def receiver_imports(donor, receiver):
    # Import order can select a different type class instance. Expand the
    # helper where the receiver imports it. A public import of the helper
    # exposes only the helper's public imports.
    entries = []
    for entry in receiver.imports:
        if entry[0] == donor.name:
            entries.extend(item for item in donor.imports if item[1])
        else:
            entries.append(entry)
    names = dict.fromkeys(name for name, _ in entries)
    exported = dict.fromkeys(name for name, public in entries if public)
    if [name for name in names if name in exported] != list(exported):
        raise ValueError(f"{receiver.name}: deduplication would reorder public imports")
    return [(name, name in exported) for name in names]


def fold(root, groups, graph, exclude):
    users = defaultdict(set)
    import_all = set()
    public = {}
    for name, imports in graph.items():
        public[name] = {i["module"] for i in imports if i["isExported"] and not i["isMeta"]}
        for i in imports:
            users[i["module"]].add(name)
            if i["importAll"]:
                import_all.add(i["module"])

    files = {}

    def add_pair(donor, receiver):
        pair = (donor, receiver)
        if donor == receiver or any(name in files for name in pair):
            raise ValueError(f"{receiver}: repeated module in the fold plan")
        for name in pair:
            if name not in graph:
                raise ValueError(f"{name}: absent from the current tree")
        if clump.lib_of(receiver) in clump.PROTECTED_LIBS or clump.lib_of(donor) != clump.lib_of(receiver):
            raise ValueError(f"{receiver}: protected module or different libraries")
        outside = users[donor] - {receiver}
        if outside:
            raise ValueError(f"{donor}: also imported by {sorted(outside)}")
        if donor not in public[receiver] or receiver in public[donor]:
            raise ValueError(f"{receiver}: expected a public import of {donor}")
        if donor in import_all or receiver in import_all:
            raise ValueError(f"{receiver}: a member is the target of an import all")

        physical = {}
        logical = {}
        for name in pair:
            path = Path("src", *name.split(".")).with_suffix(".lean")
            module = clump.Module(name, path, (root / path).read_bytes().decode())
            # Lean adds two Init imports to a module. Check the explicit imports
            # against Lean's header before using the clump reader to write them.
            parsed = [(i["module"], i["isExported"], i["isMeta"], i["importAll"]) for i in graph[name]]
            implicit = [("Init", True, False, False), ("Init", True, True, False)]
            expected = [(n, p, False, False) for n, p in module.imports]
            if "module" not in module.header.splitlines() or parsed != implicit + expected:
                raise ValueError(f"{name}: the clump reader does not support the current Lean header")
            parts = originals(module)
            if logical.keys() & parts.keys() or exclude.intersection(parts):
                raise ValueError(f"{name}: repeated or excluded clump member")
            logical.update(parts)
            physical[name] = module
        if physical[donor].decls & physical[receiver].decls:
            raise ValueError(f"{receiver}: the modules contain conflicting declaration names")
        imports = receiver_imports(physical[donor], physical[receiver])
        private = {n for n, exported in physical[donor].imports if not exported}
        if not reaches([n for n, _ in imports], private, public):
            raise ValueError(f"{receiver}: the fold would expose a new private import")
        # The clump writer preserves the member bodies and their recorded headers.
        # Use the current physical imports for the new file header.
        rendered = clump.render(receiver, list(logical), logical)
        body = clump.Module(receiver, "", rendered).body
        header = ["module", ""]
        header.extend(("public import " if public else "import ") + name for name, public in imports)
        combined = "\n".join([*header, "", body])
        if clump.unclump_text(combined) != {m: p.header + p.body for m, p in logical.items()}:
            raise ValueError(f"{receiver}: the folded source does not reproduce its members")
        for name, module in physical.items():
            files[name] = (module.path, module.header + module.body, combined if name == receiver else None)

    errors = []
    for donor, receiver in groups:
        try:
            add_pair(donor, receiver)
        except ValueError as error:
            errors.append(f"{donor} -> {receiver}: {error}")
    if errors:
        raise ValueError("Review these fold plan entries on this branch:\n" + "\n".join(errors))
    return files


def write_patch(files, stream):
    for path, before, after in files.values():
        target = f"b/{path}" if after is not None else "/dev/null"
        lines = difflib.unified_diff(StringIO(before).readlines(), StringIO(after or "").readlines(),
                                     f"a/{path}", target)
        for line in lines:
            stream.write(line if line.endswith("\n") else line + "\n\\ No newline at end of file\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    plan = Path(__file__).with_name("serial-folds.txt")
    groups = [line.split() for line in plan.read_text().splitlines() if line.strip()]
    exclude = clump.read_exclude(Path(clump.__file__).with_name("clump-exclude.txt"))
    files = fold(args.root, groups, project_imports(args.root), exclude)
    write_patch(files, sys.stdout)


if __name__ == "__main__":
    main()
