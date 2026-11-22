"""Partition existing consolidation bundles by their original access to selected modules."""

import argparse
from collections import defaultdict
from contextlib import contextmanager
from dataclasses import dataclass, field
from difflib import unified_diff
from functools import cache
from graphlib import TopologicalSorter
from pathlib import Path
import os
import re
import subprocess
import tempfile


HEADER = re.compile(r"^([ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?)([^\s/]+)([ \t]*(?:(?:--|/-)[^\n]*)?\n?)$")
MEMBER = re.compile(r"^-- bundled from (\S+)\n", re.M)
GIT_HEADER = r"^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+|^-- bundled from "


@dataclass
class Source:
    imports: list = field(default_factory=list)
    members: list = field(default_factory=list)


def path_of(name):
    return "src/" + name.replace(".", "/") + ".lean"


def module_of(path):
    return path[4:-5].replace("/", ".")


def git(repo, *args):
    return ["git", "-C", str(repo), *args]


def read_graph(repo, revision):
    paths = subprocess.check_output(git(repo, "ls-tree", "-rz", "--name-only", revision, "--", "src"))
    modules = {module_of(p): Source() for p in paths.decode().split("\0") if p.endswith(".lean")}
    with subprocess.Popen(git(repo, "grep", "--no-color", "-Iz", "-E", GIT_HEADER, revision, "--", "src"),
                            stdout=subprocess.PIPE) as proc:
        for row in proc.stdout:
            path, command = row.decode().split("\0", 1)
            source = modules.get(module_of(path.split(":", 1)[1]))
            if source is None:
                continue
            member = MEMBER.fullmatch(command)
            if member:
                source.members.append(member[1])
            else:
                match = HEADER.fullmatch(command)
                if not match:
                    raise ValueError(f"Unsupported import line in {path}: {command!r}")
                source.imports.append(match[2])
        if proc.wait() != 0:
            raise RuntimeError(f"Cannot read the imports at {revision}")
    return modules


def visibility(imports, provider_bits):
    masks = {}
    for module in TopologicalSorter(imports).static_order():
        mask = provider_bits.get(module, 0)
        for dependency in imports[module]:
            mask |= masks[dependency]
        masks[module] = mask
    return masks


def internal(graph):
    return {name: [d for d in source.imports if d in graph] for name, source in graph.items()}


class Partition:
    def __init__(self, original, bundled, providers):
        self.bundled = bundled
        self.owner = {}
        for bundle, source in bundled.items():
            for member in source.members or [bundle]:
                if member not in original or member in self.owner:
                    raise ValueError(f"Expected one original source for {member}")
                self.owner[member] = bundle
        if len(set(providers)) != len(providers) or any(n not in self.owner for n in providers):
            raise ValueError("Each provider must be a distinct, retained original module")

        bits = {n: 1 << i for i, n in enumerate(providers)}
        original_mask = visibility(internal(original), bits)
        self.members = {}
        self.location = {}
        self.previous = {}
        for bundle, source in bundled.items():
            partitions = defaultdict(list)
            for member in source.members or [bundle]:
                partitions[original_mask[member]].append(member)
            largest = max(partitions, key=lambda mask: len(partitions[mask]))
            for mask, group in partitions.items():
                destination = bundle if mask == largest else group[0]
                if destination in self.members:
                    raise ValueError(f"Bundle name collision at {destination}")
                self.members[destination] = group
                self.previous[destination] = bundle
                self.location.update((member, destination) for member in group)

        @cache
        def expand(name):
            if name in self.owner or name not in original:
                return (name,)
            return tuple(dict.fromkeys(leaf for d in original[name].imports for leaf in expand(d)))

        self.replacements = {}
        self.imports = {}
        prior_edges = defaultdict(set)
        for destination, group in self.members.items():
            parent = self.previous[destination]
            replacements = defaultdict(list)
            for member in group:
                for dependency in original[member].imports:
                    for leaf in expand(dependency):
                        before = self.owner.get(leaf, leaf)
                        after = self.location.get(leaf, leaf)
                        if before == parent and after != destination:
                            raise ValueError(f"Dependent members in the original bundle {parent}")
                        if before != parent:
                            prior_edges[parent].add(before)
                        if after != destination and after not in replacements[before]:
                            replacements[before].append(after)
            self.replacements[destination] = replacements
            # Keep the submitted order for every dependency that stays in the import list.
            self.imports[destination] = [d for old in bundled[parent].imports for d in replacements[old]]
        for parent, source in bundled.items():
            if prior_edges[parent] != set(source.imports):
                raise ValueError(f"Wrapper expansion does not reproduce the submitted imports of {parent}")

        def relocated(mapping):
            masks = defaultdict(int)
            for provider, bit in bits.items():
                masks[mapping[provider]] |= bit
            return masks

        before = visibility(internal(bundled), relocated(self.owner))
        self.graph = {n: [d for d in deps if d in self.members] for n, deps in self.imports.items()}
        after = visibility(self.graph, relocated(self.location))
        self.drift_before = sum(before[prior] != original_mask[member] for member, prior in self.owner.items())
        if any(after[target] != original_mask[m] for m, target in self.location.items()):
            raise ValueError("The partition changed which original modules can reach a provider")

    def changed(self, n):
        parent = self.previous[n]
        old = self.bundled[parent]
        return n != parent or self.members[n] != (old.members or [parent]) or self.imports[n] != old.imports

    def render(self, n, raw):
        if not self.changed(n):
            return raw
        markers = list(MEMBER.finditer(raw))
        header = raw[:markers[0].start()] if markers else raw
        lines = []
        for line in header.splitlines(keepends=True):
            match = HEADER.fullmatch(line)
            if match:
                for dep in self.replacements[n][match[2]]:
                    lines.append(match[1] + dep + match[3])
            else:
                lines.append(line)
        if markers:
            keep = set(self.members[n])
            for j, marker in enumerate(markers):
                if marker[1] in keep:
                    end = markers[j + 1].start() if j + 1 < len(markers) else len(raw)
                    lines.append(raw[marker.start():end])
        return "".join(lines)

    def cone(self, targets):
        seen = set()
        pending = list(targets)
        while pending:
            current = pending.pop()
            if current not in seen:
                seen.add(current)
                pending.extend(self.graph[current])
        return seen


def write_outputs(plan, repo, ref, targets, patchfile, output):
    cone = plan.cone(targets) if output else set()
    changed = {n for n in plan.members if plan.changed(n)} if patchfile else set()
    pipe = subprocess.Popen(git(repo, "cat-file", "--batch"), stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for n in sorted(cone | changed):
            parent = plan.previous[n]
            pipe.stdin.write(f"{ref}:{path_of(parent)}\n".encode())
            pipe.stdin.flush()
            fields = pipe.stdout.readline().split()
            if len(fields) != 3 or fields[1] != b"blob":
                raise ValueError(f"Missing source {parent}")
            raw = pipe.stdout.read(int(fields[2])).decode()
            pipe.stdout.read(1)
            updated = plan.render(n, raw)
            if n in cone:
                path = output / path_of(n)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(updated)
            if n in changed:
                old = raw if n == parent else ""
                prior = "a/" + path_of(n) if n == parent else "/dev/null"
                patchfile.writelines(unified_diff(old.splitlines(True), updated.splitlines(True),
                                                  fromfile=prior, tofile="b/" + path_of(n)))
    finally:
        pipe.stdin.close()
        pipe.stdout.close()
        pipe.wait()


@contextmanager
def patch_output(path):
    # Publish the patch only after every source blob was read and rendered.
    tmp = tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False)
    try:
        with tmp:
            yield tmp
        os.replace(tmp.name, path)
    finally:
        Path(tmp.name).unlink(missing_ok=True)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", type=Path, default=Path("."))
    cli.add_argument("--base", required=True, help="revision before the wrapper and bundle passes")
    cli.add_argument("--consolidated", required=True, help="revision containing the submitted bundles")
    cli.add_argument("--provider", action="append", required=True, help="original module to protect")
    cli.add_argument("--patch", type=Path, help="write the complete source patch")
    cli.add_argument("--target", action="append", default=[], help="retained original module to inspect")
    cli.add_argument("--materialize", type=Path, help="write the source closure of the selected targets here")
    args = cli.parse_args()
    if args.materialize and not args.target:
        cli.error("--materialize requires --target")
    base, consolidated = (subprocess.check_output(
        git(args.repo, "rev-parse", "--verify", "--end-of-options", rev + "^{commit}"), text=True).strip()
        for rev in (args.base, args.consolidated))
    original = read_graph(args.repo, base)
    bundled = read_graph(args.repo, consolidated)
    plan = Partition(original, bundled, args.provider)
    print(f"Source modules: {len(bundled)} -> {len(plan.members)}")
    print(f"Provider reachability differences across {len(plan.location)} retained origins: {plan.drift_before} -> 0")
    print(f"New or changed source files: {sum(plan.changed(n) for n in plan.members)}")
    destinations = []
    for target in args.target:
        if target not in plan.location:
            cli.error(f"{target} is not a retained original module")
        destination = plan.location[target]
        destinations.append(destination)
        print(f"{target} -> {destination} ({len(plan.cone([destination]))} project modules)")
    if args.patch:
        with patch_output(args.patch) as patch:
            write_outputs(plan, args.repo, consolidated, destinations, patch, args.materialize)
    elif args.materialize:
        write_outputs(plan, args.repo, consolidated, destinations, None, args.materialize)


if __name__ == "__main__":
    main()
