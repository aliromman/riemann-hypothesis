"""Reapply a verified provider partition to a descendant and retain its current proof text."""
import argparse
from pathlib import Path
import hashlib
import json
import re
import subprocess

from partition_bundles import HEADER, MEMBER, PUBLIC, Source, Partition, internal, path_of, read_graph, visibility


def git(repo, *args):
    return subprocess.check_output(["git", "-C", repo, *args])


def chunks(name, text):
    markers = list(MEMBER.finditer(text))
    if not markers:
        return {name: "".join(s for s in text.splitlines(keepends=True) if not HEADER.fullmatch(s))}
    return {m[1]: text[m.start():(markers[i+1].start() if i+1<len(markers) else len(text))] for i,m in enumerate(markers)}


def parse_generated(lean, output, names):
    parsed = {}
    for i in range(0, len(names), 100):
        batch = names[i:i+100]
        raw = json.loads(subprocess.check_output([lean, "--deps-json", *(output/path_of(n) for n in batch)]))
        if len(raw["imports"]) != len(batch):
            raise ValueError("incorrect count from Lean's header parser")
        for name, data in zip(batch, raw["imports"]):
            if data["errors"]:
                raise ValueError((name, data["errors"]))
            parsed[name] = data["result"]
    return parsed


def native_sources(path, revision):
    with path.open() as stream:
        meta = json.loads(next(stream))
        if meta["revision"] != revision:
            raise ValueError("native source header manifest has a different revision")
        result = {}
        for path, _, _, imports in map(json.loads,stream):
            name = path[4:-5].replace("/",".")
            result[name] = source_of(imports)
    return result


def source_of(imports):
    item = Source()
    for name, exported, meta, all_data in imports:
        mode = int(exported) | (2*int(all_data)) | (4*int(meta))
        if name in item.imports:
            mode |= item.modes.get(name, PUBLIC)
        item.imports.append(name)
        if mode == PUBLIC:
            item.modes.pop(name,None)
        else:
            item.modes[name] = mode
    return item


def access(graph, provider):
    return visibility(internal(graph), {n:s.modes for n,s in graph.items()}, {provider:1})


def owners(graph):
    result = {}
    for name, source in graph.items():
        for member in source.members or [name]:
            if member in result:
                raise ValueError("more than one owner for " + member)
            result[member] = name
    return result


def corrected_attributes(text, instance_names):
    pattern = r"(?m)^[ \t]*attribute\s+\[-instance\](?:[ \t]*(?:\n[ \t]+)?(?:" + "|".join(re.escape(n) for n in sorted(instance_names)) + r"))+(?:[ \t]+in)?[ \t]*\n"
    return re.subn(pattern, "", text)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ("repo", "out", "lean", "original_headers", "head_headers"):
        ap.add_argument("--"+key.replace("_","-"), required=True, type=Path)
    for key in ("base","initial","head","provider"):
        ap.add_argument(key)
    ap.add_argument("--instance", action="append", default=[])
    args = ap.parse_args()
    refs = [git(args.repo,"rev-parse","--verify",r+"^{commit}").decode().strip() for r in (args.base,args.initial,args.head)]
    base, first, head = refs
    source, submitted, current = [read_graph(args.repo, r) for r in refs]
    split = Partition(source, submitted, [args.provider])
    now = owners(current)
    parents = {split.previous[n] for n in split.members if split.changed(n)}
    pieces = {split.previous[n] for n in split.members if n != split.previous[n]}
    new_names = set(split.members)-set(submitted)
    if new_names & current.keys():
        raise ValueError("a new split module already exists")
    for m in parents:
        if current[m] != submitted[m]:
            raise ValueError("the shared branch changed the imports or members of "+m)
    for m,s in current.items():
        earlier = set(submitted[m].imports) if m in submitted else set()
        if (set(s.imports)-earlier) & pieces:
            raise ValueError("a new edge to a split module needs a decision in "+m)
    old = {m:git(args.repo,"show",head+":"+path_of(m)).decode() for m in parents}
    generation = {m:split.render(m, old[split.previous[m]]) for m in split.members if split.changed(m)}
    before_bodies, after_bodies = {}, {}
    for name,txt in old.items():
        before_bodies.update(chunks(name,txt))
    for name,txt in generation.items():
        for member,body in chunks(name,txt).items():
            if member in after_bodies:
                raise ValueError("repeated body for "+member)
            after_bodies[member] = body
            now[member] = name
    if before_bodies != after_bodies:
        raise ValueError("the current proof text changed during partition")
    if args.out.exists() and any(args.out.iterdir()):
        raise ValueError("select an empty output directory")
    args.out.mkdir(parents=True,exist_ok=True)
    def save(name,txt):
        p=args.out/path_of(name)
        p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(txt.encode())
    for name,txt in generation.items():
        save(name,txt)
    original_graph = native_sources(args.original_headers,base)
    head_graph = native_sources(args.head_headers,head)
    old_locations = owners(current)
    before = access(head_graph,old_locations[args.provider])
    graph = dict(head_graph)
    for name, data in parse_generated(args.lean,args.out,sorted(generation)).items():
        graph[name] = source_of([(i["module"],i["isExported"],i["isMeta"],i["importAll"]) for i in data["imports"]])
    prefixes = {m.split(".")[0] for m in graph}
    for name,s in graph.items():
        missing = [dep for dep in s.imports if dep.split(".")[0] in prefixes and dep not in graph]
        if missing:
            raise ValueError((name,missing))
    baseline = access(original_graph,args.provider)
    after = access(graph,now[args.provider])
    common = set(now)&baseline.keys()
    before_counts = [sum(baseline[m][i]!=before[old_locations[m]][i] for m in common) for i in range(4)]
    after_counts = [sum(baseline[m][i]!=after[now[m]][i] for m in common) for i in range(4)]
    if any(after_counts):
        raise ValueError(("remaining provider visibility differences",after_counts))
    attribute_changes, explicit_uses = {}, {}
    if args.instance:
        names = [".".join(n.split(".")[-2:]) for n in args.instance]
        search = subprocess.run(["git","-C",args.repo,"grep","-I","-l","-z","-F",*(v for n in names for v in ("-e",n)),head,"--","src/*.lean"],capture_output=True)
        if search.returncode not in (0,1):
            raise RuntimeError(search.stderr)
        paths = {path.decode().split(":",1)[1][4:-5].replace("/",".") for path in search.stdout.split(b"\0") if path}
        for n in sorted(paths|generation.keys()):
            if after[n].available:
                continue
            text = generation[n] if n in generation else git(args.repo,"show",head+":"+path_of(n)).decode()
            newtext,count = corrected_attributes(text,args.instance)
            uses = [i for i,l in enumerate(newtext.splitlines(),1) if any(a in l for a in names)]
            if uses:
                explicit_uses[n] = uses
            if count:
                attribute_changes[n] = count
                generation[n] = newtext
                save(n,newtext)
    summary = dict(base=base,initial=first,head=head,provider=args.provider,compared_origins=len(common),
                   new_origins=sorted(set(now)-common),current_physical=len(current),output_physical=len(graph),
                   unchanged_current_member_bodies=len(before_bodies),split_input_files=len(pieces),
                   before_access=before_counts,after_access=after_counts,removed_attributes=attribute_changes,
                   explicit_uses_without_provider=explicit_uses,checked_native_headers=len(graph),
                   source_sha256={m:hashlib.sha256(v.encode()).hexdigest() for m,v in sorted(generation.items())})
    (args.out/"projection.json").write_text(json.dumps(summary,indent=2)+"\n")
    print("physical files",len(current),len(graph),"historical origins",len(common),"access",before_counts,after_counts,flush=True)
    print("current bodies preserved",len(before_bodies),"stale erasures removed",sum(attribute_changes.values()),"in",len(attribute_changes),"files",flush=True)
    print("explicit opposite-scope uses",explicit_uses,flush=True)


if __name__ == "__main__":
    main()
