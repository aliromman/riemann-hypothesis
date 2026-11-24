"""Prepare content-addressed parent artifacts for the fork-only native screen."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

from lake_imports import import_levels

PARENT = '362d9476fbd4548dead48ed7b6a54600879e1e17'
SOURCE_TREE = '40e3cf4d94bd95ec57949a01b570b2ece95e4ceb'
DONOR = 'f82babb107b166beffa76844bbc2c64c8296d247'
MANIFEST = 'db681d77faedbe9dd13afdd6e0a4076e63539302dba3ee98d48f6e072e103855'
GRAPH = 'ec04ddec7c43648872794bfb65663d7b57eb3797051b57d67516b6292b957326'
HERE = Path(__file__).resolve().parent
def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def pin(parent, api):
    if api.git(parent, 'rev-parse', 'HEAD') != PARENT:
        raise ValueError('community checkout differs from the source revision')
    ident = api.current_identity(parent)
    if ident['source_tree'] != SOURCE_TREE or ident['toolchain'] != 'leanprover/lean4:v4.37.0-rc1':
        raise ValueError('source or compiler pin mismatch')
    return ident

def metadata(api, identity, state, remote):
    meta = state/'metadata'
    meta.mkdir(parents=True, exist_ok=True)
    path = meta/'receipt.json'
    if remote:
        raw = api.fetch(f'ci/revisions/{DONOR}.json', api.MAX_RECEIPT)
        if raw is None:
            raise ValueError('missing published parent receipt')
        path.write_bytes(raw)
    record = api.matching_record(path.read_bytes(), identity)
    if not record or record['candidate_head'] != DONOR or record['module_manifest_sha256'] != MANIFEST:
        raise ValueError('published cache identity or manifest differs')
    def get(key, limit):
        file = meta/Path(key).name
        if remote:
            value = api.fetch(key, limit)
            if value is None:
                raise ValueError(f'missing cache metadata {key}')
            file.write_bytes(value)
        return file.read_bytes()
    _, shas, rows = api.validated_blobs(record, identity, fetcher=get)
    return {r[0]: r for r in rows}, shas

def stripped(line, depth):
    if not depth and '/-' not in line:
        return line.partition('--')[0].strip(), 0
    visible = []
    i = 0
    while i < len(line):
        if line.startswith('/-', i):
            depth += 1; i += 2
        elif depth and line.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif line.startswith('--', i):
            break
        else:
            visible.append(line[i]); i += 1
    return ''.join(visible).strip(), depth

def source_path(name):
    return Path('src').joinpath(*name.split('.')).with_suffix('.lean')

def graph_from_source(parent, rows):
    pattern = load(parent/'scripts/clump.py','screen_clump').IMPORT_RE
    graph = {}
    for name in rows:
        edges = []
        is_module = False
        depth = 0
        with (parent/source_path(name)).open() as source:
            for raw in source:
                line, depth = stripped(raw, depth)
                if not line or line == 'prelude':
                    continue
                if line == 'module':
                    is_module = True
                    continue
                match = pattern.fullmatch(line)
                if match is None:
                    break
                dependency = match[3].replace('«','').replace('»','')
                if dependency in rows:
                    flags = match[1].split()
                    edges.append([dependency, 'public' in flags or not is_module, 'meta' in flags, bool(match[2])])
        graph[name] = edges
    return graph

def groups(phase):
    if phase == 'pilot':
        return ['pilot']
    if phase == 'full':
        return sorted(p.stem for p in (HERE/'plans').glob('group-*.txt'))
    raise ValueError('phase must be pilot or full')

def scope(group, graph):
    candidates = (HERE/'plans'/(group+'.txt')).read_text().splitlines()
    if (not 1 <= len(candidates) <= 2500 or len(set(candidates)) != len(candidates)
            or any(n not in graph or not n.startswith('Development.') for n in candidates)):
        raise ValueError('invalid set of Development roots')
    ancestors = set(candidates)
    private = set()
    for name in candidates:
        levels = import_levels(name, graph)
        ancestors.update(levels)
        private.update(n for n,flags in levels.items() if flags & 1)
    if len(ancestors) > 8000:
        raise ValueError('group exceeds its bounded project scope')
    return candidates, sorted(ancestors), private

def seed(args, api, rows, shas):
    graph = graph_from_source(args.parent, rows)
    data = canonical(graph)
    if hashlib.sha256(data).hexdigest() != GRAPH:
        raise ValueError('source-derived project graph differs from the pinned inventory')
    (args.state/'metadata/headers.json').write_bytes(data)
    needed = set()
    for group in groups(args.group):
        _, ancestors, _ = scope(group, graph)
        needed.update(ancestors)
    selected = [rows[n] for n in sorted(needed)]
    if args.dry_run:
        print('validated plans and parent index:', len(selected), flush=True)
        return
    prepare = load(args.parent/'scripts/ci-prepare.py','screen_prepare')
    for offset in range(0,len(selected),32):
        batch = selected[offset:offset+32]
        # This retains upstream's SHA checks and caps concurrent public requests at 32.
        prepare.downloads(args.state, {key: artifact for _,key,artifact in batch}, shas)
    print('authenticated archives:', len(selected), flush=True)

def restore(args, api, rows, shas):
    raw = (args.state/'metadata/headers.json').read_bytes()
    if hashlib.sha256(raw).hexdigest() != GRAPH:
        raise ValueError('cached project graph mismatch')
    graph = json.loads(raw)
    roots, ancestors, private = scope(args.group, graph)
    sparse = ['/scripts/','/lakefile.toml','/lake-manifest.json','/lean-toolchain']
    sparse += ['/'+str(source_path(name)) for name in ancestors]
    subprocess.run(['git','-C',str(args.parent),'sparse-checkout','set','--no-cone','--stdin'],
                   input='\n'.join(sparse)+'\n',text=True,check=True)
    build = args.parent/'.lake/build'
    if build.exists():
        raise ValueError('expected empty project build directory')
    chosen = [rows[n] for n in ancestors]
    # Every worker verifies every cached archive that enters its own baseline.
    for _,_,archive in chosen:
        path = args.state/'artifacts'/archive
        if path.is_symlink() or not path.is_file():
            raise ValueError(f'unsafe or absent archive {archive}')
        with path.open('rb') as f:
            if hashlib.file_digest(f,'sha256').hexdigest() != shas[archive]:
                raise ValueError(f'archive SHA-256 differs: {archive}')
    jobs = api.unpack_jobs(args.parent, args.state, chosen)
    for offset in range(0,len(jobs),32):
        batch = jobs[offset:offset+32]
        subprocess.run([args.leantar,'--jobs','2','-f','-x','-j','-'],input=json.dumps(batch),text=True,check=True)
        for name, _, _ in chosen[offset:offset+len(batch)]:
            path = Path(*name.split('.'))
            public = build/'lib/lean'/path
            for suffix in ('.c','.bc'):
                (build/'ir'/path).with_suffix(suffix).unlink(missing_ok=True)
            for suffix in ('.trace','.ilean'):
                public.with_suffix(suffix).unlink(missing_ok=True)
            if name not in private:
                public.with_suffix('.olean.private').unlink(missing_ok=True)
    args.work.mkdir(parents=True,exist_ok=True)
    index = [[n,key,archive,shas[archive]] for n,key,archive in chosen]
    (args.work/'index.json').write_bytes(canonical(index))
    (args.work/'roots.txt').write_text('\n'.join(roots)+'\n')
    total = sum((args.state/'artifacts'/r[2]).stat().st_size for r in chosen)
    receipt = dict(parent=PARENT,tree=SOURCE_TREE,donor=DONOR,manifest=MANIFEST,graph=GRAPH,
                   group=args.group,roots=len(roots),archives=len(ancestors),archive_bytes=total,private_parents=len(private))
    (args.work/'scope.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt,flush=True)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('operation',choices=['seed','restore'])
    parser.add_argument('group')
    for flag in ('parent','state','work'):
        parser.add_argument('--'+flag,type=Path,required=True)
    parser.add_argument('--leantar')
    parser.add_argument('--dry-run',action='store_true')
    args=parser.parse_args()
    for flag in ('parent','state','work'):
        setattr(args,flag,getattr(args,flag).resolve())
    args.state.mkdir(parents=True,exist_ok=True)
    api=load(args.parent/'scripts/ci-cache-get.py','screen_cache')
    identity=pin(args.parent,api)
    rows,shas=metadata(api,identity,args.state,args.operation=='seed')
    if args.operation=='seed':
        seed(args,api,rows,shas)
    else:
        restore(args,api,rows,shas)

if __name__=='__main__':
    main()
