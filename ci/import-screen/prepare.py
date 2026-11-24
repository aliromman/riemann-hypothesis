"""Prepare content-addressed parent artifacts for the fork-only native screen."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import shutil

from lake_imports import import_levels
from panels import digest_roots, reused_roots, remaining_panels

PARENT = 'a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1'
SOURCE_TREE = '5da48cf36c47a7d87124fe72c0becbbb26a419d9'
DONOR = PARENT
MANIFEST = '7ef75c550561a6f21d27bb76c9a53fcf6a9a6fe5d5d481f2cdb56e9b1262589d'
GRAPH = 'e032f0efab1562e8ceb57acfca014adb55937b17c3b86ad84017a6ca701ef024'
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

def catalog():
    return json.loads((HERE/'catalog.json').read_bytes())

def groups(phase):
    if phase=='pilot':
        return ['pilot']
    all_groups=sorted(k for k in catalog() if k.startswith('current-'))
    early=set(next(k for k in all_groups if k.startswith(f'current-{bound}-')) for bound in (100,300,1000,100000))
    if phase=='latest-early':
        return [k for k in all_groups if k in early]
    if phase=='latest-tail':
        return [k for k in all_groups if k not in early]
    if phase=='latest':
        return all_groups
    raise ValueError('choose pilot, latest, latest-early, or latest-tail')

def root_lists(phase,graph):
    if phase=='pilot':
        return {'pilot': (HERE/'plans/pilot.txt').read_text().splitlines()}
    if phase.startswith('latest'):
        # Seed all native-check panels once, even for a partial matrix.
        return remaining_panels(graph,{'reused':reused_roots()})
    raise ValueError('invalid panel phase')

def scope(group, graph, candidates):
    rule=catalog()[group]
    if len(candidates)!=rule['count'] or digest_roots(candidates)!=rule['roots_sha']:
        raise ValueError(f'root list differs from reviewed panel {group}')
    if (not 1 <= len(candidates) <= 2500 or len(set(candidates)) != len(candidates)
            or any(n not in graph or not n.startswith('Development.') for n in candidates)):
        raise ValueError('invalid set of Development roots')
    ancestors = set(candidates)
    private = set()
    for name in candidates:
        levels = import_levels(name, graph)
        ancestors.update(levels)
        private.update(n for n,flags in levels.items() if flags & 1)
    ordered = sorted(ancestors)
    if len(ordered)!=rule['modules'] or digest_roots(ordered)!=rule['closure_sha']:
        raise ValueError(f'project import closure differs from reviewed panel {group}')
    return candidates, ordered, private

def seed(args, api, rows, shas):
    graph = graph_from_source(args.parent, rows)
    data = canonical(graph)
    if hashlib.sha256(data).hexdigest() != GRAPH:
        raise ValueError('source-derived project graph differs from the pinned inventory')
    (args.state/'metadata/headers.json').write_bytes(data)
    from reuse_gate import check
    check(args.parent,args.state,HERE,api,graph,rows,shas,source_path,canonical)
    needed = set()
    root_directory = args.state/'metadata/root-sets'
    root_directory.mkdir(exist_ok=True)
    for group, members in root_lists(args.group,graph).items():
        _, ancestors, _ = scope(group, graph, members)
        (root_directory/(group+'.txt')).write_text('\n'.join(members)+'\n')
        needed.update(ancestors)
    selected = [rows[n] for n in sorted(needed)]
    if args.dry_run:
        print('validated plans and parent index:', len(selected), flush=True)
        return
    # A cache from the prior revision may include superseded LTARs. Keep only
    # the content-addressed archives that the current source is about to use.
    current_archives={r[2] for r in selected}
    artifact_directory=args.state/'artifacts'
    if artifact_directory.exists():
        for existing in artifact_directory.iterdir():
            if existing.name.endswith('.ltar') and existing.name not in current_archives:
                existing.unlink()
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
    root_list=args.state/'metadata/root-sets'/(args.group+'.txt')
    roots, ancestors, private = scope(args.group, graph, root_list.read_text().splitlines())
    rule=catalog()[args.group]
    sparse = ['/scripts/','/lakefile.toml','/lake-manifest.json','/lean-toolchain']
    sparse += ['/'+str(source_path(name)) for name in ancestors]
    subprocess.run(['git','-C',str(args.parent),'sparse-checkout','set','--no-cone','--stdin'],
                   input='\n'.join(sparse)+'\n',text=True,check=True)
    build = args.parent/'.lake/build'
    if any((build/'lib/lean').rglob('*.olean')):
        raise ValueError('project outputs already exist before restoring the authenticated parent')
    chosen = [rows[n] for n in ancestors]
    # The fork cache is immutable. Reclaim sibling panels' files from this VM's copy.
    keep={archive for _,_,archive in chosen}
    for path in (args.state/'artifacts').iterdir():
        if path.name.endswith('.ltar') and path.name not in keep:
            path.unlink()
    # The two revisions share these exact archives. Their four public facets
    # give a measured lower bound. Check free space again at every batch.
    free=shutil.disk_usage(args.work.parent).free
    # Mathlib is already installed. Leave space for the compiler and temporary outputs.
    reserve=2 * (1 << 30)
    required=rule['shared_public_bytes']+reserve
    if free < required:
        raise OSError(f'runner disk limit for {args.group}: {free} free, {required} required')
    # Every worker verifies every cached archive that enters its own baseline.
    for _,_,archive in chosen:
        path = args.state/'artifacts'/archive
        if path.is_symlink() or not path.is_file():
            raise ValueError(f'unsafe or absent archive {archive}')
        with path.open('rb') as f:
            if hashlib.file_digest(f,'sha256').hexdigest() != shas[archive]:
                raise ValueError(f'archive SHA-256 differs: {archive}')
    jobs = api.unpack_jobs(args.parent, args.state, chosen)
    public_bytes=0
    for offset in range(0,len(jobs),32):
        if shutil.disk_usage(args.work.parent).free < reserve:
            raise OSError('less than the compiler reserve remains before leantar')
        batch = jobs[offset:offset+32]
        subprocess.run([args.leantar,'--jobs','2','-f','-x','-j','-'],input=json.dumps(batch),text=True,check=True)
        for name, _, _ in chosen[offset:offset+len(batch)]:
            path = Path(*name.split('.'))
            public = build/'lib/lean'/path
            public_bytes+=sum(public.with_suffix(s).stat().st_size for s in ('.olean','.olean.server','.ir.sig','.ir'))
            for suffix in ('.c','.bc'):
                (build/'ir'/path).with_suffix(suffix).unlink(missing_ok=True)
            for suffix in ('.trace','.ilean'):
                public.with_suffix(suffix).unlink(missing_ok=True)
            if name not in private:
                public.with_suffix('.olean.private').unlink(missing_ok=True)
    if public_bytes < rule['shared_public_bytes'] or shutil.disk_usage(args.work.parent).free < reserve:
        raise OSError('restored scope size or remaining space is outside the measured bounds')
    args.work.mkdir(parents=True,exist_ok=True)
    index = [[n,key,archive,shas[archive]] for n,key,archive in chosen]
    (args.work/'index.json').write_bytes(canonical(index))
    (args.work/'roots.txt').write_text('\n'.join(roots)+'\n')
    total = sum((args.state/'artifacts'/r[2]).stat().st_size for r in chosen)
    if total!=rule['archive_bytes']:
        raise ValueError('project archive bytes differ from authenticated inventory')
    receipt = dict(disk_free_before_unpack=free,disk_required_before_unpack=required,
                   measured_parent_public_bytes=public_bytes,shared_parent_public_bytes=rule['shared_public_bytes'],
                   shared_archives=rule['shared_archives'],disk_free_after_unpack=shutil.disk_usage(args.work).free,
                   parent=PARENT,tree=SOURCE_TREE,donor=DONOR,manifest=MANIFEST,graph=GRAPH,
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
