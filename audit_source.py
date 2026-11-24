"""Independently count and validate the source edits between two Git trees."""
import argparse
import collections
import difflib
import json
import re
import subprocess
import sys
from pathlib import Path

PRIVATE = re.compile(rb'import (Mathlib\.[\w.]+)\n')
IMPORT = re.compile(rb'(?:(?:public|private|meta) )*import ')

def tree(rev):
    out = subprocess.check_output(['git', 'ls-tree', '-rz', rev, '--', 'src/'])
    return {p:h.split()[2] for item in out.split(b'\x00') if item
            for h,p in [item.split(b'\t', 1)] if p.endswith(b'.lean')}

def header(body):
    lines = body.splitlines(keepends=True)
    i = 0
    for line in lines:
        if not (not line.strip() or line in (b'module\n', b'prelude\n') or IMPORT.match(line)):
            break
        i += 1
    return lines[:i], lines[i:]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('base')
    ap.add_argument('head')
    ap.add_argument('--targets', type=Path, required=True)
    ap.add_argument('--extra', type=Path, help='JSON of exact additional private imports per path')
    ap.add_argument('--unclump',action='store_true',help='also check member reconstruction with the repository clump script')
    opts = ap.parse_args()
    if opts.unclump:
        sys.path.insert(0,str(Path('scripts').resolve()))
        import clump
    allowed = set(opts.targets.read_text().splitlines())
    extra = json.loads(opts.extra.read_text()) if opts.extra else {}
    old, new = tree(opts.base), tree(opts.head)
    if old.keys() != new.keys():
        raise ValueError('project source modules differ')
    changed = {p for p in old if old[p]!=new[p]}
    outside = set(subprocess.check_output(['git','diff','--no-renames','--name-only','-z',opts.base,opts.head]).split(b'\x00')) - changed - {b''}
    if outside: raise ValueError(f'unexpected additional paths: {outside}')
    run = subprocess.Popen(['git', 'cat-file', '--batch'], stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def read(blob):
        run.stdin.write(blob+b'\n'); run.stdin.flush()
        oid, kind, length = run.stdout.readline().split()
        assert oid==blob and kind==b'blob'
        data = run.stdout.read(int(length))
        assert run.stdout.read(1)==b'\n'
        return data
    base_stats = collections.Counter()
    head_stats = collections.Counter()
    removed = collections.Counter()
    added = collections.Counter()
    counts = []
    clumps=members=0
    for path, before in old.items():
        a = read(before)
        lines = a.splitlines()
        n = sum(bool(line.strip()) for line in lines)
        base_stats.update(nonblank=n,lines=len(lines),bytes=len(a))
        if path not in changed: continue
        if not path.startswith(b'src/Development/'): raise ValueError(path)
        b = read(new[path])
        ha,ba = header(a); hb,bb = header(b)
        if ba != bb: raise ValueError(f'declaration body changed in {path!r}')
        if opts.unclump and clump.CLUMP_MARK.encode() in a:
            x=clump.unclump_text(a.decode()); y=clump.unclump_text(b.decode())
            if x!=y:raise ValueError(f'changed historical clump members in {path!r}')
            clumps+=1;members+=len(x)
        measures = [0,0]
        net_extra = set(extra.get(path.decode(), []))
        for op, k,l,i,j in difflib.SequenceMatcher(None,ha,hb,autojunk=False).get_opcodes():
            if op=='equal':continue
            for part, permitted, hist,index in ((ha[k:l],allowed,removed,0),(hb[i:j],net_extra,added,1)):
                for line in part:
                    match = PRIVATE.fullmatch(line)
                    if not match or match[1].decode() not in permitted: raise ValueError((path,line))
                    hist[match[1].decode()] += 1; measures[index] += 1
        nnew = sum(bool(line.strip()) for line in b.splitlines())
        head_stats.update(nonblank=nnew-n,lines=len(b.splitlines())-len(lines),bytes=len(b)-len(a))
        counts.append(measures)
    run.stdin.close();assert run.wait()==0
    total = {k:base_stats[k]+head_stats[k] for k in base_stats}
    if base_stats['nonblank']-total['nonblank'] != sum(removed.values())-sum(added.values()):raise ValueError('line counts disagree')
    print(json.dumps(dict(base=opts.base,head=opts.head,modules=len(old),changed=len(changed),
        parent=base_stats,candidate=total,clumps=clumps,clump_members=members,removed=sum(removed.values()),added=sum(added.values()),
        minimum=min((r for r,_ in counts),default=0),maximum=max((r for r,_ in counts),default=0),
        removed_by_import=removed,added_by_import=added),ensure_ascii=False,indent=2))

if __name__=='__main__':main()
