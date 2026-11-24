"""Partition the remaining Development roots by reachable project cone size."""
from __future__ import annotations
from functools import lru_cache
from graphlib import TopologicalSorter
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
# The final panel shares a single whole-project restore between the deepest roots.
BANDS = ((300, 1100), (1000, 950), (3000, 650), (10000, 375), (100000, 10000))

def digest_roots(names):
    return hashlib.sha256(('\n'.join(names)+'\n').encode()).hexdigest()

def first_panels():
    return {f.stem:f.read_text().splitlines() for f in sorted((HERE/'plans').glob('group-*.txt'))}

def remaining_panels(graph, first):
    ordered=list(TopologicalSorter({m: [n for n,*_ in edges] for m,edges in graph.items()}).static_order())
    ids={m:i for i,m in enumerate(ordered)}

    @lru_cache(maxsize=None)
    def cone(name, flags):
        found=1<<ids[name]
        for child,public,meta,all_ in graph[name]:
            reachable=bool(flags & 1) or public
            child_meta=bool(flags & 2) or (reachable and meta)
            if reachable or child_meta:
                child_flags=int(bool(flags & 1) and all_) | (int(child_meta)<<1)
                found |= cone(child,child_flags)
        return found

    previous={m for panel in first.values() for m in panel}
    if len(previous)!=sum(map(len,first.values())):
        raise ValueError('overlapping first-wave roots')
    buckets={bound:[] for bound,_ in BANDS}
    for module in sorted(n for n in graph if n.startswith('Development.')):
        if module in previous:
            continue
        bits=1<<ids[module]
        for name,_public,meta,all_ in graph[module]:
            bits |= cone(name,int(all_) | (int(meta)<<1))
        count=bits.bit_count()
        for bound,_ in BANDS:
            if count<=bound:
                buckets[bound].append((module,count))
                break
        else:
            raise ValueError('unclassified dependency closure')
    panels={}
    for bound,size in BANDS:
        members=buckets[bound]
        if bound==BANDS[-1][0]:
            members.sort(key=lambda pair:(pair[1],pair[0]))
        for index in range(0,len(members),size):
            key=f'rest-{bound}-{index//size:02d}'
            panels[key]=[n for n,_ in members[index:index+size]]
    cone.cache_clear()
    if set(previous).intersection(m for group in panels.values() for m in group):
        raise ValueError('first and remaining panels intersect')
    if set(previous).union(m for g in panels.values() for m in g)!={m for m in graph if m.startswith('Development.')}:
        raise ValueError('incomplete Development partition')
    return panels
