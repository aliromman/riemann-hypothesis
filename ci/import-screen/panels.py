"""Partition the remaining Development roots by reachable project cone size."""
from __future__ import annotations
from functools import lru_cache
from graphlib import TopologicalSorter
import hashlib
import csv
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
# The final panel shares a single whole-project restore between the deepest roots.
BANDS = ((30,1250),(100,1100),(300,1000),(1000,850),(3000,600),(10000,375),(100000,10000))

def digest_roots(names):
    return hashlib.sha256(('\n'.join(names)+'\n').encode()).hexdigest()

def reused_roots():
    raw=(HERE/'reuse.tsv').read_bytes()
    meta=json.loads((HERE/'reuse-meta.json').read_bytes())
    if hashlib.sha256(raw).hexdigest()!=meta['reuse_tsv_sha256'] or meta['new']['source_tree']!='5da48cf36c47a7d87124fe72c0becbbb26a419d9':
        raise ValueError('cross-revision reuse evidence does not match the source')
    names=[row['module'] for row in csv.DictReader(raw.decode().splitlines(),delimiter='\t')]
    if len(names)!=meta['modules'] or len(set(names))!=len(names):
        raise ValueError('invalid reuse membership')
    return names

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
            key=f'current-{bound}-{index//size:02d}'
            panels[key]=[n for n,_ in members[index:index+size]]
    cone.cache_clear()
    if set(previous).intersection(m for group in panels.values() for m in group):
        raise ValueError('first and remaining panels intersect')
    if set(previous).union(m for g in panels.values() for m in g)!={m for m in graph if m.startswith('Development.')}:
        raise ValueError('incomplete Development partition')
    return panels
