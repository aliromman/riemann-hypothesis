"""Compute the project subset of Lean 4.37-rc1 Lake.fetchTransImportArts.

The graph stores (name, public, meta, all) import tuples. The root may be
a module (the default) or a legacy non-module. Package nodes can be omitted
when computing only project artifacts because no package imports the project.
"""
def import_levels(root, graph, *, nonmodule=False):
    # Bit 0 widens to all artifacts; bit 1 propagates meta reachability.
    direct = graph[root]
    stack = [(name, int(nonmodule or all_) | (int(meta) << 1))
             for name, _, meta, all_ in direct]
    levels = {}
    while stack:
        module, flags = stack.pop()
        prior = levels.get(module)
        if prior is not None:
            widened = prior | flags
            if widened == prior:
                continue
            flags = widened
        levels[module] = flags
        import_all = bool(flags & 1)
        needs_meta = bool(flags & 2)
        for child, exported, meta, all_ in graph.get(module, ()):
            reachable = import_all or exported
            child_meta = needs_meta or (reachable and meta)
            if reachable or child_meta:
                flags_child = int(nonmodule or (import_all and all_)) | (int(child_meta) << 1)
                stack.append((child, flags_child))
    return levels


def project_artifacts(root, graph, ordinary, *, nonmodule=False):
    levels = import_levels(root, graph, nonmodule=nonmodule)
    result = {}
    for module, level in levels.items():
        arts = ordinary[module]
        if level & 1:
            public, ir = arts
            result[module] = [public + [public[0] + '.private'], ir]
        else:
            result[module] = arts
    return result


def selftest():
    def e(n, public=False, meta=False, all_=False):
        return n, public, meta, all_

    g = {'R':[e('A')], 'A':[e('B',True), e('C')],
         'B':[e('D'),e('E',True)],'C':[e('K')]}
    assert import_levels('R',g) == {'A':0,'B':0,'E':0}
    assert import_levels('R',g,nonmodule=True) == {'A':1,'B':1,'C':1,'D':1,'E':1,'K':1}

    g['R'] = [e('A',meta=True)]
    assert import_levels('R',g) == {'A':2,'B':2,'C':2,'D':2,'E':2,'K':2}
    g['R'] = [e('A',all_=True)];g['A']=[e('B'),e('C',all_=True)]
    assert import_levels('R',g) == {'A':1,'B':0,'C':1,'E':0,'K':0}

    # The same node is reached through public, all, and meta paths. Both
    # promotions must reach its children, even if their discovery order changes.
    g={'R':[e('Ord'),e('All',all_=True),e('Meta',meta=True)],
       'Ord':[e('A',public=True)],'All':[e('A',all_=True)],'Meta':[e('A')],
       'A':[e('Priv'),e('PrivAll',all_=True)],'PrivAll':[e('L',all_=True)],
       'Priv':[e('M')]}
    expected={'A':3,'Priv':2,'PrivAll':3,'L':3,'M':2}
    for rev in (False,True):
        if rev:g['R'].reverse()
        out=import_levels('R',g)
        assert all(out[n]==v for n,v in expected.items()),out
    print('lake flag graph cases passed')


if __name__ == '__main__':
    selftest()
