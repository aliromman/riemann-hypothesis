"""Bind each final structural candidate, withdrawal and fallback to the actual Git revisions."""
from native import git, ls
from prepare import source_path

SEED = '253ce10d540880848ae81503fc1aa9654c5d1109'
BEFORE_BATCH = '1ae1f79ed3f27986e4493a1c8fb6e21455d7467a'
EARLIER_PARENT = '9893104138b909cddb3dea39fb23d62d8f83141a'
FIRST_VARIANT = 'bde5d32d9681e0e3b30295b53d7bdb45b6cf463a'


def changed(original, proposed):
    return {p for p in original.keys() & proposed.keys() if p.endswith('.lean') and original[p] != proposed[p]}


def check(req, inputs, candidate, original, final, reader, prior, proposal, fuse, compare):
    d = req['structural_dispositions']
    old = ls(candidate, EARLIER_PARENT)
    old_proposal = ls(candidate, BEFORE_BATCH)
    seed = ls(candidate, SEED)
    earlier = changed(old, old_proposal)
    coordinated = changed(original, seed)
    final_changes = changed(original, final)
    named = {str(source_path(n)) for n in inputs}
    if (d['initial_head'] != SEED or len(earlier) != 11582 or len(coordinated) != 11650 or
        len(coordinated - earlier) != 291 or len(earlier - coordinated) != 223 or named != final_changes or not named <= coordinated):
        raise ValueError('final changes differ from the authenticated coordinated #977 roster')
    for p in earlier - coordinated:
        if original[p] != final[p]:
            raise ValueError('a held or rejected historical clump differs from the latest upstream: ' + p)
    withdrawn = {str(source_path(n)) for n in d['withdrawn']}
    if len(withdrawn) != len(d['withdrawn']) or withdrawn != coordinated - named:
        raise ValueError('the declared structural withdrawals differ from the complete Git diff')
    for p in withdrawn:
        if final[p] != original[p]:
            raise ValueError('a withdrawn clump was not restored to its latest upstream source: ' + p)
    replaced = {p for p in named if final[p] != seed[p]}
    fallbacks = {str(source_path(n)) for n in d['fallback_v2']}
    if fallbacks != replaced or fallbacks & {str(source_path(n)) for n in req.get('fusion_refinements', {})}:
        raise ValueError('the declared v2 replacements differ from the final source')
    v2 = ls(candidate, FIRST_VARIANT) if fallbacks else {}
    for n, detail in d['fallback_v2'].items():
        p = str(source_path(n))
        a = reader.read(original[p])
        compare(n, a, reader.read(seed[p]), detail, prior, proposal, fuse, candidate)
        compare(n, a, reader.read(final[p]), None, prior, proposal, fuse, candidate)
        if p in earlier and old[p] == original[p] and final[p] != v2[p]:
            raise ValueError('the replacement differs from its previously published explicit v2 source: ' + n)
    return {'before_batch': len(earlier), 'coordinated': len(coordinated),
            'previously_released': len(coordinated - earlier), 'held_before_coordination': len(earlier - coordinated),
            'current_withdrawals': len(withdrawn), 'v2_fallbacks': len(fallbacks), 'selected': len(named)}
