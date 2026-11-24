"""Select reviewed groups without changing the identity of the shared archive set."""
def select(text, groups):
    items=text.split()
    if not items:raise ValueError('empty screen phase')
    if items[0]!='retry':
        if len(items)!=1:raise ValueError('expected one phase or an explicit retry group list')
        phase=items[0]
        return groups(phase),phase.split('-',1)[0],False
    ordered=items[1:]
    if not ordered or len(set(ordered))!=len(ordered) or not set(ordered)<=set(groups('latest')):
        raise ValueError('missing, duplicate, or unknown latest-parent retry group')
    return ordered,'latest',True
