"""Ask the original Lean kernel to check conversions that need elaboration."""

import json
import subprocess
from pathlib import Path


def check_conversions(before, overlay, candidates, output):
    if not candidates:
        return set()
    directory = output / 'conversions'
    directory.mkdir()
    overrides = {}
    if overlay is not None:
        for trace in overlay.rglob('*.trace'):
            module = '.'.join(trace.relative_to(overlay).with_suffix('').parts)
            stem = str(trace.with_suffix(''))
            parts = (('.olean', '.olean.server', '.olean.private'), ('.ir.sig', '.ir'))
            overrides[module] = [[stem + s for s in group if Path(stem + s).is_file()] for group in parts]
    accepted = set()

    def check(group, label):
        name = 'ConsolidationWitness' + label
        file = directory / (name + '.lean')
        modules = sorted({row['module'] for row in group})
        commands = ['module', *['import ' + module for module in modules], '', 'namespace ' + name]
        for i, row in enumerate(group):
            commands.append(f"theorem witness{i} : @_root_.{row['name']} = @_root_.{row['target']} := rfl")
        commands.append('end ' + name)
        file.write_text('\n'.join(commands) + '\n')
        setup = file.with_suffix('.setup.json')
        setup.write_text(json.dumps({'name': name, 'isModule': True, 'importArts': overrides,
                                     'dynlibs': [], 'plugins': [], 'options': {}}))
        with file.with_suffix('.log').open('w') as log:
            result = subprocess.run(['lake', 'env', 'lean', '-j1', '--setup=' + str(setup),
                                     '--root=' + str(directory), '-o', str(file.with_suffix('.olean')), str(file)],
                                    cwd=before, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode == 0:
            accepted.update(row['name'] for row in group)
        elif len(group) > 1:
            middle = len(group) // 2
            check(group[:middle], label + 'L')
            check(group[middle:], label + 'R')

    for i in range(0, len(candidates), 6):
        check(candidates[i:i + 6], str(i))
    return accepted
