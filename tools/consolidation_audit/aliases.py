"""Find candidates in deleted modules. The Lean worker verifies each substitution."""

import json
import re
import subprocess
from pathlib import Path

THEOREM = re.compile(r"^\s*(?:theorem|lemma)\s+_root_\.([\w.']+)", re.M)
TARGET = re.compile(r"(?:first\s*\|\s*exact\s+|^\s*exact\s+|:=\s*)@?([\w.']+)\s*(?:\||\Z)", re.M)


def prepare(repo, old_files, deleted, read_original, output):
    command = ['git', '-C', repo, 'cat-file', '--batch']
    with subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE) as git:
        with (output / 'alias-pairs.jsonl').open('w') as queue, (output / 'unresolved-removals.jsonl').open('w') as unresolved:
            for module in sorted(deleted):
                blob = old_files[module][0]
                git.stdin.write(blob.encode() + b'\n')
                git.stdin.flush()
                key, kind, size = git.stdout.readline().split()
                source = git.stdout.read(int(size)).decode()
                if git.stdout.read(1) != b'\n' or key.decode() != blob or kind != b'blob':
                    raise ValueError('invalid Git batch response')
                try:
                    names, targets = THEOREM.findall(source), TARGET.findall(source)
                    if len(names) != 1 or len(targets) != 1:
                        raise ValueError('expected one theorem and one target candidate')
                    candidate = targets[0].removeprefix('_root_.')
                    wrapper = read_original(module)
                    artifact = Path(wrapper['path'])
                    trace = json.loads(artifact.with_suffix('.trace').read_bytes())
                    index = json.loads(artifact.with_suffix('.ilean').read_bytes())
                    owners = set()
                    for key in index['references']:
                        ref = json.loads(key).get('c', {})
                        name = ref.get('n', '')
                        if name == candidate or name.endswith('.' + candidate):
                            owners.add((name, ref['m']))
                    if len(owners) != 1:
                        raise ValueError(f'{len(owners)} compiler reference providers for {candidate}')
                    target, owner = owners.pop()
                    pair = {'wrapper': wrapper, 'name': names[0], 'provider': read_original(owner),
                            'targetName': target, 'indexHash': trace['outputs']['i'].split('.')[0]}
                    print(json.dumps(pair), file=queue)
                except (KeyError, OSError, ValueError) as error:
                    print(json.dumps({'module': module, 'reason': str(error)}), file=unresolved)
        git.stdin.close()
        if git.wait():
            raise ValueError('failed to read original Git blobs')
