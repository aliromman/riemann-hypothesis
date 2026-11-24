"""Check the actual structural PR with its normal clump reader, writer and focused tests."""
import argparse
import json
import re
from pathlib import Path
import subprocess
import sys
from manifest import read_request, sha
from native import Blobs, file_sha, git, ls

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'import-screen'))
from prepare import load, source_path
from structural_gate import TEST_FILE, header, tooling

RECIPE = {'context_fusion.py': '322c0ac892bff0bdf808f1ca5b5ee7376bb3d3ee6cef17ab289311ac21fe04ab',
          'compact_scope.py': '9e0f5633f64a44157bc837790d3b21b58c0f098211c00c1590b9a9ea318e7d70'}


def member_sources(parts, fuse, drop_blank):
    lines = parts.body.removesuffix('\n').split('\n')
    fused, count = fuse(lines)
    def source(body):
        return parts.header + '\n'.join(body) + ('\n' if parts.body.endswith('\n') else '')
    standard = source(fused)
    if not drop_blank:
        return standard, standard
    if not count:
        raise ValueError('the named member has no verified noncomputable section fusion')
    pos = lines.index('noncomputable section')
    if pos == 0 or pos + 1 >= len(lines) or lines[pos-1] != '' or lines[pos+1] != '' or fused[pos-1:pos+1] != ['', '']:
        raise ValueError('the fused source command does not have empty lines on both sides')
    return standard, source(fused[:pos-1] + fused[pos:])


def rendered_counts(text):
    lines = text.splitlines()
    code = sum(bool(line.strip()) and not line.lstrip().startswith('--') for line in lines)
    return code, sum(line.startswith('open ') for line in lines)


def check_clump(name, a, b, refinement, prior, proposal, fuse, candidate):
    changed_members = original_bytes = gain = open_gain = 0
    header(a, b)
    original = prior.unclump_text(a.decode())
    restored = proposal.unclump_text(b.decode())
    if original.keys() != restored.keys() or list(original) != list(restored) or not original:
        raise ValueError('the normal unclumper changed member names or order: ' + name)
    modules = {}
    baseline_modules = {}
    cleaned = set(refinement['members']) if refinement is not None else set()
    if refinement is not None and (not cleaned or len(cleaned) != len(refinement['members']) or not cleaned <= original.keys()):
        raise ValueError('the refinement does not list distinct original members: ' + name)
    for n, text in original.items():
        parts = prior.Module(n, '', text)
        standard, expected = member_sources(parts, fuse, n in cleaned)
        if restored[n] != expected:
            raise ValueError('restored member has a change outside the indicated section fusion: ' + n)
        modules[n] = proposal.Module(n, '', restored[n])
        if refinement is not None:
            baseline_modules[n] = proposal.Module(n, '', standard)
        changed_members += int(text != expected)
        original_bytes += len(text.encode())
    mark = proposal.CLUMP_MARK
    rendered = proposal.render(str(candidate), list(original), modules)
    if rendered.partition(mark)[2] != b.decode().partition(mark)[2]:
        raise ValueError('the normal clump renderer does not recreate the exact selected body: ' + name)
    if refinement is not None:
        earlier = proposal.render(str(candidate), list(original), baseline_modules)
        old_code, old_opens = rendered_counts(earlier)
        new_code, new_opens = rendered_counts(rendered)
        gain = old_code - new_code
        open_gain = old_opens - new_opens
        if gain <= 0 or gain != refinement['saved_commands']:
            raise ValueError('the refined source does not realize its measured command savings: ' + name)
        if open_gain <= 0:
            raise ValueError('the refined source must reduce physical namespace open commands: ' + name)
    return {'members': len(original), 'changed_members': changed_members, 'original_bytes': original_bytes,
            'blanks': len(cleaned), 'commands': gain, 'opens': open_gain}


def check(req, inputs, parent, candidate, recipe):
    from verified_batch import BATCHES
    if req.get('source_mode') != 'clump-scopes':
        raise ValueError('unrecognized structural root request')
    base, head = req['base'], req['head']
    if (git(parent, 'rev-parse', 'HEAD').decode().strip(), git(candidate, 'rev-parse', 'HEAD').decode().strip()) != (base, head):
        raise ValueError('the clump tools have a different Git parent or candidate')
    extra = set(req['tooling'])
    if tooling(candidate, base, head, extra) != req['tooling']:
        raise ValueError('incorrect committed normal tool')
    for p in extra:
        left, right = req['tooling'][p]
        if (left is not None and file_sha(parent / p) != left['sha256']) or file_sha(candidate / p) != right['sha256']:
            raise ValueError('the normal clump tool differs from the Git file')
    for name, digest in RECIPE.items():
        if file_sha(recipe / name) != digest:
            raise ValueError('the reference source-level section fusion changed')
    sys.path.insert(0, str(recipe))
    fuse = load(recipe / 'context_fusion.py', 'reference_fusion').fuse
    prior = load(parent / 'scripts/clump.py', 'preceding_clumper')
    proposal = load(candidate / 'scripts/clump.py', 'proposed_clumper')
    old, new = ls(candidate, base), ls(candidate, head)
    reader = Blobs(candidate)
    members = changed_members = original_bytes = 0
    planner_modules = protected_modules = 0
    refinements = req.get('fusion_refinements', {})
    if not refinements.keys() <= inputs.keys():
        raise ValueError('the source refinement names an unselected file')
    removed_blank_lines = extra_commands = extra_opens = 0
    dispositions = {}
    try:
        if req['base_src'] == '6e972745429bd501b15e5daa9db46c8a9feb85db':
            from structural_choices import check as check_choices
            dispositions = check_choices(req, inputs, candidate, old, new, reader, prior, proposal, fuse, check_clump)
        elif req['base_src'] in BATCHES:
            batch = BATCHES[req['base_src']]
            from structural_choices import changed
            previous_head = batch['history']['977']['head']
            earlier_parent, earlier = ls(candidate, batch['previous_base']), ls(candidate, previous_head)
            existing = changed(earlier_parent, earlier)
            selected_now = changed(old, new)
            named = {str(source_path(n)) for n in inputs}
            declared = req['structural_dispositions']
            withdrawn = {str(source_path(n)) for n in declared['withdrawn']}
            if (declared['initial_head'] != previous_head or len(existing) != batch['history']['977']['count'] or
                    named != selected_now or not named <= existing or len(withdrawn) != len(declared['withdrawn']) or
                    existing - named != withdrawn or any(new.get(p) != old.get(p) for p in withdrawn)):
                raise ValueError('the latest selected and withdrawn clumps differ from the preceding verified PR')
            modified = sum(earlier_parent[p] != old[p] for p in named)
            if any(earlier_parent[p] == old[p] and earlier[p] != new[p] for p in named):
                raise ValueError('a retained clump changed despite identical upstream source')
            dispositions = {'preceding_verified':len(existing), 'current_withdrawals':len(withdrawn),
                            'updated_upstream_originals': modified, 'selected': len(named)}
        selected = {str(source_path(n)) for n in inputs}
        if old.keys() != new.keys():
            raise ValueError('the planning domain changed')
        for path in sorted(old):
            if not path.endswith('.lean'):
                continue
            name = path[4:-5].replace('/', '.')
            original = reader.read(old[path]).decode()
            proposed = original if old[path] == new[path] else reader.read(new[path]).decode()
            before = prior.is_clump_file(prior.Module(name, path, original))
            after = proposal.is_clump_file(proposal.Module(name, path, proposed))
            if before != after or (path in selected and not after):
                raise ValueError('the normal planner changed clump protection: ' + name)
            planner_modules += 1
            protected_modules += int(after)
        for name, row in sorted(inputs.items()):
            path = str(source_path(name))
            a, b = reader.read(old[path]), reader.read(new[path])
            if (sha(a), sha(b)) != (row['parent_source'], row['head_source']):
                raise ValueError('round-trip source hashes differ: ' + name)
            values = check_clump(name, a, b, refinements.get(name), prior, proposal, fuse, candidate)
            members += values['members']
            changed_members += values['changed_members']
            original_bytes += values['original_bytes']
            removed_blank_lines += values['blanks']
            extra_commands += values['commands']
            extra_opens += values['opens']
    finally:
        reader.close()
    test_path, = (p for p in req['tooling'] if Path(p).name == TEST_FILE)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', str((candidate / test_path).parent),
                            '-p', TEST_FILE], capture_output=True, text=True, check=True)
    test_summary = tests.stderr + tests.stdout
    if not re.search(r'^Ran [1-9][0-9]* tests? in ', test_summary, re.MULTILINE):
        raise ValueError('the proposed focused clump tests did not run')
    return {'parent': base, 'head': head, 'source_tree': req['head_src'], 'source_files': len(inputs),
            'source_dispositions': dispositions,
            'members': members, 'member_bodies_with_verified_scope_fusion': changed_members,
            'planner_modules_compared': planner_modules, 'planner_modules_protected': protected_modules,
            'fused_adjacent_empty_lines_removed': removed_blank_lines, 'additional_command_lines_saved': extra_commands,
            'additional_open_lines_saved': extra_opens, 'refined_clumps': len(refinements),
            'bytes_in_original_member_sources': original_bytes, 'candidate_tools': req['tooling'],
            'focused_test_output': (tests.stdout + tests.stderr).strip()}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for key in ('request', 'parent', 'candidate', 'out'):
        p.add_argument('--' + key, type=Path, required=True)
    p.add_argument('--recipe', type=Path, default=HERE.parent / 'structural-screen/recipe')
    args = p.parse_args()
    req, rows = read_request(args.request)
    record = check(req, rows, args.parent.resolve(), args.candidate.resolve(), args.recipe.resolve())
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record))
