"""Time the repository's two clump readers and renderers on a fixed source panel."""
import argparse
import json
import statistics
import tempfile
import time
from collections import defaultdict
from pathlib import Path

from audit_source import GitBlobs, clumper


def measure(function, *args):
    start = time.perf_counter_ns()
    cpu = time.process_time_ns()
    result = function(*args)
    return result, (time.process_time_ns() - cpu) / 1e6, (time.perf_counter_ns() - start) / 1e6


def run(repo, base, head, panel, output, inputs=None):
    reader = GitBlobs(repo)
    observations = defaultdict(list)
    try:
        with tempfile.TemporaryDirectory() as scratch, output.open("w") as report:
            tools = [clumper(reader, commit, Path(scratch), "tool_" + str(i))
                     for i, commit in enumerate((base, head))]
            for index, path in enumerate(panel):
                source_refs = (inputs, inputs) if inputs else (base, head)
                texts = [reader.read(commit, path).decode() for commit in source_refs]
                members = []
                for tool, text in zip(tools, texts):
                    restored = tool.unclump_text(text)
                    members.append({n: tool.Module(n, "", s) for n, s in restored.items()})
                names = list(members[0])
                if names != list(members[1]):
                    raise ValueError("member order differs in " + path)
                for trial in range(6):
                    for side in ((0, 1) if (index + trial) % 2 == 0 else (1, 0)):
                        tool = tools[side]
                        restored, read_cpu, read_wall = measure(tool.unclump_text, texts[side])
                        rendered, write_cpu, write_wall = measure(tool.render, "", names, members[side])
                        if (list(restored) != names or rendered.partition(tool.CLUMP_MARK)[2] !=
                                texts[side].partition(tool.CLUMP_MARK)[2]):
                            raise ValueError("source regeneration failed for " + path)
                        values = (read_cpu, read_wall, write_cpu, write_wall)
                        print(json.dumps([path, trial, side, *values], separators=(",", ":")), file=report)
                        if trial:
                            for key, value in zip(("read_cpu", "read_wall", "render_cpu", "render_wall"), values):
                                observations[path, side, key].append(value)
    finally:
        reader.close()
    totals = {}
    for key in ("read_cpu", "read_wall", "render_cpu", "render_wall"):
        pairs = [(statistics.median(observations[p, 0, key]), statistics.median(observations[p, 1, key]))
                 for p in panel]
        totals[key] = dict(parent_ms=sum(a for a, b in pairs), candidate_ms=sum(b for a, b in pairs),
                           slower_sources=sum(b > a for a, b in pairs), count=len(pairs))
    return totals


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base")
    parser.add_argument("head")
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--panel", type=Path, default=Path("tool-panel.json"))
    parser.add_argument("--output", type=Path, default=Path("reproduced-timings.jsonl"))
    parser.add_argument("--same-inputs-from", help="Read both source files from this commit.")
    args = parser.parse_args()
    result = run(args.repo, args.base, args.head, json.loads(args.panel.read_text()), args.output, args.same_inputs_from)
    print(json.dumps(result, indent=2))
