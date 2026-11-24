"""Check the seven reported source lines against the original Lean editor records."""
import json
from pathlib import Path
import re
import subprocess
import sys

repo, compiled = map(Path, sys.argv[1:])
report = json.loads(Path(__file__).with_name("references.json").read_bytes())
name = re.compile(r"[\w'₀-₉]+(?:\.[\w'₀-₉]+)*")


def line_at(rev, path, line):
    raw = subprocess.check_output(["git", "-C", repo, "show", rev + ":src/" + path])
    return raw.decode().splitlines()[line - 1]


total = 0
for row in report["rows"]:
    old_path = Path(*row["original_module"].split("."))
    line = line_at(report["base"], old_path.with_suffix(".lean").as_posix(), row["original_line"])
    current = line_at(report["revision"], row["path"], row["line"])
    edit = json.loads((compiled / old_path).with_suffix(".ilean").read_bytes())
    if edit["module"].removeprefix("src.") != row["original_module"]:
        raise ValueError("The original module differs.")
    term = row["bindings"][0]["canonical"].split(".")[-1]
    old_tokens = [m for m in name.finditer(line) if m[0].split(".")[-1] == term]
    new_tokens = [m[0] for m in name.finditer(current) if m[0].split(".")[-1] == term]
    if len(old_tokens) != len(new_tokens) or len(new_tokens) != len(row["bindings"]):
        raise ValueError("The number of occurrences differs in " + row["path"])
    for old, new, bound in zip(old_tokens, new_tokens, row["bindings"]):
        start, stop = (len(line[:p].encode("utf-16-le")) // 2 for p in old.span())
        expected = [row["original_line"] - 1, start, row["original_line"] - 1, stop]
        observed = {info["n"] for key, record in edit["references"].items()
                    if (info := json.loads(key).get("c")) and any(use[:4] == expected for use in record["usages"])}
        if observed != {bound["canonical"]} or new.removeprefix("_root_.") != bound["canonical"]:
            raise ValueError("The reference differs in " + row["path"])
        total += 1
print(f"Checked {total} occurrences in {len(report['rows'])} current files.")
