"""Check the selected identifiers at the recorded source spans in Lean's editor data."""
import csv
import json
from pathlib import Path
import sys

checkout, table = map(Path, sys.argv[1:])
cache = {}
total = 0
with table.open() as stream:
    for row in csv.DictReader(stream, delimiter="\t"):
        module = row["module"]
        path = Path(*module.split("."))
        if module not in cache:
            source = (checkout / "src" / path).with_suffix(".lean").read_text().splitlines()
            obj = (checkout / ".lake/build/lib/lean" / path).with_suffix(".ilean")
            data = json.loads(obj.read_bytes())
            if data["module"].removeprefix("src.") != module:
                raise ValueError("Incorrect editor data for " + module)
            records = {}
            for key, item in data["references"].items():
                constant = json.loads(key).get("c")
                if constant:
                    for line, start, end_line, end, *_ in item["usages"]:
                        if line == end_line:
                            records.setdefault((line + 1, start, end), set()).add(constant["n"])
            cache[module] = source, records
        source, records = cache[module]
        line, col = int(row["line"]), int(row["column"])
        text, token = source[line - 1], row["token"]
        if text[col:col + len(token)] != token:
            raise ValueError("Source span differs at " + module)
        start, end = (len(text[:c].encode("utf-16-le")) // 2 for c in (col, col + len(token)))
        names = records.get((line, start, end), set())
        if names != set(row["compiled"].split("|")):
            raise ValueError(f"Compiler result differs at {module}:{line}: {names}")
        total += 1
print("Verified compiler selections:", total)
