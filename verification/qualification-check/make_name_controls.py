"""Write source controls using original compiler positions and a checked qualification diff."""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--original", required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--extra-public-import", action="append", default=[], metavar="MODULE",
                        help="add the same public import to all three source controls")
    args = parser.parse_args()
    cases = defaultdict(list)
    for row in map(json.loads, args.receipt.read_text().splitlines()):
        if row["status"] != "matches" or row["original_constants"] != [row["token"].removeprefix("_root_.")]:
            raise ValueError("the input requires a manual reference check")
        cases[row["member"]].append(row)
    for module, rows in sorted(cases.items()):
        rel = Path(*module.split(".")).with_suffix(".lean")
        source = subprocess.check_output(["git", "-C", args.repo, "show", f"{args.original}:src/{rel}"]).decode()
        order = sorted(rows, key=lambda r: (r["original_line"], r["original_utf16_column"]), reverse=True)
        for arm in ["original", "previous", "restored"]:
            lines = source.splitlines(keepends=True)
            for row in order:
                line, col = row["original_line"] - 1, row["original_utf16_column"]
                start = len(lines[line].encode("utf-16-le")[:2*col].decode("utf-16-le"))
                token = row["original_token"]
                if lines[line][start:start + len(token)] != token:
                    raise ValueError(f"source position does not match in {module} at line {line + 1}")
                if arm != "original":
                    selected = row["previous"] if arm == "previous" else row["token"]
                    lines[line] = lines[line][:start] + selected + lines[line][start + len(token):]
            if args.extra_public_import:
                imports = [i for i, text in enumerate(lines) if re.match(r"^\s*(?:public\s+)?import ", text)]
                if not imports:
                    raise ValueError(f"no import header in {module}")
                insert_at = imports[-1] + 1
                lines[insert_at:insert_at] = [f"public import {name}\n" for name in args.extra_public_import]
            dest = args.output / arm / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            data = "".join(lines).encode()
            dest.write_bytes(data)
            print(json.dumps(dict(module=module, arm=arm, sha256=hashlib.sha256(data).hexdigest())))


if __name__ == "__main__":
    main()
