"""Read a fixed Git tree's module headers with the pinned Lean dependency parser."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


def git(repo, *args):
    return subprocess.check_output(["git", "-C", repo, *args])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path)
    ap.add_argument("--lean", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("ref")
    args = ap.parse_args()
    rev = git(args.repo, "rev-parse", "--verify", args.ref + "^{commit}").decode().strip()
    pin = git(args.repo, "show", rev + ":lean-toolchain").decode().strip().split(":")[-1].removeprefix("v")
    version = subprocess.check_output([args.lean, "--version"], text=True)
    if not re.search(r"version " + re.escape(pin) + r"[, )]", version):
        raise SystemExit("Lean version differs from the Git toolchain pin")
    inputs = {}
    for record in git(args.repo, "ls-tree", "-rz", rev, "--", "src").split(b"\0"):
        if not record.endswith(b".lean"):
            continue
        meta, name = record.split(b"\t", 1)
        inputs[name.decode()] = meta.split()[2]
    paths = sorted(inputs)
    with tempfile.TemporaryDirectory() as d, subprocess.Popen(
            ["git", "-C", args.repo, "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE) as cat:
        with args.out.with_suffix(".partial").open("w") as dest:
            dest.write(json.dumps({"revision": rev, "toolchain": pin, "src": git(args.repo, "rev-parse", rev + ":src").decode().strip()}) + "\n")
            for offset in range(0, len(paths), 256):
                batch = paths[offset:offset + 256]
                temps = []
                for i, path in enumerate(batch):
                    cat.stdin.write(inputs[path] + b"\n")
                    cat.stdin.flush()
                    oid, kind, count = cat.stdout.readline().split()
                    data = cat.stdout.read(int(count))
                    if (cat.stdout.read(1) != b"\n" or kind != b"blob" or oid != inputs[path] or
                            hashlib.sha1(b"blob " + count + b"\0" + data).hexdigest().encode() != oid):
                        raise ValueError("invalid source blob for " + path)
                    temp = Path(d, f"{i}.lean")
                    temp.write_bytes(data)
                    temps.append(str(temp))
                result = json.loads(subprocess.check_output([args.lean, "--deps-json", *temps]))
                records = result["imports"]
                if len(batch) != len(records):
                    raise ValueError("dependency parser returned the wrong number of headers")
                for path, item in zip(batch, records):
                    if item["errors"] or "result" not in item:
                        raise ValueError((path, item))
                    header = item["result"]
                    imports = [[v["module"], v["isExported"], v["isMeta"], v["importAll"]] for v in header["imports"]]
                    dest.write(json.dumps([path, inputs[path].decode(), header["isModule"], imports], ensure_ascii=False, separators=(",", ":")) + "\n")
                if offset % 8192 == 0:
                    print(offset, "of", len(paths), file=sys.stderr, flush=True)
        cat.stdin.close()
        if cat.wait() != 0:
            raise ValueError("git cat-file failed")
    args.out.with_suffix(".partial").replace(args.out)
    print("verified", rev, len(paths), file=sys.stderr)


if __name__ == "__main__":
    main()
