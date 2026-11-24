"""Repeat the public interface and native kernel checks in two built checkouts."""
import json
from pathlib import Path
import subprocess
import sys


def obj(checkout, module):
    return (checkout / ".lake/build/lib/lean" / Path(*module.split("."))).with_suffix(".olean")


def main():
    tools = Path(__file__).resolve().parent
    before, after = (Path(p).resolve() for p in sys.argv[1:])
    for row in json.loads((tools / "interfaces.json").read_bytes()):
        inputs = [obj(before, row["before"]), *(obj(after, m) for m in row["after"])]
        raw = subprocess.check_output(["lean", "--run", tools / "Interface.lean", *inputs], text=True)
        if list(map(int, raw.split())) != row["counts"]:
            raise ValueError("The compiled public interface differs for " + row["before"])
    private = json.loads((tools / "private.json").read_bytes())
    inputs = [obj(before, private["old"]), *(obj(after, n) for n in private["pieces"])]
    raw = subprocess.check_output(["lean", "--run", tools / "PrivateRelocation.lean", *inputs], text=True)
    if list(map(int, raw.split())) != private["counts"]:
        raise ValueError("The private helpers differ.")
    print("All eleven interfaces and six relocated proof terms match.")


if __name__ == "__main__":
    main()
