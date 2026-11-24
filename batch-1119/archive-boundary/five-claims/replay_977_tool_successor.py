"""Replay the archived #977 proofs after the two-file clump tool update."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import zipfile


ORIGINAL = "989ea9c41e8400a6fe894fe365298c219f8c7e1d"
HEAD = "be239239d08c7bf865ba618cf6515891b4596c84"
ARCHIVE = "44b1fe937af35e7b100e4f7d28972f349eb3d81560a78bb532c374e1c9b41de0"
HELPER = "fb69b0939d762b6766f61b3df58458456cea570cdbd344ed4284badc792481ae"
INPUTS = "7ff42467a3284016ed34d8cd01774d3fa54f91b64eddb3a8d45f823b53f9fbe5"
PROVIDERS = ("ClaimStrip", "MainConclusion")
PACKAGE = "Development.AutomorphicArithmetic.CharacterBoxes"


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def replay(args):
    def git(*command):
        return subprocess.check_output(["git", "-C", args.checkout, *command])

    require(git("rev-parse", HEAD + "^").decode().strip() == ORIGINAL, "different original commit")
    require(git("rev-parse", ORIGINAL + ":src") == git("rev-parse", HEAD + ":src"), "different Lean sources")
    changes = git("diff", "--no-renames", "--name-status", ORIGINAL, HEAD).decode().splitlines()
    require(changes == ["M\tscripts/clump.py", "M\tscripts/tests/test_clump_scopes.py"], "different Git changes")
    targets = json.loads(git("show", HEAD + ":comparator.json"))["theorem_names"]
    require(len(targets) == 5, "different number of targets")
    version = subprocess.check_output(["lean", "--version"], text=True)
    require("0b77e12952ad39077d80d8bd6b66d601f225c321" in version, "different Lean compiler")
    require(sha(args.zip) == ARCHIVE and sha(args.helper) == HELPER, "different proof archive or helper")

    with tempfile.TemporaryDirectory() as temp, zipfile.ZipFile(args.zip) as z:
        work = Path(temp)
        setup = json.loads(gzip.decompress(z.read("rh-root/roots/providers/main-setup.json.gz")))
        imports = setup["importArts"]
        selected = {row.split("\t")[0] for row in z.read("rh-root/images/images.tsv").decode().splitlines()}
        require(len(selected) == 11575 and len(imports) == 59296, "different project input counts")
        outputs = {}
        for short in ("Main", *PROVIDERS):
            name = "Main" if short == "Main" else PACKAGE + "." + short
            location = "rh-root/roots/Main" if short == "Main" else (
                "rh-root/roots/providers/" + short + "/" + name.replace(".", "/"))
            for ext in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"):
                (work / (short + ext)).write_bytes(z.read(location + ext))
            outputs[name] = work / (short + ".olean")

        digest = hashlib.sha256()
        for name in sorted(imports):
            actual = imports[name]
            require(len(actual) == 2 and len(actual[0]) == 1 and actual[1] == [], "unexpected import shape")
            path = outputs.get(name, args.lib.joinpath(*name.split(".")).with_suffix(".olean"))
            role = "candidate" if name in selected else "parent"
            digest.update((name + "\t" + role + "\t" + sha(path) + "\n").encode())
            imports[name] = [[str(path.resolve())], []]
        require(digest.hexdigest() == INPUTS, "different compiled project inputs")
        setup_file = work / "setup.json"
        setup_file.write_text(json.dumps(setup))
        cmd = ["lean", "-j1", "--tstack=400000", "--run", args.helper.resolve(), outputs["Main"], setup_file, *targets]
        output = subprocess.check_output(cmd, text=True)
        accepted = [line[16:] for line in output.splitlines() if line.startswith("kernel accepted ")]
        require(accepted == targets, "the kernel did not accept the five target proofs")
        require("negative control: while replaying declaration 'riemannHypothesis'" in output and
                "declaration type mismatch" in output, "the wrong-proof control failed")
        print(output, end="")


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("checkout", type=Path, help="Git checkout with both reviewed commits")
    p.add_argument("zip", type=Path, help="original proof ZIP from GitHub Actions run 45421761727")
    p.add_argument("lib", type=Path, help="batch 1119 compiled project library")
    p.add_argument("helper", type=Path, help="ReplayMain.lean from the original root workflow")
    replay(p.parse_args())
