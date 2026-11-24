"""Verify every project source in the requested import closure against its Git blob."""
import hashlib
import json
from pathlib import Path
import subprocess

def git(repo, *cmd):
    return subprocess.check_output(["git", "-C", repo, *cmd])

def project_closure(repo, project, revision, targets):
    entries = git(repo, "ls-tree", "-rz", revision, "--", "src", "lean-toolchain",
                  "lake-manifest.json", "lakefile.toml").split(b"\0")
    blobs = {}
    for entry in filter(None, entries):
        info, name = entry.split(b"\t", 1)
        blobs[name.decode()] = info.split()[2].decode()

    def verify(name):
        data = (project / name).read_bytes()
        header = f"blob {len(data)}\0".encode()
        if hashlib.sha1(header + data).hexdigest() != blobs[name]:
            raise ValueError("Source differs from the Git revision: " + name)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        verify(name)
    packages = json.loads((project / "lake-manifest.json").read_text())
    for pkg in packages["packages"]:
        checkout = project / packages["packagesDir"] / pkg["name"]
        if pkg["type"] != "git" or git(checkout, "rev-parse", "HEAD").decode().strip() != pkg["rev"]:
            raise ValueError("The installed dependency differs from the lock: " + pkg["name"])

    modules = {name[4:-5].replace("/", "."):name for name in blobs if name.startswith("src/") and name.endswith(".lean")}
    pending, checked = set(targets), set()
    while pending:
        names = sorted(pending)[:192]
        paths = [modules[n] for n in names]
        for path in paths:
            verify(path)
        response = json.loads(subprocess.check_output(["lean", "--deps-json", *paths], cwd=project))
        imports = response["imports"]
        if len(imports) != len(names):
            raise ValueError("Incomplete Lean header output")
        pending.difference_update(names)
        checked.update(names)
        for item in imports:
            if item["errors"]:
                raise ValueError(item["errors"])
            for imp in item["result"]["imports"]:
                dep = imp["module"]
                if dep in modules and dep not in checked:
                    pending.add(dep)
    return len(checked)
