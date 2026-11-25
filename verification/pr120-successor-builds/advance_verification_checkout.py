"""Move obsolete outputs aside and advance an idle, clean verification checkout."""
import argparse
import fcntl
from glob import escape
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lab", type=Path)
    parser.add_argument("project", type=Path)
    parser.add_argument("old")
    parser.add_argument("new")
    parser.add_argument("--from-run", type=Path)
    parser.add_argument("--to-run", type=Path)
    args = parser.parse_args()
    lab, project = args.lab.resolve(), args.project.resolve()
    old, new = args.old, args.new
    previous = (args.from_run or lab / "ready-1037-full").resolve(strict=True)
    out = (args.to_run or lab / "ready-1037-2164-full").resolve()
    if previous == out:
        raise ValueError("Use separate result directories for the two revisions.")
    out.mkdir(exist_ok=True)
    def git(*args):
        return subprocess.check_output(["git", "-C", project, *args], text=True).strip()
    def modules(rev):
        return {path[4:-5] for path in git("ls-tree", "-rz", "--name-only", rev, "--", "src").split("\0")
                if path.endswith(".lean")}
    with (previous / "restore.lock").open("r") as prior_lock, (out / "restore.lock").open("a") as next_lock:
        for lock in (prior_lock, next_lock):
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        records = [json.loads(f.read_bytes()) for f in previous.glob("*-restored.json")]
        if not records or any(row["merge"] != old for row in records):
            raise ValueError("The source lock belongs to another build.")
        head = git("rev-parse", "HEAD")
        if head not in (old, new) or git("status", "--porcelain"):
            raise ValueError("The old build checkout changed.")
        if head == new and (out / "checkout.json").is_file():
            receipt = json.loads((out / "checkout.json").read_bytes())
            if (receipt["old"], receipt["merge"]) != (old, new):
                raise ValueError("The result directory belongs to another transition.")
            return
        if git("diff", "--name-only", old, new, "--", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            raise ValueError("The Lean configuration or packages changed.")
        current = modules(new)
        retired = modules(old) - current
        build = project / ".lake/build"
        if build.resolve(strict=True) != build:
            raise ValueError("Use a private build directory.")
        saved = project / ".lake" / ("retired-" + old[:12] + "-modules")
        saved.mkdir(exist_ok=True)
        for name in sorted(retired):
            rel = Path(name)
            for folder in ("lib/lean", "ir"):
                parent = build / folder / rel.parent
                for item in parent.glob(escape(rel.name) + ".*"):
                    if not item.is_file() or item.is_symlink():
                        raise ValueError(str(item))
                    target = saved / item.relative_to(build)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    if target.exists():
                        raise ValueError(str(target))
                    item.rename(target)
        moved = sorted(str(item.relative_to(saved)) for item in saved.rglob("*") if item.is_file())
        lib = build / "lib/lean"
        retained = {f.relative_to(lib).with_suffix("").as_posix() for f in lib.rglob("*.olean")}
        if retained - current:
            raise ValueError(("Unexpected module outputs", sorted(retained - current)))
        if head != new:
            subprocess.run(["git", "-C", project, "switch", "--quiet", "--detach", new], check=True)
        if git("rev-parse", "HEAD") != new or git("status", "--porcelain"):
            raise ValueError("The new verification checkout differs from the requested revision.")
        receipt = dict(old=old, merge=new, head=git("rev-parse", "HEAD^2"), base=git("rev-parse", "HEAD^1"),
                       tree=git("rev-parse", "HEAD^{tree}"), prior_oleans_retained=len(retained),
                       deleted_source_paths=len(retired), archived_files=moved, directory=str(saved))
        partial = out / "checkout.tmp"
        partial.write_text(json.dumps(receipt, indent=2) + "\n")
        partial.replace(out / "checkout.json")
        print("Checked out", new, "with", len(retained), "existing module outputs and", len(moved), "retired files.")


if __name__ == "__main__":
    main()
