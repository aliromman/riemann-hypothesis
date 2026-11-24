"""Run the pinned source Comparator on the four declared theorem targets."""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys


HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ["RUNNER_TEMP"]).resolve()
LOG = TEMP / "proof-logs"
PROJECT = TEMP / "proof-project"
GIT = TEMP / "proof-objects.git"
UPSTREAM = "https://github.com/leanprover-community/riemann-hypothesis.git"
KERNELS = {"Lean default", "Lean paranoid", "nanoda"}


def write(name, value):
    (LOG / name).write_text(json.dumps(value, indent=2) + "\n")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_of(module):
    return Path("src", *module.split(".")).with_suffix(".lean")


def git(*args):
    return subprocess.check_output(["git", "-C", GIT, *args])


def probe():
    cmd = ["bwrap", "--unshare-all", "--ro-bind", "/", "/", "--dev", "/dev",
           "--proc", "/proc", "--die-with-parent", "--new-session", "--", "/bin/true"]
    result = subprocess.run(cmd, capture_output=True, text=True)
    settings = [Path("/proc/sys/user/max_user_namespaces"), Path("/proc/sys/kernel/unprivileged_userns_clone"),
                Path("/proc/sys/kernel/apparmor_restrict_unprivileged_userns")]
    write("namespace.json", dict(command=cmd, uid=os.getuid(), system=platform.platform(),
          package=subprocess.check_output(["bwrap", "--version"], text=True).strip(),
          settings={str(p):p.read_text().strip() for p in settings if p.exists()},
          exit=result.returncode, stdout=result.stdout, stderr=result.stderr))
    result.check_returncode()


def sources(plan):
    PROJECT.mkdir()
    subprocess.run(["git", "init", "--quiet", "--bare", GIT], check=True)
    git("remote", "add", "origin", UPSTREAM)
    fork = "https://github.com/aliromman/riemann-hypothesis.git"
    git("remote", "add", "fork", fork)
    main = git("ls-remote", "--refs", "origin", "refs/heads/main").decode().split()[0]
    live = {"refs/heads/main": main}
    git("fetch", "--quiet", "--no-tags", "--depth=4", "--filter=blob:none", "origin", main, plan["parent"])
    def blob(rev, path):
        return git("show", f"{rev}:{path}")
    def tree(rev, path):
        return git("rev-parse", f"{rev}:{path}").decode().strip()
    base = plan["parent"]
    assert tree(base, "src") == tree(live["refs/heads/main"], "src") == plan["parent_src"]
    for f, sha in plan["config_blobs"].items():
        assert tree(base, f) == tree(live["refs/heads/main"], f) == sha
        (PROJECT / f).write_bytes(blob(base, f))
    bound = {}
    for number, entry in plan["pulls"].items():
        head = git("ls-remote", "--refs", "fork", entry["source_ref"]).decode().split()[0]
        assert head == entry["author"]
        merge = head
        git("fetch", "--quiet", "--no-tags", "--depth=8", "--filter=blob:none", "fork", head)
        git("merge-base", "--is-ancestor", base, head)
        assert tree(head, "src") == entry["src"]
        assert all(tree(head, f) == sha for f,sha in plan["config_blobs"].items())
        bound[number] = dict(author=head, public_fork_ref=entry["source_ref"],
                             checked_commit=head, comparison_base=base, candidate_src=entry["src"])
        for module, hashes in entry["source_sha256"].items():
            for side, rev in (("parent",base), ("candidate",merge)):
                path = file_of(module)
                data = blob(rev, str(path))
                assert digest(data) == hashes[side]
                dst = TEMP / "sources" / number / side / path
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(data)
    write("bound.json", dict(parent=base, current_main=live["refs/heads/main"], project=plan["parent_src"],
                              pulls=bound, pins=plan["config_blobs"], source_sha256={n:p["source_sha256"] for n,p in plan["pulls"].items()}))
    (LOG / "mathlib.txt").write_text("\n".join(plan["mathlib"]) + "\n")


def reset_sources(number, side):
    for path in (PROJECT / "src", PROJECT / ".lake/build", PROJECT / ".lake/cache"):
        if path.exists():
            shutil.rmtree(path)
    shutil.copytree(TEMP / "sources" / number / side / "src", PROJECT / "src")


def invoke(lake, project, entry, export, cfg, label, expected):
    config = LOG / (label + "-config.json")
    config.write_text(json.dumps(cfg, indent=2) + "\n")
    command = [lake, "comparator", "--config", config, "--challenge-from-export", export, "--json"]
    result = subprocess.run(command, cwd=project, capture_output=True, timeout=360)
    (LOG / (label + "-report.json")).write_bytes(result.stdout)
    (LOG / (label + "-stderr.txt")).write_bytes(result.stderr)
    verdict = json.loads(result.stdout)
    report = verdict["report"]
    assert verdict["sandboxed"] is True and set(report["kernel_reports"]) == KERNELS
    steps = {k:v["judgement"] for k,v in report.items() if k not in ("kernel_reports", "config")}
    kernels = {k:v["judgement"] for k,v in report["kernel_reports"].items()}
    assert all(steps[k] == "success" for k in ("resolve_dependencies", "build_solution", "export_solution"))
    assert all(steps[k] == "skipped" for k in ("build_challenge", "export_challenge"))
    assert (result.returncode == 0, verdict["judgement"], steps["compare_statements"], steps["check_axioms"], set(kernels.values())) == expected
    output = json.dumps(report["build_solution"]["output"], ensure_ascii=False)
    artifacts = {}
    for module in entry["project_closure"]:
        assert re.search(r"\bBuilt " + re.escape(module) + r"(?=[ \(]|$)", output), (module, output)
        dest = project / ".lake/build/lib/lean" / Path(*module.split("."))
        artifacts[module] = {ext:digest(dest.with_suffix(ext).read_bytes()) for ext in (".olean", ".ir.sig", ".ir")}
    if label == "control-axiom":
        assert "SandboxControl.extra" in str(report["check_axioms"]["output"])
    return dict(command=[str(x) for x in command], project_facets=artifacts, judgement=verdict["judgement"],
                steps=steps, kernels=kernels, sandboxed=True)


def trusted_export(lake, project, module, name, support, target):
    with target.open("wb") as out:
        subprocess.run([lake,"env","leanexport",module,"--",*support,name],cwd=project,stdout=out,check=True,timeout=180)


def compare(plan):
    assert LOG.joinpath("bound.json").is_file()
    lake = shutil.which("lake")
    lean = subprocess.check_output(["lean","--version"], text=True).strip()
    policy = json.loads((PROJECT/"comparator.json").read_bytes())
    assert set(policy["permitted_axioms"]) == {"Classical.choice","propext","Quot.sound"}
    assert set(policy["external_kernels"]) == KERNELS - {"Lean default"}
    support = [n for n in (PROJECT/"export-targets.txt").read_text().split() if n not in policy["theorem_names"]]
    positive = (True, "accepted", "success", "success", {"success"})
    manifest=json.loads((PROJECT/"lake-manifest.json").read_bytes())
    packages=PROJECT/".lake/packages"
    for row in manifest["packages"]:
        checkout=packages/row["name"]
        assert not checkout.is_symlink() and subprocess.check_output(["git","-C",checkout,"rev-parse","HEAD"],text=True).strip()==row["rev"]
    stats = dict(lean=lean,lake=lake,pulls={},controls={},errors=[])
    for number, entry in plan["pulls"].items():
        reset_sources(number, "parent")
        roots = [t["module"] for t in entry["theorems"]]
        parent_build = subprocess.run([lake, "--no-cache", "--fail-fast", "build", *["+"+n+":olean" for n in roots]],
                                      cwd=PROJECT, capture_output=True, timeout=360)
        (LOG/(number+"-parent-build.txt")).write_bytes(parent_build.stdout+parent_build.stderr)
        parent_build.check_returncode()
        exports={}
        for t in entry["theorems"]:
            dest=TEMP/(number+"-"+t["module"].split(".")[-1]+".jsonl")
            trusted_export(lake,PROJECT,t["module"],t["name"],support,dest)
            assert dest.stat().st_size==t["bytes"] and digest(dest.read_bytes())==t["sha256"]
            exports[t["name"]]=dest
        stats["pulls"][number]={}
        for t in entry["theorems"]:
            reset_sources(number,"candidate")
            cfg=dict(policy,challenge_module=t["module"],solution_module=t["module"],theorem_names=[t["name"]])
            label=number+"-"+t["module"].split(".")[-1]
            try:
                row=invoke(lake,PROJECT,t,exports[t["name"]],cfg,label,positive)
                stats["pulls"][number][t["name"]]=dict(parent_export_sha256=t["sha256"],parent_export_bytes=t["bytes"],**row)
            except Exception as ex:
                stats["errors"].append([label,repr(ex)])
            write("summary.json",stats)
    fixture=TEMP/"control-project";fixture.mkdir()
    (fixture/"lakefile.toml").write_text('name = "control"\n[[lean_lib]]\nname = "Control"\n')
    (fixture/"lean-toolchain").write_bytes((PROJECT/"lean-toolchain").read_bytes())
    header="module\n@[expose] public section\nnamespace SandboxControl\n"
    original="theorem value (n : Nat) : n + 0 = n := Nat.add_zero n"
    def control(body):
        (fixture/"Control.lean").write_text(header+body+"\nend SandboxControl\n")
    control(original);subprocess.run([lake,"build","Control"],cwd=fixture,check=True)
    name="SandboxControl.value";ref=TEMP/"control.jsonl"
    trusted_export(lake,fixture,"Control",name,support,ref)
    cfg=dict(policy,challenge_module="Control",solution_module="Control",theorem_names=[name])
    cases=[("alternate","theorem value (n : Nat) : n + 0 = n := by rfl",positive),
           ("statement","theorem value (n : Nat) : n * 1 = n := Nat.mul_one n",(False,"failure","failure","skipped",{"skipped"})),
           ("axiom","axiom extra (n : Nat) : n + 0 = n\ntheorem value (n : Nat) : n + 0 = n := extra n",(False,"failure","success","failure",{"skipped"}))]
    for label,body,expected in cases:
        shutil.rmtree(fixture/".lake/build");control(body)
        try:
            stats["controls"][label]=invoke(lake,fixture,{"project_closure":["Control"]},ref,cfg,"control-"+label,expected)
        except Exception as ex:
            stats["errors"].append([label,repr(ex)])
        write("summary.json",stats)
    if stats["errors"]:
        raise ValueError(stats["errors"])


if __name__ == "__main__":
    plan=json.loads((HERE/"plan.json").read_bytes())
    if sys.argv[1]=="probe":
        probe()
    elif sys.argv[1]=="sources":
        sources(plan)
    elif sys.argv[1]=="compare":
        compare(plan)
    else:
        raise ValueError(sys.argv[1])
