"""Replay the complete 4.36 amplifier proof with the logical members of its direct imports."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULE = "Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses"
OWNERS = ["Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace",
          "Formalism.DoubleCosetMeasures.StatementZ", "GroundTheory.AutomorphicForms.GL2.GJMatrixCoord"]
PUBLIC = "@[expose] public section"
OPTIONS = ["--json", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
           "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000"]
parser = argparse.ArgumentParser(description=__doc__)
for arg in ("repo","bin","stock","providers","output"):
    parser.add_argument("--"+arg, type=Path, required=True)
parser.add_argument("--revision", required=True)
args=parser.parse_args()
repo,binary,stock,providers,out=(path.resolve() for path in (args.repo,args.bin,args.stock,args.providers,args.output))
if out == stock or stock in out.parents or out == providers or providers in out.parents:
    raise ValueError("Keep the output directory outside the input libraries.")
if out.exists() and any(out.iterdir()):
    raise ValueError("Use an empty output directory for the proof controls.")
out.mkdir(parents=True,exist_ok=True)
revision=subprocess.check_output(["git","-C",repo,"rev-parse","--verify",args.revision+"^{commit}"],text=True).strip()
def source(module):
    return subprocess.check_output(["git","-C",repo,"show",revision+":src/"+module.replace(".","/")+".lean"],text=True)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def fill_view(source_dir, dest_dir, blocked):
    for item in source_dir.iterdir():
        dest = dest_dir/item.name
        if dest in blocked or any(dest.parent==f.parent and dest.name.startswith(f.name+'.') for f in blocked):
            continue
        if not dest.exists():
            dest.symlink_to(item,target_is_directory=item.is_dir())
        elif item.is_dir() and not dest.is_symlink():
            fill_view(item,dest,blocked)
system=dict(os.environ,PATH=str(binary)+os.pathsep+os.environ["PATH"],LEAN_NUM_THREADS="2")
version=subprocess.check_output([binary/"lean","--version"],text=True).strip()
if "version 4.36.0," not in version:
    raise ValueError(version)
package_path=subprocess.check_output([binary/"lake","--no-cache","env","printenv","LEAN_PATH"],cwd=repo,env=system,text=True).strip()
packages=[str(Path(entry).resolve() if Path(entry).is_absolute() else (repo/entry).resolve()) for entry in package_path.split(os.pathsep) if "/packages/" in entry]
if not packages:
    raise ValueError("The package environment is empty.")
current=source(MODULE)
head,body=current.split(PUBLIC,1)
physical=re.findall(r"(?m)^public import (\S+)",head)
logical=[]
for dep in physical:
    members=[dep] if dep=="Mathlib" else re.findall(r"(?m)^-- bundled from (\S+)$",source(dep)) or [dep]
    for name in members:
        if name!="Mathlib" and not (stock/Path(*name.split(".")).with_suffix(".olean")).is_file():
            raise ValueError("Missing original input: "+name)
        if name not in logical:logical.append(name)
source_path=Path(*MODULE.split(".")).with_suffix(".lean")
stock_pin="c7791603122c0328f79e49f6be5d7d4402effc53"
package_src=subprocess.check_output(["git","-C",repo,"show",stock_pin+":lake-manifest.json"])
if package_src!=(repo/"lake-manifest.json").read_bytes() or package_src!=subprocess.check_output(["git","-C",repo,"show",revision+":lake-manifest.json"]):
    raise ValueError("The original and current package locks differ.")
for dep in json.loads(package_src)["packages"]:
    actual=subprocess.check_output(["git","-C",repo/".lake/packages"/dep["name"],"rev-parse","HEAD"],text=True).strip()
    if actual!=dep["rev"]:raise ValueError("Wrong package revision: "+dep["name"])
receipt=dict(revision=revision,module=MODULE,lean=version,full_source_sha256=sha(current.encode()),body_sha256=sha(body.encode()),
             physical_imports=physical,logical_members=logical,package_lock_sha256=sha(package_src),cases={})
haves="  have : BorelSpace (Matrix"
if body.count(haves)!=1:raise ValueError("The local Borel-space proof changed.")
def run(label,extra,body_text,libraries):
    target=out/label
    f=target/source_path
    f.parent.mkdir(exist_ok=True,parents=True)
    imports=list(dict.fromkeys([*logical,*extra]))
    contents="module\n\n"+"".join("public import "+n+"\n" for n in imports)+"\n"+PUBLIC+body_text
    f.write_text(contents)
    blocked={f.with_suffix("")}
    if libraries!=stock:
        for owner in OWNERS:
            relative=Path(*owner.split("."))
            directory=target/relative.parent
            directory.mkdir(exist_ok=True,parents=True)
            blocked.add(target/relative)
            for suffix in (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig"):
                file=(libraries/relative).with_suffix(suffix)
                if not file.is_file():
                    raise ValueError("Incomplete provider build at "+str(file))
                dest=directory/file.name
                dest.symlink_to(file)
    fill_view(stock,target,blocked)
    env=dict(system,LEAN_PATH=os.pathsep.join([str(target),*packages]))
    result=subprocess.run([binary/"lean",*OPTIONS,"--root",target,"-o",f.with_suffix(".olean"),f],cwd=target,env=env,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=result.stdout
    (target/"compile.jsonl").write_bytes(log)
    messages=[json.loads(line) for line in log.splitlines() if line.startswith(b"{")]
    errors=[dict(pos=x.get("pos"),message=x.get("data")) for x in messages if x.get("severity")=="error"]
    kernel=None
    if not result.returncode:
        kernel=subprocess.run([binary/"leanchecker","-v",MODULE],cwd=target,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (target/"kernel.log").write_bytes(kernel.stdout)
    record=dict(extra=extra,compile_exit=result.returncode,errors=errors,source_sha256=sha(contents.encode()),kernel_exit=None if kernel is None else kernel.returncode)
    receipt["cases"][label]=record
    (out/"results.json").write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+"\n")
    print(label,"compile",result.returncode,"errors",len(errors),"first",errors[0]["message"][:160] if errors else "",flush=True)
    if kernel is not None:
        kernel.check_returncode()
    if result.returncode and not errors:raise ValueError(log[-400:])
for name,lib,extra,case_body in (("logical",stock,[],body),("all-providers",stock,OWNERS,body),("all-providers-local-instance",stock,OWNERS,body.replace(haves,"  haveI : BorelSpace (Matrix")),("aliases",providers,OWNERS,body)):
    run(name,extra,case_body,lib)
negative = receipt["cases"]["logical"]
if negative["compile_exit"] == 0 or not any("Formalism.DoubleCosetMeasures.instMeasMat" in e["message"] for e in negative["errors"]):
    raise ValueError("The original member imports did not reproduce the missing provider name.")
for name in ("all-providers", "all-providers-local-instance", "aliases"):
    if receipt["cases"][name]["compile_exit"] != 0 or receipt["cases"][name]["kernel_exit"] != 0:
        raise ValueError("The complete proof failed in " + name)
