"""Build the exact upstream PR 911 source trees and compare their affected public declarations."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

from verify_sources import project_closure

HERE = Path(__file__).resolve().parent
PIN = "leanprover/lean4:v4.37.0-rc1"

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--stock",type=Path,required=True)
    cli.add_argument("--candidate",type=Path,required=True)
    cli.add_argument("--out",type=Path,required=True)
    cli.add_argument("--no-build",action="store_true",help="require all Lake targets to be up to date")
    cli.add_argument("--plan",type=Path,default=HERE/"dependents.json",help="versioned dependency list and exact source revisions")
    cli.add_argument("--modules",type=Path,help="check a subset, one module per line")
    cli.add_argument("--source-repo",type=Path,help="check a source cone against these Git objects in place of a complete checkout")
    args=cli.parse_args()
    stock, candidate, out = (p.resolve() for p in (args.stock,args.candidate,args.out))
    out.mkdir(parents=True,exist_ok=True)
    plan=json.loads(args.plan.read_text())
    BASE, FIX = plan["base"], plan["candidate"]
    full=plan["modules"];requested=full if args.modules is None else args.modules.read_text().splitlines()
    if not requested or len(requested)!=len(set(requested)) or not set(requested)<=set(full):
        raise ValueError("The selected modules must belong to the recorded dependency set.")
    targets=plan["targets"] if args.modules is None else requested
    env={**os.environ,"LEAN_ABORT_ON_PANIC":"1","LAKE_ARTIFACT_CACHE":"false"}
    def git(p,*cmd):return subprocess.check_output(["git","-C",p,*cmd],text=True).strip()
    verified = {}
    for label,p,sha in (("stock",stock,BASE),("candidate",candidate,FIX)):
        if (p/"lean-toolchain").read_text().strip()!=PIN or "version 4.37.0-rc1," not in subprocess.check_output(["lean","--version"],cwd=p,text=True):
            raise ValueError("Wrong Lean version in "+str(p))
        if args.source_repo:
            verified[label] = project_closure(args.source_repo.resolve(),p,sha,targets)
        else:
            if git(p,"rev-parse","HEAD")!=sha:
                raise ValueError("Wrong Git revision in "+str(p))
            if git(p,"status","--porcelain","--untracked-files=all","--","src","lean-toolchain","lakefile.toml","lake-manifest.json"):
                raise ValueError("Uncommitted source or build configuration in "+str(p))
        cmd=["lake","--no-cache","--log-level=error","build"]
        if args.no_build:cmd.append("--no-build")
        with (out/(label+"-build.log")).open("wb") as log:
            subprocess.run([*cmd,*targets],cwd=p,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
    def module_object(p,n):
        file=p/".lake/build/lib/lean"/Path(*n.split(".")).with_suffix(".olean")
        if not all(Path(str(file)+suffix).is_file() for suffix in ("",".server",".private")):
            raise ValueError("Missing module data for "+n+" in "+str(p))
        return str(file)
    def run_batch(mode,p,batch):
        with tempfile.TemporaryDirectory() as temp:
            manifest=Path(temp)/"objects.tsv"
            manifest.write_text("".join(n+"\t"+module_object(stock,n)+"\t"+module_object(candidate,n)+"\n" for n in batch))
            q=subprocess.run(["lake","--no-cache","env","lean","--run",str(HERE/"AuditPublic.lean"),mode,str(manifest)],
                             cwd=p,env=env,stdout=subprocess.PIPE,check=True,text=True)
        rows=[json.loads(v) for v in q.stdout.splitlines() if v.strip()]
        if [r["module"] for r in rows]!=batch:raise ValueError("Incomplete comparison output.")
        return rows
    def phase(label,mode,project,names,size):
        records=[]
        with (out/(label+".jsonl")).open("w") as f:
            for i in range(0,len(names),size):
                rows=run_batch(mode,project,names[i:i+size])
                for row in rows:f.write(json.dumps(row,separators=(",",":"))+"\n")
                f.flush();records.extend(rows)
        return records
    raw=phase("public","scan",stock,requested,32)
    pending=[r["module"] for r in raw if r["terms"]]
    sides=[phase(label,"kernel",p,pending,4) for label,p in (("old-conversion",stock),("new-conversion",candidate))]
    failures = [r["module"] for r in raw if r["structural"]]
    affected = {}
    for side in sides:
        for row in side:
            if row["structural"]:
                failures.append(row["module"])
            for term in row["terms"]:
                if term["conversion"] != "defeq":
                    affected.setdefault(row["module"], set()).add((term["declaration"], term["field"]))
    for label, project in (("stock",stock),("candidate",candidate)):
        with (out/(label+"-proof-helpers.jsonl")).open("w") as log:
            for module, terms in sorted(affected.items()):
                fields = sorted(terms)
                result = subprocess.run(["lake","--no-cache","env","lean","--run",str(HERE/"CompareAuxProofs.lean"),
                                         label,module,module_object(stock,module),module_object(candidate,module),
                                         *["\t".join(t) for t in fields]],cwd=project,env=env,text=True,stdout=subprocess.PIPE)
                rows = [json.loads(line) for line in result.stdout.splitlines()]
                for row in rows:
                    log.write(json.dumps(row,separators=(",",":"))+"\n")
                log.flush()
                if result.returncode or [(r["declaration"],r["field"]) for r in rows] != fields or any(
                    r["module"] != module or r["environment"] != label or
                    r["originalToExpanded"] != "defeq" or r["expandedConversion"] != "defeq" for r in rows):
                    failures.append(module)
    totals={k:sum(r[k] for r in raw) for k in ("public","rawTypes","definitions","rawDefinitions","theorems","rawProofs","axiomRecords")}
    result=dict(stock=BASE,candidate=FIX,modules=len(requested),fullModules=len(full),targets=targets,verifiedSourceFiles=verified,
                totals=totals,kernelComparisonModules=len(pending),expandedProofFields=sum(map(len,affected.values())),failedModules=sorted(set(failures)))
    (out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2),flush=True)
    if failures:raise SystemExit(1)

if __name__=="__main__":
    main()
