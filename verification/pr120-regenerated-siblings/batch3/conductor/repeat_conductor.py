"""Check the conductor group's public union and its changed definition in both kernels."""
import argparse
import json
import os
from pathlib import Path
import subprocess

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("before","after","bin","audit","aux","record"):
        parser.add_argument("--"+name,required=True,type=Path)
    a=parser.parse_args()
    tool=a.bin.resolve()
    record=json.loads(a.record.read_bytes())
    module, inputs=record["module"], record["inputs"]
    env={**os.environ,"PATH":str(tool)+os.pathsep+os.environ["PATH"],"LAKE_ARTIFACT_CACHE":"false"}
    def obj(project,name):
        return project.resolve()/".lake/build/lib/lean"/Path(*name.split(".")).with_suffix(".olean")
    def lean(project,script,args):
        data=subprocess.check_output([tool/"lake","--no-cache","env",tool/"lean","--run",script.resolve(),*args],cwd=project,env=env)
        return [json.loads(line) for line in data.splitlines()]
    new=obj(a.after,module)
    args=[module,new,*[n+"\t"+str(obj(a.before,n)) for n in inputs]]
    scan=lean(a.before,a.audit,["scan",*args])
    if [r["module"] for r in scan]!=inputs or any(r["structural"] for r in scan):raise ValueError(scan)
    if sum(r["public"] for r in scan)!=record["totals"]["public"]:raise ValueError("Public declaration count changed.")
    for label,project in [("stock",a.before),("candidate",a.after)]:
        checked=lean(project,a.audit,[label,*args])
        for first,second in zip(scan,checked,strict=True):
            if second["structural"] or first["module"]!=second["module"]:raise ValueError(second)
            pairs=lambda row:[(d["declaration"],d["field"]) for d in row["terms"]]
            if pairs(first)!=pairs(second):raise ValueError("Kernel compared a different set of expressions.")
            changes=[d for d in second["terms"] if d["conversion"]!="defeq"]
            if not changes:continue
            old=second["module"];name=old if label=="stock" else module
            terms=[d["declaration"]+"\t"+d["field"] for d in changes]
            expanded=lean(project,a.aux,[label,name,obj(a.before,old),new,*terms])
            if len(expanded)!=len(terms) or any(r["originalToExpanded"]!="defeq" or r["expandedConversion"]!="defeq" for r in expanded):
                raise ValueError(expanded)
        print(label, sum(r["public"] for r in checked), "public declarations checked")
if __name__=="__main__":
    main()
