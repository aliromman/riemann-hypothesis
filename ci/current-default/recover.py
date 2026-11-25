"""Keep complete, native Lake artifacts if a hosted default build reaches its limit."""
from pathlib import Path
import gzip, hashlib, importlib.util, json, os, shutil, subprocess, sys
p=Path(os.environ["PROJECT"]); report=Path(os.environ["REPORT"]); mode=sys.argv[1]
def save(path,value):path.write_text(json.dumps(value,separators=(",",":"))+"\n")
def current():
    return subprocess.check_output(["git","rev-parse","HEAD"],cwd=p,text=True).strip()
def inputs():
    data={}
    root=p/".lake/build/lib/lean"
    for f in root.rglob("*.trace"):
        rel=f.relative_to(root).with_suffix("")
        if (p/"src"/rel.with_suffix(".lean")).is_file():
            data[".".join(rel.parts)]=json.loads(f.read_bytes())["depHash"]
    return data
index=report/"parent-inputs.json.gz"
if mode=="before":
    assert current()==os.environ["PARENT"]
    with gzip.open(index,"wt",encoding="utf-8") as out:json.dump(inputs(),out,separators=(",",":"))
    sys.exit(0)
assert mode=="recover" and current()==os.environ["CANDIDATE"]
with gzip.open(index,"rt") as fd:previous=json.load(fd)
actual=inputs();names=sorted(k for k,v in actual.items() if previous.get(k)!=v)
stage=report/"partial";art=stage/"artifacts";art.mkdir(parents=True)
jobs=report/"recovery-modules.json";out=report/"recovery.jsonl";overrides=report/"overrides.json"
save(jobs,names);save(overrides,{"version":"1.2.0","packages":[]})
bundle=Path(subprocess.check_output(["elan","which","lean"],cwd=p,text=True).strip()).parent.parent
subprocess.run([str(bundle/"bin/lean"),"--load-dynlib="+str(bundle/"lib/lean/libLake_shared.so"),"--run",str(p/"scripts/cache-bootstrap/RecoverCompleted.lean"),str(p),str(jobs),str(out),str(overrides),"4"],cwd=p,check=True)
r=[json.loads(line) for line in out.read_bytes().splitlines()]
assert len(r)==len(names) and {row["name"] for row in r}==set(names)
registered=[]
for row in r:
    if not row["ok"]:continue
    n=row["name"];a=row["artifact"]
    assert row["input"]==actual[n] and a==Path(a).name and a.endswith(".ltar")
    source=p/".lake/cache/artifacts"/a;target=art/a
    if not target.exists():os.link(source,target)
    with target.open("rb")as f:sha=hashlib.file_digest(f,"sha256").hexdigest()
    registered.append([n,row["input"],a,sha])
config=importlib.util.spec_from_file_location("stock_ci_cache",p/"scripts/ci-cache-get.py")
stock=importlib.util.module_from_spec(config);config.loader.exec_module(stock)
stock.write_map(stage/"outputs.jsonl",[(key,a) for _,key,a,_ in registered])
save(stage/"modules.json",registered)
save(stage/"receipt.json",{"parent":os.environ["PARENT"],"head":current(),"source":os.environ["SOURCE"],"candidate_traces":len(names),"recoverable_archives":len(registered),"rejected":len(r)-len(registered),"build_exit":(report/"producer.exit").read_text().strip()})
print("Verified partial Lake artifacts",len(registered),"/",len(names),flush=True)
