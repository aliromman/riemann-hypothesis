"""Replay current-main proof bodies after importing the other product-space provider."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor

parser=argparse.ArgumentParser(description=__doc__)
for name in ("before","after","output","bin"):
    parser.add_argument("--"+name,type=Path,required=True)
args=parser.parse_args()
before,after,out,binary=(p.resolve() for p in (args.before,args.after,args.output,args.bin))
out.mkdir(exist_ok=True,parents=True)
mods=["Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue",
      "Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero"]
providers=["Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace",
           "Formalism.DoubleCosetMeasures.StatementZ","GroundTheory.AutomorphicForms.GL2.GJMatrixCoord"]
aliases=["GlobalTheory.SplitWeil.matrixMeasurableSpace","Formalism.DoubleCosetMeasures.instMeasMat",
         "GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix","Matrix.instMeasurableSpace"]
def path(n):return Path(*n.split(".")).with_suffix(".lean")
def proof_source(module, extra):
    f=path(module);text=(before/"src"/f).read_text()
    if text!=(after/"src"/f).read_text():raise ValueError("The proof body changed: "+module)
    lines=text.splitlines(keepends=True)
    last=max(i for i,l in enumerate(lines) if re.match(r"^(?:public )?(?:meta )?import ",l))
    lines[last+1:last+1]=["public import "+k+"\n" for k in extra]
    return "".join(lines)
probe="module\n"+"\n".join("public import "+n for n in [*providers,"Mathlib.Analysis.Matrix.MeasurableSpace"])+"\n@[expose] public section\nvariable {m n X : Type} [MeasurableSpace X]\n"
for i,left in enumerate(aliases):
    for right in aliases[i+1:]:
        probe+=f"example : ({left} : MeasurableSpace (Matrix m n X)) = {right} := by with_reducible rfl\n"
cases=[("double",mods[0],proof_source(mods[0], [providers[0]])),("twist",mods[1],proof_source(mods[1],providers[1:])),
       ("agreement","MatrixSpaceAgreement",probe)]
opts=["--json","--tstack=400000","-DautoImplicit=false","-DrelaxedAutoImplicit=false","-DmaxSynthPendingDepth=3","-DmaxHeartbeats=4000000"]
def run(case):
    tag,name,src,side,proj=case
    d=out/(side+"-"+tag);f=d/path(name);f.parent.mkdir(parents=True,exist_ok=True);f.write_text(src)
    env={**os.environ,"PATH":str(binary)+":"+os.environ["PATH"],"LEAN_NUM_THREADS":"2","LAKE_ARTIFACT_CACHE":"false"}
    res=subprocess.run([binary/"lake","--no-cache","env",binary/"lean",*opts,"--root",d,"-o",f.with_suffix(".olean"),f],cwd=proj,env=env,capture_output=True)
    buf=res.stdout+res.stderr;(d/"compile.jsonl").write_bytes(buf)
    errors=[]
    for l in buf.splitlines():
        try: row=json.loads(l)
        except ValueError: continue
        if row.get("severity")=="error": errors.append(dict(position=row["pos"],message=row["data"]))
    print(tag,side,res.returncode,len(errors),[e["message"][:130] for e in errors[:1]],flush=True)
    if res.returncode and not errors: raise RuntimeError(buf.decode()[:250])
    return tag+"-"+side,dict(module=name,exit=res.returncode,errors=errors)
with ThreadPoolExecutor(max_workers=2) as pool:
    results=dict(pool.map(run,[(tag,n,src,side,proj) for tag,n,src in cases for side,proj in [("stock",before),("candidate",after)]]))
(out/"results.json").write_text(json.dumps(results,indent=2)+"\n")
