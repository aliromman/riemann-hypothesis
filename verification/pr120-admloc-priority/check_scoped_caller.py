"""Check the six original Satake sections with namespace-scoped tensor and function instances."""
import argparse
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

from check_priorities import (ORIGINAL, OPTIONS, PROVIDER, control_source, declarations, fill_library,
                              invoke, path_of, source)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for k in ("repo","original-lib","original-object","out"):
        p.add_argument("--"+k,type=Path,required=True)
    a=p.parse_args()
    out=a.out.resolve()
    out.mkdir(exist_ok=True)
    if any(out.iterdir()):raise ValueError("Select an empty output directory.")
    lib=out/"provider"
    path=lib/path_of(PROVIDER)
    path.parent.mkdir(parents=True)
    raw,n=re.subn(r"(?m)^instance \(priority := high\)(?= (?:modTens|modFun)\b)",
                  "scoped instance (priority := high)",source(a.repo,ORIGINAL,PROVIDER))
    if n!=2:raise ValueError("The two instance declarations changed.")
    path.write_text(raw)
    packages=[Path(x) for x in os.environ["LEAN_PATH"].split(os.pathsep) if "/.lake/packages/" in x]
    def build(file,root,inputs):
        return invoke(["lean",*OPTIONS,"--root",str(root),"-o",str(file.with_suffix(".olean")),str(file)],
                      root,inputs,root/"compile.jsonl")
    result={"provider":build(path,lib,[a.original_lib.resolve(),*packages])}
    if result["provider"]["exit"]:raise ValueError("The declaring module failed.")
    fill_library(a.original_lib.resolve(),lib)
    text=control_source(a.repo,*declarations(a.repo),expose=True)
    test=out/"SatakeProof.lean"
    test.write_text(text)
    result["source_sha256"]=hashlib.sha256(text.encode()).hexdigest()
    result["target"]=build(test,out,[lib,*packages])
    if not result["target"]["exit"]:
        result["kernel"]=invoke(["leanchecker","-v","SatakeProof"],out,[out,lib,*packages],out/"kernel.log")
        compare=subprocess.run(["lean","--run",Path(__file__).with_name("Interface.lean"),
                                test.with_suffix(".olean"),a.original_object.resolve()],capture_output=True,text=True)
        result["interface_exit"]=compare.returncode
        result["comparison"]=(compare.stdout+compare.stderr).strip()
    (out/"results.json").write_text(json.dumps(result,indent=2)+"\n")
    print(result,flush=True)
    if result["target"]["exit"] or result["kernel"]["exit"] or result["interface_exit"]:raise SystemExit(1)


if __name__=="__main__":
    main()
