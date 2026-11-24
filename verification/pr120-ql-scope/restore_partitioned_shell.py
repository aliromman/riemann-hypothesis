"""Restore the historical shell proof once all inputs use its original measure."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

repo, structural, output = map(Path,sys.argv[1:])
if output.exists():
    raise ValueError("select a fresh output directory")
shutil.copytree(structural,output)
report=json.loads((output/"projection.json").read_bytes())
name="Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamified"
path=Path("src",*name.split(".")).with_suffix(".lean")
marker="theorem shell_lemma : ShellLemma := by\n"
def body(ref):
    raw=subprocess.check_output(["git","-C",repo,"show",ref+":"+path.as_posix()]).decode()
    front,anchor,proof=raw.partition(marker)
    if not anchor or marker in proof:
        raise ValueError("the theorem boundary has changed")
    return front,proof
if set(report["explicit_uses_without_provider"])!={name}:
    raise ValueError("inspect the other explicit instance uses")
_, current=body(report["head"])
_, bridge=body("17e20263b0b")
_, old=body(report["base"])
_, pre_bridge=body("17e20263b0b^")
if current!=bridge or old!=pre_bridge:
    raise ValueError("the shared branch has other shell proof changes")
target=output/path
data=target.read_text()
before, sep, after=data.partition(marker)
if not sep or after!=current:
    raise ValueError("unexpected shell body in generated tree")
target.write_bytes((before+marker+old).encode())
report["restored_proof"]={"module":name,"declaration":"shell_lemma","source":report["base"],
                          "prior_body_sha256":hashlib.sha256(current.encode()).hexdigest(),
                          "restored_body_sha256":hashlib.sha256(old.encode()).hexdigest(),
                          "previous_integration_fix":"17e20263b0b",
                          "reason":"The original proof uses the Units measurable space throughout."}
report["source_sha256"][name]=hashlib.sha256(target.read_bytes()).hexdigest()
report["explicit_uses_without_provider"]={}
(output/"projection.json").write_text(json.dumps(report,indent=2)+"\n")
print(report["restored_proof"])
