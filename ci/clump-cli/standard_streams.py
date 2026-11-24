"""Retain the actual CLI output after the timed trials and restore the checkout."""
import hashlib,json,pathlib,subprocess,sys,tempfile
project,tools,results=map(pathlib.Path,sys.argv[1:])
def sha(raw):return hashlib.sha256(raw).hexdigest()
def run(cmd):
 return subprocess.run(cmd,cwd=project,capture_output=True,check=True)
summary=json.loads((results/"summary.json").read_bytes());rows=[json.loads(x)for x in (results/"observations.jsonl").read_text().splitlines()]
out=results/"standard-streams";out.mkdir();plan=results/"saved-plan.json";test=out/"untimed-plan.json"
published=run([sys.executable,"-B",tools/"published.py","plan",project,"--out",test,"--exclude",project/"scripts/clump-exclude.txt"])
assert published.stderr==b"" and test.read_bytes()==plan.read_bytes()
assert {r["output_sha256"]for r in rows if r["command"]=="plan"}=={sha(published.stdout)}
(out/"plan.stdout").write_bytes(published.stdout);(out/"plan.stderr").write_bytes(published.stderr);test.unlink()
data=json.loads(plan.read_bytes());names=["src/"+m.replace(".","/")+".lean" for members in data.values() for m in members]
assert len(names)==len(set(names))==656
hashes={}
with tempfile.TemporaryDirectory()as name:
 pathspec=pathlib.Path(name)/"paths";pathspec.write_bytes(b"\0".join(k.encode()for k in names)+b"\0")
 for label in ("community","published","proposed"):
  try:
   invocation=run([sys.executable,"-B",tools/(label+".py"),"apply",project,plan]);(out/(label+"-apply.stdout")).write_bytes(invocation.stdout);(out/(label+"-apply.stderr")).write_bytes(invocation.stderr)
   hashes[label]=[sha(invocation.stdout),sha(invocation.stderr)]
  finally:
   run(["git","restore","--source=HEAD","--worktree","--pathspec-from-file="+str(pathspec),"--pathspec-file-nul"]);run(["git","diff","--exit-code","--","src"])
assert len(set(map(tuple,hashes.values())))==1
(out/"results.json").write_text(json.dumps(dict(plan_unchanged=True,plan_stdout_sha256=sha(published.stdout),plan_stderr_sha256=sha(published.stderr),timed_planner_stdout_count=12,untimed_apply_stdout_stderr_sha256=hashes,restored_after_each_apply=True),indent=2)+"\n")
