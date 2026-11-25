import Lean.Replay

open Lean

unsafe def main (args : List String) : IO Unit := do
  let file :: setupFile :: targets := args | throw (IO.userError "expected module, setup and theorem names")
  initSearchPath (← findSysroot)
  let file := System.FilePath.mk file
  let parts ← readModuleDataParts #[file, OLeanLevel.server.adjustFileName file, OLeanLevel.private.adjustFileName file]
  let some (mainData, _) := parts[0]? | throw (IO.userError "missing module header")
  let some (full, _) := parts.back? | throw (IO.userError "missing private declarations")
  let setup ← ModuleSetup.load setupFile
  let env ← importModules mainData.imports {} (trustLevel := 0) (level := .exported) (arts := setup.importArts)
  let kernel := env.toKernelEnv
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for ci in full.constants do
    unless ci matches .thmInfo _ do throw (IO.userError s!"unexpected declaration {ci.name}")
    if (kernel.find? ci.name).isSome then throw (IO.userError s!"already imported {ci.name}")
    constants := constants.insert ci.name ci
  unless constants.size == targets.length && targets.all (fun s => constants.contains s.toName) do
    throw (IO.userError "theorem names differ from comparator.json")
  let some (.thmInfo original) := constants[`riemannHypothesis]? | throw (IO.userError "missing theorem")
  let bad := constants.insert `riemannHypothesis (.thmInfo { original with value := mkConst ``True.intro })
  let rejected ← try
    discard <| kernel.replay bad
    pure false
  catch e =>
    IO.println s!"negative control: {e}"
    pure true
  unless rejected do throw (IO.userError "kernel accepted the negative control")
  let checked ← kernel.replay constants
  for t in targets do
    let some (.thmInfo info) := checked.find? t.toName | throw (IO.userError s!"missing replayed theorem {t}")
    IO.println s!"kernel accepted {info.name}"
