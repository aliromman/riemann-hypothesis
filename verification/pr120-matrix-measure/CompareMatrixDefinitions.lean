module
import Lean

open Lean

private def readDecls (path : String) : IO (NameMap ConstantInfo × Array CompactedRegion) := do
  let parts ← readModuleDataParts (#[path, path ++ ".server", path ++ ".private"].map System.FilePath.mk)
  let mut decls := {}
  for (data, _) in parts do
    for c in data.constants do decls := decls.insert c.name c
  return (decls, parts.map (·.2))

private def assertEqual (env : Environment) (a b : Expr) : IO Unit := do
  let .ok x := Kernel.check env {} a | throw (IO.userError "first term failed to typecheck")
  let .ok y := Kernel.check env {} b | throw (IO.userError "second term failed to typecheck")
  let .ok true := Kernel.isDefEq env {} x y | throw (IO.userError "different inferred types")
  let .ok true := Kernel.isDefEq env {} a b | throw (IO.userError "different values")

public unsafe def main (args : List String) : IO Unit := do
  let [side, mod, decl, oldPath, newPath] := args | throw (IO.userError "expected side, module, name and two objects")
  unless side == "stock" || side == "candidate" do throw (IO.userError "unknown environment")
  let name := decl.toName
  let (old, oldRegions) ← readDecls oldPath
  let (new, newRegions) ← readDecls newPath
  let some (.defnInfo a) := old.find? name | throw (IO.userError "missing old definition")
  let some (.defnInfo b) := new.find? name | throw (IO.userError "missing new definition")
  let .regular oldHeight := a.hints | throw (IO.userError "expected a regular old definition")
  let .regular newHeight := b.hints | throw (IO.userError "expected a regular new definition")
  unless a.name == b.name && a.levelParams == b.levelParams && a.safety == b.safety && a.all == b.all do
    throw (IO.userError s!"changed name {a.name != b.name}, levels {a.levelParams != b.levelParams}, safety {a.safety != b.safety}, mutual block {a.all != b.all}")
  let aux := name.str "_aux_1"
  let expanded := a.value.replace fun e => do
    let .const n ls := e | none
    guard (n == aux)
    let some (.defnInfo d) := old.find? n | none
    return d.value.instantiateLevelParams d.levelParams ls
  initSearchPath (← findSysroot)
  withImportModules #[{module := mod.toName, importAll := true},
      {module := `Mathlib.Analysis.Matrix.MeasurableSpace, importAll := true}] {} fun env => do
    assertEqual env a.type b.type
    if side == "stock" then assertEqual env a.value expanded
    assertEqual env expanded b.value
    IO.println <| Json.compress <| Json.mkObj [("side", toJson side), ("declaration", toJson decl),
      ("oldHeight", toJson oldHeight.toNat), ("newHeight", toJson newHeight.toNat),
      ("expandedAuxiliary", toJson (!Expr.equal expanded a.value)), ("definitionallyEqual", toJson true)]
  if oldRegions.isEmpty || newRegions.isEmpty then throw (IO.userError "empty object")
