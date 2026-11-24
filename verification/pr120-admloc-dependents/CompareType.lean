module
import Lean
open Lean

private def readType (path : String) (name : Name) : IO (Expr × List Name × CompactedRegion) := do
  let (data, region) ← readModuleData path
  let some info := data.constants.find? (·.name == name) | throw <| IO.userError s!"missing {name} in {path}"
  return (info.type, info.levelParams, region)

public unsafe def main (args : List String) : IO Unit := do
  let [mod, name, stockPath, changedPath] := args | throw <| IO.userError "expected module, declaration and two objects"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod.toName, importAll := true }] {} (level := .private)
  let (a, ls, r₁) ← readType stockPath name.toName
  let (b, rs, r₂) ← readType changedPath name.toName
  unless ls == rs do throw <| IO.userError "universe parameters differ"
  let ac := a.getUsedConstants
  let bc := b.getUsedConstants
  IO.println s!"only in stock: {ac.filter fun n => !bc.contains n}"
  IO.println s!"only in changed: {bc.filter fun n => !ac.contains n}"
  let .ok ta := Kernel.check env {} a | throw <| IO.userError "stock type did not check in this environment"
  let .ok tb := Kernel.check env {} b | throw <| IO.userError "changed type did not check in this environment"
  let .ok true := Kernel.isDefEq env {} ta tb | throw <| IO.userError "sorts differ"
  let .ok yes := Kernel.isDefEq env {} a b | throw <| IO.userError "kernel conversion failed"
  IO.println s!"raw equal: {Expr.equal a b}, kernel definitionally equal: {yes}"
  -- Keep the regions in memory until the kernel has read both expressions.
  let _ := (r₁, r₂)
  unless yes do throw <| IO.userError "the two public types are not definitionally equal"
