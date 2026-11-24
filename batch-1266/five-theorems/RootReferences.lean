import Lean
import Lean.Util.FoldConsts

open Lean

private def reference (env : Environment) (localNames : NameSet) (n : Name) : IO Json := do
  let owner ← if localNames.contains n then pure "Main" else do
    let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing owner for {n}"
    let some owner := env.header.moduleNames[idx.toNat]? | throw <| IO.userError s!"missing module for {n}"
    pure owner.toString
  return Json.mkObj [("name", toJson n.toString), ("module", toJson owner)]

unsafe def main (args : List String) : IO Unit := do
  let file :: setupFile :: targets := args | throw <| IO.userError "expected a Main image, setup file and theorem names"
  initSearchPath (← findSysroot)
  let file := System.FilePath.mk file
  let parts ← readModuleDataParts #[file, OLeanLevel.server.adjustFileName file, OLeanLevel.private.adjustFileName file]
  let some (publicData, _) := parts[0]? | throw <| IO.userError "missing Main header"
  let some (moduleData, _) := parts.back? | throw <| IO.userError "missing Main private data"
  let setup ← ModuleSetup.load setupFile
  let env ← importModules publicData.imports {} (trustLevel := 0) (level := .exported) (arts := setup.importArts)
  let localNames := moduleData.constants.foldl (fun ns c => ns.insert c.name) ({} : NameSet)
  let mut rs := #[]
  for target in targets do
    let some (.thmInfo c) := moduleData.constants.find? (fun e => e.name == target.toName)
      | throw <| IO.userError s!"missing proof of {target}"
    let owner := reference env localNames
    let statement ← (c.type.getUsedConstants.qsort Name.quickLt).mapM owner
    let body ← (c.value.getUsedConstants.qsort Name.quickLt).mapM owner
    rs := rs.push <| Json.mkObj [("theorem", toJson target), ("type", toJson statement), ("proof", toJson body)]
  IO.println <| (toJson rs).compress
