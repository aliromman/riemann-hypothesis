module
import Lean
open Lean

private abbrev Decls := NameMap ConstantInfo

private def readDecls (path : String) : IO (Decls × Array CompactedRegion) := do
  let parts ← readModuleDataParts (#[path, path ++ ".server", path ++ ".private"].map System.FilePath.mk)
  let mut decls : Decls := {}
  for (data, _) in parts do
    for c in data.constants do decls := decls.insert c.name c
  return (decls, parts.map (·.2))

private def readRemoved (manifest : String) : IO (Decls × Array CompactedRegion) := do
  let mut removed : Decls := {}
  let mut regions := #[]
  for line in ← IO.FS.lines manifest do
    let [name, before, after] := line.splitOn "\t" | throw <| IO.userError "expected a name and two objects"
    let (old, leftRegions) ← readDecls before
    let (new, rightRegions) ← readDecls after
    let root := name.toName
    unless old.contains root && !new.contains root do throw <| IO.userError s!"expected a removed declaration: {name}"
    for (n, info) in old do
      let userName := (privateToUserName? n).getD n
      if root.isPrefixOf userName && !new.contains n then
        removed := removed.insert n info
    regions := regions ++ leftRegions ++ rightRegions
  return (removed, regions)

private def isAuxProof (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_proof_" && (s.drop 7).toString.toNat?.isSome
  | _ => false

private partial def expandAux (env other removed : Decls) (e : Expr) (expanding : NameSet := {}) : Expr :=
  e.replace fun v => do
    let .const n levels := v | none
    if let some info := removed.find? n then
      guard (!expanding.contains n)
      let value ← info.value? (allowOpaque := true)
      return expandAux env other removed (value.instantiateLevelParams info.levelParams levels) (expanding.insert n)
    guard (isAuxProof n && !expanding.contains n)
    let some (.thmInfo t) := env.find? n | none
    if let some (.thmInfo u) := other.find? n then
      if t.levelParams == u.levelParams && Expr.equal t.type u.type then none
      else some (expandAux env other removed (t.value.instantiateLevelParams t.levelParams levels) (expanding.insert n))
    else some (expandAux env other removed (t.value.instantiateLevelParams t.levelParams levels) (expanding.insert n))

private def exprOf (info : ConstantInfo) (field : String) : IO Expr := do
  if field == "type" then return info.type
  if field == "proof" then
    let .thmInfo t := info | throw <| IO.userError "expected a theorem"
    return t.value
  if field == "definition" then
    let some e := info.value? (allowOpaque := true) | throw <| IO.userError "missing definition body"
    return e
  if field.startsWith "recursor rule " then
    let .recInfo r := info | throw <| IO.userError "expected recursor"
    let ctor := (field.drop 14).toString.toName
    let some rule := r.rules.find? (·.ctor == ctor) | throw <| IO.userError "missing recursor rule"
    return rule.rhs
  throw <| IO.userError "unknown declaration field"

private def compare (env : Environment) (a b : Expr) : IO String := do
  let .ok x := Kernel.check env {} a | return "left expression does not typecheck"
  let .ok y := Kernel.check env {} b | return "right expression does not typecheck"
  let .ok true := Kernel.isDefEq env {} x y | return "different inferred types"
  match Kernel.isDefEq env {} a b with
  | .ok true => return "defeq"
  | .ok false => return "different"
  | .error _ => return "kernel error"

public unsafe def main (args : List String) : IO Unit := do
  let (removedPath, args) := match args with
    | "--unfold-removed" :: path :: rest => (some path, rest)
    | _ => (none, args)
  let owner :: mod :: oldPath :: newPath :: fields := args | throw <| IO.userError "expected ownership, module, objects and fields"
  unless (owner == "stock" || owner == "candidate") && !fields.isEmpty do
    throw <| IO.userError "invalid owner or empty field list"
  initSearchPath (← findSysroot)
  let (removed, removedRegions) ← match removedPath with
    | some path => readRemoved path
    | none => pure ({}, #[])
  let (old, oldRegions) ← readDecls oldPath
  let (new, newRegions) ← readDecls newPath
  withImportModules #[{module := mod.toName, importAll := true}] {} fun env => do
    let mut passed := true
    for item in fields do
      let [n,k] := item.splitOn "\t" | throw <| IO.userError "expected declaration and field"
      let some oldInfo := old.find? n.toName | throw <| IO.userError ("missing original " ++ n)
      let some newInfo := new.find? n.toName | throw <| IO.userError ("missing revised " ++ n)
      let a ← exprOf oldInfo k
      let b ← exprOf newInfo k
      let x := expandAux old new removed a
      let y := expandAux new old {} b
      let own ← if owner == "stock" then compare env a x else compare env b y
      let both ← compare env x y
      IO.println <| Json.compress <| Json.mkObj [("module",toJson mod),("declaration",toJson n),
        ("field",toJson k),("environment",toJson owner),("originalToExpanded",toJson own),
        ("expandedConversion",toJson both)]
      if own != "defeq" || both != "defeq" then passed := false
    unless passed do IO.Process.exit 1
    if oldRegions.isEmpty || newRegions.isEmpty || (removedPath.isSome && removedRegions.isEmpty) then throw <| IO.userError "empty module regions"
