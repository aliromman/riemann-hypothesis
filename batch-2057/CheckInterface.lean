import Lean

open Lean

unsafe def loadParts (stem : String) : IO (Array (ModuleData × CompactedRegion)) :=
  readModuleDataParts ((#[stem, stem ++ ".server", stem ++ ".private"]).map System.FilePath.mk)

private def constants (parts : Array (ModuleData × CompactedRegion)) : NameMap ConstantInfo := Id.run do
  let mut result := {}
  for (part, _) in parts do
    for c in part.constants do result := result.insert c.name c
  return result

private def same (a b : ConstantInfo) : Bool :=
  a == b && Expr.equal a.type b.type && match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
    | some x, some y => Expr.equal x y
    | none, none => true
    | _, _ => false

private def writeKernelImage (m : Name) (data : ModuleData) (out : System.FilePath) : IO Unit := do
  let cs := data.constants.qsort (fun a b => a.name.quickCmp b.name == .lt)
  let payload : ModuleData := { (default : ModuleData) with isModule := true, constNames := cs.map (·.name), constants := cs }
  saveModuleDataParts m #[(out, payload)]

unsafe def main (args : List String) : IO UInt32 := do
  let [mod, before, after, scratch] := args | throw <| IO.userError "expected module, two olean paths and a scratch directory"
  let l ← loadParts before
  let r ← loadParts after
  let some (p, _) := l[0]? | throw <| IO.userError "missing parent module"
  let some (q, _) := r[0]? | throw <| IO.userError "missing candidate module"
  let x := constants l
  let y := constants r
  let mut mismatches := 0
  let mut proofChanges := 0
  let mut examples : Array String := #[]
  for (n, a) in x do
    if !(y.find? n).any (same a) then
      match a, y.find? n with
      | .thmInfo beforeThm, some (.thmInfo afterThm) =>
        if Expr.equal beforeThm.type afterThm.type && beforeThm.levelParams == afterThm.levelParams &&
            { beforeThm with value := afterThm.value } == afterThm then
          proofChanges := proofChanges + 1
        else
          mismatches := mismatches + 1
          if examples.size < 4 then examples := examples.push n.toString
      | _, _ =>
        mismatches := mismatches + 1
        if examples.size < 4 then examples := examples.push n.toString
  let left := System.FilePath.mk scratch / "parent.normalized"
  let right := System.FilePath.mk scratch / "candidate.normalized"
  saveModuleDataParts mod.toName #[(left, { p with imports := #[] })]
  saveModuleDataParts mod.toName #[(right, { q with imports := #[] })]
  let identical := (← IO.FS.readBinFile left) == (← IO.FS.readBinFile right)
  let some (fullParent, _) := l.back? | throw <| IO.userError "missing parent declarations"
  let some (fullCandidate, _) := r.back? | throw <| IO.userError "missing candidate declarations"
  let kl := System.FilePath.mk scratch / "parent.kernel"
  let kr := System.FilePath.mk scratch / "candidate.kernel"
  writeKernelImage mod.toName fullParent kl
  writeKernelImage mod.toName fullCandidate kr
  let sameKernel := (← IO.FS.readBinFile kl) == (← IO.FS.readBinFile kr)
  let pub₁ := p.imports.filter (·.isExported)
  let pub₂ := q.imports.filter (·.isExported)
  let count₁ := x.toList.length
  let count₂ := y.toList.length
  IO.println <| (Json.mkObj [("kernelImage", toJson sameKernel), ("publicImage", toJson identical), ("publicImports", toJson (pub₁ == pub₂)),
    ("parentNames", toJson count₁), ("candidateNames", toJson count₂), ("different", toJson mismatches),
    ("proofChanges", toJson proofChanges), ("examples", toJson examples)]).compress
  return if identical && pub₁ == pub₂ && count₁ == count₂ && mismatches == 0 && proofChanges == 0 && sameKernel then 0 else 2
