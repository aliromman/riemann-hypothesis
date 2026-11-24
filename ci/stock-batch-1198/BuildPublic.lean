import Lean.Elab.Import

open Lean

private def importsOf (path : System.FilePath) : IO (Array Import) := do
  let (imports, _, diagnostics) ← Elab.parseImports (← IO.FS.readFile path) (some path.toString)
  if diagnostics.hasErrors then throw <| IO.userError s!"the pinned Lean parser rejected {path}"
  return imports

private def newHeader (p : ModuleData) (fresh : Array Import) : ModuleData :=
  let reuse (i : Import) := (p.imports.find? (· == i)).getD i
  { p with imports := fresh.map reuse }

unsafe def rebuild (fields : List String) : IO Unit := do
  let name :: pub :: orig :: candidate :: result :: ir := fields | throw <| IO.userError "incomplete row"
  let (p, _) ← readModuleData pub
  let old ← importsOf orig
  unless old == p.imports do throw <| IO.userError s!"parent artifact and source have different imports in {name}"
  let fresh ← importsOf candidate
  unless old.filter (·.isExported) == fresh.filter (·.isExported) do
    throw <| IO.userError s!"public imports changed in {name}"
  saveModuleDataParts name.toName #[(result, newHeader p fresh)]
  if ir.isEmpty then return
  let [si, fi, so, fo] := ir | throw <| IO.userError "incomplete IR paths"
  let parts ← readModuleDataParts #[si, fi]
  let mut writes : Array (System.FilePath × ModuleData) := #[]
  for i in [0:2] do
    let some (q, _) := parts[i]? | throw <| IO.userError "missing IR part"
    let q' ← if q.imports == old then pure (newHeader q fresh)
      else if q.imports.isEmpty then pure q
      else throw <| IO.userError s!"parent IR part {i} has independent import references in {name}"
    writes := writes.push (System.FilePath.mk (if i == 0 then so else fo), q')
  saveModuleDataParts (name.toName ++ `ir) writes

unsafe def main (args : List String) : IO Unit := do
  let [rows] := args | throw <| IO.userError "expected TSV"
  for row in (← IO.FS.readFile rows).splitOn "\n" do
    unless row.isEmpty do rebuild (row.splitOn "\t")
