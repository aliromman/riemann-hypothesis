import Lean.Elab.Import

open Lean

private def flags (xs : Array Import) : Json :=
  Json.mkObj [("total", toJson xs.size), ("exported", toJson (xs.filter (·.isExported)).size),
    ("meta", toJson (xs.filter (·.isMeta)).size), ("all", toJson (xs.filter (·.importAll)).size)]

private def sourceImports (path : System.FilePath) : IO (Array Import) := do
  let (xs, _, errors) ← Elab.parseImports (← IO.FS.readFile path) (some path.toString)
  if errors.hasErrors then throw <| IO.userError s!"invalid import header in {path}"
  return xs

unsafe def main (args : List String) : IO Unit := do
  let [spec] := args | throw <| IO.userError "expected TSV"
  for row in (← IO.FS.readFile spec).splitOn "\n" do
    unless row.isEmpty do
      let [name, _, before, after, _, ips, ipf, _, _, actualSig, actualFull] := row.splitOn "\t"
        | throw <| IO.userError "invalid IR header row"
      let old ← sourceImports before
      let fresh ← sourceImports after
      let parent ← readModuleDataParts #[ips, ipf]
      let candidate ← readModuleDataParts #[actualSig, actualFull]
      let mut parts := #[]
      for i in [0:2] do
        let some (p, _) := parent[i]? | throw <| IO.userError "missing parent IR part"
        let some (q, _) := candidate[i]? | throw <| IO.userError "missing compiled IR part"
        let kind ← if p.imports == old && q.imports == fresh then pure "source"
          else if p.imports.isEmpty && q.imports.isEmpty then pure "empty"
          else throw <| IO.userError s!"a stored import or flag differs from the actual source in {name}"
        parts := parts.push <| Json.mkObj [("kind", toJson kind), ("parent", flags p.imports), ("candidate", flags q.imports)]
      IO.println <| (Json.mkObj [("module", toJson name), ("parts", Json.arr parts)]).compress
