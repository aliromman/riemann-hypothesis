import Lean

open Lean

private unsafe def scan (src out : System.FilePath) : IO Unit := do
  let parts ← readModuleDataParts #[src.withExtension "ir.sig", src.withExtension "ir"]
  let some (part, _) := parts[1]? | throw <| IO.userError "missing compiler IR"
  let stem := `InspectIR
  IO.FS.createDirAll out
  saveModuleData (out / "fields.bin") stem { part with entries := #[] }
  let mut groups := #[]
  for h : i in [:part.entries.size] do
    let (ext, values) := part.entries[i]
    let mut names := #[]
    for hj : j in [:values.size] do
      let v := values[j]
      let label := s!"group-{i}-row-{j}"
      saveModuleData (out / (label ++ ".bin")) stem { (default : ModuleData) with entries := #[(ext, #[v])] }
      if ext == IR.declMapExt.name then
        let d : IR.Decl := unsafeCast v
        names := names.push d.name.toString
        IO.FS.writeFile (out / (label ++ ".txt")) (toString d)
      else
        names := names.push label
    groups := groups.push (ext.toString, names)
  let fields := Json.mkObj [("imports", toJson (part.imports.map (·.module.toString))),
    ("constNames", toJson (part.constNames.map (·.toString))),
    ("extraConstNames", toJson (part.extraConstNames.map (·.toString))),
    ("groups", toJson groups)]
  IO.FS.writeFile (out / "entries.json") fields.compress

unsafe def main (args : List String) : IO Unit := do
  let [parent, candidate, out] := args | throw <| IO.userError "expected public parent, candidate and output path"
  scan parent ((out : System.FilePath) / "before")
  scan candidate ((out : System.FilePath) / "after")
