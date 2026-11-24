module
import Lean
import all Lean.Util.CollectAxioms
open Lean

unsafe def rows (p : System.FilePath) : IO (Array (Name × Array Name)) := do
  let some (data, _) := (← readModuleDataParts #[p])[0]?
    | throw <| IO.userError s!"Missing module data in {p}"
  let some (_, entries) := data.entries.find? (·.1 == exportedAxiomsExt.name)
    | throw <| IO.userError s!"Missing axiom table in {p}"
  return unsafeCast entries

public unsafe def main (args : List String) : IO Unit := do
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  for p in args do
    let decls ← rows p
    if decls.isEmpty then throw <| IO.userError s!"Empty axiom table in {p}"
    for (name, deps) in decls do
      unless deps.all allowed.contains do throw <| IO.userError s!"Unexpected axiom for {name}: {deps}"
    IO.println s!"{p}\t{decls.size}"
