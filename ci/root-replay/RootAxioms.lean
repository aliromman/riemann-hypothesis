import Lean

open Lean

unsafe def main (args : List String) : IO Unit := do
  let file :: targets := args | throw <| IO.userError "need Main.olean and theorem names"
  let (p, _) ← readModuleData file
  let some (table, rows) := p.entries.find? (fun e => e.1.toString == "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt")
    | throw <| IO.userError s!"missing compiler axiom table: {p.entries.map (·.1)}"
  IO.println s!"axiom table {table}"
  let entries : Array (Name × Array Name) := unsafeCast rows
  for t in targets do
    let some (_, axs) := entries.find? (fun e => e.1 == t.toName)
      | throw <| IO.userError s!"missing axiom row for {t}"
    unless axs.size == 3 && #[``propext, ``Quot.sound, ``Classical.choice].all axs.contains do
      throw <| IO.userError s!"unexpected axiom set for {t}: {axs}"
    IO.println s!"{t}\t{axs}"
