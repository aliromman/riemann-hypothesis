import Lean

open Lean

private def need (data : ModuleData) (name : Name) : IO ConstantInfo := do
  let some info := data.constants.find? (·.name == name) | throw <| IO.userError s!"missing {name}"
  return info

unsafe def main (args : List String) : IO Unit := do
  let file :: challengeFile :: statementsFile :: targets := args
    | throw <| IO.userError "expected fresh Main, Challenge, Statements and theorem names"
  let (solution, _) ← readModuleData file
  let (challenge, _) ← readModuleData challengeFile
  let (statements, _) ← readModuleData statementsFile
  for t in targets do
    let a ← need solution t.toName
    let b ← need challenge t.toName
    unless a.levelParams == b.levelParams && Expr.equal a.type b.type do
      throw <| IO.userError s!"different theorem statement: {t}"
    IO.println s!"claim {t}"
  for s in [`RiemannZetaZerosOnLine, `DirichletLNonvanishingRightOfHalf, `DirichletLZerosOnLine, `PrimitiveDirichletLZerosOnLine] do
    let some av := (← need statements s).value? | throw <| IO.userError s!"missing body: {s}"
    let some bv := (← need challenge s).value? | throw <| IO.userError s!"missing challenge body: {s}"
    unless av == bv do throw <| IO.userError s!"different proposition definition: {s}"
    IO.println s!"definition {s}  exact={Expr.equal av bv}  alphaEquivalent={av == bv}"
