import Lean
import Lean.Compiler.IR.NormIds

open Lean Lean.IR

private partial def permute (target : JoinPointId) : FnBody → FnBody
  | .jdecl j params rhs rest =>
    if j == target then
      let a := params[0]!.x
      let b := params[1]!.x
      let rename := fun x => if x == a then b else if x == b then a else x
      let params := (params.swapIfInBounds 0 1).map fun p => { p with x := rename p.x }
      .jdecl j params (MapVars.mapFnBody rename (permute target rhs)) (permute target rest)
    else
      .jdecl j params (permute target rhs) (permute target rest)
  | .jmp j xs => .jmp j (if j == target then xs.swapIfInBounds 0 1 else xs)
  | .case n x t alts => .case n x t (alts.map fun alt => alt.modifyBody (permute target))
  | b => if b.isTerminal then b else b.setBody (permute target b.body)

private def change (d : IR.Decl) (j : Nat) : IR.Decl :=
  if d.name != `Formalism.MainNotions.G.SymmetricFormBlocks.fL then d
  else match d with
    | .fdecl f xs ty b info => .fdecl f xs ty (permute ⟨j⟩ b) info
    | .extern .. => d

private unsafe def save (part₀ part : ModuleData) (out : System.FilePath) (j : Nat) : IO Unit := do
  let ext := part.entries.map fun (name, es) =>
    if name == IR.declMapExt.name then
      let ds : Array IR.Decl := unsafeCast es
      (name, unsafeCast (ds.map fun d => change d j))
    else (name, es)
  let mod := `Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationOverZpHolds.ir
  saveModuleDataParts mod #[(out.withExtension "ir.sig", part₀), (out.withExtension "ir", { part with entries := ext })]

unsafe def main (args : List String) : IO Unit := do
  let [parent, candidate, w] := args | throw <| IO.userError "expected public parent, candidate and output path"
  let p := System.FilePath.mk parent
  let q := System.FilePath.mk candidate
  let dir := System.FilePath.mk w
  let data ← readModuleDataParts #[p.withExtension "ir.sig", p.withExtension "ir"]
  let some (sig, _) := data[0]? | throw <| IO.userError "missing IR signature"
  let some (body, _) := data[1]? | throw <| IO.userError "missing IR body"
  let nochange := dir / "control"
  let changed := dir / "permuted"
  save sig body nochange 100000
  save sig body changed 3
  for (tag, original, new) in [("signature-control", p.withExtension "ir.sig", nochange.withExtension "ir.sig"),
        ("body-control", p.withExtension "ir", nochange.withExtension "ir"),
        ("signature-permutation", q.withExtension "ir.sig", changed.withExtension "ir.sig"),
        ("body-permutation", q.withExtension "ir", changed.withExtension "ir")] do
    let equal := (← IO.FS.readBinFile original) == (← IO.FS.readBinFile new)
    IO.println s!"{tag} {equal}"
    if !equal then throw <| IO.userError s!"unexplained compiler difference: {tag}"
