module
import Lean
import all Lean.Util.CollectAxioms
open Lean
abbrev Parts := Array (ModuleData × CompactedRegion)
def readParts (p : String) : IO Parts :=
  readModuleDataParts (#[p, p ++ ".server", p ++ ".private"].map System.FilePath.mk)
def binderEq (a b : Name) : Bool :=
  a == b || (a.hasMacroScopes && b.hasMacroScopes && a.eraseMacroScopes == b.eraseMacroScopes)

abbrev Seen := Std.HashSet (ExprStructEq × ExprStructEq)
partial def same (x y : Expr) : StateM Seen Bool := do
  if Expr.equal x y then return true
  let k : ExprStructEq × ExprStructEq := (⟨x⟩, ⟨y⟩)
  if (← get).contains k then return true
  modify (·.insert k)
  match x,y with
  | .forallE a t v bi, .forallE b u w ci
  | .lam a t v bi, .lam b u w ci =>
    return bi == ci && binderEq a b && (← same t u) && (← same v w)
  | .letE a t v k d, .letE b u w q e =>
    return d == e && binderEq a b && (← same t u) && (← same v w) && (← same k q)
  | .app f a, .app g b => return (← same f g) && (← same a b)
  | .mdata a e, .mdata b f => return a == b && (← same e f)
  | .proj n i a, .proj m j b => return n == m && i == j && (← same a b)
  | _, _ => return false

def equalExpr (a b : Expr) : Bool := (same a b).run' {}
abbrev Axs := NameMap (Array Name)
unsafe def axRows (d : ModuleData) : Axs := Id.run do
  let mut m := {}
  for (n,r) in d.entries do
    if n == exportedAxiomsExt.name then
      for (k,v) in (unsafeCast r : Array (Name × Array Name)) do m := m.insert k v
  return m
abbrev Infos := NameMap ConstantInfo
def named (n : Name) := !isPrivateName n && !n.isInternal
def records (ps : Parts) : Infos := Id.run do
  let mut m := {}
  for (d,_) in ps do
    for c in d.constants do
      if named c.name then m := m.insert c.name c
  return m
def checking (b : Bool) (n : Name) (msg : String) : IO Unit := do
  unless b do throw (IO.userError s!"{msg} {n}")
def sameAx : Option (Array Name) → Option (Array Name) → Bool
  | none, none => true
  | some a, some b => a.all b.contains && b.all a.contains &&
      b.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n)
  | _,_ => false
def kindAndValue (a b : ConstantInfo) : Bool := Id.run do
  match a,b with
  | .axiomInfo a, .axiomInfo b => return a.isUnsafe == b.isUnsafe
  | .thmInfo a, .thmInfo b => return a.all == b.all
  | .opaqueInfo a, .opaqueInfo b =>
    return a.isUnsafe == b.isUnsafe && a.all == b.all && equalExpr a.value b.value
  | .defnInfo a, .defnInfo b =>
    return a.safety == b.safety && a.all == b.all && a.hints == b.hints && equalExpr a.value b.value
  | .inductInfo a, .inductInfo b => return { a with toConstantVal := b.toConstantVal } == b
  | .ctorInfo a, .ctorInfo b => return { a with toConstantVal := b.toConstantVal } == b
  | .recInfo a, .recInfo b => return { a with toConstantVal := b.toConstantVal, rules := b.rules } == b &&
      a.rules.length == b.rules.length && (a.rules.zip b.rules).all (fun (x,y) =>
        x.ctor == y.ctor && x.nfields == y.nfields && equalExpr x.rhs y.rhs)
  | .quotInfo a, .quotInfo b => return a.kind == b.kind
  | _, _ => return false

public unsafe def main (args : List String) : IO Unit := do
  let newPath :: oldPaths := args | throw (IO.userError "missing paths")
  let right ← readParts newPath
  let some (d, _) := right[0]? | throw (IO.userError "missing new module")
  let pub : Infos := d.constants.foldl (fun m c => m.insert c.name c) {}
  let full := records right
  let axs := axRows d
  let mut names : NameSet := {}
  let mut types := 0
  let mut data := 0
  let mut thms := 0
  let mut proofs := 0
  let mut axCount := 0
  for p in oldPaths do
    let left ← readParts p
    let some (lp, _) := left[0]? | throw (IO.userError "missing old module")
    let ax := axRows lp
    let oldFull := records left
    for c in lp.constants do
      let name := c.name
      unless named name do continue
      checking (!names.contains name) name "duplicate original name"
      names := names.insert name
      let some v := pub.find? name | throw (IO.userError s!"missing public {name}")
      checking (c.levelParams == v.levelParams && equalExpr c.type v.type) name "public type"
      checking (kindAndValue c v) name "public kind or data"
      if Expr.equal c.type v.type then types := types+1
      checking (sameAx (ax.find? name) (axs.find? name)) name "axiom set"
      if (ax.find? name).isSome then axCount := axCount + 1
      let some a := oldFull.find? name | throw (IO.userError s!"missing original body {name}")
      let some b := full.find? name | throw (IO.userError s!"missing new body {name}")
      checking (a.levelParams == b.levelParams && equalExpr a.type b.type && kindAndValue a b)
        name "full type, data or declaration kind"
      match a,b with
      | .thmInfo x,.thmInfo y =>
        checking ((ax.find? name).isSome) name "missing theorem axiom record"
        thms := thms+1
        if equalExpr x.value y.value then proofs := proofs+1
      | .defnInfo ..,.defnInfo .. | .opaqueInfo ..,.opaqueInfo .. => data := data+1
      | _,_ => pure ()
  let total := (d.constants.filter fun c => named c.name).size
  unless total == names.toList.length do throw (IO.userError s!"extra public {total} {names.toList.length}")
  IO.println s!"{total}\t{types}\t{data}\t{thms}\t{proofs}\t{axCount}"
