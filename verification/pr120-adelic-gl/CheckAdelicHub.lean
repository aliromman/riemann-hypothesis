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
  let [stock,candidate,mod] := args | throw (IO.userError "expected two objects and a module")
  initSearchPath (← findSysroot)
  let a ← readParts stock
  let b ← readParts candidate
  let some (da,_) := a[0]? | throw (IO.userError "missing stock module")
  let some (db,_) := b[0]? | throw (IO.userError "missing candidate module")
  let old := da.constants.filter fun c => named c.name
  let new := db.constants.filter fun c => named c.name
  let oldNames := old.map (·.name)
  let oldAx := axRows da
  let newAx := axRows db
  let changes := new.filter fun c => !oldNames.contains c.name ||
    c.name == `GroundTheory.Automorphic.AdelicGLn.locallyCompactSpace
  let permitted := #[`propext, `Quot.sound, `Classical.choice]
  withImportModules #[{module := mod.toName, importAll := true}] {} fun env => do
    for c in old do
      let some d := new.find? (·.name == c.name) | throw (IO.userError s!"missing {c.name}")
      checking (c.levelParams == d.levelParams && equalExpr c.type d.type) c.name "existing type"
      checking (sameAx (oldAx.find? c.name) (newAx.find? c.name)) c.name "existing axiom set"
    for c in changes do
      let .ok sort := Kernel.check env {} c.type | throw (IO.userError s!"ill-typed {c.name}")
      let .ok true := Kernel.isDefEq env {} sort (.sort .zero) | throw (IO.userError s!"expected a proposition {c.name}")
      let some xs := newAx.find? c.name | throw (IO.userError s!"missing axiom set {c.name}")
      checking (xs.all permitted.contains) c.name "additional axiom"
    unless changes.size == 36 && new.size == old.size + 35 do throw (IO.userError s!"unexpected declaration counts {old.size} {new.size} {changes.size}")
    IO.println s!"existing {old.size} candidate {new.size} proposition-valued instances {changes.size}"
