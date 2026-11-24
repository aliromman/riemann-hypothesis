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


def allItems (ps : Parts) : Infos := Id.run do
  let mut m := {}
  for (d, _) in ps do
    for c in d.constants do m := m.insert c.name c
  return m

def relocate (rename : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => (rename.find? n).map fun p => .const p us
    | _ => none

def val? (v : ConstantInfo) : Option Expr :=
  match v with
  | .thmInfo x => some x.value
  | .defnInfo x => some x.value
  | .opaqueInfo x => some x.value
  | _ => none

public unsafe def main (args : List String) : IO Unit := do
  let old :: pieces := args | throw (IO.userError "missing old module")
  let ps ← readParts old
  let some (pub, _) := ps[0]? | throw (IO.userError "missing public data")
  let before := allItems ps
  let mut after : Infos := {}
  let mut byUser : NameMap (Array Name) := {}
  for p in pieces do
    for (n,c) in allItems (← readParts p) do
      checking (!(after.contains n)) n "duplicate split declaration"
      after := after.insert n c
      if let some user := privateToUserName? n then
        byUser := byUser.insert user ((byUser.find? user).getD #[] |>.push n)
  let mut rename : NameMap Name := {}
  for (n,_) in before do
    if after.contains n then continue
    if let some u := privateToUserName? n then
      if let some #[only] := byUser.find? u then
        rename := rename.insert n only
  let mut used : NameSet := {}
  let mut examined : NameSet := {}
  let mut pending : Array Name := #[]
  let mut rawChanges := 0
  for item in pub.constants do
    let n := item.name
    unless named n do continue
    let some a := before.find? n | throw (IO.userError s!"missing original {n}")
    let some b := after.find? n | throw (IO.userError s!"missing new {n}")
    if let some av := val? a then
      let some bv := val? b | throw (IO.userError s!"missing new body {n}")
      if !equalExpr av bv then
        rawChanges := rawChanges + 1
        checking (equalExpr (relocate rename av) bv) n "proof differs after name replacement"
        pending := pending ++ av.getUsedConstants.filter before.contains
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if examined.contains n then continue
    examined := examined.insert n
    let some a := before.find? n | throw (IO.userError s!"missing private source {n}")
    let dest := (rename.find? n).getD n
    let some b := after.find? dest | throw (IO.userError s!"missing private destination {dest}")
    checking (a.levelParams == b.levelParams && equalExpr (relocate rename a.type) b.type) n "helper type"
    let compatible := match a,b with
      | .thmInfo _, .thmInfo _ => true
      | .defnInfo x, .defnInfo y => x.safety == y.safety && x.hints == y.hints
      | .opaqueInfo x, .opaqueInfo y => x.isUnsafe == y.isUnsafe
      | _,_ => kindAndValue a b
    checking compatible n "helper kind"
    pending := pending ++ a.type.getUsedConstants.filter before.contains
    if let some av := val? a then
      let some bv := val? b | throw (IO.userError s!"helper has no value {dest}")
      checking (equalExpr (relocate rename av) bv) n "helper value"
      pending := pending ++ av.getUsedConstants.filter before.contains
    if n != dest then used := used.insert n
  IO.println s!"{rawChanges}\t{examined.toList.length}\t{used.toList.length}"
