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


unsafe def readMany (paths : List String) : IO Infos := do
  let mut combined : Infos := {}
  for p in paths do
    for (n, item) in records (← readParts p) do
      checking (!(combined.contains n)) n "duplicate declaration"
      combined := combined.insert n item
  return combined

def codeValue (c : ConstantInfo) : Option Expr := Id.run do
  match c with
  | .thmInfo v => return some v.value
  | .defnInfo v => return some v.value
  | .opaqueInfo v => return some v.value
  | _ => return none

def became (x y : Expr) : Array String :=
  let a := x.getUsedConstantsAsSet
  (y.getUsedConstants.filter (!a.contains ·)).map Name.toString

public unsafe def main (args : List String) : IO Unit := do
  let current :: paths := args | throw (IO.userError "missing current module")
  let parts ← readParts current
  let projected ← readMany (paths.takeWhile (· != "--original"))
  let original ← readMany ((paths.dropWhile (· != "--original")).drop 1)
  let shared := records parts
  let some (publicPart, _) := parts[0]? | throw (IO.userError "missing public object data")
  for item in publicPart.constants do
    let n := item.name
    unless named n do continue
    let some s := shared.find? n | throw (IO.userError s!"missing shared body {n}")
    let some p := projected.find? n | throw (IO.userError s!"missing projected body {n}")
    let some o := original.find? n | throw (IO.userError s!"missing historical body {n}")
    let mut row := [("name", toJson n.toString), ("sharedHistoricalType", toJson (equalExpr s.type o.type)),
                    ("projectedHistoricalType", toJson (equalExpr p.type o.type))]
    if let some sv := codeValue s then
      let some pv := codeValue p | throw (IO.userError s!"missing value {n}")
      let some ov := codeValue o | throw (IO.userError s!"missing original value {n}")
      row := row ++ [("sharedHistoricalValue", toJson (equalExpr sv ov)),
                     ("projectedHistoricalValue", toJson (equalExpr pv ov)),
                     ("sharedProjectedValue", toJson (equalExpr sv pv)),
                     ("lostConstants", toJson (became pv sv)), ("gainedConstants", toJson (became sv pv))]
    IO.println (Json.mkObj row).compress
