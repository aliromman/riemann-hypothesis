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

private partial def bindersAgree (a b : Expr) : Bool :=
  match a, b with
  | .mdata _ x, _ => bindersAgree x b
  | _, .mdata _ y => bindersAgree a y
  | .forallE n t x i, .forallE m s y j => i == j && binderEq n m && bindersAgree t s && bindersAgree x y
  | .forallE .., _ | _, .forallE .. => false
  | _, _ => true

private def sameRecursorFields (x y : RecursorVal) : Bool :=
  { x with toConstantVal := y.toConstantVal, rules := y.rules } == y &&
    x.rules.length == y.rules.length && (x.rules.zip y.rules).all fun (a,b) => a.ctor == b.ctor && a.nfields == b.nfields

private def metadataAgrees (a b : ConstantInfo) : Bool :=
  match a, b with
  | .defnInfo x, .defnInfo y => x.safety == y.safety && x.hints == y.hints && x.all == y.all
  | .opaqueInfo x, .opaqueInfo y => x.isUnsafe == y.isUnsafe && x.all == y.all
  | .recInfo x, .recInfo y =>
    sameRecursorFields x y
  | _, _ => kindAndValue a b

private def conversion (env : Environment) (a b : Expr) : String := Id.run do
  let .ok x := Kernel.check env {} a | return "stock expression does not typecheck"
  let .ok y := Kernel.check env {} b | return "candidate expression does not typecheck"
  let .ok true := Kernel.isDefEq env {} x y | return "different inferred types"
  match Kernel.isDefEq env {} a b with
  | .ok true => return "defeq"
  | .ok false => return "different"
  | .error _ => return "kernel error"

private def difference (env : Option Environment) (n : Name) (field : String) (a b : Expr) : Json :=
  Json.mkObj [("declaration", toJson n.toString), ("field", toJson field),
    ("conversion", toJson (env.map (fun e => conversion e a b) |>.getD "pending"))]

private unsafe def audit (mod oldPath newPath : String) (env : Option Environment) (includeProofs : Bool) : IO Unit := do
  let oldParts ← readParts oldPath
  let newParts ← readParts newPath
  let some (oldData, _) := oldParts[0]? | throw <| IO.userError "missing original public data"
  let some (newData, _) := newParts[0]? | throw <| IO.userError "missing candidate public data"
  let original := records oldParts
  let revised := records newParts
  let oldPub := (oldData.constants.filter (fun c => named c.name)).map (·.name)
  let newPub := (newData.constants.filter (fun c => named c.name)).map (·.name)
  let oldAx := axRows oldData
  let newAx := axRows newData
  let mut bad : Array String := #[]
  let mut terms : Array Json := #[]
  let mut rawTypes := 0
  let mut defs := 0
  let mut rawDefs := 0
  let mut thms := 0
  let mut rawProofs := 0
  let mut axCount := 0
  unless oldPub.size == newPub.size && oldPub.all newPub.contains do
    bad := bad.push "exported declaration set changed"
  for name in oldPub do
    let some a := original.find? name | throw <| IO.userError s!"missing original {name}"
    let some b := revised.find? name | bad := bad.push s!"missing candidate {name}"; continue
    if a.levelParams != b.levelParams || !metadataAgrees a b || !bindersAgree a.type b.type then
      bad := bad.push s!"kind, universe parameters, binders or declaration metadata changed: {name}"
    if equalExpr a.type b.type then rawTypes := rawTypes + 1
    else terms := terms.push (difference env name "type" a.type b.type)
    let ax := oldAx.find? name
    unless sameAx ax (newAx.find? name) do bad := bad.push s!"axiom set: {name}"
    if ax.isSome then axCount := axCount + 1
    match a, b with
    | .thmInfo x, .thmInfo y =>
      thms := thms + 1
      if ax.isNone then bad := bad.push s!"missing theorem axiom record: {name}"
      if equalExpr x.value y.value then rawProofs := rawProofs + 1
      else if includeProofs then terms := terms.push (difference env name "proof" x.value y.value)
    | .defnInfo .., .defnInfo .. | .opaqueInfo .., .opaqueInfo .. =>
      defs := defs + 1
      let some x := a.value? (allowOpaque := true) | throw <| IO.userError s!"missing original body {name}"
      let some y := b.value? (allowOpaque := true) | throw <| IO.userError s!"missing candidate body {name}"
      if equalExpr x y then rawDefs := rawDefs + 1
      else terms := terms.push (difference env name "definition" x y)
    | .recInfo x, .recInfo y =>
      for (oldRule, newRule) in x.rules.zip y.rules do
        if !equalExpr oldRule.rhs newRule.rhs then
          terms := terms.push (difference env name ("recursor rule " ++ oldRule.ctor.toString) oldRule.rhs newRule.rhs)
    | _, _ => pure ()
  IO.println <| Json.compress <| Json.mkObj [
    ("module", toJson mod), ("public", toJson oldPub.size), ("rawTypes", toJson rawTypes),
    ("definitions", toJson defs), ("rawDefinitions", toJson rawDefs), ("theorems", toJson thms),
    ("rawProofs", toJson rawProofs), ("axiomRecords", toJson axCount), ("structural", toJson bad),
    ("terms", Json.arr terms)]

public unsafe def main (args : List String) : IO Unit := do
  let [mode, manifest] := args | throw <| IO.userError "expected scan, scan-proofs or kernel, then a tab-separated manifest"
  unless mode == "scan" || mode == "scan-proofs" || mode == "kernel" do throw <| IO.userError "unknown mode"
  initSearchPath (← findSysroot)
  for line in ← IO.FS.lines manifest do
    let [mod, before, after] := line.splitOn "\t" | throw <| IO.userError "expected module, original object, candidate object"
    if mode == "kernel" then
      withImportModules #[{module := mod.toName, importAll := true}] {} fun env =>
        audit mod before after (some env) false
    else
      audit mod before after none (mode == "scan-proofs")
