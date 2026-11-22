module
import Lean
import all Lean.Util.CollectAxioms
import Lake.Build.Trace

open Lean

structure Artifact where
  name : String
  path : String
  hashes : Array String
  source : Option String := none
  sourceHash : Option String := none
  selected : Option (List String) := none
  deriving FromJson

structure Comparison where
  current : Artifact
  originals : Array Artifact
  deriving FromJson

structure Declarations where
  full : NameMap ConstantInfo := {}
  visible : NameSet := {}
  axioms : NameMap (Array Name) := {}
  regions : Array CompactedRegion := #[]

-- This extension stores an array of (declaration name, axiom names) in the public part.
private unsafe def readAxioms (data : ModuleData) : NameMap (Array Name) := Id.run do
  let some (_, entries) := data.entries.find? (·.1 == exportedAxiomsExt.name) | return {}
  let rows : Array (Name × Array Name) := unsafeCast entries
  return rows.foldl (fun result (n, axioms) => result.insert n axioms) {}

private unsafe def loadArtifact (artifact : Artifact) : IO Declarations := do
  if let some source := artifact.source then
    let some expected := artifact.sourceHash | throw <| IO.userError "source hash missing"
    unless (← Lake.computeTextFileHash source).toString == expected do
      throw <| IO.userError s!"stale source in {artifact.name}"
  unless artifact.hashes.size == 1 || artifact.hashes.size == 3 do
    throw <| IO.userError s!"incomplete module parts for {artifact.name}"
  let paths := (#["", ".server", ".private"].extract 0 artifact.hashes.size).map fun s => System.FilePath.mk (artifact.path ++ s)
  for (path, expected) in paths.zip artifact.hashes do
    unless (← Lake.computeBinFileHash path).toString == expected do
      throw <| IO.userError s!"unexpected contents of {path}"
  let parts ← readModuleDataParts paths
  let some (publicData, _) := parts[0]? | throw <| IO.userError "empty module data"
  unless publicData.isModule == (parts.size == 3) do
    throw <| IO.userError s!"unexpected export level in {artifact.path}"
  let mut byName := {}
  for (data, _) in parts do
    for c in data.constants do byName := byName.insert c.name c
  if let some wanted := artifact.selected then
    let mut subset := {}
    for name in wanted do
      let some info := byName.find? name.toName | throw <| IO.userError s!"missing original export {name}"
      subset := subset.insert info.name info
    byName := subset
  return { full := byName, visible := .ofList publicData.constNames.toList, axioms := readAxioms publicData, regions := parts.map (·.2) }

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

private def transparency : ReducibilityHints → Nat
  | .opaque => 0 | .abbrev => 1 | .regular _ => 2

private def declarationFlagsMatch (renames : NameMap Name) (a b : ConstantInfo) : Bool := Id.run do
  let rename := fun n => (renames.find? n).getD n
  return match a, b with
  | .defnInfo x, .defnInfo y =>
    x.safety == y.safety && transparency x.hints == transparency y.hints && x.all.map rename == y.all
  | .thmInfo x, .thmInfo y => x.all.map rename == y.all
  | .opaqueInfo x, .opaqueInfo y => x.all.map rename == y.all
  | .inductInfo x, .inductInfo y =>
    x.numParams == y.numParams && x.numIndices == y.numIndices && x.all.map rename == y.all &&
    x.ctors.map rename == y.ctors && x.numNested == y.numNested && x.isRec == y.isRec && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y =>
    rename x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams && x.numFields == y.numFields
  | .recInfo x, .recInfo y =>
    x.all.map rename == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
    x.numMotives == y.numMotives && x.numMinors == y.numMinors && x.k == y.k &&
    x.rules.map (fun r => (rename r.ctor, r.nfields)) == y.rules.map (fun r => (r.ctor, r.nfields))
  | .quotInfo x, .quotInfo y => x.kind == y.kind
  | .axiomInfo _, .axiomInfo _ => true
  | _, _ => false

private partial def binderNames : Expr → List Name
  | .forallE n _ body _ => n.eraseMacroScopes :: binderNames body
  | .mdata _ body => binderNames body
  | _ => []

private partial def functionBindersMatch (a b : Expr) : Bool :=
  match a, b with
  | .mdata _ x, _ => functionBindersMatch x b
  | _, .mdata _ y => functionBindersMatch a y
  | .forallE _ d x i, .forallE _ e y j => i == j && functionBindersMatch d e && functionBindersMatch x y
  | .forallE .., _ | _, .forallE .. => false
  | _, _ => true

private def bodies (c : ConstantInfo) : List Expr :=
  match c with
  | .recInfo v => v.rules.map (·.rhs)
  | _ => (c.value? (allowOpaque := true)).toList

private def newName (origin target name : Name) (after : NameMap ConstantInfo) : Name := Id.run do
  for originalPrefix in [mkPrivateNameCore origin .anonymous, mkPrivateNameCore (`src ++ origin) .anonymous] do
    if originalPrefix.isPrefixOf name then
      let possible := [mkPrivateNameCore target .anonymous, mkPrivateNameCore (`src ++ target) .anonymous]
        |>.map (fun p => name.replacePrefix originalPrefix p) |>.filter after.contains
      if let [one] := possible then return one
  return name

private partial def canonical (renames : NameMap Name) (e : Expr) : StateM (ExprStructMap Expr) Expr := do
  if let some result := (← get).get? ⟨e⟩ then return result
  let result ← match e with
    | .forallE _ d b bi => pure <| .forallE .anonymous (← canonical renames d) (← canonical renames b) bi
    | .lam _ d b bi => pure <| .lam .anonymous (← canonical renames d) (← canonical renames b) bi
    | .letE _ t v b nd => pure <| .letE .anonymous (← canonical renames t) (← canonical renames v) (← canonical renames b) nd
    | .app f a => pure <| .app (← canonical renames f) (← canonical renames a)
    | .proj n i b => pure <| .proj ((renames.find? n).getD n) i (← canonical renames b)
    | .mdata _ b => canonical renames b
    | .sort u => pure <| .sort u.normalize
    | .const n ls => pure <| .const ((renames.find? n).getD n) (ls.map Level.normalize)
    | _ => pure e
  modify (·.insert ⟨e⟩ result)
  return result

private def same (renames : NameMap Name) (before after : Expr) : Bool :=
  (Expr.equal before after && !before.getUsedConstants.any renames.contains) || Expr.equal ((canonical renames before).run' {}) ((canonical {} after).run' {})

private def describe : Expr → String
  | .bvar n => s!"bvar {n}" | .sort l => s!"sort {l}" | .const n ls => s!"{n} {ls}"
  | .proj n i _ => s!"projection {n} {i}" | .lit v => s!"{repr v}" | .app .. => "application"
  | .forallE _ _ _ bi => s!"forall {repr bi}" | .lam _ _ _ bi => s!"lambda {repr bi}"
  | .letE _ _ _ _ nd => s!"let {nd}" | .mdata .. => "metadata" | .fvar .. => "fvar" | .mvar .. => "mvar"

private partial def firstChange (a b : Expr) : String × String := Id.run do
  let children := match a, b with
    | .app f x, .app g y => [(f,g), (x,y)]
    | .lam _ d x i, .lam _ e y j | .forallE _ d x i, .forallE _ e y j => if i == j then [(d,e),(x,y)] else []
    | .letE _ t v x n, .letE _ u w y m => if n == m then [(t,u),(v,w),(x,y)] else []
    | .proj n i x, .proj m j y => if n == m && i == j then [(x,y)] else []
    | _, _ => []
  for (x,y) in children do
    if !Expr.equal x y then return firstChange x y
  return (describe a, describe b)

private def output (kind mod decl field : String) (lost added : List String := []) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj [("event", toJson kind), ("module", toJson mod),
    ("declaration", toJson decl), ("field", toJson field), ("lost", toJson lost), ("gained", toJson added)]

private def compareRefs (renames : NameMap Name) (target : String) (n : Name)
    (field : String) (before after : List Expr) : IO Nat := do
  let oldNames := before.foldl (fun s e => e.foldConsts s fun c acc => acc.insert ((renames.find? c).getD c)) ({} : NameSet)
  let newNames := after.foldl (fun s e => s ++ e.getUsedConstantsAsSet) ({} : NameSet)
  let oldOnly := oldNames.toList.filter (!newNames.contains ·)
  let newOnly := newNames.toList.filter (!oldNames.contains ·)
  if oldOnly.isEmpty && newOnly.isEmpty then return 0
  else
    output "difference" target n.toString field (oldOnly.map toString) (newOnly.map toString)
    return 1

@[noinline] private unsafe def inspect (aliases : NameMap Name) (comparison : Comparison) : IO (Array CompactedRegion) := do
  let current := comparison.current.name
  let target := current.toName
  let new ← loadArtifact comparison.current
  let old ← comparison.originals.mapM loadArtifact
  let mut regions := new.regions
  let mut owners : NameMap Nat := {}
  let mut renames := aliases
  for (part, entry) in old.zip comparison.originals do
    regions := regions ++ part.regions
    for (n, _) in part.full do
      let k := newName entry.name.toName target n new.full
      owners := owners.insert k ((owners.find? k).getD 0 + 1)
  for (part, entry) in old.zip comparison.originals do
    for (n, _) in part.full do
      let k := newName entry.name.toName target n new.full
      if n != k && owners.find? k == some 1 && new.full.contains k then renames := renames.insert n k
  let mut count := 0
  let mut axiomSets := 0
  let mut flagged := 0
  for (part, entry) in old.zip comparison.originals do
    for (n, original) in part.full do
      let k := newName entry.name.toName target n new.full
      if owners.find? k != some 1 then
        output "difference" current n.toString "ambiguous-original-owner"
        flagged := flagged + 1
        continue
      let some updated := new.full.find? k | do
        output "difference" current n.toString "missing-declaration"
        flagged := flagged + 1
        continue
      count := count + 1
      if kind original != kind updated || original.isUnsafe != updated.isUnsafe || !declarationFlagsMatch renames original updated || part.visible.contains n != new.visible.contains k then
        output "difference" current n.toString "declaration-flags-or-visibility"
        flagged := flagged + 1
      if part.visible.contains n && new.visible.contains k then
        match part.axioms.find? n, new.axioms.find? k with
        | some oldAxioms, some newAxioms =>
          axiomSets := axiomSets + 1
          let before := oldAxioms.map (fun ax => (renames.find? ax).getD ax)
          let lost := before.filter (!newAxioms.contains ·)
          let gained := newAxioms.filter (!before.contains ·)
          unless lost.isEmpty && gained.isEmpty do
            output "difference" current n.toString "axiom-dependencies" (lost.toList.map toString) (gained.toList.map toString)
            flagged := flagged + 1
        | _, _ =>
          output "difference" current n.toString "axiom-table-entry-unavailable"
          flagged := flagged + 1
      if part.visible.contains n && !isPrivateName n && !n.isInternal && binderNames original.type != binderNames updated.type then
        output "difference" current n.toString "binder-names" ((binderNames original.type).map toString) ((binderNames updated.type).map toString)
        flagged := flagged + 1
      let rebase := fun (e : Expr) => e.instantiateLevelParams original.levelParams (updated.levelParams.map .param)
      if original.levelParams.length != updated.levelParams.length || !same renames (rebase original.type) updated.type then
        let (left, right) := firstChange ((canonical renames (rebase original.type)).run' {}) ((canonical {} updated.type).run' {})
        output "difference" current n.toString "type" [left] [right]
        flagged := flagged + 1
      flagged := flagged + (← compareRefs renames current n "type-references" [original.type] [updated.type])
      let a := bodies original
      let b := bodies updated
      flagged := flagged + (← compareRefs renames current n "body-references" a b)
      if a.length != b.length || !(a.zip b).all (fun (o, u) => same renames (rebase o) u) then
        let change := (a.zip b).find? (fun (o, u) => !same renames (rebase o) u)
        let (left, right) := change.map (fun (o, u) => firstChange ((canonical renames (rebase o)).run' {}) ((canonical {} u).run' {})) |>.getD (s!"{a.length} expression(s)", s!"{b.length} expression(s)")
        let field := if kind original == "theorem" then "proof-term" else "body"
        output "difference" current n.toString field [left] [right]
        flagged := flagged + 1
  for (n, _) in new.full do
    if !owners.contains n then
      output "difference" current n.toString "additional-declaration"
      flagged := flagged + 1
  IO.println <| Json.compress <| Json.mkObj [("event", toJson "module"),("module", toJson current),
    ("aligned", toJson count), ("comparedAxiomSets", toJson axiomSets), ("findings", toJson flagged)]
  return regions

structure AliasCase where
  wrapper : Artifact
  name : String
  provider : Artifact
  targetName : String
  indexHash : String
  deriving FromJson

@[noinline] private unsafe def certifyAlias (spec : AliasCase) : IO (Array CompactedRegion) := do
  let checkedIndex := (System.FilePath.mk spec.wrapper.path).withExtension "ilean"
  unless (← Lake.computeBinFileHash checkedIndex).toString == spec.indexHash do
    throw <| IO.userError "old compiler reference index hash differs"
  let wrapper ← loadArtifact spec.wrapper
  let provider ← loadArtifact spec.provider
  let name := spec.name.toName
  let target := spec.targetName.toName
  let some (.thmInfo a) := wrapper.full.find? name | throw <| IO.userError "missing wrapper theorem"
  let some (.thmInfo b) := provider.full.find? target | throw <| IO.userError "missing target theorem"
  let direct := Expr.equal a.value (.const target (a.levelParams.map Level.param))
  let value := a.value.etaExpanded?.getD a.value
  let pointwise := Expr.equal value (.const target (a.levelParams.map Level.param))
  let sameLevels := a.levelParams.length == b.levelParams.length
  let samePlicity := functionBindersMatch a.type b.type
  let sameType := same {} a.type (b.type.instantiateLevelParams b.levelParams (a.levelParams.map Level.param))
  let exported := wrapper.visible.contains name && provider.visible.contains target
  let extra := wrapper.visible.toList.filter (fun n => n != name && !isPrivateName n && !n.isInternal)
  let sameNames := binderNames a.type == binderNames b.type
  let eligible := pointwise && sameLevels && samePlicity && sameNames && exported
  let status := if eligible && sameType then "alias" else if eligible then "conversion-required" else "unresolved-removal"
  IO.println <| Json.compress <| Json.mkObj [
    ("event", toJson status), ("module", toJson spec.wrapper.name), ("name", toJson spec.name),
    ("provider", toJson spec.provider.name), ("target", toJson spec.targetName),
    ("direct", toJson direct), ("directAfterEta", toJson pointwise), ("sameArity", toJson sameLevels),
    ("samePlicity", toJson samePlicity), ("sameBinderNames", toJson sameNames),
    ("sameType", toJson sameType), ("exported", toJson exported),
    ("otherPublicNames", toJson <| extra.map toString)]
  return wrapper.regions ++ provider.regions

public unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["certify", manifest] =>
    for line in ← IO.FS.lines manifest do
      let item : AliasCase ← IO.ofExcept (Json.parse line >>= fromJson?)
      try
        for region in (← certifyAlias item).reverse do region.free
      catch e => output "unavailable" item.wrapper.name "" e.toString
  | ["compare", substitutions, manifest] =>
    let mut aliases : NameMap Name := {}
    for line in ← IO.FS.lines substitutions do
      let [name, target] := line.splitOn "\t" | throw <| IO.userError "invalid certified alias entry"
      aliases := aliases.insert name.toName target.toName
    for line in ← IO.FS.lines manifest do
      let item : Comparison ← IO.ofExcept (Json.parse line >>= fromJson?)
      try
        for region in (← inspect aliases item).reverse do region.free
      catch e => output "unavailable" item.current.name "" e.toString
  | _ => throw <| IO.userError "expected certify MANIFEST or compare SUBSTITUTIONS MANIFEST"
