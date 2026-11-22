import Lean

open Lean

structure SelectedRef where
  spelling : String
  constant : String
  deriving FromJson

structure Case where
  id : Nat
  ns : String
  token : String
  form : String
  correction : String
  oldOpen : Array (String × Array String)
  newOpen : Array (String × Array String)
  oldNamespaces : Array String
  newNamespaces : Array String
  old : Array String
  new : Array String
  selected : Array SelectedRef
  deriving FromJson

def opened (xs : Array (String × Array String)) : List OpenDecl :=
  xs.toList.map fun (n, excluded) => .simple n.toName (excluded.toList.map String.toName)

def registered (env : Environment) (names : Array String) : Environment :=
  names.foldl (fun e n => e.registerNamespace n.toName) env

def resolve (env : Environment) (ns : String) (opened : List OpenDecl) (name : String) : List Name :=
  (ResolveName.resolveNamespace env ns.toName opened name.toName).eraseDups

def verify (empty : Environment) (r : Case) : Bool := Id.run do
  let source := registered empty r.oldNamespaces
  let merged := registered empty r.newNamespaces
  let original := resolve source r.ns (opened r.oldOpen) r.token
  let uncorrected := resolve merged r.ns (opened r.newOpen) r.token
  let corrected := (r.correction.splitOn " ").flatMap (resolve merged r.ns (opened r.newOpen))
  if original != r.old.toList.map String.toName || uncorrected != r.new.toList.map String.toName ||
      original == uncorrected then return false
  if r.form == "selected" && original.length > 1 then
    let [owner] := corrected | return false
    return original.contains owner && !r.selected.isEmpty &&
      r.selected.all fun s => owner ++ s.spelling.toName == s.constant.toName
  return corrected == original

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one evidence file")
  let env ← mkEmptyEnvironment
  let mut count := 0
  for line in ← IO.FS.lines path do
    let row : Case ← IO.ofExcept (Json.parse line >>= fromJson?)
    unless verify env row do throw (IO.userError s!"namespace resolution differs at record {row.id}")
    count := count + 1
  IO.println s!"verified {count}"
