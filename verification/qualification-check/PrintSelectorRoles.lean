import Lean

open Lean Elab Parser

/-- These names are namespace operands or aliases in the open declaration. -/
def selectedNames (node : Syntax) : Array (String × Ident) := Id.run do
  match node with
  | `(Parser.Command.openDecl| $_ ($ids*)) =>
    return ids.map fun id => ("open", id)
  | `(Parser.Command.openDecl| $_ hiding $ids*) =>
    return ids.map fun id => ("hiding", id)
  | `(Parser.Command.openDecl| $_ renaming $[$froms -> $tos],*) =>
    return (froms.map fun id => ("rename source", id)) ++ (tos.map fun id => ("rename alias", id))
  | `(export $_ ($ids*)) =>
    return ids.map fun id => ("export", id)
  | _ => return #[]

partial def printRoles (fileMap : FileMap) (node : Syntax) : IO Unit := do
  for (role, id) in selectedNames node do
    let some range := id.raw.getRange? | continue
    let pos := fileMap.toPosition range.start
    IO.println (Json.mkObj [("role", toJson role), ("identifier", toJson id.getId.toString),
      ("line", toJson pos.line), ("column", toJson pos.column),
      ("startByte", toJson range.start.byteIdx), ("endByte", toJson range.stop.byteIdx)]).compress
  for child in node.getArgs do
    printRoles fileMap child

unsafe def main (args : List String) : IO UInt32 := do
  let [moduleName, path] := args | do
    IO.eprintln "Usage: PrintSelectorRoles.lean MODULE SOURCE"
    return 2
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let ctx := mkInputContext (← IO.FS.readFile path) path
  let (header, parserState, messages) ← parseHeader ctx
  let opts := ({} : Options) |>.setBool `autoImplicit false |>.setBool `relaxedAutoImplicit false
    |>.set `maxSynthPendingDepth (3 : Nat) |>.set `maxHeartbeats (4000000 : Nat)
  let (env, messages) ← processHeader header opts messages ctx (mainModule := moduleName.toName)
  if messages.hasErrors then
    for msg in messages.toList do IO.eprintln (← msg.toString)
    return 1
  let processed ← IO.processCommands ctx parserState (Command.mkState env messages opts)
  if processed.commandState.messages.hasErrors then
    for msg in processed.commandState.messages.toList do
      if msg.severity == .error then IO.eprintln (← msg.toString)
    return 1
  for cmd in processed.commands do printRoles ctx.fileMap cmd
  return 0
