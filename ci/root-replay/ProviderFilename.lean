import Lean.Linter.PersistentLintLog

open Lean

unsafe def main (args : List String) : IO Unit := do
  let [file] := args | throw <| IO.userError "expected a public module file"
  let publicFile := System.FilePath.mk file
  let parts ← readModuleDataParts #[publicFile, OLeanLevel.server.adjustFileName publicFile]
  let some (server, _) := parts.back? | throw <| IO.userError "missing server image"
  let mut paths := #[]
  let mut count := 0
  for (extension, entries) in server.entries do
    if extension == Linter.lintLogExt.name then
      let lints : Array Linter.LintEntry := unsafeCast entries
      for lint in lints do
        unless lint.file == lint.message.fileName do
          throw <| IO.userError "inconsistent source filename in the original module"
        unless paths.contains lint.file do
          paths := paths.push lint.file
        count := count + 1
  IO.println <| Json.compress <| Json.mkObj [("paths",toJson paths),("messages",toJson count)]
