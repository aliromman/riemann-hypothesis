import LeanChecker

open Lean

-- Run the stock kernel replay for the exact modules in a build receipt.
private unsafe def replaySelected : IO Unit := do
  initSearchPath (← findSysroot)
  let some selection ← IO.getEnv "PR120_REPLAY_LIST" | throw <| IO.userError "missing module list"
  let stdout ← IO.getStdout
  for line in (← IO.FS.readFile selection).splitOn "\n" do
    if line.isEmpty then continue
    let name := line.toName
    let actual ← IO.FS.realPath (← findOLean name)
    let relative := String.intercalate "/" (line.splitOn ".") ++ ".olean"
    let root := (← IO.getEnv "PR120_REPLAY_ROOT").getD ".lake/build/lib/lean"
    let expected ← IO.FS.realPath (System.FilePath.mk root / relative)
    unless actual == expected do throw <| IO.userError s!"unexpected object for {name}: {actual}"
    replayFromImports name
    stdout.putStrLn s!"pass\t{line}"
    stdout.flush

#eval replaySelected
