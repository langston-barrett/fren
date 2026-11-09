module

import FrenOirToSmt.Process

open FrenOirToSmt

/-! Owned transport-path controls; never used as solver evidence. The first
argument names the mode. Installed at a tree's fixed cvc5 path, where it is
called with cvc5's arguments, it reads the mode from the file beside it with
the extension `.mode`; an unknown mode there drains stdin and exits 9. -/

private def out (s : String) : IO Unit := do
  let h ← IO.getStdout
  h.putStr s
  h.flush

private def err (s : String) : IO Unit := do
  let h ← IO.getStderr
  h.putStr s
  h.flush

private def bytes (b : ByteArray) : IO Unit := do
  let h ← IO.getStdout
  h.write b
  h.flush

private def drain : IO Unit := do
  let stdin ← IO.getStdin
  repeat
    if (← stdin.read 4096).isEmpty then break

private def forever : IO Unit := do
  repeat IO.sleep 1000

/-- A same-group descendant that holds the inherited pipes and outlives us. -/
private def descendant : IO Unit := do
  let _ ← IO.Process.spawn {cmd := (← IO.appPath).toString, args := #["hold-input"]}

private def modes : List String := ["unknown", "unsupported", "suspended", "nonzero", "protocol",
  "stderr", "flood", "bytes", "closed", "closed-exit", "descendant", "orphan", "sleep",
  "hold-input", "timeout", "unsat", "ready"]

public def main (args : List String) : IO UInt32 := do
  let (mode, rest, fixture) ← match args with
    | m :: rest => if modes.contains m then pure (m, rest, false) else fixtureMode
    | [] => fixtureMode
  if !["hold-input", "orphan", "ready", "unsat", "closed-exit"].contains mode then
    drain
  match mode with
  | "unknown" => out "unknown\n"
  | "unsupported" => out "unsupported\n"
  | "unsat" => out "unsat\n"
  | "suspended" => do
    let _ ← Process.signalProcess (← IO.Process.getPID) Process.sigstop
    pure ()
  | "nonzero" =>
    out "unsat\n"
    unless fixture do err "owned failure\n"
    return 7
  | "protocol" => out "unsat\n(error \"owned failure\")\n"
  | "stderr" =>
    out "unsat\n"
    err "owned diagnostic\n"
  | "flood" => bytes (ByteArray.mk (Array.replicate 100000 120))
  | "bytes" => bytes (ByteArray.mk #[0xff])
  | "closed" =>
    Process.closeFd 1
    Process.closeFd 2
    IO.sleep 60000
  | "closed-exit" =>
    Process.closeFd 1
    Process.closeFd 2
    IO.sleep 20
  | "descendant" => descendant
  | "orphan" => descendant
  | "ready" =>
    -- Readiness for a cancellation control: our PID (to the named file, or
    -- beside us at a fixed solver path), then a long sleep.
    let path ← match rest with
      | [path] => pure (System.FilePath.mk path)
      | _ => pure ((← IO.appPath).withExtension "pid")
    -- Written whole, then renamed, so that no reader sees a partial PID.
    let staging := path.withExtension "partial"
    IO.FS.writeFile staging (toString (← IO.Process.getPID))
    IO.FS.rename staging path
    IO.sleep 60000
  | "sleep" | "hold-input" | "timeout" => IO.sleep 60000
  | _ => if fixture then return 9 else forever
  return 0
where
  fixtureMode : IO (String × List String × Bool) := do
    let path := (← IO.appPath).withExtension "mode"
    let mode ← try IO.FS.readFile path catch _ => pure ""
    let mode := mode.trimAscii.toString
    return (if modes.contains mode then mode else "invalid", [], true)
