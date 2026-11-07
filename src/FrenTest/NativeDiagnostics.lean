-- keep-sorted start
import FrenTest.OwnSpecProgress
-- keep-sorted end

/-!
# In-place native diagnostics for the enumeration job

The parent wraps only the selected enumeration child. Its flushed journal
uses a separate handle, so isolated diagnostic streams cannot swallow the
active phase, fixture or method. GDB watches that original child while
the other shard workers continue; there is no later replay.
-/

namespace FrenTest.NativeDiagnostics

open Lean

initialize context : FrenTest.OwnSpecProgress.Journal ←
  FrenTest.OwnSpecProgress.journal "FREN_ENUM_PROGRESS"

/-- A flushed checkpoint outside the check's isolated output buffer. -/
def checkpoint (event : Array String) : IO Unit := context.write event

/-- Enabled only in the outer job runner. Children cannot recursively
wrap themselves, even if another runner is invoked within a probe. -/
def enabled : IO Bool := do
  return (← IO.getEnv "FREN_DIAG_ENUMERATION") == some "1" &&
    (← IO.getEnv "FREN_ENUM_DIAG_ACTIVE") != some "1"

/-- Run the original selected job under the source-bound wrapper. The
wrapper preserves child output, distinguishes its status from GDB's and
reports checkpoints/frames on failure. -/
def capture (args : Array String) (env : Array (String × Option String))
    (cohort : Array (List String)) (workers : Nat) : IO IO.Process.Output :=
  IO.FS.withTempDir fun root => do
    let out ← IO.Process.output {
      cmd := "python3",
      args := #["scripts/native_diagnostic.py", "--report", (root / "report.json").toString,
        "--cohort", (toJson cohort).compress, "--workers", toString workers,
        "--", (← IO.appPath).toString] ++ args,
      env }
    -- A local integration test can retain the exact parent receipt even
    -- on success; CI's normal successful output remains unchanged.
    if let some destination ← IO.getEnv "FREN_ENUM_DIAG_RECEIPT" then
      let report := root / "report.json"
      if ← report.pathExists then IO.FS.writeFile destination (← IO.FS.readFile report)
    return out

/-- A real checker call for testing the wrapper's successful output and
controlled crash handling. Its checkpoints are inside isolated streams. -/
def probe (crash : Bool) : IO (Array String) := do
  let (out, code) ← IO.FS.withIsolatedStreams do
    checkpoint #["phase", "controlled-check"]
    checkpoint #["diagnostic-env", (← IO.getEnv "FREN_DIAG_ENUMERATION").getD "unset",
      (← IO.getEnv "FREN_ENUM_DIAG_ACTIVE").getD "unset"]
    checkpoint #["fixture", "test/fixtures/own_spec_progress.fren"]
    checkpoint #["method", "solver"]
    IO.println "captured output must not escape"
    FrenCli.check { files := #["test/fixtures/own_spec_progress.fren"], jobs? := some 1 }
      (progress? := some fun label started => do
        checkpoint #["component", label, if started then "start" else "done"]
        if crash && started then
          discard <| IO.Process.output {
            cmd := "kill", args := #["-s", "ABRT", toString (← IO.Process.getPID)] })
  return if code == 0 then #[] else #[s!"native diagnostic probe failed (exit {code}):\n{out}"]

/-- The native wrapper's integration tests use this freshly built driver. -/
def regression : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "python3", args := #["scripts/native_diagnostic_test.py", "--driver", (← IO.appPath).toString] }
  for line in out.stdout.splitOn "\n" do
    if line.startsWith "skipped: " then IO.println line
  return if out.exitCode == 0 then #[] else
    #[s!"native diagnostic harness failed (exit {out.exitCode}):\n{out.stdout}{out.stderr}"]

end FrenTest.NativeDiagnostics
