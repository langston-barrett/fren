-- keep-sorted start
import FrenTest.OwnSpecProgress
-- keep-sorted end

/-!
# In-place native diagnostics for selected test invocations

The parent wraps selected enumeration and own-requirements invocations. Its flushed journal
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
    (cohort : Array (List String)) (workers : Nat)
    (progressEnv : String := "FREN_ENUM_PROGRESS") : IO IO.Process.Output :=
  IO.FS.withTempDir fun root => do
    let out ← IO.Process.output {
      cmd := "python3",
      args := #["scripts/native_diagnostic.py", "--report", (root / "report.json").toString,
        "--cohort", (toJson cohort).compress, "--workers", toString workers,
        "--progress-env", progressEnv,
        "--", (← IO.appPath).toString] ++ args,
      env := env ++ (← FrenTest.OwnSpecProgress.liveEnv) }
    -- A local integration test can retain the exact parent receipt even
    -- on success; CI's normal successful output remains unchanged.
    if let some destination ← IO.getEnv "FREN_ENUM_DIAG_RECEIPT" then
      let report := root / "report.json"
      if ← report.pathExists then IO.FS.writeFile destination (← IO.FS.readFile report)
    if progressEnv == "FREN_OWN_SPEC_PROGRESS" then
      if let some destination ← IO.getEnv "FREN_OWN_DIAG_RECEIPTS" then
        let report := root / "report.json"
        if ← report.pathExists then
          IO.FS.createDirAll destination
          IO.FS.writeFile (System.FilePath.mk destination / s!"own-native-{← IO.monoNanosNow}.json")
            (← IO.FS.readFile report)
    return out

/-- Only the original own-requirements invocations opt in. Wrapped
children cannot activate a second debugger or replay themselves. -/
def ownEnabled : IO Bool := do
  return (← IO.getEnv "FREN_DIAG_OWN_SPEC_INITIAL") == some "1" &&
    (← IO.getEnv "FREN_OWN_DIAG_ACTIVE") != some "1"

/-- The shared requirements child, excluding the paired UI invocations. -/
def ownRequirements (args : List String) : Bool :=
  args.head? == some "check" && args.any (·.startsWith "src/Reqs/")

#guard ownRequirements ["check", "--jobs", "4", "src/Reqs/Check.md"]
#guard !ownRequirements ["check", "test/ui/checks/contracts.fren"]
#guard !ownRequirements ["quickcheck", "src/Reqs/Check.md"]

/-- Use the outer job's actual selection metadata, including when its
original requirements check launches a nested persistent child. -/
def captureOwn (args : Array String) : IO IO.Process.Output := do
  let raw ← IO.getEnv "FREN_OWN_DIAG_CONTEXT"
  let (cohort, workers) ← match raw with
    | none => pure (#[], 1)
    | some raw => IO.ofExcept <| (Json.parse raw >>= fromJson? :
        Except String (Array (List String) × Nat)).mapError IO.userError
  capture args #[] cohort workers "FREN_OWN_SPEC_PROGRESS"

/-- A complete JSON payload cannot turn a failed diagnostic child green. -/
def failure? (out : IO.Process.Output) : Option String :=
  if out.exitCode == 0 then none else
    some s!"native child failed (exit {out.exitCode}):\n{out.stderr}{out.stdout}"

def requireSuccess (out : IO.Process.Output) : IO Unit := do
  if let some failure := failure? out then throw (IO.userError failure)

abbrev InitialInput := Array String × Option String × Option String

/-- A real ABRT on this checking thread, without a process/reader helper. -/
@[extern "fren_test_raise_abrt"]
private opaque raiseAbort : IO Unit

/-- The same initial check, with the original default checker concurrency
and cache options. A controlled signal is available only to the probe entry. -/
def initial (input : InitialInput) (crash : Bool := false) : IO (String × UInt32) := do
  if crash && (← IO.getEnv "FREN_NATIVE_CORELESS") != some "1" then
    throw (IO.userError "the signal probe requires FREN_NATIVE_CORELESS=1")
  let (files, queryCache?, verifyQueryCache?) := input
  let progress ← FrenTest.OwnSpecProgress.journal
  progress.phase "checking requirements"
  progress.write #["initial-input", (toJson input).compress]
  let signal? ← if crash then some <$> IO.mkRef false else pure none
  IO.FS.withIsolatedStreams do
    FrenCli.check { files, queryCache?, verifyQueryCache? }
      (progress? := some fun label started => do
        progress.component label started
        if started then
          if let some signal := signal? then
            if ← signal.modifyGet fun sent => (!sent, true) then raiseAbort)

/-- In diagnostic mode this is the one original initial check, not a replay.
The parent retains every later ownSpec check after a returned verdict. -/
def runInitial (input : InitialInput) (probe : Option String := none) : IO (String × UInt32) := do
  unless ← ownEnabled do
    if probe.isSome then throw (IO.userError "the native initial probe requires FREN_DIAG_OWN_SPEC_INITIAL=1")
    return ← initial input
  let args := match probe with
    | none => #["--own-spec-initial-check", (toJson input).compress]
    | some mode => #["--native-initial-child", mode, (toJson input).compress]
  let out ← captureOwn args
  let invalid := IO.userError s!"initial check failed (exit {out.exitCode}):\n{out.stderr}{out.stdout}"
  let last := ((out.stdout.splitOn "\n").filter (!·.isEmpty)).getLast?.getD ""
  let .ok #[code, text] := (Json.parse last >>= fromJson? : Except String (Array String))
    | throw invalid
  let some code := code.toNat? | throw invalid
  -- Native faults, handled faults, unknown terminal status and missing
  -- GDB cannot be replaced by a successful serialized checker verdict.
  unless code <= 255 && code.toUInt32 == out.exitCode do throw invalid
  -- Keep uncaptured native stderr visible to the outer job's existing
  -- stderr check, even when the serialized checker verdict is zero.
  IO.eprint out.stderr
  return (text, code.toUInt32)

/-- A real checker call for testing the wrapper's successful output and
controlled crash handling. Its checkpoints are inside isolated streams. -/
def probe (crash : Bool) : IO (Array String) := do
  if crash && (← IO.getEnv "FREN_NATIVE_CORELESS") != some "1" then
    throw (IO.userError "the signal probe requires FREN_NATIVE_CORELESS=1")
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
        if crash && started then raiseAbort)
  return if code == 0 then #[] else #[s!"native diagnostic probe failed (exit {code}):\n{out}"]

/-- The native wrapper's integration tests use this freshly built driver. -/
def regression (group : String) : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "python3", args := #["scripts/native_diagnostic_test.py", "--driver", (← IO.appPath).toString,
      "--group", group] }
  for line in out.stdout.splitOn "\n" do
    if line.startsWith "skipped: " then IO.println line
  return if out.exitCode == 0 then #[] else
    #[s!"native diagnostic harness failed (exit {out.exitCode}):\n{out.stdout}{out.stderr}"]

/-- Real process checks of live capture, interruption and owned lifetime. -/
def observationRegression : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "python3", args := #["scripts/native_observation_test.py", "--driver", (← IO.appPath).toString] }
  return if out.exitCode == 0 then #[] else
    #[s!"native observation harness failed (exit {out.exitCode}):\n{out.stdout}{out.stderr}"]

end FrenTest.NativeDiagnostics
