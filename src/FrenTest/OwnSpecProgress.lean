-- keep-sorted start
import FrenCli.Run
import Lean.Data.Json
import Std.Sync.Mutex
-- keep-sorted end

/-!
# Diagnostics that survive an `ownSpec` crash

The checks capture their streams in memory. A native signal loses that
output, so the parent gives `ownSpec` a separate journal, flushed before
each component starts. The parent reports it only after a crash. This
does not handle signals or change the checks, their methods or parallelism.
-/

namespace FrenTest.OwnSpecProgress

open Lean System

/-- Writes one complete event at a time, including from checker workers. -/
structure Journal where
  write : Array String → IO Unit

instance : Inhabited Journal := ⟨⟨fun _ => pure ()⟩⟩

/-- The journal that the parent gave this child, or a silent one when
running a job directly. It is separate from the captured check output. -/
def journal (envKey : String := "FREN_OWN_SPEC_PROGRESS") : IO Journal := do
  let some path ← IO.getEnv envKey | return ⟨fun _ => pure ()⟩
  let h ← IO.FS.Handle.mk path .append
  let lock ← Std.Mutex.new ()
  return ⟨fun event => lock.atomically do
    h.putStrLn (toJson event).compress
    h.flush⟩

/-- Starts a phase, whose components have not started yet. -/
def Journal.phase (j : Journal) (name : String) : IO Unit := j.write #["phase", name]

/-- Records a component's entry or completion, after flushing its event. -/
def Journal.component (j : Journal) (name : String) (started : Bool) : IO Unit :=
  j.write #[if started then "start" else "done", name]

/-- The last phase and all component entries with no completion record.
A signal can interrupt the last write; earlier complete lines still count. -/
def summary (text : String) : String := Id.run do
  let mut phase := "before the first phase"
  let mut active : Array String := #[]
  for line in text.splitOn "\n" do
    match (Json.parse line >>= fromJson? : Except String (Array String)) with
    | .ok #["phase", name] => phase := name; active := #[]
    | .ok #["start", name] => active := active.push name
    | .ok #["done", name] => active := active.erase name
    | _ => pure ()
  return s!"ownSpec progress: {phase}\n" ++
    if active.isEmpty then "no active component recorded\n"
    else "active components (no completion recorded):\n" ++ String.join (active.toList.map (s!"  {·}\n"))

/-- Captures a child and its separate progress journal. Core dumps are
disabled even when the caller allows them; the original exit status and
streams are retained. Shell arguments are forwarded without interpolation. -/
def capture (args : Array String) (env : Array (String × Option String) := #[]) : IO (IO.Process.Output × String) :=
  IO.FS.withTempFile fun _ path => do
    let out ← IO.Process.output {
      cmd := "sh", args := #["-c", "ulimit -c 0 && exec \"$@\"", "sh", (← IO.appPath).toString] ++ args,
      env := env.push ("FREN_OWN_SPEC_PROGRESS", some path.toString)
        |>.push ("FREN_NATIVE_CORELESS", some "1") }
    return (out, summary (← IO.FS.readFile path))

/-- A real check whose first component can receive SIGFPE, after its
entry is flushed. The parent disables core dumps before starting it. -/
def probe (crash : Bool) : IO (Array String) := do
  if crash && (← IO.getEnv "FREN_NATIVE_CORELESS") != some "1" then
    throw (IO.userError "the signal probe requires FREN_NATIVE_CORELESS=1")
  let file := "test/fixtures/own_spec_progress.fren"
  let j ← journal
  j.phase "checking requirements"
  let (out, code) ← IO.FS.withIsolatedStreams do
    IO.println "captured output must not escape"
    FrenCli.check { files := #[file], jobs? := some 1 }
      (progress? := some fun name started => do
        j.component name started
        if crash && started then
          discard <| IO.Process.output { cmd := "kill", args := #["-s", "FPE", toString (← IO.Process.getPID)] })
  return if code == 0 then #[] else #[s!"the progress probe failed (exit {code}):\n{out}"]

/-- A native signal must leave the entered component visible, even though
the captured check output is lost. A normal check still returns only JSON. -/
def regression : IO (Array String) := do
  let mut failures := #[]
  let (ok, done) ← capture #["--job", "ownSpecProgressProbe", "pass"]
  unless ok.exitCode == 0 && ok.stdout.trimAscii.toString == "[]" && ok.stderr.isEmpty
      && done == "ownSpec progress: checking requirements\nno active component recorded\n" do
    failures := failures.push s!"a normal progress probe changed its output or did not finish:\n{ok.stdout}{ok.stderr}{done}"
  let (bad, active) ← capture #["--job", "ownSpecProgressProbe", "crash"]
  unless bad.exitCode == 136 && bad.stdout.isEmpty && bad.stderr.isEmpty
      && active.startsWith "ownSpec progress: checking requirements\nactive components"
      && active.contains "first".toSlice && !active.contains "second".toSlice do
    failures := failures.push s!"SIGFPE did not retain the active component (exit {bad.exitCode}):\n{bad.stdout}{bad.stderr}{active}"
  -- A long-running component can start before many others finish. Keep
  -- it, including when the crash interrupts the last event's write.
  let events := #[#["phase", "checks"], #["start", "old"], #["start", "old"], #["start", "new"],
    #["done", "old"], #["done", "new"]]
  let torn := String.join (events.toList.map (fun e => (toJson e).compress ++ "\n")) ++ "[\"done\",\"old"
  unless summary torn == "ownSpec progress: checks\nactive components (no completion recorded):\n  old\n" do
    failures := failures.push "a partial final event lost an earlier active component"
  return failures

end FrenTest.OwnSpecProgress
