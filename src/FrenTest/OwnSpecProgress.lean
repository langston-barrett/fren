-- keep-sorted start
import FrenCli.Run
import Lean.Data.Json
import Std.Sync.Mutex
-- keep-sorted end

/-!
# Diagnostics that survive an `ownSpec` crash

The checks capture their streams in memory. A native signal loses that
output, so the parent gives `ownSpec` a separate journal, flushed before
each component starts. The diagnostic root also relays bounded events
while captured children run. This does not handle signals or change the
checks, their methods or parallelism.
-/

namespace FrenTest.OwnSpecProgress

open Lean System

initialize livePath : IO.Ref (Option String) ← IO.mkRef none

/-- Pass the root relay's file through every captured process boundary. -/
def liveEnv : IO (Array (String × Option String)) := do
  let path ← match ← IO.getEnv "FREN_NATIVE_LIVE_FILE" with
    | some path => pure (some path)
    | none => livePath.get
  return path.toArray.map (fun path => ("FREN_NATIVE_LIVE_FILE", some path))

@[extern "fren_test_live_write"]
private opaque liveWrite (bytes : ByteArray) : IO Unit

/-- Only the root driver relays live records through its OS stderr,
rather than a nested process or isolated check's captured stream. -/
def withLive (action : IO α) : IO α := do
  if (← IO.getEnv "FREN_NATIVE_LIVE_FILE").isSome then return ← action
  IO.FS.withTempFile fun _ path => do
    let input ← IO.FS.Handle.mk path .read
    let stop ← IO.mkRef false
    livePath.set (some path.toString)
    let relay ← IO.asTask (prio := .dedicated) do
      repeat
        let chunk ← input.read 4096
        if !chunk.isEmpty then
          liveWrite chunk
        else if ← stop.get then break
        else IO.sleep 20
    try action
    finally
      stop.set true
      discard <| IO.ofExcept relay.get
      livePath.set none

/-- Writes one complete event at a time, including from checker workers. -/
structure Journal where
  write : Array String → IO Unit

instance : Inhabited Journal := ⟨⟨fun _ => pure ()⟩⟩

/-- The journal that the parent gave this child, or a silent one when
running a job directly. It is separate from the captured check output. -/
def journal (envKey : String := "FREN_OWN_SPEC_PROGRESS") : IO Journal := do
  let some path ← IO.getEnv envKey | return ⟨fun _ => pure ()⟩
  let h ← IO.FS.Handle.mk path .append
  let live ← match ← IO.getEnv "FREN_NATIVE_LIVE_FILE" with
    | none => pure none
    | some path => some <$> IO.FS.Handle.mk path .append
  let lock ← Std.Mutex.new ()
  return ⟨fun event => lock.atomically do
    h.putStrLn (toJson event).compress
    h.flush
    if let some live := live then
      -- The complete event remains in the journal. The live channel has
      -- bounded excerpts and never forwards isolated checker output.
      live.putStrLn (toJson (#["native-progress", envKey] ++
        (event.take 8).map (fun s => (s.take 512).toString))).compress
      live.flush⟩

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
streams are retained. Arguments are forwarded without interpolation. -/
def capture (args : Array String) (env : Array (String × Option String) := #[]) : IO (IO.Process.Output × String) :=
  IO.FS.withTempFile fun _ path => do
    let out ← IO.FS.withTempFile fun _ report => do IO.Process.output {
      cmd := "python3", args := #["scripts/native_diagnostic.py", "--capture-only",
        "--report", report.toString, "--progress-env", "FREN_OWN_SPEC_PROGRESS",
        "--", (← IO.appPath).toString] ++ args,
      env := env ++ (← liveEnv) ++ #[("FREN_OWN_SPEC_PROGRESS", some path.toString)] }
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
