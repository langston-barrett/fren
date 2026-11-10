import Lean.Data.Json
import CompilerRecords
import Heavy.Forecast

open Lean Heavy.CompilerForecast

@[extern "heavy_observe_read_regular"]
opaque readFingerprintBytes (path : @& String) (accept : @& (Nat → Nat → Bool)) : IO (Option ByteArray)

namespace CompilerAdvice

def fingerprint (path : String) : IO String := do
  let some bytes ← readFingerprintBytes path Heavy.Process.fingerprintAllowed
    | throw (IO.userError s!"unavailable fingerprint: {path}")
  return s!"lean-bytearray64:{bytes.size}:{hash bytes}"

def bootIdentity : IO String := do
  return (← IO.FS.readFile "/proc/sys/kernel/random/boot_id").trimAscii.copy

def capture (compiler : String) (args : List String) : IO Context := do
  let some m := Heavy.Process.parseMetadata args | throw (IO.userError "unsupported compiler args")
  let some source := m.source | throw (IO.userError "no disk source")
  let real ← IO.FS.realPath compiler
  let query := fun flag => do
    let p ← IO.Process.output {cmd := real.toString, args := #[flag]}
    if p.exitCode != 0 then throw (IO.userError s!"compiler query failed: {flag}")
    pure p.stdout.trimAscii.copy
  return {
    source, cwd := (← IO.currentDir).toString, sourceFingerprint := ← fingerprint source
    compiler := real.toString, compilerFingerprint := ← fingerprint real.toString
    version := ← query "--version", githash := ← query "--githash", args
    setup := m.setup, setupFingerprint := ← m.setup.mapM fingerprint }

def run (request : Json) : IO (Json × Context × String × Option Int) := do
  let get := @IO.ofExcept
  let compiler ← get (str request "real_compiler")
  unless compiler.startsWith "/" do throw (IO.userError "absolute compiler required")
  let args ← get (strings (← get (field request "args")))
  let cutoff ← get (nat request "cutoff_monotonic_ns")
  let n ← get (nat request "recent_count")
  let minimum ← get (nat request "minimum_samples")
  if n > 1024 then throw (IO.userError "recent_count exceeds 1024")
  let paths ← get (strings (← get (field request "records")))
  let c ← capture compiler args
  let boot ← bootIdentity
  let mut records := []
  let mut rejected := 0
  for path in paths do
    let row ← try pure (Json.parse (← IO.FS.readFile path) >>= decode)
      catch e => pure (.error e.toString)
    match row with
    | .ok r => records := r :: records
    | .error _ => rejected := rejected + 1
  -- Recheck the current snapshot after reading history and querying the tool.
  let current ← capture compiler args
  let bootAfter ← bootIdentity
  let now ← IO.monoNanosNow
  let (peak, samples) := advice records c boot cutoff now n minimum
  let stable := c == current && boot == bootAfter
  return (Json.mkObj [
    ("status", toJson (if stable && peak.isSome then "estimate" else "unknown")),
    ("estimated_peak_rss_kib", if stable then toJson peak else .null),
    ("sample_count", toJson samples), ("rejected_records", toJson rejected),
    ("context", Json.mkObj [("source", toJson c.source), ("cwd", toJson c.cwd),
      ("source_fingerprint", toJson c.sourceFingerprint), ("real_compiler", toJson c.compiler),
      ("compiler_fingerprint", toJson c.compilerFingerprint), ("compiler_version", toJson c.version),
      ("compiler_githash", toJson c.githash), ("args", toJson c.args),
      ("setup", toJson c.setup), ("setup_fingerprint", toJson c.setupFingerprint)]),
    ("boot_id", toJson boot), ("now_monotonic_ns", toJson now),
    ("cutoff_monotonic_ns", toJson cutoff), ("recent_count", toJson n), ("minimum_samples", toJson minimum),
    ("limits", toJson "advisory selected maximum only; partial noncryptographic identity; no input closure, headroom, fallback, concurrent RAM or future bound; exported cohort row checks partial identity at gate")], c, boot, if stable then peak else none)

end CompilerAdvice


namespace JobForecast

-- Tie the executable's protocol to the source that selected the key and
-- decoded the history. A stale binary must never quietly return an estimate.
def adapterSource : String := include_str "ForecastMain.lean"
def kernelSource : String := include_str "../../src/Heavy/Forecast.lean"
def toolchainSource : String := include_str "lean-toolchain"
def lakefileSource : String := include_str "lakefile.lean"

def verifySources (root : String) : IO Unit := do
  let root := System.FilePath.mk root
  unless (← IO.FS.readFile (root / "tools/heavy-observe/ForecastMain.lean")) == adapterSource &&
      (← IO.FS.readFile (root / "src/Heavy/Forecast.lean")) == kernelSource &&
      (← IO.FS.readFile (root / "tools/heavy-observe/lean-toolchain")) == toolchainSource &&
      (← IO.FS.readFile (root / "tools/heavy-observe/lakefile.lean")) == lakefileSource do
    throw (IO.userError "job forecast executable is stale")

-- Eighteen decimal places retain ordinary JSON floating-point timestamps
-- while keeping selection in integral units.
def ticks (j : Json) : Option Int := do
  let n ← j.getNum?.toOption
  if n.exponent > 18 then none else some (n.mantissa * (10 ^ (18 - n.exponent) : Nat))

def loggedCommand (j : Json) : Option String := do
  if let .ok c := j.getObjValAs? String "prediction_command" then
    return c
  let c ← (j.getObjValAs? String "command").toOption
  if c.endsWith "..." then none
  else if c.startsWith "--offline " then some (String.ofList (c.toList.drop 10))
  else some c

def observation (j : Json) : Heavy.Forecast.Observation (Bool × String) :=
  let event := match j.getObjVal? "event" with
    | .error _ => some "job"
    | .ok x => x.getStr?.toOption
  let kind := (j.getObjValAs? String "job_kind").toOption
  let key := kind.map (Heavy.Forecast.predictionKey (loggedCommand j))
  -- Only a record that carries a status other than the integer 0 failed.
  let failed := match j.getObjVal? "exit_status" with
    | .error _ => false
    | .ok x => x != Json.num 0
  { event, key, ended := (j.getObjVal? "ended_at").toOption.bind ticks
    peak := (j.getObjValAs? Int "peak_rss_kb").toOption, failed }

def run (path nowText command secondsText countText : String) : IO Unit := do
  let now ← IO.ofExcept (Json.parse nowText)
  let some now := ticks now | throw (IO.userError "invalid time")
  let seconds ← IO.ofExcept (Json.parse secondsText >>= Json.getInt?)
  let count ← IO.ofExcept (Json.parse countText >>= Json.getNat?)
  if count > 1024 then throw (IO.userError "sample count too large")
  let key := Heavy.Forecast.predictionKey (some command) ""
  let cutoff := now - seconds * 1000000000000000000
  let mut ps : Heavy.Forecast.Peaks := []
  let mut seen := false
  let mut ok : Heavy.Forecast.Peaks := []
  try
    let f ← IO.FS.Handle.mk path IO.FS.Mode.read
    repeat
      let line ← f.getLine
      if line.isEmpty then break
      if let .ok j := Json.parse line then
        let o := observation j
        if Heavy.Forecast.eligible o key cutoff now then
          seen := seen || !o.failed
          if let (some t, some p) := (o.ended, o.peak) then
            ps := Heavy.Forecast.insert t p count ps
            if !o.failed then ok := Heavy.Forecast.insert t p 1 ok
  catch _ => pure ()
  IO.println (toJson (Heavy.Forecast.forecast seen ok ps)).compress

end JobForecast

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--job-forecast", path, now, command, seconds, count, root] =>
    try
      JobForecast.verifySources root
      JobForecast.run path now command seconds count
      return 0
    catch e => (← IO.getStderr).putStrLn s!"job forecast: {e}"; return 1
  | ["--manifest", "--padding-kib", paddingText, path] =>
    try
      let some padding := paddingText.toNat? | throw (IO.userError "invalid padding")
      if padding == 0 || padding > 2^50 then throw (IO.userError "padding out of range")
      let request ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      let (_, context, boot, peak) ← CompilerAdvice.run request
      let some peak := peak | throw (IO.userError "unknown advice; no manifest row")
      let some demand := padded (some peak) padding
        | throw (IO.userError "demand out of range")
      let canonical ← IO.FS.realPath context.source
      let source := canonical.toString
      let fingerprint ← CompilerAdvice.fingerprint source
      if fingerprint != context.sourceFingerprint then
        throw (IO.userError "source changed; no manifest row")
      if [source, fingerprint].any (fun s => s.contains '\t' || s.contains '\n' || s.contains '\r') then
        throw (IO.userError "unsupported manifest field")
      let some identity := cohortIdentity context boot | throw (IO.userError "unknown cohort identity")
      IO.println s!"{source}\t{fingerprint}\tcohort-v1\t{identity}\t{demand}"
      return 0
    catch e =>
      (← IO.getStderr).putStrLn s!"compiler_advice: {e}"
      return 1
  | [path] =>
    if path.startsWith "--" then
      (← IO.getStderr).putStrLn "usage: compiler_advice REQUEST.json | --manifest --padding-kib N REQUEST.json"
      return 1
    try
      let request ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      let (result, _, _, _) ← CompilerAdvice.run request
      IO.println result.compress
      return 0
    catch e =>
      IO.println (Json.mkObj [("status", toJson "unknown"), ("estimated_peak_rss_kib", .null),
        ("sample_count", toJson (0 : Nat)), ("error", toJson e.toString)]).compress
      return 0
  | _ =>
    (← IO.getStderr).putStrLn "usage: compiler_advice REQUEST.json | --manifest --padding-kib N REQUEST.json"
    return 1
