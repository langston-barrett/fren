import Lean.Data.Json
import Heavy.CompilerForecast

open Lean Heavy.CompilerForecast

@[extern "heavy_observe_read_regular"]
opaque readFingerprintBytes (path : @& String) (accept : @& (Nat → Nat → Bool)) : IO (Option ByteArray)

namespace CompilerAdvice

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

def str (j : Json) (k : String) : Except String String := field j k >>= Json.getStr?
def nat (j : Json) (k : String) : Except String Nat := field j k >>= Json.getNat?
def strings (j : Json) : Except String (List String) := do
  return (← (← j.getArr?).mapM Json.getStr?).toList

/-- Missing optional identities remain absent; wrong types are errors. -/
def optional (j : Json) (k : String) (f : Json → Except String α) : Except String (Option α) := do
  match j.getObjVal? k with
  | .error _ => return none
  | .ok .null => return none
  | .ok v => return some (← f v)

/-- Nullable schema fields must still be present; absence is not a null. -/
def nullable (j : Json) (k : String) (f : Json → Except String α) : Except String (Option α) := do
  let value ← field j k
  if value.isNull then return none else return some (← f value)

def decode (j : Json) : Except String Record := do
  let schema ← nat j "schema"
  if schema != 2 && schema != 3 then throw "unsupported observation schema"
  let context : Context := {
    source := ← str j "source", cwd := ← str j "cwd"
    sourceFingerprint := ← str j "source_before", compiler := ← str j "real_compiler"
    compilerFingerprint := ← str j "compiler_fingerprint", version := ← str j "compiler_version"
    githash := ← str j "compiler_githash", args := ← strings (← field j "args")
    setup := ← nullable j "setup" Json.getStr?
    setupFingerprint := ← nullable j "setup_fingerprint" Json.getStr? }
  let gateError ← if schema == 3 then do pure (some (← nat j "gate_errno")) else pure none
  let childPresent ← if schema == 3 then do pure (some (← (← field j "child_present").getBool?)) else pure none
  let wrapperCode ← if schema == 3 then do pure (some (← nat j "wrapper_code")) else pure none
  return {
    context, schema, sourceAfter := ← str j "source_after"
    boot := ← optional j "boot_id" Json.getStr?, family := ← str j "family", kind := ← str j "input_kind"
    launchError := ← nat j "launch_errno", execError := ← nat j "exec_errno"
    waitError := ← nat j "wait_errno", clockError := ← nat j "clock_errno"
    status := ← nat j "raw_wait_status", pid := ← nat j "child_pid"
    gateError, childPresent, wrapperCode
    start := ← nat j "start_monotonic_ns", finish := ← nat j "end_monotonic_ns"
    rss := ← nat j "peak_rss_kib", measuredRss := ← nat j "measured_peak_rss_kib" }

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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--manifest", "--padding-kib", paddingText, path] =>
    try
      let some padding := paddingText.toNat? | throw (IO.userError "invalid padding")
      if padding == 0 || padding > 2^50 then throw (IO.userError "padding out of range")
      let request ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      let (_, context, boot, peak) ← CompilerAdvice.run request
      let some peak := peak | throw (IO.userError "unknown advice; no manifest row")
      if peak ≤ 0 || peak + padding > (2^50 : Int) then
        throw (IO.userError "demand out of range")
      let canonical ← IO.FS.realPath context.source
      let source := canonical.toString
      let fingerprint ← CompilerAdvice.fingerprint source
      if fingerprint != context.sourceFingerprint then
        throw (IO.userError "source changed; no manifest row")
      if [source, fingerprint].any (fun s => s.contains '\t' || s.contains '\n' || s.contains '\r') then
        throw (IO.userError "unsupported manifest field")
      let some identity := cohortIdentity context boot | throw (IO.userError "unknown cohort identity")
      IO.println s!"{source}\t{fingerprint}\tcohort-v1\t{identity}\t{peak + padding}"
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
