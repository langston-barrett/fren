import BudgetAdapter
import Heavy.Process

/-! Standalone Linux Lean compiler observer. No Fren, solver or Lake imports.
The standalone package uses the installed Lean core/Std and observer.c. -/

open Heavy.Process System

@[extern "heavy_observe_wait"]
opaque observe (exe : @& String) (args : @& Array String) : IO (Array UInt64)

@[extern "heavy_observe_signal"]
opaque terminateBySignal (signal : UInt32) : IO Unit

@[extern "heavy_observe_write"]
opaque writeRecord (dir record : @& String) : IO UInt32

@[extern "heavy_observe_read_regular"]
opaque readRegular (path : @& String) (accept : @& (Nat → Nat → Bool)) : IO (Option ByteArray)

@[extern "heavy_budget_observe"]
opaque observeBudget (exe : @& String) (args : @& Array String) (dir : @& String)
    (demand : UInt64) (decide : @& (Array String → Array UInt64))
    (control : @& (Array UInt64 → Array UInt64)) : IO (Array UInt64)

-- JSON output needs no elaborator/Lean JSON dependency.
def quoted (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => if c.toNat < 32 then
          let digits := "0123456789abcdef".toList.toArray
          "\\u00" ++ String.singleton digits[c.toNat / 16]! ++ String.singleton digits[c.toNat % 16]!
        else String.singleton c
  return out ++ "\""

def object (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (k, v) => quoted k ++ ":" ++ v) ++ "}"

def strings (xs : List String) : String := "[" ++ String.intercalate "," (xs.map quoted) ++ "]"

def jsonOption (f : α → String) : Option α → String
  | some x => f x
  | none => "null"

/-- This is deliberately labelled partial/non-cryptographic, never a complete
input closure. It is useful for comparing observed source and artifact bytes. -/
def fingerprint (path : FilePath) : IO (Option String) := do
  let bytes ← readRegular path.toString fingerprintAllowed
  return bytes.map fun bytes => s!"lean-bytearray64:{bytes.size}:{hash bytes}"

def artifact (path : String) : IO String := do
  return object [("path", quoted path), ("fingerprint", jsonOption quoted (← fingerprint path))]

def warn (s : String) : IO Unit := do
  try (← IO.getStderr).putStrLn s!"heavy-observe: {s}"
  catch _ => pure ()

def run (args : List String) : IO UInt32 := do
  let self ← IO.FS.realPath (← IO.appPath)
  let root := self.parent.getD "." |>.parent.getD "."
  -- No PATH lookup and no reliance on --print-prefix to find the real compiler.
  let configured := (← IO.FS.readFile (root / "real-lean.path")).trimAscii.copy
  if !(FilePath.mk configured).isAbsolute then
    throw (IO.userError "real compiler must be an absolute path")
  -- realPath fails for a missing target; retain that path so exec errno is recorded.
  let real ← try IO.FS.realPath configured catch _ => pure (FilePath.mk configured)
  if self == real then throw (IO.userError "recursive overlay: real compiler is the observer")
  -- Also reject a copied observer, not just a symlink or the same pathname.
  if (← real.pathExists) then
    if (← self.metadata).byteSize == (← real.metadata).byteSize then
      let a ← readRegular self.toString fingerprintAllowed
      let b ← readRegular real.toString fingerprintAllowed
      if a.isSome && a == b then throw (IO.userError "recursive overlay: real compiler is a copy of the observer")
  let cwd ← IO.currentDir
  let parsed := parseMetadata args
  let source := parsed.bind (·.source)
  let sourceBefore ← source.mapM fun s => fingerprint s
  let setup := parsed.bind (·.setup)
  let setupBefore ← setup.mapM fun s => fingerprint s
  let compilerFingerprint ← fingerprint real
  let version ← try
    let out ← IO.Process.output {cmd := real.toString, args := #["--version"]}
    pure (if out.exitCode == 0 then some out.stdout.trimAscii.copy else none)
    catch _ => pure none
  let githash ← try
    let out ← IO.Process.output {cmd := real.toString, args := #["--githash"]}
    pure (if out.exitCode == 0 then some out.stdout.trimAscii.copy else none)
    catch _ => pure none
  let gateDir ← IO.getEnv "HEAVY_BUDGET_DIR"
  let gated := gateDir.isSome && (parsed.map (·.kind)) != some "query"
  let mut requestDemand := 0
  let mut provenance := ""
  let raw ← if gated then do
    let dir := FilePath.mk gateDir.get!
    let some configBytes ← readRegular (dir / "config").toString fingerprintAllowed
      | throw (IO.userError "unreadable budget config")
    let some config := String.fromUTF8? configBytes | throw (IO.userError "invalid budget config")
    let [_, _, fallback, _] := BudgetAdapter.words config.trimAscii.copy
      | throw (IO.userError "malformed budget config")
    let some fallback := fallback.toNat? | throw (IO.userError "malformed fallback")
    let some bytes ← readRegular (dir / "requests").toString fingerprintAllowed
      | throw (IO.userError "unreadable request manifest")
    let some manifest := String.fromUTF8? bytes | throw (IO.userError "invalid request manifest")
    -- Identity is optional even when realPath fails: the compiler must still
    -- receive the original arguments and diagnose its own inaccessible input.
    let canonical ← try source.mapM fun s => do pure (← IO.FS.realPath s).toString
      catch _ => pure none
    let (requestSource, requestFingerprint) := Heavy.Budget.sourceIdentity canonical (sourceBefore.bind id)
    let some (demand, origin) := BudgetAdapter.request manifest requestSource requestFingerprint fallback
      | throw (IO.userError "invalid request demand")
    requestDemand := demand
    provenance := origin
    observeBudget real.toString args.toArray dir.toString demand.toUInt64 BudgetAdapter.snapshot BudgetAdapter.control
    else observe real.toString args.toArray
  if raw.size != (if gated then 18 else 11) then throw (IO.userError "invalid FFI observation length")
  let v := fun i => raw[i]!.toNat
  let gateError := if gated then v 11 else 0
  let childPresent := !gated || v 5 != 0
  let outcome := result (v 0) (v 1) (v 2) (v 4)
  let wall := if childPresent then elapsed (v 3) (v 6) (v 7) else none
  let measured := if childPresent then usage (v 0) (v 1) (v 2) (v 4) (v 8) (v 9) (v 10) else none
  let inputClosure : Option String := none
  let complete := identityComplete (sourceBefore.bind id) compilerFingerprint inputClosure
  let outputs := [parsed.bind (·.olean), parsed.bind (·.ilean), parsed.bind (·.c), parsed.bind (·.bc)] |>.filterMap id
  -- Recording failures are explicitly separate from the available child outcome.
  try
    let artifacts ← outputs.mapM artifact
    let sourceAfter ← source.mapM fun s => fingerprint s
    let gateFields := if gated then [
      ("gate_errno", toString gateError), ("admission_wait_ns", toString (v 12)),
      ("admission_granted_ns", toString (v 17)),
      ("reservation_ticket", toString (v 13)), ("held_before_kib", toString (v 14)),
      ("allowance_kib", toString (v 15)), ("parent_headroom_kib", toString (v 16)),
      ("requested_reservation_kib", toString requestDemand), ("request_provenance", quoted provenance),
      ("child_present", toString childPresent),
      ("wrapper_code", toString (if gateError != 0 then 125 else outcome.shellCode))] else []
    let record := object (gateFields ++ [
      ("schema", if gated then "3" else "2"), ("family", quoted "lean"),
      ("input_kind", quoted ((parsed.map (·.kind)).getD "unknown")),
      ("source", jsonOption quoted source),
      ("module_hint", jsonOption quoted (source.map fun s => (FilePath.mk s).withExtension "" |>.toString.replace "/" ".")),
      ("cwd", quoted cwd.toString), ("args", strings args),
      ("source_before", jsonOption quoted (sourceBefore.bind id)),
      ("source_after", jsonOption quoted (sourceAfter.bind id)),
      ("setup", jsonOption quoted setup), ("setup_fingerprint", jsonOption quoted (setupBefore.bind id)),
      ("artifacts", "[" ++ String.intercalate "," artifacts ++ "]"),
      ("real_compiler", quoted real.toString), ("compiler_fingerprint", jsonOption quoted compilerFingerprint),
      ("compiler_version", jsonOption quoted version), ("compiler_githash", jsonOption quoted githash),
      ("identity_complete", toString complete), ("input_closure", jsonOption quoted inputClosure),
      ("identity_missing", strings ["imports", "reader inputs", "plugins", "environment closure", "toolchain libraries"]),
      ("launch_errno", toString (v 0)), ("exec_errno", toString (v 1)),
      ("wait_errno", toString (v 2)), ("clock_errno", toString (v 3)),
      ("raw_wait_status", toString (v 4)), ("child_pid", toString (v 5)),
      ("start_monotonic_ns", toString (v 6)), ("end_monotonic_ns", toString (v 7)),
      ("wall_ns", jsonOption toString wall), ("user_us", toString (v 8)),
      ("system_us", toString (v 9)), ("peak_rss_kib", toString (v 10)),
      ("measured_cpu_us", jsonOption (fun p => toString p.1) measured),
      ("measured_peak_rss_kib", jsonOption (fun p => toString p.2) measured),
      ("result_kind", if childPresent then toString outcome.kind else "null"), ("result_detail", if childPresent then toString outcome.detail else "null"),
      ("shell_code", if childPresent then toString outcome.shellCode else "null")])
    let dir := (← IO.getEnv "HEAVY_OBSERVE_DIR").map FilePath.mk |>.getD (root / "records")
    -- Atomic publication gives each invocation its own file, avoiding JSONL races.
    IO.FS.createDirAll dir
    let err ← writeRecord dir.toString record
    if err != 0 then warn s!"record failed (errno {err}): {dir}"
  catch e => warn s!"record failed: {e}"
  if gateError != 0 then
    warn s!"budget control failed (errno {gateError}); child present={childPresent}"
    return 125
  if outcome.kind == 2 then warn s!"exec failed (errno {outcome.detail}): {real}"
  if outcome.kind == 3 then warn s!"observation failed (errno {outcome.detail})"
  if outcome.kind == 1 then terminateBySignal outcome.detail.toUInt32
  return outcome.shellCode.toUInt32

def main (args : List String) : IO UInt32 := do
  try run args
  catch e =>
    warn s!"setup failed: {e}"
    return 125
