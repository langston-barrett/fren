import BudgetAdapter
import CompilerRecords
import Heavy.Process
import Heavy.ModuleMemory

/-! Standalone Linux Lean compiler observer. No Fren, solver or Lake imports.
The standalone package uses the installed Lean core/Std and observer.c. -/

open Heavy.Process System

@[extern "heavy_observe_wait"]
opaque observe (exe : @& String) (args : @& Array String) : IO (Array UInt64)

@[extern "heavy_observe_signal"]
opaque terminateBySignal (signal : UInt32) : IO Unit

@[extern "heavy_observe_write"]
opaque writeRecord (dir record : @& String) : IO UInt32

@[extern "heavy_observe_publish"]
opaque publishProcess (helper record : @& String) : IO UInt32

@[extern "heavy_observe_read_regular"]
opaque readRegular (path : @& String) (accept : @& (Nat → Nat → Bool)) : IO (Option ByteArray)

@[extern "heavy_budget_observe"]
opaque observeBudget (exe : @& String) (args : @& Array String) (dir : @& String)
    (demand cpuLimit wallLimit memoryLimit : UInt64) (decide : @& (Array String → Array UInt64))
    (control : @& (Array UInt64 → Array UInt64)) : IO (Array UInt64)

-- Record output retains its compact serializer.
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

def compilerQuery (real : FilePath) (flag : String) : IO (Option String) := do
  try
    let out ← IO.Process.output {cmd := real.toString, args := #[flag]}
    return if out.exitCode == 0 then some out.stdout.trimAscii.copy else none
  catch _ => return none

/-- Setup-only entry, selected by a private helper basename, never by compiler
argv. The caller promises a native Lean with immutable installed assets. -/
def prepareMetadata (real output : FilePath) : IO Unit := do
  let real ← IO.FS.realPath real
  let some bytes ← readRegular real.toString fingerprintAllowed | return
  -- Scripts/wrappers are outside the constant compiled-metadata contract.
  unless (bytes.extract 0 4).toList == [127, 69, 76, 70] do return
  let some version ← compilerQuery real "--version" | return
  let some githash ← compilerQuery real "--githash" | return
  unless version.startsWith "Lean (version " && githash.length == 40 &&
      githash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) &&
      (version.splitOn githash).length > 1 do return
  let fields := ["heavy-native-lean-metadata-v1", real.toString,
    s!"lean-bytearray64:{bytes.size}:{hash bytes}", version, githash]
  unless fields.all (fun s => !(s.contains '\n') && !(s.contains '\r')) do return
  -- Keep the pre-query and post-query images equal, without substituting stat.
  unless (← readRegular real.toString fingerprintAllowed) == some bytes do return
  let body := String.intercalate "\n" fields
  IO.FS.writeFile output (body ++ s!"\n{hash body}\n")

def preparedMetadata (root real : FilePath) (current : Option String) : IO (Option (String × String)) := do
  try
    let some bytes ← readRegular (root / "compiler-metadata").toString fingerprintAllowed | return none
    let some raw := String.fromUTF8? bytes | return none
    let [tag, path, digest, version, githash, checksum, ""] := raw.splitOn "\n" | return none
    unless tag == "heavy-native-lean-metadata-v1" do return none
    let some stored := checksum.toNat? | return none
    let body := String.intercalate "\n" [tag, path, digest, version, githash]
    return if reuseMetadata real.toString current path digest version githash
        (hash body).toNat stored then some (version, githash) else none
  catch _ => return none

def artifact (path : String) : IO String := do
  return object [("path", quoted path), ("fingerprint", jsonOption quoted (← fingerprint path))]

def warn (s : String) : IO Unit := do
  try (← IO.getStderr).putStrLn s!"heavy-observe: {s}"
  catch _ => pure ()

def publishOptional (publisher record : String) : IO Unit := do
  try
    let result ← publishProcess publisher record
    if result != 0 then warn s!"optional publication failed (status {result})"
  catch e => warn s!"optional publication failed: {e}"

/-- Optional bounded session snapshot, decoded by the same raw reader as the
adviser. Any malformed row makes the snapshot unknown. No recapture/query of
an unrelated compiler and no precomputed eligibility verdict. -/
def automaticPeak (root : FilePath) (context : Heavy.CompilerForecast.Context)
    (boot : String) (allowance parent : Int) : IO (Option Int × Nat) := do
  try
    let some bytes ← readRegular (root / "compiler-history.json").toString
        (fun mode size => decide (mode / 4096 % 16 = 8 ∧ size ≤ 16777473))
      | return (none, 0)
    let some text := String.fromUTF8? bytes | return (none, 0)
    let rows ← IO.ofExcept (Lean.Json.parse text >>= Lean.Json.getArr?)
    if rows.size > 256 then return (none, 0)
    let records ← IO.ofExcept (rows.toList.mapM CompilerAdvice.decode)
    let now ← IO.monoNanosNow
    let (peak, samples) := Heavy.CompilerForecast.advice records context boot
      (now - 604800000000000) now 2 2
    let paddingText ← match (← IO.getEnv "HEAVY_AUTOMATIC_PADDING_KIB") with
      | some text => pure (some text)
      | none => do
        let bytes ← readRegular (root / "compiler-padding").toString
          (fun mode size => decide (mode / 4096 % 16 = 8 ∧ size ≤ 32))
        pure (bytes.bind String.fromUTF8?)
    let some paddingText := paddingText | return (none, samples)
    if paddingText.utf8ByteSize > 32 then return (none, samples)
    let some padding := paddingText.toNat? | return (none, samples)
    return (Heavy.CompilerForecast.forSession peak padding allowance parent, samples)
  catch _ => return (none, 0)

/-- Canonical parent preserves missing-file diagnostics without pretending the
file bytes exist. Unresolvable parents remain explicitly unknown. -/
def memoryPath (path : String) : IO String := do
  try return (← IO.FS.realPath path).toString
  catch _ =>
    let p := FilePath.mk path
    try
      let parent ← IO.FS.realPath (p.parent.getD ".")
      return (parent / (p.fileName.getD "")).toString
    catch _ => return ""

def memorySourcePath (root : String) (args : List String) : IO String := do
  let parsed := parseMetadata args
  let mut source ← match parsed.bind (·.source) with
    | some s => memoryPath s
    | none => pure ""
  -- Ambiguous metadata must not silently bypass a possible selected source.
  if parsed.isNone then
    for arg in args do
      if arg.endsWith ".lean" then
        let candidate ← memoryPath arg
        if Heavy.ModuleMemory.selected root candidate then source := candidate
  return source

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
  -- Best effort only: missing boot identity cannot change the child's status.
  let boot ← try
    let value := (← IO.FS.readFile "/proc/sys/kernel/random/boot_id").trimAscii.copy
    pure (if value == "" then none else some value)
    catch _ => pure none
  let cwd ← IO.currentDir
  let parsed := parseMetadata args
  let source := parsed.bind (·.source)
  let sourceBefore ← source.mapM fun s => fingerprint s
  let setup := parsed.bind (·.setup)
  let setupBefore ← setup.mapM fun s => fingerprint s
  let compilerFingerprint ← fingerprint real
  let prepared ← preparedMetadata root real compilerFingerprint
  let (version, githash) ← match prepared with
    | some (version, githash) => pure (some version, some githash)
    | none => do pure (← compilerQuery real "--version", ← compilerQuery real "--githash")
  let gateDir ← IO.getEnv "HEAVY_BUDGET_DIR"
  let gated := gateDir.isSome && (parsed.map (·.kind)) != some "query"
  let cpuText ← IO.getEnv "HEAVY_COMPILER_CPU_SECONDS"
  let cpuSeconds ← match cpuText with
    | none => pure 0
    | some text => match text.toNat? with
      | some n => if n > 0 then pure n else throw (IO.userError "invalid compiler CPU limit")
      | none => throw (IO.userError "invalid compiler CPU limit")
  let some cpuLimit := compilerCpuLimit cpuSeconds gateDir.isSome ((parsed.map (·.kind)) == some "query")
    | throw (IO.userError "invalid compiler CPU limit or missing budget session")
  let wallText ← IO.getEnv "HEAVY_COMPILER_WALL_MS"
  let wallMs ← match wallText with
    | none => pure 0
    | some text => match text.toNat? with
      | some n => if n > 0 then pure n else throw (IO.userError "invalid compiler wall limit")
      | none => throw (IO.userError "invalid compiler wall limit")
  let some wallLimit := compilerWallLimit wallMs gateDir.isSome ((parsed.map (·.kind)) == some "query")
    | throw (IO.userError "invalid compiler wall limit or missing budget session")
  let memoryText ← IO.getEnv "HEAVY_COMPILER_MEMORY_BYTES"
  let memoryConfigured := match memoryText with
    | none => Heavy.ModuleMemory.defaultBytes
    | some text => if text.length > 16 then 0 else text.toNat?.getD 0
  let memoryRoot := (← IO.getEnv "HEAVY_MODULE_SOURCE_ROOT").getD ""
  let memorySource ← memorySourcePath memoryRoot args
  let memoryKind := (parsed.map (·.kind)).getD "unknown"
  let memoryPlan := Heavy.ModuleMemory.limit memoryRoot memorySource memoryKind memoryConfigured
  let memoryLimit := memoryPlan.getD (2^50 + 1)
  let memoryGroupRoot ← IO.getEnv "HEAVY_MODULE_MEMORY_ROOT"
  if !gated && memoryLimit != 0 then
    throw (IO.userError "selected module memory requires the ordinary budget session")
  let mut requestDemand := 0
  let mut provenance := ""
  let mut adviceSamples := 0
  let raw ← if gated then do
    let dir := FilePath.mk gateDir.get!
    let some configBytes ← readRegular (dir / "config").toString fingerprintAllowed
      | throw (IO.userError "unreadable budget config")
    let some config := String.fromUTF8? configBytes | throw (IO.userError "invalid budget config")
    let [allowance, parent, fallback, _] := BudgetAdapter.words config.trimAscii.copy
      | throw (IO.userError "malformed budget config")
    let some fallback := fallback.toNat? | throw (IO.userError "malformed fallback")
    let some allowance := allowance.toInt? | throw (IO.userError "malformed allowance")
    let some parent := parent.toInt? | throw (IO.userError "malformed parent headroom")
    let some bytes ← readRegular (dir / "requests").toString fingerprintAllowed
      | throw (IO.userError "unreadable request manifest")
    let some manifest := String.fromUTF8? bytes | throw (IO.userError "invalid request manifest")
    -- Identity is optional even when realPath fails: the compiler must still
    -- receive the original arguments and diagnose its own inaccessible input.
    let canonical ← try source.mapM fun s => do pure (← IO.FS.realPath s).toString
      catch _ => pure none
    let (requestSource, requestFingerprint) := Heavy.Budget.sourceIdentity canonical (sourceBefore.bind id)
    let context := do
      let source ← source
      let sourceFingerprint ← sourceBefore.bind id
      let compilerFingerprint ← compilerFingerprint
      let version ← version
      let githash ← githash
      let boot ← boot
      let setupFingerprint ← match setup, setupBefore with
        | none, none => some none
        | some _, some (some f) => some (some f)
        | _, _ => none
      let c : Heavy.CompilerForecast.Context := {
        source := source, cwd := cwd.toString, sourceFingerprint := sourceFingerprint
        compiler := real.toString, compilerFingerprint := compilerFingerprint
        version := version, githash := githash, args := args
        setup := setup, setupFingerprint := setupFingerprint }
      if Heavy.CompilerForecast.validContext c then some (c, boot) else none
    let cohort := context.bind fun (c, boot) => Heavy.CompilerForecast.cohortIdentity c boot
    let some (demand, origin) := BudgetAdapter.request manifest requestSource requestFingerprint fallback cohort
      | throw (IO.userError "invalid request demand")
    requestDemand := demand
    provenance := origin
    try
      if origin == "explicit-unknown-fallback" then
        if let some (c, currentBoot) := context then
          if cohort.isSome then
            let (estimate, samples) ← automaticPeak root c currentBoot allowance parent
            adviceSamples := samples
            if let some estimate := estimate then
              -- Revalidate the partial input after optional history IO, directly
              -- before admission. Mutation during admission/exec is still outside
              -- this snapshot contract, as are imports/environment closure.
              let sourceNow ← fingerprint c.source
              let compilerNow ← fingerprint c.compiler
              let setupNow ← c.setup.mapM fingerprint
              let cwdNow ← IO.currentDir
              let bootNow ← try pure (← IO.FS.readFile "/proc/sys/kernel/random/boot_id").trimAscii.copy
                catch _ => pure ""
              let canonicalNow ← try pure (some (← IO.FS.realPath c.source).toString)
                catch _ => pure none
              if sourceNow == some c.sourceFingerprint && compilerNow == some c.compilerFingerprint &&
                  setupNow.bind id == c.setupFingerprint && cwdNow == cwd && bootNow == currentBoot &&
                  canonicalNow == canonical then
                requestDemand := estimate.toNat
                provenance := "automatic-cohort-estimate"
    catch _ => pure () -- Optional IO failure leaves the positive fallback.
    observeBudget real.toString args.toArray dir.toString requestDemand.toUInt64 cpuLimit.toUInt64 wallLimit.toUInt64 memoryLimit.toUInt64 BudgetAdapter.snapshot BudgetAdapter.control
    else observe real.toString args.toArray
  if raw.size != (if gated then 41 else 18) then throw (IO.userError "invalid FFI observation length")
  let v := fun i => raw[i]!.toNat
  let gateError := if gated then v 18 else 0
  let childPresent := !gated || v 5 != 0
  let outcome := result (v 0) (v 1) (v 2) (v 4)
  let wall := if childPresent then elapsed (v 3) (v 6) (v 7) else none
  let measured := if childPresent then usage (v 0) (v 1) (v 2) (v 4) (v 8) (v 9) (v 10) else none
  -- Compare exactly the request and wait4 peak recorded below. Unsupported
  -- metadata, queries, no admission and missing usage are unknown, not zero.
  let requested := if gated && gateError == 0 && childPresent &&
      (parsed.map (·.kind)) == some "file" then some requestDemand else none
  let excess := requestExcess requested (measured.map (·.2))
  let inputClosure : Option String := none
  let complete := identityComplete (sourceBefore.bind id) compilerFingerprint inputClosure
  let outputs := [parsed.bind (·.olean), parsed.bind (·.ilean), parsed.bind (·.c), parsed.bind (·.bc)] |>.filterMap id
  -- Recording failures are explicitly separate from the available child outcome.
  try
    let artifacts ← outputs.mapM artifact
    let sourceAfter ← source.mapM fun s => fingerprint s
    let gateFields := if gated then [
      ("gate_errno", toString gateError), ("admission_wait_ns", toString (v 19)),
      ("admission_granted_ns", toString (v 24)),
      ("reservation_ticket", toString (v 20)), ("held_before_kib", toString (v 21)),
      ("allowance_kib", toString (v 22)), ("parent_headroom_kib", toString (v 23)),
      ("requested_reservation_kib", toString requestDemand), ("request_provenance", quoted provenance),
      ("automatic_sample_count", toString adviceSamples),
      ("child_present", toString childPresent),
      ("wrapper_code", if v 15 == 1 || v 17 != 0 then "null"
        else toString (if gateError != 0 || v 36 != 0 then 125 else outcome.shellCode))] else []
    let memoryFields := if gated then [
      ("compiler_memory_configured_text", jsonOption quoted memoryText),
      ("compiler_memory_configured_bytes", toString memoryConfigured),
      ("compiler_memory_source", quoted memorySource),
      ("compiler_memory_limit_bytes", jsonOption toString memoryPlan),
      ("compiler_memory_selected", toString (memoryLimit != 0)),
      ("compiler_memory_setup_errno", toString (v 26)),
      ("compiler_memory_readback_bytes", toString (v 27)),
      ("compiler_memory_swap_readback_bytes", toString (v 28)),
      ("compiler_memory_applied_bytes", if v 29 == 0 then "null" else toString (v 29)),
      ("compiler_memory_effective_bytes", if v 30 == 0 then "null" else toString (v 30)),
      ("compiler_memory_ack_pid", toString (v 31)),
      ("compiler_memory_expected_inode", toString (v 32)),
      ("compiler_memory_observed_inode", toString (v 33)),
      ("compiler_memory_oom_kill_delta", toString (v 34)),
      ("compiler_memory_peak_bytes", toString (v 35)),
      ("compiler_memory_cleanup_errno", toString (v 36)),
      ("compiler_memory_populated_after", toString (v 37)),
      ("compiler_memory_scope", if v 38 == 0 then "null" else
        jsonOption quoted (memoryGroupRoot.map fun p => p ++ s!"/m-{v 38}")),
      ("compiler_memory_aggregate_max_bytes", toString (v 39)),
      ("compiler_memory_oom_delta", toString (v 40))] else []
    let record := object (gateFields ++ memoryFields ++ [
      ("compiler_wall_requested_ms", if wallMs == 0 then "null" else toString wallMs),
      ("compiler_wall_applied_ms", if wallLimit == 0 || !childPresent then "null" else toString wallLimit),
      ("wall_timeout", toString (v 15 == 1)), ("wall_deadline_sample_ns", toString (v 16)),
      ("wall_control_errno", toString (v 17)),
      ("compiler_cpu_requested_seconds", if cpuSeconds == 0 then "null" else toString cpuSeconds),
      ("cpu_protocol_bytes", toString (v 11)), ("cpu_protocol_first", toString (v 12)),
      ("cpu_protocol_errno", toString (v 13)), ("cpu_protocol_eof", toString (v 14)),
      ("compiler_cpu_limit_seconds", jsonOption toString
        (appliedCompilerCpu cpuLimit (v 11) (v 12) (v 13) (v 14) (v 2))),
      ("boot_id", jsonOption quoted boot),
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
      ("request_excess_kib", jsonOption toString excess),
      ("result_kind", if childPresent then toString outcome.kind else "null"), ("result_detail", if childPresent then toString outcome.detail else "null"),
      ("shell_code", if childPresent then toString outcome.shellCode else "null")])
    let dir := (← IO.getEnv "HEAVY_OBSERVE_DIR").map FilePath.mk |>.getD (root / "records")
    -- Atomic publication gives each invocation its own file, avoiding JSONL races.
    IO.FS.createDirAll dir
    let err ← writeRecord dir.toString record
    if err != 0 then warn s!"record failed (errno {err}): {dir}"
    -- Persistence is optional; neither its failure nor its status replaces
    -- the observed compiler result. The private receipt is written first.
    if gated && err == 0 then
      let currentBoot := boot.getD ""
      let now ← IO.monoNanosNow
      let candidate : Option Unit := do
        let source ← source
        let before ← sourceBefore.bind id
        let after ← sourceAfter.bind id
        let compilerFp ← compilerFingerprint
        let version ← version
        let githash ← githash
        let peak ← measured.map (fun (usage : Nat × Nat) => usage.2)
        let setupFp ← match setup, setupBefore with
          | none, none => some none
          | some _, some (some f) => some (some f)
          | _, _ => none
        let context : Heavy.CompilerForecast.Context := {
          source, cwd := cwd.toString, sourceFingerprint := before,
          compiler := real.toString, compilerFingerprint := compilerFp,
          version, githash, args, setup, setupFingerprint := setupFp }
        let sample : Heavy.CompilerForecast.Record := {
          context, sourceAfter := after, boot, schema := 3, family := "lean",
          kind := (parsed.map (fun (metadata : Metadata) => metadata.kind)).getD "unknown", launchError := v 0,
          execError := v 1, waitError := v 2, clockError := v 3, status := v 4,
          pid := v 5, gateError := some gateError, childPresent := some childPresent,
          wrapperCode := if v 15 == 1 || v 17 != 0 then none else
            some (if gateError != 0 || v 36 != 0 then 125 else outcome.shellCode),
          start := v 6, finish := v 7, rss := v 10, measuredRss := peak }
        if Heavy.CompilerForecast.eligible sample context currentBoot (now - 604800000000000) now
          && (Heavy.CompilerForecast.cohortIdentity context currentBoot).isSome
        then some () else none
      if candidate.isSome then
        if let some publisher ← IO.getEnv "HEAVY_OBSERVE_PUBLISHER" then
          publishOptional publisher record
  catch e => warn s!"record failed: {e}"
  if gated && (v 15 == 1 || v 17 != 0) then
    if v 17 != 0 then return 125
    return 124
  if gated && v 36 != 0 then
    warn s!"module memory cleanup unknown (errno {v 36}); physical root status {v 4}"
    return 125
  if gateError != 0 then
    warn s!"budget control failed (errno {gateError}); child present={childPresent}"
    return 125
  if outcome.kind == 2 then warn s!"exec failed (errno {outcome.detail}): {real}"
  if outcome.kind == 3 then warn s!"observation failed (errno {outcome.detail})"
  if outcome.kind == 1 then terminateBySignal outcome.detail.toUInt32
  return outcome.shellCode.toUInt32

def main (args : List String) : IO UInt32 := do
  -- Only the standalone tool classifies the ordinary wrapper's raw Lean tail;
  -- an overlay named lean always forwards even these same arguments.
  if (← IO.appPath).fileName == some "heavy_observe" then
    if let "--classify-direct" :: root :: tail := args then
      let selected := Heavy.ModuleMemory.directFile tail &&
        Heavy.ModuleMemory.selected root (← memorySourcePath root tail)
      IO.println (if selected then "selected" else "unselected")
      return 0
  -- Only overlay.py's short-lived private copy can select preparation. Even
  -- identical arguments to bin/lean continue to reach the actual compiler.
  if (← IO.appPath).fileName == some ".prepare-compiler-metadata" then
    try
      if let [real, output] := args then prepareMetadata real output
    catch _ => pure ()
    return 0
  try run args
  catch e =>
    warn s!"setup failed: {e}"
    return 125
