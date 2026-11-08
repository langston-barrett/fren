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
  let raw ← observe real.toString args.toArray
  if raw.size != 11 then throw (IO.userError "invalid FFI observation length")
  let v := fun i => raw[i]!.toNat
  let outcome := result (v 0) (v 1) (v 2) (v 4)
  let wall := elapsed (v 3) (v 6) (v 7)
  let measured := usage (v 0) (v 1) (v 2) (v 4) (v 8) (v 9) (v 10)
  let inputClosure : Option String := none
  let complete := identityComplete (sourceBefore.bind id) compilerFingerprint inputClosure
  let outputs := [parsed.bind (·.olean), parsed.bind (·.ilean), parsed.bind (·.c), parsed.bind (·.bc)] |>.filterMap id
  -- Recording failures are explicitly separate from the available child outcome.
  try
    let artifacts ← outputs.mapM artifact
    let sourceAfter ← source.mapM fun s => fingerprint s
    let record := object [
      ("schema", "2"), ("family", quoted "lean"),
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
      ("result_kind", toString outcome.kind), ("result_detail", toString outcome.detail),
      ("shell_code", toString outcome.shellCode)]
    let dir := (← IO.getEnv "HEAVY_OBSERVE_DIR").map FilePath.mk |>.getD (root / "records")
    -- Atomic publication gives each invocation its own file, avoiding JSONL races.
    IO.FS.createDirAll dir
    let err ← writeRecord dir.toString record
    if err != 0 then warn s!"record failed (errno {err}): {dir}"
  catch e => warn s!"record failed: {e}"
  if outcome.kind == 2 then warn s!"exec failed (errno {outcome.detail}): {real}"
  if outcome.kind == 3 then warn s!"observation failed (errno {outcome.detail})"
  if outcome.kind == 1 then terminateBySignal outcome.detail.toUInt32
  return outcome.shellCode.toUInt32

def main (args : List String) : IO UInt32 := do
  try run args
  catch e =>
    warn s!"setup failed: {e}"
    return 125
