module

public import FrenOirToSmt

public section
namespace FrenCli2
open FrenOirToSmt Lean

/-- Limits are per physical solver invocation, not a whole-file deadline. -/
structure Config where
  limits : Limits := {}
  evaluationDepth : Nat := 10000
  deriving Repr

def Config.valid (c : Config) : Bool :=
  c.limits.wallMs > 0 && c.limits.wallMs ≤ 10000 &&
  c.limits.solverMs > 0 && c.limits.solverMs ≤ 10000 &&
  c.limits.solverResources > 0 && c.limits.solverResources ≤ 1000000000 &&
  c.limits.inputBytes > 0 && c.limits.inputBytes ≤ 1048576 &&
  c.limits.outputBytes > 0 && c.limits.outputBytes ≤ 1048576 && c.evaluationDepth ≤ 10000

def exitCode : Verdict → UInt32
  | .verified => 0
  | .refuted => 1
  | .inconsistent => 2
  | .inconclusive => 3
  | .noChecks => 4
  | .inputFailure => 5

def verdictName : Verdict → String
  | .verified => "verified" | .refuted => "refuted" | .inconsistent => "inconsistent"
  | .inconclusive => "inconclusive" | .noChecks => "noChecks" | .inputFailure => "inputFailure"

def statusName : CheckStatus → String
  | .verified => "verified" | .witness => "witness" | .counterexample => "counterexample"
  | .inconsistent => "inconsistent" | .vacuous => "vacuous" | .unconfirmed => "unconfirmed"
  | .blocked => "blocked" | .unknown => "unknown" | .unsupported => "unsupported"
  | .resourceExhausted => "resourceExhausted" | .processFailure => "processFailure"
  | .invalidEvidence => "invalidEvidence"

structure Result where
  report : Report
  diagnostic : Option FrenDiag.Diagnostic := none

private def inputFailure (reason : String) (diagnostic : Option FrenDiag.Diagnostic := none) : Result :=
  ⟨⟨.inputFailure, reason, #[], none⟩, diagnostic⟩

private def staticDiagnostic : FrenHirToThir.StaticFailure → FrenDiag.Diagnostic
  | .typing d => d
  | .validation f =>
    let span := match f with
      | .coverage s .. | .invalidMetadata s | .cycle s _ => s
    ⟨none, reprStr f, span⟩

/-- Reuse the admitted source producer, then the production checker. No IR or
caller-supplied solver answer can enter this interface. File identity is local
to this single-file invocation; byte offsets refer to the unchanged text. -/
def checkText (text : String) (c : Config := {}) : IO Result := do
  unless c.valid do return inputFailure "invalid bounded configuration"
  if text.utf8ByteSize > 1048576 then return inputFailure "source exceeds 1048576 bytes"
  match FrenThirDesugar.fromSource ⟨0⟩ text with
  | .error e =>
    let d := staticDiagnostic e
    return inputFailure d.headline (some d)
  | .ok p => return ⟨← FrenOirToSmt.check p c.limits c.evaluationDepth, none⟩

/-- Read at most the source cap plus one byte; never normalize EOLs or replace
invalid UTF-8. Paths are passed directly to the filesystem, never a shell. -/
def checkFile (path : System.FilePath) (c : Config := {}) : IO Result := do
  try
    let handle ← IO.FS.Handle.mk path .read
    let mut bytes := ByteArray.empty
    repeat
      let chunk ← handle.read (USize.ofNat (1048577 - bytes.size))
      bytes := bytes ++ chunk
      if chunk.isEmpty || bytes.size > 1048576 then break
    if bytes.size > 1048576 then return inputFailure "source exceeds 1048576 bytes"
    let some text := String.fromUTF8? bytes | return inputFailure "source is not valid UTF-8"
    checkText text c
  catch e => return inputFailure ("source read failed: " ++ e.toString)

private def clip (s : String) (n : Nat := 1024) : String :=
  if s.length ≤ n then s else (s.take n).toString ++ "… [truncated]"

private def spanJson (s : FrenSource.Span) : Json := Json.mkObj [
  ("file_id", toJson s.file.value), ("start_byte", toJson s.start), ("stop_byte", toJson s.stop)]

private def valueText : FrenEval.Value → String
  | .bool b => toString b | .int n => toString n | .enum _ c => c.render

private def summary (report : Report) (index : Nat) : Json := Id.run do
  let some run := report.run | return Json.null
  let some r := run.results[index]? | return Json.null
  let .ok values := r.assignment | return Json.null
  let entries := (values.zipIdx.extract 0 16).map fun (v, i) => Json.mkObj [
    ("parameter_index", toJson i), ("value", toJson (clip (valueText v) 256))]
  return Json.mkObj [("confirmation", toJson (clip (reprStr r.confirmation))),
    ("values", toJson entries), ("omitted_values", toJson (values.size - entries.size))]

/-- Retain every question, including blocked ones. Only explanatory strings
and assignment previews are shortened, with explicit truncation markers. Raw
SMT scripts and models remain in the library report, not the command output. -/
def resultJson (path : String) (c : Config) (r : Result) : Json :=
  let report := r.report
  let rows := report.checks.mapIdx fun i row => Json.mkObj [
    ("id", toJson row.question.id), ("owner", toJson (clip row.question.owner.render)),
    ("kind", toJson (reprStr row.question.kind)),
    ("location", row.location.map spanJson |>.getD Json.null),
    ("status", toJson (statusName row.status)), ("reason", toJson (clip row.reason)),
    ("answer_ref", toJson row.answerRef), ("model_ref", toJson row.modelRef),
    ("assignment_summary", summary report i)]
  Json.mkObj [("file", toJson path), ("verdict", toJson (verdictName report.verdict)),
    ("exit_code", toJson (exitCode report.verdict).toNat), ("reason", toJson (clip report.reason)),
    ("diagnostic", r.diagnostic.map (fun d => Json.mkObj [
      ("code", toJson d.code), ("message", toJson (clip d.headline)), ("location", spanJson d.span)])
      |>.getD Json.null),
    ("limits", Json.mkObj [("wall_ms", toJson c.limits.wallMs), ("solver_ms", toJson c.limits.solverMs),
      ("solver_resources", toJson c.limits.solverResources), ("input_bytes", toJson c.limits.inputBytes),
      ("output_bytes", toJson c.limits.outputBytes), ("evaluation_depth", toJson c.evaluationDepth)]),
    ("checks", toJson rows)]

private def setLimit (c : Config) (flag : String) (n : Nat) : Except String Config := do
  let c ← match flag with
    | "--wall-ms" => pure {c with limits.wallMs := n}
    | "--solver-ms" => pure {c with limits.solverMs := n}
    | "--solver-resources" => pure {c with limits.solverResources := n}
    | "--input-bytes" => pure {c with limits.inputBytes := n}
    | "--output-bytes" => pure {c with limits.outputBytes := n}
    | "--evaluation-depth" => pure {c with evaluationDepth := n}
    | _ => throw ("unknown option: " ++ flag)
  unless c.valid do throw ("out-of-range limit: " ++ flag)
  return c

/-- One file, with `--` for a filename beginning with a dash. -/
def parseArgs : List String → Config → Except String (Config × String)
  | ["--", path], c => .ok (c, path)
  | [path], c => if path.startsWith "-" then .error "expected a source file (use -- before dash paths)"
      else .ok (c, path)
  | flag :: value :: rest, c => do
    unless flag.startsWith "--" && value.length ≤ 10 && !value.isEmpty && value.all Char.isDigit do
      throw "expected options followed by one source file"
    let some n := value.toNat? | throw "expected a decimal limit"
    let c ← setLimit c flag n
    parseArgs rest c
  | _, _ => .error "expected one source file; use --help"

def help : String := "Usage: fren2_check [LIMIT VALUE ...] [--] FILE\n\
  --wall-ms N            per solver process, 1..10000 (default 2000)\n\
  --solver-ms N          cvc5 per-query time, 1..10000 (default 1000)\n\
  --solver-resources N   cvc5 per-query resources, 1..1000000000 (default 1000000)\n\
  --input-bytes N        per solver script, 1..1048576 (default 1048576)\n\
  --output-bytes N       per solver output, 1..1048576 (default 65536)\n\
  --evaluation-depth N   source confirmation, 0..10000 (default 10000)\n\
JSON output; source cap 1048576 UTF-8 bytes. Uses the shipped pinned cvc5.\n\
Exit: 0 verified, 1 refuted, 2 inconsistent, 3 inconclusive, 4 noChecks, 5 inputFailure.\n\
Verification is conditional on current solver/encoding/source-evaluation trust boundaries."

def run (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println help
    return 0
  let (c, path) ← match parseArgs args {} with
    | .ok parsed => pure parsed
    | .error reason =>
      IO.println ((resultJson "" {} (inputFailure reason)).compress)
      return 5
  let r ← checkFile path c
  IO.println ((resultJson path c r).compress)
  return exitCode r.report.verdict

end FrenCli2
