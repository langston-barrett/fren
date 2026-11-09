module

public import FrenOirToSmt

public section
namespace FrenOirToSmtTests
open FrenOirToSmt

def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def load (text : String) : IO FrenThirDesugar.Program :=
  match FrenThirDesugar.fromSource ⟨811⟩ text with
  | .ok p => pure p
  | .error e => throw (IO.userError (reprStr e))

def results (text : String) : IO (Program × Array Result) := do
  let p ← load text
  match ← solve p with
  | .ok r => return r
  | .error e => throw (IO.userError (reprStr e))

def name (r : Result) : String := r.query.question.owner.component.map (fun c => match c with
  | .named n => n | .generated n _ => n) |>.getD "missing"

def label (r : Result) : String :=
  r.query.question.subject.bind (fun b => b.member.map (·.label.text)) |>.getD "missing"

def isDomain (r : Result) : Bool :=
  [.functionDefinedness, .assumptionDefinedness, .goalDefinedness].contains r.query.question.kind

def isNonzero (r : Result) : Bool := match r.query.question.condition with
  | .binary .ne _ (.int 0) => true
  | _ => false

def answer (rs : Array Result) (owner member : String) (expected : Outcome) : IO Unit := do
  let selected := rs.filter (fun r => name r == owner && label r == member &&
    r.query.question.kind == .validity)
  require (selected.size == 1) s!"expected one validity {owner}/{member}"
  for r in selected do
    require (r.outcome == expected) s!"{owner}/{member}: {reprStr r.outcome}; {reprStr r.receipt}"

def receiptJson (r : Receipt) : Lean.Json := Lean.Json.mkObj [
  ("command", Lean.toJson r.command), ("exit_code", Lean.toJson r.exitCode),
  ("stdout", Lean.toJson r.stdout), ("stderr", Lean.toJson r.stderr),
  ("stdout_hex", Lean.toJson r.stdoutHex), ("stderr_hex", Lean.toJson r.stderrHex),
  ("elapsed_ms", Lean.toJson r.elapsedMs), ("reason", Lean.toJson r.reason),
  ("outcome", Lean.toJson (reprStr r.outcome))]

initialize evidenceIndex : IO.Ref Nat ← IO.mkRef 0

def evidence (stem : String) (value : Lean.Json) : IO Unit := do
  if let some dir ← IO.getEnv "FREN2_SMT_EVIDENCE_DIR" then
    IO.FS.createDirAll dir
    let index ← evidenceIndex.modifyGet (fun i => (i, i + 1))
    let file := System.FilePath.mk dir / s!"{← IO.Process.getPID}-{stem}-{index}.json"
    IO.FS.writeFile file (value.pretty ++ "\n")

def ask (script : String) (limits : Limits := {}) : IO Receipt := do
  let r ← transport (← solverCommand limits) script limits
  evidence "query" (Lean.Json.mkObj [("script", Lean.toJson script), ("receipt", receiptJson r)])
  return r

def validityScript (p : Program) (owner member : String) : IO String := do
  let some q := p.queries.find? (fun q => q.question.owner.component == some (.named owner) &&
    q.question.subject.bind (fun b => b.member.map (·.label.text)) == some member && q.question.kind == .validity)
    | throw (IO.userError "missing validity script")
  match q.script with
  | .ok s => return s
  | .error e => throw (IO.userError (reprStr e))

end FrenOirToSmtTests
