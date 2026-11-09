module

public import FrenOirToSmtTests.Support
import Plausible

public section
namespace FrenOirToSmtTests
open FrenOirToSmt Plausible
open scoped Plausible.Decorations

private def goodSource : String := "mod checker\nfn next(n: Int): Int := n + 1\n\
  expect safe(n: Int) { assume nonnegative: n >= 0 expect grows: next(n) > n }\n\
  expect other() { expect tautology: true }"

private def reportEvidence (label : String) (report : Report) : IO Unit := do
  let rows := report.checks.map fun r => Lean.Json.mkObj [
    ("question", Lean.toJson (reprStr r.question)), ("location", Lean.toJson (reprStr r.location)),
    ("status", Lean.toJson (reprStr r.status)), ("reason", Lean.toJson r.reason),
    ("answer_ref", Lean.toJson r.answerRef), ("model_ref", Lean.toJson r.modelRef)]
  let raw := report.run.map fun run => run.results.map fun r => Lean.Json.mkObj [
    ("query", Lean.toJson (reprStr r.raw.query)),
    ("answer", r.raw.receipt.map receiptJson |>.getD Lean.Json.null),
    ("model_request", Lean.toJson r.modelRequest),
    ("model", r.modelReceipt.map receiptJson |>.getD Lean.Json.null),
    ("assignment", Lean.toJson (reprStr r.assignment)),
    ("confirmation", Lean.toJson (reprStr r.confirmation))]
  evidence ("checker-" ++ label) (Lean.Json.mkObj [
    ("verdict", Lean.toJson (reprStr report.verdict)), ("reason", Lean.toJson report.reason),
    ("checks", Lean.toJson rows), ("raw", Lean.toJson raw)])

private def runSource (label text : String) (limits : Limits := {}) : IO Report := do
  let r ← checkSource ⟨815⟩ text limits
  reportEvidence label r
  return r

/-- Mutate actual producer/process inputs at the real aggregation boundary,
without an implication that could discard rejected cases. -/
private def aggregationSample (p : FrenThirDesugar.Program) (command : Array String)
    (run : ModelRun) (n : Nat) : Bool := Id.run do
  if (summarize p command run).verdict != .verified || run.results.size < 2 then return false
  let i := n % run.results.size
  let j := (i + 1) % run.results.size
  let some a := run.results[i]? | return false
  let some b := run.results[j]? | return false
  let some receipt := a.raw.receipt | return false
  let change (entry : Readback) := {run with results := run.results.set! i entry}
  let missing := {run with results := run.results.pop}
  let duplicate := change b
  let shuffled := {run with results := run.results.reverse}
  let foreignId := change {a with raw := {a.raw with query := {a.raw.query with
    question := {a.raw.query.question with id := a.raw.query.question.id + n + 1}}}}
  let absent := change {a with raw := {a.raw with receipt := none}}
  let stale := change {a with raw := {a.raw with receipt := some {receipt with binding := "old-run"}}}
  let request := change {a with raw := {a.raw with receipt := some {receipt with request := "(check-sat)"}}}
  let commandBad := change {a with raw := {a.raw with receipt := some {receipt with command := #["/bin/true"]}}}
  let conflict := change {a with raw := {a.raw with outcome := .unknown "changed"}}
  let bytes := change {a with raw := {a.raw with receipt := some {receipt with stdoutHex := "00"}}}
  return #[missing, duplicate, shuffled, foreignId, absent, stale, request, commandBad, conflict, bytes].all
    (fun changed => (summarize p command changed).verdict != .verified)

private def property (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let r ← Testable.checkIO decorated {numInst := 100, maxSize := 40, randomSeed := some 20261110}
  IO.println s!"actual checker aggregation Plausible: {r}"
  match r with
  | .success _ => pure ()
  | _ => throw (IO.userError "actual checker aggregation property")

def runCheckerOutcomes : IO Unit := do
  let started ← IO.monoMsNow
  let good ← runSource "verified" goodSource
  require (good.verdict == .verified) s!"supported source not verified: {good.reason}; {reprStr good.checks}"
  let some run := good.run | throw (IO.userError "checker lost physical run")
  let p := run.source
  let command ← solverCommand run.limits
  require (good.checks.map (·.question) == run.program.oir.questions) "checker inventory retention"
  require (good.checks.all (fun r => r.answerRef.isSome && !r.reason.isEmpty)) "actionable evidence refs"
  require (good.checks.any (fun r => r.question.kind == .validity && r.location.isSome)) "source location"
  property <| ∀ n : Nat, aggregationSample p command run n = true
  for n in [0, 1, 2, 7, 104729] do
    require (aggregationSample p command run n) "deterministic aggregation mutation"
  let bad ← runSource "refuted" "mod checker\nexpect bad(n: Int) { assume a: n = 2 expect wrong: n = 3 }"
  require (bad.verdict == .refuted && bad.checks.any (fun r => r.status == .counterexample &&
    r.question.owner.component == some (.named "bad") && r.location.isSome && r.modelRef.isSome))
    "source counterexample missing attribution or confirmation"
  let inconsistent ← runSource "inconsistent"
    "mod checker\nexpect c(n: Int) { assume a: n = 0 assume b: n = 1 expect wrong: false }"
  require (inconsistent.verdict == .inconsistent && inconsistent.checks.any (·.status == .vacuous))
    "all-UNSAT inconsistent assumptions verified"
  let some inconsistentRun := inconsistent.run | throw (IO.userError "inconsistent run")
  require (inconsistentRun.results.all (·.raw.outcome == .unsat)) "all-UNSAT polarity control"
  for (label, text) in [("module", "mod empty"), ("block", "mod empty\nexpect empty() {}") ] do
    require ((← runSource label text).verdict == .noChecks) "no-checks reported verified"
  for expression in ["false and (1 div 0 = 0)", "true or (1 div 0 = 0)",
      "let unused := 1 div 0 in true", "if true then true else 1 div 0 = 0"] do
    let r ← runSource "static" ("mod checker\nexpect c() { expect goal: " ++ expression ++ " }")
    require (r.verdict == .inconclusive && r.checks.any (fun r => isNonzero ⟨⟨r.question, .ok ""⟩, .sat, none⟩))
      "static undefinedness/guard obligations disappeared"
  let unused ← runSource "unused"
    "mod checker\nfn unused(x: Int): Int := let bad := 1 div 0 in x\nexpect c() { expect good: true }"
  require (unused.verdict == .inconclusive && unused.checks.any (fun r =>
    r.question.owner.component == some (.named "unused") && r.status == .unconfirmed))
    "unused definition static obligations ignored or bare SAT confirmed"
  let cyclic ← runSource "unresolved"
    "mod checker\nexpect c(d: Int) { assume a: 1 div d = 0 assume b: 1 div d != 0 expect bad: false }"
  require (cyclic.verdict == .inconclusive && cyclic.checks.any (·.status == .blocked))
    "unresolved cyclic assumptions discharged"
  IO.println s!"checker-outcomes: {(← IO.monoMsNow) - started} ms; verified/refuted/inconsistent/no-checks; unused, both Boolean operands, binder/conditional and unresolved obligations; 100 accepted and 1000 rejected Plausible cases, discarded=0; 5 accepted and 50 rejected deterministic cases"

/-- Exercise owned physical failures through the same actual consumer. Only
this low-level test supplies an expected command; checkSource fixes cvc5 itself. -/
def runCheckerEntryControls : IO Unit := do
  let started ← IO.monoMsNow
  let good ← runSource "entry" goodSource
  let some run := good.run | throw (IO.userError "entry run")
  let command ← solverCommand run.limits
  let some i := run.results.findIdx? (·.raw.outcome == .sat) | throw (IO.userError "entry SAT")
  let some original := run.results[i]? | throw (IO.userError "entry result")
  let q := original.raw.query
  let change (r : Readback) := {run with results := run.results.set! i r}
  for r in #[{original with modelReceipt := none}, {original with modelRequest := none},
      {original with assignment := .ok #[]}, {original with confirmation := .counterexample},
      {original with modelReceipt := original.modelReceipt.map (fun r => {r with binding := "stale"})}] do
    require ((summarize run.source command (change r)).verdict != .verified) "model evidence bypass"
  let replay ← runSource "replay" goodSource
  let some replayRun := replay.run | throw (IO.userError "replayed source run")
  let some replayed := replayRun.results[i]? | throw (IO.userError "replayed SAT result")
  require (replayed.raw.query == original.raw.query &&
    replayed.raw.receipt.map (·.request) == original.raw.receipt.map (·.request)) "replay request differs"
  for r in #[{original with raw := {original.raw with receipt := replayed.raw.receipt}},
      {original with modelReceipt := replayed.modelReceipt}] do
    require ((summarize run.source command (change r)).verdict == .inconclusive) "actual stale process receipt accepted"
  let truncated := {run.program with queries := run.program.queries.pop}
  let skipped := {run with program := truncated, results := run.results.pop}
  require ((summarize run.source command skipped).verdict == .inconclusive) "self-consistent truncated inventory accepted"
  let other ← load (goodSource.replace "mod checker" "mod other")
  require ((summarize other command run).verdict == .inconclusive) "cross-program results accepted"
  let moved := {run with source := other}
  require ((summarize run.source command moved).verdict == .inconclusive) "cross-source witness accepted"
  let some foreign := run.results.find? (fun r => r.raw.query.question.owner != q.question.owner)
    | throw (IO.userError "cross-owner control")
  let wrong := {original with raw := {original.raw with query := {q with question :=
    {q.question with owner := foreign.raw.query.question.owner}}}}
  require ((summarize run.source command (change wrong)).verdict == .inconclusive) "cross-owner result accepted"
  let root ← sourceRoot
  for (mode, expected) in [("unknown", CheckStatus.unknown), ("unsupported", .unsupported),
      ("nonzero", .processFailure), ("protocol", .processFailure), ("stderr", .processFailure),
      ("bytes", .processFailure), ("sleep", .resourceExhausted), ("flood", .resourceExhausted)] do
    let fake := #["python3", (root / "src/FrenOirToSmtTests/fake_solver.py").toString, mode]
    let receipt ← transport fake (q.script.toOption.getD "") {wallMs := 100, outputBytes := 64}
      s!"{run.runId}/{i}/answer"
    let raw : Result := ⟨q, receipt.outcome, some receipt⟩
    let r : Readback := ⟨raw, none, none, .error "no SAT model", .unconfirmed "no SAT model"⟩
    let report := summarize run.source fake {change r with limits := {wallMs := 100, outputBytes := 64}}
    reportEvidence mode report
    require ((report.checks[i]?).any (·.status == expected) && report.verdict != .verified)
      s!"actual consumer lost physical failure {mode}"
  for (label, limits, expected) in [("input", {inputBytes := 1 : Limits}, CheckStatus.resourceExhausted),
      ("limits", {wallMs := 0}, .processFailure), ("unknown", {solverResources := 1}, .unknown)] do
    let r ← runSource label goodSource limits
    require (r.verdict == .inconclusive && r.checks.any (·.status == expected)) s!"source entry {label}"
  let exhausted ← checkSource ⟨815⟩ goodSource {} 0
  reportEvidence "evaluation-exhaustion" exhausted
  require (exhausted.verdict == .inconclusive && exhausted.checks.any (fun r =>
    r.status == .unconfirmed && r.reason.startsWith "source premise evaluation:"))
    "actual evaluator exhaustion became a false predicate or verification"
  let unsupported ← runSource "unsupported-confirmation"
    "mod checker\nexpect c() { expect goal: 1 div 0 = 0 }"
  require (unsupported.verdict == .inconclusive && unsupported.checks.any (fun r =>
    r.status == .unconfirmed && r.reason == "source definedness-site confirmation unsupported"))
    "unsupported definedness confirmation hidden"
  require ((← runSource "invalid" "mod checker\nexpect c() { expect bad: absent }").verdict == .inputFailure)
    "invalid source admitted"
  IO.println s!"checker-entry-controls: {(← IO.monoMsNow) - started} ms; model absence/staleness/conflict, cross-program/source/owner; 8 owned process controls through actual consumer; real source input/resource/unknown/unsupported/admission failures"

#print axioms FrenOirToSmt.stale_receipt
#print axioms FrenOirToSmt.empty_no_checks
#print axioms FrenOirToSmt.verified_all

end FrenOirToSmtTests
