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
      "let unused := 1 div 0 in true"] do
    let r ← runSource "static" ("mod checker\nexpect c() { expect goal: " ++ expression ++ " }")
    require (r.verdict == .refuted && r.checks.any (fun r => isNonzero ⟨⟨r.question, .ok ""⟩, .sat, none⟩))
      "static undefinedness/guard obligations disappeared"
  let unused ← runSource "unused"
    "mod checker\nfn unused(x: Int): Int := let bad := 1 div 0 in x\nexpect c() { expect good: true }"
  require (unused.verdict == .refuted && unused.checks.any (fun r =>
    r.question.owner.component == some (.named "unused") && r.status == .counterexample))
    "unused definition static obligations not source-confirmed"
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
  for (mode, expected) in [("unknown", CheckStatus.unknown), ("unsupported", .unsupported),
      ("nonzero", .processFailure), ("protocol", .processFailure), ("stderr", .processFailure),
      ("bytes", .processFailure), ("sleep", .resourceExhausted), ("flood", .resourceExhausted)] do
    let fake ← fakeSolver mode
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
  let undefined ← runSource "definedness-confirmation"
    "mod checker\nexpect c() { expect goal: 1 div 0 = 0 }"
  require (undefined.verdict == .refuted && undefined.checks.any (fun r =>
    r.status == .counterexample && r.modelRef.isSome))
    "reachable undefinedness not confirmed"
  require ((← runSource "invalid" "mod checker\nexpect c() { expect bad: absent }").verdict == .inputFailure)
    "invalid source admitted"
  IO.println s!"checker-entry-controls: {(← IO.monoMsNow) - started} ms; model absence/staleness/conflict, cross-program/source/owner; 8 owned process controls through actual consumer; real source input/resource/unknown/definedness/admission failures"

/-- Source-site confirmation is checked separately from raw solver answers.
The end-to-end corpus job also checks the public command's exit classes. -/
def runDefinednessControls : IO Unit := do
  for op in ["div", "%"] do
    for (label, text, expected) in [
        ("unrelated", s!"fn half(n: Int): Int := n {op} 2\nexpect c(a: Int) \{ expect good: a = a }", Verdict.verified),
        ("zero", s!"expect c(d: Int) \{ assume zero: d = 0 expect bad: 1 {op} d = 0 }", .refuted),
        ("false-guard", s!"expect c() \{ expect good: if false then 1 {op} 0 = 0 else true }", .verified),
        ("nonzero", s!"expect c(d: Int) \{ assume nz: d != 0 expect good: d {op} d = {if op == "div" then "1" else "0"} }", .verified),
        ("let-site", s!"expect c(d: Int) \{ expect bad: let x := d - d in 1 {op} x = 0 }", .refuted),
        ("shadow-site", s!"expect c(d: Int) \{ expect bad: let d := 1 in let d := d - 1 in 1 {op} d = 0 }", .refuted),
        ("nested-divisor", s!"expect c() \{ expect bad: 1 {op} (1 {op} 0) = 0 }", .refuted),
        ("undefined-guard", s!"expect c() \{ expect bad: if 1 {op} 0 = 0 then 1 {op} 0 = 0 else true }", .refuted),
        ("enum-site", s!"enum E \{ A, B }\nexpect c(e: E) \{ assume a: e = E::A expect bad: match e \{ E::A => 1 {op} 0 = 0, E::B => true } }", .refuted)] do
      let r ← runSource (op ++ "-" ++ label) ("mod sites\n" ++ text)
      require (r.verdict == expected) s!"{op}/{label}: {reprStr r.verdict}; {reprStr r.checks}"
      if expected == .refuted then
        let some run := r.run | throw (IO.userError "definedness run missing")
        if label == "nested-divisor" || label == "undefined-guard" then
          require (run.results.any (fun entry => match entry.confirmation with
            | .unconfirmed reason => reason.startsWith "source definedness evaluation:"
            | _ => false)) "undefined prefix evaluated as a counterexample"
        let some i := r.checks.findIdx? (·.status == .counterexample)
          | throw (IO.userError "definedness counterexample missing")
        let some model := run.results[i]? | throw (IO.userError "definedness model missing")
        require (model.confirmation == .counterexample && model.assignment.isOk &&
          model.modelReceipt.isSome && model.raw.receipt.isSome) "bare SAT refuted"
        let command ← solverCommand run.limits
        for changed in #[{model with modelReceipt := none},
            {model with confirmation := .witness},
            {model with modelReceipt := model.modelReceipt.map (fun m => {m with binding := "stale"})}] do
          require ((summarize run.source command {run with results := run.results.set! i changed}).verdict
            == .inconclusive) "definedness evidence binding bypass"
  let p ← load "mod sites\nexpect c(d: Int) { expect bad: if d = 0 then 1 div d = 0 else true }"
  let .ok out := produce p | throw (IO.userError "site control production")
  let some i := out.queries.findIdx? (fun q => isNonzero ⟨q, .sat, none⟩)
    | throw (IO.userError "nonzero question missing")
  require (confirmAssignment p i #[.int 0] == .counterexample) "source zero rejected"
  require (confirmAssignment p i #[.int 1] == .rejected "source site is unreachable")
    "unreachable if site not rejected"
  require (confirmAssignment p i #[.int 0] 0 != .counterexample) "exhausted site confirmed"
  let p ← load "mod sites\nenum E { A, B }\nexpect c(e: E) { expect bad: match e { E::A => 1 div 0 = 0, E::B => true } }"
  let .ok out := produce p | throw (IO.userError "match site control production")
  let some i := out.queries.findIdx? (fun q => isNonzero ⟨q, .sat, none⟩)
    | throw (IO.userError "match nonzero question missing")
  let some enumItem := out.oir.enumerations[0]? | throw (IO.userError "match enum missing")
  let some (ctor, _) := enumItem.constructors[1]?
    | throw (IO.userError "match constructor missing")
  -- Admission requires each arm's resolved reference to have role `.pattern`
  -- (FrenHirToThir.Typing.Selects and Coverage), so a different role cannot
  -- reach confirmation through an admitted program.
  require (confirmAssignment p i #[.enum enumItem.id ctor] == .rejected "source site is unreachable")
    "unreachable match site not rejected"
  let p ← load "mod sites\nexpect c(d: Int) { assume z: d = 0 expect bad: 1 % d = 0 }"
  let .ok out := produce p | throw (IO.userError "premise control production")
  let some i := out.queries.findIdx? (fun q => isNonzero ⟨q, .sat, none⟩)
    | throw (IO.userError "mod question missing")
  require (confirmAssignment p i #[.int 1] == .rejected "source premise is false") "false premise confirmed"
  let p ← load "mod sites\nexpect c(d: Int) { expect bad: 1 div d = 0 }"
  let .ok out := produce p | throw (IO.userError "divisor control production")
  let some i := out.queries.findIdx? (fun q => isNonzero ⟨q, .sat, none⟩)
    | throw (IO.userError "divisor question missing")
  require (confirmAssignment p i #[.int 2] == .rejected "source divisor is nonzero") "nonzero divisor confirmed"
  let guardFailure ← runSource "failed-prerequisite"
    "mod sites\nexpect c(d: Int) { expect bad: if 1 div 0 = 0 then d = d else d = d }"
  require (guardFailure.verdict == .refuted && guardFailure.checks.any (·.status == .blocked))
    "refuted guard definedness discharged a dependent question"
  -- Each level calls the one below twice; totality must visit each body once,
  -- or this 2^40 walk exceeds the job deadline.
  let levels := (List.range 39).map fun i =>
    s!"fn f{i + 1}(x: Int): Int := if x >= 0 then f{i}(x) else f{i}(x)"
  let p ← load ("mod sites\nfn f0(x: Int): Int := x\n" ++ "\n".intercalate levels ++
    "\nexpect c(a: Int) { assume p: f39(a) >= 0 expect good: a >= 0 }")
  let .ok out := produce p | throw (IO.userError "shared callee production")
  let some i := out.queries.findIdx? (·.question.kind == .assumptionsSatisfiable)
    | throw (IO.userError "shared callee witness question missing")
  require (confirmAssignment p i #[.int 0] == .witness) "shared callee witness not confirmed"
  -- Division-free bodies skip strict evaluation, so a short-circuited `and`
  -- whose skipped operand calls 2^40 times costs only the interpreter's walk.
  let levels := (List.range 39).map fun i => s!"fn g{i + 1}(x: Int): Bool := g{i}(x) and g{i}(x)"
  let p ← load ("mod sites\nfn g0(x: Int): Bool := x > 0\n" ++ "\n".intercalate levels ++
    "\nexpect c(a: Int) { assume p: g39(a) = false expect good: a <= 0 }")
  let .ok out := produce p | throw (IO.userError "short-circuit production")
  let some i := out.queries.findIdx? (·.question.kind == .assumptionsSatisfiable)
    | throw (IO.userError "short-circuit witness question missing")
  require (confirmAssignment p i #[.int 0] == .witness) "division-free witness not confirmed"
  IO.println "definedness-controls: div/mod source sites, bindings, guards, hypotheses, shared callees and physical evidence controls"

#print axioms FrenOirToSmt.stale_receipt
#print axioms FrenOirToSmt.empty_no_checks
#print axioms FrenOirToSmt.verified_all

end FrenOirToSmtTests
