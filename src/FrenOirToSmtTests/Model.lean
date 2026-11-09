module

public import FrenOirToSmtTests.Support
import Plausible

public section
namespace FrenOirToSmtTests
open FrenOirToSmt Fren Plausible
open scoped Plausible.Decorations

private def modelSource : String := "mod readback\nenum A { One, Two }\nenum B { One }\n\
  fn choose(a: A): Int := match a { A::One => -3, A::Two => 7 }\n\
  fn bump(n: Int): Int := let n := n + 1 in n\n\
  expect c(b: Bool, n: Int, a: A) { assume yes: b assume neg: n = -3\n\
    assume ctor: a = A::One expect wrong: choose(a) = bump(n) }\n\
  expect empty() { expect wrong: false expect right: true }"

private def select (out : Program) (kind : FrenOir.Kind) (owner : String) : IO Nat := do
  let some i := out.queries.findIdx? (fun e => e.question.kind == kind &&
    e.question.owner.component == some (.named owner)) | throw (IO.userError "missing model question")
  return i

private def decoderSample (out : Program) (q : FrenOir.Question) (n : Nat) (b : Bool) : Bool := Id.run do
  let k : Int := if n % 2 == 0 then Int.ofNat (n % 10000) else -Int.ofNat (n % 10000 + 1)
  let ctor := n % 2
  let bool := if b then "true" else "false"
  let text := s!"sat ((P2 C0_{ctor}) (true true) (P0 {bool}) (P1 {integer k}))"
  let some e := out.oir.enumerations[0]? | return false
  let some (id, _) := e.constructors[ctor]? | return false
  let expected := #[FrenEval.Value.bool b, .int k, .enum e.id id]
  let accepted := (decodeModel out.oir q text).toOption == some expected
  let mutations := #[text.replace "P0" "P1", text.replace "P2" "P3",
    text.replace "C0_" "C1_", text ++ " unsat", text.replace "true true" "true false",
    text.replace s!"P0 {bool}" "P0 0", text.replace (integer k) "(- 0)", text.dropEnd 1 |>.toString]
  return accepted && mutations.all (fun bad => !(decodeModel out.oir q bad).isOk)

private def checkProperty (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated
    {numInst := 100, maxSize := 40, randomSeed := some 20261109}
  IO.println s!"actual model decoder Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "model decoder property")

def runModelReadback : IO Unit := do
  let p ← load modelSource
  let .ok out := produce p | throw (IO.userError "model production")
  let i ← select out .validity "c"
  let some entry := out.queries[i]? | throw (IO.userError "model query")
  let q := entry.question
  for bad in #["", "sat", "unsat ((true true))", "sat ()", "sat ((P0 true))",
      "sat ((true true) (P0 true) (P1 0) (P2 C0_0) (P0 true))",
      "sat ((true true) (P0 true) (P1 0) (P2 C0_9))",
      "sat ((true true) (P0 true) (P1 false) (P2 C0_0))",
      "sat ((true true) (P0 true) (P1 01) (P2 C0_0))",
      "sat ((true true) (P0 true) (P1 (+ 1 2)) (P2 C0_0))",
      "sat ((true true) (P0 true) (P1 0) (P2 C1_0))",
      "sat ((true true) (P0 true) (P1 0) (P2 C0_0)); diagnostic",
      "sat ((true true) (P0 true) (P1 0) (P2 C0_0)) (error diagnostic)"] do
    require (!(decodeModel out.oir q bad).isOk) s!"accepted malformed model: {bad}"
  require (!(decodeModel out.oir q "sat ((true true))" 1).isOk) "decoder byte cap"
  checkProperty <| ∀ (n : Nat) (b : Bool), decoderSample out q n b = true
  for n in [0, 1, 7, 104729, 4294967295] do
    for b in [true, false] do require (decoderSample out q n b) "decoder regression seed"
  let .ok run ← solveModels p | throw (IO.userError "model solver")
  require (run.program.queries.map (·.question) == out.queries.map (·.question)) "model changed question envelope"
  let mut accepted := 0
  for r in run.results do
    evidence "model" (Lean.Json.mkObj [("question", Lean.toJson (reprStr r.raw.query.question)),
      ("script", Lean.toJson r.raw.query.script.toOption),
      ("first", r.raw.receipt.map receiptJson |>.getD Lean.Json.null),
      ("model_request", Lean.toJson r.modelRequest),
      ("second", r.modelReceipt.map receiptJson |>.getD Lean.Json.null),
      ("assignment", Lean.toJson (reprStr r.assignment)),
      ("confirmation", Lean.toJson (reprStr r.confirmation))])
    if r.raw.outcome == .sat then
      require r.assignment.isOk s!"actual solver model rejected: {reprStr r}"
      let some first := r.raw.receipt | throw (IO.userError "first model receipt")
      let some second := r.modelReceipt | throw (IO.userError "second model receipt")
      require (second.command == first.command && modelData second) "model solver provenance"
      require (r.modelRequest == (modelScript r.raw.query).toOption) "model request changed original search"
      accepted := accepted + 1
    else
      require (r.modelReceipt.isNone && r.modelRequest.isNone && !r.assignment.isOk) "model requested for non-SAT"
  require (accepted == 4) s!"actual SAT readback census {accepted}"
  let some real := run.results[i]? | throw (IO.userError "actual assignment")
  require ((real.assignment.toOption.map (·[1]?)) == some (some (.int (-3)))) "negative integer readback"
  IO.println "model-readback: 4 real cvc5 models (Bool/negative Int/nominal enum/zero parameters); 100 Plausible accepted and 800 rejected cases, discarded=0; 10 deterministic accepted and 80 rejected regressions; 14 malformed/size controls"

def runSourceConfirmation : IO Unit := do
  let p ← load modelSource
  let .ok out := produce p | throw (IO.userError "source confirmation production")
  let i ← select out .validity "c"
  let sat ← select out .assumptionsSatisfiable "c"
  let some e := out.oir.enumerations[0]? | throw (IO.userError "source enum")
  let some (ctor, _) := e.constructors[0]? | throw (IO.userError "source constructor")
  let values := #[FrenEval.Value.bool true, .int (-3), .enum e.id ctor]
  require (confirmAssignment p i values == .counterexample) "real source counterexample"
  require (confirmAssignment p sat values == .witness) "real source premise witness"
  require (confirmAssignment p i (values.set! 0 (.bool false)) == .rejected "source premise is false")
    "SMT-shaped false premise accepted"
  require (confirmAssignment p i (values.set! 1 (.int 0)) == .rejected "source premise is false")
    "wrong source integer premise accepted"
  require (confirmAssignment p i #[] == .rejected "assignment arity") "missing assignment"
  require (confirmAssignment p i (values.set! 0 (.int 0)) == .rejected "assignment sort or enum membership")
    "wrong assignment sort"
  require (confirmAssignment p i (values.set! 2 (.enum e.id e.id)) == .rejected "assignment sort or enum membership")
    "invented constructor accepted"
  match confirmAssignment p i values 0 with
  | .unconfirmed _ => pure ()
  | _ => throw (IO.userError "source evaluation exhaustion became confirmation")
  let goal ← load "mod source\nexpect c(n: Int) { expect wrong: n = 0 }"
  let .ok goals := produce goal | throw (IO.userError "source goal production")
  let gi ← select goals .validity "c"
  let some q := goals.queries[gi]? | throw (IO.userError "source goal query")
  -- Shape/sort-valid SMT data is insufficient: actual source polarity rejects it.
  let .ok same := decodeModel goals.oir q.question "sat ((true true) (P0 0))"
    | throw (IO.userError "SMT-shaped control decoding")
  require (confirmAssignment goal gi same == .rejected "source goal is true") "false counterexample accepted"
  let .ok originalRequest := modelScript q | throw (IO.userError "mutation model request")
  let changedRequest := originalRequest.replace "(not (= P0 0))" "(= P0 0)"
  require (changedRequest != originalRequest) "polarity mutation did not affect actual SMT"
  let changedReceipt ← ask changedRequest
  evidence "source-rejected-model" (Lean.Json.mkObj [
    ("original_request", Lean.toJson originalRequest), ("changed_request", Lean.toJson changedRequest),
    ("receipt", receiptJson changedReceipt)])
  require (modelData changedReceipt) "mutated actual SMT did not return model data"
  let .ok changedValues := decodeModel goals.oir q.question changedReceipt.stdout
    | throw (IO.userError "mutated actual SMT model decoding")
  require (confirmAssignment goal gi changedValues == .rejected "source goal is true")
    "actual SMT polarity mutant escaped source interpreter"
  -- Strict confirmation evaluates every retained operand, unused let and
  -- callee step; only an explicit if/match guard selects what it evaluates.
  for (expression, strict) in [("false and (1 div 0 = 0)", false), ("true or (1 div 0 = 0)", false),
      ("let x := 1 div 0 in false", false), ("skip(0)", false),
      ("if true then false else 1 div 0 = 0", true), ("half(3) = 2", true)] do
    let partialInput ← load ("mod partial\nfn skip(x: Int): Bool := false and 1 div x = 0\n" ++
      "fn half(x: Int): Int := x div 2\nexpect c() { expect wrong: " ++ expression ++ " }")
    let .ok partialOut := produce partialInput | throw (IO.userError "partial source production")
    let pi ← select partialOut .validity "c"
    match confirmAssignment partialInput pi #[], strict with
    | .unconfirmed reason, false =>
      require (reason.startsWith "source goal evaluation: strict: ") s!"{expression}: {reason}"
    | .counterexample, true => pure ()
    | other, _ => throw (IO.userError s!"strict confirmation of {expression}: {reprStr other}")
  let cyclicInput ← load "mod partial\nexpect c(d: Int) { assume a: 1 div d = 0 assume b: 1 div d != 0 expect wrong: false }"
  let .ok mutualOut := produce cyclicInput | throw (IO.userError "mutual source production")
  let mi ← select mutualOut .validity "c"
  require (confirmAssignment cyclicInput mi #[.int 1] == .unconfirmed "unresolved question readiness")
    "unresolved dependencies confirmed"
  let .ok real ← solveModels p | throw (IO.userError "actual source model run")
  require ((real.results[i]?).any (·.confirmation == .counterexample)) "actual model not source-confirmed"
  require ((real.results[sat]?).any (·.confirmation == .witness)) "actual witness not source-confirmed"
  -- Reuse bounded transport controls directly at the new admission boundary.
  let root ← sourceRoot
  let fake := (root / "src/FrenOirToSmtTests/fake_solver.py").toString
  for mode in ["unknown", "unsupported", "nonzero", "bytes", "protocol", "stderr", "flood", "sleep", "hold-input"] do
    let receipt ← transport #["python3", fake, mode] "(get-value (true))\n" {wallMs := 100, outputBytes := 64}
    evidence ("readback-" ++ mode) (receiptJson receipt)
    let decoded : Except String (Array FrenEval.Value) := if modelData receipt then
      decodeModel goals.oir q.question receipt.stdout 64
      else .error "ineligible model transport"
    require (!decoded.isOk) s!"failed model transport decoded: {mode}"
  let input ← transport #["/bin/false"] "too long" {inputBytes := 1}
  evidence "readback-input" (receiptJson input)
  require (!modelData input) "model stdin cap admitted"
  require (classify (some 0) "unsat\n(error diagnostic)" "" "finished" "" != .unsat)
    "ordinary classifier weakened"
  IO.println "source-confirmation: actual retained source interpreter witness/counterexample; false premise/true goal/arity/sort/enum rejects; evaluator exhaustion, 4 strictly undefined forms and unresolved readiness unconfirmed; guarded and total dividing goals confirmed; 10 bounded transport failure controls"

#print axioms FrenOirToSmt.wrong_bool
#print axioms FrenOirToSmt.strict_operand
#print axioms FrenOirToSmt.strict_div_zero
#print axioms FrenOirToSmt.model_nonzero

end FrenOirToSmtTests
