module

public import FrenOirToSmt.Producer
public import FrenOirToSmt.Model
public import FrenEval

public section
namespace FrenOirToSmt

inductive Confirmation where
  | witness
  | counterexample
  | rejected (reason : String)
  | unconfirmed (reason : String)
  deriving Repr, BEq

/-- A conservative syntactic domain, independent of runtime demand. In
particular partial operations in unused lets, skipped operands and unselected
branches prevent confirmation. Every named body is checked, including callees. -/
@[expose] def confirmationFragment : Nat → FrenAst.Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    let go := confirmationFragment n
    match e with
    | .bool .. | .integer .. | .name .. => true
    | .paren _ e _ | .unary _ _ e => go e
    | .binary a _ op b => match op with
      | .div | .mod => false
      | _ => go a && go b
    | .ifE _ c _ a _ b => go c && go a && go b
    | .letE _ _ _ a _ b => go a && go b
    | .matchE _ e _ arms _ => go e && arms.all (fun (_, _, arm, _) => go arm)
    | .call f _ args _ _ => go f && args.all go

private def sourceBoolean (p : FrenEval.Program) (b : FrenModule.TypedBody)
    (values : Array FrenEval.Value) (depth : Nat) : Except String Bool := do
  let e ← (FrenEval.evaluate p ⟨b.owner, b.member.map (·.label.text)⟩ values depth).mapError reprStr
  unless e.body == b do throw "source evaluator selected another body"
  let v ← e.outcome.mapError reprStr
  let .bool value := v | throw "source evaluator returned a non-Boolean"
  return value

/-- This helper consumes the actual producer's output, not editable solver
formulas. The public assignment entry below re-runs that producer. Successful
confirmation is a concrete evaluation, never a universal verified verdict. -/
private def confirmProduced (p : FrenThirDesugar.Program) (out : Program) (index : Nat)
    (values : Array FrenEval.Value) (depth : Nat) : Confirmation := Id.run do
  let some entry := out.queries[index]? | return .unconfirmed "missing question"
  let q := entry.question
  if q.readiness != .ready then return .unconfirmed "unresolved question readiness"
  if q.kind != .assumptionsSatisfiable && q.kind != .validity then
    return .unconfirmed "source definedness-site confirmation unsupported"
  -- This deliberately examines every expression, rather than the walker's
  -- short-circuit trace, and does not accept raw UNSAT as proof of a premise.
  if !p.typed.bodies.all (fun b => confirmationFragment 10000 b.expression) then
    return .unconfirmed "source static obligations outside total confirmation fragment"
  for edge in q.dependencies do
    match edge with
    | .definition id =>
      if !out.oir.definitions.any (fun d => d.signature.id == id) then
        return .unconfirmed "missing definition dependency"
    | .question id =>
      let some prerequisite := out.oir.questions[id]? | return .unconfirmed "missing question dependency"
      if prerequisite.readiness != .ready ||
          ![FrenOir.Kind.functionDefinedness, .assumptionDefinedness, .goalDefinedness].contains prerequisite.kind then
        return .unconfirmed "unsupported prerequisite"
  if values.size != q.parameters.size then return .rejected "assignment arity"
  for i in [:values.size] do
    let some value := values[i]? | return .rejected "missing assignment"
    let some param := q.parameters[i]? | return .rejected "missing parameter"
    if value.type != param.source.type || !value.valid p.typed then
      return .rejected "assignment sort or enum membership"
  let evaluator : FrenEval.Program := ⟨p.input, p.typed, p.accepted⟩
  for hypothesis in q.hypotheses do
    match sourceBoolean evaluator hypothesis.source values depth with
    | .error e => return .unconfirmed ("source premise evaluation: " ++ e)
    | .ok false => return .rejected "source premise is false"
    | .ok true => pure ()
  if q.kind == .assumptionsSatisfiable then return .witness
  let some subject := q.subject | return .unconfirmed "missing source goal"
  match sourceBoolean evaluator subject values depth with
  | .error e => return .unconfirmed ("source goal evaluation: " ++ e)
  | .ok true => return .rejected "source goal is true"
  | .ok false => return .counterexample

/-- Low-level assignment control also binds to the original admitted source
and exact ordered producer question. It cannot certify a forged OIR record. -/
def confirmAssignment (p : FrenThirDesugar.Program) (index : Nat)
    (values : Array FrenEval.Value) (depth : Nat := 10000) : Confirmation :=
  match produce p with
  | .error _ => .unconfirmed "source production failed"
  | .ok out => confirmProduced p out index values depth

structure Readback where
  raw : Result
  modelRequest : Option String
  modelReceipt : Option Receipt
  assignment : Except String (Array FrenEval.Value)
  confirmation : Confirmation
  deriving Repr

/-- Retain the original source witness alongside every unfiltered raw query,
its first physical receipt and (when SAT) the second physical request/receipt. -/
structure ModelRun where
  source : FrenThirDesugar.Program
  program : Program
  results : Array Readback
  limits : Limits

/-- Eligibility is stricter than process success alone. The ordinary answer
classifier remains unchanged; its full model output is intentionally a protocol
error there. Resource, UTF-8, diagnostics and helper failures stay failures. -/
@[expose] def modelData (r : Receipt) : Bool :=
  r.exitCode == some 0 && r.stderr.isEmpty && r.reason.isEmpty &&
    (r.outcome == .error "invalid solver answer protocol")

/-- Each retrieval replays the exact producer script and same solver argv and
limits. Only strict complete typed readback enters the source interpreter. -/
def solveModels (p : FrenThirDesugar.Program) (limits : Limits := {}) :
    IO (Except InputFailure ModelRun) := do
  match ← solve p limits with
  | .error e => return .error e
  | .ok (out, raw) =>
    let mut results := #[]
    for i in [:raw.size] do
      let some r := raw[i]? | throw (IO.userError "missing raw query")
      let mut entry : Readback := ⟨r, none, none, .error "no SAT model", .unconfirmed "no SAT model"⟩
      if r.outcome == .sat then
        if let some first := r.receipt then
          match modelScript r.query with
          | .error e => entry := {entry with assignment := .error (reprStr e)}
          | .ok request =>
            let receipt ← transport first.command request limits
            let assignment := if modelData receipt then
              decodeModel out.oir r.query.question receipt.stdout limits.outputBytes
              else .error ("model transport: " ++ reprStr receipt.outcome)
            let confirmation := match assignment with
              | .error e => Confirmation.unconfirmed e
              | .ok values => confirmProduced p out i values 10000
            entry := ⟨r, some request, some receipt, assignment, confirmation⟩
      results := results.push entry
    return .ok ⟨p, out, results, limits⟩

theorem fragment_div (n : Nat) (a b : FrenAst.Expr) (token : FrenAst.Token) :
    confirmationFragment (n + 1) (.binary a token .div b) = false := rfl

theorem model_nonzero (r : Receipt) (h : r.exitCode ≠ some 0) : modelData r = false := by
  simp [modelData, h]

end FrenOirToSmt
