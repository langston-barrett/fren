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
branches prevent value confirmation. The caller scopes this test to the
consumed bodies and their transitive callees. -/
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

/-- Totality is scoped to the source expressions actually used by confirmation,
including their transitive callees, rather than every body in the file. -/
private def totalBody : Nat → FrenModule.Typed → FrenModule.TypedBody → Bool
  | 0, _, _ => false
  | n + 1, t, b => confirmationFragment 10000 b.expression && b.occurrences.all (fun o =>
      match o.type with
      | .callable sig => (t.bodies.find? (fun target =>
          target.owner == sig.id && target.member.isNone)).any (totalBody n t)
      | _ => true)

private def containsSite : Nat → FrenAst.Expr → FrenAst.Expr → Bool
  | 0, _, _ => false
  | n + 1, target, e => e == target || (match e with
    | .paren _ a _ | .unary _ _ a => containsSite n target a
    | .binary a _ _ b | .letE _ _ _ a _ b => containsSite n target a || containsSite n target b
    | .ifE _ c _ a _ b => [c, a, b].any (containsSite n target)
    | .matchE _ a _ arms _ => containsSite n target a || arms.any (fun (_, _, b, _) => containsSite n target b)
    | .call _ _ args _ _ => args.any (containsSite n target)
    | _ => false)

/-- Locate the exact retained source occurrence under its lexical bindings and
conditional guards. Boolean operands and unused lets retain static obligations;
only if/match select branches. Never evaluate the target operation itself. -/
private def siteEnvironment : Nat → FrenModule.Typed → FrenModule.TypedBody →
    FrenEval.Environment → FrenAst.Expr → FrenAst.Expr → Except String FrenEval.Environment
  | 0, _, _, _, _, _ => .error "source site traversal exhausted"
  | n + 1, t, b, env, target, e => do
    if e == target then return env
    let has := containsSite 10000 target
    let visit := siteEnvironment n t b
    let eval := fun a => (FrenEval.walk n t b env a).mapError reprStr
    match e with
    | .paren _ a _ | .unary _ _ a => visit env target a
    | .binary a _ _ c => visit env target (if has a then a else c)
    | .letE _ _ _ a _ rest =>
      if has a then visit env target a
      else visit (.ok (← eval a) :: env) target rest
    | .ifE _ c _ yes _ no =>
      if has c then visit env target c
      else
        let .bool choice ← eval c | throw "source guard is not Boolean"
        let selected := if choice then yes else no
        unless has selected do throw "source site is unreachable"
        visit env target selected
    | .matchE _ a _ arms _ =>
      if has a then visit env target a
      else
        let .enum _ ctor ← eval a | throw "source match guard is not an enum"
        let some (_, _, selected, _) := arms.find? (fun (pattern, _, _, _) =>
          (t.resolved.referenceAt pattern.head.slice).any (·.target == .item ctor))
          | throw "source match arm missing"
        unless has selected do throw "source site is unreachable"
        visit env target selected
    | .call _ _ args _ _ =>
      let some a := args.find? has | throw "source site not in call arguments"
      visit env target a
    | _ => throw "source site not found"

private def confirmDefinedness (p : FrenEval.Program) (q : FrenOir.Question)
    (values : Array FrenEval.Value) (depth : Nat) : Confirmation := Id.run do
  let some b := q.subject | return .unconfirmed "missing source body"
  let some origin := q.origin | return .unconfirmed "missing source site"
  if !p.typed.bodies.contains b || origin.owner != b.owner || origin.member != b.member then
    return .unconfirmed "source site body mismatch"
  let .binary _ _ op divisor := origin.expression
    | return .unconfirmed "source definedness site unsupported"
  if op != .div && op != .mod then return .unconfirmed "source definedness operator unsupported"
  -- The question is regenerated from admitted source. This shape restricts
  -- confirmation to the producer's divisor-nonzero leaf, never call domains.
  let .binary .ne _ (.int 0) := q.condition
    | return .unconfirmed "source definedness condition unsupported"
  let result : Except String FrenEval.Value := do
    let env ← (FrenEval.arguments p.typed b values).mapError reprStr
    let env ← siteEnvironment depth p.typed b env origin.expression b.expression
    (FrenEval.walk depth p.typed b env divisor).mapError reprStr
  match result with
  | .error reason => return .unconfirmed ("source definedness evaluation: " ++ reason)
  | .ok (.int 0) => return .counterexample
  | .ok (.int _) => return .rejected "source divisor is nonzero"
  | .ok _ => return .unconfirmed "source divisor is not an integer"

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
  -- Only expressions consumed below need the conservative total fragment.
  -- Definedness confirmation evaluates a source prefix instead of its body.
  if !q.hypotheses.all (fun h => totalBody 10000 p.typed h.source) ||
      (q.kind == .validity && !q.subject.any (totalBody 10000 p.typed)) then
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
  if q.kind != .validity then return confirmDefinedness evaluator q values depth
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
  runId : String := ""
  evaluationDepth : Nat := 10000

/-- Eligibility is stricter than process success alone. The ordinary answer
classifier remains unchanged; its full model output is intentionally a protocol
error there. Resource, UTF-8, diagnostics and helper failures stay failures. -/
@[expose] def modelData (r : Receipt) : Bool :=
  r.exitCode == some 0 && r.stderr.isEmpty && r.reason.isEmpty &&
    (r.outcome == .error "invalid solver answer protocol")

/-- Each retrieval replays the exact producer script and same solver argv and
limits. Only strict complete typed readback enters the source interpreter. -/
def solveModels (p : FrenThirDesugar.Program) (limits : Limits := {})
    (evaluationDepth : Nat := 10000) :
    IO (Except InputFailure ModelRun) := do
  let evaluationDepth := min evaluationDepth 10000
  let runId ← freshRunId
  match ← solveTagged p limits runId with
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
            let receipt ← transport first.command request limits s!"{runId}/{i}/model"
            let assignment := if modelData receipt then
              decodeModel out.oir r.query.question receipt.stdout limits.outputBytes
              else .error ("model transport: " ++ reprStr receipt.outcome)
            let confirmation := match assignment with
              | .error e => Confirmation.unconfirmed e
              | .ok values => confirmProduced p out i values evaluationDepth
            entry := ⟨r, some request, some receipt, assignment, confirmation⟩
      results := results.push entry
    return .ok ⟨p, out, results, limits, runId, evaluationDepth⟩

theorem fragment_div (n : Nat) (a b : FrenAst.Expr) (token : FrenAst.Token) :
    confirmationFragment (n + 1) (.binary a token .div b) = false := rfl

theorem model_nonzero (r : Receipt) (h : r.exitCode ≠ some 0) : modelData r = false := by
  simp [modelData, h]

end FrenOirToSmt
