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

/-- One strict traversal step, shared by the specification evaluator and the
budgeted confirmation evaluator. The caller supplies recursive visits and calls. -/
@[expose] def strictStep [Monad m] [MonadExceptOf String m]
    (t : FrenModule.Typed) (b : FrenModule.TypedBody) (env : FrenEval.Environment)
    (visit : FrenAst.Expr → m FrenEval.Value)
    (letVisit : FrenEval.Value → FrenAst.Expr → m FrenEval.Value)
    (call : FrenModule.TypedBody → Array FrenEval.Value → m FrenEval.Value)
    (e : FrenAst.Expr) : m FrenEval.Value := do
  match e with
  | .bool .. | .integer .. | .name .. => ofExcept ((FrenEval.walk 1 t b env e).mapError reprStr)
  | .paren _ a _ => visit a
  | .unary _ op a => ofExcept ((FrenEval.unary op (← visit a)).mapError reprStr)
  | .binary a _ op c =>
    let l ← visit a
    let r ← visit c
    ofExcept ((FrenEval.binary op l r).mapError reprStr)
  | .ifE _ c _ yes _ no =>
    let .bool selected ← visit c | throw "non-Boolean condition"
    visit (if selected then yes else no)
  | .letE _ _ _ a _ rest =>
    letVisit (← visit a) rest
  | .matchE _ s _ arms _ =>
    let .enum _ ctor ← visit s | throw "non-enum scrutinee"
    let some (_, _, arm, _) := arms.find? (fun (pattern, _, _, _) =>
        (t.resolved.referenceAt pattern.head.slice).any (fun ref =>
          ref.role == .pattern && ref.target == .item ctor))
      | throw "no arm for canonical constructor"
    visit arm
  | .call callee _ args _ _ =>
    let some (.callable sig) := FrenHirToThir.occurrenceType b callee
      | throw "callee is not a callable designator"
    let some target := t.bodies.find? (fun x => x.owner == sig.id && x.member.isNone)
      | throw "missing resolved function body"
    call target (← args.mapM visit)

/-- Strict source evaluation follows every retained operand and call argument,
and only the selected conditional branch. -/
@[expose] def strictWalk : Nat → FrenModule.Typed → FrenModule.TypedBody →
    FrenEval.Environment → FrenAst.Expr → Except String FrenEval.Value
  | 0, _, _, _, _ => .error "strict source evaluation exhausted"
  | n + 1, t, b, env, e =>
    strictStep t b env (strictWalk n t b env)
      (fun v rest => strictWalk n t b (.ok v :: env) rest)
      (fun target values => do
        let slots ← (FrenEval.arguments t target values).mapError reprStr
        let v ← strictWalk n t target slots target.expression
        unless v.type == target.type && v.valid t do throw "callee result disagrees with its type"
        return v) e

/-- Strict evaluation of a retained body on positional parameter values. -/
@[expose] def strictBody (t : FrenModule.Typed) (b : FrenModule.TypedBody)
    (values : Array FrenEval.Value) (depth : Nat) : Except String FrenEval.Value := do
  let env ← (FrenEval.arguments t b values).mapError reprStr
  strictWalk depth t b env b.expression

private structure StrictState where
  budget : Nat
  cache : Array (FrenBase.ItemId × Array FrenEval.Value × Nat × FrenEval.Value) := #[]

/-- The budget counts visits across the entire question. Only successful calls
are cached, keyed by depth as well as callee and arguments, so a shallower
call cannot borrow a result that required more recursion. -/
private def boundedStrictWalk : Nat → FrenModule.Typed → FrenModule.TypedBody →
    FrenEval.Environment → FrenAst.Expr → StateT StrictState (Except String) FrenEval.Value
  | 0, _, _, _, _ => throw "strict source evaluation exhausted"
  | n + 1, t, b, env, e => do
    let state ← get
    if state.budget == 0 then throw "evaluation budget exhausted"
    set {state with budget := state.budget - 1}
    strictStep t b env (boundedStrictWalk n t b env)
      (fun v rest => boundedStrictWalk n t b (.ok v :: env) rest)
      (fun target values => do
        let state ← get
        if let some (_, _, _, v) := state.cache.find? (fun (id, args, depth, _) =>
            id == target.owner && args == values && depth == n) then return v
        let slots ← liftM ((FrenEval.arguments t target values).mapError reprStr)
        let v ← boundedStrictWalk n t target slots target.expression
        unless v.type == target.type && v.valid t do throw "callee result disagrees with its type"
        modify fun state => {state with cache := state.cache.push (target.owner, values, n, v)}
        return v) e

private def boundedStrictBody (t : FrenModule.Typed) (b : FrenModule.TypedBody)
    (values : Array FrenEval.Value) (depth : Nat) (state : StrictState) :
    Except String (FrenEval.Value × StrictState) := do
  let env ← (FrenEval.arguments t b values).mapError reprStr
  (boundedStrictWalk depth t b env b.expression).run state

/-- Syntactic test for a partial operation anywhere in an expression, in
every branch, operand and let. Exhausted traversal counts as partial. -/
@[expose] def mentionsDivision : Nat → FrenAst.Expr → Bool
  | 0, _ => true
  | n + 1, e =>
    let go := mentionsDivision n
    match e with
    | .bool .. | .integer .. | .name .. => false
    | .paren _ e _ | .unary _ _ e => go e
    | .binary a _ op b => op == .div || op == .rem || go a || go b
    | .ifE _ c _ a _ b => go c || go a || go b
    | .letE _ _ _ a _ b => go a || go b
    | .matchE _ e _ arms _ => go e || arms.any (fun (_, _, arm, _) => go arm)
    | .call f _ args _ _ => go f || args.any go

/-- Whether a body and its transitive callees are free of division and remainder.
Without them no primitive step is undefined, so a successful demand-driven
evaluation already means every static obligation holds and strict evaluation
is skipped; this bounds confirmation cost by the interpreter's. Each reachable
body is scanned once; a missing callee body or leftover worklist is partial. -/
@[expose] def divisionFree (t : FrenModule.Typed) (root : FrenModule.TypedBody) : Bool := Id.run do
  let mut work := #[root]
  let mut seen : Array FrenBase.ItemId := #[]
  for _ in [:t.bodies.size + 1] do
    let some b := work.back? | return true
    work := work.pop
    if mentionsDivision 10000 b.expression then return false
    for o in b.occurrences do
      if let .callable sig := o.type then
        unless seen.contains sig.id do
          seen := seen.push sig.id
          let some target := t.bodies.find? (fun target =>
              target.owner == sig.id && target.member.isNone) | return false
          work := work.push target
  return work.isEmpty

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
    FrenEval.Environment → FrenAst.Expr → FrenAst.Expr → Except (Option String) FrenEval.Environment
  | 0, _, _, _, _, _ => .error (some "source site traversal exhausted")
  | n + 1, t, b, env, target, e => do
    if e == target then return env
    let has := containsSite 10000 target
    let visit := siteEnvironment n t b
    let eval := fun a => (FrenEval.walk n t b env a).mapError (some ∘ reprStr)
    match e with
    | .paren _ a _ | .unary _ _ a => visit env target a
    | .binary a _ _ c => visit env target (if has a then a else c)
    | .letE _ _ _ a _ rest =>
      if has a then visit env target a
      else visit (.ok (← eval a) :: env) target rest
    | .ifE _ c _ yes _ no =>
      if has c then visit env target c
      else
        let .bool choice ← eval c | throw (some "source guard is not Boolean")
        let selected := if choice then yes else no
        unless has selected do throw none
        visit env target selected
    | .matchE _ a _ arms _ =>
      if has a then visit env target a
      else
        let .enum _ ctor ← eval a | throw (some "source match guard is not an enum")
        let some (_, _, selected, _) := arms.find? (fun (pattern, _, _, _) =>
          (t.resolved.referenceAt pattern.head.slice).any (fun ref =>
            ref.role == .pattern && ref.target == .item ctor))
          | throw (some "source match arm missing")
        unless has selected do throw none
        visit env target selected
    | .call _ _ args _ _ =>
      let some a := args.find? has | throw (some "source site not in call arguments")
      visit env target a
    | _ => throw (some "source site not found")

private def confirmDefinedness (p : FrenEval.Program) (q : FrenOir.Question)
    (values : Array FrenEval.Value) (depth : Nat) : Confirmation := Id.run do
  let some b := q.subject | return .unconfirmed "missing source body"
  let some origin := q.origin | return .unconfirmed "missing source site"
  if !p.typed.bodies.contains b || origin.owner != b.owner || origin.member != b.member then
    return .unconfirmed "source site body mismatch"
  let .binary _ _ op divisor := origin.expression
    | return .unconfirmed "source definedness site unsupported"
  if op != .div && op != .rem then return .unconfirmed "source definedness operator unsupported"
  -- The question is regenerated from admitted source. This shape restricts
  -- confirmation to the producer's divisor-nonzero leaf, never call domains.
  let .binary .ne _ (.int 0) := q.condition
    | return .unconfirmed "source definedness condition unsupported"
  let result : Except (Option String) FrenEval.Value := do
    let env ← (FrenEval.arguments p.typed b values).mapError (some ∘ reprStr)
    let env ← siteEnvironment depth p.typed b env origin.expression b.expression
    (FrenEval.walk depth p.typed b env divisor).mapError (some ∘ reprStr)
  match result with
  | .error none => return .rejected "source site is unreachable"
  | .error (some reason) => return .unconfirmed ("source definedness evaluation: " ++ reason)
  | .ok (.int 0) => return .counterexample
  | .ok (.int _) => return .rejected "source divisor is nonzero"
  | .ok _ => return .unconfirmed "source divisor is not an integer"

/-- The demand-driven interpreter supplies the value; when division is
reachable, strict evaluation must agree, so a skipped undefined operand, unused
let or callee step leaves the observation unconfirmed instead of becoming a
witness or counterexample. -/
private def sourceBoolean (p : FrenEval.Program) (b : FrenModule.TypedBody)
    (values : Array FrenEval.Value) (depth : Nat) (state : StrictState) : Except String (Bool × StrictState) := do
  let e ← (FrenEval.evaluate p ⟨b.owner, b.member.map (·.label.text)⟩ values depth).mapError reprStr
  unless e.body == b do throw "source evaluator selected another body"
  let v ← e.outcome.mapError reprStr
  let .bool value := v | throw "source evaluator returned a non-Boolean"
  if !divisionFree p.typed b then
    let (strict, remaining) ← (boundedStrictBody p.typed b values depth state).mapError ("strict: " ++ ·)
    unless strict == v do throw "strict and demand-driven evaluation disagree"
    return (value, remaining)
  return (value, state)

/-- Evaluate the retained source observations with one shared state. This is a
low-level observation routine: the caller must validate question readiness,
dependencies and the assignment before treating its result as confirmation. -/
def confirmObservations (evaluator : FrenEval.Program) (q : FrenOir.Question)
    (values : Array FrenEval.Value) (depth : Nat) : Confirmation := Id.run do
  let mut state : StrictState := ⟨10000, #[]⟩
  for hypothesis in q.hypotheses do
    match sourceBoolean evaluator hypothesis.source values depth state with
    | .error e => return .unconfirmed ("source premise evaluation: " ++ e)
    | .ok (false, _) => return .rejected "source premise is false"
    | .ok (true, remaining) => state := remaining
  if q.kind == .assumptionsSatisfiable then return .witness
  if q.kind != .validity then return confirmDefinedness evaluator q values depth
  let some subject := q.subject | return .unconfirmed "missing source goal"
  match sourceBoolean evaluator subject values depth state with
  | .error e => return .unconfirmed ("source goal evaluation: " ++ e)
  | .ok (true, _) => return .rejected "source goal is true"
  | .ok (false, _) => return .counterexample

/-- This helper consumes the actual producer's output, not editable solver
formulas. The public assignment entry below re-runs that producer. Successful
confirmation is a concrete evaluation, never a universal verified verdict. -/
private def confirmProduced (p : FrenThirDesugar.Program) (out : Program) (index : Nat)
    (values : Array FrenEval.Value) (depth : Nat) : Confirmation := Id.run do
  let some entry := out.queries[index]? | return .unconfirmed "missing question"
  let q := entry.question
  if q.readiness != .ready then return .unconfirmed "unresolved question readiness"
  -- sourceBoolean evaluates consumed hypotheses and goals, strictly too when
  -- the body or a transitive callee mentions division or remainder.
  -- Definedness confirmation evaluates a source prefix instead of its body.
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
  confirmObservations ⟨p.input, p.typed, p.accepted⟩ q values depth

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

/-- Strict evaluation never skips an operand: a failure of the right operand
is the result even when `and`/`or` demand would short-circuit on the left. -/
theorem strict_operand (n : Nat) (t : FrenModule.Typed) (b : FrenModule.TypedBody)
    (env : FrenEval.Environment) (left right : FrenAst.Expr) (token : FrenAst.Token)
    (op : FrenAst.BinaryOp) (value : FrenEval.Value) (failure : String)
    (hl : strictWalk n t b env left = .ok value) (hr : strictWalk n t b env right = .error failure) :
    strictWalk (n + 1) t b env (.binary left token op right) = .error failure := by
  simp [strictWalk, strictStep, hl, hr, Bind.bind, Except.bind]

/-- A zero divisor is undefined under strict evaluation; it has no value. -/
theorem strict_div_zero (n : Nat) (t : FrenModule.Typed) (b : FrenModule.TypedBody)
    (env : FrenEval.Environment) (left right : FrenAst.Expr) (token : FrenAst.Token)
    (value : FrenEval.Value)
    (hl : strictWalk n t b env left = .ok value) (hr : strictWalk n t b env right = .ok (.int 0)) :
    (strictWalk (n + 1) t b env (.binary left token .div right)).isOk = false := by
  cases value <;> simp [strictWalk, strictStep, hl, hr, Bind.bind, Except.bind, FrenEval.binary,
    Except.mapError, ofExcept, Except.isOk, Except.toBool] <;> rfl

/-- The same holds for remainder. -/
theorem strict_mod_zero (n : Nat) (t : FrenModule.Typed) (b : FrenModule.TypedBody)
    (env : FrenEval.Environment) (left right : FrenAst.Expr) (token : FrenAst.Token)
    (value : FrenEval.Value)
    (hl : strictWalk n t b env left = .ok value) (hr : strictWalk n t b env right = .ok (.int 0)) :
    (strictWalk (n + 1) t b env (.binary left token .rem right)).isOk = false := by
  cases value <;> simp [strictWalk, strictStep, hl, hr, Bind.bind, Except.bind, FrenEval.binary,
    Except.mapError, ofExcept, Except.isOk, Except.toBool] <;> rfl

theorem model_nonzero (r : Receipt) (h : r.exitCode ≠ some 0) : modelData r = false := by
  simp [modelData, h]

/-- A confirmed answer names a question of the re-run producer that is ready. -/
theorem confirmAssignment_ready (p : FrenThirDesugar.Program) (out : Program) (hp : produce p = .ok out)
    (index : Nat) (values : Array FrenEval.Value) (depth : Nat)
    (h : confirmAssignment p index values depth = .witness ∨
      confirmAssignment p index values depth = .counterexample) :
    ∃ entry, out.queries[index]? = some entry ∧ entry.question.readiness = .ready := by
  simp only [confirmAssignment, hp] at h
  unfold confirmProduced at h
  cases hq : out.queries[index]? with
  | none => simp [hq, Id.run] at h
  | some entry =>
    refine ⟨entry, rfl, ?_⟩
    cases hr : entry.question.readiness with
    | ready => rfl
    | unresolved reason =>
      have : (entry.question.readiness != .ready) = true := by
        rw [hr]; exact FrenOir.Readiness.unresolved_bne_ready reason
      simp [hq, this, Id.run] at h

end FrenOirToSmt
