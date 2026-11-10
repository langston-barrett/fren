module

public import FrenOirToSmt.Confirm

public section
namespace FrenOirToSmt

inductive CheckStatus where
  | verified | witness | counterexample | inconsistent | vacuous
  | unconfirmed | blocked | unknown | unsupported | resourceExhausted
  | processFailure | invalidEvidence
  deriving Repr, BEq, DecidableEq

inductive Verdict where
  | verified | refuted | inconsistent | inconclusive | noChecks | inputFailure
  deriving Repr, BEq, DecidableEq

/-- Question metadata is retained in full; evidence keys index the physical
receipts in Report.run. Locations are UTF-8 source spans, not SMT positions. -/
structure CheckResult where
  question : FrenOir.Question
  location : Option FrenSource.Span
  status : CheckStatus
  reason : String
  answerRef : Option String
  modelRef : Option String
  deriving Repr

structure Report where
  verdict : Verdict
  reason : String
  checks : Array CheckResult
  run : Option ModelRun

private def row (q : FrenOir.Question) (status : CheckStatus) (reason : String)
    (r : Option Readback := none) : CheckResult :=
  ⟨q, (q.origin.bind (fun o => o.expression.tokens.head?.map (·.span))).orElse
      (fun _ => q.subject.bind (fun b => b.expression.tokens.head?.map (·.span))),
    status, reason, r.bind (·.raw.receipt.map (·.binding)), r.bind (·.modelReceipt.map (·.binding))⟩

def receiptHex (s : String) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList (s.toUTF8.toList.flatMap fun b => [digits[b.toNat / 16]!, digits[b.toNat % 16]!])

/-- The retained status must agree with the complete physical output. Binding
is a run/question/phase reference, not an authentication of arbitrary records. -/
@[expose] def receiptMatches (r : Receipt) (command : Array String) (request binding : String) (limits : Limits) : Bool :=
  !binding.isEmpty && r.binding == binding && r.command == command && r.request == request && r.limits == limits &&
    r.outcome == classify r.exitCode r.stdout r.stderr r.kind r.reason &&
    (r.kind != "finished" || (r.reason.isEmpty && r.stdoutHex == receiptHex r.stdout && r.stderrHex == receiptHex r.stderr))

private def nonanswer (q : FrenOir.Question) (r : Readback) : CheckResult :=
  match r.raw.outcome with
  | .unknown reason => row q .unknown reason (some r)
  | .unsupported reason => row q .unsupported reason (some r)
  | .resourceExhausted reason => row q .resourceExhausted reason (some r)
  | .error reason => row q .processFailure reason (some r)
  | _ => row q .invalidEvidence "unexpected answer" (some r)

private def classifyReadback (p : FrenWalking.Program) (out : Program)
    (command : Array String) (run : ModelRun) (i : Nat) (q : Query) (r : Readback) : CheckResult := Id.run do
  let bad := fun reason => row q.question .invalidEvidence reason (some r)
  let answerKey := s!"{run.runId}/{i}/answer"
  match q.script with
  | .error failure =>
    let expected := match failure with
      | .unsupported s => Outcome.unsupported s
      | .resourceExhausted s => .resourceExhausted s
      | .invalid s => .error s
    if r.raw.receipt.isSome || r.raw.outcome != expected || r.modelReceipt.isSome ||
        r.modelRequest.isSome || r.assignment.isOk then return bad "translation failure evidence conflicts"
    return nonanswer q.question r
  | .ok request =>
    let some receipt := r.raw.receipt | return bad "missing answer receipt"
    if !receiptMatches receipt command request answerKey run.limits || receipt.outcome != r.raw.outcome then
      return bad "answer receipt binding, request, command or protocol conflicts"
    if r.raw.outcome != .sat then
      if r.modelReceipt.isSome || r.modelRequest.isSome || r.assignment.isOk ||
          r.confirmation != .unconfirmed "no SAT model" then
        return bad "non-SAT answer has model evidence"
      if r.raw.outcome == .unsat then
        if q.question.kind == .assumptionsSatisfiable then
          return row q.question .inconsistent "assumption search is UNSAT" (some r)
        return row q.question .verified "counterexample search is UNSAT; solver/encoding trusted" (some r)
      return nonanswer q.question r
    let some model := r.modelReceipt | return row q.question .unconfirmed "SAT without model receipt" (some r)
    let .ok modelRequest := modelScript q | return row q.question .unconfirmed "model request unsupported" (some r)
    if r.modelRequest != some modelRequest ||
        !receiptMatches model command modelRequest s!"{run.runId}/{i}/model" run.limits then
      return bad "model receipt binding, request, command or protocol conflicts"
    if !modelData model then
      return row q.question .unconfirmed ("model transport: " ++ reprStr model.outcome) (some r)
    let assignment := decodeModel out.oir q.question model.stdout run.limits.outputBytes
    if !sameExcept assignment r.assignment then return bad "retained assignment differs from actual readback"
    match assignment with
    | .error reason => return row q.question .unconfirmed reason (some r)
    | .ok values =>
      let confirmation := confirmAssignment p i values run.evaluationDepth
      if confirmation != r.confirmation then return bad "retained source confirmation conflicts"
      match confirmation with
      | .witness => return row q.question .witness "source premises evaluated true" (some r)
      | .counterexample => return row q.question .counterexample "source premises true and obligation false" (some r)
      | .rejected reason | .unconfirmed reason => return row q.question .unconfirmed reason (some r)

private def candidate (s : CheckStatus) : Bool :=
  [CheckStatus.verified, .witness, .counterexample, .inconsistent].contains s

/-- Definition edges require their actual global definedness inventory, as well
as an equation. Question edges require a verified definedness prerequisite.
The bounded fixed point refuses cycles; it never assumes that ready means proved. -/
private def dependenciesReady (out : Program) (ready : Array Bool) (q : FrenOir.Question) : Bool :=
  q.dependencies.all fun edge => match edge with
  | .question id => (out.queries[id]?).any (fun entry =>
      [FrenOir.Kind.functionDefinedness, .assumptionDefinedness, .goalDefinedness].contains entry.question.kind &&
      (ready[id]?).getD false)
  | .definition id => out.oir.definitions.any (fun d => d.signature.id == id) &&
      out.queries.toList.zipIdx.all (fun (entry, i) =>
        entry.question.kind != .functionDefinedness || entry.question.owner != id || (ready[i]?).getD false)

private def discharge (out : Program) (rows : Array CheckResult) : Array CheckResult := Id.run do
  let mut ready := Array.replicate rows.size false
  for _ in [:rows.size + 1] do
    ready := rows.mapIdx fun i r => (ready[i]?).getD false ||
      (r.status == .verified && r.question.readiness == .ready && dependenciesReady out ready r.question)
  let resolved := rows.map fun r =>
    if candidate r.status && (r.question.readiness != .ready || !dependenciesReady out ready r.question) then
      {r with status := .blocked, reason := "unresolved readiness or unproved dependency"}
    else r
  return resolved.map fun r =>
    if r.status != .verified ||
        ![FrenOir.Kind.validity, .goalDefinedness].contains r.question.kind then r
    else
      match resolved.find? (fun sat => sat.question.kind == .assumptionsSatisfiable &&
          sat.question.owner == r.question.owner && sat.question.hypotheses == r.question.hypotheses) with
      | some sat =>
        if sat.status == .witness then r
        else if sat.status == .inconsistent then
          {r with status := .vacuous, reason := "owner assumptions are inconsistent"}
        else {r with status := .blocked, reason := "owner has no confirmed nonvacuity witness"}
      | none => {r with status := .blocked, reason := "missing owner nonvacuity question"}

/-- A report with only nonvacuity searches proves no obligation. All other
positive reports require every inventory row, including unused definitions. -/
@[expose] def verdict (rows : Array CheckResult) : Verdict :=
  if !rows.any (fun r => r.question.kind != .assumptionsSatisfiable) then .noChecks
  else if rows.any (fun r => r.status == .invalidEvidence) then .inconclusive
  else if rows.any (fun r => r.status == .counterexample) then .refuted
  else if rows.any (fun r => r.status == .inconsistent) then .inconsistent
  else if rows.all (fun r => r.status == .verified || r.status == .witness) then .verified
  else .inconclusive

/-- Low-level pure consumer for actual raw runs. It regenerates the COMPLETE
source inventory, checks exact source/ordered envelopes and physical bindings,
and recomputes decoding and source confirmation. Editable receipts remain an IO
trust boundary. Use check/checkSource for an end-to-end result, never to certify
caller-supplied success flags. -/
def summarize (p : FrenWalking.Program) (command : Array String) (run : ModelRun) : Report := Id.run do
  let .ok out := produce p | return ⟨.inputFailure, "source production failed", #[], some run⟩
  let invalid (reason : String) : Report :=
    ⟨.inconclusive, reason, out.queries.map (fun q => row q.question .invalidEvidence reason), some run⟩
  if p.input != run.source.input || p.typed != run.source.typed || out != run.program then
    return invalid "run belongs to another source program or inventory"
  if run.evaluationDepth > 10000 then return invalid "unbounded source evaluation depth"
  if run.runId.isEmpty || run.results.size != out.queries.size then
    return invalid "missing run identity or incomplete result inventory"
  if !(out.queries.zip run.results).all (fun (q, r) => q == r.raw.query) then
    return invalid "duplicate, reordered or foreign question envelope"
  let rows := discharge out (out.queries.mapIdx fun i q =>
    match run.results[i]? with
    | none => row q.question .invalidEvidence "missing result"
    | some r => classifyReadback p out command run i q r)
  -- A concrete source witness contradicts an UNSAT assumption search in the
  -- same owner. Such evidence is conflicting, not a successful program proof.
  let conflict := rows.any (fun r => r.status == .counterexample && rows.any (fun s =>
    s.status == .inconsistent && s.question.owner == r.question.owner))
  if conflict then return invalid "source counterexample conflicts with owner UNSAT receipt"
  return ⟨verdict rows, "conditional on trusted bounded solver, encoding and source evaluation", rows, some run⟩

/-- The real entry runs the admitted-source producer and bounded solver/model
pipeline itself. It accepts neither raw answers nor caller success predicates. -/
def check (p : FrenWalking.Program) (limits : Limits := {})
    (evaluationDepth : Nat := 10000) : IO Report := do
  try
    match ← solveModels p limits evaluationDepth with
    | .error e => return ⟨.inputFailure, reprStr e, #[], none⟩
    | .ok run => return summarize p (← solverCommand limits) run
  catch e => return ⟨.inconclusive, "checker process failure: " ++ e.toString, #[], none⟩

/-- Parse, resolve, admit, produce and execute actual source text. -/
def checkSource (file : FrenSource.FileId) (text : String) (limits : Limits := {})
    (evaluationDepth : Nat := 10000) : IO Report := do
  match FrenWalking.fromSource file text with
  | .error e => return ⟨.inputFailure, reprStr e, #[], none⟩
  | .ok p => check p limits evaluationDepth

theorem stale_receipt (r : Receipt) (command : Array String) (request binding : String)
    (limits : Limits) (h : (r.binding == binding) = false) :
    receiptMatches r command request binding limits = false := by
  simp [receiptMatches, h]

theorem empty_no_checks : verdict #[] = .noChecks := by simp [verdict]

theorem verified_all (rows : Array CheckResult) (h : verdict rows = .verified) :
    rows.all (fun r => r.status == .verified || r.status == .witness) = true := by
  unfold verdict at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  next ha => exact ha
  next => contradiction

end FrenOirToSmt
