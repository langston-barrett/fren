module

public import FrenOirToSmt.Translate
public import FrenOirToSmt.Transport
public import FrenLirToOir

public section
namespace FrenOirToSmt

inductive InputFailure where
  | upstream (failure : FrenLirToOir.Failure)
  deriving Repr

private def encode (oir : FrenOir.Program) : Program :=
  let textPrelude := prelude oir
  ⟨oir, oir.questions.map (fun q => ⟨q, textPrelude >>= fun text => script oir text q⟩)⟩

/-- Input is the admitted source witness, never an editable question array and
success flag. Unsupported translation remains attached to every question. -/
def produce (p : FrenThirDesugar.Program) : Except InputFailure Program := do
  let oir ← (FrenLirToOir.produce p).mapError InputFailure.upstream
  return encode oir

def fromSource (file : FrenSource.FileId) (text : String) : Except String Program := do
  let p ← (FrenThirDesugar.fromSource file text).mapError reprStr
  (produce p).mapError reprStr

private def solveQueries (p : Program) (limits : Limits) : IO (Array Result) := do
  let command ← solverCommand limits
  p.queries.mapM fun query => do
    match query.script with
    | .error (.unsupported reason) => return ⟨query, .unsupported reason, none⟩
    | .error (.resourceExhausted reason) => return ⟨query, .resourceExhausted reason, none⟩
    | .error (.invalid reason) => return ⟨query, .error reason, none⟩
    | .ok text =>
      let receipt ← transport command text limits
      return ⟨query, receipt.outcome, some receipt⟩

/-- Raw answers retain their questions, dependencies and unresolved readiness.
There is deliberately no aggregate verified-source result or model decoding. -/
def solve (p : FrenThirDesugar.Program) (limits : Limits := {}) :
    IO (Except InputFailure (Program × Array Result)) := do
  match produce p with
  | .error e => return .error e
  | .ok out => return .ok (out, ← solveQueries out limits)

theorem deterministic (p : FrenThirDesugar.Program) (a b : Program)
    (ha : produce p = .ok a) (hb : produce p = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

theorem retains_oir (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    FrenLirToOir.produce p = .ok out.oir := by
  unfold produce at h
  cases ho : FrenLirToOir.produce p with
  | error e => simp [ho, Except.mapError, Bind.bind, Except.bind] at h
  | ok oir =>
    simp only [ho, Except.mapError, Bind.bind, Except.bind] at h
    cases Except.ok.inj h
    rfl

theorem retains_questions (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    out.queries.map Query.question = out.oir.questions := by
  unfold produce at h
  cases ho : FrenLirToOir.produce p with
  | error e => simp [ho, Except.mapError, Bind.bind, Except.bind] at h
  | ok oir =>
    simp only [ho, Except.mapError, Bind.bind, Except.bind] at h
    cases Except.ok.inj h
    simp [encode, Array.map_map, Function.comp_def]

theorem admission (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    FrenHirToThir.checkWalking p.input = .ok out.oir.lir.mir.source :=
  FrenLirToOir.admission p out.oir (retains_oir p out h)

end FrenOirToSmt
