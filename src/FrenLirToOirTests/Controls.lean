module

public import FrenLirToOirTests.Dependencies

public section
namespace FrenLirToOirTests
open FrenOir FrenLir FrenEval

private def replacing (p : FrenOir.Program) (q : FrenOir.Question) (changed : FrenOir.Question) : FrenOir.Program :=
  {p with questions := p.questions.set! q.id changed}

/-- Every mutant is well-sorted and edits real output. The independent source
census or concrete mathematical observation must reject it; no output equality
with the producer itself is used as an oracle. -/
def runControls : IO Unit := do
  let started ← IO.monoMsNow
  let c ← load source
  let p := c.program
  let #[ordinary] := divisions p "andCheck" | throw (IO.userError "ordinary division")
  let missing := {p with questions := p.questions.filter (fun q => q.id != ordinary.id)}
  -- Renumber, so this cannot be caught merely by the ID invariant.
  let missing := {missing with questions := missing.questions.mapIdx (fun i q => {q with id := i})}
  require (graphAudit missing) "missing-check mutant retains sorts, source identity and valid IDs"
  require (!sourceAudit missing) "missing required question survived"
  let wrongOwner := {ordinary with owner := key "orCheck"}
  require (sorted p wrongOwner && !sourceAudit (replacing p ordinary wrongOwner)) "wrong owner survived"
  let #[other] := divisions p "orCheck" | throw (IO.userError "other origin")
  let wrongOrigin := {ordinary with origin := other.origin}
  require (sorted p wrongOrigin && !sourceAudit (replacing p ordinary wrongOrigin)) "wrong origin survived"
  let guarded := {ordinary with frames := [.guard (.bool false) true]}
  require (sorted p guarded && !sourceAudit (replacing p ordinary guarded)) "ordinary operand guarded"
  let #[before] := divisions p "preGuard" | throw (IO.userError "pre-guard division")
  let moved := {before with frames := [.guard (.binary .ne (.local .int 0 .value) (.int 0)) true]}
  require (sorted p moved && !sourceAudit (replacing p before moved)) "let check moved under use guard"
  let some valid := one? p "safe" .validity (some "goal") | throw (IO.userError "validity")
  let some request := p.lir.requests[valid.request.getD 0]? | throw (IO.userError "source request")
  let .validity goal := request.question
    | throw (IO.userError "validity source")
  let selfPremise := {valid with hypotheses := valid.hypotheses.push goal}
  require (sorted p selfPremise && !dependencyAudit (replacing p valid selfPremise)) "goal as premise"
  let polarity := {valid with condition := .unary .not valid.condition}
  require (sorted p polarity && !dependencyAudit (replacing p valid polarity)) "flipped polarity"
  let #[nested] := divisions p "nested" | throw (IO.userError "nested")
  let wrongSlot := {nested with condition := .binary .ne (.local .int 1 .value) (.int 0)}
  require (sorted p wrongSlot && sees nested #[.int (-1)] false && sees wrongSlot #[.int (-1)] true)
    "same-type wrong slot control"
  let noEquations := {p with definitions := #[]}
  require (!sourceAudit noEquations) "missing call/domain equations"
  for text in #[source ++ "\nfn bad(x: Int): Int := false", source ++ "\nfn bad(x: Int): Int := missing",
      source ++ "\nfn loop(x: Int): Int := loop(x)", source ++ "\nfn bad(x: Int): Int := ("] do
    require (!(FrenLirToOir.fromSource ⟨603⟩ text).isOk) "invalid source admitted"
  match FrenLirToOir.questions p.lir #[] with
  | .error (.unsupported _) => pure ()
  | _ => throw (IO.userError "missing equations were silently accepted")
  match FrenLirToOir.applications 0 (.bool true) with
  | .error (.resourceExhausted _) => pure ()
  | _ => throw (IO.userError "term traversal exhaustion became success")
  match FrenLirToOir.walk 0 .empty none [] [] [] [] with
  | .error (.resourceExhausted _) => pure ()
  | _ => throw (IO.userError "traversal exhaustion became success")
  match FrenLirToOir.walk 1 (.check (.bool false)) none [] [] [] [] with
  | .error (.invalidInput _) => pure ()
  | _ => throw (IO.userError "missing attribution became success")
  IO.println s!"OIR negative controls execution: {(← IO.monoMsNow) - started} ms; 9 semantic mutants killed (missing, owner, origin, ordinary guard, let guard, self premise, polarity, slot, equations), 4 source rejections, explicit resource/unattributed/unsupported errors"

end FrenLirToOirTests
