module

public import FrenWalking.Check

/-! The walking skeleton's whole static boundary: admission, legacy typing and
both validators. See `FrenWalking.Check` for why this lives outside the pass. -/

public section
namespace FrenHirToThir
open FrenModule

/-- Actual admitted-producer/typechecker followed by both static validators.
No caller-provided typed occurrence table or Boolean can establish success.
This produces no evaluation/definedness/solver/property verdict. -/
def checkWalking (input : Resolved) : Except StaticFailure Typed := do
  let typed ← (check input).mapError StaticFailure.typing
  (validateWalking typed).mapError StaticFailure.validation
  return typed

def checkWalkingSource (file : FrenSource.FileId) (source : String) : Except StaticFailure Typed := do
  let typed ← (checkSource file source).mapError StaticFailure.typing
  (validateWalking typed).mapError StaticFailure.validation
  return typed

/-- A proof-carrying typed entrypoint can reuse the actual producer result;
it does not trust an arbitrary Typed record. -/
def checkWalkingTyped (t : Typed) (_produced : check t.resolved = .ok t) :
    Except WalkingFailure Typed := do
  validateWalking t
  return t

theorem walking_success (input : Resolved) (out : Typed) : checkWalking input = .ok out ↔
    check input = .ok out ∧ WalkingCoverage out ∧ WalkingNonrecursive out := by
  unfold checkWalking
  cases h : check input with
  | error d => simp [Except.mapError, Except.bind, Bind.bind]
  | ok t =>
    simp only [Except.mapError, Except.bind, Bind.bind]
    constructor
    · intro hs
      cases hv : validateWalking t with
      | error d => simp [hv] at hs
      | ok u =>
        cases u
        simp only [hv] at hs
        have he : t = out := Except.ok.inj hs
        subst out
        exact ⟨rfl, (validateWalking_iff t).1 hv⟩
    · rintro ⟨he, hc, hn⟩
      have ht := Except.ok.inj he
      subst out
      rw [(validateWalking_iff t).2 ⟨hc, hn⟩]
      rfl

theorem walking_retains (input : Resolved) (out : Typed) (h : checkWalking input = .ok out) :
    out.resolved = input ∧ Admitted input :=
  check_retains input out ((walking_success input out).1 h).1

theorem walking_failure_iff (input : Resolved) : (checkWalking input).isOk = false ↔
    ¬ ∃ out, check input = .ok out ∧ WalkingCoverage out ∧ WalkingNonrecursive out := by
  constructor
  · intro h ⟨out, ho⟩
    rw [(walking_success input out).2 ho] at h
    contradiction
  · intro h
    cases hr : checkWalking input with
    | error _ => rfl
    | ok out => exact (h ⟨out, (walking_success input out).1 hr⟩).elim

theorem walking_deterministic (input : Resolved) (a b : Typed)
    (ha : checkWalking input = .ok a) (hb : checkWalking input = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

/-- This is the remaining universal traversal soundness obligation. Native
cases/Plausible test actual successful and failing traversals; they do not
turn this proposition into a theorem. Admission, erasure, primitive decisions,
local lookup and determinism have separate genuine proofs. -/
def TypingSound : Prop := ∀ input out, check input = .ok out →
  ∀ body ∈ out.bodies.toList,
    HasValue input out.signatures body.context body.expression body.type

end FrenHirToThir
