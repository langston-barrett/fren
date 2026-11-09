module

public import FrenWalking
public import FrenEval.Value

public section
namespace FrenEval
open FrenModule FrenHirToThir

/-- Evidence is equality to the actual producer, not a validity Boolean or
an unchecked Typed record. The producer re-admits its complete resolved input. -/
structure Program where
  input : Resolved
  typed : Typed
  accepted : checkWalking input = .ok typed

def fromResolved (input : Resolved) : Except StaticFailure Program :=
  match h : checkWalking input with
  | .error d => .error d
  | .ok typed => .ok ⟨input, typed, h⟩

/-- The same parse/resolve/type/validate stages as checkWalkingSource, retaining
proof of the successful resolved producer for subsequent compiler consumers. -/
def fromSource (file : FrenSource.FileId) (source : String) : Except StaticFailure Program := do
  let doc ← (FrenParse.parseFile file source).mapError (fun e =>
    .typing ⟨none, "expected " ++ e.diagnostic.expected, e.diagnostic.span⟩)
  let resolved ← (FrenAstToHir.resolve doc).mapError StaticFailure.typing
  fromResolved resolved

def fromTyped (t : Typed) (produced : check t.resolved = .ok t) :
    Except WalkingFailure Program :=
  match h : validateWalking t with
  | .error d => .error d
  | .ok () => .ok ⟨t.resolved, t,
    (walking_success t.resolved t).2 ⟨produced, (validateWalking_iff t).1 h⟩⟩

theorem Program.retains (p : Program) : p.typed.resolved = p.input ∧ Admitted p.input :=
  walking_retains p.input p.typed p.accepted

theorem Program.static (p : Program) :
    check p.input = .ok p.typed ∧ WalkingCoverage p.typed ∧ WalkingNonrecursive p.typed :=
  (walking_success p.input p.typed).1 p.accepted

/-- Producer-bound correspondence; clients cannot substitute edited tables. -/
theorem fromResolved_success (r : Resolved) (t : Typed) :
    (∃ p, fromResolved r = .ok p ∧ p.typed = t) ↔ checkWalking r = .ok t := by
  unfold fromResolved
  split
  · rename_i d hd
    simp [hd]
  · rename_i out ho
    constructor
    · rintro ⟨p, hp, ht⟩
      cases Except.ok.inj hp
      simpa using ht ▸ ho
    · intro ht
      have he := Except.ok.inj (ho.symm.trans ht)
      exact ⟨⟨r, out, ho⟩, rfl, he⟩

end FrenEval
