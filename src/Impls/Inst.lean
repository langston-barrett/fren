-- keep-sorted start
import Impls.Check
import Reqs.Inst
-- keep-sorted end
open Fren.Lang

/-! # Instances (`Reqs/Inst`) -/

namespace Fren.Impls

open Fren.Core (Place Role bindingOk bindingsAccepted checkMention inputsOf repeatsOf repeatsOf_eq_zero)

instance : Fren.Finite Place := ⟨[.assume, .binding, .prop, .argument], by intro x; cases x <;> simp⟩
instance : Fren.Finite Role :=
  ⟨[.input, .output, .instInput, .instOutput, .instHidden], by intro x; cases x <;> simp⟩

def toPlace : Place → inst.Place
  | .assume => .Assume
  | .binding => .Binding
  | .prop => .Constraint
  | .argument => .Argument

def toRole : Role → inst.Role
  | .input => .Input
  | .output => .Output
  | .instInput => .InstInput
  | .instOutput => .InstOutput
  | .instHidden => .InstHidden

impl mention: inst::mention for (p : Place) (r : Role) (earlier : Bool) {
  place := toPlace p,
  role := toRole r,
  earlier? := earlier,
  allowed? := (checkMention p r earlier `w.x).isOk,
}

/-- The instantiated component's variables, when the bound name `x` is `t`. -/
def targetVars : inst.Target → Array (Lean.Name × Role)
  | .CompInput => #[(`x, .input)]
  | .CompOutput => #[(`x, .output)]
  | .Absent => #[]

-- One name, bound `n` times. Over `Nat`, so a proof by cases.
impl binding: inst::binding for (t : inst.Target) (n : Nat) {
  target := t,
  n := n,
  accepted? := bindingsAccepted (targetVars t) (Array.replicate n `x),
} by
  intro t n _
  cases t <;> rcases n with _ | _ | n <;> simp [fren_spec, bindingsAccepted, inputsOf, targetVars, repeatsOf_eq_zero] <;> omega

interp inst::VarName := Lean.Name

-- For every instance, with the check that both front ends use.
impl bindings: inst::bindings for (vars : Array (Lean.Name × Role)) (bound : Array Lean.Name) {
  inputs := Fren.FinSet.ofArray (inputsOf vars),
  outputs := Fren.FinSet.ofArray (vars.filterMap fun (n, r) => if r == .input then none else some n),
  bound := Fren.FinSet.ofArray bound,
  n_repeated := repeatsOf bound,
  accepted? := bindingsAccepted vars bound,
} by
  intro vars bound h
  simp only [fren_spec] at h ⊢
  have hin : ∀ n, n ∈ inputsOf vars ↔ (n, Role.input) ∈ vars := by
    intro n
    simp only [inputsOf, Array.mem_filterMap]
    constructor
    · rintro ⟨⟨a, r⟩, hm, e⟩
      by_cases hr : r = .input <;> simp [hr] at e
      exact e ▸ hr ▸ hm
    · exact fun hm => ⟨_, hm, by simp⟩
  -- No name is both an input and something else.
  have hdisj : ∀ n r, (n, Role.input) ∈ vars → (n, r) ∈ vars → r = .input := by
    intro n r hi hr
    by_cases e : r = .input
    · exact e
    have hn := FinSet.ext_iff.mp h n
    simp only [FinSet.mem_inter, FinSet.mem_ofArray, FinSet.not_mem_empty, iff_false] at hn
    exact (hn ⟨(hin n).mpr hi, Array.mem_filterMap.mpr ⟨_, hr, by simp [e]⟩⟩).elim
  -- So the first variable named `b` is an input just when `b` is one.
  have htarget : ∀ b, ((vars.find? (·.1 == b)).map (·.2) == some Role.input) = true ↔ b ∈ inputsOf vars := by
    intro b
    rw [hin]
    constructor
    · intro e
      cases hf : vars.find? (·.1 == b) with
      | none => simp [hf] at e
      | some y =>
        have hb := Array.find?_some hf
        have hm := Array.mem_of_find?_eq_some hf
        obtain ⟨y1, y2⟩ := y
        rw [hf] at e
        simp only [Option.map_some, beq_iff_eq, Option.some.injEq] at e hb
        subst e; subst hb; exact hm
    · intro hm
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((Array.find?_isSome (p := fun x => x.1 == b)).mpr ⟨(b, Role.input), hm, beq_self_eq_true b⟩)
      have hb := Array.find?_some hy
      have hmy := Array.mem_of_find?_eq_some hy
      obtain ⟨y1, y2⟩ := y
      simp only [beq_iff_eq] at hb; subst hb
      simp [hy, hdisj _ _ hm hmy]
  simp only [bindingsAccepted, Bool.and_eq_true, Array.all_eq_true', htarget, Array.contains_iff_mem,
    beq_iff_eq, FinSet.ext_iff, FinSet.mem_ofArray, repeatsOf_eq_zero]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun x => ⟨h1 x, h2 x⟩, by simp [repeatsOf_eq_zero.mpr h3]⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨fun x => (h1 x).mp, fun x => (h1 x).mpr⟩, repeatsOf_eq_zero.mp (by omega)⟩

end Fren.Impls
