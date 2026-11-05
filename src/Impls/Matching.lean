-- keep-sorted start
import FrenCore.Matching
import Reqs.Check
-- keep-sorted end
open Fren.Lang

/-! # Matching normalization (`Reqs/Evidence#matching-terms-and-finite-closure`) -/

namespace Fren.Impls.Matching

open Fren.Core (definitionValue)
open Fren.Core.Matching (Term normalize definitions same)

def term : Term → check.MatchingTerm
  | .atom s => .Atom s
  | .ref s => .Reference s
  | .app s args => .Application s (term args)
  | .nil => .Nil
  | .cons a b => .Cons (term a) (term b)

def defs : List (String × Term) → check.MatchingDefinitions
  | [] => .Nil
  | (n, v) :: rest => .Cons n (term v) (defs rest)

def fromTerm : check.MatchingTerm → Term
  | .Atom s => .atom s
  | .Reference s => .ref s
  | .Application s args => .app s (fromTerm args)
  | .Nil => .nil
  | .Cons a b => .cons (fromTerm a) (fromTerm b)

theorem fromTerm_term (t : Term) : fromTerm (term t) = t := by
  induction t <;> simp [term, fromTerm, *]

theorem term_injective : Function.Injective term := Function.LeftInverse.injective fromTerm_term

theorem lookup_eq (ds : List (String × Term)) (n : String) :
    term (definitionValue ds.toArray n (.ref n)) = check.definition_value (defs ds) n := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨k, v⟩ := d
    by_cases h : k = n
    · subst k
      simp [definitionValue, defs, check.definition_value, List.find?]
    · have hb : (k == n) = false := beq_eq_false_iff_ne.mpr h
      simpa [definitionValue, defs, check.definition_value, List.find?, h, hb] using ih

theorem normalize_eq (ds : List (String × Term)) (t : Term) :
    term (normalize ds t) = check.normalize_term (defs ds) (term t) := by
  induction t <;> simp [normalize, term, check.normalize_term, lookup_eq, *]

theorem definitions_eq (ds : List (String × Term)) :
    defs (definitions ds) = check.normalize_definitions (defs ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨k, v⟩ := d
    simp [definitions, defs, check.normalize_definitions, normalize_eq, ih]

-- Every term, argument list and ordered environment, with no size bound.
impl matching_normalization: check::matching_normalization for (ds : List (String × Term)) (a b : Term) {
  ds := defs ds,
  a := term a,
  b := term b,
  left := term (normalize (definitions ds) a),
  right := term (normalize (definitions ds) b),
  same? := same ds a b,
} by
  intro ds a b _
  simp [fren_spec, same, ← definitions_eq, ← normalize_eq, term_injective.eq_iff]

end Fren.Impls.Matching
