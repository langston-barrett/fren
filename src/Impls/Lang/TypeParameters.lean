-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Impls.Sequences
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls


/-- Whether a type is a type parameter (`lang::param?`). -/
def isParam : Fren.Core.Ty → Bool
  | .param .. => true
  | _ => false

interp lang::param? := isParam

/-- A type parameter's position among its declaration's, and 0 for any
other type (`lang::param_index`). -/
def paramIndex : Fren.Core.Ty → Nat
  | .param k _ => k
  | _ => 0

interp lang::param_index := paramIndex
interp lang::parts := fun (t : Fren.Core.Ty) => Fren.Seq.ofList t.parts
interp lang::with_parts := fun (t : Fren.Core.Ty) (ps : Fren.Seq Fren.Core.Ty) => t.withParts ps.toList

interp lang::instantiated_type := fun (t : Fren.Core.Ty) (args : Fren.Seq Fren.Core.Ty) =>
  t.subst args.toList.toArray

interp lang::instantiated_parts := fun (ts : Fren.Seq Fren.Core.Ty) (args : Fren.Seq Fren.Core.Ty) =>
  Fren.Seq.ofList (Fren.Core.Ty.substAll args.toList.toArray ts.toList)

theorem substAll_eq_map (args : Array Fren.Core.Ty) (ts : List Fren.Core.Ty) :
    Fren.Core.Ty.substAll args ts = ts.map (Fren.Core.Ty.subst args) := by
  induction ts with
  | nil => simp [Fren.Core.Ty.substAll]
  | cons t ts ih => simp [Fren.Core.Ty.substAll, ih]

impl instantiation_parts: lang::instantiation_parts for (ts args : List Fren.Core.Ty) {
  types := Fren.Seq.ofList ts,
  arguments := Fren.Seq.ofList args,
  instantiated := Fren.Seq.ofList (Fren.Core.Ty.substAll args.toArray ts),
} by
  intro ts args _
  simpa [fren_spec, substAll_eq_map, Fren.Seq.unit] using seqMapParts (Fren.Core.Ty.subst args.toArray) ts

-- For every type and arguments, with the substitution that both front ends
-- make in an instance's payloads and fields (`Ty.subst`).
impl instantiation: lang::instantiation for (ty : Fren.Core.Ty) (args : List Fren.Core.Ty) {
  ty := ty,
  arguments := Fren.Seq.ofList args,
  result := (Fren.Core.genericTypeMorphism args.toArray).type ty,
} by
  intro ty args _
  cases ty
  case param k n _ =>
    by_cases h : k < args.length <;>
      simp [fren_spec, isParam, paramIndex, Fren.Core.genericTypeMorphism, Fren.Core.Ty.subst, h]
  all_goals
    simp [fren_spec, isParam, Fren.Core.genericTypeMorphism, Fren.Core.Ty.subst,
      Fren.Core.Ty.parts, Fren.Core.Ty.withParts, Fren.Core.Ty.substAll]

mutual
/-- Matching against a declared type that does not mention `k` gives `k`
no argument. -/
theorem matchParam_of_not_mentions (k : Nat) : (d f : Fren.Core.Ty) → d.mentions k = false →
    Fren.Core.matchParam k d f = none
  | .param j _, f, h => by simp_all [Fren.Core.Ty.mentions, Fren.Core.matchParam]
  | .set d, f, h | .seq d, f, h => by
    cases f <;> simp [Fren.Core.matchParam]
    exact matchParam_of_not_mentions k d _ (by simpa [Fren.Core.Ty.mentions] using h)
  | .rel d e, f, h => by
    simp only [Fren.Core.Ty.mentions, Bool.or_eq_false_iff] at h
    cases f <;> simp [Fren.Core.matchParam, h.1]
    exact matchParam_of_not_mentions k e _ h.2
  | .enum p ds, f, h | .record p ds, f, h => by
    cases f <;> simp [Fren.Core.matchParam]
    intro _ _
    exact matchFirst_of_not_mentions k ds _ (by simpa [Fren.Core.Ty.mentions] using h)
  | .bool, f, _ | .int, f, _ | .nat, f, _ | .string, f, _ | .abstract _, f, _ | .newtype .., f, _ => by
    cases f <;> simp [Fren.Core.matchParam]

theorem matchFirst_of_not_mentions (k : Nat) :
    (ds fs : List Fren.Core.Ty) → Fren.Core.Ty.mentionsAny k ds = false → Fren.Core.matchFirst k ds fs = none
  | [], fs, _ => by cases fs <;> simp [Fren.Core.matchFirst]
  | d :: ds, [], _ => by simp [Fren.Core.matchFirst]
  | d :: ds, f :: fs, h => by
    simp only [Fren.Core.Ty.mentionsAny, Bool.or_eq_false_iff] at h
    simp [Fren.Core.matchFirst, h.1]
    exact matchFirst_of_not_mentions k ds fs h.2
end

/-- The argument that matching the part of `fs` in its place against the
first of `ds` that mentions the type parameter `k` gives `k`, if it gives
one. -/
def matchFirstMentioning (k : Nat) (ds fs : List Fren.Core.Ty) : Option Fren.Core.Ty :=
  (ds.findIdx? (·.mentions k)).bind fun i => do Fren.Core.matchParam k (← ds[i]?) (← fs[i]?)

theorem matchFirst_eq (k : Nat) (ds fs : List Fren.Core.Ty) :
    Fren.Core.matchFirst k ds fs = matchFirstMentioning k ds fs := by
  induction ds generalizing fs with
  | nil => cases fs <;> simp [Fren.Core.matchFirst, matchFirstMentioning]
  | cons d ds ih =>
    cases fs with
    | nil => cases h : d.mentions k <;> simp [Fren.Core.matchFirst, matchFirstMentioning, List.findIdx?_cons, h]
    | cons f fs =>
      cases h : d.mentions k <;> simp [Fren.Core.matchFirst, matchFirstMentioning, List.findIdx?_cons, h, ih,
        Option.bind_map, Function.comp_def]

/-- Matching against a declared type that is not a type parameter matches
against the first of its parts that mentions `k`, if the two types have
the same shape. -/
theorem matchParam_eq (k : Nat) (d f : Fren.Core.Ty) (hd : isParam d = false) :
    Fren.Core.matchParam k d f = if d.sameShape f then matchFirstMentioning k d.parts f.parts else none := by
  cases d
  case param => simp [isParam] at hd
  case set d | seq d =>
    cases f <;> try simp [Fren.Core.matchParam, Fren.Core.Ty.sameShape, Fren.Core.Ty.parts]
    all_goals cases h : d.mentions k <;> simp [matchFirstMentioning, h, matchParam_of_not_mentions]
  case rel d e =>
    cases f <;> try simp [Fren.Core.matchParam, Fren.Core.Ty.sameShape, Fren.Core.Ty.parts]
    cases h : d.mentions k <;> cases h' : e.mentions k <;>
      simp [matchFirstMentioning, List.findIdx?_cons, h, h', matchParam_of_not_mentions]
  all_goals cases f <;>
    simp [Fren.Core.matchParam, Fren.Core.Ty.sameShape, Fren.Core.Ty.parts, matchFirst_eq, Bool.and_comm]

interp lang::same_shape? := Fren.Core.Ty.sameShape

-- For every declared type, found type and type parameter, with the matching
-- that both front ends make to infer a construction's type arguments
-- (`Core.matchParam`). With no match, the argument is not used, and the one
-- that the definition gives stands in for it.
impl parameter_matching: lang::parameter_matching for (declared found : Fren.Core.Ty) (k : Nat) {
  declared := declared,
  found := found,
  k := k,
  first := ((declared.parts.findIdx? (·.mentions k)).map Int.ofNat).getD (-1),
  part_matched? := (matchFirstMentioning k declared.parts found.parts).isSome,
  part_argument := (matchFirstMentioning k declared.parts found.parts).getD found,
  matched? := (Fren.Core.matchParam k declared found).isSome,
  argument := (Fren.Core.matchParam k declared found).getD
    (if isParam declared then found else (matchFirstMentioning k declared.parts found.parts).getD found),
} by
  intro declared found k _
  cases hd : isParam declared
  · rw [matchParam_eq k declared found hd]
    cases hs : declared.sameShape found <;> cases hm : matchFirstMentioning k declared.parts found.parts <;>
      simp_all [fren_spec]
    cases hf : declared.parts.findIdx? (·.mentions k) <;> simp_all [matchFirstMentioning]
  · cases declared <;> simp [isParam] at hd
    rename_i j _ _
    by_cases h : j = k <;> simp [fren_spec, isParam, paramIndex, Fren.Core.matchParam, h]

end Fren.Impls
