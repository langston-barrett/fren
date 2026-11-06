-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Quantifiers (`Reqs/Lang/Quantifiers`) -/

def toQuantifiedKind : lang.ValueType → Fren.Core.QuantifiedKind
  | .BoolTy => .bool
  | .EnumTy => .enum
  | .RecordTy => .record
  | .IntTy | .NatTy | .StringTy | .AbstractTy | .SetTy | .RelTy | .SeqTy => .other

-- For every number of instances, which both front ends count.
impl quantifier_size: lang::quantifier_size for (n : Nat) {
  n_instances := n,
  accepted? := Fren.Core.quantifierSizeAccepted n,
} by
  intro n _
  simp [fren_spec, Fren.Core.quantifierSizeAccepted, Fren.Core.maxInstances] <;> omega

def toBinderTarget : lang.BinderTarget → Fren.Core.BinderTarget
  | .TypeName => .typeName
  | .Component => .component

-- For every binder, by what its type names.
impl quantifier_binder: lang::quantifier_binder for (t : lang.BinderTarget) {
  target := t,
  accepted? := Fren.Core.quantifierBinder (toBinderTarget t),
} by
  intro t _
  cases t <;> simp [fren_spec, toBinderTarget, Fren.Core.quantifierBinder]

/-- A type wraps at least itself. -/
theorem wrapped_ne_nil (t : Fren.Core.Ty) : t.wrapped ≠ [] := by
  cases t <;> simp [Fren.Core.Ty.wrapped]

/-- The last type that `t` wraps is the one it is erased to, whose values
a comparison of `t`'s compares. -/
theorem wrapped_last : ∀ t : Fren.Core.Ty, t.wrapped[t.wrapped.length - 1]? = some t.erased
  | .newtype p u => by
    have ih := wrapped_last u
    have hlen : u.wrapped.length - 1 + 1 = u.wrapped.length := by
      cases h : u.wrapped with
      | nil => exact absurd h (wrapped_ne_nil u)
      | cons a l => simp
    simp only [Fren.Core.Ty.wrapped, Fren.Core.Ty.erased, List.length_cons, Nat.add_sub_cancel]
    rw [← hlen, List.getElem?_cons_succ]
    exact ih
  | .bool | .int | .nat | .string | .set _ | .rel _ _ | .seq _ | .enum _ _ | .record _ _ | .abstract _
  | .param _ _ => rfl

/-- The last type that `t` wraps, by position in the spec's sequence. -/
theorem wrapped_nth_last (t : Fren.Core.Ty) :
    (Fren.Seq.ofList t.wrapped).nth ((Fren.Seq.ofList t.wrapped).len - 1) = t.erased := by
  have hne := wrapped_ne_nil t
  have hpos : 0 < t.wrapped.length := by
    cases h : t.wrapped with
    | nil => exact absurd h hne
    | cons a l => simp
  have hidx : t.wrapped.length - 1 < t.wrapped.length := by omega
  have hget : t.wrapped[t.wrapped.length - 1] = t.erased :=
    Option.some.inj ((List.getElem?_eq_getElem hidx).symm.trans (wrapped_last t))
  have hlenInt : (Fren.Seq.ofList t.wrapped).len - 1 = ((t.wrapped.length - 1 : Nat) : Int) := by
    rw [Fren.Seq.len_eq, Fren.Seq.toList_ofList]; omega
  rw [hlenInt, Fren.Seq.nth_of_lt _ _ (by omega) (by simp only [Fren.Seq.toList_ofList]; omega)]
  simpa using hget

-- For every type, it and the types that the newtypes it is wrap, by the
-- predicate that both front ends ask of a comparison in a guard
-- (`Fren.Core.countedBetween`).
impl range_domain: lang::range_domain for (t : Fren.Core.Ty) {
  types := Fren.Seq.ofList t.wrapped,
  ranged? := Fren.Core.countedBetween t,
} by
  intro t _
  simp only [fren_spec, wrapped_nth_last]
  refine ⟨?_, trivial⟩
  cases h : t.erased <;> simp [Fren.Core.countedBetween, h, kindOf]

-- For every type, it and the types that the newtypes it is wrap, by the
-- predicate that both front ends' evaluators ask of a bound name with only
-- an upper bound (`Fren.Core.startsAtZero`).
impl nat_floor: lang::nat_floor for (t : Fren.Core.Ty) {
  types := Fren.Seq.ofList t.wrapped,
  nat? := Fren.Core.startsAtZero t,
} by
  intro t _
  simp only [fren_spec, wrapped_nth_last]
  refine ⟨?_, trivial⟩
  cases h : t.erased <;> simp [Fren.Core.startsAtZero, h, kindOf]

-- For every operand, of a bound name of every type, read through every
-- list of fields, as both front ends decide that it is the bound name
-- written alone (`Fren.Core.nameAlone`).
impl name_alone: lang::name_alone for (k : Option Nat) (t : Fren.Core.Ty) (fs : List String) {
  base := posOr k,
  types := Fren.Seq.ofList t.wrapped,
  fields := Fren.Seq.ofList fs,
  alone := posOr (Fren.Core.nameAlone k t fs),
} by
  intro k t fs _
  simp only [fren_spec, Fren.Core.nameAlone, Fren.Str.lit]
  have hall : (fs.all fun x => x == "0") = true ↔
      ∀ j : Int, 0 ≤ j ∧ j < (Fren.Seq.ofList fs).len → (Fren.Seq.ofList fs).nth j = "0" := by
    simp only [List.all_eq_true, beq_iff_eq, Fren.Seq.len_eq, Fren.Seq.toList_ofList]
    constructor
    · intro h j ⟨h0, h1⟩
      rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)]
      exact h _ (List.getElem_mem _)
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have := h i ⟨by omega, by omega⟩
      rwa [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using hi)] at this
  have hlen : decide (fs.length < t.wrapped.length) = true ↔
      (Fren.Seq.ofList fs).len < (Fren.Seq.ofList t.wrapped).len := by
    simp only [decide_eq_true_eq, Fren.Seq.len_eq, Fren.Seq.toList_ofList]; omega
  have hiff : (decide (fs.length < t.wrapped.length) && fs.all fun x => x == "0") = true ↔
      ((Fren.Seq.ofList fs).len < (Fren.Seq.ofList t.wrapped).len ∧
        ∀ j : Int, 0 ≤ j ∧ j < (Fren.Seq.ofList fs).len → (Fren.Seq.ofList fs).nth j = "0") := by
    rw [Bool.and_eq_true, hlen, hall]
  by_cases h : (decide (fs.length < t.wrapped.length) && fs.all fun x => x == "0") = true
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; rfl

/-- The declarations of `Option<T>`, `Pair<A, B>` and `List<T>`, which is
recursive, as both front ends give them to `Core.countIn`
(`lang::instance_values`). -/
def exampleSigs (p : Lean.Name) : Option Fren.Core.DataSig :=
  if p == `Option then some { isRecord := false, unbounded := false, ctors := #[#[], #[.param 0 `T]] }
  else if p == `Pair then some { isRecord := true, unbounded := false, ctors := #[#[.param 0 `A, .param 1 `B]] }
  else if p == `List then
    some { isRecord := false, unbounded := true, ctors := #[#[], #[.param 0 `T, .enum `List [.param 0 `T]]] }
  else none

/-- A number of values, or `-1` if a quantifier ranges over none
(`lang::instance_values`). -/
def countInt (c : Option Nat) : Int := (c.map Int.ofNat).getD (-1)

theorem countIn_param (sigs : Lean.Name → Option Fren.Core.DataSig) (n : Nat) (env : List (Option Nat))
    (k : Nat) (x : Lean.Name) : Fren.Core.countIn sigs (n + 1) env (.param k x) = env[k]?.join := by
  simp [Fren.Core.countIn]

theorem count_option (n : Nat) (a : Fren.Core.Ty) :
    Fren.Core.countIn exampleSigs (n + 2) [] (.enum `Option [a]) =
      (Fren.Core.countIn exampleSigs (n + 1) [] a).map (· + 1) := by
  rw [Fren.Core.countIn]
  cases h : Fren.Core.countIn exampleSigs (n + 1) [] a <;>
    simp [exampleSigs, h, countIn_param, Fren.Core.quantifiedTypeAccepted] <;> omega

theorem count_pair (n : Nat) (a b : Fren.Core.Ty) :
    (Fren.Core.countIn exampleSigs (n + 2) [] (.record `Pair [a, b])).isSome =
      ((Fren.Core.countIn exampleSigs (n + 1) [] a).isSome &&
        (Fren.Core.countIn exampleSigs (n + 1) [] b).isSome) := by
  rw [Fren.Core.countIn]
  cases h : Fren.Core.countIn exampleSigs (n + 1) [] a <;> cases h' : Fren.Core.countIn exampleSigs (n + 1) [] b <;>
    simp [exampleSigs, h, h', countIn_param, Fren.Core.quantifiedTypeAccepted]

theorem count_list (n : Nat) (a : Fren.Core.Ty) :
    Fren.Core.countIn exampleSigs (n + 1) [] (.enum `List [a]) = none := by
  rw [Fren.Core.countIn]
  simp [exampleSigs]

-- For every two type arguments, by the count that both front ends make of a
-- quantified type's values (`Ty.valueCount`), with the declarations of
-- `Option`, `Pair` and `List`. Each argument is counted as `Core.countIn`
-- counts it within an instance: one level less deep.
impl instance_values: lang::instance_values for (a b : Fren.Core.Ty) {
  a := countInt (Fren.Core.countIn exampleSigs (Fren.Core.valueFuel - 1) [] a),
  b := countInt (Fren.Core.countIn exampleSigs (Fren.Core.valueFuel - 1) [] b),
  option := countInt ((Fren.Core.Ty.enum `Option [a]).valueCount exampleSigs),
  pair_finite? := ((Fren.Core.Ty.record `Pair [a, b]).valueCount exampleSigs).isSome,
  list := countInt ((Fren.Core.Ty.enum `List [a]).valueCount exampleSigs),
} by
  intro a b _
  have hf : Fren.Core.valueFuel = 998 + 2 := rfl
  simp only [Fren.Core.Ty.valueCount, hf, count_option, count_pair, count_list]
  cases Fren.Core.countIn exampleSigs (998 + 1) [] a <;> cases Fren.Core.countIn exampleSigs (998 + 1) [] b <;>
    simp [fren_spec, countInt] <;> omega

end Fren.Impls
