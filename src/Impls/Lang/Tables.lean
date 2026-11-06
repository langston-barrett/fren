-- keep-sorted start
import Impls.Check
import Impls.Lang.GuardedMatch
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Tables over a scrutinee -/

-- `checkTableArms` rejects a pair, or asks about it, by `tableArmPair`.
impl table_arm_pair: lang::table_arm_pair for (o g w : Bool) {
  overlap? := o,
  guarded? := g,
  otherwise? := w,
  rejected? := (Fren.Core.tableArmPair o g w).1,
  asked? := (Fren.Core.tableArmPair o g w).2,
} by
  intro o g w _
  cases o <;> cases g <;> cases w <;> simp [fren_spec, Fren.Core.tableArmPair]

/-- What an arm of a table over a scrutinee is, from whether its pattern is
`_` and whether it has a guard (`lang::TableArm`). -/
def armKind (a : Bool × Bool) : lang.TableArm := if a.2 then .Guarded else if a.1 then .Wildcard else .Unguarded

/-- Whether the static rules reject arms `a` and `b` of `arms`, each
whether its pattern is `_` and whether it has a guard, as
`checkTableArms` decides it (`armPair`), the patterns of arms `a` and `b`
overlapping where `ovm a b`. -/
def rejectedOf (arms : List (Bool × Bool)) (ovm : Nat → Nat → Bool) (a b : Nat) : Bool :=
  (Fren.Core.armPair (arms.map (·.1)).toArray (arms.map (·.2)).toArray (decide (a < arms.length) && ovm a b) a b).1

/-- The first element of `l` that satisfies `p` is `x` exactly when `x`
satisfies it and none before the first `x` does. -/
theorem find?_eq_some_iff_takeWhile [BEq α] [LawfulBEq α] (l : List α) (p : α → Bool) (x : α) (hx : x ∈ l) :
    l.find? p = some x ↔ p x = true ∧ ((l.takeWhile (· != x)).any p) = false := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases hax : a = x
    · subst hax
      by_cases hp : p a
      · simp [hp]
      · simp only [List.find?_cons, hp, List.takeWhile_cons, bne_self_eq_false]
        simp only [Bool.false_eq_true, false_and, iff_false]
        exact fun h => hp (List.find?_some h)
    · have hx' : x ∈ l := by simpa [Ne.symm hax] using hx
      have hne : (a != x) = true := by simpa using hax
      by_cases hp : p a
      · simp [hp, hne, hax]
      · simp [hp, hne, ih hx']

theorem mem_armPairs (n i j : Nat) (hij : i < j) (hj : j < n) : (i, j) ∈ Fren.Core.armPairs n := by
  simp [Fren.Core.armPairs]
  exact ⟨j, hj, i, hij, rfl, rfl⟩

-- `checkTableArms` reports the first pair that `armPair` rejects
-- (`firstRejected?`), and asks about the pairs that it asks about.
impl table_arms: lang::table_arms for (arms : List (Bool × Bool)) (ovm : Nat → Nat → Bool) (i j : Nat) {
  arms := Fren.Seq.ofList (arms.map armKind),
  overlaps := Fren.Seq.ofList ((List.range arms.length).map fun k => if ovm k j then .Overlapping else .Apart),
  i := i,
  j := j,
  earlier_rejected? := ((Fren.Core.armPairs arms.length).takeWhile (· != (i, j))).any fun (a, b) => rejectedOf arms ovm a b,
  rejected? := rejectedOf arms ovm i j,
  asked? := (Fren.Core.armPair (arms.map (·.1)).toArray (arms.map (·.2)).toArray (decide (i < arms.length) && ovm i j) i j).2,
  reported? := Fren.Core.firstRejected? arms.length (rejectedOf arms ovm) == some (i, j),
} by
  intro arms ovm i j _
  simp only [fren_spec]
  simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map, List.length_range]
  have hrule : ∀ a b : Nat, (rejectedOf arms ovm a b = true ↔
      ((a < arms.length ∧ ovm a b = true) ∧ ¬((a < arms.length ∧ (arms.getD a (false, false)).2 = true) ∨
        (b < arms.length ∧ (arms.getD b (false, false)).2 = true)) ∧
        ¬(b + 1 = arms.length ∧ (arms.getD b (false, false)).1 = true ∧ (arms.getD b (false, false)).2 = false))) := by
    intro a b
    simp only [rejectedOf, Fren.Core.armPair, Fren.Core.tableArmPair, Fren.Core.isOtherwise]
    by_cases ha : a < arms.length <;> by_cases hb : b < arms.length <;>
      simp [ha, hb, List.getD_eq_getElem?_getD]
    by_cases h1 : arms[b].fst <;> by_cases h2 : arms[b].snd <;> by_cases h3 : arms[a].snd <;>
      by_cases h4 : ovm a b <;> by_cases h5 : b + 1 = arms.length <;> simp_all
  have hask : (Fren.Core.armPair (arms.map (·.1)).toArray (arms.map (·.2)).toArray (decide (i < arms.length) && ovm i j)
      i j).2 = true ↔
      ((i < arms.length ∧ ovm i j = true) ∧ ((i < arms.length ∧ (arms.getD i (false, false)).2 = true) ∨
        (j < arms.length ∧ (arms.getD j (false, false)).2 = true)) ∧
        ¬(j + 1 = arms.length ∧ (arms.getD j (false, false)).1 = true ∧ (arms.getD j (false, false)).2 = false)) := by
    simp only [Fren.Core.armPair, Fren.Core.tableArmPair, Fren.Core.isOtherwise]
    by_cases ha : i < arms.length <;> by_cases hb : j < arms.length <;>
      simp [ha, hb, List.getD_eq_getElem?_getD]
    all_goals by_cases h1 : arms[j].fst <;> by_cases h2 : arms[j].snd <;> by_cases h4 : ovm i j <;>
      by_cases h5 : j + 1 = arms.length <;> simp_all
  have hfirst : (Fren.Core.firstRejected? arms.length (rejectedOf arms ovm) == some (i, j)) = true ↔
      (i < j ∧ j < arms.length ∧ rejectedOf arms ovm i j = true ∧
        ((Fren.Core.armPairs arms.length).takeWhile (· != (i, j))).any (fun (a, b) => rejectedOf arms ovm a b) = false) := by
    simp only [beq_iff_eq, Fren.Core.firstRejected?]
    by_cases hp : i < j ∧ j < arms.length
    · rw [find?_eq_some_iff_takeWhile _ _ _ (mem_armPairs _ _ _ hp.1 hp.2)]
      simp [hp]
    · constructor
      · intro h
        have hm := List.mem_of_find?_eq_some h
        simp [Fren.Core.armPairs] at hm
        omega
      · intro h; exact absurd ⟨h.1, h.2.1⟩ hp
  have kG (a : Bool × Bool) : armKind a = .Guarded ↔ a.2 = true := by
    rcases a with ⟨_ | _, _ | _⟩ <;> simp [armKind]
  have kW (a : Bool × Bool) : armKind a = .Wildcard ↔ (a.1 = true ∧ a.2 = false) := by
    rcases a with ⟨_ | _, _ | _⟩ <;> simp [armKind]
  have oO (b : Bool) : ((if b then lang.Overlap.Overlapping else lang.Overlap.Apart) = .Overlapping) ↔ b = true := by
    cases b <;> simp
  have hje : ((j : Int) = (arms.length : Int) - 1) ↔ j + 1 = arms.length := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hrule]
    by_cases hi : i < arms.length <;> by_cases hj : j < arms.length <;>
      simp [hi, hj, kG, kW, oO, hje, List.getD_eq_getElem?_getD]
    all_goals first | (intros; omega) | (simp only [and_assoc]; done) | (constructor <;> intro h <;> simp_all)
  · rw [hask]
    by_cases hi : i < arms.length <;> by_cases hj : j < arms.length <;>
      simp [hi, hj, kG, kW, oO, hje, List.getD_eq_getElem?_getD]
    all_goals first | (intros; omega) | (simp only [and_assoc]; done) | (constructor <;> intro h <;> simp_all)
  · rw [hfirst]
    constructor
    · rintro ⟨hij, hjn, hr, he⟩
      refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, hr⟩, ?_⟩
      simpa using he
    · rintro ⟨⟨⟨⟨_, hij⟩, hjn⟩, hr⟩, he⟩
      exact ⟨by omega, by omega, hr, by simpa using he⟩

/-- `checkTableArms` reports a table at the first pair of its arms that
`armPair` rejects, by `firstRejected?`, as `table_arms`'s `reported?` is
bound: with `F0391`, at the later arm, naming the earlier one, where no
arm stands for too many cases. -/
theorem checkTableArms_reports (sigs : Fren.Core.Sigs) (ty : Fren.Core.PatTy) (arms : Array Fren.Core.Pat)
    (guarded : Array Bool) (i j : Nat) (hc : arms.findIdx? (·.cases > Fren.Core.maxCases) = none)
    (hr : Fren.Core.firstRejected? arms.size (fun i j => (Fren.Core.tableArmVerdict sigs ty arms guarded i j).1) =
      some (i, j)) :
    Fren.Core.checkTableArms sigs ty arms guarded =
      .error (some (j, none), Fren.Core.armsOverlapMsg i (arms[i]!.overlapWit? sigs ty arms[j]!).get!) := by
  unfold Fren.Core.checkTableArms
  simp only [hc, hr]
  rfl

/-- The arms of a table over a scrutinee as the evaluator tries them, the
`_` arm last, whose pattern matches and which has no guard. -/
def evalArms (arms : List (Bool × Bool × Int)) (otherwise : Option Int) : List (Bool × Bool × Int) :=
  arms ++ otherwise.toList.map fun v => (true, true, v)

/-- The value that the evaluator gives a table over a scrutinee: that of
its first arm taken (`Fren.Core.firstCase`), as of the `match` it means. -/
def evalTable (arms : List (Bool × Bool × Int)) (otherwise : Option Int) : Int :=
  ((Fren.Core.firstCase (evalArms arms otherwise) fun a => some (if a.1 && a.2.1 then some a.2.2 else none)).join).getD 0

theorem evalTable_first (arms : List (Bool × Bool × Int)) (otherwise : Option Int) (i : Nat)
    (hi : arms.findIdx? (fun a => a.1 && a.2.1) = some i) :
    evalTable arms otherwise = (arms[i]?.map (·.2.2)).getD 0 := by
  obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  have hf : (evalArms arms otherwise).find? (fun a => a.1 && a.2.1) = some arms[i] := by
    rw [evalArms, List.find?_append, find?_eq_findIdx?, hi]
    simp [List.getElem?_eq_getElem hlt]
  simp only [evalTable, firstCase_find, hf, List.getElem?_eq_getElem hlt]
  simp

theorem evalTable_none (arms : List (Bool × Bool × Int)) (v : Int)
    (hi : arms.findIdx? (fun a => a.1 && a.2.1) = none) : evalTable arms (some v) = v := by
  have hn : arms.find? (fun a => a.1 && a.2.1) = none := by
    rw [find?_eq_findIdx?, hi]; rfl
  rw [evalTable, firstCase_find, evalArms, List.find?_append, hn]
  simp

theorem evalTable_held (arms : List (Bool × Bool × Int)) (otherwise : Option Int) (h0 : firstTakenIdx arms ≥ 0) :
    evalTable arms otherwise = (Fren.Seq.ofList (arms.map (·.2.2))).nth (firstTakenIdx arms) := by
  cases hi : arms.findIdx? (fun a => a.1 && a.2.1) with
  | none => simp [firstTakenIdx, hi] at h0
  | some i =>
    obtain ⟨hlt, _, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
    rw [evalTable_first arms otherwise i hi, firstTakenIdx, hi,
      Fren.Seq.nth_of_lt _ _ (by simp) (by simpa using hlt)]
    simp [List.getElem?_eq_getElem hlt]

theorem evalTable_otherwise (arms : List (Bool × Bool × Int)) (otherwise : Option Int)
    (h1 : firstTakenIdx arms = -1) (h2 : Fren.Seq.ofList otherwise.toList ≠ ∅) :
    evalTable arms otherwise = (Fren.Seq.ofList otherwise.toList).nth 0 := by
  cases otherwise with
  | none => exact absurd rfl h2
  | some v =>
    have hi : arms.findIdx? (fun a => a.1 && a.2.1) = none := by
      cases h : arms.findIdx? (fun a => a.1 && a.2.1) with
      | none => rfl
      | some i => simp [firstTakenIdx, h] at h1
    rw [evalTable_none arms v hi, Fren.Seq.nth_of_lt _ _ (by simp) (by simp)]
    rfl

impl table_eval: lang::table_eval for (arms : List (Bool × Bool × Int)) (otherwise : Option Int) {
  arms := Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)),
  values := Fren.Seq.ofList (arms.map (·.2.2)),
  otherwise := Fren.Seq.ofList otherwise.toList,
  first := firstTakenIdx arms,
  value := evalTable arms otherwise,
} by
  intro arms otherwise _
  simp only [fren_spec]
  exact ⟨firstTakenIdx_indexOf arms, evalTable_held arms otherwise, fun ⟨h1, h2⟩ => evalTable_otherwise arms otherwise h1 h2⟩

-- The meaning of a table over a scrutinee, as the evaluator gives it: the
-- value of its first arm taken, which is the one where they are disjoint.
impl table_match: lang::table_match for (arms : List (Bool × Bool × Int)) (otherwise : Option Int) (k : Int) {
  arms := Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)),
  values := Fren.Seq.ofList (arms.map (·.2.2)),
  otherwise := Fren.Seq.ofList otherwise.toList,
  k := k,
  one := firstTakenIdx arms,
  disjoint? := decide (Fren.Seq.indexOf (Fren.Seq.ofList (arms.map fun a => toArmAt (a.1, a.2.1)))
    (Fren.Seq.unit lang.ArmAt.Taken) (firstTakenIdx arms + 1) = -1),
  value := evalTable arms otherwise,
} by
  intro arms otherwise k _
  simp only [fren_spec]
  rw [← firstTakenIdx_indexOf arms]
  exact ⟨⟨rfl, rfl⟩, fun ⟨_, h0⟩ => evalTable_held arms otherwise h0,
    fun ⟨h1, h2⟩ => evalTable_otherwise arms otherwise h1 h2⟩

end Fren.Impls
