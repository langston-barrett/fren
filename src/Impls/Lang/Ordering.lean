-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-- `Ty.ordered`, where the declarations declared `ordered` are those of
`os`, as `lang::ordered_in?` states it of the type's kind and name. -/
theorem ordered_iff (t : Fren.Core.Ty) (os : List Lean.Name) :
    t.ordered (fun x => decide (x ∈ os)) = true ↔
      (kindOf t = .IntTy ∨ kindOf t = .NatTy ∨ kindOf t = .StringTy) ∨
        ((kindOf t = .EnumTy ∨ kindOf t = .RecordTy) ∧ typeNameOf t ∈ os) := by
  cases t <;> simp [kindOf, typeNameOf, Fren.Core.Ty.ordered]

-- For every declared type, with its invariants, where `os` are the
-- declarations declared `ordered`, by the function that both front ends
-- ask of a declaration's fields (`Fren.Core.PTy.ordered`), which is
-- `Fren.Core.Ty.ordered`, asked of an expression's type, of its base.
impl ordered_type: lang::ordered_type for (pt : Fren.Core.PTy) (os : List Lean.Name) {
  base := pt.ty,
  restricted? := pt.pat?.isSome || !pt.invariants.isEmpty,
  ordered_items := Fren.FinSet.ofList os,
  ordered? := pt.ordered (fun x => decide (x ∈ os)),
} by
  intro pt os _
  simp [fren_spec, Fren.Core.PTy.ordered, ordered_iff, or_assoc]

def toDeclaration : Fren.Core.OrderedDecl → lang.Declaration
  | .enumeration => .Enumeration
  | .record => .Record
  | .newtype => .Newtype

theorem firstUnordered_some (od : Lean.Name → Bool) :
    ∀ (ts : List Fren.Core.PTy) (i : Nat), Fren.Core.PTy.firstUnordered? od ts = some i →
      ∃ h : i < ts.length, ts[i].ordered od = false
  | [], _, h => by simp [Fren.Core.PTy.firstUnordered?] at h
  | t :: ts, i, h => by
    by_cases ht : t.ordered od = true
    · simp only [Fren.Core.PTy.firstUnordered?, ht, if_true, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨hl, hf⟩ := firstUnordered_some od ts j hj
      exact ⟨by simp; omega, by simpa using hf⟩
    · simp only [Fren.Core.PTy.firstUnordered?, ht] at h
      simp at h
      subst h
      exact ⟨by simp, by simpa using ht⟩

theorem firstUnordered_le (od : Lean.Name → Bool) :
    ∀ (ts : List Fren.Core.PTy) (k : Nat) (hk : k < ts.length), ts[k].ordered od = false →
      ∃ i, Fren.Core.PTy.firstUnordered? od ts = some i ∧ i ≤ k
  | [], _, hk, _ => by simp at hk
  | t :: ts, k, hk, hf => by
    by_cases ht : t.ordered od = true
    · cases k with
      | zero => simp_all
      | succ k =>
        obtain ⟨i, hi, hle⟩ := firstUnordered_le od ts k (by simp at hk; omega) (by simpa using hf)
        exact ⟨i + 1, by simp [Fren.Core.PTy.firstUnordered?, ht, hi], by omega⟩
    · exact ⟨0, by simp [Fren.Core.PTy.firstUnordered?, ht], by omega⟩

-- For every declaration, whether it is ordered, how many of its variants
-- have a payload, and its fields' declared types, where `os` are the
-- declarations declared `ordered`, by the functions that both front ends
-- call to accept it and to report its field.
impl ordered_declaration: lang::ordered_declaration
    for (d : Fren.Core.OrderedDecl) (o : Bool) (n : Nat) (pts : List Fren.Core.PTy) (os : List Lean.Name) (k : Int) {
  declaration := toDeclaration d,
  ordered? := o,
  n_payloads := n,
  fields := Fren.Seq.ofList (pts.map (·.ty)),
  ordered_items := Fren.FinSet.ofList os,
  k := k,
  first_unordered := posOr (Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts),
  accepted? := Fren.Core.orderedDeclAccepted o n (Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts),
} by
  intro d o n pts os k _
  simp only [fren_spec]
  have nth (i : Nat) (h : i < pts.length) : (Fren.Seq.ofList (pts.map (·.ty))).nth (i : Int) = pts[i].ty := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  have hord (t : Fren.Core.PTy) := ordered_iff t.ty os
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hf : Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts with
    | none => simp [posOr]; omega
    | some i =>
      obtain ⟨hi, _⟩ := firstUnordered_some _ pts i hf
      simp [posOr]; omega
  · intro ⟨hki, hne⟩
    cases hf : Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts with
    | none => simp [hf, posOr] at hki; omega
    | some i =>
      obtain ⟨hi, hu⟩ := firstUnordered_some _ pts i hf
      simp only [hf, posOr] at hki
      rw [hki, nth i hi]
      have := hord pts[i]
      simp only [Fren.Core.PTy.ordered] at hu
      simp_all
  · intro ⟨⟨h0, hk⟩, hno⟩
    have hk' : k.toNat < pts.length := by simp at hk; omega
    have hkk : k = ((k.toNat : Nat) : Int) := by omega
    rw [hkk, nth k.toNat hk'] at hno
    have := hord pts[k.toNat]
    obtain ⟨i, hi, hle⟩ := firstUnordered_le (fun x => decide (x ∈ os)) pts k.toNat hk'
      (by
        simp only [Fren.Core.PTy.ordered]
        cases hc : pts[k.toNat].ty.ordered (fun x => decide (x ∈ os))
        · rfl
        · exact absurd (this.1 hc) (by simpa [and_assoc] using hno))
    simp only [hi, posOr]
    omega
  · cases hf : Fren.Core.PTy.firstUnordered? (fun x => decide (x ∈ os)) pts <;>
      cases o <;> simp [Fren.Core.orderedDeclAccepted, posOr]

/-- The kind of a plan (`lang::Plan`). -/
def planKind : Fren.Core.OrderPlan → lang.Plan
  | .number => .Number
  | .string => .Text
  | .enum .. => .Position
  | .newtype .. => .AsField
  | .record .. => .Fields

/-- A plan is only of an ordered type, and of the kind that `lang::plan_of`
gives of it. -/
theorem plan_kind (od : Lean.Name → Bool) (fieldsOf : Lean.Name → List (Lean.Name × Fren.Core.Ty)) :
    ∀ (m : Nat) (t : Fren.Core.Ty) (p : Fren.Core.OrderPlan), Fren.Core.orderPlanAt od fieldsOf m t = some p →
      planKind p = lang.plan_of (kindOf t) (isNewtype t) ∧ t.ordered od = true
  | 0, _, _, h => by simp [Fren.Core.orderPlanAt] at h
  | m + 1, t, p, h => by
    cases t <;> simp only [Fren.Core.orderPlanAt] at h <;> try simp at h
    all_goals first
      | (subst h; simp [planKind, lang.plan_of, kindOf, Fren.Core.Ty.ordered])
      | (obtain ⟨hd, rfl⟩ := h; simp [planKind, lang.plan_of, kindOf, Fren.Core.Ty.ordered, hd])
      | (obtain ⟨hd, _, _, rfl⟩ := h; simp [planKind, lang.plan_of, kindOf, isNewtype, Fren.Core.Ty.ordered, hd])

/-- A record's plan has its fields' names, in order, and each field's plan
is its type's. -/
theorem fields_plan {α β : Type} (g : β → Option Fren.Core.OrderPlan) :
    ∀ (l : List (α × β)) (r : List (α × Fren.Core.OrderPlan)),
      l.mapM (fun (f, t) => (f, ·) <$> g t) = some r →
        r.map (·.1) = l.map (·.1) ∧ ∀ (i : Nat) (h : i < l.length), ∃ h' : i < r.length, g l[i].2 = some r[i].2
  | [], r, h => by simp at h; subst h; simp
  | (f, t) :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.map_eq_some_iff, Functor.map] at h
    obtain ⟨⟨f', p⟩, ⟨p', hp, hpe⟩, rs, hrs, hr⟩ := h
    cases hpe
    cases hr
    obtain ⟨hn, hi⟩ := fields_plan g l rs hrs
    refine ⟨by simp [hn], fun i hil => ?_⟩
    cases i with
    | zero => exact ⟨by simp, by simpa using hp⟩
    | succ i =>
      obtain ⟨h', hg⟩ := hi i (by simp at hil; omega)
      exact ⟨by simp; omega, by simpa using hg⟩

/-- The record's plan, where `t` is the record `q` that `od` orders. -/
theorem record_plan (od : Lean.Name → Bool) (fieldsOf : Lean.Name → List (Lean.Name × Fren.Core.Ty)) (m : Nat)
    (q : Lean.Name) (as : List Fren.Core.Ty) (p : Fren.Core.OrderPlan)
    (h : Fren.Core.orderPlanAt od fieldsOf (m + 1) (.record q as) = some p) :
    ∃ r, p = .record q r ∧
      (fieldsOf q).mapM (fun (f, t) => (f, ·) <$> Fren.Core.orderPlanAt od fieldsOf m t) = some r := by
  simp only [Fren.Core.orderPlanAt] at h
  split at h
  · simp only [Functor.map, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨r, rfl, hr⟩
  · simp at h

-- For every type, where `os` are the declarations declared `ordered` and
-- `fieldsOf` gives each record's fields, by the function that both front
-- ends call to plan a comparison, whose plan they render, and which the
-- evaluator follows (`Fren.Core.orderPlan?`).
impl order_plan: lang::order_plan
    for (t : Fren.Core.Ty) (os : List Lean.Name) (fieldsOf : Lean.Name → List (Lean.Name × Fren.Core.Ty)) (n k : Nat) {
  t := t,
  ordered_items := Fren.FinSet.ofList os,
  fields := Fren.Seq.ofList ((fieldsOf (typeNameOf t)).map (·.1)),
  field_types := Fren.Seq.ofList ((fieldsOf (typeNameOf t)).map (·.2)),
  k := k,
  planned? := (Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t).isSome,
  plan := ((Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t).map planKind).getD .Number,
  compared := Fren.Seq.ofList (match Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t with
    | some (.record _ fs) => fs.map (·.1)
    | _ => []),
  field_plans := Fren.Seq.ofList (match Fren.Core.orderPlan? (fun x => decide (x ∈ os)) fieldsOf n t with
    | some (.record _ fs) => fs.map (planKind ·.2)
    | _ => []),
} by
  intro t os fieldsOf n k _
  simp only [fren_spec, Fren.Core.orderPlan?]
  cases hp : Fren.Core.orderPlanAt (fun x => decide (x ∈ os)) fieldsOf (n + 2) t with
  | none => simp
  | some p =>
    obtain ⟨hk, hord⟩ := plan_kind _ fieldsOf (n + 2) t p hp
    have hin := (ordered_iff t os).1 (by simpa using hord)
    simp only [Option.isSome_some, Option.map_some, Option.getD_some, true_implies, hk, true_and]
    refine ⟨?_, ?_, ?_⟩
    · cases t <;> simp_all [kindOf, typeNameOf, Fren.Core.Ty.ordered]
    · intro hf
      obtain ⟨q, as, rfl⟩ : ∃ q as, t = .record q as := by
        cases t <;> first | exact ⟨_, _, rfl⟩ | simp [lang.plan_of, kindOf, isNewtype, Fren.Core.orderPlanAt] at hf hp
      · obtain ⟨r, rfl, hr⟩ := record_plan _ fieldsOf (n + 1) q as p hp
        obtain ⟨hn, _⟩ := fields_plan _ (fieldsOf q) r hr
        have hlen : r.length = (fieldsOf q).length := by simpa using congrArg List.length hn
        exact ⟨by simp [typeNameOf, hn], by simp [typeNameOf, hlen]⟩
    · intro ⟨hf, h0, hkl⟩
      obtain ⟨q, as, rfl⟩ : ∃ q as, t = .record q as := by
        cases t <;> first | exact ⟨_, _, rfl⟩ | simp [lang.plan_of, kindOf, isNewtype, Fren.Core.orderPlanAt] at hf hp
      · obtain ⟨r, rfl, hr⟩ := record_plan _ fieldsOf (n + 1) q as p hp
        obtain ⟨_, hi⟩ := fields_plan _ (fieldsOf q) r hr
        have hkl' : k < (fieldsOf q).length := by simp [typeNameOf] at hkl; omega
        obtain ⟨h', hg⟩ := hi k hkl'
        obtain ⟨hpk, _⟩ := plan_kind _ fieldsOf (n + 1) _ _ hg
        rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa [typeNameOf] using h'),
          Fren.Seq.nth_of_lt _ _ (by omega) (by simpa [typeNameOf] using hkl')]
        simp only [typeNameOf, Fren.Seq.toList_ofList, List.getElem_map, Int.toNat_natCast]
        rw [hpk]

end Fren.Impls
