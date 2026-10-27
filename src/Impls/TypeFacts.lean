-- keep-sorted start
import Impls.Lang
-- keep-sorted end
open Fren.Lang

/-!
# Facts of types over their constituents (`Reqs/Lang/Types#finite-types`)

The components that use a fact of a type closed over its constituents
(`lang::type_facts`), proved against the one-layer functions of FrenCore
that both front ends call, for every type and every finite constituent
relation: each function, given the facts of the type's constituents, gives
the type's fact. Each front end supplies those facts by its own recursion,
which is tested (`Impls.Trace`).
-/

namespace Fren.Impls

/-- A constituent relation (`lang::type_facts`). -/
abbrev Constituents := FinSet (Fren.Core.Ty × Fren.Core.Ty)

/-! ## The closure, one layer at a time -/

section Closure

theorem transGen_iff_head {α : Type} {r : α → α → Prop} {a c : α} :
    Relation.TransGen r a c ↔ ∃ b, r a b ∧ (c = b ∨ Relation.TransGen r b c) := by
  constructor
  · intro h
    induction h with
    | single h => exact ⟨_, h, .inl rfl⟩
    | tail _ hbc ih =>
      obtain ⟨b, hab, hb⟩ := ih
      refine ⟨b, hab, .inr ?_⟩
      rcases hb with rfl | hb
      · exact .single hbc
      · exact .tail hb hbc
  · rintro ⟨b, hab, rfl | hb⟩
    · exact .single hab
    · exact Relation.TransGen.trans (.single hab) hb

variable {α : Type}

/-- A type is built from itself and from what each of its constituents is
built from (`lang::built_from`). -/
theorem mem_built_from {C : FinSet (α × α)} {t u : α} :
    u ∈ lang.built_from α t C ↔ u = t ∨ ∃ v, (t, v) ∈ C ∧ u ∈ lang.built_from α v C := by
  simp only [lang.built_from, FinSet.mem_union, FinSet.mem_image, FinSet.mem_singleton,
    FinSet.mem_closure, exists_eq_left]
  rw [transGen_iff_head]
  constructor
  · rintro (⟨v, hv, h⟩ | rfl)
    · exact .inr ⟨v, hv, h.symm⟩
    · exact .inl rfl
  · rintro (rfl | ⟨v, hv, h⟩)
    · exact .inr rfl
    · exact .inl ⟨v, hv, h.symm⟩

theorem self_mem_built_from {C : FinSet (α × α)} {t : α} : t ∈ lang.built_from α t C :=
  mem_built_from.mpr (.inl rfl)

theorem forall_built_from {C : FinSet (α × α)} {t : α} {p : α → Prop} :
    (∀ u, u ∈ lang.built_from α t C → p u) ↔
      p t ∧ ∀ v, (t, v) ∈ C → ∀ u, u ∈ lang.built_from α v C → p u := by
  constructor
  · intro h
    exact ⟨h t self_mem_built_from, fun v hv u hu => h u (mem_built_from.mpr (.inr ⟨v, hv, hu⟩))⟩
  · rintro ⟨ht, hv⟩ u hu
    rcases mem_built_from.mp hu with rfl | ⟨v, hc, hu⟩
    · exact ht
    · exact hv v hc u hu

theorem exists_built_from {C : FinSet (α × α)} {t : α} {p : α → Prop} :
    (∃ u, u ∈ lang.built_from α t C ∧ p u) ↔
      p t ∨ ∃ v, (t, v) ∈ C ∧ ∃ u, u ∈ lang.built_from α v C ∧ p u := by
  constructor
  · rintro ⟨u, hu, hp⟩
    rcases mem_built_from.mp hu with rfl | ⟨v, hc, hu⟩
    · exact .inl hp
    · exact .inr ⟨v, hc, u, hu, hp⟩
  · rintro (hp | ⟨v, hc, u, hu, hp⟩)
    · exact ⟨t, self_mem_built_from, hp⟩
    · exact ⟨u, mem_built_from.mpr (.inr ⟨v, hc, hu⟩), hp⟩

/-- A type on a cycle of the constituent relation is built from one of its
constituents. -/
theorem recursive_built_from [DecidableEq α] {C : FinSet (α × α)} {t : α} (h : (t, t) ∈ FinSet.closure C) :
    ∃ v, (t, v) ∈ C ∧ t ∈ lang.built_from α v C := by
  rw [FinSet.mem_closure, transGen_iff_head] at h
  obtain ⟨v, hv, h⟩ := h
  refine ⟨v, hv, ?_⟩
  simp only [lang.built_from, FinSet.mem_union, FinSet.mem_image, FinSet.mem_singleton,
    FinSet.mem_closure, exists_eq_left]
  exact h.symm

end Closure

/-! ## The facts (`lang::type_facts`) -/

/-- Every type that `t` is built from has a finite former and is not
recursive (`lang::type_facts`'s `finiteness`). -/
def FiniteOver (t : Fren.Core.Ty) (C : Constituents) : Prop :=
  ∀ u, u ∈ lang.built_from Fren.Core.Ty t C → (lang.former (kindOf u)).finite? = true ∧ ¬(u, u) ∈ C.closure

/-- Some type that `t` is built from has a growing former or is recursive
(`lang::type_facts`'s `bounds`). -/
def UnboundedOver (t : Fren.Core.Ty) (C : Constituents) : Prop :=
  ∃ u, u ∈ lang.built_from Fren.Core.Ty t C ∧ ((lang.former (kindOf u)).growing? = true ∨ (u, u) ∈ C.closure)

/-- A listed type (`lang::quantified_type`). -/
def ListedOver (t : Fren.Core.Ty) (C : Constituents) : Prop := FiniteOver t C ∧ ¬UnboundedOver t C

open Classical in
/-- The facts as `Bool`s, which the spec's outputs are. -/
noncomputable def finiteOf (t : Fren.Core.Ty) (C : Constituents) : Bool := decide (FiniteOver t C)

open Classical in
noncomputable def unboundedOf (t : Fren.Core.Ty) (C : Constituents) : Bool := decide (UnboundedOver t C)

open Classical in
noncomputable def constituentsListedOf (t : Fren.Core.Ty) (C : Constituents) : Bool :=
  decide (∀ v, (t, v) ∈ C → ListedOver v C)

open Classical in
noncomputable def recursiveOf (t : Fren.Core.Ty) (C : Constituents) : Bool := decide ((t, t) ∈ C.closure)

/-- One layer of `UnboundedOver`. -/
theorem unboundedOver_iff {t : Fren.Core.Ty} {C : Constituents} :
    UnboundedOver t C ↔ ((lang.former (kindOf t)).growing? = true ∨ (t, t) ∈ C.closure)
      ∨ ∃ v, (t, v) ∈ C ∧ UnboundedOver v C :=
  exists_built_from

/-- A type is listed exactly when its former is finite and not growing and
all of its constituents are listed: a recursive type is built from one of
its constituents, which is then not listed. -/
theorem listedOver_iff {t : Fren.Core.Ty} {C : Constituents} :
    ListedOver t C ↔ (lang.former (kindOf t)).finite? = true ∧ (lang.former (kindOf t)).growing? = false
      ∧ ∀ v, (t, v) ∈ C → ListedOver v C := by
  unfold ListedOver FiniteOver
  rw [forall_built_from, unboundedOver_iff]
  constructor
  · rintro ⟨⟨⟨hf, _⟩, hv⟩, hu⟩
    refine ⟨hf, ?_, fun v hc => ⟨hv v hc, fun h => hu (.inr ⟨v, hc, h⟩)⟩⟩
    cases h : (lang.former (kindOf t)).growing?
    · rfl
    · exact absurd (.inl (.inl h)) hu
  · rintro ⟨hf, hg, hv⟩
    have hr : ¬(t, t) ∈ C.closure := fun hr =>
      let ⟨v, hc, hb⟩ := recursive_built_from hr
      ((hv v hc).1 t hb).2 hr
    refine ⟨⟨⟨hf, hr⟩, fun v hc => (hv v hc).1⟩, ?_⟩
    rintro ((h | h) | ⟨v, hc, h⟩)
    · simp [hg] at h
    · exact hr h
    · exact (hv v hc).2 h

/-! ## Quantifiers (`Reqs/Lang/Quantifiers#types`) -/

/-- `Fren.Core.quantifiedTypeAccepted` is one layer of `ListedOver`, for a
type of a former without constituents that has none. -/
theorem quantifiedType_layer (t : Fren.Core.Ty) (C : Constituents)
    (hleaf : (lang.former (kindOf t)).composite? = false → ∀ v, (t, v) ∉ C) :
    Fren.Core.quantifiedTypeAccepted (toQuantifiedKind (kindOf t)) (recursiveOf t C)
      (constituentsListedOf t C) = true ↔ ListedOver t C := by
  have hr : (∀ v, (t, v) ∈ C → ListedOver v C) → ¬(t, t) ∈ C.closure := fun hv hr =>
    let ⟨v, hc, hb⟩ := recursive_built_from hr
    ((hv v hc).1 t hb).2 hr
  rw [listedOver_iff]
  cases hk : kindOf t <;>
    simp only [hk, lang.former, toQuantifiedKind, Fren.Core.quantifiedTypeAccepted, recursiveOf, constituentsListedOf, reduceCtorEq,
      ite_true, ite_false, true_and, Bool.false_eq_true, false_and, decide_eq_true_eq, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, and_iff_left_iff_imp, forall_const] at hleaf ⊢
  · exact iff_of_true trivial fun v hv => absurd hv (hleaf v)
  · exact hr

-- For every type and constituent relation: `Fren.Core.quantifiedTypeAccepted`,
-- given whether the type is recursive and whether its constituents are
-- listed, which both front ends compute from the type they quantify over
-- (`Fren.Core.countIn`), gives whether it is listed.
impl quantified_type: lang::quantified_type for (t : Fren.Core.Ty) (C : Constituents) {
  ty := t,
  constituents := C,
  listed? := Fren.Core.quantifiedTypeAccepted (toQuantifiedKind (kindOf t)) (recursiveOf t C)
    (constituentsListedOf t C),
} by
  intro t C hleaf0
  have hleaf : (lang.former (kindOf t)).composite? = false → ∀ v, (t, v) ∉ C := by
    intro hc v hv
    simp only [fren_spec] at hleaf0
    have he := FinSet.ext_iff.mp (hleaf0 (by simpa [lang.former] using hc)) v
    simp only [FinSet.mem_image, FinSet.mem_singleton, exists_eq_left, FinSet.not_mem_empty, iff_false] at he
    exact he hv
  refine ⟨t, C, recursiveOf t C, finiteOf t C, unboundedOf t C, ?_⟩
  have key := quantifiedType_layer t C hleaf
  simp only [fren_spec]
  refine ⟨?_, by simp [finiteOf, unboundedOf, recursiveOf, FiniteOver, UnboundedOver, lang.former, lang.built_from,
    FinSet.mem_closure]⟩
  rw [key]
  simp [ListedOver, finiteOf, unboundedOf]

/-! ## Variables (`Reqs/Lang/Components#members`) -/

-- For every variable, type and constituent relation: the check that both
-- front ends call, given whether the type is unbounded.
impl variable_type: lang::variable_type for (o d : Bool) (t : Fren.Core.Ty) (C : Constituents) {
  output? := o,
  ty := t,
  constituents := C,
  defined? := d,
  accepted? := Fren.Core.variableTypeAccepted o (unboundedOf t C) d,
} by
  intro o d t C _
  refine ⟨t, C, recursiveOf t C, finiteOf t C, unboundedOf t C, ?_⟩
  simp only [fren_spec]
  refine ⟨by cases o <;> cases d <;> simp [Fren.Core.variableTypeAccepted], ?_⟩
  simp [finiteOf, unboundedOf, recursiveOf, FiniteOver, UnboundedOver, lang.former, lang.built_from,
    FinSet.mem_closure]

/-! ## Newtypes (`Reqs/Lang/Items#newtypes`) -/

-- For every newtype and constituent relation whose one pair from it is its
-- underlying type: the checks that both front ends use, given whether its
-- underlying type is unbounded.
impl newtype: lang::newtype for (n : Nat) (f : Bool) (t : Fren.Core.Ty) (C : Constituents) {
  n_fields := n,
  field_accepted? := f,
  ty := t,
  constituents := C,
  accepted? := Fren.Core.newtypeAccepted n f,
  unbounded? := Fren.Core.newtypeUnbounded (unboundedOf (underOf t) C),
} by
  intro n f t C h
  refine ⟨t, C, recursiveOf t C, finiteOf t C, unboundedOf t C, ?_⟩
  simp only [fren_spec] at h
  obtain ⟨⟨_, hk⟩, hu, hr⟩ := h
  have hc : ∀ v, (t, v) ∈ C ↔ v = underOf t := fun v => by
    have := FinSet.ext_iff.mp hu v
    simp only [FinSet.mem_image, FinSet.mem_singleton, exists_eq_left] at this
    exact this
  have hb : UnboundedOver t C ↔ UnboundedOver (underOf t) C := by
    rw [unboundedOver_iff]
    simp only [hc, exists_eq_left]
    have : ¬(t, t) ∈ C.closure := by simpa [FinSet.mem_closure] using hr
    simp [hk, lang.former, this]
  simp only [fren_spec]
  refine ⟨⟨by simp [Fren.Core.newtypeAccepted]; omega, ?_⟩, ?_⟩
  · simp only [Fren.Core.newtypeUnbounded, unboundedOf, decide_eq_true_eq, hb]
  · simp [finiteOf, unboundedOf, recursiveOf, FiniteOver, UnboundedOver, lang.former, lang.built_from,
      FinSet.mem_closure]

/-! ## Operators of newtypes (`Reqs/Lang/Expressions#newtypes`) -/

/-- The pairs `(n, under(n))` of the newtypes of `t`'s chain: `t`, if it
is a newtype, and those of its underlying type (`lang::newtype_operator`). -/
def undersOf : Fren.Core.Ty → List (Fren.Core.Ty × Fren.Core.Ty)
  | .newtype p v => (.newtype p v, v) :: undersOf v
  | _ => []

/-- The base of `t`'s chain: the first type that is not a newtype. -/
def baseOf : Fren.Core.Ty → Fren.Core.Ty
  | .newtype _ v => baseOf v
  | t => t

theorem undersOf_source : ∀ {u a b : Fren.Core.Ty}, (a, b) ∈ undersOf u → ∃ p, a = .newtype p b
  | .newtype p v, a, b, h => by
    simp only [undersOf, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨p, rfl⟩
    · exact undersOf_source h
  | .bool, _, _, h | .int, _, _, h | .nat, _, _, h | .string, _, _, h | .set _, _, _, h | .rel .., _, _, h
  | .seq _, _, _, h | .enum .., _, _, h | .record .., _, _, h | .abstract _, _, _, h | .param .., _, _, h => by
    simp [undersOf] at h

/-- A type that is not a newtype is the one type built from it, over a
relation of newtypes and their underlying types. -/
theorem exists_base_leaf {R : Constituents} (hR : ∀ a b, (a, b) ∈ R → ∃ p, a = .newtype p b)
    {N : Fren.Core.Ty → Bool} (hN : ∀ t, N t = true ↔ ∃ p v, t = .newtype p v) (P : Fren.Core.Ty → Prop)
    (w : Fren.Core.Ty) (hw : ∀ p v, w ≠ .newtype p v) :
    (∃ b, (b ∈ lang.built_from Fren.Core.Ty w R ∧ ¬N b = true) ∧ P b) ↔ P w := by
  have := exists_built_from (C := R) (t := w) (p := fun b => ¬N b = true ∧ P b)
  simp only [and_assoc] at this ⊢
  rw [this]
  constructor
  · rintro (⟨_, h⟩ | ⟨v, hv, _⟩)
    · exact h
    · obtain ⟨p, e⟩ := hR _ _ hv
      exact absurd e (hw p v)
  · intro h
    refine .inl ⟨fun hn => ?_, h⟩
    obtain ⟨p, v, e⟩ := (hN w).mp hn
    exact hw p v e

/-- Over a relation of newtypes and their underlying types that holds `w`'s
chain, a type with a property is built from `w` and not a newtype, by `N`,
exactly when `w`'s base has it. -/
theorem exists_base {R : Constituents} (hR : ∀ a b, (a, b) ∈ R → ∃ p, a = .newtype p b)
    {N : Fren.Core.Ty → Bool} (hN : ∀ t, N t = true ↔ ∃ p v, t = .newtype p v) (P : Fren.Core.Ty → Prop) :
    ∀ w : Fren.Core.Ty, (∀ x ∈ undersOf w, x ∈ R) →
      ((∃ b, (b ∈ lang.built_from Fren.Core.Ty w R ∧ ¬N b = true) ∧ P b) ↔ P (baseOf w))
  | .newtype p v, hw => by
    have hv : ∀ x, (Fren.Core.Ty.newtype p v, x) ∈ R ↔ x = v := fun x =>
      ⟨fun h => by obtain ⟨_, e⟩ := hR _ _ h; cases e; rfl,
       fun e => e ▸ hw _ (by simp [undersOf, e])⟩
    have := exists_built_from (C := R) (t := .newtype p v) (p := fun b => ¬N b = true ∧ P b)
    simp only [and_assoc] at this ⊢
    rw [this]
    simp only [hv, exists_eq_left, baseOf, hN, not_exists]
    rw [← exists_base hR hN P v fun x hx => hw x (by simp [undersOf, hx])]
    simp [and_assoc, hN]
  | .bool, _ | .int, _ | .nat, _ | .string, _ | .set _, _ | .rel .., _ | .seq _, _ | .enum .., _ | .record .., _
  | .abstract _, _ | .param .., _ => exists_base_leaf hR hN P _ (by intro _ _ h; cases h)

theorem newtypeOpAccepted_add : ∀ (t : Fren.Core.Ty) (o : Bool),
    Fren.Core.newtypeOpAccepted .add t o = (baseOf t matches .int | .nat)
  | .newtype _ v, _ => by simp only [Fren.Core.newtypeOpAccepted, baseOf]; exact newtypeOpAccepted_add v false
  | .bool, _ | .int, _ | .nat, _ | .string, _ | .set _, _ | .rel .., _ | .seq _, _ | .enum .., _ | .record .., _
  | .abstract _, _ | .param .., _ => by simp [Fren.Core.newtypeOpAccepted, baseOf]

theorem newtypeOpAccepted_sub : ∀ (t : Fren.Core.Ty) (o : Bool),
    Fren.Core.newtypeOpAccepted .sub t o = (baseOf t matches .int)
  | .newtype _ v, _ => by simp only [Fren.Core.newtypeOpAccepted, baseOf]; exact newtypeOpAccepted_sub v false
  | .bool, _ | .int, _ | .nat, _ | .string, _ | .set _, _ | .rel .., _ | .seq _, _ | .enum .., _ | .record .., _
  | .abstract _, _ | .param .., _ => by simp [Fren.Core.newtypeOpAccepted, baseOf]

-- For every operator, underlying type and whether the newtype is ordered,
-- over the underlying types of its chain: the check that both front ends
-- use, which follows the chain to its base.
impl newtype_operator: lang::newtype_operator for (op : Fren.Core.NewtypeOp) (u : Fren.Core.Ty) (o : Bool) {
  op := toNewtypeOp op,
  underlying := u,
  ordered? := o,
  unders := FinSet.ofList (undersOf u),
  accepted? := Fren.Core.newtypeOpAccepted op u o,
} by
  intro op u o _
  have hR : ∀ a b, (a, b) ∈ FinSet.ofList (undersOf u) → ∃ p, a = .newtype p b :=
    fun _ _ h => undersOf_source (FinSet.mem_ofList.mp h)
  have hw : ∀ x ∈ undersOf u, x ∈ FinSet.ofList (undersOf u) := fun _ => FinSet.mem_ofList.mpr
  have hN : ∀ t, isNewtype t = true ↔ ∃ p v, t = .newtype p v := by
    intro t; cases t <;> simp [isNewtype]
  simp only [fren_spec]
  cases op <;> simp only [toNewtypeOp, Fren.Core.newtypeOpAccepted, newtypeOpAccepted_add, newtypeOpAccepted_sub,
    reduceCtorEq, ite_true, ite_false, decide_eq_true_eq]
  case add =>
    rw [exists_base hR hN (fun b => kindOf b ∈ ({lang.ValueType.IntTy, lang.ValueType.NatTy} : FinSet _)) u hw]
    cases baseOf u <;> simp [kindOf]
  case sub =>
    rw [exists_base hR hN (fun b => kindOf b = lang.ValueType.IntTy) u hw]
    cases baseOf u <;> simp [kindOf]
  all_goals rfl

/-! ## Well-founded enumerations (`Reqs/Lang/Items#enumerations`) -/

open Classical in
/-- Whether one of a variant's payloads has a type that the enumeration `t`
is built from (`lang::well_founded`). -/
noncomputable def recursiveVariant (t : Fren.Core.Ty) (C : Constituents) (payloads : List Fren.Core.Ty) : Bool :=
  decide (∃ u ∈ payloads, t ∈ lang.built_from Fren.Core.Ty u C)

-- For every enumeration `t`, constituent relation, variants `vs` and their
-- payloads' types `pay`: the count that both front ends compare, of the
-- variants that have a payload that the enumeration is built from. Both
-- front ends count a payload of the enumeration's own type: no other type
-- that a payload can have is built from the enumeration, since a type is
-- declared before it is written, and the enumeration's own type within an
-- argument of an instance is an error (`lang::recursive_payload`).
impl well_founded: lang::well_founded for (t : Fren.Core.Ty) (C : Constituents) (vs : List Lean.Name)
    (pay : Lean.Name → List Fren.Core.Ty) {
  ty := t,
  constituents := C,
  variants := FinSet.ofList vs,
  payloads := FinSet.ofList (vs.flatMap fun v => (pay v).map (v, ·)),
  accepted? := Fren.Core.wellFounded vs.length (vs.filter fun v => recursiveVariant t C (pay v)).length,
} by
  intro t C vs pay _
  have hi : ∀ v u, u ∈ @FinSet.image _ _ (fun a b => Classical.propDecidable (a = b))
      (FinSet.ofList (vs.flatMap fun v => (pay v).map (v, ·))) {v} ↔ v ∈ vs ∧ u ∈ pay v := by
    intro v u
    simp only [FinSet.mem_image, FinSet.mem_singleton, exists_eq_left, FinSet.mem_ofList, List.mem_flatMap,
      List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨w, hw, u', hu, rfl, rfl⟩
      exact ⟨hw, hu⟩
    · rintro ⟨hv, hu⟩
      exact ⟨v, hv, u, hu, rfl, rfl⟩
  simp only [fren_spec, Fren.Core.wellFounded, decide_eq_true_eq, List.length_filter_lt_length_iff_exists,
    FinSet.mem_ofList]
  constructor
  · rintro ⟨v, hv, hr⟩
    refine ⟨v, hv, fun u hu hb => hr ?_⟩
    simp only [recursiveVariant, decide_eq_true_eq]
    exact ⟨u, ((hi v u).mp hu).2, by simpa [lang.built_from] using hb⟩
  · rintro ⟨v, hv, hr⟩
    refine ⟨v, hv, ?_⟩
    simp only [recursiveVariant, decide_eq_true_eq, not_exists, not_and]
    intro u hu hb
    exact hr u ((hi v u).mpr ⟨hv, hu⟩) (by simpa [lang.built_from] using hb)

end Fren.Impls
