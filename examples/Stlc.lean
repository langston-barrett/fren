-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# The simply typed lambda calculus in Lean

The theorems of `stlc.fren` that need induction, proved over its generated
definitions and bound to its procedures with `impl`, in the order of its
sections:

- **Substitution**: the fresh name of a renamed binder is free in nothing
  that matters (`fresh_not_mem`, `new_binder_not_mem_apply`), and the laws
  of `subst` (`substitution_laws`).
- **Typing**: inversion, and the book's inductively defined typing relation,
  which `typeof` decides (`typeof_iff`), so that a term has at most one type
  (`Typing.unique`).
- **Evaluation**: inversion of `step`, the book's reduction relation, which
  `step` decides (`step_iff`), so that it is deterministic
  (`Step.deterministic`), and the laws of the evaluators (`evaluators`).
- **Metatheory**: the context lemmas and the substitution lemma
  (`context_lemmas`); canonical forms, `preservation`, `progress`, `safety`
  and big-step preservation (`type_safety`); and normalization, by Tait's
  method as in chapter 12 of TAPL, proved here alone, since `stlc.fren` has
  no check that states it (`normalization`).
- **Nameless terms**: the round trip (`nameless_round_trip`), and
  alpha-equivalence: substitution commutes with the nameless form, renaming
  a binder, and typing (`alpha_laws`).
- **One layer of a term**: `size` is the fold of `size_alg` (`layer_laws`).

Tested only, not proved: the round trip of the concrete syntax
(`print_parse`).
-/

open Fren.Lang

#fren_md "stlc.fren"

-- The solver's and the enumerated checks, as `fren check` runs them; the
-- laws set to random testing are left to `fren check`.
#fren_check

namespace Stlc
open Fren.Generated stlc

abbrev Named := Term String String

/-! ## Substitution

The fresh name of a renamed binder is free in nothing that matters, and the
laws of `subst`. -/

theorem mem_free_var {x y : String} : x ∈ free (Term.Var y : Named) ↔ x = y := by simp [free]

theorem mem_free_lam {x y : String} {ty : Ty} {b : Named} :
    x ∈ free (Term.Lam y ty b) ↔ x ∈ free b ∧ x ≠ y := by simp [free]

theorem mem_free_app {x : String} {a b : Named} : x ∈ free (Term.App a b) ↔ x ∈ free a ∨ x ∈ free b := by simp [free]

theorem mem_free_if {x : String} {c a b : Named} :
    x ∈ free (Term.If c a b) ↔ x ∈ free c ∨ x ∈ free a ∨ x ∈ free b := by simp [free, or_assoc]

/-- A name free in a term is no longer than all its names joined. -/
theorem length_le_all_names : ∀ (t : Named) (x : String), x ∈ free t → x.length ≤ (all_names t).length := by
  intro t
  induction t with
  | Var y => intro x h; rw [mem_free_var] at h; subst h; simp [all_names]
  | Lam y ty b ih =>
    intro x h; rw [mem_free_lam] at h
    have := ih x h.1
    simp only [all_names, String.length_append]; omega
  | App a b iha ihb =>
    intro x h; rw [mem_free_app] at h
    simp only [all_names, String.length_append]
    rcases h with h | h
    · have := iha x h; omega
    · have := ihb x h; omega
  | True => intro x h; simp [free] at h
  | False => intro x h; simp [free] at h
  | If c a b ihc iha ihb =>
    intro x h; rw [mem_free_if] at h
    simp only [all_names, String.length_append]
    rcases h with h | h | h
    · have := ihc x h; omega
    · have := iha x h; omega
    · have := ihb x h; omega

/-- `s` is a term that `sub` may substitute: a value of one of its entries. -/
def InRange : Subst → Named → Prop
  | .Id, _ => False
  | .Bind _ s rest, u => u = s ∨ InRange rest u

theorem apply_subst_cases : ∀ (sub : Subst) (x : String),
    apply_subst sub x = .Var x ∨ InRange sub (apply_subst sub x) := by
  intro sub x
  induction sub with
  | Id => left; simp [apply_subst]
  | Bind y s rest ih =>
    by_cases h : y = x
    · right; simp [apply_subst, h, InRange]
    · simp only [apply_subst, h, if_false]
      rcases ih with ih | ih
      · exact Or.inl ih
      · exact Or.inr (Or.inr ih)

theorem length_fresh_pos : ∀ (sub : Subst) (body : Named), 1 ≤ (fresh sub body).length
  | .Id, body => by
    have e : (Fren.Str.lit "'").length = 1 := rfl
    simp only [fresh, String.length_append]; omega
  | .Bind _ _ rest, body => by
    have := length_fresh_pos rest body
    simp only [fresh, String.length_append]; omega

/-- The fresh name is longer than every name free in the body or in a term
that `sub` substitutes. -/
theorem length_lt_fresh : ∀ (sub : Subst) (body : Named) (x : String),
    (x ∈ free body ∨ ∃ s, InRange sub s ∧ x ∈ free s) → x.length < (fresh sub body).length := by
  intro sub
  induction sub with
  | Id =>
    intro body x h
    rcases h with h | ⟨s, hs, _⟩
    · have := length_le_all_names body x h
      have e : (Fren.Str.lit "'").length = 1 := rfl
      simp only [fresh, String.length_append]; omega
    · exact absurd hs id
  | Bind y u rest ih =>
    intro body x h
    simp only [fresh, String.length_append]
    rcases h with h | ⟨s, hs, hx⟩
    · have := ih body x (Or.inl h); omega
    · rcases hs with rfl | hs
      · have := length_le_all_names s x hx
        have := length_fresh_pos rest body
        omega
      · have := ih body x (Or.inr ⟨s, hs, hx⟩); omega

/-- The fresh name is free neither in the body nor in what `sub` substitutes. -/
theorem fresh_not_mem (sub : Subst) (body : Named) :
    fresh sub body ∉ free body ∧ ∀ s, InRange sub s → fresh sub body ∉ free s := by
  constructor
  · intro h; have := length_lt_fresh sub body _ (Or.inl h); omega
  · intro s hs h; have := length_lt_fresh sub body _ (Or.inr ⟨s, hs, h⟩); omega

theorem fresh_ne_of_mem {sub : Subst} {body : Named} {x : String} (h : x ∈ free body) : fresh sub body ≠ x := by
  intro e; exact (fresh_not_mem sub body).1 (e ▸ h)

theorem fresh_not_mem_apply (sub : Subst) (body : Named) (x : String) (hx : x ∈ free body) :
    fresh sub body ∉ free (apply_subst sub x) := by
  rcases apply_subst_cases sub x with h | h
  · rw [h, mem_free_var]; exact fresh_ne_of_mem hx
  · exact (fresh_not_mem sub body).2 _ h

/-- Where no binder is captured, the binder is free in nothing substituted
for a free variable of the body. -/
theorem not_captures_apply : ∀ (sub : Subst) (y x : String) (fv : Fren.FinSet String),
    captures? sub y fv = false → x ∈ fv → x ≠ y → y ∉ free (apply_subst sub x) := by
  intro sub
  induction sub with
  | Id => intro y x fv _ _ hxy; rw [apply_subst, mem_free_var]; exact Ne.symm hxy
  | Bind z s rest ih =>
    intro y x fv hc hx hxy
    simp only [captures?, decide_eq_false_iff_not, not_or, Bool.not_eq_true] at hc
    by_cases hz : z = x
    · subst hz
      simp only [apply_subst, if_true]
      intro hy; exact hc.1 ⟨⟨hxy, hx⟩, hy⟩
    · simp only [apply_subst, hz, if_false]
      exact ih y x _ hc.2 (by simp [hx, Ne.symm hz]) hxy

/-- The new binder of a `Lam` is free in nothing substituted for another
free variable of the body: by construction where it is fresh, and because
nothing is captured where it is kept. -/
theorem new_binder_not_mem_apply (sub : Subst) (y : String) (body : Named) (x : String)
    (hx : x ∈ free body) (hxy : x ≠ y) : new_binder sub y body ∉ free (apply_subst sub x) := by
  simp only [new_binder]
  split
  · exact fresh_not_mem_apply sub body x hx
  · rename_i h
    exact not_captures_apply sub y x _ (by simpa using h) hx hxy

/-- Nothing is captured by a substitution that leaves the free variables alone. -/
theorem captures_false_of_id : ∀ (sub : Subst) (y : String) (fv : Fren.FinSet String),
    (∀ x, x ∈ fv → x ≠ y → apply_subst sub x = .Var x) → captures? sub y fv = false := by
  intro sub
  induction sub with
  | Id => intro y fv _; simp [captures?]
  | Bind z s rest ih =>
    intro y fv h
    simp only [captures?, decide_eq_false_iff_not, not_or, Bool.not_eq_true]
    constructor
    · rintro ⟨⟨hzy, hz⟩, hy⟩
      have := h z hz hzy
      simp only [apply_subst, if_true] at this
      subst this; rw [mem_free_var] at hy; exact hzy hy.symm
    · apply ih
      intro x hx hxy
      have hx' : x ∈ fv ∧ x ≠ z := by simpa using hx
      have := h x hx'.1 hxy
      simpa [apply_subst, Ne.symm hx'.2] using this

/-- A substitution that leaves the free variables of `t` alone leaves `t` alone. -/
theorem subst_all_id : ∀ (t : Named) (sub : Subst),
    (∀ x, x ∈ free t → apply_subst sub x = .Var x) → subst_all sub t = t := by
  intro t
  induction t with
  | Var x => intro sub h; simp only [subst_all]; exact h x (by simp [free])
  | Lam y ty body ih =>
    intro sub h
    have hnb : new_binder sub y body = y := by
      simp only [new_binder]
      rw [captures_false_of_id sub y (free body) fun x hx hxy => h x (mem_free_lam.2 ⟨hx, hxy⟩)]
      rfl
    simp only [subst_all, hnb]
    congr 1
    apply ih
    intro x hx
    by_cases hxy : y = x
    · subst hxy; simp [apply_subst]
    · simp only [apply_subst, hxy, if_false]; exact h x (mem_free_lam.2 ⟨hx, Ne.symm hxy⟩)
  | App f a ihf iha =>
    intro sub h; simp only [subst_all]
    rw [ihf sub fun x hx => h x (mem_free_app.2 (Or.inl hx)), iha sub fun x hx => h x (mem_free_app.2 (Or.inr hx))]
  | True => intro sub _; rfl
  | False => intro sub _; rfl
  | If c a b ihc iha ihb =>
    intro sub h; simp only [subst_all]
    rw [ihc sub fun x hx => h x (mem_free_if.2 (Or.inl hx)),
      iha sub fun x hx => h x (mem_free_if.2 (Or.inr (Or.inl hx))),
      ihb sub fun x hx => h x (mem_free_if.2 (Or.inr (Or.inr hx)))]

/-- `substitution_laws::unused`. -/
theorem subst_unused {x : String} {s t : Named} (h : x ∉ free t) : subst x s t = t := by
  apply subst_all_id
  intro z hz
  have : x ≠ z := fun e => h (e ▸ hz)
  simp [apply_subst, this]

/-- A free variable of the result is free in what some free variable of the
term was replaced by. -/
theorem free_subst_all : ∀ (t : Named) (sub : Subst) (z : String),
    z ∈ free (subst_all sub t) → ∃ x, x ∈ free t ∧ z ∈ free (apply_subst sub x) := by
  intro t
  induction t with
  | Var x => intro sub z h; exact ⟨x, by simp [free], by simpa [subst_all] using h⟩
  | Lam y ty body ih =>
    intro sub z h
    simp only [subst_all, mem_free_lam] at h
    obtain ⟨x, hx, hz⟩ := ih _ _ h.1
    by_cases hxy : y = x
    · subst hxy; simp only [apply_subst, if_true, mem_free_var] at hz; exact absurd hz h.2
    · simp only [apply_subst, hxy, if_false] at hz
      exact ⟨x, mem_free_lam.2 ⟨hx, Ne.symm hxy⟩, hz⟩
  | App f a ihf iha =>
    intro sub z h
    simp only [subst_all, mem_free_app] at h
    rcases h with h | h
    · obtain ⟨x, hx, hz⟩ := ihf _ _ h; exact ⟨x, mem_free_app.2 (Or.inl hx), hz⟩
    · obtain ⟨x, hx, hz⟩ := iha _ _ h; exact ⟨x, mem_free_app.2 (Or.inr hx), hz⟩
  | True => intro sub z h; simp [subst_all, free] at h
  | False => intro sub z h; simp [subst_all, free] at h
  | If c a b ihc iha ihb =>
    intro sub z h
    simp only [subst_all, mem_free_if] at h
    rcases h with h | h | h
    · obtain ⟨x, hx, hz⟩ := ihc _ _ h; exact ⟨x, mem_free_if.2 (Or.inl hx), hz⟩
    · obtain ⟨x, hx, hz⟩ := iha _ _ h; exact ⟨x, mem_free_if.2 (Or.inr (Or.inl hx)), hz⟩
    · obtain ⟨x, hx, hz⟩ := ihb _ _ h; exact ⟨x, mem_free_if.2 (Or.inr (Or.inr hx)), hz⟩

/-- `substitution_laws::free_after`. -/
theorem free_subst (x : String) (s t : Named) : free (subst x s t) ⊆ (free t \ {x}) ∪ free s := by
  intro z hz
  obtain ⟨w, hw, hz⟩ := free_subst_all t _ z hz
  by_cases hwx : x = w
  · subst hwx; simp only [apply_subst, if_true] at hz; simp [hz]
  · simp only [apply_subst, hwx, if_false, mem_free_var] at hz; subst hz; simp [hw, Ne.symm hwx]

/-! ## Typing -/

/-- Inversion (TAPL 9.3.1), one lemma per form of term. -/
theorem typeof_app_inv {ctx : Ctx} {t1 t2 : Named} {ty : Ty} (h : typeof ctx (Term.App t1 t2) = some ty) :
    ∃ p, typeof ctx t1 = some (Ty.Arrow p ty) ∧ typeof ctx t2 = some p := by
  simp only [typeof] at h
  split at h
  · rename_i ty11 ty12 ty2 h1 h2
    split at h
    · rename_i e; cases h; exact ⟨_, e ▸ h1, h2⟩
    · cases h
  · cases h

theorem typeof_lam_inv {ctx : Ctx} {x : String} {ty1 : Ty} {b : Named} {ty : Ty}
    (h : typeof ctx (Term.Lam x ty1 b) = some ty) :
    ∃ ty2, typeof (.Bind x ty1 ctx) b = some ty2 ∧ ty = .Arrow ty1 ty2 := by
  simp only [typeof] at h
  split at h
  · rename_i ty2 h2; cases h; exact ⟨ty2, h2, rfl⟩
  · cases h

theorem typeof_if_inv {ctx : Ctx} {c a b : Named} {ty : Ty} (h : typeof ctx (Term.If c a b) = some ty) :
    typeof ctx c = some .Boolean ∧ typeof ctx a = some ty ∧ typeof ctx b = some ty := by
  simp only [typeof] at h
  split at h
  · rename_i ty2 ty3 h1 h2 h3
    split at h
    · rename_i e; cases h; exact ⟨h1, h2, e ▸ h3⟩
    · cases h
  · cases h

/-- The rules T-App, T-Abs and T-If, read forwards. -/
theorem typeof_app {ctx : Ctx} {t1 t2 : Named} {p ty : Ty} (h1 : typeof ctx t1 = some (.Arrow p ty))
    (h2 : typeof ctx t2 = some p) : typeof ctx (Term.App t1 t2) = some ty := by
  simp [typeof, h1, h2]

theorem typeof_lam {ctx : Ctx} {x : String} {ty1 ty2 : Ty} {b : Named} (h : typeof (.Bind x ty1 ctx) b = some ty2) :
    typeof ctx (Term.Lam x ty1 b) = some (.Arrow ty1 ty2) := by
  simp [typeof, h]

theorem typeof_if {ctx : Ctx} {c a b : Named} {ty : Ty} (hc : typeof ctx c = some .Boolean)
    (ha : typeof ctx a = some ty) (hb : typeof ctx b = some ty) : typeof ctx (Term.If c a b) = some ty := by
  simp [typeof, hc, ha, hb]

theorem lookup_bind_same (ctx : Ctx) (x : String) (ty : Ty) : lookup (.Bind x ty ctx) x = some ty := by simp [lookup]

theorem lookup_bind_other {ctx : Ctx} {x y : String} (ty : Ty) (h : y ≠ x) :
    lookup (.Bind y ty ctx) x = lookup ctx x := by
  simp [lookup, h]

/-! ### The typing relation

The book defines `ctx |- t: T` inductively, by the rules in the comment of
`typeof`; `typeof` decides it. -/

inductive Typing : Ctx → Named → Ty → Prop
  | var {ctx : Ctx} {x : String} {ty : Ty} : lookup ctx x = some ty → Typing ctx (.Var x) ty
  | abs {ctx : Ctx} {x : String} {ty1 : Ty} {t2 : Named} {ty2 : Ty} :
      Typing (.Bind x ty1 ctx) t2 ty2 → Typing ctx (.Lam x ty1 t2) (.Arrow ty1 ty2)
  | app {ctx : Ctx} {t1 t2 : Named} {ty11 ty12 : Ty} :
      Typing ctx t1 (.Arrow ty11 ty12) → Typing ctx t2 ty11 → Typing ctx (.App t1 t2) ty12
  | if_ {ctx : Ctx} {t1 t2 t3 : Named} {ty : Ty} :
      Typing ctx t1 .Boolean → Typing ctx t2 ty → Typing ctx t3 ty → Typing ctx (.If t1 t2 t3) ty
  | true {ctx : Ctx} : Typing ctx .True .Boolean
  | false {ctx : Ctx} : Typing ctx .False .Boolean

/-- `typeof` is sound and complete for the typing relation. -/
theorem typeof_iff : ∀ (t : Named) (ctx : Ctx) (ty : Ty), typeof ctx t = some ty ↔ Typing ctx t ty := by
  intro t
  induction t with
  | Var x =>
    intro ctx ty
    constructor
    · intro h; exact .var (by simpa [typeof] using h)
    · intro h; cases h with | var hl => simpa [typeof] using hl
  | Lam y ty1 b ih =>
    intro ctx ty
    constructor
    · intro h
      obtain ⟨ty2, hb, rfl⟩ := typeof_lam_inv h
      exact .abs ((ih _ _).1 hb)
    · intro h; cases h with | abs hb => exact typeof_lam ((ih _ _).2 hb)
  | App f a ihf iha =>
    intro ctx ty
    constructor
    · intro h
      obtain ⟨p, hf, ha⟩ := typeof_app_inv h
      exact .app ((ihf _ _).1 hf) ((iha _ _).1 ha)
    · intro h; cases h with | app hf ha => exact typeof_app ((ihf _ _).2 hf) ((iha _ _).2 ha)
  | True =>
    intro ctx ty
    constructor
    · intro h; simp only [typeof, Option.some.injEq] at h; subst h; exact .true
    · intro h; cases h; simp [typeof]
  | False =>
    intro ctx ty
    constructor
    · intro h; simp only [typeof, Option.some.injEq] at h; subst h; exact .false
    · intro h; cases h; simp [typeof]
  | If c a b ihc iha ihb =>
    intro ctx ty
    constructor
    · intro h
      obtain ⟨hc, ha, hb⟩ := typeof_if_inv h
      exact .if_ ((ihc _ _).1 hc) ((iha _ _).1 ha) ((ihb _ _).1 hb)
    · intro h
      cases h with | if_ hc ha hb => exact typeof_if ((ihc _ _).2 hc) ((iha _ _).2 ha) ((ihb _ _).2 hb)

/-- Uniqueness of types (TAPL 9.3.3): `typeof` is a function. -/
theorem Typing.unique {ctx : Ctx} {t : Named} {ty1 ty2 : Ty} (h1 : Typing ctx t ty1) (h2 : Typing ctx t ty2) :
    ty1 = ty2 := by
  have e1 := (typeof_iff t ctx ty1).2 h1
  have e2 := (typeof_iff t ctx ty2).2 h2
  rw [e1] at e2; cases e2; rfl

/-! ## Evaluation -/

theorem value_iff (t : Named) :
    value? String String t = true ↔ (∃ x ty b, t = .Lam x ty b) ∨ t = .True ∨ t = .False := by
  cases t <;> simp [value?]

/-- A value takes no step (TAPL 3.5.7). -/
theorem step_value {t : Named} (h : value? String String t = true) : step t = none := by
  rw [value_iff] at h
  rcases h with ⟨x, ty, b, rfl⟩ | rfl | rfl <;> simp [step]

theorem step_var (x : String) : step (Term.Var x : Named) = none := by simp [step]

theorem not_value_cases {t : Named} (h : ¬ value? String String t = true) :
    (∃ x, t = .Var x) ∨ (∃ a b, t = .App a b) ∨ (∃ c a b, t = .If c a b) := by
  cases t <;> simp_all [value?]

/-- The rules E-AppAbs, E-App1, E-App2 and E-If, read forwards, and where
`step` stops. -/
theorem step_app_beta {x : String} {ty : Ty} {b v : Named} (hv : value? String String v = true) :
    step (Term.App (Term.Lam x ty b) v) = some (subst x v b) := by
  simp [step, hv, value?]

theorem step_app_left_some {t1 t2 u1 : Named} (h : ¬ value? String String t1 = true) (hs : step t1 = some u1) :
    step (Term.App t1 t2) = some (Term.App u1 t2) := by
  rcases not_value_cases h with ⟨x, rfl⟩ | ⟨a, b, rfl⟩ | ⟨c, a, b, rfl⟩
  · simp [step] at hs
  · rw [step]
    all_goals first | (rw [hs]; simp [h]) | simp
  · rw [step]
    all_goals first | (rw [hs]; simp [h]) | simp

theorem step_app_left_none {t1 t2 : Named} (h : ¬ value? String String t1 = true) (hs : step t1 = none) :
    step (Term.App t1 t2) = none := by
  rcases not_value_cases h with ⟨x, rfl⟩ | ⟨a, b, rfl⟩ | ⟨c, a, b, rfl⟩
  · simp [step]
  · rw [step]
    all_goals first | (rw [hs]; simp [h]) | simp
  · rw [step]
    all_goals first | (rw [hs]; simp [h]) | simp

theorem step_app_right_some {t1 t2 u2 : Named} (h1 : value? String String t1 = true)
    (h2 : ¬ value? String String t2 = true) (hs : step t2 = some u2) :
    step (Term.App t1 t2) = some (Term.App t1 u2) := by
  rcases (value_iff t1).1 h1 with ⟨x, ty, b, rfl⟩ | rfl | rfl <;>
    rcases not_value_cases h2 with ⟨y, rfl⟩ | ⟨a, c, rfl⟩ | ⟨c, a, d, rfl⟩
  all_goals first
    | (rw [step_var] at hs; cases hs)
    | (rw [step]; all_goals first | (rw [hs]; simp [value?]) | simp)

theorem step_app_right_none {t1 t2 : Named} (h1 : value? String String t1 = true)
    (h2 : ¬ value? String String t2 = true) (hs : step t2 = none) : step (Term.App t1 t2) = none := by
  rcases (value_iff t1).1 h1 with ⟨x, ty, b, rfl⟩ | rfl | rfl <;>
    rcases not_value_cases h2 with ⟨y, rfl⟩ | ⟨a, c, rfl⟩ | ⟨c, a, d, rfl⟩
  all_goals (rw [step]; all_goals first | (rw [hs]; simp [value?]) | simp)

theorem step_app_stuck {t1 t2 : Named} (h1 : value? String String t1 = true) (h2 : value? String String t2 = true)
    (hl : ∀ x ty b, t1 ≠ .Lam x ty b) : step (Term.App t1 t2) = none := by
  rw [value_iff] at h1
  rcases h1 with ⟨x, ty, b, rfl⟩ | rfl | rfl
  · exact absurd rfl (hl x ty b)
  · simp [step, h2, value?]
  · simp [step, h2, value?]

theorem step_if_some {c a b u : Named} (hc : c ≠ .True) (hc' : c ≠ .False) (hs : step c = some u) :
    step (Term.If c a b) = some (Term.If u a b) := by
  cases c with
  | True => exact absurd rfl hc
  | False => exact absurd rfl hc'
  | Var x => simp [step] at hs
  | Lam x ty b => simp [step] at hs
  | App c1 c2 => rw [step]; all_goals first | (rw [hs]; done) | (rw [hs]; simp) | simp
  | If c1 c2 c3 => rw [step]; all_goals first | (rw [hs]; done) | (rw [hs]; simp) | simp

theorem step_if_none {c a b : Named} (hc : c ≠ .True) (hc' : c ≠ .False) (hs : step c = none) :
    step (Term.If c a b) = none := by
  cases c with
  | True => exact absurd rfl hc
  | False => exact absurd rfl hc'
  | Var x => simp [step]
  | Lam x ty b => simp [step]
  | App c1 c2 => rw [step]; all_goals first | (rw [hs]; done) | (rw [hs]; simp) | simp
  | If c1 c2 c3 => rw [step]; all_goals first | (rw [hs]; done) | (rw [hs]; simp) | simp

/-- Inversion: a step of an application, by the shape of its parts. -/
theorem step_app_inv {t1 t2 u : Named} (hs : step (Term.App t1 t2) = some u) :
    (¬ value? String String t1 = true ∧ ∃ u1, step t1 = some u1 ∧ u = Term.App u1 t2) ∨
    (value? String String t1 = true ∧ ¬ value? String String t2 = true ∧ ∃ u2, step t2 = some u2 ∧ u = Term.App t1 u2) ∨
    (value? String String t2 = true ∧ ∃ x ty b, t1 = Term.Lam x ty b ∧ u = subst x t2 b) := by
  by_cases v1 : value? String String t1 = true
  · by_cases v2 : value? String String t2 = true
    · right; right
      refine ⟨v2, ?_⟩
      rcases (value_iff t1).1 v1 with ⟨x, ty, b, rfl⟩ | rfl | rfl
      · rw [step_app_beta v2] at hs; cases hs; exact ⟨x, ty, b, rfl, rfl⟩
      · rw [step_app_stuck v1 v2 (by simp)] at hs; cases hs
      · rw [step_app_stuck v1 v2 (by simp)] at hs; cases hs
    · right; left
      refine ⟨v1, v2, ?_⟩
      cases h2 : step t2 with
      | none => rw [step_app_right_none v1 v2 h2] at hs; cases hs
      | some u2 => rw [step_app_right_some v1 v2 h2] at hs; cases hs; exact ⟨u2, rfl, rfl⟩
  · left
    refine ⟨v1, ?_⟩
    cases h1 : step t1 with
    | none => rw [step_app_left_none v1 h1] at hs; cases hs
    | some u1 => rw [step_app_left_some v1 h1] at hs; cases hs; exact ⟨u1, rfl, rfl⟩

/-- Inversion: a step of a conditional, by the shape of its condition. -/
theorem step_if_inv {c a b u : Named} (hs : step (Term.If c a b) = some u) :
    (c = .True ∧ u = a) ∨ (c = .False ∧ u = b) ∨ (c ≠ .True ∧ c ≠ .False ∧ ∃ u1, step c = some u1 ∧ u = Term.If u1 a b) := by
  by_cases e1 : c = .True
  · subst e1; simp [step] at hs; exact Or.inl ⟨rfl, hs.symm⟩
  · by_cases e2 : c = .False
    · subst e2; simp [step] at hs; exact Or.inr (Or.inl ⟨rfl, hs.symm⟩)
    · right; right
      refine ⟨e1, e2, ?_⟩
      cases h1 : step c with
      | none => rw [step_if_none e1 e2 h1] at hs; cases hs
      | some u1 => rw [step_if_some e1 e2 h1] at hs; cases hs; exact ⟨u1, rfl, rfl⟩

/-! ### The reduction relation

The book defines `t --> u` inductively, by the rules in the comment of
`step`; `step` decides it. -/

inductive Step : Named → Named → Prop
  | app_abs {x : String} {ty : Ty} {t12 v : Named} :
      value? String String v = true → Step (.App (.Lam x ty t12) v) (subst x v t12)
  | app1 {t1 t1' t2 : Named} : Step t1 t1' → Step (.App t1 t2) (.App t1' t2)
  | app2 {v1 t2 t2' : Named} : value? String String v1 = true → Step t2 t2' → Step (.App v1 t2) (.App v1 t2')
  | if_true {t2 t3 : Named} : Step (.If .True t2 t3) t2
  | if_false {t2 t3 : Named} : Step (.If .False t2 t3) t3
  | if_ {t1 t1' t2 t3 : Named} : Step t1 t1' → Step (.If t1 t2 t3) (.If t1' t2 t3)

/-- `step` is sound and complete for the reduction relation. -/
theorem step_iff : ∀ (t u : Named), step t = some u ↔ Step t u := by
  intro t
  induction t with
  | Var x =>
    intro u
    constructor
    · intro h; simp [step] at h
    · intro h; cases h
  | Lam x ty b _ =>
    intro u
    constructor
    · intro h; simp [step] at h
    · intro h; cases h
  | True =>
    intro u
    constructor
    · intro h; simp [step] at h
    · intro h; cases h
  | False =>
    intro u
    constructor
    · intro h; simp [step] at h
    · intro h; cases h
  | App t1 t2 ih1 ih2 =>
    intro u
    constructor
    · intro h
      rcases step_app_inv h with ⟨_, u1, hu1, rfl⟩ | ⟨v1, _, u2, hu2, rfl⟩ | ⟨v2, x, ty, b, rfl, rfl⟩
      · exact .app1 ((ih1 _).1 hu1)
      · exact .app2 v1 ((ih2 _).1 hu2)
      · exact .app_abs v2
    · intro h
      cases h with
      | app_abs hv => exact step_app_beta hv
      | app1 hs =>
        have hs' := (ih1 _).2 hs
        exact step_app_left_some (fun v => by rw [step_value v] at hs'; cases hs') hs'
      | app2 hv hs =>
        have hs' := (ih2 _).2 hs
        exact step_app_right_some hv (fun v => by rw [step_value v] at hs'; cases hs') hs'
  | If c a b ihc _ _ =>
    intro u
    constructor
    · intro h
      rcases step_if_inv h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, u1, hu1, rfl⟩
      · exact .if_true
      · exact .if_false
      · exact .if_ ((ihc _).1 hu1)
    · intro h
      cases h with
      | if_true => simp [step]
      | if_false => simp [step]
      | if_ hs =>
        have hs' := (ihc _).2 hs
        have e1 : c ≠ .True := by rintro rfl; simp [step] at hs'
        have e2 : c ≠ .False := by rintro rfl; simp [step] at hs'
        exact step_if_some e1 e2 hs'

/-- Determinacy of one-step evaluation (TAPL 3.5.4): `step` is a function. -/
theorem Step.deterministic {t u u' : Named} (h1 : Step t u) (h2 : Step t u') : u = u' := by
  have e1 := (step_iff t u).2 h1
  have e2 := (step_iff t u').2 h2
  rw [e1] at e2; cases e2; rfl

/-! ### The evaluators -/

theorem normalize_zero_inv {t v : Named} (h : normalize .Zero t = some v) :
    value? String String t = true ∧ v = t := by
  by_cases hv : value? String String t = true
  · simp [normalize, hv] at h; exact ⟨hv, h.symm⟩
  · simp [normalize, hv] at h

theorem normalize_more_inv {n : Fuel} {t v : Named} (h : normalize (.More n) t = some v) :
    (value? String String t = true ∧ v = t) ∨ (∃ u, step t = some u ∧ normalize n u = some v) := by
  by_cases hv : value? String String t = true
  · simp [normalize, hv] at h; exact Or.inl ⟨hv, h.symm⟩
  · simp only [normalize, hv, Bool.false_eq_true, if_false] at h
    cases hs : step t with
    | none => simp [hs] at h
    | some u => simp [hs] at h; exact Or.inr ⟨u, rfl, h⟩

theorem normalize_value {t : Named} (hv : value? String String t = true) : ∀ n, normalize n t = some t
  | .Zero => by simp [normalize, hv]
  | .More _ => by simp [normalize, hv]

theorem normalize_step {t u : Named} (hs : step t = some u) (n : Fuel) :
    normalize (.More n) t = normalize n u := by
  have hv : ¬ value? String String t = true := fun hv => by rw [step_value hv] at hs; cases hs
  simp [normalize, hv, hs]

theorem normalize_some_value : ∀ (n : Fuel) {t v : Named}, normalize n t = some v → value? String String v = true
  | .Zero, _, _, h => by obtain ⟨hv, rfl⟩ := normalize_zero_inv h; exact hv
  | .More n, _, _, h => by
    rcases normalize_more_inv h with ⟨hv, rfl⟩ | ⟨u, _, hu⟩
    · exact hv
    · exact normalize_some_value n hu

/-- `evaluators::normalize_monotone`: more fuel changes nothing. -/
theorem normalize_mono : ∀ (n : Fuel) {t v : Named}, normalize n t = some v → normalize (.More n) t = some v
  | .Zero, _, _, h => by obtain ⟨hv, rfl⟩ := normalize_zero_inv h; exact normalize_value hv _
  | .More n, _, _, h => by
    rcases normalize_more_inv h with ⟨hv, rfl⟩ | ⟨u, hs, hu⟩
    · exact normalize_value hv _
    · rw [normalize_step hs]; exact normalize_mono n hu

theorem eval_zero (t : Named) : eval .Zero t = none := by simp [eval]

theorem eval_of_value {t : Named} (n : Fuel) (h : value? String String t = true) : eval (.More n) t = some t := by
  rcases (value_iff t).1 h with ⟨x, ty, b, rfl⟩ | rfl | rfl <;> simp [eval]

theorem eval_app_inv {n : Fuel} {t1 t2 v : Named} (h : eval (.More n) (Term.App t1 t2) = some v) :
    ∃ x ty b w, eval n t1 = some (Term.Lam x ty b) ∧ eval n t2 = some w ∧ eval n (subst x w b) = some v := by
  simp only [eval] at h
  split at h
  · rename_i x ty b w h1 h2; exact ⟨x, ty, b, w, h1, h2, h⟩
  · cases h

theorem eval_if_inv {n : Fuel} {c a b v : Named} (h : eval (.More n) (Term.If c a b) = some v) :
    (eval n c = some .True ∧ eval n a = some v) ∨ (eval n c = some .False ∧ eval n b = some v) := by
  simp only [eval] at h
  split at h
  · rename_i hc; exact Or.inl ⟨hc, h⟩
  · rename_i hc; exact Or.inr ⟨hc, h⟩
  · cases h

theorem eval_app {n : Fuel} {t1 t2 v : Named} {x : String} {ty : Ty} {b w : Named} (h1 : eval n t1 = some (Term.Lam x ty b))
    (h2 : eval n t2 = some w) (h3 : eval n (subst x w b) = some v) : eval (.More n) (Term.App t1 t2) = some v := by
  simp [eval, h1, h2, h3]

theorem eval_if_true {n : Fuel} {c a b v : Named} (hc : eval n c = some .True) (ha : eval n a = some v) :
    eval (.More n) (Term.If c a b) = some v := by
  simp [eval, hc, ha]

theorem eval_if_false {n : Fuel} {c a b v : Named} (hc : eval n c = some .False) (hb : eval n b = some v) :
    eval (.More n) (Term.If c a b) = some v := by
  simp [eval, hc, hb]

/-- `evaluators::big_step_values`: what big-step evaluation gives is a value. -/
theorem eval_value : ∀ (n : Fuel) (t v : Named), eval n t = some v → value? String String v = true := by
  intro n
  induction n with
  | Zero => intro t v h; simp [eval] at h
  | More m ih =>
    intro t v h
    cases t with
    | Var x => simp [eval] at h
    | App t1 t2 => obtain ⟨x, ty, b, w, _, _, h3⟩ := eval_app_inv h; exact ih _ _ h3
    | If c a b =>
      rcases eval_if_inv h with ⟨_, ha⟩ | ⟨_, hb⟩
      · exact ih _ _ ha
      · exact ih _ _ hb
    | Lam x ty b => simp only [eval] at h; cases h; simp [value?]
    | True => simp only [eval] at h; cases h; simp [value?]
    | False => simp only [eval] at h; cases h; simp [value?]

/-- `evaluators::eval_monotone`: more fuel changes nothing. -/
theorem eval_mono : ∀ (n : Fuel) (t v : Named), eval n t = some v → eval (.More n) t = some v := by
  intro n
  induction n with
  | Zero => intro t v h; simp [eval] at h
  | More m ih =>
    intro t v h
    cases t with
    | Var x => simp [eval] at h
    | App t1 t2 =>
      obtain ⟨x, ty, b, w, h1, h2, h3⟩ := eval_app_inv h
      exact eval_app (ih _ _ h1) (ih _ _ h2) (ih _ _ h3)
    | If c a b =>
      rcases eval_if_inv h with ⟨hc, ha⟩ | ⟨hc, hb⟩
      · exact eval_if_true (ih _ _ hc) (ih _ _ ha)
      · exact eval_if_false (ih _ _ hc) (ih _ _ hb)
    | Lam x ty b => simp only [eval] at h ⊢; exact h
    | True => simp only [eval] at h ⊢; exact h
    | False => simp only [eval] at h ⊢; exact h

theorem eval_value_inv {n : Fuel} {t v : Named} (hv : value? String String t = true) (h : eval n t = some v) : v = t := by
  cases n with
  | Zero => simp [eval] at h
  | More m => rw [eval_of_value m hv] at h; cases h; rfl

/-- `evaluators::step_eval`: a step changes nothing of what big-step
evaluation gives. -/
theorem step_eval : ∀ (n : Fuel) (t u v : Named), step t = some u → eval n t = some v → eval n u = some v := by
  intro n
  induction n with
  | Zero => intro t u v _ h; simp [eval] at h
  | More m ih =>
    intro t u v hs h
    cases t with
    | Var x => simp [step] at hs
    | Lam x ty b => simp [step] at hs
    | True => simp [step] at hs
    | False => simp [step] at hs
    | App t1 t2 =>
      obtain ⟨x, ty, b, w, h1, h2, h3⟩ := eval_app_inv h
      rcases step_app_inv hs with ⟨_, u1, hu1, rfl⟩ | ⟨_, _, u2, hu2, rfl⟩ | ⟨v2, y, ty', bd, rfl, rfl⟩
      · exact eval_app (ih _ _ _ hu1 h1) h2 h3
      · exact eval_app h1 (ih _ _ _ hu2 h2) h3
      · cases m with
        | Zero => simp [eval] at h1
        | More k =>
          rw [eval_of_value k (by simp [value?])] at h1; cases h1
          rw [eval_of_value k v2] at h2; cases h2
          exact eval_mono _ _ _ h3
    | If c a b =>
      rcases step_if_inv hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e1, e2, u1, hu1, rfl⟩
      · rcases eval_if_inv h with ⟨_, ha⟩ | ⟨hc, _⟩
        · exact eval_mono _ _ _ ha
        · cases m with
          | Zero => simp [eval] at hc
          | More k => rw [eval_of_value k (by simp [value?])] at hc; cases hc
      · rcases eval_if_inv h with ⟨hc, _⟩ | ⟨_, hb⟩
        · cases m with
          | Zero => simp [eval] at hc
          | More k => rw [eval_of_value k (by simp [value?])] at hc; cases hc
        · exact eval_mono _ _ _ hb
      · rcases eval_if_inv h with ⟨hc, ha⟩ | ⟨hc, hb⟩
        · exact eval_if_true (ih _ _ _ hu1 hc) ha
        · exact eval_if_false (ih _ _ _ hu1 hc) hb

/-- `evaluators::agree`: the two evaluators agree. -/
theorem eval_normalize : ∀ (m n : Fuel) (t v w : Named), eval n t = some v → normalize m t = some w → v = w := by
  intro m
  induction m with
  | Zero =>
    intro n t v w he hn
    simp only [normalize] at hn
    split at hn
    · rename_i hv; cases hn; exact eval_value_inv hv he
    · cases hn
  | More k ih =>
    intro n t v w he hn
    simp only [normalize] at hn
    split at hn
    · rename_i hv; cases hn; exact eval_value_inv hv he
    · split at hn
      · rename_i u hu; exact ih n u v w (step_eval n t u v hu he) hn
      · cases hn

/-! ## Metatheory -/

/-! ### The context lemmas -/

/-- `context_lemmas::extensional`: typing depends on the context only at the
free variables. -/
theorem typeof_ext : ∀ (t : Named) (c1 c2 : Ctx),
    (∀ x, x ∈ free t → lookup c1 x = lookup c2 x) → typeof c1 t = typeof c2 t := by
  intro t
  induction t with
  | Var x => intro c1 c2 h; simp only [typeof]; exact h x (by simp [free])
  | Lam y ty body ih =>
    intro c1 c2 h
    simp only [typeof]
    rw [ih (.Bind y ty c1) (.Bind y ty c2)]
    intro x hx
    by_cases hxy : y = x
    · subst hxy; simp [lookup]
    · rw [lookup_bind_other ty hxy, lookup_bind_other ty hxy]
      exact h x (mem_free_lam.2 ⟨hx, Ne.symm hxy⟩)
  | App f a ihf iha =>
    intro c1 c2 h
    simp only [typeof]
    rw [ihf c1 c2 (fun x hx => h x (mem_free_app.2 (Or.inl hx))),
      iha c1 c2 (fun x hx => h x (mem_free_app.2 (Or.inr hx)))]
  | True => intro c1 c2 _; rfl
  | False => intro c1 c2 _; rfl
  | If c a b ihc iha ihb =>
    intro c1 c2 h
    simp only [typeof]
    rw [ihc c1 c2 (fun x hx => h x (mem_free_if.2 (Or.inl hx))),
      iha c1 c2 (fun x hx => h x (mem_free_if.2 (Or.inr (Or.inl hx)))),
      ihb c1 c2 (fun x hx => h x (mem_free_if.2 (Or.inr (Or.inr hx))))]

/-- `context_lemmas::weakening` (TAPL 9.3.7): a binding of a name that is not
free changes no type. -/
theorem typeof_weaken {ctx : Ctx} {t : Named} {x : String} (ty : Ty) (hx : x ∉ free t) :
    typeof (.Bind x ty ctx) t = typeof ctx t :=
  typeof_ext t _ _ fun _ hz => lookup_bind_other ty fun e => hx (e ▸ hz)

/-- The substitution lemma, for a parallel substitution: where `sub` gives
each free variable of `t` a term of its type, it keeps `t`'s type. -/
theorem typeof_subst_all : ∀ (t : Named) (c1 c2 : Ctx) (sub : Subst) (ty : Ty),
    typeof c1 t = some ty →
    (∀ x, x ∈ free t → ∀ τ, lookup c1 x = some τ → typeof c2 (apply_subst sub x) = some τ) →
    typeof c2 (subst_all sub t) = some ty := by
  intro t
  induction t with
  | Var x =>
    intro c1 c2 sub ty h hs
    simp only [subst_all]
    exact hs x (by simp [free]) ty (by simpa [typeof] using h)
  | Lam y ty1 body ih =>
    intro c1 c2 sub ty h hs
    obtain ⟨ty2, hb, rfl⟩ := typeof_lam_inv h
    simp only [subst_all]
    apply typeof_lam
    apply ih _ _ _ _ hb
    intro x hx τ hl
    by_cases hxy : y = x
    · subst hxy
      rw [lookup_bind_same] at hl; cases hl
      simp [apply_subst, typeof, lookup]
    · rw [lookup_bind_other _ hxy] at hl
      have := hs x (mem_free_lam.2 ⟨hx, Ne.symm hxy⟩) τ hl
      simp only [apply_subst, hxy, if_false]
      rw [typeof_weaken _ (new_binder_not_mem_apply sub y body x hx (Ne.symm hxy))]
      exact this
  | App f a ihf iha =>
    intro c1 c2 sub ty h hs
    obtain ⟨p, hf, ha⟩ := typeof_app_inv h
    simp only [subst_all]
    exact typeof_app (ihf _ _ _ _ hf fun x hx => hs x (mem_free_app.2 (Or.inl hx)))
      (iha _ _ _ _ ha fun x hx => hs x (mem_free_app.2 (Or.inr hx)))
  | True => intro c1 c2 sub ty h _; simpa [subst_all, typeof] using h
  | False => intro c1 c2 sub ty h _; simpa [subst_all, typeof] using h
  | If c a b ihc iha ihb =>
    intro c1 c2 sub ty h hs
    obtain ⟨hc, ha, hb⟩ := typeof_if_inv h
    simp only [subst_all]
    exact typeof_if (ihc _ _ _ _ hc fun x hx => hs x (mem_free_if.2 (Or.inl hx)))
      (iha _ _ _ _ ha fun x hx => hs x (mem_free_if.2 (Or.inr (Or.inl hx))))
      (ihb _ _ _ _ hb fun x hx => hs x (mem_free_if.2 (Or.inr (Or.inr hx))))

/-- `context_lemmas::substitution`, the substitution lemma (TAPL 9.3.8). -/
theorem typeof_subst {ctx : Ctx} {x : String} {s t : Named} {tx ty : Ty} (ht : typeof (.Bind x tx ctx) t = some ty)
    (hs : typeof ctx s = some tx) : typeof ctx (subst x s t) = some ty := by
  apply typeof_subst_all t _ _ _ _ ht
  intro z _ τ hl
  by_cases hz : x = z
  · subst hz; rw [lookup_bind_same] at hl; cases hl; simpa [apply_subst] using hs
  · rw [lookup_bind_other _ hz] at hl; simpa [apply_subst, hz, typeof] using hl

/-! ### Type safety -/

/-- Canonical forms (TAPL 9.3.4). -/
theorem canonical_bool {ctx : Ctx} {t : Named} (hv : value? String String t = true)
    (ht : typeof ctx t = some .Boolean) : t = .True ∨ t = .False := by
  rw [value_iff] at hv
  rcases hv with ⟨x, ty, b, rfl⟩ | rfl | rfl
  · obtain ⟨_, _, h⟩ := typeof_lam_inv ht; cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem canonical_arrow {ctx : Ctx} {t : Named} {p r : Ty} (hv : value? String String t = true)
    (ht : typeof ctx t = some (.Arrow p r)) : ∃ x b, t = .Lam x p b := by
  rw [value_iff] at hv
  rcases hv with ⟨x, ty, b, rfl⟩ | rfl | rfl
  · obtain ⟨_, _, h⟩ := typeof_lam_inv ht; cases h; exact ⟨x, b, rfl⟩
  · simp [typeof] at ht
  · simp [typeof] at ht

/-- `type_safety::preservation` (TAPL 9.3.9): a step keeps the type. -/
theorem preservation : ∀ (t : Named) (ctx : Ctx) (ty : Ty) (u : Named),
    typeof ctx t = some ty → step t = some u → typeof ctx u = some ty := by
  intro t
  induction t with
  | Var x => intro ctx ty u _ hs; simp [step] at hs
  | Lam y ty1 b _ => intro ctx ty u _ hs; simp [step] at hs
  | True => intro ctx ty u _ hs; simp [step] at hs
  | False => intro ctx ty u _ hs; simp [step] at hs
  | App t1 t2 ih1 ih2 =>
    intro ctx ty u ht hs
    obtain ⟨p, h1, h2⟩ := typeof_app_inv ht
    rcases step_app_inv hs with ⟨_, u1, hu1, rfl⟩ | ⟨_, _, u2, hu2, rfl⟩ | ⟨_, x, ty1, b, rfl, rfl⟩
    · exact typeof_app (ih1 _ _ _ h1 hu1) h2
    · exact typeof_app h1 (ih2 _ _ _ h2 hu2)
    · obtain ⟨ty2, hb, e⟩ := typeof_lam_inv h1
      cases e
      exact typeof_subst hb h2
  | If c a b ihc _ _ =>
    intro ctx ty u ht hs
    obtain ⟨hc, ha, hb⟩ := typeof_if_inv ht
    rcases step_if_inv hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, u1, hu1, rfl⟩
    · exact ha
    · exact hb
    · exact typeof_if (ihc _ _ _ hc hu1) ha hb

/-- `type_safety::progress` (TAPL 9.3.5): a well-typed closed term is a value
or steps. -/
theorem progress : ∀ (t : Named) (ty : Ty),
    typeof .Empty t = some ty → value? String String t = true ∨ ∃ u, step t = some u := by
  intro t
  induction t with
  | Var x => intro ty h; simp [typeof, lookup] at h
  | Lam y ty1 b _ => intro ty _; left; simp [value?]
  | True => intro ty _; left; simp [value?]
  | False => intro ty _; left; simp [value?]
  | App t1 t2 ih1 ih2 =>
    intro ty ht
    right
    obtain ⟨p, h1, h2⟩ := typeof_app_inv ht
    rcases ih1 _ h1 with v1 | ⟨u1, hu1⟩
    · rcases ih2 _ h2 with v2 | ⟨u2, hu2⟩
      · obtain ⟨x, b, rfl⟩ := canonical_arrow v1 h1
        exact ⟨_, step_app_beta v2⟩
      · have nv2 : ¬ value? String String t2 = true := fun v => by rw [step_value v] at hu2; cases hu2
        exact ⟨_, step_app_right_some v1 nv2 hu2⟩
    · have nv1 : ¬ value? String String t1 = true := fun v => by rw [step_value v] at hu1; cases hu1
      exact ⟨_, step_app_left_some nv1 hu1⟩
  | If c a b ihc _ _ =>
    intro ty ht
    right
    obtain ⟨hc, _, _⟩ := typeof_if_inv ht
    rcases ihc _ hc with vc | ⟨u, hu⟩
    · rcases canonical_bool vc hc with rfl | rfl
      · exact ⟨a, by simp [step]⟩
      · exact ⟨b, by simp [step]⟩
    · have e1 : c ≠ .True := by rintro rfl; simp [step] at hu
      have e2 : c ≠ .False := by rintro rfl; simp [step] at hu
      exact ⟨_, step_if_some e1 e2 hu⟩

/-- `type_safety::safety`: however far a well-typed closed term is reduced,
it has its type and is a value or steps. -/
theorem safety : ∀ (n : Fuel) (t : Named) (ty : Ty), typeof .Empty t = some ty →
    typeof .Empty (reduce n t) = some ty ∧
      (value? String String (reduce n t) = true ∨ ∃ u, step (reduce n t) = some u) := by
  intro n
  induction n with
  | Zero => intro t ty h; simp only [reduce]; exact ⟨h, progress t ty h⟩
  | More m ih =>
    intro t ty h
    simp only [reduce]
    split
    · rename_i u hu; exact ih u ty (preservation t _ ty u h hu)
    · exact ⟨h, progress t ty h⟩

/-- `type_safety::big_step_preservation`: big-step evaluation preserves the
type. -/
theorem eval_preservation : ∀ (n : Fuel) (ctx : Ctx) (t v : Named) (ty : Ty),
    typeof ctx t = some ty → eval n t = some v → typeof ctx v = some ty := by
  intro n
  induction n with
  | Zero => intro ctx t v ty _ h; simp [eval] at h
  | More m ih =>
    intro ctx t v ty ht h
    cases t with
    | Var x => simp [eval] at h
    | Lam x ty1 b => simp only [eval] at h; cases h; exact ht
    | True => simp only [eval] at h; cases h; exact ht
    | False => simp only [eval] at h; cases h; exact ht
    | App t1 t2 =>
      obtain ⟨x, ty1, b, w, h1, h2, h3⟩ := eval_app_inv h
      obtain ⟨p, hf, ha⟩ := typeof_app_inv ht
      have hl := ih _ _ _ _ hf h1
      obtain ⟨ty2, hb, e⟩ := typeof_lam_inv hl
      cases e
      exact ih _ _ _ _ (typeof_subst hb (ih _ _ _ _ ha h2)) h3
    | If c a b =>
      obtain ⟨_, ha, hb⟩ := typeof_if_inv ht
      rcases eval_if_inv h with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact ih _ _ _ _ ha h2
      · exact ih _ _ _ _ hb h2

/-! ### Normalization

Tait's method, as in chapter 12 of TAPL: a logical relation `R` on closed
terms of each type, closed under steps in both directions, and the
fundamental theorem, that a well-typed term closed by related terms is
related. The closing substitutions are `Good`: they capture nothing, so
`subst_all` renames no binder under them, and composing two of them is one
(`subst_comp`). -/

/-- A substitution that captures nothing: what it substitutes for a
variable is closed, or the variable itself. -/
def Good (sub : Subst) : Prop := ∀ w z, z ∈ free (apply_subst sub w) → z = w

theorem good_id : Good .Id := by
  intro w z hz; simp only [apply_subst, mem_free_var] at hz; exact hz

theorem good_bind {sub : Subst} {x : String} {s : Named} (h : Good sub) (hs : ∀ z, z ∈ free s → z = x) :
    Good (.Bind x s sub) := by
  intro w z hz
  by_cases hx : x = w
  · subst hx; simp only [apply_subst, if_true] at hz; exact hs z hz
  · simp only [apply_subst, hx, if_false] at hz; exact h w z hz

theorem good_bind_var {sub : Subst} (h : Good sub) (x : String) : Good (.Bind x (.Var x) sub) :=
  good_bind h fun _ hz => mem_free_var.1 hz

theorem good_bind_closed {sub : Subst} {x : String} {s : Named} (h : Good sub) (hs : ∀ z, z ∉ free s) :
    Good (.Bind x s sub) :=
  good_bind h fun z hz => absurd hz (hs z)

/-- A good substitution captures nothing, whatever the body's free variables. -/
theorem captures_false_of_good : ∀ (sub : Subst) (y : String) (fv : Fren.FinSet String),
    (∀ w, w ∈ fv → ∀ z, z ∈ free (apply_subst sub w) → z = w) → captures? sub y fv = false := by
  intro sub
  induction sub with
  | Id => intro y fv _; simp [captures?]
  | Bind x s rest ih =>
    intro y fv h
    simp only [captures?, decide_eq_false_iff_not, not_or, Bool.not_eq_true]
    constructor
    · rintro ⟨⟨hxy, hx⟩, hy⟩
      exact hxy (h x hx y (by simpa [apply_subst] using hy)).symm
    · apply ih
      intro w hw z hz
      have hw' : w ∈ fv ∧ w ≠ x := by simpa using hw
      exact h w hw'.1 z (by simpa [apply_subst, Ne.symm hw'.2] using hz)

theorem new_binder_of_good {sub : Subst} (h : Good sub) (y : String) (body : Named) :
    new_binder sub y body = y := by
  simp only [new_binder]
  rw [captures_false_of_good sub y (free body) fun w _ z hz => h w z hz]
  rfl

theorem subst_all_lam_of_good {sub : Subst} (h : Good sub) (y : String) (ty : Ty) (b : Named) :
    subst_all sub (.Lam y ty b) = .Lam y ty (subst_all (.Bind y (.Var y) sub) b) := by
  simp only [subst_all, new_binder_of_good h]

/-- The identity on `zs` in front of `sub`: the binders passed on the way
into a term. -/
def rename : List String → Subst → Subst
  | [], sub => sub
  | z :: zs, sub => .Bind z (.Var z) (rename zs sub)

theorem good_rename {sub : Subst} (h : Good sub) : ∀ zs, Good (rename zs sub)
  | [] => h
  | z :: zs => good_bind_var (good_rename h zs) z

theorem apply_rename_mem {x : String} : ∀ (zs : List String) (sub : Subst), x ∈ zs →
    apply_subst (rename zs sub) x = .Var x
  | [], _, h => by simp at h
  | z :: zs, sub, h => by
    simp only [rename, apply_subst]
    by_cases hz : z = x
    · subst hz; simp
    · rw [if_neg hz]; exact apply_rename_mem zs sub (by simpa [List.mem_cons, Ne.symm hz] using h)

theorem apply_rename_not_mem {x : String} : ∀ (zs : List String) (sub : Subst), x ∉ zs →
    apply_subst (rename zs sub) x = apply_subst sub x
  | [], _, _ => rfl
  | z :: zs, sub, h => by
    have hz : z ≠ x := fun e => h (by simp [e])
    simp only [rename, apply_subst, hz, if_false]
    exact apply_rename_not_mem zs sub fun hm => h (List.mem_cons_of_mem z hm)

/-- Substituting a closed `v` for `y` after a good `σ` that kept `y` is
substituting `σ` with `y ↦ v`, under any binders. -/
theorem subst_all_comp : ∀ (b : Named) (zs : List String) (y : String) (v : Named) (σ : Subst),
    Good σ → (∀ z, z ∉ free v) →
    subst_all (rename zs (.Bind y v .Id)) (subst_all (rename zs (.Bind y (.Var y) σ)) b) =
      subst_all (rename zs (.Bind y v σ)) b := by
  intro b
  induction b with
  | Var x =>
    intro zs y v σ hσ hv
    simp only [subst_all]
    by_cases hx : x ∈ zs
    · rw [apply_rename_mem zs _ hx, apply_rename_mem zs _ hx]
      simp only [subst_all]
      rw [apply_rename_mem zs _ hx]
    · rw [apply_rename_not_mem zs _ hx, apply_rename_not_mem zs _ hx]
      by_cases hy : y = x
      · subst hy
        simp [apply_subst, subst_all, apply_rename_not_mem zs _ hx]
      · simp only [apply_subst, hy, if_false]
        apply subst_all_id
        intro w hw
        rw [hσ x w hw, apply_rename_not_mem zs _ hx]
        simp [apply_subst, hy]
  | Lam w ty b ih =>
    intro zs y v σ hσ hv
    have h1 : Good (rename zs (.Bind y (.Var y) σ)) := good_rename (good_bind_var hσ y) zs
    have h2 : Good (rename zs (.Bind y v .Id)) := good_rename (good_bind_closed good_id hv) zs
    have h3 : Good (rename zs (.Bind y v σ)) := good_rename (good_bind_closed hσ hv) zs
    rw [subst_all_lam_of_good h1, subst_all_lam_of_good h2, subst_all_lam_of_good h3]
    congr 1
    exact ih (w :: zs) y v σ hσ hv
  | App f a ihf iha =>
    intro zs y v σ hσ hv
    simp only [subst_all]
    rw [ihf zs y v σ hσ hv, iha zs y v σ hσ hv]
  | True => intros; rfl
  | False => intros; rfl
  | If c a b ihc iha ihb =>
    intro zs y v σ hσ hv
    simp only [subst_all]
    rw [ihc zs y v σ hσ hv, iha zs y v σ hσ hv, ihb zs y v σ hσ hv]

theorem subst_comp {σ : Subst} {y : String} {v b : Named} (hσ : Good σ) (hv : ∀ z, z ∉ free v) :
    subst y v (subst_all (.Bind y (.Var y) σ) b) = subst_all (.Bind y v σ) b := by
  have := subst_all_comp b [] y v σ hσ hv
  simpa [subst, rename] using this

/-- A free variable of a well-typed term is in the context. -/
theorem free_lookup : ∀ (t : Named) (ctx : Ctx) (ty : Ty), typeof ctx t = some ty →
    ∀ z, z ∈ free t → lookup ctx z ≠ none := by
  intro t
  induction t with
  | Var x =>
    intro ctx ty h z hz
    rw [mem_free_var] at hz; subst hz
    simp only [typeof] at h
    simp [h]
  | Lam x ty1 b ih =>
    intro ctx ty h z hz
    obtain ⟨ty2, hb, rfl⟩ := typeof_lam_inv h
    rw [mem_free_lam] at hz
    have := ih _ _ hb z hz.1
    rwa [lookup_bind_other _ (Ne.symm hz.2)] at this
  | App f a ihf iha =>
    intro ctx ty h z hz
    obtain ⟨p, hf, ha⟩ := typeof_app_inv h
    rcases mem_free_app.1 hz with hz | hz
    · exact ihf _ _ hf z hz
    · exact iha _ _ ha z hz
  | True => intro ctx ty _ z hz; simp [free] at hz
  | False => intro ctx ty _ z hz; simp [free] at hz
  | If c a b ihc iha ihb =>
    intro ctx ty h z hz
    obtain ⟨hc, ha, hb⟩ := typeof_if_inv h
    rcases mem_free_if.1 hz with hz | hz | hz
    · exact ihc _ _ hc z hz
    · exact iha _ _ ha z hz
    · exact ihb _ _ hb z hz

theorem closed_of_typed {t : Named} {ty : Ty} (h : typeof .Empty t = some ty) : ∀ z, z ∉ free t :=
  fun z hz => free_lookup t _ _ h z hz (by simp [lookup])

/-- `t` reduces to a value with some fuel. -/
def Halts (t : Named) : Prop := ∃ n v, normalize n t = some v

theorem halts_step {t u : Named} (hs : step t = some u) : Halts t ↔ Halts u := by
  constructor
  · rintro ⟨n, v, h⟩
    cases n with
    | Zero => obtain ⟨hv, _⟩ := normalize_zero_inv h; rw [step_value hv] at hs; cases hs
    | More m => exact ⟨m, v, by rwa [normalize_step hs] at h⟩
  · rintro ⟨n, v, h⟩; exact ⟨.More n, v, by rw [normalize_step hs]; exact h⟩

/-- The logical relation: a closed term of the type that halts and, at an
arrow type, takes related arguments to related results. -/
def R : Ty → Named → Prop
  | .Boolean, t => typeof .Empty t = some .Boolean ∧ Halts t
  | .Arrow a b, t => typeof .Empty t = some (.Arrow a b) ∧ Halts t ∧ ∀ s, R a s → R b (.App t s)

theorem R_typed : ∀ {ty : Ty} {t : Named}, R ty t → typeof .Empty t = some ty
  | .Boolean, _, h => h.1
  | .Arrow _ _, _, h => h.1

theorem R_halts : ∀ {ty : Ty} {t : Named}, R ty t → Halts t
  | .Boolean, _, h => h.2
  | .Arrow _ _, _, h => h.2.1

/-- `R` is closed under a step, forwards and backwards. -/
theorem R_step : ∀ (ty : Ty) {t u : Named}, typeof .Empty t = some ty → step t = some u → (R ty t ↔ R ty u)
  | .Boolean, t, u, ht, hs => by
    have hu := preservation t .Empty .Boolean u ht hs
    simp only [R, ht, hu, true_and]
    exact halts_step hs
  | .Arrow a b, t, u, ht, hs => by
    have hu := preservation t .Empty (.Arrow a b) u ht hs
    have hv : ¬ value? String String t = true := fun hv => by rw [step_value hv] at hs; cases hs
    simp only [R, ht, hu, true_and]
    rw [halts_step hs]
    apply and_congr_right; intro _
    constructor
    · intro h s hr; exact (R_step b (typeof_app ht (R_typed hr)) (step_app_left_some hv hs)).1 (h s hr)
    · intro h s hr; exact (R_step b (typeof_app ht (R_typed hr)) (step_app_left_some hv hs)).2 (h s hr)

theorem R_normalize : ∀ (n : Fuel) (ty : Ty) {t v : Named}, typeof .Empty t = some ty → normalize n t = some v →
    (R ty t ↔ R ty v)
  | .Zero, _, _, _, _, h => by obtain ⟨_, rfl⟩ := normalize_zero_inv h; exact Iff.rfl
  | .More n, ty, t, _, ht, h => by
    rcases normalize_more_inv h with ⟨_, rfl⟩ | ⟨u, hs, hu⟩
    · exact Iff.rfl
    · exact (R_step ty ht hs).trans (R_normalize n ty (preservation t .Empty ty u ht hs) hu)

/-- The argument of a value reduces under the application. -/
theorem R_app_arg : ∀ (n : Fuel) (b : Ty) {f s v : Named}, value? String String f = true →
    typeof .Empty (.App f s) = some b → normalize n s = some v → (R b (.App f s) ↔ R b (.App f v))
  | .Zero, _, _, _, _, _, _, h => by obtain ⟨_, rfl⟩ := normalize_zero_inv h; exact Iff.rfl
  | .More n, b, f, s, _, hf, ht, h => by
    rcases normalize_more_inv h with ⟨_, rfl⟩ | ⟨u, hs, hu⟩
    · exact Iff.rfl
    · have hv : ¬ value? String String s = true := fun hv => by rw [step_value hv] at hs; cases hs
      have hstep := step_app_right_some (t2 := s) (u2 := u) hf hv hs
      exact (R_step b ht hstep).trans (R_app_arg n b hf (preservation _ .Empty b _ ht hstep) hu)

/-- The condition of a conditional reduces under it. -/
theorem R_if_cond : ∀ (n : Fuel) (ty : Ty) {c a b v : Named},
    typeof .Empty (.If c a b) = some ty → normalize n c = some v → (R ty (.If c a b) ↔ R ty (.If v a b))
  | .Zero, _, _, _, _, _, _, h => by obtain ⟨_, rfl⟩ := normalize_zero_inv h; exact Iff.rfl
  | .More n, ty, c, a, b, _, ht, h => by
    rcases normalize_more_inv h with ⟨_, rfl⟩ | ⟨u, hs, hu⟩
    · exact Iff.rfl
    · have h1 : c ≠ .True := fun e => by subst e; rw [step_value (by simp [value?])] at hs; cases hs
      have h2 : c ≠ .False := fun e => by subst e; rw [step_value (by simp [value?])] at hs; cases hs
      have hstep := step_if_some (a := a) (b := b) h1 h2 hs
      exact (R_step ty ht hstep).trans (R_if_cond n ty (preservation _ .Empty ty _ ht hstep) hu)

theorem R_true : R .Boolean .True := ⟨by simp [typeof], .Zero, .True, normalize_value (by simp [value?]) _⟩
theorem R_false : R .Boolean .False := ⟨by simp [typeof], .Zero, .False, normalize_value (by simp [value?]) _⟩

/-- `σ` closes `Γ`: it takes each variable of `Γ` to a related term, and
leaves every other variable alone. -/
def Inst (Γ : Ctx) (σ : Subst) : Prop :=
  ∀ x, (∀ ty, lookup Γ x = some ty → R ty (apply_subst σ x)) ∧ (lookup Γ x = none → apply_subst σ x = .Var x)

theorem good_of_inst {Γ : Ctx} {σ : Subst} (h : Inst Γ σ) : Good σ := by
  intro w z hz
  cases hl : lookup Γ w with
  | none => rw [(h w).2 hl, mem_free_var] at hz; exact hz
  | some ty => exact absurd hz (closed_of_typed (R_typed ((h w).1 ty hl)) z)

theorem inst_empty : Inst .Empty .Id := fun _ =>
  ⟨fun _ h => by simp [lookup] at h, fun _ => by simp [apply_subst]⟩

theorem inst_bind {Γ : Ctx} {σ : Subst} {y : String} {a : Ty} {v : Named} (h : Inst Γ σ) (hv : R a v) :
    Inst (.Bind y a Γ) (.Bind y v σ) := by
  intro x
  by_cases hyx : y = x
  · subst hyx
    refine ⟨fun ty hl => ?_, fun hl => ?_⟩
    · rw [lookup_bind_same] at hl; cases hl; simpa [apply_subst] using hv
    · rw [lookup_bind_same] at hl; cases hl
  · rw [lookup_bind_other _ hyx]
    simp only [apply_subst, hyx, if_false]
    exact h x

/-- The fundamental theorem: a well-typed term, closed by related terms, is related. -/
theorem fundamental : ∀ (t : Named) (Γ : Ctx) (ty : Ty) (σ : Subst), typeof Γ t = some ty → Inst Γ σ →
    R ty (subst_all σ t) := by
  intro t
  induction t with
  | Var x =>
    intro Γ ty σ h hσ
    simp only [subst_all]
    exact (hσ x).1 ty (by simpa [typeof] using h)
  | Lam y a b ih =>
    intro Γ ty σ h hσ
    obtain ⟨b', hb, rfl⟩ := typeof_lam_inv h
    have hg := good_of_inst hσ
    rw [subst_all_lam_of_good hg]
    have hB : typeof (.Bind y a .Empty) (subst_all (.Bind y (.Var y) σ) b) = some b' := by
      apply typeof_subst_all b _ _ _ _ hb
      intro x _ τ hl
      by_cases hyx : y = x
      · subst hyx; rw [lookup_bind_same] at hl; cases hl; simp [apply_subst, typeof, lookup]
      · rw [lookup_bind_other _ hyx] at hl
        simp only [apply_subst, hyx, if_false]
        have hx := (hσ x).1 τ hl
        rw [typeof_weaken a (closed_of_typed (R_typed hx) y)]
        exact R_typed hx
    refine ⟨typeof_lam hB, ⟨.Zero, _, normalize_value (by simp [value?]) _⟩, fun s hs => ?_⟩
    obtain ⟨n, v, hn⟩ := R_halts hs
    have hsv : R a v := (R_normalize n a (R_typed hs) hn).1 hs
    have hvv : value? String String v = true := normalize_some_value n hn
    have hApp : typeof .Empty (.App (.Lam y a (subst_all (.Bind y (.Var y) σ) b)) s) = some b' :=
      typeof_app (typeof_lam hB) (R_typed hs)
    rw [R_app_arg n b' (by simp [value?]) hApp hn]
    have hApp' : typeof .Empty (.App (.Lam y a (subst_all (.Bind y (.Var y) σ) b)) v) = some b' :=
      typeof_app (typeof_lam hB) (R_typed hsv)
    rw [R_step b' hApp' (step_app_beta hvv), subst_comp hg (closed_of_typed (R_typed hsv))]
    exact ih _ _ _ hb (inst_bind hσ hsv)
  | App f x ihf ihx =>
    intro Γ ty σ h hσ
    obtain ⟨p, hf, hx⟩ := typeof_app_inv h
    simp only [subst_all]
    exact (ihf _ _ _ hf hσ).2.2 _ (ihx _ _ _ hx hσ)
  | True =>
    intro Γ ty σ h _
    simp only [typeof, Option.some.injEq] at h
    subst h; exact R_true
  | False =>
    intro Γ ty σ h _
    simp only [typeof, Option.some.injEq] at h
    subst h; exact R_false
  | If c a b ihc iha ihb =>
    intro Γ ty σ h hσ
    obtain ⟨hc, ha, hb⟩ := typeof_if_inv h
    simp only [subst_all]
    have hC := ihc _ _ _ hc hσ
    have hA := iha _ _ _ ha hσ
    have hB := ihb _ _ _ hb hσ
    obtain ⟨n, v, hn⟩ := R_halts hC
    have hCv : R .Boolean v := (R_normalize n .Boolean (R_typed hC) hn).1 hC
    have hvv := normalize_some_value n hn
    have hIf : typeof .Empty (.If (subst_all σ c) (subst_all σ a) (subst_all σ b)) = some ty :=
      typeof_if (R_typed hC) (R_typed hA) (R_typed hB)
    rw [R_if_cond n ty hIf hn]
    have hIf' : typeof .Empty (.If v (subst_all σ a) (subst_all σ b)) = some ty :=
      typeof_if (R_typed hCv) (R_typed hA) (R_typed hB)
    rcases canonical_bool hvv (R_typed hCv) with rfl | rfl
    · rw [R_step ty (u := subst_all σ a) hIf' (by simp [step])]; exact hA
    · rw [R_step ty (u := subst_all σ b) hIf' (by simp [step])]; exact hB

/-- Normalization: a well-typed closed term reduces to a value. -/
theorem normalization (t : Named) (ty : Ty) (h : typeof .Empty t = some ty) : ∃ n v, normalize n t = some v := by
  have hR := fundamental t .Empty ty .Id h inst_empty
  rw [subst_all_id t .Id fun x _ => by simp [apply_subst]] at hR
  exact R_halts hR

/-! ## Nameless terms -/

/-- The names that `to_named` declares, from the outside in: `x`, `x'`, ... -/
def gen : Nat → Names
  | 0 => .Nil
  | d + 1 => .Cons (fresh_name (gen d)) (gen d)

theorem length_fresh_name : ∀ d, (fresh_name (gen d)).length = d + 1
  | 0 => by simp [gen, fresh_name, Fren.Str.lit]; rfl
  | d + 1 => by
    simp only [gen, fresh_name, Fren.Str.lit, String.length_append, length_fresh_name d]; rfl

theorem fresh_name_gen_inj {i j : Nat} (h : fresh_name (gen i) = fresh_name (gen j)) : i = j := by
  have := congrArg String.length h
  rw [length_fresh_name, length_fresh_name] at this
  omega

theorem nth_gen : ∀ (d k : Nat), k < d → nth (gen d) (k : Int) = some (fresh_name (gen (d - 1 - k)))
  | 0, k, h => absurd h (Nat.not_lt_zero k)
  | d + 1, 0, _ => by simp [gen, nth]
  | d + 1, k + 1, h => by
    have e1 : ((k + 1 : Nat) : Int) ≠ 0 := by omega
    have e2 : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
    simp only [gen, nth]
    rw [if_neg e1, e2, nth_gen d k (by omega)]
    congr 3; omega

theorem nth_gen_none : ∀ (d : Nat) (k : Int), (k < 0 ∨ (d : Int) ≤ k) → nth (gen d) k = none
  | 0, k, _ => by simp [gen, nth]
  | d + 1, k, h => by
    simp only [gen, nth]
    split
    · rename_i e; subst e; omega
    · apply nth_gen_none; omega

theorem index_of_gen : ∀ (d j : Nat), j < d → index_of (gen d) (fresh_name (gen j)) = some ((d - 1 - j : Nat) : Int)
  | 0, j, h => absurd h (Nat.not_lt_zero j)
  | d + 1, j, h => by
    simp only [gen, index_of]
    by_cases hd : d = j
    · subst hd; simp
    · have ne : fresh_name (gen d) ≠ fresh_name (gen j) := fun e => hd (fresh_name_gen_inj e)
      rw [if_neg ne, index_of_gen d j (by omega)]
      simp only
      congr 1; omega

theorem to_named_lam_inv {names : Names} {a : Anon} {ty : Ty} {body : Term Int Anon} {t : Named}
    (h : to_named names (Term.Lam a ty body) = some t) :
    ∃ b, to_named (.Cons (fresh_name names) names) body = some b ∧ t = Term.Lam (fresh_name names) ty b := by
  simp only [to_named] at h
  split at h
  · rename_i b hb; cases h; exact ⟨b, hb, rfl⟩
  · cases h

/-- `nameless_round_trip::named_nameless`: a closed nameless term, named and
nameless again, is itself. -/
theorem to_nameless_to_named : ∀ (n : Term Int Anon) (d : Nat) (t : Named),
    to_named (gen d) n = some t → to_nameless (gen d) t = some n := by
  intro n
  induction n with
  | Var k =>
    intro d t h
    simp only [to_named] at h
    split at h
    · rename_i x hx; cases h
      by_cases hk : k < 0 ∨ (d : Int) ≤ k
      · rw [nth_gen_none d k hk] at hx; cases hx
      · have hk' : k.toNat < d := by omega
        have e : ((k.toNat : Nat) : Int) = k := by omega
        rw [← e, nth_gen d k.toNat hk'] at hx; cases hx
        simp only [to_nameless]
        rw [index_of_gen d _ (by omega)]
        simp only
        congr 2; omega
    · cases h
  | Lam a ty body ih =>
    intro d t h
    obtain ⟨b, hb, rfl⟩ := to_named_lam_inv h
    have : Names.Cons (fresh_name (gen d)) (gen d) = gen (d + 1) := rfl
    rw [this] at hb
    simp only [to_nameless, this, ih (d + 1) b hb]
  | App n1 n2 ih1 ih2 =>
    intro d t h
    simp only [to_named] at h
    split at h
    · rename_i t1 t2 h1 h2; cases h; simp [to_nameless, ih1 d t1 h1, ih2 d t2 h2]
    · cases h
  | If n1 n2 n3 ih1 ih2 ih3 =>
    intro d t h
    simp only [to_named] at h
    split at h
    · rename_i t1 t2 t3 h1 h2 h3; cases h; simp [to_nameless, ih1 d t1 h1, ih2 d t2 h2, ih3 d t3 h3]
    · cases h
  | True => intro d t h; simp only [to_named] at h; cases h; simp [to_nameless]
  | False => intro d t h; simp only [to_named] at h; cases h; simp [to_nameless]

/-- `nameless_round_trip::closed_converts`: a term converts to the nameless
form where each free variable is in scope. -/
theorem to_nameless_some : ∀ (t : Named) (names : Names), (∀ x, x ∈ free t → ∃ k, index_of names x = some k) →
    ∃ n, to_nameless names t = some n := by
  intro t
  induction t with
  | Var x =>
    intro names h
    obtain ⟨k, hk⟩ := h x (by simp [free])
    exact ⟨Term.Var k, by simp [to_nameless, hk]⟩
  | Lam y ty b ih =>
    intro names h
    obtain ⟨nb, hnb⟩ := ih (.Cons y names) (by
      intro x hx
      by_cases hxy : y = x
      · subst hxy; exact ⟨0, by simp [index_of]⟩
      · obtain ⟨k, hk⟩ := h x (by simp [free, hx, Ne.symm hxy])
        exact ⟨k + 1, by simp [index_of, hxy, hk]⟩)
    exact ⟨Term.Lam .Anon ty nb, by simp [to_nameless, hnb]⟩
  | App a b iha ihb =>
    intro names h
    obtain ⟨na, ha⟩ := iha names fun x hx => h x (by simp [free, hx])
    obtain ⟨nb, hb⟩ := ihb names fun x hx => h x (by simp [free, hx])
    exact ⟨Term.App na nb, by simp [to_nameless, ha, hb]⟩
  | True => intro names _; exact ⟨Term.True, by simp [to_nameless]⟩
  | False => intro names _; exact ⟨Term.False, by simp [to_nameless]⟩
  | If c a b ihc iha ihb =>
    intro names h
    obtain ⟨nc, hc⟩ := ihc names fun x hx => h x (by simp [free, hx])
    obtain ⟨na, ha⟩ := iha names fun x hx => h x (by simp [free, hx])
    obtain ⟨nb, hb⟩ := ihb names fun x hx => h x (by simp [free, hx])
    exact ⟨Term.If nc na nb, by simp [to_nameless, hc, ha, hb]⟩

/-- How many names a list has. -/
def namesLen : Names → Nat
  | .Nil => 0
  | .Cons _ rest => namesLen rest + 1

theorem index_of_lt : ∀ (names : Names) (x : String) (k : Int), index_of names x = some k → 0 ≤ k ∧ k < namesLen names := by
  intro names
  induction names with
  | Nil => intro x k h; simp [index_of] at h
  | Cons y rest ih =>
    intro x k h
    simp only [index_of] at h
    split at h
    · cases h; simp [namesLen]
    · split at h
      · rename_i j hj; cases h; have := ih x j hj; simp only [namesLen]; omega
      · cases h

theorem nth_of_lt : ∀ (names : Names) (k : Int), 0 ≤ k → k < namesLen names → ∃ x, nth names k = some x := by
  intro names
  induction names with
  | Nil => intro k _ h; simp [namesLen] at h; omega
  | Cons y rest ih =>
    intro k h0 h
    simp only [nth]
    split
    · exact ⟨y, rfl⟩
    · simp only [namesLen] at h; exact ih (k - 1) (by omega) (by omega)

/-- What `to_nameless` gives, by the shapes of the two terms. -/
theorem to_nameless_inv {names : Names} {t : Named} {n : Term Int Anon} (h : to_nameless names t = some n) :
    match n, t with
    | .Var k, .Var x => index_of names x = some k
    | .Lam _ ty nb, .Lam y ty' b => ty = ty' ∧ to_nameless (.Cons y names) b = some nb
    | .App n1 n2, .App t1 t2 => to_nameless names t1 = some n1 ∧ to_nameless names t2 = some n2
    | .If n1 n2 n3, .If t1 t2 t3 =>
      to_nameless names t1 = some n1 ∧ to_nameless names t2 = some n2 ∧ to_nameless names t3 = some n3
    | .True, .True => True
    | .False, .False => True
    | _, _ => False := by
  cases t <;> simp only [to_nameless] at h <;> (try split at h) <;> cases h <;> simp_all

/-- `nameless_round_trip::converts_back`: what converts to the nameless form
under some names converts back under as many. -/
theorem to_named_some : ∀ (n : Term Int Anon) (names names' : Names) (t : Named), namesLen names' = namesLen names →
    to_nameless names t = some n → ∃ t', to_named names' n = some t' := by
  intro n
  induction n with
  | Var k =>
    intro names names' t hl h
    have h' := to_nameless_inv h
    cases t <;> simp only at h' <;> try exact absurd h' id
    rename_i x
    obtain ⟨h0, hlt⟩ := index_of_lt names x k h'
    obtain ⟨y, hy⟩ := nth_of_lt names' k h0 (hl ▸ hlt)
    exact ⟨Term.Var y, by simp [to_named, hy]⟩
  | Lam a ty body ih =>
    intro names names' t hl h
    have h' := to_nameless_inv h
    cases t <;> simp only at h' <;> try exact absurd h' id
    rename_i y ty' b
    obtain ⟨b', hb'⟩ := ih (.Cons y names) (.Cons (fresh_name names') names') b (by simp [namesLen, hl]) h'.2
    exact ⟨Term.Lam (fresh_name names') ty b', by simp [to_named, hb']⟩
  | App n1 n2 ih1 ih2 =>
    intro names names' t hl h
    have h' := to_nameless_inv h
    cases t <;> simp only at h' <;> try exact absurd h' id
    rename_i t1 t2
    obtain ⟨u1, hu1⟩ := ih1 names names' t1 hl h'.1
    obtain ⟨u2, hu2⟩ := ih2 names names' t2 hl h'.2
    exact ⟨Term.App u1 u2, by simp [to_named, hu1, hu2]⟩
  | If n1 n2 n3 ih1 ih2 ih3 =>
    intro names names' t hl h
    have h' := to_nameless_inv h
    cases t <;> simp only at h' <;> try exact absurd h' id
    rename_i t1 t2 t3
    obtain ⟨u1, hu1⟩ := ih1 names names' t1 hl h'.1
    obtain ⟨u2, hu2⟩ := ih2 names names' t2 hl h'.2.1
    obtain ⟨u3, hu3⟩ := ih3 names names' t3 hl h'.2.2
    exact ⟨Term.If u1 u2 u3, by simp [to_named, hu1, hu2, hu3]⟩
  | True => intro names names' t _ _; exact ⟨Term.True, by simp [to_named]⟩
  | False => intro names names' t _ _; exact ⟨Term.False, by simp [to_named]⟩

/-! ### Alpha-equivalence

Substitution commutes with the nameless form (`to_nameless_subst_all`): a
substitution `σ` on names is a parallel substitution `ρ` on indices
(`napply`), and the renamed binders change nothing, because a new binder
is free in nothing substituted for another free variable
(`new_binder_not_mem_apply`). The three laws of `alpha_laws` follow. -/

/-- The names of `l1`, then those of `l2`. -/
def napp : Names → Names → Names
  | .Nil, l2 => l2
  | .Cons y rest, l2 => .Cons y (napp rest l2)

theorem index_of_napp_some : ∀ (l1 l2 : Names) (z : String) (j : Int),
    index_of l1 z = some j → index_of (napp l1 l2) z = some j
  | .Nil, _, _, _, h => by simp [index_of] at h
  | .Cons y rest, l2, z, j, h => by
    simp only [napp, index_of] at h ⊢
    by_cases hy : y = z
    · simpa [hy] using h
    · simp only [hy, if_false] at h ⊢
      cases hr : index_of rest z with
      | none => rw [hr] at h; cases h
      | some k =>
        rw [hr] at h
        rw [index_of_napp_some rest l2 z k hr]
        exact h

theorem index_of_napp_none : ∀ (l1 l2 : Names) (z : String), index_of l1 z = none →
    index_of (napp l1 l2) z = (index_of l2 z).map (· + (namesLen l1 : Int))
  | .Nil, l2, z, _ => by simp only [napp]; cases h : index_of l2 z <;> simp [namesLen]
  | .Cons y rest, l2, z, h => by
    simp only [napp, index_of] at h ⊢
    by_cases hy : y = z
    · simp [hy] at h
    · simp only [hy, if_false] at h ⊢
      cases hr : index_of rest z with
      | none =>
        rw [index_of_napp_none rest l2 z hr]
        cases index_of l2 z <;> simp [namesLen]; omega
      | some k => rw [hr] at h; cases h

theorem to_nameless_var_inv {names : Names} {z : String} {n : Term Int Anon}
    (h : to_nameless names (.Var z) = some n) : ∃ j, index_of names z = some j ∧ n = .Var j := by
  simp only [to_nameless] at h
  cases hj : index_of names z with
  | none => rw [hj] at h; cases h
  | some j => rw [hj] at h; cases h; exact ⟨j, rfl, rfl⟩

theorem to_nameless_lam_inv {names : Names} {y : String} {ty : Ty} {b : Named} {n : Term Int Anon}
    (h : to_nameless names (.Lam y ty b) = some n) :
    ∃ nb, to_nameless (.Cons y names) b = some nb ∧ n = .Lam .Anon ty nb := by
  simp only [to_nameless] at h
  cases hb : to_nameless (.Cons y names) b with
  | none => rw [hb] at h; cases h
  | some nb => rw [hb] at h; cases h; exact ⟨nb, rfl, rfl⟩

theorem to_nameless_app_inv {names : Names} {a b : Named} {n : Term Int Anon}
    (h : to_nameless names (.App a b) = some n) :
    ∃ na nb, to_nameless names a = some na ∧ to_nameless names b = some nb ∧ n = .App na nb := by
  simp only [to_nameless] at h
  cases ha : to_nameless names a with
  | none => rw [ha] at h; cases h
  | some na =>
    cases hb : to_nameless names b with
    | none => rw [ha, hb] at h; cases h
    | some nb => rw [ha, hb] at h; cases h; exact ⟨na, nb, rfl, rfl, rfl⟩

theorem to_nameless_if_inv {names : Names} {c a b : Named} {n : Term Int Anon}
    (h : to_nameless names (.If c a b) = some n) :
    ∃ nc na nb, to_nameless names c = some nc ∧ to_nameless names a = some na ∧ to_nameless names b = some nb ∧
      n = .If nc na nb := by
  simp only [to_nameless] at h
  cases hc : to_nameless names c with
  | none => rw [hc] at h; cases h
  | some nc =>
    cases ha : to_nameless names a with
    | none => rw [hc, ha] at h; cases h
    | some na =>
      cases hb : to_nameless names b with
      | none => rw [hc, ha, hb] at h; cases h
      | some nb => rw [hc, ha, hb] at h; cases h; exact ⟨nc, na, nb, rfl, rfl, rfl, rfl⟩

/-- Weakening: a name declared outside `l1` binders that is free nowhere in
the term shifts the indices beyond `l1` by one. -/
theorem to_nameless_weaken : ∀ (u : Named) (l1 l' : Names) (y : String) (nu : Term Int Anon),
    to_nameless (napp l1 l') u = some nu → (∀ z, z ∈ free u → index_of l1 z = none → z ≠ y) →
    to_nameless (napp l1 (.Cons y l')) u = some (shift 1 (namesLen l1) nu) := by
  intro u
  induction u with
  | Var z =>
    intro l1 l' y nu h hy
    obtain ⟨j, hj, rfl⟩ := to_nameless_var_inv h
    simp only [to_nameless, shift]
    cases h1 : index_of l1 z with
    | some j1 =>
      have := index_of_napp_some l1 l' z j1 h1
      rw [this] at hj; cases hj
      rw [index_of_napp_some l1 (.Cons y l') z j h1]
      have := (index_of_lt l1 z j h1).2
      simp; omega
    | none =>
      have hz : z ≠ y := hy z (by simp [free]) h1
      rw [index_of_napp_none l1 l' z h1] at hj
      rw [index_of_napp_none l1 (.Cons y l') z h1]
      cases h2 : index_of l' z with
      | none => rw [h2] at hj; cases hj
      | some j2 =>
        rw [h2] at hj; simp at hj; subst hj
        have h0 := (index_of_lt l' z j2 h2).1
        have hge : j2 + (namesLen l1 : Int) ≥ (namesLen l1 : Int) := by omega
        simp [index_of, Ne.symm hz, h2, hge]
        try omega
  | Lam w ty b ih =>
    intro l1 l' y nu h hy
    obtain ⟨nb, hb, rfl⟩ := to_nameless_lam_inv h
    have := ih (.Cons w l1) l' y nb hb (fun z hz hn => by
      simp only [index_of] at hn
      by_cases hw : w = z
      · simp [hw] at hn
      · simp only [hw, if_false] at hn
        cases hr : index_of l1 z with
        | none => exact hy z (mem_free_lam.2 ⟨hz, Ne.symm hw⟩) hr
        | some k => rw [hr] at hn; cases hn)
    simp only [to_nameless, napp] at this ⊢
    rw [this]
    simp [shift, namesLen]
  | App a b iha ihb =>
    intro l1 l' y nu h hy
    obtain ⟨na, nb, ha, hb, rfl⟩ := to_nameless_app_inv h
    have ha' := iha l1 l' y na ha fun z hz => hy z (mem_free_app.2 (Or.inl hz))
    have hb' := ihb l1 l' y nb hb fun z hz => hy z (mem_free_app.2 (Or.inr hz))
    simp [to_nameless, ha', hb', shift]
  | True => intro l1 l' y nu h _; simp only [to_nameless] at h; cases h; simp [to_nameless, shift]
  | False => intro l1 l' y nu h _; simp only [to_nameless] at h; cases h; simp [to_nameless, shift]
  | If c a b ihc iha ihb =>
    intro l1 l' y nu h hy
    obtain ⟨nc, na, nb, hc, ha, hb, rfl⟩ := to_nameless_if_inv h
    have hc' := ihc l1 l' y nc hc fun z hz => hy z (mem_free_if.2 (Or.inl hz))
    have ha' := iha l1 l' y na ha fun z hz => hy z (mem_free_if.2 (Or.inr (Or.inl hz)))
    have hb' := ihb l1 l' y nb hb fun z hz => hy z (mem_free_if.2 (Or.inr (Or.inr hz)))
    simp [to_nameless, hc', ha', hb', shift]

/-- A parallel substitution on nameless terms, and its passage under a binder. -/
def lift (ρ : Int → Term Int Anon) (j : Int) : Term Int Anon := if j ≤ 0 then .Var j else shift 1 0 (ρ (j - 1))

def napply (ρ : Int → Term Int Anon) : Term Int Anon → Term Int Anon
  | .Var j => ρ j
  | .Lam b ty body => .Lam b ty (napply (lift ρ) body)
  | .App a b => .App (napply ρ a) (napply ρ b)
  | .If c a b => .If (napply ρ c) (napply ρ a) (napply ρ b)
  | .True => .True
  | .False => .False

/-- `nsubst k s` as a parallel substitution. -/
def nsubstFun (k : Int) (s : Term Int Anon) (j : Int) : Term Int Anon :=
  if j = k then s else if j > k then .Var (j - 1) else .Var j

/-- Where the shift in `nsubst` matters: without it, this is false. -/
theorem lift_nsubstFun (k : Int) (s : Term Int Anon) (hk : 0 ≤ k) :
    lift (nsubstFun k s) = nsubstFun (k + 1) (shift 1 0 s) := by
  funext j
  simp only [lift, nsubstFun]
  by_cases h0 : j ≤ 0
  · rw [if_pos h0, if_neg (show ¬ j = k + 1 by omega), if_neg (show ¬ j > k + 1 by omega)]
  · rw [if_neg h0]
    by_cases h1 : j - 1 = k
    · rw [if_pos h1, if_pos (show j = k + 1 by omega)]
    · rw [if_neg h1, if_neg (show ¬ j = k + 1 by omega)]
      by_cases h2 : j - 1 > k
      · rw [if_pos h2, if_pos (show j > k + 1 by omega)]
        simp only [shift]
        rw [if_pos (show j - 1 - 1 ≥ 0 by omega)]
        congr 1; omega
      · rw [if_neg h2, if_neg (show ¬ j > k + 1 by omega)]
        simp only [shift]
        rw [if_pos (show j - 1 ≥ 0 by omega)]
        congr 1; omega

theorem napply_nsubst : ∀ (nt : Term Int Anon) (k : Int) (s : Term Int Anon), 0 ≤ k →
    napply (nsubstFun k s) nt = nsubst k s nt
  | .Var j, k, s, _ => by simp [napply, nsubstFun, nsubst]
  | .Lam b ty body, k, s, hk => by
    simp only [napply, nsubst]
    rw [lift_nsubstFun k s hk, napply_nsubst body (k + 1) (shift 1 0 s) (by omega)]
  | .App a b, k, s, hk => by simp [napply, nsubst, napply_nsubst a k s hk, napply_nsubst b k s hk]
  | .If c a b, k, s, hk => by
    simp [napply, nsubst, napply_nsubst c k s hk, napply_nsubst a k s hk, napply_nsubst b k s hk]
  | .True, _, _, _ => rfl
  | .False, _, _, _ => rfl

/-- Substitution commutes with the nameless form: where `σ` takes each free
variable of `t` to what `ρ` takes its index to, `subst_all σ t` converts to
`napply ρ` of `t`'s nameless form. -/
theorem to_nameless_subst_all : ∀ (t : Named) (σ : Subst) (l l' : Names) (ρ : Int → Term Int Anon)
    (nt : Term Int Anon), to_nameless l t = some nt →
    (∀ z, z ∈ free t → ∀ k, index_of l z = some k → to_nameless l' (apply_subst σ z) = some (ρ k)) →
    to_nameless l' (subst_all σ t) = some (napply ρ nt) := by
  intro t
  induction t with
  | Var z =>
    intro σ l l' ρ nt h hρ
    obtain ⟨j, hj, rfl⟩ := to_nameless_var_inv h
    simp only [subst_all, napply]
    exact hρ z (by simp [free]) j hj
  | Lam y ty b ih =>
    intro σ l l' ρ nt h hρ
    obtain ⟨nb, hb, rfl⟩ := to_nameless_lam_inv h
    simp only [subst_all, napply]
    have := ih (.Bind y (.Var (new_binder σ y b)) σ) (.Cons y l) (.Cons (new_binder σ y b) l') (lift ρ) nb hb
      (fun z hz k hk => by
        by_cases hyz : y = z
        · subst hyz
          simp only [index_of, if_true] at hk; cases hk
          simp [apply_subst, to_nameless, index_of, lift]
        · simp only [index_of, hyz, if_false] at hk
          cases hk0 : index_of l z with
          | none => rw [hk0] at hk; cases hk
          | some k0 =>
            rw [hk0] at hk; simp at hk; subst hk
            have h0 := (index_of_lt l z k0 hk0).1
            simp only [apply_subst, hyz, if_false]
            have hw := to_nameless_weaken (apply_subst σ z) .Nil l' (new_binder σ y b) (ρ k0)
              (hρ z (mem_free_lam.2 ⟨hz, Ne.symm hyz⟩) k0 hk0)
              (fun w hw _ e => new_binder_not_mem_apply σ y b z hz (Ne.symm hyz) (e ▸ hw))
            simp only [napp, namesLen] at hw
            rw [hw]
            have : ¬ k0 + 1 ≤ 0 := by omega
            simp [lift, this])
    simp only [to_nameless]
    rw [this]
  | App f a ihf iha =>
    intro σ l l' ρ nt h hρ
    obtain ⟨nf, na, hf, ha, rfl⟩ := to_nameless_app_inv h
    simp only [subst_all, napply, to_nameless]
    rw [ihf σ l l' ρ nf hf fun z hz => hρ z (mem_free_app.2 (Or.inl hz)),
      iha σ l l' ρ na ha fun z hz => hρ z (mem_free_app.2 (Or.inr hz))]
  | True => intro σ l l' ρ nt h _; simp only [to_nameless] at h; cases h; rfl
  | False => intro σ l l' ρ nt h _; simp only [to_nameless] at h; cases h; rfl
  | If c a b ihc iha ihb =>
    intro σ l l' ρ nt h hρ
    obtain ⟨nc, na, nb, hc, ha, hb, rfl⟩ := to_nameless_if_inv h
    simp only [subst_all, napply, to_nameless]
    rw [ihc σ l l' ρ nc hc fun z hz => hρ z (mem_free_if.2 (Or.inl hz)),
      iha σ l l' ρ na ha fun z hz => hρ z (mem_free_if.2 (Or.inr (Or.inl hz))),
      ihb σ l l' ρ nb hb fun z hz => hρ z (mem_free_if.2 (Or.inr (Or.inr hz)))]

/-- `alpha_laws::subst_nameless`: substitution commutes with the conversion. -/
theorem subst_nameless {x : String} {names : Names} {t s : Named} {nt ns : Term Int Anon}
    (ht : to_nameless (.Cons x names) t = some nt) (hs : to_nameless names s = some ns) :
    to_nameless names (subst x s t) = some (nsubst 0 ns nt) := by
  have h := to_nameless_subst_all t (.Bind x s .Id) (.Cons x names) names (nsubstFun 0 ns) nt ht (by
    intro z hz k hk
    by_cases hxz : x = z
    · subst hxz
      simp only [index_of, if_true] at hk; cases hk
      simpa [apply_subst, nsubstFun] using hs
    · simp only [index_of, hxz, if_false] at hk
      cases hk0 : index_of names z with
      | none => rw [hk0] at hk; cases hk
      | some k0 =>
        rw [hk0] at hk; simp at hk; subst hk
        have h0 := (index_of_lt names z k0 hk0).1
        have h1 : ¬ k0 + 1 = 0 := by omega
        have h2 : k0 + 1 > 0 := by omega
        simp [apply_subst, hxz, to_nameless, hk0, nsubstFun, h1, h2])
  rw [napply_nsubst nt 0 ns (by omega)] at h
  have e : subst x s t = subst_all (.Bind x s .Id) t := rfl
  rw [e]; exact h

theorem lift_var : lift (fun j => Term.Var j) = fun j => Term.Var j := by
  funext j
  simp only [lift]
  by_cases h : j ≤ 0
  · rw [if_pos h]
  · rw [if_neg h]; simp only [shift]; rw [if_pos (show j - 1 ≥ 0 by omega)]; congr 1; omega

theorem napply_var : ∀ (n : Term Int Anon), napply (fun j => Term.Var j) n = n
  | .Var _ => rfl
  | .Lam _ _ body => by simp only [napply]; rw [lift_var, napply_var body]
  | .App a b => by simp only [napply]; rw [napply_var a, napply_var b]
  | .If c a b => by simp only [napply]; rw [napply_var c, napply_var a, napply_var b]
  | .True => rfl
  | .False => rfl

/-- `alpha_laws::rename_binder`: a binder renamed to a name free nowhere in
the body converts to the same nameless term, under the new name. -/
theorem rename_binder {names : Names} {y z : String} {body : Named} {nb : Term Int Anon}
    (hb : to_nameless (.Cons y names) body = some nb) (hz : z ∉ free body) :
    to_nameless (.Cons z names) (subst_all (.Bind y (.Var z) .Id) body) = some nb := by
  have := to_nameless_subst_all body (.Bind y (.Var z) .Id) (.Cons y names) (.Cons z names) (fun j => .Var j) nb hb
    (by
      intro w hw k hk
      by_cases hyw : y = w
      · subst hyw
        simp only [index_of, if_true] at hk; cases hk
        simp [apply_subst, to_nameless, index_of]
      · simp only [index_of, hyw, if_false] at hk
        have hzw : ¬ z = w := fun e => hz (e ▸ hw)
        cases hk0 : index_of names w with
        | none => rw [hk0] at hk; cases hk
        | some k0 =>
          rw [hk0] at hk; simp at hk; subst hk
          simp [apply_subst, hyw, to_nameless, index_of, hzw, hk0])
  rw [napply_var] at this
  exact this

/-! #### Typing is invariant under alpha-equivalence -/

/-- The names a context declares, innermost first, and their types. -/
def ctxNames : Ctx → Names
  | .Empty => .Nil
  | .Bind x _ rest => .Cons x (ctxNames rest)

def ctxTys : Ctx → List Ty
  | .Empty => []
  | .Bind _ ty rest => ty :: ctxTys rest

/-- Typing of nameless terms, under the types of the binders in scope. -/
def ntypeof (tys : List Ty) : Term Int Anon → Option Ty
  | .Var k => if k < 0 then none else tys[k.toNat]?
  | .Lam _ ty b => match ntypeof (ty :: tys) b with
    | some ty2 => some (.Arrow ty ty2)
    | none => none
  | .App a b => match ntypeof tys a, ntypeof tys b with
    | some (.Arrow p r), some q => if p = q then some r else none
    | _, _ => none
  | .If c a b => match ntypeof tys c, ntypeof tys a, ntypeof tys b with
    | some .Boolean, some ty2, some ty3 => if ty2 = ty3 then some ty2 else none
    | _, _, _ => none
  | .True => some .Boolean
  | .False => some .Boolean

theorem lookup_ctxTys : ∀ (ctx : Ctx) (x : String) (k : Int), index_of (ctxNames ctx) x = some k →
    lookup ctx x = (ctxTys ctx)[k.toNat]?
  | .Empty, x, k, h => by simp [ctxNames, index_of] at h
  | .Bind y ty rest, x, k, h => by
    simp only [ctxNames, index_of] at h
    simp only [lookup, ctxTys]
    by_cases hyx : y = x
    · simp only [hyx, if_true] at h ⊢; cases h; simp
    · simp only [hyx, if_false] at h ⊢
      cases hk : index_of (ctxNames rest) x with
      | none => rw [hk] at h; cases h
      | some k0 =>
        rw [hk] at h; simp at h; subst h
        have h0 := (index_of_lt _ x k0 hk).1
        rw [lookup_ctxTys rest x k0 hk]
        have : (k0 + 1).toNat = k0.toNat + 1 := by omega
        simp [this]

/-- A term's type is its nameless form's. -/
theorem typeof_nameless : ∀ (t : Named) (ctx : Ctx) (nt : Term Int Anon), to_nameless (ctxNames ctx) t = some nt →
    typeof ctx t = ntypeof (ctxTys ctx) nt := by
  intro t
  induction t with
  | Var x =>
    intro ctx nt h
    obtain ⟨k, hk, rfl⟩ := to_nameless_var_inv h
    have h0 := (index_of_lt _ x k hk).1
    simp only [typeof, ntypeof]
    rw [if_neg (show ¬ k < 0 by omega)]
    exact lookup_ctxTys ctx x k hk
  | Lam y ty b ih =>
    intro ctx nt h
    obtain ⟨nb, hb, rfl⟩ := to_nameless_lam_inv h
    have := ih (.Bind y ty ctx) nb hb
    simp only [typeof, ntypeof, ctxTys] at this ⊢
    rw [this]
    cases ntypeof (ty :: ctxTys ctx) nb <;> rfl
  | App f a ihf iha =>
    intro ctx nt h
    obtain ⟨nf, na, hf, ha, rfl⟩ := to_nameless_app_inv h
    simp only [typeof, ntypeof]
    rw [ihf ctx nf hf, iha ctx na ha]
    rcases ntypeof (ctxTys ctx) nf with _ | (_ | ⟨p, r⟩) <;> cases ntypeof (ctxTys ctx) na <;> rfl
  | True => intro ctx nt h; simp only [to_nameless] at h; cases h; rfl
  | False => intro ctx nt h; simp only [to_nameless] at h; cases h; rfl
  | If c a b ihc iha ihb =>
    intro ctx nt h
    obtain ⟨nc, na, nb, hc, ha, hb, rfl⟩ := to_nameless_if_inv h
    simp only [typeof, ntypeof]
    rw [ihc ctx nc hc, iha ctx na ha, ihb ctx nb hb]
    rcases ntypeof (ctxTys ctx) nc with _ | (_ | ⟨p, r⟩) <;> cases ntypeof (ctxTys ctx) na <;>
      cases ntypeof (ctxTys ctx) nb <;> rfl

/-- `alpha_laws::typed_alpha`: alpha-equivalent closed terms have the same type. -/
theorem typed_alpha {t t2 : Named} {n : Term Int Anon} (h1 : to_nameless .Nil t = some n)
    (h2 : to_nameless .Nil t2 = some n) : typeof .Empty t = typeof .Empty t2 := by
  rw [typeof_nameless t .Empty n h1, typeof_nameless t2 .Empty n h2]

/-! ## One layer of a term

`Term` is the fixpoint of `TermF`, and `size` is the fold of `size_alg`. -/

/-- The layer of a term, with `f` at each child. -/
def layer {E : Type} (f : Named → E) : Named → TermF String String E
  | .Var x => .Var x
  | .Lam x ty b => .Lam x ty (f b)
  | .App a b => .App (f a) (f b)
  | .True => .True
  | .False => .False
  | .If c a b => .If (f c) (f a) (f b)

theorem size_fold (t : Named) : size t = size_alg String String (layer size t) := by
  cases t <;> simp [size, size_alg, layer]

theorem map_layer_id {V B E : Type} [Inhabited V] [Inhabited B] [Inhabited E] (l : TermF V B E) :
    map_layer V B E E l id = l := by
  cases l <;> simp [map_layer]

/-! ## The procedures of the spec

Each `impl` binds a procedure's laws to the proofs above, for every value of
its parameters. -/

impl substitution_laws_proved: substitution_laws for (x : String) (s t : Named) { x := x, s := s, t := t } by
  intro x s t _
  simp only [fren_spec]
  refine ⟨fun h => subst_unused h, ?_, free_subst x s t⟩
  simp

impl context_lemmas_proved: context_lemmas for (ctx ctx2 : Ctx) (t : Named) (x : String) (ty ty1 : Ty) (s : Named) {
  ctx := ctx, ctx2 := ctx2, t := t, x := x, ty := ty, ty1 := ty1, s := s
} by
  intro ctx ctx2 t x ty ty1 s _
  simp only [fren_spec]
  refine ⟨fun h => typeof_ext t ctx ctx2 h, fun h => ?_, fun h => typeof_subst h.1 h.2⟩
  rw [typeof_weaken ty1 h.2]; exact h.1

impl evaluators_proved: evaluators for (t u v w : Named) (n m : Fuel) {
  t := t, u := u, v := v, w := w, n := n, m := m
} by
  intro t u v w n m _
  simp only [fren_spec]
  exact ⟨fun h => eval_value n t v h, fun h => eval_mono n t v h, fun h => normalize_mono n h,
    fun h => step_eval n t u v h.1 h.2, fun h => eval_normalize m n t v w h.1 h.2⟩

impl type_safety_proved: type_safety for (ctx : Ctx) (t u : Named) (ty : Ty) (n : Fuel) {
  ctx := ctx, t := t, u := u, ty := ty, n := n
} by
  intro ctx t u ty n _
  simp only [fren_spec]
  refine ⟨fun h => ?_, fun h => preservation t ctx ty u h.1 h.2, fun h => ?_,
    fun h => eval_preservation n ctx t u ty h.1 h.2⟩
  · rcases progress t ty h with hv | ⟨u, hu⟩
    · exact Or.inl hv
    · right; rw [hu]
  · obtain ⟨hty, hv | ⟨u, hu⟩⟩ := safety n t ty h
    · exact ⟨hty, Or.inl hv⟩
    · exact ⟨hty, Or.inr (by rw [hu])⟩

impl nameless_round_trip_proved: nameless_round_trip for (t : Named) (nt : Term Int Anon) { t := t, nt := nt } by
  intro t nt _
  simp only [fren_spec]
  refine ⟨fun h => to_nameless_to_named nt 0 t h, fun h => ?_, fun h => ?_⟩
  · obtain ⟨n, hn⟩ := to_nameless_some t .Nil fun x hx => by rw [of_decide_eq_true h] at hx; simp at hx
    simp [hn]
  · obtain ⟨t', ht'⟩ := to_named_some nt .Nil .Nil t rfl h.2
    simp [ht']

impl alpha_laws_proved: alpha_laws for (names : Names) (t : Named) (nt : Term Int Anon) (s : Named)
    (ns : Term Int Anon) (x y z : String) (ty : Ty) (body t2 : Named) {
  names := names, t := t, nt := nt, s := s, ns := ns, x := x, y := y, z := z, ty := ty, body := body, t2 := t2
} by
  intro names t nt s ns x y z ty body t2 _
  simp only [fren_spec]
  refine ⟨fun h => ?_, fun h => subst_nameless h.1 h.2, fun h => ?_⟩
  · obtain ⟨⟨hsome, hz⟩, _⟩ := h
    apply (@decide_eq_true_iff _ _).2
    cases hb : to_nameless (Names.Cons y names) body with
    | none => simp [hb] at hsome
    | some nb => simp [rename_binder hb hz]
  · have h := (@decide_eq_true_iff _ _).1 h
    obtain ⟨hsome, he⟩ := h
    cases hv : to_nameless .Nil t with
    | none => simp [hv] at hsome
    | some n =>
      have ht2 : to_nameless .Nil t2 = some n := by first | (rw [← he]; exact hv) | exact he.symm
      exact typed_alpha hv ht2

impl layer_laws_proved: layer_laws for (l : TermF String String Int) (t1 t2 : Named) { l := l, t1 := t1, t2 := t2 } by
  intro l t1 t2 _
  simp only [fren_spec]

end Stlc
