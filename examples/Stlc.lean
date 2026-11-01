-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# The simply typed lambda calculus in Lean

The theorems of `stlc.fren` that need induction, proved over its generated
definitions and bound to its procedures with `impl`: the context lemmas and
the substitution lemma, preservation, progress and type safety, the
soundness and completeness of the type checker for the typing relation and
of the evaluator for the reduction relation, the agreement of the two
evaluators, and the laws of substitution, of the nameless form and of the
concrete syntax. The last section ties the knot of the one-layer algebras:
each recursion over terms is the fold of its algebra.
-/

open Fren.Lang

#fren_md "stlc.fren"

-- The solver's checks, as `fren check` runs them; the laws set to random
-- testing are run by `fren check`.
#fren_check

namespace Stlc
open Fren.Generated stlc

abbrev Named := Term String String

/-! ## Free variables and fresh names -/

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

theorem length_le_range_names : ∀ (sub : Subst) (s : Named) (x : String),
    InRange sub s → x ∈ free s → x.length ≤ (range_names sub).length := by
  intro sub
  induction sub with
  | Id => intro s x h; exact absurd h id
  | Bind y u rest ih =>
    intro s x h hx
    simp only [range_names, String.length_append]
    rcases h with rfl | h
    · have := length_le_all_names s x hx; omega
    · have := ih s x h hx; omega

theorem length_fresh (sub : Subst) (body : Named) :
    (fresh sub body).length = (range_names sub).length + (all_names body).length + 1 := by
  simp only [fresh, String.length_append, Fren.Str.lit]; rfl

/-- The fresh name is free neither in the body nor in what `sub` substitutes. -/
theorem fresh_not_mem (sub : Subst) (body : Named) :
    fresh sub body ∉ free body ∧ ∀ s, InRange sub s → fresh sub body ∉ free s := by
  constructor
  · intro h
    have := length_le_all_names body _ h
    rw [length_fresh] at this; omega
  · intro s hs h
    have := length_le_range_names sub s _ hs h
    rw [length_fresh] at this; omega

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

/-! ## Typing -/

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

/-- Typing depends on the context only at the free variables. -/
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

/-- Weakening: a binding of a name that is not free changes no type. -/
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

/-- The substitution lemma. -/
theorem typeof_subst {ctx : Ctx} {x : String} {s t : Named} {tx ty : Ty} (ht : typeof (.Bind x tx ctx) t = some ty)
    (hs : typeof ctx s = some tx) : typeof ctx (subst x s t) = some ty := by
  apply typeof_subst_all t _ _ _ _ ht
  intro z _ τ hl
  by_cases hz : x = z
  · subst hz; rw [lookup_bind_same] at hl; cases hl; simpa [apply_subst] using hs
  · rw [lookup_bind_other _ hz] at hl; simpa [apply_subst, hz, typeof] using hl

/-! ## Substitution -/

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

theorem free_subst (x : String) (s t : Named) : free (subst x s t) ⊆ (free t \ {x}) ∪ free s := by
  intro z hz
  obtain ⟨w, hw, hz⟩ := free_subst_all t _ z hz
  by_cases hwx : x = w
  · subst hwx; simp only [apply_subst, if_true] at hz; simp [hz]
  · simp only [apply_subst, hwx, if_false, mem_free_var] at hz; subst hz; simp [hw, Ne.symm hwx]

/-! ## Values and steps -/

theorem value_iff (t : Named) :
    value? String String t = true ↔ (∃ x ty b, t = .Lam x ty b) ∨ t = .True ∨ t = .False := by
  cases t <;> simp [value?]

theorem step_value {t : Named} (h : value? String String t = true) : step t = none := by
  rw [value_iff] at h
  rcases h with ⟨x, ty, b, rfl⟩ | rfl | rfl <;> simp [step]

theorem step_var (x : String) : step (Term.Var x : Named) = none := by simp [step]

theorem not_value_cases {t : Named} (h : ¬ value? String String t = true) :
    (∃ x, t = .Var x) ∨ (∃ a b, t = .App a b) ∨ (∃ c a b, t = .If c a b) := by
  cases t <;> simp_all [value?]

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

/-- A step of an application, by the shape of its parts. -/
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

/-- A step of a conditional, by the shape of its condition. -/
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

/-- Canonical forms. -/
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

/-- Preservation: a step keeps the type. -/
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

/-- Progress: a well-typed closed term is a value or steps. -/
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

/-- Type safety: however far a well-typed closed term is reduced, it has its
type and is a value or steps. -/
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

/-! ## The type checker and the typing relation -/

theorem mem_types {typing : Fren.FinSet (Judgment × Ty)} {ctx : Ctx} {t : Named} {ty : Ty} :
    ty ∈ types typing ctx t ↔ (judgment ctx t, ty) ∈ typing := by
  simp [types]

theorem judgment_eq (ctx : Ctx) (t : Named) : judgment ctx t = ⟨ctx, t⟩ := rfl

/-- `typing_rule?`, case by case. -/
theorem typing_rule_iff (typing : Fren.FinSet (Judgment × Ty)) (ctx : Ctx) (t : Named) (ty : Ty) :
    typing_rule? typing ctx t ty = true ↔ match t with
      | .Var x => lookup ctx x = some ty
      | .Lam x ty1 t2 => match ty with
        | .Arrow p ty2 => p = ty1 ∧ (judgment (.Bind x ty1 ctx) t2, ty2) ∈ typing
        | .Boolean => False
      | .App t1 t2 => ∃ ty11, (judgment ctx t2, ty11) ∈ typing ∧ (judgment ctx t1, .Arrow ty11 ty) ∈ typing
      | .If t1 t2 t3 =>
        (judgment ctx t1, .Boolean) ∈ typing ∧ (judgment ctx t2, ty) ∈ typing ∧ (judgment ctx t3, ty) ∈ typing
      | .True => ty = .Boolean
      | .False => ty = .Boolean := by
  cases t <;> simp only [typing_rule?, decide_eq_true_eq, fren_spec, mem_types, and_assoc] <;> try simp
  cases ty <;> simp

theorem derivation_iff (typing : Fren.FinSet (Judgment × Ty)) :
    typing_derivation? typing = true ↔
      ∀ ctx t ty, (judgment ctx t, ty) ∈ typing → typing_rule? typing ctx t ty = true := by
  simp only [typing_derivation?, decide_eq_true_eq, Fren.FinSet.mem_domain, Fren.FinSet.mem_image,
    Fren.FinSet.mem_singleton]
  constructor
  · intro h ctx t ty hm
    exact h ⟨ctx, t⟩ ⟨ty, hm⟩ ty ⟨_, rfl, hm⟩
  · rintro h ⟨ctx, t⟩ _ ty ⟨_, rfl, hm⟩
    exact h ctx t ty hm

/-- Completeness: the checker agrees with every derivation. -/
theorem checker_complete : ∀ (t : Named) (typing : Fren.FinSet (Judgment × Ty)) (ctx : Ctx) (ty : Ty),
    typing_derivation? typing = true → (judgment ctx t, ty) ∈ typing → typeof ctx t = some ty := by
  intro t
  induction t with
  | Var x =>
    intro typing ctx ty hd hm
    have := (typing_rule_iff ..).1 ((derivation_iff _).1 hd _ _ _ hm)
    simpa [typeof] using this
  | Lam y ty1 b ih =>
    intro typing ctx ty hd hm
    have h := (typing_rule_iff ..).1 ((derivation_iff _).1 hd _ _ _ hm)
    cases ty with
    | Boolean => exact absurd h id
    | Arrow p ty2 =>
      obtain ⟨rfl, h2⟩ := h
      exact typeof_lam (ih typing _ _ hd h2)
  | App f a ihf iha =>
    intro typing ctx ty hd hm
    obtain ⟨p, h2, h1⟩ := (typing_rule_iff ..).1 ((derivation_iff _).1 hd _ _ _ hm)
    exact typeof_app (ihf typing _ _ hd h1) (iha typing _ _ hd h2)
  | True =>
    intro typing ctx ty hd hm
    have := (typing_rule_iff ..).1 ((derivation_iff _).1 hd _ _ _ hm)
    simp [typeof, this]
  | False =>
    intro typing ctx ty hd hm
    have := (typing_rule_iff ..).1 ((derivation_iff _).1 hd _ _ _ hm)
    simp [typeof, this]
  | If c a b ihc iha ihb =>
    intro typing ctx ty hd hm
    obtain ⟨hc, ha, hb⟩ := (typing_rule_iff ..).1 ((derivation_iff _).1 hd _ _ _ hm)
    exact typeof_if (ihc typing _ _ hd hc) (iha typing _ _ hd ha) (ihb typing _ _ hd hb)

/-- A rule stays justified in a larger relation. -/
theorem typing_rule_mono {r s : Fren.FinSet (Judgment × Ty)} (h : ∀ p, p ∈ r → p ∈ s) (ctx : Ctx) (t : Named)
    (ty : Ty) (hr : typing_rule? r ctx t ty = true) : typing_rule? s ctx t ty = true := by
  rw [typing_rule_iff] at *
  cases t <;> simp only at *
  · exact hr
  · cases ty with
    | Boolean => exact hr
    | Arrow p ty2 => exact ⟨hr.1, h _ hr.2⟩
  · obtain ⟨p, h1, h2⟩ := hr; exact ⟨p, h _ h1, h _ h2⟩
  · exact hr
  · exact hr
  · exact ⟨h _ hr.1, h _ hr.2.1, h _ hr.2.2⟩

theorem mem_typing_of {ctx : Ctx} {t : Named} {ty : Ty} (h : typeof ctx t = some ty) :
    (judgment ctx t, ty) ∈ typing_of ctx t := by
  cases t <;> simp [typing_of, h, judgment_eq]

/-- What the checker's derivation holds, under a judgment with a type: that
judgment, or a judgment of a subterm's derivation. -/
theorem mem_typing_of_iff {ctx : Ctx} {t : Named} {ty : Ty} (h : typeof ctx t = some ty) (p : Judgment × Ty) :
    p ∈ typing_of ctx t ↔ p = (judgment ctx t, ty) ∨ match t with
      | .Lam x ty1 b => p ∈ typing_of (.Bind x ty1 ctx) b
      | .App f a => p ∈ typing_of ctx f ∨ p ∈ typing_of ctx a
      | .If c a b => p ∈ typing_of ctx c ∨ p ∈ typing_of ctx a ∨ p ∈ typing_of ctx b
      | _ => False := by
  cases t <;> simp [typing_of, h, judgment_eq, or_assoc]

/-- Every judgment that the checker's derivation holds is justified in it. -/
theorem typing_of_derivation : ∀ (t : Named) (ctx : Ctx), typing_derivation? (typing_of ctx t) = true := by
  intro t
  induction t with
  | Var x =>
    intro ctx; rw [derivation_iff]; intro c u ty h
    cases hty : typeof ctx (Term.Var x) with
    | none => simp [typing_of, hty] at h
    | some ty' =>
      rw [mem_typing_of_iff hty] at h
      simp only at h
      rcases h with h | h
      · cases h; rw [typing_rule_iff]; simpa [typeof] using hty
      · exact absurd h id
  | True =>
    intro ctx; rw [derivation_iff]; intro c u ty h
    cases hty : typeof ctx (Term.True : Named) with
    | none => simp [typing_of, hty] at h
    | some ty' =>
      rw [mem_typing_of_iff hty] at h
      simp only at h
      rcases h with h | h
      · cases h; rw [typing_rule_iff]; simpa [typeof] using hty.symm
      · exact absurd h id
  | False =>
    intro ctx; rw [derivation_iff]; intro c u ty h
    cases hty : typeof ctx (Term.False : Named) with
    | none => simp [typing_of, hty] at h
    | some ty' =>
      rw [mem_typing_of_iff hty] at h
      simp only at h
      rcases h with h | h
      · cases h; rw [typing_rule_iff]; simpa [typeof] using hty.symm
      · exact absurd h id
  | Lam y ty1 b ih =>
    intro ctx; rw [derivation_iff]; intro c u ty h
    cases hty : typeof ctx (Term.Lam y ty1 b) with
    | none => simp [typing_of, hty] at h
    | some ty' =>
      have sub : ∀ p, p ∈ typing_of (.Bind y ty1 ctx) b → p ∈ typing_of ctx (Term.Lam y ty1 b) := by
        intro p hp; rw [mem_typing_of_iff hty]; exact Or.inr hp
      rw [mem_typing_of_iff hty] at h
      simp only at h
      rcases h with h | h
      · cases h
        obtain ⟨ty2, hb, rfl⟩ := typeof_lam_inv hty
        rw [typing_rule_iff]
        exact ⟨rfl, sub _ (mem_typing_of hb)⟩
      · exact typing_rule_mono sub _ _ _ ((derivation_iff _).1 (ih _) _ _ _ h)
  | App f a ihf iha =>
    intro ctx; rw [derivation_iff]; intro c u ty h
    cases hty : typeof ctx (Term.App f a) with
    | none => simp [typing_of, hty] at h
    | some ty' =>
      have subf : ∀ p, p ∈ typing_of ctx f → p ∈ typing_of ctx (Term.App f a) := by
        intro p hp; rw [mem_typing_of_iff hty]; exact Or.inr (Or.inl hp)
      have suba : ∀ p, p ∈ typing_of ctx a → p ∈ typing_of ctx (Term.App f a) := by
        intro p hp; rw [mem_typing_of_iff hty]; exact Or.inr (Or.inr hp)
      rw [mem_typing_of_iff hty] at h
      simp only at h
      rcases h with h | h | h
      · cases h
        obtain ⟨p, hf, ha⟩ := typeof_app_inv hty
        rw [typing_rule_iff]
        exact ⟨p, suba _ (mem_typing_of ha), subf _ (mem_typing_of hf)⟩
      · exact typing_rule_mono subf _ _ _ ((derivation_iff _).1 (ihf _) _ _ _ h)
      · exact typing_rule_mono suba _ _ _ ((derivation_iff _).1 (iha _) _ _ _ h)
  | If c a b ihc iha ihb =>
    intro ctx; rw [derivation_iff]; intro c' u ty h
    cases hty : typeof ctx (Term.If c a b) with
    | none => simp [typing_of, hty] at h
    | some ty' =>
      have subc : ∀ p, p ∈ typing_of ctx c → p ∈ typing_of ctx (Term.If c a b) := by
        intro p hp; rw [mem_typing_of_iff hty]; exact Or.inr (Or.inl hp)
      have suba : ∀ p, p ∈ typing_of ctx a → p ∈ typing_of ctx (Term.If c a b) := by
        intro p hp; rw [mem_typing_of_iff hty]; exact Or.inr (Or.inr (Or.inl hp))
      have subb : ∀ p, p ∈ typing_of ctx b → p ∈ typing_of ctx (Term.If c a b) := by
        intro p hp; rw [mem_typing_of_iff hty]; exact Or.inr (Or.inr (Or.inr hp))
      rw [mem_typing_of_iff hty] at h
      simp only at h
      rcases h with h | h | h | h
      · cases h
        obtain ⟨hc, ha, hb⟩ := typeof_if_inv hty
        rw [typing_rule_iff]
        exact ⟨subc _ (mem_typing_of hc), suba _ (mem_typing_of ha), subb _ (mem_typing_of hb)⟩
      · exact typing_rule_mono subc _ _ _ ((derivation_iff _).1 (ihc _) _ _ _ h)
      · exact typing_rule_mono suba _ _ _ ((derivation_iff _).1 (iha _) _ _ _ h)
      · exact typing_rule_mono subb _ _ _ ((derivation_iff _).1 (ihb _) _ _ _ h)

/-! ## The evaluator and the reduction relation -/

theorem red_derivation_iff (red : Fren.FinSet (Named × Named)) :
    reduction_derivation? red = true ↔ ∀ t u, (t, u) ∈ red → reduction_rule? red t u = true := by
  simp only [reduction_derivation?, decide_eq_true_eq, Fren.FinSet.mem_domain, Fren.FinSet.mem_image,
    Fren.FinSet.mem_singleton]
  constructor
  · intro h t u hm
    exact h t ⟨u, hm⟩ u ⟨_, rfl, hm⟩
  · rintro h t _ u ⟨_, rfl, hm⟩
    exact h _ u hm

/-- Unfolds a reduction rule applied to constructors: the selectors of the generated
definitions, then `value?` on constructors, and the Boolean algebra left behind. -/
macro "rule_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  (simp only [Term.App.x0, Term.App.x1, Term.Lam.x0, Term.Lam.x1, Term.Lam.x2, Term.If.x0, Term.If.x1, Term.If.x2,
      true_and, and_true, and_self, if_true, if_false, false_and, and_false, or_false, false_or, true_or, or_true,
      Term.App.injEq, Term.Lam.injEq, Term.If.injEq, reduceCtorEq, not_false_eq_true, not_true_eq_false,
      Bool.false_eq_true, Bool.true_eq_false, $ls,*] $[$loc:location]?
   try simp only [value?, decide_eq_true_eq, true_and, and_true, and_self, if_true, if_false, false_and, and_false,
      or_false, false_or, true_or, or_true, not_false_eq_true, not_true_eq_false, Bool.false_eq_true,
      Bool.true_eq_false] $[$loc:location]?))

/-- `reduction_rule?` at an application: the three rules that can justify it. -/
theorem rule_app_elim {red : Fren.FinSet (Named × Named)} {t1 t2 u : Named}
    (h : reduction_rule? red (Term.App t1 t2) u = true) :
    (∃ x ty b, t1 = Term.Lam x ty b ∧ value? String String t2 = true ∧ u = subst x t2 b) ∨
    (∃ u1, u = Term.App u1 t2 ∧ ¬ value? String String t1 = true ∧ (t1, u1) ∈ red) ∨
    (∃ u2, u = Term.App t1 u2 ∧ value? String String t1 = true ∧
      ¬ (∃ x ty b, t1 = Term.Lam x ty b ∧ value? String String t2 = true) ∧ (t2, u2) ∈ red) := by
  have h := (@decide_eq_true_iff _ _).1 h
  by_cases hv : value? String String t2 = true
  all_goals cases t1 <;> cases u <;> rule_simp [hv] at h
  all_goals first
    | exact h.elim
    | exact Or.inl ⟨_, _, _, rfl, hv, h⟩
    | (obtain ⟨rfl, hm⟩ := h; exact Or.inr (Or.inl ⟨_, rfl, by simp [value?], hm⟩))
    | (obtain ⟨rfl, hm⟩ := h
       exact Or.inr (Or.inr ⟨_, rfl, by simp [value?], (fun ⟨_, _, _, _, v⟩ => hv v), hm⟩))
    | (obtain ⟨rfl, hm⟩ := h
       exact Or.inr (Or.inr ⟨_, rfl, by simp [value?], (fun ⟨_, _, _, e, _⟩ => nomatch e), hm⟩))

/-- `reduction_rule?` at a conditional: the three rules that can justify it. -/
theorem rule_if_elim {red : Fren.FinSet (Named × Named)} {c a b u : Named}
    (h : reduction_rule? red (Term.If c a b) u = true) :
    (c = .True ∧ u = a) ∨ (c = .False ∧ u = b) ∨
    (c ≠ .True ∧ c ≠ .False ∧ ∃ c', u = Term.If c' a b ∧ (c, c') ∈ red) := by
  have h := (@decide_eq_true_iff _ _).1 h
  cases c <;> cases u <;> rule_simp [] at h
  all_goals first
    | exact h.elim
    | exact Or.inl ⟨rfl, h⟩
    | exact Or.inr (Or.inl ⟨rfl, h⟩)
    | (obtain ⟨⟨rfl, rfl⟩, hm⟩ := h; exact Or.inr (Or.inr ⟨nofun, nofun, _, rfl, hm⟩))

/-- No rule reduces a value. -/
theorem rule_value_elim {red : Fren.FinSet (Named × Named)} {t u : Named} (hv : value? String String t = true)
    (h : reduction_rule? red t u = true) : False := by
  have h := (@decide_eq_true_iff _ _).1 h
  rcases (value_iff t).1 hv with ⟨x, ty, b, rfl⟩ | rfl | rfl <;> rule_simp [] at h

/-- No rule reduces a variable. -/
theorem rule_var_elim {red : Fren.FinSet (Named × Named)} {x : String} {u : Named}
    (h : reduction_rule? red (Term.Var x) u = true) : False := by
  have h := (@decide_eq_true_iff _ _).1 h
  rule_simp [] at h

theorem rule_beta (red : Fren.FinSet (Named × Named)) {x : String} {ty : Ty} {b v : Named}
    (hv : value? String String v = true) : reduction_rule? red (Term.App (Term.Lam x ty b) v) (subst x v b) = true := by
  apply (@decide_eq_true_iff _ _).2
  rule_simp [hv]

theorem rule_app_left {red : Fren.FinSet (Named × Named)} {t1 t2 u1 : Named} (h : ¬ value? String String t1 = true)
    (hm : (t1, u1) ∈ red) : reduction_rule? red (Term.App t1 t2) (Term.App u1 t2) = true := by
  apply (@decide_eq_true_iff _ _).2
  rcases not_value_cases h with ⟨x, rfl⟩ | ⟨a, b, rfl⟩ | ⟨c, a, b, rfl⟩ <;> rule_simp [] <;> exact hm

theorem rule_app_right {red : Fren.FinSet (Named × Named)} {t1 t2 u2 : Named} (h1 : value? String String t1 = true)
    (h2 : ¬ (∃ x ty b, t1 = Term.Lam x ty b ∧ value? String String t2 = true)) (hm : (t2, u2) ∈ red) :
    reduction_rule? red (Term.App t1 t2) (Term.App t1 u2) = true := by
  apply (@decide_eq_true_iff _ _).2
  rcases (value_iff t1).1 h1 with ⟨x, ty, b, rfl⟩ | rfl | rfl
  · have nv : ¬ value? String String t2 = true := fun v => h2 ⟨x, ty, b, rfl, v⟩
    rule_simp [nv]; exact hm
  all_goals rule_simp []; exact hm

theorem rule_if_true (red : Fren.FinSet (Named × Named)) (a b : Named) :
    reduction_rule? red (Term.If Term.True a b) a = true := by
  apply (@decide_eq_true_iff _ _).2
  rule_simp []

theorem rule_if_false (red : Fren.FinSet (Named × Named)) (a b : Named) :
    reduction_rule? red (Term.If Term.False a b) b = true := by
  apply (@decide_eq_true_iff _ _).2
  rule_simp []

theorem rule_if_cong {red : Fren.FinSet (Named × Named)} {c a b c' : Named} (e1 : c ≠ .True) (e2 : c ≠ .False)
    (hm : (c, c') ∈ red) : reduction_rule? red (Term.If c a b) (Term.If c' a b) = true := by
  apply (@decide_eq_true_iff _ _).2
  cases c
  case True => exact absurd rfl e1
  case False => exact absurd rfl e2
  all_goals rule_simp []; exact hm

/-- Completeness: the evaluator takes every step of every derivation. -/
theorem step_complete : ∀ (t : Named) (red : Fren.FinSet (Named × Named)) (u : Named),
    reduction_derivation? red = true → (t, u) ∈ red → step t = some u := by
  intro t
  induction t with
  | Var x => intro red u hd hm; exact (rule_var_elim ((red_derivation_iff _).1 hd _ _ hm)).elim
  | Lam x ty b _ =>
    intro red u hd hm; exact (rule_value_elim (by simp [value?]) ((red_derivation_iff _).1 hd _ _ hm)).elim
  | True => intro red u hd hm; exact (rule_value_elim (by simp [value?]) ((red_derivation_iff _).1 hd _ _ hm)).elim
  | False => intro red u hd hm; exact (rule_value_elim (by simp [value?]) ((red_derivation_iff _).1 hd _ _ hm)).elim
  | App t1 t2 ih1 ih2 =>
    intro red u hd hm
    rcases rule_app_elim ((red_derivation_iff _).1 hd _ _ hm) with
      ⟨x, ty, b, rfl, hv, rfl⟩ | ⟨u1, rfl, nv1, h1⟩ | ⟨u2, rfl, v1, _, h2⟩
    · exact step_app_beta hv
    · exact step_app_left_some nv1 (ih1 red u1 hd h1)
    · have hs := ih2 red u2 hd h2
      exact step_app_right_some v1 (fun v => by rw [step_value v] at hs; cases hs) hs
  | If c a b ihc _ _ =>
    intro red u hd hm
    rcases rule_if_elim ((red_derivation_iff _).1 hd _ _ hm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e1, e2, c', rfl, hc⟩
    · simp [step]
    · simp [step]
    · exact step_if_some e1 e2 (ihc red c' hd hc)

/-- A rule stays justified in a larger relation. -/
theorem reduction_rule_mono {r s : Fren.FinSet (Named × Named)} (h : ∀ p, p ∈ r → p ∈ s) (t u : Named)
    (hr : reduction_rule? r t u = true) : reduction_rule? s t u = true := by
  cases t with
  | Var x => exact (rule_var_elim hr).elim
  | Lam x ty b => exact (rule_value_elim (by simp [value?]) hr).elim
  | True => exact (rule_value_elim (by simp [value?]) hr).elim
  | False => exact (rule_value_elim (by simp [value?]) hr).elim
  | App t1 t2 =>
    rcases rule_app_elim hr with ⟨x, ty, b, rfl, hv, rfl⟩ | ⟨u1, rfl, nv1, h1⟩ | ⟨u2, rfl, v1, nb, h2⟩
    · exact rule_beta s hv
    · exact rule_app_left nv1 (h _ h1)
    · exact rule_app_right v1 nb (h _ h2)
  | If c a b =>
    rcases rule_if_elim hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e1, e2, c', rfl, hc⟩
    · exact rule_if_true s _ _
    · exact rule_if_false s _ _
    · exact rule_if_cong e1 e2 (h _ hc)

/-- What the evaluator's derivation holds: the step, and the derivation of
the part that steps. -/
theorem mem_step_derivation_iff {t u : Named} (hs : step t = some u) (p : Named × Named) :
    p ∈ step_derivation t ↔ p = (t, u) ∨ match t with
      | .App t1 t2 =>
        if ¬ value? String String t1 = true then p ∈ step_derivation t1
        else if ¬ value? String String t2 = true then p ∈ step_derivation t2 else False
      | .If c _ _ => if c = .True ∨ c = .False then False else p ∈ step_derivation c
      | _ => False := by
  cases t with
  | App t1 t2 =>
    simp only [step_derivation, hs]
    cases h1 : value? String String t1 <;> cases h2 : value? String String t2 <;> simp
  | If c a b => cases c <;> simp [step_derivation, hs]
  | _ => simp [step_derivation, hs]

theorem mem_step_derivation_self {t u : Named} (hs : step t = some u) : (t, u) ∈ step_derivation t :=
  (mem_step_derivation_iff hs _).2 (Or.inl rfl)

/-- Soundness: the evaluator's derivation of a step is a derivation. -/
theorem step_sound : ∀ (t : Named) (u : Named), step t = some u → reduction_derivation? (step_derivation t) = true := by
  intro t
  induction t with
  | Var x => intro u hs; simp [step] at hs
  | Lam x ty b _ => intro u hs; simp [step] at hs
  | True => intro u hs; simp [step] at hs
  | False => intro u hs; simp [step] at hs
  | App t1 t2 ih1 ih2 =>
    intro u hs
    rw [red_derivation_iff]
    intro a b hm
    rw [mem_step_derivation_iff hs] at hm
    rcases step_app_inv hs with ⟨nv1, u1, hu1, rfl⟩ | ⟨v1, nv2, u2, hu2, rfl⟩ | ⟨v2, x, ty, bd, rfl, rfl⟩
    · have sub : ∀ p, p ∈ step_derivation t1 → p ∈ step_derivation (Term.App t1 t2) := by
        intro p hp; rw [mem_step_derivation_iff hs]; simp [nv1, hp]
      simp only [nv1] at hm
      rcases hm with h | h
      · cases h; exact rule_app_left nv1 (sub _ (mem_step_derivation_self hu1))
      · exact reduction_rule_mono sub _ _ ((red_derivation_iff _).1 (ih1 _ hu1) _ _ h)
    · have sub : ∀ p, p ∈ step_derivation t2 → p ∈ step_derivation (Term.App t1 t2) := by
        intro p hp; rw [mem_step_derivation_iff hs]; simp [v1, nv2, hp]
      simp only [v1, not_true_eq_false, if_false, nv2] at hm
      rcases hm with h | h
      · cases h
        exact rule_app_right v1 (fun ⟨_, _, _, _, v2⟩ => nv2 v2) (sub _ (mem_step_derivation_self hu2))
      · exact reduction_rule_mono sub _ _ ((red_derivation_iff _).1 (ih2 _ hu2) _ _ h)
    · have v1 : value? String String (Term.Lam x ty bd) = true := by simp [value?]
      simp only [v1, not_true_eq_false, if_false, v2] at hm
      rcases hm with h | h
      · cases h; exact rule_beta _ v2
      · exact h.elim
  | If c a b ihc _ _ =>
    intro u hs
    rw [red_derivation_iff]
    intro p q hm
    rw [mem_step_derivation_iff hs] at hm
    rcases step_if_inv hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e1, e2, u1, hu1, rfl⟩
    · simp only [true_or, if_true] at hm
      rcases hm with h | h
      · cases h; exact rule_if_true _ _ _
      · exact h.elim
    · simp only [or_true, if_true] at hm
      rcases hm with h | h
      · cases h; exact rule_if_false _ _ _
      · exact h.elim
    · have ne : ¬ (c = Term.True ∨ c = Term.False) := by rintro (h | h) <;> contradiction
      have sub : ∀ p, p ∈ step_derivation c → p ∈ step_derivation (Term.If c a b) := by
        intro p hp; rw [mem_step_derivation_iff hs]; simp [ne, hp]
      simp only [ne, if_false] at hm
      rcases hm with h | h
      · cases h; exact rule_if_cong e1 e2 (sub _ (mem_step_derivation_self hu1))
      · exact reduction_rule_mono sub _ _ ((red_derivation_iff _).1 (ihc _ hu1) _ _ h)

/-! ## Big-step evaluation -/

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

/-- What big-step evaluation gives is a value. -/
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

/-- More fuel changes nothing. -/
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

/-- A step changes nothing of what big-step evaluation gives. -/
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

/-- The two evaluators agree. -/
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

/-- Big-step evaluation preserves the type. -/
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

/-- Preservation along the transitive closure of a derivation. -/
theorem preservation_closure {typing : Fren.FinSet (Judgment × Ty)} {red : Fren.FinSet (Named × Named)} {t u : Named}
    {ty : Ty} (hd : typing_derivation? typing = true) (ht : ty ∈ types typing .Empty t) (hr : reduction_derivation? red = true)
    (hc : (t, u) ∈ red.closure) : typeof .Empty u = some ty := by
  have h0 : typeof .Empty t = some ty := checker_complete t typing _ ty hd (mem_types.1 ht)
  rw [Fren.FinSet.mem_closure] at hc
  induction hc with
  | single h => exact preservation _ _ _ _ h0 (step_complete _ red _ hr h)
  | tail _ h ih => exact preservation _ _ _ _ ih (step_complete _ red _ hr h)

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

/-- A closed nameless term, named and nameless again, is itself. -/
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

/-- A term converts to the nameless form where each free variable is in scope. -/
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

theorem value_fold (t : Named) : value? String String t = value_alg? String String Named (layer id t) := by
  cases t <;> simp [value?, value_alg?, layer]

theorem free_fold (t : Named) : free t = free_alg (layer free t) := by
  cases t <;> simp [free, free_alg, layer]

/-- The children of `typeof`'s layer are typed in their own contexts: the
body of an abstraction in the context extended by its binder. -/
def typeLayer (ctx : Ctx) : Named → TermF String String (Option Ty)
  | .Var x => .Var x
  | .Lam x ty b => .Lam x ty (typeof (.Bind x ty ctx) b)
  | .App a b => .App (typeof ctx a) (typeof ctx b)
  | .True => .True
  | .False => .False
  | .If c a b => .If (typeof ctx c) (typeof ctx a) (typeof ctx b)

theorem typeof_fold (ctx : Ctx) (t : Named) : typeof ctx t = typeof_alg ctx (typeLayer ctx t) := by
  cases t <;> simp only [typeof, typeof_alg, typeLayer]
  case Lam x ty b => cases typeof (Ctx.Bind x ty ctx) b <;> rfl
  case App f a => rcases typeof ctx f with _ | (_ | ⟨p, q⟩) <;> cases typeof ctx a <;> rfl
  case If c a b => rcases typeof ctx c with _ | (_ | ⟨p, q⟩) <;> cases typeof ctx a <;> cases typeof ctx b <;> rfl

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

impl checker_proved: checker for (typing : Fren.FinSet (Judgment × Ty)) (ctx : Ctx) (t : Named) (ty ty2 : Ty) {
  typing := typing, ctx := ctx, t := t, ty := ty, ty2 := ty2
} by
  intro typing ctx t ty ty2 _
  simp only [fren_spec]
  refine ⟨fun h => ⟨typing_of_derivation t ctx, mem_types.2 (mem_typing_of h)⟩,
    fun h => checker_complete t typing ctx ty h.1 (mem_types.1 h.2), fun h => ?_⟩
  have h1 := checker_complete t typing ctx ty h.1.1 (mem_types.1 h.1.2)
  have h2 := checker_complete t typing ctx ty2 h.1.1 (mem_types.1 h.2)
  rw [h1] at h2; cases h2; rfl

impl evaluator_proved: evaluator for (red : Fren.FinSet (Named × Named)) (t u v w : Named) (n m : Fuel) {
  red := red, t := t, u := u, v := v, w := w, n := n, m := m
} by
  intro red t u v w n m _
  simp only [fren_spec]
  refine ⟨fun h => ⟨step_sound t u h, mem_step_derivation_self h⟩, fun h => step_complete t red u h.1 h.2, fun h => ?_,
    fun h => step_value h, fun h => eval_value n t v h, fun h => eval_mono n t v h,
    fun h => step_eval n t u v h.1 h.2, fun h => eval_normalize m n t v w h.1 h.2⟩
  have h1 := step_complete t red u h.1.1 h.1.2
  have h2 := step_complete t red v h.1.1 h.2
  rw [h1] at h2; cases h2; rfl

impl type_safety_proved: type_safety for (typing : Fren.FinSet (Judgment × Ty)) (red : Fren.FinSet (Named × Named))
    (ctx : Ctx) (t u : Named) (ty : Ty) (n : Fuel) {
  typing := typing, red := red, ctx := ctx, t := t, u := u, ty := ty, n := n
} by
  intro typing red ctx t u ty n _
  simp only [fren_spec]
  refine ⟨fun h => ?_, fun h => preservation t ctx ty u h.1 h.2, fun h => ?_,
    fun h => eval_preservation n ctx t u ty h.1 h.2, fun h => preservation_closure h.1.1.1 h.1.1.2 h.1.2 h.2⟩
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

end Stlc
