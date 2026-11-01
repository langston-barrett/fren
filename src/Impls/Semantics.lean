-- keep-sorted start
import Fren.Impl
import Reqs.Lang
-- keep-sorted end

/-! # The dynamic semantics (`Reqs/Lang/EvaluationRules#free-variables`)

The coincidence lemma, proved by induction on `lang::Expr`: an expression
has one outcome under two interpretations and environments that agree on
its free variables, and the structural recursions and primitive operations.
`lang::coincidence` and `lang::closed` are proved from it, for every
interpretation, environment and expression. -/

open Fren.Generated

namespace SemProof
open lang

variable (i j : Interp)

/-- Two environments agree on a set of mentions, under `i` and `j`. -/
def Agree (p q : Env) (ms : Fren.FinSet Mention) : Prop :=
  ∀ m ∈ ms, match m with
    | .Var x => lookup p x = lookup q x
    | .Fn f => points i.functions f = points j.functions f

theorem Agree.mono {i j : Interp} {p q : Env} {ms ns : Fren.FinSet Mention} (h : Agree i j p q ms)
    (hs : ∀ m, m ∈ ns → m ∈ ms) : Agree i j p q ns := fun m hm => h m (hs m hm)

theorem apply_points (g : Graph) (f : String) (l : Value) : apply g f l = apply (points g f) f l := by
  induction g with
  | Empty => simp [apply, points]
  | Point h a r rest ih =>
    by_cases hf : h = f
    · subst hf; by_cases ha : a = l <;> simp [apply, points, ha, ih]
    · simp [apply, points, hf, ih]

theorem fn_not_binder (f : String) (pat : Pattern String) : Mention.Fn f ∉ binders pat := by
  induction pat <;> simp_all [binders]

theorem lookup_bind (pat : Pattern String) : ∀ (v : Value) (p q : Env) (y : String), matches_value? pat v = true →
    (lookup p y = lookup q y ∨ Mention.Var y ∈ binders pat) →
    lookup (lang.bind pat v p) y = lookup (lang.bind pat v q) y := by
  induction pat with
  | Binder x =>
    intro v p q y _ h
    by_cases hx : x = y
    · subst hx; simp [lang.bind, lookup]
    · have hy : lookup p y = lookup q y := by
        rcases h with h | h
        · exact h
        · simp [binders] at h; exact absurd h.symm hx
      simp [lang.bind, lookup, hx, hy]
  | Variant c ps ih =>
    intro v p q y hm h
    cases v with
    | Constructed d payload =>
      simp only [matches_value?, decide_eq_true_eq] at hm
      simp only [lang.bind]
      exact ih payload p q y hm.2 (by simpa [binders] using h)
    | _ => simp [matches_value?] at hm
  | Cons first rest ihf ihr =>
    intro v p q y hm h
    cases v with
    | Cons w more =>
      simp only [matches_value?, decide_eq_true_eq] at hm
      simp only [lang.bind]
      apply ihr more _ _ y hm.2
      by_cases hr : Mention.Var y ∈ binders rest
      · exact Or.inr hr
      · left
        apply ihf w p q y hm.1
        simp only [binders, Fren.FinSet.mem_union] at h
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hr
    | _ => simp [matches_value?] at hm
  | _ => intro v p q y _ h; simp_all [lang.bind, binders]
theorem fn_not_param (f : String) (ps : Params String) : Mention.Fn f ∉ param_names ps := by
  induction ps <;> simp_all [param_names]

variable {i j}

theorem binary_value_prims (hp : i.primitives = j.primitives) (op : BinaryOp) (a b : Outcome) :
    binary_value i op a b = binary_value j op a b := by
  simp only [binary_value, primitive, hp]

/-- The coincidence lemma: an expression has one outcome under two
interpretations and environments that agree on its free variables. -/
theorem eval_coincide (hr : i.recursions = j.recursions) (hp : i.primitives = j.primitives) :
    ∀ (e : Expr String) (p q : Env), Agree i j p q (free_vars e) → eval i p e = eval j q e := by
  intro e
  induction e with
  | Literal v => intro p q _; simp [eval]
  | Var x =>
    intro p q h
    have := h (.Var x) (by simp [free_vars])
    simpa [eval] using this
  | Let x d b ihd ihb =>
    intro p q h
    simp only [eval]
    apply ihb
    intro m hm
    cases m with
    | Var y =>
      by_cases hy : x = y
      · subst hy
        have hd : eval i p d = eval j q d := ihd p q (h.mono (by
          intro n hn; simp [free_vars, hm, hn]))
        simp [lookup, hd]
      · have := h (.Var y) (by simp [free_vars, hm, Ne.symm hy])
        simpa [lookup, hy] using this
    | Fn f => exact h (.Fn f) (by simp [free_vars, hm])
  | Unary op a iha =>
    intro p q h
    simp only [eval, iha p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Binary op a b iha ihb =>
    intro p q h
    simp only [eval, iha p q (h.mono (by intro m hm; simp [free_vars, hm])),
      ihb p q (h.mono (by intro m hm; simp [free_vars, hm])), binary_value_prims hp]
  | And a b iha ihb =>
    intro p q h
    simp only [eval, iha p q (h.mono (by intro m hm; simp [free_vars, hm])),
      ihb p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Or a b iha ihb =>
    intro p q h
    simp only [eval, iha p q (h.mono (by intro m hm; simp [free_vars, hm])),
      ihb p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | If c t f ihc iht ihf =>
    intro p q h
    simp only [eval, ihc p q (h.mono (by intro m hm; simp [free_vars, hm])),
      iht p q (h.mono (by intro m hm; simp [free_vars, hm])),
      ihf p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Is s pat ihs =>
    intro p q h
    simp only [eval, ihs p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Match s pat g b rest ihs ihg ihb ihr =>
    intro p q h
    have bound : ∀ (v : Value) (e : Expr String), matches_value? pat v = true →
        (∀ m, m ∈ free_vars e → m ∈ binders pat ∨ m ∈ free_vars (.Match s pat g b rest)) →
        Agree i j (lang.bind pat v p) (lang.bind pat v q) (free_vars e) := by
      intro v e hmv hsub m hm
      cases m with
      | Var y =>
        rcases hsub _ hm with hb | hf
        · exact lookup_bind pat v p q y hmv (Or.inr hb)
        · exact lookup_bind pat v p q y hmv (Or.inl (h _ hf))
      | Fn f =>
        rcases hsub _ hm with hb | hf
        · exact absurd hb (fn_not_binder f pat)
        · exact h _ hf
    simp only [eval]
    rw [ihs p q (h.mono (by intro m hm; simp [free_vars, hm]))]
    rw [ihr p q (h.mono (by intro m hm; simp [free_vars, hm]))]
    cases eval j q s with
    | Undefined => rfl
    | Defined v =>
      simp only []
      by_cases hmv : matches_value? pat v = true
      · have sub : ∀ e, (∀ m, m ∈ free_vars e → m ∈ free_vars g ∨ m ∈ free_vars b) →
            ∀ m, m ∈ free_vars e → m ∈ binders pat ∨ m ∈ free_vars (.Match s pat g b rest) := by
          intro e he m hm
          by_cases hb : m ∈ binders pat
          · exact Or.inl hb
          · right; rcases he m hm with h1 | h1 <;> simp [free_vars, h1, hb]
        rw [ihg _ _ (bound v g hmv (sub g (fun m hm => Or.inl hm))),
          ihb _ _ (bound v b hmv (sub b (fun m hm => Or.inr hm)))]
      · simp [hmv]
  | NoMatch => intro p q _; simp [eval]
  | Nil => intro p q _; simp [eval]
  | Cons a rest iha ihr =>
    intro p q h
    simp only [eval, iha p q (h.mono (by intro m hm; simp [free_vars, hm])),
      ihr p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Construct c args ih =>
    intro p q h
    simp only [eval, ih p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Project a c k ih =>
    intro p q h
    simp only [eval, ih p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Index a k iha ihk =>
    intro p q h
    simp only [eval, iha p q (h.mono (by intro m hm; simp [free_vars, hm])),
      ihk p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Method m r args ihr iha =>
    intro p q h
    simp only [eval, ihr p q (h.mono (by intro n hn; simp [free_vars, hn])),
      iha p q (h.mono (by intro n hn; simp [free_vars, hn]))]
  | Count c args ih =>
    intro p q h
    simp only [eval, ih p q (h.mono (by intro m hm; simp [free_vars, hm]))]
  | Apply f args ps body iha ihb =>
    intro p q h
    simp only [eval]
    rw [iha p q (h.mono (by intro m hm; simp [free_vars, hm]))]
    cases eval j q args with
    | Undefined => rfl
    | Defined l =>
      simp only []
      apply ihb
      intro m hm
      cases m with
      | Var y => rfl
      | Fn g => exact h (.Fn g) (by simp [free_vars, hm, fn_not_param])
  | Call f args ih =>
    intro p q h
    simp only [eval, call_value]
    rw [ih p q (h.mono (by intro m hm; simp [free_vars, hm]))]
    cases eval j q args with
    | Undefined => rfl
    | Defined l =>
      have hf : points i.functions f = points j.functions f := h (.Fn f) (by simp [free_vars])
      simp only []
      rw [apply_points i.functions, apply_points j.functions, hf]
  | Recur f args ih =>
    intro p q h
    simp only [eval, hr, ih p q (h.mono (by intro m hm; simp [free_vars, hm]))]

end SemProof

open Fren.Lang

namespace SemProof

theorem agree_of (i j : lang.Interp) (p q : lang.Env) (ms : Fren.FinSet lang.Mention)
    (h : lang.agree? i p j q ms = true) :
    (i.recursions = j.recursions ∧ i.primitives = j.primitives) ∧ Agree i j p q ms := by
  simp only [lang.agree?, decide_eq_true_eq] at h
  refine ⟨h.1, fun m hm => ?_⟩
  have := h.2 m hm
  cases m <;> simpa [lang.Mention.Var.x0, lang.Mention.Fn.x0] using this

end SemProof

-- For every two interpretations, environments and expressions.
impl coincidence: lang::coincidence for (i : lang.Interp) (p : lang.Env) (j : lang.Interp) (q : lang.Env)
    (e : lang.Expr String) {
  i := i, p := p, j := j, q := q, e := e,
} by
  intro i p j q e _
  simp only [fren_spec]
  intro h
  obtain ⟨⟨hr, hp⟩, ha⟩ := SemProof.agree_of i j p q _ h
  exact SemProof.eval_coincide hr hp e p q ha

-- For every two interpretations, environments and expressions.
impl closed: lang::closed for (i : lang.Interp) (p : lang.Env) (j : lang.Interp) (q : lang.Env) (e : lang.Expr String) {
  i := i, p := p, j := j, q := q, e := e,
} by
  intro i p j q e _
  simp only [fren_spec]
  rintro ⟨⟨he, hr⟩, hp⟩
  exact SemProof.eval_coincide hr hp e p q (by intro m hm; rw [he] at hm; simp at hm)
