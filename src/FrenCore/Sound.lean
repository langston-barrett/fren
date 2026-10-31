-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# Soundness of the checks

The check algorithms (`FrenCore.Check`) give the verdicts that `Reqs/Check`
says they give, provided the solver is sound: these theorems say what each
verdict, and what a failure reports, means about the procedure's behaviours,
whatever the solver answers. Fixed declaration inhabitation is distinguished
from a procedure's universal-input realizability: its actual SAT witness is
proved directly, and `fixed_inhabitation_completion` supplies the explicit
output-locality bridge for fixed interpretations. An `inconclusive` verdict means nothing, so no
theorem mentions it.

A backend's formulas are interpreted as predicates on environments, which give
every name a value (`Sound`): variables, and also the uninterpreted functions
a formula may use. A solver is typed, so only well-typed environments
(`Sound.Typed`) are behaviours, and only on them must formulas mean what they
say. What a procedure means (`Sound.Admits`, `Sound.Behaves`) is defined
from its items, its defined outputs' equations among them, not from the
hypotheses the checks build, so the theorems also check that each check asks
the right query. Realizability replaces the defined outputs by their
definitions instead, which needs `Sound.DefsOk` of the backend's `subst`. `checkComp_mem` and
`checkComp_runs` say which checks `checkComp` runs, and `checkComp_pass`
what it means when they all pass; `realizable_behaves` says what a passing
`realizable` means for the others.

Not covered: the theorems are over `Id`, and the front ends run the same
code in `MetaM` and `IO`; that a front end builds the `Comp` (its formulas,
calls' behaviours and triggers) faithfully from the source; that an
call's behaviour is possible because its procedure is realizable; a
solver that sizes a sort's domain per query (`Sound.HasType`); that cores
are minimal (`minimize`); that a front end's `subst` meets `Sound.DefsOk`;
that a definedness goal says its index is in range; and that a table's
goals say what its rows are.
-/

open Lean

namespace Fren.Core

variable {F V Val : Type}

/-- An environment: a value for every name. -/
abbrev Env (Val : Type) := Name → Val

/-- `n` is the name of a variable of `vars` whose role satisfies `p`. -/
def HasRole (vars : Array VarSig) (p : Role → Bool) (n : Name) : Prop := ∃ v ∈ vars, v.name = n ∧ p v.role

theorem hasRole_iff_any {vars : Array VarSig} {p : Role → Bool} {n : Name} :
    HasRole vars p n ↔ (vars.any fun v => v.name == n && p v.role) = true := by
  simp only [HasRole, Array.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨v, hv, h⟩ => let ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hv; ⟨i, hi, e ▸ h⟩,
    fun ⟨i, h, hv⟩ => ⟨_, Array.getElem_mem h, hv⟩⟩

instance (vars : Array VarSig) (p : Role → Bool) (n : Name) : Decidable (HasRole vars p n) :=
  decidable_of_iff _ hasRole_iff_any.symm

/-- `n` is the name of an output of the procedure, which the procedure
chooses. -/
abbrev IsOut (vars : Array VarSig) : Name → Prop := HasRole vars (· == .output)

/-- `n` is the name of a variable that is not an own parameter: an output, or a
variable of a call. `determinism` gives these a second copy, as the
backends choose them (`check::copied`). -/
abbrev IsCopied (vars : Array VarSig) : Name → Prop := HasRole vars fun r => (Symbol.ofRole r).copied

/-- `n` is the name of the second copy of a copied variable. -/
def IsPrimed (vars : Array VarSig) (n : Name) : Prop := ∃ m, IsCopied vars m ∧ primed m = n

/-- `ρ'` differs from `ρ` at most in the outputs. -/
def OnlyOuts (vars : Array VarSig) (ρ ρ' : Env Val) : Prop := ∀ n, ¬IsOut vars n → ρ' n = ρ n

/-- `ρ` with each variable that is not an own parameter read from its second copy,
as `Backend.prime` renames them. -/
def primeEnv (vars : Array VarSig) (ρ : Env Val) : Env Val :=
  fun n => if IsCopied vars n then ρ (primed n) else ρ n

/-- What it means for a backend to be sound, for a procedure with variables
`vars`: an interpretation `den` of its formulas, `value` of its model values
and `HasType` of the names' sorts, under which each formula builder means
what it says in well-typed environments, and the solver's answers are true
of them. -/
structure Sound (b : Backend Id F V) (vars : Array VarSig) (Val : Type) where
  den : F → Env Val → Prop
  value : V → Val
  /-- The values of `n`'s sort, the same for every query: a solver that
  sizes a sort's domain per query (finite model finding) is not covered. -/
  HasType : Name → Val → Prop
  /-- Every sort has values. -/
  inhabited : ∀ n, ∃ v, HasType n v
  /-- A second copy has its original's sort. -/
  hasType_primed : IsCopied vars n → (HasType (primed n) v ↔ HasType n v)
  /-- `unsat`: the goal holds wherever the hypotheses do. -/
  query_unsat : b.query hs g w = .unsat → ∀ ρ, (∀ n, HasType n (ρ n)) → (∀ h ∈ hs, den h.2 ρ) → den g ρ
  /-- `sat`: somewhere the hypotheses hold and the goal does not, and the
  model gives values there. -/
  query_sat : b.query hs g w = .sat model →
    ∃ ρ, (∀ n, HasType n (ρ n)) ∧ (∀ h ∈ hs, den h.2 ρ) ∧ ¬den g ρ ∧ ∀ p ∈ model, ρ p.1 = value p.2
  falseF : (∀ n, HasType n (ρ n)) → ¬den b.falseF ρ
  notF : (∀ n, HasType n (ρ n)) → (den (b.notF f) ρ ↔ ¬den f ρ)
  conj : (∀ n, HasType n (ρ n)) → (den (b.conj fs) ρ ↔ ∀ f ∈ fs, den f ρ)
  /-- `∃ outputs, f`: `f` holds after changing only the outputs, to values
  of their sorts. -/
  existsOutputs : (∀ n, HasType n (ρ n)) →
    (den (b.existsOutputs f) ρ ↔ ∃ ρ', (∀ n, HasType n (ρ' n)) ∧ OnlyOuts vars ρ ρ' ∧ den f ρ')
  pin : b.pin n v = some f → (∀ n, HasType n (ρ n)) → (den f ρ ↔ ρ n = value v)
  /-- The variant of a value of an enumeration; none for any other value. -/
  variantOf : Val → Option Variant
  /-- A tester: `x` is of the variant of `v`, which `pinVariant` gives. -/
  pinVariant : b.pinVariant n v = some (k, f) → (∀ n, HasType n (ρ n)) →
    variantOf (value v) = some k ∧ (den f ρ ↔ variantOf (ρ n) = some k)
  prime : (∀ n, HasType n (ρ n)) → (den (b.prime f) ρ ↔ den f (primeEnv vars ρ))
  samePrimed : (∀ n, HasType n (ρ n)) → (den (b.samePrimed x) ρ ↔ ρ x = ρ (primed x))
  /-- Different values of a sort are rendered differently. -/
  render_inj : (b.render n v).run = (b.render n v').run → HasType n (value v) → HasType n (value v') →
    value v = value v'

variable {b : Backend Id F V} {c : Comp F} (s : Sound b c.vars Val)

/-- Every name has a value of its sort. -/
def Sound.Typed (ρ : Env Val) : Prop := ∀ n, s.HasType n (ρ n)

/-- Some environment is well-typed. -/
theorem Sound.exists_typed : ∃ ρ, s.Typed ρ :=
  ⟨fun n => (s.inhabited n).choose, fun n => (s.inhabited n).choose_spec⟩

/-- Every hypothesis in `hs` holds in `ρ`. -/
def Sound.Holds (hs : Array (Name × F)) (ρ : Env Val) : Prop := ∀ h ∈ hs, s.den h.2 ρ

/-- `ρ` meets the definitions: each defined output is its definition. -/
def Sound.Defined (ρ : Env Val) : Prop := ∀ d ∈ c.defs, s.den d.2.1 ρ

/-- `ρ` meets the assumptions, and its first `k` calls are bound as the
procedure says and behave as their procedures do. -/
def Sound.Possible (ρ : Env Val) (k : Nat := c.insts.size) : Prop :=
  (∀ a ∈ c.assumes, s.den a.2 ρ) ∧
    ∀ (j : Nat) (hj : j < c.insts.size), j < k → s.den c.insts[j].bindings ρ ∧ s.den c.insts[j].behaviour ρ

/-- `ρ` is a possible environment of the procedure: it meets the
definitions, and is `Possible`. -/
def Sound.Admits (ρ : Env Val) (k : Nat := c.insts.size) : Prop := s.Defined ρ ∧ s.Possible ρ k

/-- `ρ` is a behaviour of the procedure: a possible environment, in which the
requirements hold. -/
def Sound.Behaves (ρ : Env Val) : Prop := s.Admits ρ ∧ ∀ r ∈ c.reqs, s.den r.2 ρ

/-- `ρ` has the values that `model` gives. -/
def Sound.Agrees (ρ : Env Val) (model : Array (Name × V)) : Prop := ∀ p ∈ model, ρ p.1 = s.value p.2

private theorem run_eq (x : α) : Id.run x = x := rfl
private theorem bind_eq (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
private theorem map_eq (x : Id α) (f : α → β) : f <$> x = f x := rfl
private theorem pure_eq (x : α) : (pure x : Id α) = x := rfl

theorem Sound.holds_append (xs ys : Array (Name × F)) (ρ : Env Val) :
    s.Holds (xs ++ ys) ρ ↔ s.Holds xs ρ ∧ s.Holds ys ρ := by
  simp only [Sound.Holds, Array.mem_append, or_imp, forall_and]

/-- The definitions' equations, which every check but realizability
assumes, mean that the definitions hold. -/
theorem Sound.holds_defEqs {kd : CheckKind} (hk : kd.substitutes = false) (ρ : Env Val) :
    s.Holds (c.defEqs kd) ρ ↔ s.Defined ρ := by
  simp only [Comp.defEqs, hk, Bool.false_eq_true, if_false, Sound.Holds, Sound.Defined, Array.mem_map]
  constructor
  · intro h d hd
    exact h _ ⟨d, hd, rfl⟩
  · rintro h _ ⟨d, hd, rfl⟩
    exact h d hd

/-- The assumptions and calls mean what the procedure means. -/
theorem Sound.holds_possible (k : Nat) {ρ : Env Val} (hρ : s.Typed ρ) :
    s.Holds (c.hyps b k) ρ ↔ s.Possible ρ k := by
  rw [Comp.hyps, s.holds_append, Sound.Possible]
  refine and_congr .rfl ⟨fun h j hj hk => ?_, fun h p hp => ?_⟩
  · have := h (c.insts[j].name, b.conj #[c.insts[j].bindings, c.insts[j].behaviour])
      (Array.mem_map.2 ⟨c.insts[j], Array.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩, rfl⟩)
    simpa [s.conj hρ] using this
  · obtain ⟨i, hi, rfl⟩ := Array.mem_map.1 hp
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hi
    simp only [Array.getElem_extract, Nat.zero_add, Array.size_extract] at hj ⊢
    simpa [s.conj hρ] using h j (by omega) (by omega)

/-- The checks' hypotheses mean what the procedure means. -/
theorem Sound.holds_hyps {kd : CheckKind} (hk : kd.substitutes = false) (k : Nat) {ρ : Env Val} (hρ : s.Typed ρ) :
    s.Holds (c.defEqs kd ++ c.hyps b k) ρ ↔ s.Admits ρ k := by
  rw [s.holds_append, s.holds_defEqs hk, s.holds_possible _ hρ]; rfl

theorem Sound.holds_behaves {kd : CheckKind} (hk : kd.substitutes = false) {ρ : Env Val} (hρ : s.Typed ρ) :
    s.Holds (c.defEqs kd ++ (c.hyps b ++ c.reqs)) ρ ↔ s.Behaves ρ := by
  rw [← Array.append_assoc, s.holds_append, s.holds_hyps hk _ hρ]; rfl

/-! ## What failures report -/

private theorem filterMapM_id {xs : Array α} {f : α → Id (Option β)} :
    (xs.filterMapM f).run = xs.filterMap fun x => (f x).run := by
  apply Array.toList_inj.1
  have e := congrArg Id.run (Array.toList_filterMapM (xs := xs) (f := f))
  refine e.trans ?_
  rw [Array.toList_filterMap]
  induction xs.toList with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMapM_cons, List.filterMap_cons]
    simp only [bind_eq, run_eq] at ih ⊢
    cases f x <;> simp only [pure_eq]
    · exact ih
    · exact congrArg _ ih

private theorem filterMapM_id' {xs : Array α} {f : α → Id (Option β)} :
    xs.filterMapM f = xs.filterMap fun x => (f x).run := filterMapM_id

private theorem mapM_id' {xs : Array α} {f : α → Id β} : xs.mapM f = xs.map fun x => (f x).run :=
  Array.idRun_mapM

/-- Each value shown is the rendering of a value in the model. -/
theorem renderModel_mem {vars : Array VarSig} {model : Array (Name × V)} {keep : VarSig → Bool}
    {n : Name} {str : String} (h : (n, str) ∈ (renderModel b vars model keep).run) :
    ∃ v ∈ vars, keep v ∧ v.name = n ∧ ∃ val, (n, val) ∈ model ∧ str = (b.render n val).run := by
  unfold renderModel at h
  rw [filterMapM_id, Array.mem_filterMap] at h
  obtain ⟨v, hv, e⟩ := h
  simp only [run_eq, bind_eq] at e
  split at e
  · cases e
  · next hk =>
    split at e
    · next _ n' val hp =>
      cases e
      have hf := Array.find?_some hp
      simp only [beq_iff_eq] at hf
      subst hf
      exact ⟨v, hv, by simpa using hk, rfl, val, Array.mem_of_find?_eq_some hp, rfl⟩
    · cases e

/-- A value shown for `n` is `?`, or the rendering of the model's value of
`n`. -/
theorem modelValue_spec (x : Name) (model : Array (Name × V)) (n : Name) :
    (modelValue b x model n).run = "?" ∨
      ∃ val, (n, val) ∈ model ∧ (modelValue b x model n).run = (b.render x val).run := by
  unfold modelValue
  split
  · next _ n' val hp =>
    have hf := Array.find?_some hp
    simp only [beq_iff_eq] at hf
    subst hf
    exact .inr ⟨val, Array.mem_of_find?_eq_some hp, rfl⟩
  · exact .inl rfl

/-- Closes a goal about a check that reports a model, in which `h` says
that its verdict is one that a contradicted model's never is, by cases
on what the backend's `confirm?` finds (`confirmReport`). -/
macro "confirm_close" b:term:max h:ident : tactic => `(tactic| (
  cases hc : ($b).confirm? <;> simp [hc, bind_eq, run_eq, pure_eq, map_eq] at $h:ident <;> (try split at $h:ident) <;> simp_all))

/-- Proves that a check's detail is the model it reports, given `h`, that
its verdict is one that a contradicted model's never is. -/
macro "confirm_detail" b:term:max h:ident : tactic => `(tactic| (
  cases hc : ($b).confirm? <;> simp [hc, bind_eq, run_eq, pure_eq, map_eq] at $h:ident ⊢ <;> (try split at $h:ident) <;>
    simp_all))

/-! ## Expectations -/

/-- A `pass` means the expectation holds in every behaviour. -/
theorem checkExpect_pass (e : Name × F) (h : (checkExpect b c e).run.verdict = .pass) :
    ∀ ρ, s.Typed ρ → s.Behaves ρ → s.den e.2 ρ := by
  unfold checkExpect confirmReport at h
  cases hq : b.query (c.defEqs .expect ++ (c.hyps b ++ c.reqs)) e.2 true <;> simp [hq, expectVerdict, Outcome.answer] at h
  case sat => confirm_close b h
  exact fun ρ ht hρ => s.query_unsat hq ρ ht ((s.holds_behaves (kd := .expect) rfl ht).2 hρ)

/-- A `fail` is a behaviour in which the expectation is false, which the
counterexample shows. -/
theorem checkExpect_fail (e : Name × F) (h : (checkExpect b c e).run.verdict = .fail) :
    ∃ ρ model, s.Typed ρ ∧ s.Behaves ρ ∧ ¬s.den e.2 ρ ∧ s.Agrees ρ model ∧
      (checkExpect b c e).run.detail = .counterexample (renderModel b c.vars model (·.isPub)).run := by
  unfold checkExpect confirmReport at h ⊢
  cases hq : b.query (c.defEqs .expect ++ (c.hyps b ++ c.reqs)) e.2 true <;>
    simp [hq, expectVerdict, Outcome.answer] at h ⊢
  obtain ⟨ρ, ht, hρ, hg, hm⟩ := s.query_sat hq
  refine ⟨ρ, ht, (s.holds_behaves (kd := .expect) rfl ht).1 hρ, hg, _, hm, ?_⟩
  confirm_detail b h

/-! ## Vacuity -/

/-- A `pass` is a behaviour in which the trigger holds. -/
theorem checkVacuity_pass (t : Name × F) (h : (checkVacuity b c t).run.verdict = .pass) :
    ∃ ρ, s.Typed ρ ∧ s.Behaves ρ ∧ s.den t.2 ρ := by
  unfold checkVacuity at h
  cases hq : b.query (c.defEqs .vacuity ++ (c.hyps b ++ c.reqs)) (b.notF t.2) (c.memberGroups.any (·.owner == t.1)) <;>
    simp [hq, vacuityVerdict, Outcome.answer] at h
  obtain ⟨ρ, ht, hρ, hg, -⟩ := s.query_sat hq
  exact ⟨ρ, ht, (s.holds_behaves (kd := .vacuity) rfl ht).1 hρ, by simpa [s.notF ht] using hg⟩

theorem Outcome.isUnsat_iff {q : Outcome V} : q.isUnsat = true ↔ q = .unsat := by
  cases q <;> simp [Outcome.isUnsat]

/-- An invariant of a loop that never stops early. -/
private theorem forIn_invariant {α β : Type} (xs : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h₀ : P init) (hf : ∀ x acc, P acc → ∃ acc', f x acc = pure (.yield acc') ∧ P acc') :
    P (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact h₀
  | cons x xs ih =>
    obtain ⟨acc', he, hp⟩ := hf x init h₀
    rw [List.forIn_cons, he]
    exact ih acc' hp

/-- The core is a subset of the candidates that, with `base`, still entails
the goal, if all the candidates do; and unless it is all of them, it does
whether or not they do. -/
theorem minimize_spec (base cands : Array (Name × F)) (goal : F) :
    ∃ keep : Array (Name × F), keep.toList.Sublist cands.toList ∧
      (minimize b base cands goal).run = keep.map (·.1) ∧
      ((∀ ρ, s.Typed ρ → s.Holds (base ++ cands) ρ → s.den goal ρ) →
        ∀ ρ, s.Typed ρ → s.Holds (base ++ keep) ρ → s.den goal ρ) ∧
      (keep = cands ∨ ∀ ρ, s.Typed ρ → s.Holds (base ++ keep) ρ → s.den goal ρ) := by
  unfold minimize
  simp only [bind_eq, run_eq]
  -- Each candidate is dropped only if the rest still entail the goal.
  let P (keep : Array (Name × F)) := keep.toList.Sublist cands.toList ∧
    ((∀ ρ, s.Typed ρ → s.Holds (base ++ cands) ρ → s.den goal ρ) →
      ∀ ρ, s.Typed ρ → s.Holds (base ++ keep) ρ → s.den goal ρ) ∧
    (keep = cands ∨ ∀ ρ, s.Typed ρ → s.Holds (base ++ keep) ρ → s.den goal ρ)
  refine ⟨_, ?_, rfl, ?_, ?_⟩ <;> rw [← Array.forIn_toList]
  case' refine_1 => refine (forIn_invariant _ _ _ P ⟨.refl _, id, .inl rfl⟩ ?_).1
  case' refine_2 => refine (forIn_invariant _ _ _ P ⟨.refl _, id, .inl rfl⟩ ?_).2.1
  case' refine_3 => refine (forIn_invariant _ _ _ P ⟨.refl _, id, .inl rfl⟩ ?_).2.2
  all_goals
    rintro x keep ⟨hsub, hent, hor⟩
    split
    · next hq =>
      have hu := s.query_unsat (Outcome.isUnsat_iff.1 hq)
      refine ⟨_, rfl, ?_, fun _ => hu, .inr hu⟩
      rw [Array.toList_filter]
      exact List.filter_sublist.trans hsub
    · exact ⟨_, rfl, hsub, hent, hor⟩

/-- Found forcing is forcing (`check::forcing`): if `forces` says `hyps`
force `x` to `v`, then `x` is `v` wherever they hold. -/
theorem forces_spec (hyps : Array (Name × F)) (x : Name) (v : V) (h : (forces b hyps x v).run = true) :
    ∀ ρ, s.Typed ρ → s.Holds hyps ρ → ρ x = s.value v := by
  unfold forces at h
  simp only [bind_eq, run_eq] at h
  cases hf : b.pin x v with
  | none => simp [hf, pure_eq] at h
  | some f =>
    simp only [hf, pure_eq] at h
    intro ρ hρ hh
    exact (s.pin hf hρ).1 (s.query_unsat (Outcome.isUnsat_iff.1 h) ρ hρ hh)

/-- Found variant forcing is variant forcing (`check::forcing`): if
`forcesVariant` says `hyps` force `x` to `v`'s variant, then `x` is of
that variant wherever they hold. -/
theorem forcesVariant_spec (hyps : Array (Name × F)) (x : Name) (v : V)
    (h : (forcesVariant b hyps x v).run = true) :
    ∀ ρ, s.Typed ρ → s.Holds hyps ρ → s.variantOf (ρ x) = s.variantOf (s.value v) := by
  unfold forcesVariant at h
  simp only [bind_eq, run_eq] at h
  cases hf : b.pinVariant x v with
  | none => simp [hf, pure_eq] at h
  | some kf =>
    obtain ⟨k, f⟩ := kf
    simp only [hf, pure_eq] at h
    intro ρ hρ hh
    have ⟨hv, hd⟩ := s.pinVariant hf hρ
    rw [hv]
    exact hd.1 (s.query_unsat (Outcome.isUnsat_iff.1 h) ρ hρ hh)

/-- A `fail` means the trigger holds in no behaviour, and the reported
constraints rule it out wherever the definitions hold. -/
theorem checkVacuity_fail (t : Name × F) (h : (checkVacuity b c t).run.verdict = .fail) :
    (∀ ρ, s.Typed ρ → s.Behaves ρ → ¬s.den t.2 ρ) ∧
    ∃ keep : Array (Name × F), keep.toList.Sublist (c.hyps b ++ c.reqs).toList ∧
      (checkVacuity b c t).run.detail = .vacuous (keep.map (·.1)) ∧
      ∀ ρ, s.Typed ρ → s.Defined ρ → s.Holds keep ρ → ¬s.den t.2 ρ := by
  obtain ⟨keep, hsub, hmin, hent, -⟩ := minimize_spec s (c.defEqs .vacuity) (c.hyps b ++ c.reqs) (b.notF t.2)
  unfold checkVacuity at h
  cases hq : b.query (c.defEqs .vacuity ++ (c.hyps b ++ c.reqs)) (b.notF t.2) (c.memberGroups.any (·.owner == t.1)) <;>
    simp [hq, vacuityVerdict, Outcome.answer] at h
  have hall := s.query_unsat hq
  refine ⟨fun ρ ht hρ => (s.notF ht).1 (hall ρ ht ((s.holds_behaves (kd := .vacuity) rfl ht).2 hρ)), keep, hsub, ?_,
    fun ρ ht hd hρ => (s.notF ht).1 (hent hall ρ ht
      ((s.holds_append _ _ ρ).2 ⟨(s.holds_defEqs rfl ρ).2 hd, hρ⟩))⟩
  simp only [run_eq] at hmin
  unfold checkVacuity
  simp [hq, vacuityVerdict, Outcome.answer, bind_eq, run_eq, pure_eq, hmin]

/-! ## Cover goals -/

/-- A `pass` is a behaviour in which the cover goal holds, which the
witness shows. -/
theorem checkCover_pass (g : Name × F) (h : (checkCover b c g).run.verdict = .pass) :
    ∃ ρ model, s.Typed ρ ∧ s.Behaves ρ ∧ s.den g.2 ρ ∧ s.Agrees ρ model ∧
      (checkCover b c g).run.detail = .witness (renderModel b c.vars model (·.isPub)).run := by
  unfold checkCover confirmReport at h ⊢
  cases hq : b.query (c.defEqs .cover ++ (c.hyps b ++ c.reqs)) (b.notF g.2) true <;>
    simp [hq, coverVerdict, Outcome.answer] at h ⊢
  obtain ⟨ρ, ht, hρ, hg, hm⟩ := s.query_sat hq
  refine ⟨ρ, ht, (s.holds_behaves (kd := .cover) rfl ht).1 hρ, by simpa [s.notF ht] using hg, _, hm, ?_⟩
  confirm_detail b h

/-- A `fail` means the cover goal holds in no behaviour, and the reported
constraints rule it out wherever the definitions hold. -/
theorem checkCover_fail (g : Name × F) (h : (checkCover b c g).run.verdict = .fail) :
    (∀ ρ, s.Typed ρ → s.Behaves ρ → ¬s.den g.2 ρ) ∧
    ∃ keep : Array (Name × F), keep.toList.Sublist (c.hyps b ++ c.reqs).toList ∧
      (checkCover b c g).run.detail = .vacuous (keep.map (·.1)) ∧
      ∀ ρ, s.Typed ρ → s.Defined ρ → s.Holds keep ρ → ¬s.den g.2 ρ := by
  obtain ⟨keep, hsub, hmin, hent, -⟩ := minimize_spec s (c.defEqs .cover) (c.hyps b ++ c.reqs) (b.notF g.2)
  unfold checkCover confirmReport at h
  cases hq : b.query (c.defEqs .cover ++ (c.hyps b ++ c.reqs)) (b.notF g.2) true <;>
    simp [hq, coverVerdict, Outcome.answer] at h
  case sat => confirm_close b h
  have hall := s.query_unsat hq
  refine ⟨fun ρ ht hρ => (s.notF ht).1 (hall ρ ht ((s.holds_behaves (kd := .cover) rfl ht).2 hρ)), keep, hsub, ?_,
    fun ρ ht hd hρ => (s.notF ht).1 (hent hall ρ ht
      ((s.holds_append _ _ ρ).2 ⟨(s.holds_defEqs rfl ρ).2 hd, hρ⟩))⟩
  simp only [run_eq] at hmin
  unfold checkCover
  simp [hq, coverVerdict, Outcome.answer, bind_eq, run_eq, pure_eq, hmin]

/-! ## Redundancy -/

/-- A `pass` is an environment that meets the definitions, in which `others`
hold and `p` does not. -/
theorem checkRedundant_pass (others : Array (Name × F)) (p : Name × F)
    (h : (checkRedundant b c others p).run.verdict = .pass) :
    ∃ ρ, s.Typed ρ ∧ s.Defined ρ ∧ s.Holds others ρ ∧ ¬s.den p.2 ρ := by
  unfold checkRedundant at h
  cases hq : b.query (c.defEqs .redundancy ++ others) p.2 false <;> simp [hq, vacuityVerdict, Outcome.answer] at h
  obtain ⟨ρ, ht, hρ, hg, -⟩ := s.query_sat hq
  have hρ := (s.holds_append _ _ ρ).1 hρ
  exact ⟨ρ, ht, (s.holds_defEqs rfl ρ).1 hρ.1, hρ.2, hg⟩

/-- A `fail` means `p` follows from `others` wherever the definitions hold,
and from the reported ones among them. -/
theorem checkRedundant_fail (others : Array (Name × F)) (p : Name × F)
    (h : (checkRedundant b c others p).run.verdict = .fail) :
    (∀ ρ, s.Typed ρ → s.Defined ρ → s.Holds others ρ → s.den p.2 ρ) ∧
    ∃ keep : Array (Name × F), keep.toList.Sublist others.toList ∧
      (checkRedundant b c others p).run.detail = .redundant (keep.map (·.1)) ∧
      ∀ ρ, s.Typed ρ → s.Defined ρ → s.Holds keep ρ → s.den p.2 ρ := by
  obtain ⟨keep, hsub, hmin, hent, -⟩ := minimize_spec s (c.defEqs .redundancy) others p.2
  unfold checkRedundant at h
  cases hq : b.query (c.defEqs .redundancy ++ others) p.2 false <;> simp [hq, vacuityVerdict, Outcome.answer] at h
  have hall := s.query_unsat hq
  have hdef : ∀ {xs : Array (Name × F)} {ρ}, s.Defined ρ → s.Holds xs ρ → s.Holds (c.defEqs .redundancy ++ xs) ρ :=
    fun hd hx => (s.holds_append _ _ _).2 ⟨(s.holds_defEqs rfl _).2 hd, hx⟩
  refine ⟨fun ρ ht hd hρ => hall ρ ht (hdef hd hρ), keep, hsub, ?_,
    fun ρ ht hd hρ => hent hall ρ ht (hdef hd hρ)⟩
  simp only [run_eq] at hmin
  unfold checkRedundant
  simp [hq, vacuityVerdict, Outcome.answer, bind_eq, run_eq, pure_eq, hmin]

private theorem holds_others (s : Sound b c.vars Val) (xs : Array (Name × F)) (p : Name × F) (ρ : Env Val) :
    s.Holds (xs.filter (·.1 != p.1)) ρ ↔ ∀ q ∈ xs, q.1 ≠ p.1 → s.den q.2 ρ := by
  simp [Sound.Holds, Array.mem_filter]

/-- An assumption passes when it does not follow from the other assumptions
(the comparison set `checkComp` uses). -/
theorem checkRedundant_assume_pass (a : Name × F)
    (h : (checkRedundant b c (c.assumes.filter (·.1 != a.1)) a).run.verdict = .pass) :
    ∃ ρ, s.Typed ρ ∧ s.Defined ρ ∧ (∀ q ∈ c.assumes, q.1 ≠ a.1 → s.den q.2 ρ) ∧ ¬s.den a.2 ρ := by
  obtain ⟨ρ, ht, hd, hρ, hn⟩ := checkRedundant_pass s _ a h
  exact ⟨ρ, ht, hd, (holds_others s _ a ρ).1 hρ, hn⟩

/-- An assumption fails when it follows from the other assumptions. -/
theorem checkRedundant_assume_fail (a : Name × F)
    (h : (checkRedundant b c (c.assumes.filter (·.1 != a.1)) a).run.verdict = .fail) :
    ∀ ρ, s.Typed ρ → s.Defined ρ → (∀ q ∈ c.assumes, q.1 ≠ a.1 → s.den q.2 ρ) → s.den a.2 ρ :=
  fun ρ ht hd hρ => (checkRedundant_fail s _ a h).1 ρ ht hd ((holds_others s _ a ρ).2 hρ)

/-- A requirement passes when it does not follow from the environment and
the other requirements (the comparison set `checkComp` uses). -/
theorem checkRedundant_req_pass (r : Name × F)
    (h : (checkRedundant b c (c.hyps b ++ c.reqs.filter (·.1 != r.1)) r).run.verdict = .pass) :
    ∃ ρ, s.Typed ρ ∧ s.Admits ρ ∧ (∀ q ∈ c.reqs, q.1 ≠ r.1 → s.den q.2 ρ) ∧ ¬s.den r.2 ρ := by
  obtain ⟨ρ, ht, hd, hρ, hn⟩ := checkRedundant_pass s _ r h
  rw [s.holds_append, s.holds_possible _ ht, holds_others s _ r ρ] at hρ
  exact ⟨ρ, ht, ⟨hd, hρ.1⟩, hρ.2, hn⟩

/-- A requirement fails when it follows from the environment and the other
requirements. -/
theorem checkRedundant_req_fail (r : Name × F)
    (h : (checkRedundant b c (c.hyps b ++ c.reqs.filter (·.1 != r.1)) r).run.verdict = .fail) :
    ∀ ρ, s.Typed ρ → s.Admits ρ → (∀ q ∈ c.reqs, q.1 ≠ r.1 → s.den q.2 ρ) → s.den r.2 ρ := fun ρ ht ha hr =>
  (checkRedundant_fail s _ r h).1 ρ ht ha.1 <|
    (s.holds_append _ _ ρ).2 ⟨(s.holds_possible _ ht).2 ha.2, (holds_others s _ r ρ).2 hr⟩

/-! ## Call assumptions -/

/-- A `pass` means the call's assumption follows from the assumptions,
the earlier calls and the call's bindings. -/
theorem checkInst_pass (k : Nat) (i : Inst F) (a : Name × F) (h : (checkInst b c k i a).run.verdict = .pass) :
    ∀ ρ, s.Typed ρ → s.Admits ρ k → s.den i.bindings ρ → s.den a.2 ρ := by
  unfold checkInst confirmReport at h
  cases hq : b.query (c.defEqs .inst ++ (c.hyps b k).push (i.name, i.bindings)) a.2 true <;>
    simp [hq, expectVerdict, Outcome.answer] at h
  case sat => confirm_close b h
  refine fun ρ ht hρ hb => s.query_unsat hq ρ ht ((s.holds_append _ _ ρ).2 ⟨(s.holds_defEqs rfl ρ).2 hρ.1,
    fun g hg => ?_⟩)
  rcases Array.mem_push.1 hg with hg | rfl
  · exact (s.holds_possible k ht).2 hρ.2 g hg
  · exact hb

/-- A `fail` is an environment in which the call's assumption is false,
which the counterexample shows. -/
theorem checkInst_fail (k : Nat) (i : Inst F) (a : Name × F) (h : (checkInst b c k i a).run.verdict = .fail) :
    ∃ ρ model, s.Typed ρ ∧ s.Admits ρ k ∧ s.den i.bindings ρ ∧ ¬s.den a.2 ρ ∧ s.Agrees ρ model ∧
      (checkInst b c k i a).run.detail = .counterexample (renderModel b c.vars model fun v =>
        v.isIn && v.isPub && !((c.insts.extract k).map (·.name)).contains v.name.getRoot).run := by
  unfold checkInst confirmReport at h ⊢
  cases hq : b.query (c.defEqs .inst ++ (c.hyps b k).push (i.name, i.bindings)) a.2 true <;>
    simp [hq, expectVerdict, Outcome.answer] at h ⊢
  obtain ⟨ρ, ht, hρ, hg, hm⟩ := s.query_sat hq
  refine ⟨ρ, ht, ⟨(s.holds_defEqs rfl ρ).1 fun g hg => hρ g (Array.mem_append_left _ hg),
      (s.holds_possible k ht).1 fun g hg => hρ g (Array.mem_append_right _ (Array.mem_push_of_mem _ hg))⟩,
    hρ _ (Array.mem_append_right _ (Array.mem_push_self ..)), hg, _, hm, ?_⟩
  confirm_detail b h

/-! ## Definedness -/

/-- A clause independent of the written site: a distributed group's
owner and descendant leaves cannot justify that group's own operation. -/
def IndexSite.Independent (site : IndexSite F) (name : Name) : Prop :=
  name ≠ site.prop ∧ (site.excludeSelf = true →
    (name.toString (escape := false)).startsWith (site.prop.toString (escape := false) ++ ".") = false)

private theorem independent_test (site : IndexSite F) (name : Name) :
    (!(name == site.prop || (site.excludeSelf &&
      (name.toString (escape := false)).startsWith (site.prop.toString (escape := false) ++ ".")))) = true ↔
      site.Independent name := by
  cases h : site.excludeSelf <;> by_cases hn : name = site.prop <;>
    simp [IndexSite.Independent, h, hn]

/-- The actual semantic context of an operation, retaining the exclusion
of its own clause/group when the operation is checked independently. -/
def Sound.AtSite (site : IndexSite F) (ρ : Env Val) : Prop :=
  match site.place with
  | .assume => s.Defined ρ ∧ ∀ q ∈ c.assumes, site.Independent q.1 → s.den q.2 ρ
  | .binding k => s.Admits ρ k
  | .prop => s.Admits ρ ∧ ∀ q ∈ c.reqs, (site.excludeSelf = true → site.Independent q.1) → s.den q.2 ρ
  | .body => s.Defined ρ ∧ ∀ q ∈ c.assumes, s.den q.2 ρ

theorem Sound.holds_site {kd : CheckKind} (hk : kd.substitutes = false) (site : IndexSite F) {ρ : Env Val}
    (ht : s.Typed ρ) : s.Holds (c.defEqs kd ++ c.siteHyps b site) ρ ↔ s.AtSite site ρ := by
  cases hp : site.place <;> simp only [Comp.siteHyps, hp, Sound.AtSite]
  · rw [s.holds_append, s.holds_defEqs hk]
    simp only [Sound.Holds, Array.mem_filter]
    simp only [independent_test]
    exact ⟨fun ⟨hd, h⟩ => ⟨hd, fun q hq hi => h q ⟨hq, hi⟩⟩,
      fun ⟨hd, h⟩ => ⟨hd, fun q ⟨hq, hi⟩ => h q hq hi⟩⟩
  · rw [← Array.append_assoc, s.holds_append, s.holds_hyps hk _ ht]
    cases he : site.excludeSelf <;>
      simp [he, Sound.Holds, Array.mem_filter, IndexSite.Independent, and_imp]
  · exact s.holds_hyps hk _ ht
  · rw [s.holds_append, s.holds_defEqs hk]
    exact .rfl

/-- A `pass` means the index is in range wherever it is evaluated. -/
theorem checkDefinedness_pass (site : IndexSite F) (h : (checkDefinedness b c site).run.verdict = .pass) :
    ∀ ρ, s.Typed ρ → s.AtSite site ρ → s.den site.goal ρ := by
  unfold checkDefinedness confirmReport at h
  cases hq : b.query (c.defEqs .definedness ++ c.siteHyps b site) site.goal true <;>
    simp [hq, expectVerdict, Outcome.answer] at h
  case sat => confirm_close b h
  exact fun ρ ht hρ => s.query_unsat hq ρ ht ((s.holds_site (kd := .definedness) rfl site ht).2 hρ)

/-- A `fail` is an environment where the index is evaluated and out of
range, which the counterexample shows. -/
theorem checkDefinedness_fail (site : IndexSite F) (h : (checkDefinedness b c site).run.verdict = .fail) :
    ∃ ρ model, s.Typed ρ ∧ s.AtSite site ρ ∧ ¬s.den site.goal ρ ∧ s.Agrees ρ model ∧
      (checkDefinedness b c site).run.detail = .counterexample (renderModel b c.vars model (·.isPub)).run := by
  unfold checkDefinedness confirmReport at h ⊢
  cases hq : b.query (c.defEqs .definedness ++ c.siteHyps b site) site.goal true <;>
    simp [hq, expectVerdict, Outcome.answer] at h ⊢
  obtain ⟨ρ, ht, hρ, hg, hm⟩ := s.query_sat hq
  refine ⟨ρ, ht, (s.holds_site (kd := .definedness) rfl site ht).1 hρ, hg, _, hm, ?_⟩
  confirm_detail b h

/-! ## Tables -/

theorem TableGoal.kind_substitutes (g : TableGoal) : g.kind.substitutes = false := by
  cases g <;> rfl

/-- The hypotheses of a question about a table hold wherever it is
evaluated: they are those of its place, or, for disjointness, some of
them (`Comp.tableHyps`). -/
theorem Sound.holds_tableHyps (t : TableSite F) {ρ : Env Val} (ht : s.Typed ρ) (hρ : s.AtSite t.site ρ) :
    s.Holds (c.tableHyps b t) ρ := by
  have hall := (s.holds_site t.goal.kind_substitutes t.site ht).2 hρ
  unfold Comp.tableHyps
  split
  · rename_i hk
    have hk : t.goal.kind = .disjointness := by simpa using hk
    unfold Comp.caseHyps
    rw [← hk]
    exact fun h hm => hall h (Array.mem_filter.1 hm).1
  · exact hall

/-- A `pass` means that what the question about the table's rows asks
holds wherever the table is evaluated. -/
theorem checkTable_pass (t : TableSite F) (h : (checkTable b c t).run.verdict = .pass) :
    ∀ ρ, s.Typed ρ → s.AtSite t.site ρ → s.den t.site.goal ρ := by
  unfold checkTable confirmReport at h
  cases hq : b.query (c.tableHyps b t) t.site.goal true <;>
    simp [hq, expectVerdict, Outcome.answer] at h
  case sat => confirm_close b h
  exact fun ρ ht hρ => s.query_unsat hq ρ ht (s.holds_tableHyps t ht hρ)

/-- A `fail` is an environment where the hypotheses of the question hold
(`Comp.tableHyps`), the table is evaluated there unless the question is
about disjointness, which leaves out the constraint that the table is in,
and what the question asks is false, which the counterexample shows. -/
theorem checkTable_fail (t : TableSite F) (h : (checkTable b c t).run.verdict = .fail) :
    ∃ ρ model, s.Typed ρ ∧ s.Holds (c.tableHyps b t) ρ ∧ (t.goal.kind ≠ .disjointness → s.AtSite t.site ρ) ∧
      ¬s.den t.site.goal ρ ∧ s.Agrees ρ model ∧
      (checkTable b c t).run.detail = .counterexample (renderModel b c.vars model (·.isPub)).run := by
  unfold checkTable confirmReport at h ⊢
  cases hq : b.query (c.tableHyps b t) t.site.goal true <;>
    simp [hq, expectVerdict, Outcome.answer] at h ⊢
  obtain ⟨ρ, ht, hρ, hg, hm⟩ := s.query_sat hq
  refine ⟨ρ, ht, hρ, fun hk => ?_, hg, _, hm, ?_⟩
  rotate_left
  · confirm_detail b h
  have : c.tableHyps b t = c.defEqs t.goal.kind ++ c.siteHyps b t.site := by
    simp [Comp.tableHyps, hk]
  rw [this] at hρ
  exact (s.holds_site t.goal.kind_substitutes t.site ht).1 hρ

/-- A `pass` of `reachability` is an environment where the hypotheses of
the case's place hold, but perhaps not the constraint it is in
(`Comp.reachHyps`), and its goal, that it is not taken, is false: the case
is taken there. -/
theorem checkReach_pass (t : TableSite F) (h : (checkReach b c t).run.verdict = .pass) :
    ∃ ρ, s.Typed ρ ∧ s.Holds (c.reachHyps b t.site) ρ ∧ ¬s.den t.site.goal ρ := by
  unfold checkReach at h
  cases hq : b.query (c.reachHyps b t.site) t.site.goal false <;>
    simp [hq, vacuityVerdict, Outcome.answer] at h
  obtain ⟨ρ, ht, hρ, hg, -⟩ := s.query_sat hq
  exact ⟨ρ, ht, hρ, hg⟩

/-- A `fail` of `reachability` means that the case is taken nowhere its
place's hypotheses, but the constraint it is in, hold. Those include
every environment where it is evaluated (`Sound.AtSite`). -/
theorem checkReach_fail (t : TableSite F) (h : (checkReach b c t).run.verdict = .fail) :
    ∀ ρ, s.Typed ρ → s.Holds (c.reachHyps b t.site) ρ → s.den t.site.goal ρ := by
  unfold checkReach at h
  cases hq : b.query (c.reachHyps b t.site) t.site.goal false <;>
    simp [hq, vacuityVerdict, Outcome.answer] at h
  exact fun ρ ht hρ => s.query_unsat hq ρ ht hρ

/-! ## Realizability -/

/-- `n` is the name of a defined output. -/
def IsDef (c : Comp F) (n : Name) : Prop := ∃ d ∈ c.defs, d.1 = n

/-- What realizability, which replaces the defined outputs by their
definitions (`Comp.subst`), needs of the backend's `subst` and of the
definitions. Without definitions it always holds (`Sound.defsOk_of_empty`). -/
structure Sound.DefsOk : Prop where
  /-- Defined outputs are `out`s. -/
  out : ∀ n, IsDef c n → IsOut c.vars n
  /-- Substituting the definitions keeps a formula's meaning wherever they hold. -/
  subst : ∀ f ρ, s.Typed ρ → s.Defined ρ → (s.den (c.subst b .realizable f) ρ ↔ s.den f ρ)
  /-- A formula with the definitions substituted does not depend on the defined outputs. -/
  free : ∀ f ρ ρ', (∀ n, ¬IsDef c n → ρ n = ρ' n) →
    (s.den (c.subst b .realizable f) ρ ↔ s.den (c.subst b .realizable f) ρ')
  /-- The definitions can be met by choosing the defined outputs, as they are acyclic. -/
  complete : ∀ ρ, s.Typed ρ → ∃ ρ', s.Typed ρ' ∧ (∀ n, ¬IsDef c n → ρ' n = ρ n) ∧ s.Defined ρ'

theorem Sound.defsOk_of_empty (h : c.defs = #[]) : s.DefsOk where
  out n := fun ⟨d, hd, _⟩ => by simp [h] at hd
  subst f ρ _ _ := by simp [Comp.subst, h]
  free f ρ ρ' hρ := by
    have : ρ = ρ' := funext fun n => hρ n fun ⟨d, hd, _⟩ => by simp [h] at hd
    rw [this]
  complete ρ ht := ⟨ρ, ht, fun _ _ => rfl, fun d hd => by simp [h] at hd⟩

variable {s} in
theorem Sound.DefsOk.holds_subst (hd : s.DefsOk) (hs : Array (Name × F)) {ρ : Env Val} (ht : s.Typed ρ)
    (hdef : s.Defined ρ) : s.Holds (c.substHyps b hs) ρ ↔ s.Holds hs ρ := by
  simp only [Sound.Holds, Comp.substHyps, Array.mem_map]
  constructor
  · intro h q hq
    exact (hd.subst _ _ ht hdef).1 (h _ ⟨q, hq, rfl⟩)
  · rintro h _ ⟨q, hq, rfl⟩
    exact (hd.subst _ _ ht hdef).2 (h q hq)

variable {s} in
theorem Sound.DefsOk.holds_free (hd : s.DefsOk) (hs : Array (Name × F)) {ρ ρ' : Env Val}
    (hρ : ∀ n, ¬IsDef c n → ρ n = ρ' n) : s.Holds (c.substHyps b hs) ρ ↔ s.Holds (c.substHyps b hs) ρ' := by
  simp only [Sound.Holds, Comp.substHyps, Array.mem_map]
  constructor
  · rintro h _ ⟨q, hq, rfl⟩
    exact (hd.free _ _ _ hρ).1 (h _ ⟨q, hq, rfl⟩)
  · rintro h _ ⟨q, hq, rfl⟩
    exact (hd.free _ _ _ hρ).2 (h _ ⟨q, hq, rfl⟩)

/-- The requirements, with the definitions substituted, as realizability
asks for them. -/
private theorem Sound.den_subst_reqs (hd : s.DefsOk) {ρ : Env Val} (ht : s.Typed ρ) (hdef : s.Defined ρ) :
    s.den (c.subst b .realizable (b.conj (c.reqs.map (·.2)))) ρ ↔ ∀ r ∈ c.reqs, s.den r.2 ρ := by
  rw [hd.subst _ _ ht hdef, s.conj ht]
  exact ⟨fun h r hr => h _ (Array.mem_map_of_mem hr), fun h f hf => by
    obtain ⟨r, hr, rfl⟩ := Array.mem_map.1 hf
    exact h r hr⟩

/-- The universal-input meaning of a procedure's realizability. -/
def Sound.ProcedureRealizable : Prop :=
  (∃ ρ, s.Typed ρ ∧ s.Defined ρ ∧ ∀ a ∈ c.assumes, s.den a.2 ρ) ∧
    ∀ ρ, s.Typed ρ → s.Admits ρ →
      ∃ ρ', s.Typed ρ' ∧ OnlyOuts c.vars ρ ρ' ∧ s.Defined ρ' ∧ ∀ r ∈ c.reqs, s.den r.2 ρ'

/-- The ordinary protocol's concrete failure, including its reported core. -/
def Sound.ProcedureFailure (result : CheckResult) : Prop :=
  ((∀ ρ, s.Typed ρ → s.Defined ρ → ¬∀ a ∈ c.assumes, s.den a.2 ρ) ∧
      ∃ keep : Array (Name × F), keep.toList.Sublist (c.substHyps b c.assumes).toList ∧
        result.detail = .vacuousAssumptions (keep.map (·.1)) ∧
        ∀ ρ, s.Typed ρ → ¬s.Holds keep ρ) ∨
    ∃ ρ model, s.Typed ρ ∧ s.Admits ρ ∧
      (¬∃ ρ', s.Typed ρ' ∧ OnlyOuts c.vars ρ ρ' ∧ s.Defined ρ' ∧ ∀ r ∈ c.reqs, s.den r.2 ρ') ∧
      s.Agrees ρ (conflictInput c.vars model) ∧
      ∃ keep : Array (Name × F), keep.toList.Sublist (c.substHyps b c.reqs).toList ∧
        result.detail =
          .conflict (renderModel b c.vars (conflictInput c.vars model) fun v => v.isIn && v.isPub).run
            (keep.map (·.1)) ∧
        ∀ ρ', s.Typed ρ' → OnlyOuts c.vars ρ ρ' → ¬s.Holds keep ρ'

/-- The declaration carrier is checked, rather than inferred from its tag. -/
theorem Comp.fixedInhabitation_shape (h : c.fixedInhabitation = true) :
    c.defs = #[] ∧ c.assumes = #[] ∧ c.insts = #[] ∧ c.vars.all (·.role == .output) = true := by
  simp only [Comp.fixedInhabitation, Bool.and_eq_true, Array.isEmpty_iff] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem Sound.fixed_behaves (hc : c.fixedInhabitation = true) (ρ : Env Val) :
    s.Behaves ρ ↔ ∀ r ∈ c.reqs, s.den r.2 ρ := by
  obtain ⟨hd, ha, hi, _⟩ := c.fixedInhabitation_shape hc
  simp [Sound.Behaves, Sound.Admits, Sound.Defined, Sound.Possible, hd, ha, hi]

/-- The checker has two actual domains: a fixed declaration needs a typed
witness; a procedure needs completion for every possible input environment. -/
def Sound.Realizable : Prop :=
  if c.fixedInhabitation then ∃ ρ, s.Typed ρ ∧ s.Behaves ρ else s.ProcedureRealizable

/-- Diagnostic metadata cannot change the ordinary protocol's verdict. -/
private theorem checkRealizableUniversal_verdict :
    (checkRealizableUniversal b c).run.verdict =
      (realizableVerdict (b.query (c.substHyps b c.assumes) b.falseF false).answer
        (b.query (c.substHyps b (c.hyps b))
          (b.existsOutputs (c.subst b .realizable (b.conj (c.reqs.map (·.2))))) true).answer).1 := by
  unfold checkRealizableUniversal
  cases ha : b.query (c.substHyps b c.assumes) b.falseF false <;>
    cases hc : b.query (c.substHyps b (c.hyps b))
      (b.existsOutputs (c.subst b .realizable (b.conj (c.reqs.map (·.2))))) true <;>
    simp +decide [ha, hc, realizableVerdict, Outcome.answer, Outcome.isUnsat, bind_eq, run_eq, pure_eq]
  all_goals split <;> rfl

/-- A `pass` means the assumptions are satisfiable, and every possible
environment, whatever the calls do, can be changed in its outputs alone
to meet the definitions and the requirements. -/
theorem checkRealizableUniversal_pass (hd : s.DefsOk) (h : (checkRealizableUniversal b c).run.verdict = .pass) :
    s.ProcedureRealizable := by
  unfold Sound.ProcedureRealizable
  rw [checkRealizableUniversal_verdict] at h
  cases ha : b.query (c.substHyps b c.assumes) b.falseF false <;>
    cases hc : b.query (c.substHyps b (c.hyps b))
      (b.existsOutputs (c.subst b .realizable (b.conj (c.reqs.map (·.2))))) true <;>
    simp +decide [ha, hc, realizableVerdict, Outcome.answer] at h
  refine ⟨?_, fun ρ ht hρ => ?_⟩
  · obtain ⟨ρ, ht, hρ, -⟩ := s.query_sat ha
    obtain ⟨ρ₀, ht₀, hsame, hdef⟩ := hd.complete ρ ht
    exact ⟨ρ₀, ht₀, hdef, (hd.holds_subst _ ht₀ hdef).1 ((hd.holds_free _ fun n hn => (hsame n hn).symm).1 hρ)⟩
  · have hq := s.query_unsat hc ρ ht ((hd.holds_subst _ ht hρ.1).2 ((s.holds_possible _ ht).2 hρ.2))
    obtain ⟨ρ', ht', hout, hr⟩ := (s.existsOutputs ht).1 hq
    obtain ⟨ρ'', ht'', hsame, hdef⟩ := hd.complete ρ' ht'
    refine ⟨ρ'', ht'', fun n hn => ?_, hdef, (s.den_subst_reqs hd ht'' hdef).1 ((hd.free _ _ _ hsame).2 hr)⟩
    rw [hsame n fun hdn => hn (hd.out n hdn)]
    exact hout n hn

/-- A `fail` means the assumptions contradict each other wherever the
definitions hold, and the reported ones do; or some possible environment
cannot be changed in its outputs to meet the definitions and the
requirements, and cannot be to meet the reported ones, with the
definitions substituted. Its input is shown. -/
theorem checkRealizableUniversal_fail (hd : s.DefsOk) (h : (checkRealizableUniversal b c).run.verdict = .fail) :
    s.ProcedureFailure (checkRealizableUniversal b c).run := by
  unfold Sound.ProcedureFailure
  rw [checkRealizableUniversal_verdict] at h
  cases ha : b.query (c.substHyps b c.assumes) b.falseF false <;>
    cases hc : b.query (c.substHyps b (c.hyps b))
      (b.existsOutputs (c.subst b .realizable (b.conj (c.reqs.map (·.2))))) true <;>
    simp +decide [ha, hc, realizableVerdict, Outcome.answer] at h
  all_goals first
    | -- The assumptions contradict each other.
      have hall := s.query_unsat ha
      obtain ⟨keep, hsub, hmin, hent, -⟩ := minimize_spec s #[] (c.substHyps b c.assumes) b.falseF
      refine .inl ⟨fun ρ ht hdef hρ => s.falseF ht (hall ρ ht ((hd.holds_subst _ ht hdef).2 hρ)), keep, hsub, ?_,
        fun ρ ht hρ => s.falseF ht <|
          hent (fun ρ ht hρ => hall ρ ht (by simpa [Sound.Holds] using hρ)) ρ ht (by simpa [Sound.Holds] using hρ)⟩
      simp only [run_eq] at hmin
      unfold checkRealizableUniversal
      simp +decide [ha, hc, realizableVerdict, Outcome.answer, Outcome.isUnsat, bind_eq, run_eq, pure_eq, hmin]
    | -- A conflict.
      rename_i model
      obtain ⟨ρ₁, ht₁, hρ₁, hg, hm⟩ := s.query_sat hc
      obtain ⟨ρ, ht, hsame, hdef⟩ := hd.complete ρ₁ ht₁
      -- `ρ` differs from `ρ₁` only in defined outputs, which are `out`s.
      have hout₁ : OnlyOuts c.vars ρ₁ ρ := fun n hn => hsame n fun hdn => hn (hd.out n hdn)
      have hposs : s.Possible ρ := (s.holds_possible _ ht).1 <| (hd.holds_subst _ ht hdef).1 <|
        (hd.holds_free _ fun n hn => (hsame n hn).symm).1 hρ₁
      have hno : ¬∃ ρ', s.Typed ρ' ∧ OnlyOuts c.vars ρ ρ' ∧ s.Defined ρ' ∧ ∀ r ∈ c.reqs, s.den r.2 ρ' :=
        fun ⟨ρ', ht', hin, hdef', hr⟩ => hg ((s.existsOutputs ht₁).2
          ⟨ρ', ht', fun n hn => (hin n hn).trans (hout₁ n hn), (s.den_subst_reqs hd ht' hdef').2 hr⟩)
      let input := conflictInput c.vars model
      have hinput : ∀ p ∈ input, p ∈ model ∧ ¬IsOut c.vars p.1 := by
        intro p hp
        simp only [input, conflictInput, Array.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hp
        obtain ⟨hp, -, hnout⟩ := hp
        refine ⟨hp, fun ho => ?_⟩
        have ho' := hasRole_iff_any.1 ho
        rw [hnout] at ho'
        cases ho'
      have hagree : s.Agrees ρ input := fun p hp =>
        (hout₁ _ (hinput p hp).2).trans (hm _ (hinput p hp).1)
      let pinned := (pins b input).run
      obtain ⟨keep, hsub, hmin, -, hor⟩ := minimize_spec s pinned (c.substHyps b c.reqs) b.falseF
      refine .inr ⟨ρ, model, ht, ⟨hdef, hposs⟩, hno, hagree, keep, hsub, ?_,
        fun ρ' ht' hout hkeep => ?_⟩
      · simp only [pinned, input, run_eq] at hmin
        unfold checkRealizableUniversal
        simp +decide [ha, hc, realizableVerdict, Outcome.answer, Outcome.isUnsat, bind_eq, run_eq, pure_eq, hmin]
      rcases hor with rfl | hent
      · -- Nothing was dropped: no outputs meet all the requirements.
        obtain ⟨ρ'', ht'', hsame', hdef''⟩ := hd.complete ρ' ht'
        exact hno ⟨ρ'', ht'', fun n hn => (hsame' n fun hdn => hn (hd.out n hdn)).trans (hout n hn), hdef'',
          (hd.holds_subst _ ht'' hdef'').1 ((hd.holds_free _ fun n hn => (hsame' n hn).symm).1 hkeep)⟩
      -- Something was dropped, so the pins and the core contradict each other; and the
      -- pins hold whatever the outputs, since no pinned variable is an output.
      refine s.falseF ht' (hent ρ' ht' ((s.holds_append _ _ ρ').2 ⟨fun q hq => ?_, hkeep⟩))
      simp only [pinned, pins] at hq
      rw [filterMapM_id] at hq
      simp only [Array.mem_filterMap, bind_eq, run_eq, pure_eq] at hq
      obtain ⟨⟨n, val⟩, hin, e⟩ := hq
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 e
      exact (s.pin hf ht').2 ((hout n (hinput _ hin).2).trans (hagree _ hin))

/-- If `realizable` passes, every possible environment is completed to a
behaviour by choosing the outputs, provided that changing the outputs keeps
the environment `Possible`: assumptions and bindings cannot mention outputs
(`inst::binding`). So `expect` and `determinism` do not pass vacuously,
provided some environment is possible: one that meets the definitions and
the assumptions, if the procedure has no calls. -/
theorem realizableUniversal_behaves (hd : s.DefsOk) (hindep : ∀ ρ ρ', OnlyOuts c.vars ρ ρ' → s.Possible ρ → s.Possible ρ')
    (h : (checkRealizableUniversal b c).run.verdict = .pass) :
    ∀ ρ, s.Typed ρ → s.Admits ρ → ∃ ρ', s.Typed ρ' ∧ OnlyOuts c.vars ρ ρ' ∧ s.Behaves ρ' := fun ρ ht hρ =>
  let ⟨ρ', ht', hin, hdef, hr⟩ := (checkRealizableUniversal_pass s hd h).2 ρ ht hρ
  ⟨ρ', ht', hin, ⟨hdef, hindep ρ ρ' hin hρ.2⟩, hr⟩

/-- Passing the fixed SAT query gives an actual typed satisfying witness.
No assumption that the declaration tag itself proves interpretation locality
is used; the locality bridge below is a separate semantic theorem. -/
theorem checkFixedInhabitation_pass (hc : c.fixedInhabitation = true)
    (h : (checkRealizable b c).run.verdict = .pass) : ∃ ρ, s.Typed ρ ∧ s.Behaves ρ := by
  obtain ⟨hdefs, ha, hi, _⟩ := c.fixedInhabitation_shape hc
  simp [checkRealizable, hc, Comp.defEqs, CheckKind.substitutes, Comp.hyps, ha, hi] at h
  cases hq : b.query c.reqs b.falseF true <;>
    simp [hq, run_eq, pure_eq] at h
  obtain ⟨ρ, ht, hr, _, _⟩ := s.query_sat hq
  exact ⟨ρ, ht, (s.fixed_behaves hc ρ).2 hr⟩

theorem checkRealizable_pass (hd : s.DefsOk) (h : (checkRealizable b c).run.verdict = .pass) :
    s.Realizable := by
  by_cases hc : c.fixedInhabitation = true
  · simpa only [Sound.Realizable, hc, if_true] using checkFixedInhabitation_pass s hc h
  · simp only [Sound.Realizable, hc]
    apply checkRealizableUniversal_pass s hd
    simpa [checkRealizable, hc] using h

/-- Failure in declaration mode rules out every typed witness, and the
reported invariant core itself is unsatisfiable. Procedure-mode failures
retain the ordinary counterexample/core theorem unchanged. -/
theorem checkRealizable_fail (hd : s.DefsOk) (h : (checkRealizable b c).run.verdict = .fail) :
    if c.fixedInhabitation then
      (∀ ρ, s.Typed ρ → ¬s.Behaves ρ) ∧
      ∃ keep : Array (Name × F), keep.toList.Sublist c.reqs.toList ∧
        (checkRealizable b c).run.detail = .conflict #[] (keep.map (·.1)) ∧
        ∀ ρ, s.Typed ρ → ¬s.Holds keep ρ
    else s.ProcedureFailure (checkRealizable b c).run := by
  by_cases hc : c.fixedInhabitation = true
  · obtain ⟨hdefs, ha, hi, _⟩ := c.fixedInhabitation_shape hc
    simp only [hc, if_true]
    have hh := h
    simp [checkRealizable, hc, Comp.defEqs, CheckKind.substitutes, Comp.hyps, ha, hi] at hh
    cases hq : b.query c.reqs b.falseF true <;>
      simp [hq, run_eq, pure_eq] at hh
    have hall := s.query_unsat hq
    obtain ⟨keep, hsub, hmin, hent, _⟩ := minimize_spec s #[] c.reqs b.falseF
    refine ⟨fun ρ ht hb => s.falseF ht (hall ρ ht ((s.fixed_behaves hc ρ).1 hb)), keep, hsub, ?_, ?_⟩
    · simp only [run_eq] at hmin
      simp [checkRealizable, hc, Comp.defEqs, CheckKind.substitutes, Comp.hyps, ha, hi, hq,
        bind_eq, run_eq, pure_eq, hmin]
    · intro ρ ht hk
      exact s.falseF ht (hent (fun ρ ht hr => hall ρ ht (by simpa [Sound.Holds] using hr))
        ρ ht (by simpa [Sound.Holds] using hk))
  · simp only [hc]
    have hp : (checkRealizableUniversal b c).run.verdict = .fail := by
      simpa [checkRealizable, hc] using h
    simpa [checkRealizable, hc] using checkRealizableUniversal_fail s hd hp

/-- A concrete proof link for fixed interpreted declarations: each invariant
has the same truth in typed environments agreeing on the fresh outputs.
This is semantic output locality, not a Boolean promise from the tag. -/
def Sound.OutputLocal : Prop :=
  ∀ r ∈ c.reqs, ∀ ρ ρ', s.Typed ρ → s.Typed ρ' →
    (∀ n, IsOut c.vars n → ρ n = ρ' n) → (s.den r.2 ρ ↔ s.den r.2 ρ')

/-- Copy the satisfying value into any fixed interpreted environment.
This is the witness-to-universal-completion bridge required for the SAT
optimization of declaration inhabitation. -/
theorem fixed_inhabitation_completion (hc : c.fixedInhabitation = true)
    (hlocal : s.OutputLocal) (h : (checkRealizable b c).run.verdict = .pass) :
    ∀ ρ, s.Typed ρ → ∃ ρ', s.Typed ρ' ∧ OnlyOuts c.vars ρ ρ' ∧ s.Behaves ρ' := by
  have hw := checkFixedInhabitation_pass s hc h
  obtain ⟨witness, hwtyped, hwbehaves⟩ := hw
  intro ρ ht
  let completed : Env Val := fun n => if IsOut c.vars n then witness n else ρ n
  have completed_typed : s.Typed completed := by
    intro n
    dsimp [completed]
    split <;> first | exact hwtyped n | exact ht n
  refine ⟨completed, completed_typed, fun n hn => ?_, (s.fixed_behaves hc completed).2 ?_⟩
  · simp [completed, hn]
  · intro r hr
    exact (hlocal r hr witness completed hwtyped completed_typed (fun n hn => by simp [completed, hn])).1
      ((s.fixed_behaves hc witness).1 hwbehaves r hr)

/-- Both query modes give a nonvacuous behaviour. For ordinary procedures
this follows by completing a possible environment; declaration mode supplies
its satisfying witness directly. -/
theorem realizable_behaves (hd : s.DefsOk)
    (hindep : ∀ ρ ρ', OnlyOuts c.vars ρ ρ' → s.Possible ρ → s.Possible ρ')
    (h : (checkRealizable b c).run.verdict = .pass)
    (possible : ∃ ρ, s.Typed ρ ∧ s.Admits ρ) : ∃ ρ, s.Typed ρ ∧ s.Behaves ρ := by
  by_cases hc : c.fixedInhabitation = true
  · simpa [Sound.Realizable, hc] using checkRealizable_pass s hd h
  · obtain ⟨ρ, ht, hp⟩ := possible
    have hu : (checkRealizableUniversal b c).run.verdict = .pass := by simpa [checkRealizable, hc] using h
    obtain ⟨ρ', ht', _, hb⟩ := realizableUniversal_behaves s hd hindep hu ρ ht hp
    exact ⟨ρ', ht', hb⟩

/-! ## Determinism -/

/-- The hypotheses of `determinism`'s query, before they are copied. -/
abbrev Comp.once (c : Comp F) (b : Backend Id F V) : Array (Name × F) := c.defEqs .determinism ++ (c.hyps b ++ c.reqs)

theorem Sound.holds_twice (hs : Array (Name × F)) {ρ : Env Val} (ht : s.Typed ρ) :
    s.Holds (hs ++ hs.map fun x => (primed x.1, b.prime x.2)) ρ ↔
      s.Holds hs ρ ∧ s.Holds hs (primeEnv c.vars ρ) := by
  simp only [Sound.Holds, Array.mem_append, Array.mem_map]
  constructor
  · intro h
    exact ⟨fun g hg => h g (.inl hg), fun g hg => (s.prime ht).1 (h _ (.inr ⟨g, hg, rfl⟩))⟩
  · rintro ⟨h₁, h₂⟩ g (hg | ⟨g, hg, rfl⟩)
    · exact h₁ g hg
    · exact (s.prime ht).2 (h₂ g hg)

/-- The second copy of an environment agrees with it on the own parameters. -/
theorem primeEnv_of_not_copied {vars : Array VarSig} {ρ : Env Val} {n : Name} (hn : ¬IsCopied vars n) :
    primeEnv vars ρ n = ρ n := by
  simp [primeEnv, hn]

theorem Sound.typed_primeEnv {ρ : Env Val} (ht : s.Typed ρ) : s.Typed (primeEnv c.vars ρ) := by
  intro n
  unfold primeEnv
  split
  · next hn => exact (s.hasType_primed hn).1 (ht _)
  · exact ht n

private theorem copied_of_out {vars : Array VarSig} {x : Name} (hx : IsOut vars x) : IsCopied vars x :=
  let ⟨v, hv, hn, ho⟩ := hx
  ⟨v, hv, hn, by simp at ho; simp [ho, Symbol.ofRole, Symbol.copied]⟩

/-- A `fail` is two behaviours that agree on everything but the copied
variables (`primeEnv_of_not_copied`), and disagree on `x`: `ρ`, and its
second copy. The values shown are the model's, so they differ unless the
model leaves one out (`?`). -/
theorem checkDeterminism_fail (x : Name) (hx : IsOut c.vars x)
    (h : (checkDeterminism b c x).run.verdict = .fail) :
    ∃ ρ model, s.Typed ρ ∧ s.Typed (primeEnv c.vars ρ) ∧ s.Behaves ρ ∧ s.Behaves (primeEnv c.vars ρ) ∧
      ρ x ≠ primeEnv c.vars ρ x ∧ s.Agrees ρ model ∧
      (checkDeterminism b c x).run.detail = .nondeterministic
        (renderModel b c.vars model fun v => v.isIn && v.isPub && v.name.isAtomic).run
        (modelValue b x model x).run (modelValue b x model (primed x)).run ∧
      ((modelValue b x model x).run = "?" ∨ (modelValue b x model (primed x)).run = "?" ∨
        (modelValue b x model x).run ≠ (modelValue b x model (primed x)).run) := by
  unfold checkDeterminism confirmReport at h ⊢
  simp only [bind_eq] at h ⊢
  cases hq : b.query (c.once b ++ (c.once b).map fun x => (primed x.1, b.prime x.2)) (b.samePrimed x) true <;>
    rw [hq] at h <;> simp +decide [determinismVerdict, expectVerdict, Outcome.answer, run_eq, pure_eq] at h ⊢
  obtain ⟨ρ, ht, hρ, hg, hm⟩ := s.query_sat hq
  have ht' := s.typed_primeEnv ht
  replace hρ := (s.holds_twice _ ht).1 hρ
  rename_i model
  have hne : ρ x ≠ ρ (primed x) := by simpa [s.samePrimed ht] using hg
  refine ⟨ρ, ht, ht', (s.holds_behaves (kd := .determinism) rfl ht).1 hρ.1, (s.holds_behaves (kd := .determinism) rfl ht').1 hρ.2,
    by simpa [primeEnv, copied_of_out hx] using hne, _, hm, ?_, ?_⟩
  · confirm_detail b h
  rcases modelValue_spec x model x with h₁ | ⟨v₁, hv₁, e₁⟩
  · exact .inl h₁
  rcases modelValue_spec x model (primed x) with h₂ | ⟨v₂, hv₂, e₂⟩
  · exact .inr (.inl h₂)
  refine .inr (.inr fun e => hne ?_)
  rw [hm _ hv₁, hm _ hv₂]
  refine s.render_inj (by rw [← e₁, ← e₂, e]) ?_ ?_
  · rw [← hm _ hv₁]; exact ht x
  · rw [← hm _ hv₂]; exact (s.hasType_primed (copied_of_out hx)).1 (ht _)

/-- A `pass` means any two behaviours that agree on everything but the
copied variables agree on `x`: the same inputs, and the same interpretation
of any functions, whatever the calls do. This needs the behaviours not
to depend on the second copies, and second copies' names to be distinct and
not `x`. -/
theorem checkDeterminism_pass (x : Name) (hx : IsOut c.vars x)
    (hprimes : ∀ ρ ρ', (∀ n, ¬IsPrimed c.vars n → ρ n = ρ' n) → (s.Behaves ρ ↔ s.Behaves ρ'))
    (hfresh : ¬IsPrimed c.vars x)
    (hinj : ∀ m n, IsCopied c.vars m → IsCopied c.vars n → primed m = primed n → m = n)
    (h : (checkDeterminism b c x).run.verdict = .pass) :
    ∀ ρ₁ ρ₂, s.Typed ρ₁ → s.Typed ρ₂ → (∀ n, ¬IsCopied c.vars n → ρ₁ n = ρ₂ n) →
      s.Behaves ρ₁ → s.Behaves ρ₂ → ρ₁ x = ρ₂ x := by
  unfold checkDeterminism confirmReport at h
  simp only [bind_eq] at h
  cases hq : b.query (c.once b ++ (c.once b).map fun x => (primed x.1, b.prime x.2)) (b.samePrimed x) true <;>
    rw [hq] at h <;> simp +decide [determinismVerdict, expectVerdict, Outcome.answer, run_eq] at h
  case sat => confirm_close b h
  intro ρ₁ ρ₂ ht₁ ht₂ hsame h₁ h₂
  classical
  -- One environment holding both behaviours: `ρ₂`'s copied variables in their second copies.
  let glue : Env Val := fun n => if hp : IsPrimed c.vars n then ρ₂ hp.choose else ρ₁ n
  have glue_primed : ∀ m, IsCopied c.vars m → glue (primed m) = ρ₂ m := by
    intro m hm
    have hp : IsPrimed c.vars (primed m) := ⟨m, hm, rfl⟩
    simp only [glue, dif_pos hp]
    exact congrArg ρ₂ (hinj _ _ hp.choose_spec.1 hm hp.choose_spec.2)
  have glue_other : ∀ n, ¬IsPrimed c.vars n → glue n = ρ₁ n := fun n hn => by
    simp only [glue, dif_neg hn]
  have glue_typed : s.Typed glue := by
    intro n
    by_cases hp : IsPrimed c.vars n
    · obtain ⟨m, hm, rfl⟩ := hp
      rw [glue_primed m hm]
      exact (s.hasType_primed hm).2 (ht₂ m)
    · rw [glue_other n hp]
      exact ht₁ n
  have prime_other : ∀ n, ¬IsPrimed c.vars n → primeEnv c.vars glue n = ρ₂ n := by
    intro n hn
    unfold primeEnv
    split
    · next ho => exact glue_primed _ ho
    · next ho => rw [glue_other n hn]; exact hsame n ho
  have := s.query_unsat hq glue glue_typed <| (s.holds_twice _ glue_typed).2
    ⟨(s.holds_behaves (kd := .determinism) rfl glue_typed).2 ((hprimes _ _ glue_other).2 h₁),
     (s.holds_behaves (kd := .determinism) rfl (s.typed_primeEnv glue_typed)).2 ((hprimes _ _ prime_other).2 h₂)⟩
  rwa [s.samePrimed glue_typed, glue_primed x (copied_of_out hx), glue_other x hfresh] at this

/-! ## Which checks run -/

private theorem mem_ite {p : Prop} [Decidable p] {x : Array α} {r : α} (h : r ∈ (if p then x else #[])) :
    p ∧ r ∈ x := by
  split at h
  · exact ⟨‹_›, h⟩
  · simp at h

private theorem mem_filterMap_ite {xs : Array α} {p : α → Bool} {f : α → β} {r : β} :
    r ∈ xs.filterMap (fun x => if p x then some (f x) else none) ↔ ∃ x ∈ xs, p x ∧ r = f x := by
  simp only [Array.mem_filterMap]
  refine ⟨fun ⟨x, hx, e⟩ => ?_, fun ⟨x, hx, hp, e⟩ => ⟨x, hx, by simp [hp, e]⟩⟩
  split at e
  · exact ⟨x, hx, ‹_›, (Option.some.inj e).symm⟩
  · cases e

private theorem checkInsts_mem {b : Backend Id F V} {r : CheckResult} :
    r ∈ (checkInsts b c).run ↔
      ∃ k, ∃ hk : k < c.insts.size, ∃ a ∈ c.insts[k].assumes, r = (checkInst b c k c.insts[k] a).run := by
  unfold checkInsts
  simp only [bind_eq, run_eq, pure_eq, mapM_id', Array.mem_flatten, Array.mem_map]
  constructor
  · rintro ⟨_, ⟨⟨i, k⟩, hik, rfl⟩, hr⟩
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 hr
    obtain ⟨hk, e⟩ := Array.mem_zipIdx' hik
    have e' : i = c.insts[k]'hk := e
    clear e hik
    subst e'
    exact ⟨k, hk, a, ha, rfl⟩
  · rintro ⟨k, hk, a, ha, rfl⟩
    exact ⟨_, ⟨(c.insts[k], k), Array.mem_zipIdx_iff_getElem?.2 (by simp [hk]), rfl⟩,
      Array.mem_map.2 ⟨a, ha, rfl⟩⟩

private theorem checkRedundancies_mem {b : Backend Id F V} {vacuous : Array Name} {satisfied : Bool}
    {r : CheckResult} :
    r ∈ (checkRedundancies b c vacuous satisfied).run ↔
      (∃ a ∈ c.assumes,
        redundancyAsked (if satisfied then .sat else (consistent b (c.defEqs .redundancy ++ c.assumes)).run) false ∧
        r = (checkRedundant b c (c.assumes.filter (·.1 != a.1)) a).run) ∨
      (∃ q ∈ c.reqs,
        redundancyAsked (if c.reqs.isEmpty || satisfied then .sat
            else (consistent b (c.defEqs .redundancy ++ (c.hyps b ++ c.reqs))).run)
          (vacuous.contains q.1) ∧
        r = (checkRedundant b c (c.hyps b ++ c.reqs.filter (·.1 != q.1)) q).run) := by
  unfold checkRedundancies
  by_cases he : c.reqs.isEmpty <;> cases satisfied <;>
    simp only [bind_eq, run_eq, pure_eq, filterMapM_id', he, if_true, if_false, Bool.false_eq_true,
      Bool.or_true, Bool.or_false, Array.mem_append] <;>
    exact or_congr mem_filterMap_ite mem_filterMap_ite

private theorem checkDets_mem {b : Backend Id F V} {r : CheckResult} :
    r ∈ (checkDets b c).run ↔ ∃ v ∈ c.vars, v.isDet ∧ r = (checkDeterminism b c v.name).run := by
  unfold checkDets
  simp only [bind_eq, run_eq, pure_eq, filterMapM_id']
  exact mem_filterMap_ite

/-- `checkComp`'s results, in order: each selected stage in turn. -/
theorem checkComp_eq (bk : CheckKind → Backend Id F V) (kinds : Array CheckKind) :
    (checkComp bk c kinds).run =
      (if kinds.contains .realizable then #[(checkRealizable (bk .realizable) c).run] else #[]) ++
      (if kinds.contains .inst then (checkInsts (bk .inst) c).run else #[]) ++
      (if kinds.contains .expect then c.expects.map (checkExpect (bk .expect) c · |>.run) else #[]) ++
      (if kinds.contains .cover then c.covers.map (checkCover (bk .cover) c · |>.run) else #[]) ++
      (if kinds.contains .vacuity then c.triggers.map (checkVacuity (bk .vacuity) c · |>.run) else #[]) ++
      (if kinds.contains .redundancy then (checkRedundancies (bk .redundancy) c (vacuousOf
        (if kinds.contains .vacuity then c.triggers.map (checkVacuity (bk .vacuity) c · |>.run) else #[]))
        (satisfiedOf
        (if kinds.contains .vacuity then c.triggers.map (checkVacuity (bk .vacuity) c · |>.run) else #[]))).run
        else #[]) ++
      (if kinds.contains .determinism then (checkDets (bk .determinism) c).run else #[]) ++
      (if kinds.contains .definedness then c.indexes.map (checkDefinedness (bk .definedness) c · |>.run) else #[]) ++
      (if kinds.contains .completeness then (c.tablesOf .completeness).map (checkTable (bk .completeness) c · |>.run)
        else #[]) ++
      (if kinds.contains .disjointness then (c.tablesOf .disjointness).map (checkTable (bk .disjointness) c · |>.run)
        else #[]) ++
      (if kinds.contains .precondition then (c.tablesOf .precondition).map (checkTable (bk .precondition) c · |>.run)
        else #[]) ++
      (if kinds.contains .postcondition then c.posts.map (checkPostcondition (bk .postcondition) c · |>.run)
        else #[]) ++
      (if kinds.contains .reachability then (c.tablesOf .reachability).map (checkReach (bk .reachability) c · |>.run)
        else #[]) := by
  unfold checkComp
  simp only [withApplies_none, withAllApplies_none, bind_eq, run_eq, pure_eq, ifSelected, map_eq, mapM_id']
  split <;> rfl

/-- Every result of `checkComp` is the result of one of the checks, on an
item of the procedure: its calls' own assumptions, its expectations,
cover goals and triggers, the comparison sets of `redundancy`, its `det` variables and its
indexes. `checkComp_eq` says exactly which, and when. -/
theorem checkComp_mem {bk : CheckKind → Backend Id F V} {kinds : Array CheckKind} {r : CheckResult}
    (h : r ∈ (checkComp bk c kinds).run) :
    r = (checkRealizable (bk .realizable) c).run ∨
    (∃ k, ∃ hk : k < c.insts.size, ∃ a ∈ c.insts[k].assumes,
      r = (checkInst (bk .inst) c k c.insts[k] a).run) ∨
    (∃ e ∈ c.expects, r = (checkExpect (bk .expect) c e).run) ∨
    (∃ g ∈ c.covers, r = (checkCover (bk .cover) c g).run) ∨
    (∃ t ∈ c.triggers, r = (checkVacuity (bk .vacuity) c t).run) ∨
    (∃ a ∈ c.assumes, r = (checkRedundant (bk .redundancy) c (c.assumes.filter (·.1 != a.1)) a).run) ∨
    (∃ q ∈ c.reqs,
      r = (checkRedundant (bk .redundancy) c (c.hyps (bk .redundancy) ++ c.reqs.filter (·.1 != q.1)) q).run) ∨
    (∃ v ∈ c.vars, v.isDet ∧ r = (checkDeterminism (bk .determinism) c v.name).run) ∨
    (∃ site ∈ c.indexes, r = (checkDefinedness (bk .definedness) c site).run) ∨
    (∃ t ∈ c.tablesOf .completeness, r = (checkTable (bk .completeness) c t).run) ∨
    (∃ t ∈ c.tablesOf .disjointness, r = (checkTable (bk .disjointness) c t).run) ∨
    (∃ t ∈ c.tablesOf .precondition, r = (checkTable (bk .precondition) c t).run) ∨
    (∃ p ∈ c.posts, r = (checkPostcondition (bk .postcondition) c p).run) ∨
    (∃ t ∈ c.tablesOf .reachability, r = (checkReach (bk .reachability) c t).run) := by
  rw [checkComp_eq] at h
  simp only [Array.mem_append, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · left; simpa using (mem_ite h).2
  · exact .inr (.inl (checkInsts_mem.1 (mem_ite h).2))
  · obtain ⟨e, he, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inl ⟨e, he, rfl⟩))
  · obtain ⟨g, hg, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inl ⟨g, hg, rfl⟩)))
  · obtain ⟨t, ht, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inr (.inl ⟨t, ht, rfl⟩))))
  · rcases checkRedundancies_mem.1 (mem_ite h).2 with ⟨a, ha, -, e⟩ | ⟨q, hq, -, e⟩
    · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨a, ha, e⟩)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨q, hq, e⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (checkDets_mem.1 (mem_ite h).2))))))))
  · obtain ⟨site, hs, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨site, hs, rfl⟩))))))))
  · obtain ⟨t, ht, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, ht, rfl⟩)))))))))
  · obtain ⟨t, ht, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, ht, rfl⟩))))))))))
  · obtain ⟨t, ht, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨t, ht, rfl⟩)))))))))))
  · obtain ⟨p, hp, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨p, hp, rfl⟩))))))))))))
  · obtain ⟨t, ht, rfl⟩ := Array.mem_map.1 (mem_ite h).2
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨t, ht, rfl⟩))))))))))))

/-- Each selected check runs: on the procedure, on each assumption of each
call, each expectation, each cover goal, each trigger, each `det` variable and each index; and
`redundancy` on each assumption and each requirement it is asked about
(`check::redundancy_asked`): not if they are contradictory, nor for a
requirement whose `vacuity` check failed. Whether they are contradictory is
not asked once a `vacuity` check has passed (`satisfiedOf`). -/
theorem checkComp_runs {bk : CheckKind → Backend Id F V} {kinds : Array CheckKind} :
    (kinds.contains .realizable → (checkRealizable (bk .realizable) c).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .inst → ∀ k (hk : k < c.insts.size), ∀ a ∈ c.insts[k].assumes,
      (checkInst (bk .inst) c k c.insts[k] a).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .expect → ∀ e ∈ c.expects, (checkExpect (bk .expect) c e).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .cover → ∀ g ∈ c.covers, (checkCover (bk .cover) c g).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .vacuity → ∀ t ∈ c.triggers,
      (checkVacuity (bk .vacuity) c t).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .redundancy → ∀ a ∈ c.assumes,
      redundancyAsked
        (if satisfiedOf (if kinds.contains .vacuity then c.triggers.map (checkVacuity (bk .vacuity) c · |>.run)
          else #[]) then .sat
        else (consistent (bk .redundancy) (c.defEqs .redundancy ++ c.assumes)).run) false →
      (checkRedundant (bk .redundancy) c (c.assumes.filter (·.1 != a.1)) a).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .redundancy → ∀ q ∈ c.reqs,
      redundancyAsked
        (if c.reqs.isEmpty || satisfiedOf (if kinds.contains .vacuity then
            c.triggers.map (checkVacuity (bk .vacuity) c · |>.run) else #[]) then .sat
          else (consistent (bk .redundancy) (c.defEqs .redundancy ++ (c.hyps (bk .redundancy) ++ c.reqs))).run)
        ((vacuousOf (if kinds.contains .vacuity then c.triggers.map (checkVacuity (bk .vacuity) c · |>.run)
          else #[])).contains q.1) →
      (checkRedundant (bk .redundancy) c (c.hyps (bk .redundancy) ++ c.reqs.filter (·.1 != q.1)) q).run ∈
        (checkComp bk c kinds).run) ∧
    (kinds.contains .determinism → ∀ v ∈ c.vars, v.isDet →
      (checkDeterminism (bk .determinism) c v.name).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .definedness → ∀ site ∈ c.indexes,
      (checkDefinedness (bk .definedness) c site).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .completeness → ∀ t ∈ c.tablesOf .completeness,
      (checkTable (bk .completeness) c t).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .disjointness → ∀ t ∈ c.tablesOf .disjointness,
      (checkTable (bk .disjointness) c t).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .precondition → ∀ t ∈ c.tablesOf .precondition,
      (checkTable (bk .precondition) c t).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .postcondition → ∀ p ∈ c.posts,
      (checkPostcondition (bk .postcondition) c p).run ∈ (checkComp bk c kinds).run) ∧
    (kinds.contains .reachability → ∀ t ∈ c.tablesOf .reachability,
      (checkReach (bk .reachability) c t).run ∈ (checkComp bk c kinds).run) := by
  simp only [checkComp_eq, Array.mem_append]
  refine ⟨fun hk => ?_, fun hk k hk' a ha => ?_, fun hk e he => ?_, fun hk g hg => ?_, fun hk t ht => ?_,
    fun hk a ha hq => ?_, fun hk q hq hr => ?_, fun hk v hv hd => ?_, fun hk site hs => ?_, fun hk t ht => ?_,
    fun hk t ht => ?_, fun hk t ht => ?_, fun hk p hp => ?_, fun hk t ht => ?_⟩
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (Array.mem_singleton.2 rfl))))))))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (checkInsts_mem.2 ⟨k, hk', a, ha, rfl⟩))))))))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (Array.mem_map.2 ⟨e, he, rfl⟩)))))))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (Array.mem_map.2 ⟨g, hg, rfl⟩))))))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (Array.mem_map.2 ⟨t, ht, rfl⟩)))))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (checkRedundancies_mem.2 (.inl ⟨a, ha, hq, rfl⟩)))))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (checkRedundancies_mem.2 (.inr ⟨q, hq, hr, rfl⟩)))))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (checkDets_mem.2 ⟨v, hv, hd, rfl⟩)))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inl (.inr (Array.mem_map.2 ⟨site, hs, rfl⟩))))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inl (.inr (Array.mem_map.2 ⟨t, ht, rfl⟩)))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inl (.inr (Array.mem_map.2 ⟨t, ht, rfl⟩))))
  · simp only [hk, if_true]
    exact .inl (.inl (.inr (Array.mem_map.2 ⟨t, ht, rfl⟩)))
  · simp only [hk, if_true]
    exact .inl (.inr (Array.mem_map.2 ⟨p, hp, rfl⟩))
  · simp only [hk, if_true]
    exact .inr (Array.mem_map.2 ⟨t, ht, rfl⟩)

/-- What `fren` runs for a global expectation, and for a procedure
(`check::applies`). -/
theorem kindsFor_spec :
    kindsFor true = #[.realizable, .inst, .expect, .cover, .vacuity, .definedness, .completeness, .disjointness,
      .precondition, .reachability] ∧
      kindsFor false = CheckKind.all :=
  ⟨rfl, rfl⟩

theorem checkRealizable_kind {b : Backend Id F V} : (checkRealizable b c).run.kind = .realizable := by
  unfold checkRealizable checkRealizableUniversal
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkInst_kind {b : Backend Id F V} {k i a} : (checkInst b c k i a).run.kind = .inst := by
  unfold checkInst
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkExpect_kind {b : Backend Id F V} {e} : (checkExpect b c e).run.kind = .expect := by
  unfold checkExpect
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkCover_kind {b : Backend Id F V} {g} : (checkCover b c g).run.kind = .cover := by
  unfold checkCover
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkVacuity_kind {b : Backend Id F V} {t} : (checkVacuity b c t).run.kind = .vacuity := by
  unfold checkVacuity
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkDeterminism_kind {b : Backend Id F V} {x} : (checkDeterminism b c x).run.kind = .determinism := by
  unfold checkDeterminism
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkDefinedness_kind {b : Backend Id F V} {site} :
    (checkDefinedness b c site).run.kind = .definedness := by
  unfold checkDefinedness
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkTable_kind {b : Backend Id F V} {t : TableSite F} :
    (checkTable b c t).run.kind = t.goal.kind := by
  unfold checkTable
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

theorem checkReach_kind {b : Backend Id F V} {t : TableSite F} :
    (checkReach b c t).run.kind = .reachability := by
  unfold checkReach
  simp only [bind_eq, run_eq, pure_eq]
  repeat' split
  all_goals rfl

/-- Interpretations with the same meaning of formulas and sorts mean the
same by a procedure. -/
private theorem Sound.congr {b b' : Backend Id F V} (s : Sound b c.vars Val) (s' : Sound b' c.vars Val)
    (h : s.den = s'.den ∧ s.HasType = s'.HasType) :
    (∀ ρ, s.Typed ρ ↔ s'.Typed ρ) ∧ (∀ ρ k, s.Admits ρ k ↔ s'.Admits ρ k) ∧
      (∀ ρ, s.Behaves ρ ↔ s'.Behaves ρ) ∧ (∀ site ρ, s.AtSite site ρ ↔ s'.AtSite site ρ) := by
  obtain ⟨hd, ht⟩ := h
  have hA : ∀ ρ k, s.Admits ρ k ↔ s'.Admits ρ k := fun ρ k => by
    simp [Sound.Admits, Sound.Defined, Sound.Possible, hd]
  have hB : ∀ ρ, s.Behaves ρ ↔ s'.Behaves ρ := fun ρ => by simp [Sound.Behaves, hA, hd]
  refine ⟨fun ρ => by simp [Sound.Typed, ht], hA, hB, fun site ρ => ?_⟩
  unfold Sound.AtSite
  split
  · simp [Sound.Defined, hd]
  · exact hA ρ _
  · simp [Sound.Admits, Sound.Defined, Sound.Possible, hd]
  · simp [Sound.Defined, hd]

/-- When every check of a procedure passes, except perhaps `redundancy`,
whose failures are only warnings: it has its mode's realizability meaning
(`Sound.Realizable`: a fixed declaration witness or universal procedure
completion), every call's
assumptions hold, every expectation holds, every cover goal is met by some
behaviour, every trigger can hold, every
`det` variable's check passes, so that `checkDeterminism_pass` applies to it (the
front ends allow `det` only on outputs), every index is in range where it
is evaluated, every question about a table's rows or a `match`'s arms
but reachability holds where it is evaluated, and every arm or row asked
about is taken somewhere the hypotheses of its place, but the constraint
it is in, hold (`Comp.reachHyps`). This is for backends that agree on what formulas and sorts
mean, as the front ends' do (they differ only in the SMT-LIB logic they
declare), and whose definitions realizability can substitute
(`Sound.DefsOk`). And when changing the outputs keeps an environment
`Possible` (as for `realizable_behaves`), and some environment is possible,
some behaviour meets every expectation: they do not hold vacuously. -/
theorem checkComp_pass {bk : CheckKind → Backend Id F V} (s : ∀ k, Sound (bk k) c.vars Val)
    (hsame : ∀ k, (s k).den = (s .realizable).den ∧ (s k).HasType = (s .realizable).HasType)
    (hdefs : (s .realizable).DefsOk)
    (h : ∀ r ∈ (checkComp bk c).run, r.kind ≠ .redundancy → r.verdict = .pass) :
    (s .realizable).Realizable ∧
    (∀ k (hk : k < c.insts.size), ∀ a ∈ c.insts[k].assumes, ∀ ρ, (s .realizable).Typed ρ →
      (s .realizable).Admits ρ k → (s .realizable).den c.insts[k].bindings ρ → (s .realizable).den a.2 ρ) ∧
    (∀ e ∈ c.expects, ∀ ρ, (s .realizable).Typed ρ → (s .realizable).Behaves ρ → (s .realizable).den e.2 ρ) ∧
    (∀ g ∈ c.covers, ∃ ρ, (s .realizable).Typed ρ ∧ (s .realizable).Behaves ρ ∧ (s .realizable).den g.2 ρ) ∧
    (∀ t ∈ c.triggers, ∃ ρ, (s .realizable).Typed ρ ∧ (s .realizable).Behaves ρ ∧ (s .realizable).den t.2 ρ) ∧
    (∀ v ∈ c.vars, v.isDet → (checkDeterminism (bk .determinism) c v.name).run.verdict = .pass) ∧
    (∀ site ∈ c.indexes, ∀ ρ, (s .realizable).Typed ρ → (s .realizable).AtSite site ρ →
      (s .realizable).den site.goal ρ) ∧
    (∀ t ∈ c.tables, t.goal.kind ≠ .reachability → ∀ ρ, (s .realizable).Typed ρ → (s .realizable).AtSite t.site ρ →
      (s .realizable).den t.site.goal ρ) ∧
    (∀ t ∈ c.tablesOf .reachability, ∃ ρ, (s .realizable).Typed ρ ∧
      (s .realizable).Holds (c.reachHyps (bk .reachability) t.site) ρ ∧
      ¬(s .realizable).den t.site.goal ρ) ∧
    ((∀ ρ ρ', OnlyOuts c.vars ρ ρ' → (s .realizable).Possible ρ → (s .realizable).Possible ρ') →
      (∃ ρ, (s .realizable).Typed ρ ∧ (s .realizable).Admits ρ) →
      ∃ ρ, (s .realizable).Typed ρ ∧ (s .realizable).Behaves ρ ∧ ∀ e ∈ c.expects, (s .realizable).den e.2 ρ) := by
  obtain ⟨hr, hi, he, hcv, hv, -, -, hd, hix, hcp, hdj, hpre, -, hrc⟩ :=
    checkComp_runs (c := c) (bk := bk) (kinds := CheckKind.all)
  have all : ∀ k, CheckKind.all.contains k := by intro k; cases k <;> simp +decide [CheckKind.all]
  have pass : ∀ r ∈ (checkComp bk c).run, r.kind ≠ .redundancy → r.verdict = .pass := h
  have hR := checkRealizable_pass (s .realizable) hdefs
    (pass _ (hr (all _)) (by rw [checkRealizable_kind]; intro h; cases h))
  have hE : ∀ e ∈ c.expects, ∀ ρ, (s .realizable).Typed ρ → (s .realizable).Behaves ρ →
      (s .realizable).den e.2 ρ := by
    intro e he' ρ
    have := checkExpect_pass (s .expect) e (pass _ (he (all _) e he') (by rw [checkExpect_kind]; intro h; cases h)) ρ
    obtain ⟨tT, -, tB, -⟩ := Sound.congr (s .expect) (s .realizable) (hsame _)
    simpa only [tT, tB, (hsame _).1] using this
  refine ⟨hR, fun k hk a ha ρ => ?_, hE, fun g hg => ?_, fun t ht => ?_,
    fun v hv' hdet => pass _ (hd (all _) v hv' hdet) (by rw [checkDeterminism_kind]; intro h; cases h),
    fun site hs ρ => ?_, fun t hs hk ρ => ?_, fun t hs => ?_, fun hindep ⟨ρ, ht, hρ⟩ => ?_⟩
  · have := checkInst_pass (s .inst) k _ a (pass _ (hi (all _) k hk a ha) (by rw [checkInst_kind]; intro h; cases h)) ρ
    obtain ⟨tT, tA, -, -⟩ := Sound.congr (s .inst) (s .realizable) (hsame _)
    simpa only [tT, tA, (hsame _).1] using this
  · obtain ⟨ρ, -, ht, hb, hg, -⟩ := checkCover_pass (s .cover) g
      (pass _ (hcv (all _) g hg) (by rw [checkCover_kind]; intro h; cases h))
    obtain ⟨tT, -, tB, -⟩ := Sound.congr (s .cover) (s .realizable) (hsame _)
    exact ⟨ρ, (tT ρ).1 ht, (tB ρ).1 hb, by simpa only [(hsame _).1] using hg⟩
  · have := checkVacuity_pass (s .vacuity) t (pass _ (hv (all _) t ht) (by rw [checkVacuity_kind]; intro h; cases h))
    obtain ⟨tT, -, tB, -⟩ := Sound.congr (s .vacuity) (s .realizable) (hsame _)
    simpa only [tT, tB, (hsame _).1] using this
  · have := checkDefinedness_pass (s .definedness) site
      (pass _ (hix (all _) site hs) (by rw [checkDefinedness_kind]; intro h; cases h)) ρ
    obtain ⟨tT, -, -, tS⟩ := Sound.congr (s .definedness) (s .realizable) (hsame _)
    simpa only [tT, tS, (hsame _).1] using this
  · -- Each question is answered by the check of its kind.
    have hmem : t ∈ c.tablesOf t.goal.kind := Array.mem_filter.2 ⟨hs, by simp⟩
    have hrun : (checkTable (bk t.goal.kind) c t).run ∈ (checkComp bk c).run := by
      cases hg : t.goal <;> rw [hg] at hmem
      · exact hcp (all _) t hmem
      · exact hdj (all _) t hmem
      · exact hpre (all _) t hmem
      · exact absurd (by rw [hg]; rfl) hk
    have := checkTable_pass (s t.goal.kind) t (pass _ hrun (by
      rw [checkTable_kind]; cases t.goal <;> intro h <;> cases h)) ρ
    obtain ⟨tT, -, -, tS⟩ := Sound.congr (s t.goal.kind) (s .realizable) (hsame _)
    simpa only [tT, tS, (hsame _).1] using this
  · obtain ⟨ρ, ht, hρ, hg⟩ := checkReach_pass (s .reachability) t
      (pass _ (hrc (all _) t hs) (by rw [checkReach_kind]; intro h; cases h))
    obtain ⟨tT, -, -, -⟩ := Sound.congr (s .reachability) (s .realizable) (hsame _)
    exact ⟨ρ, (tT ρ).1 ht, by simpa only [Sound.Holds, (hsame _).1] using hρ, by simpa only [(hsame _).1] using hg⟩
  · obtain ⟨ρ', ht', hb⟩ := realizable_behaves (s .realizable) hdefs hindep
      (pass _ (hr (all _)) (by rw [checkRealizable_kind]; intro h; cases h)) ⟨ρ, ht, hρ⟩
    exact ⟨ρ', ht', hb, fun e he' => hE e he' ρ' ht' hb⟩

/-! ## A sound backend

`Sound` can be met, so the theorems above are not vacuous: formulas are
predicates, and the solver is an oracle that always knows the answer, over
environments typed by `ty`. -/

/-- Formulas as predicates on environments, with an all-knowing solver. -/
noncomputable def semBackend (vars : Array VarSig) (Val : Type) (ty : Name → Val → Prop)
    (str : Val → String) : Backend Id (Env Val → Prop) Val :=
  open Classical in
  { query := fun hs g _ => if ∀ ρ, (∀ n, ty n (ρ n)) → (∀ h ∈ hs, h.2 ρ) → g ρ then .unsat else .sat #[]
    falseF := fun _ => False
    notF := fun f ρ => ¬f ρ
    conj := fun fs ρ => ∀ f ∈ fs, f ρ
    existsOutputs := fun f ρ => ∃ ρ', (∀ n, ty n (ρ' n)) ∧ OnlyOuts vars ρ ρ' ∧ f ρ'
    pin := fun n v => some fun ρ => ρ n = v
    -- Values have no variants here.
    pinVariant := fun _ _ => none
    render := fun _ v => str v
    prime := fun f ρ => f (primeEnv vars ρ)
    samePrimed := fun x ρ => ρ x = ρ (primed x)
    -- Formulas are only predicates, which cannot be substituted into, so
    -- `Sound.DefsOk` holds of this backend only without definitions.
    subst := fun _ f => f }

noncomputable def semSound (vars : Array VarSig) (Val : Type) (ty : Name → Val → Prop)
    (hne : ∀ n, ∃ v, ty n v) (hty : ∀ n v, IsCopied vars n → (ty (primed n) v ↔ ty n v))
    (str : Val → String) (hstr : ∀ v v', str v = str v' → v = v') :
    Sound (semBackend vars Val ty str) vars Val where
  den f := f
  value := id
  HasType := ty
  inhabited := hne
  hasType_primed := hty _ _
  query_unsat := by
    intro _ _ _ h
    simp only [semBackend] at h
    split at h
    · assumption
    · cases h
  query_sat := by
    intro _ _ _ _ h
    simp only [semBackend] at h
    split at h
    · cases h
    · next hn =>
      cases h
      simpa using hn
  falseF := fun _ => id
  notF := fun _ => .rfl
  conj := fun _ => .rfl
  existsOutputs := fun _ => .rfl
  pin := by
    intro _ _ _ _ h _
    cases h
    rfl
  variantOf _ := none
  pinVariant := by
    intro _ _ _ _ _ h
    cases h
  prime := fun _ => .rfl
  samePrimed := fun _ => .rfl
  render_inj := fun h _ _ => hstr _ _ h

end Fren.Core
