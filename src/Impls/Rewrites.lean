-- keep-sorted start
import Impls.Lint
import Reqs.Lint
-- keep-sorted end

/-! # Lints over the syntax of the semantics (`Reqs/Lint/Rewrites`)

`overly_complex_bool_expr`, `double_neg` and `int_plus_one` over
`lang::Expr`: each fix agrees with the expression where it fires, and the
linter's rule for `overly_complex_bool_expr`, `Core.overlyComplexRule`,
meets `lint::overly_complex_bool_expr` at `lang::Expr`. Then the laws of
fixing every lint everywhere (`lint::fix_all_laws`), by induction on the
expression, from three facts about each lint where it fires: its fix is
the expression where it does not fire, it agrees, and where the lint fires
within no operand, it fires nowhere within the fix. `Le o o'` says that
`o'` agrees with `o`: `lint::agrees?(o', o)`. -/

open Fren.Lang
open Fren.Generated

namespace RewriteProof
open lang

variable {i : Interp}

/-- `o'` is at least as defined as `o`, and has its outcome where `o` is defined. -/
def Le (o o' : Outcome) : Prop := o = .Undefined ∨ o' = o

theorem Le.refl (o : Outcome) : Le o o := Or.inr rfl

theorem Le.trans {a b c : Outcome} (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with h | rfl
  · exact Or.inl h
  · exact h2

theorem agrees_iff (f o : Outcome) : lint.agrees? f o = true ↔ Le o f := by
  simp [lint.agrees?, Le]

/-- The rows of the table of `overly_complex_bool_expr`: each fix agrees
with the expression, at every outcome of the operands. -/
theorem site_shapes (env : Env) (a b : Expr) :
    Le (eval i env (.Or a (.And a b))) (eval i env a) ∧ Le (eval i env (.Or a (.And b a))) (eval i env a) ∧
    Le (eval i env (.Or (.And a b) a)) (eval i env a) ∧ Le (eval i env (.Or (.And b a) a)) (eval i env a) ∧
    Le (eval i env (.And a (.Or a b))) (eval i env a) ∧ Le (eval i env (.And a (.Or b a))) (eval i env a) ∧
    Le (eval i env (.And (.Or a b) a)) (eval i env a) ∧ Le (eval i env (.And (.Or b a) a)) (eval i env a) ∧
    Le (eval i env (.And a (.Unary .Not a))) (.Defined .False) ∧
    Le (eval i env (.And (.Unary .Not a) a)) (.Defined .False) ∧
    Le (eval i env (.Or a (.Unary .Not a))) (.Defined .True) ∧
    Le (eval i env (.Or (.Unary .Not a) a)) (.Defined .True) := by
  simp only [eval]
  generalize eval i env a = A
  generalize eval i env b = B
  rcases A with v | _ <;> rcases B with w | _ <;> (try cases v) <;> (try cases w) <;> simp [Le, unary_value]

/-- `absorbs_operand?`, without its selectors. -/
theorem absorbs_iff (c : Bool) (k o : Expr) : lint.absorbs_operand? c k o = true ↔
    (c = true ∧ ∃ q, k = .Or o q ∨ k = .Or q o) ∨ (c = false ∧ ∃ q, k = .And o q ∨ k = .And q o) := by
  cases k <;> cases c <;> simp [lint.absorbs_operand?, lang.Expr.Or.x0, lang.Expr.Or.x1, lang.Expr.And.x0,
    lang.Expr.And.x1] <;> grind

theorem drops_iff (c : Bool) (a b : Expr) : lint.drops? c a b = true ↔
    lint.absorbs_operand? c b a = true ∨ lint.absorbs_operand? c a b = true ∨ lint.negates_operand? a b = true ∨
      lint.negates_operand? b a = true := by
  unfold lint.drops?
  rw [decide_eq_true_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem fires_and (a b : Expr) : lint.overly_complex_fires? (.And a b) = lint.drops? true a b := by
  show decide (lint.drops? true a b = true) = _
  cases lint.drops? true a b <;> rfl

theorem fires_or (a b : Expr) : lint.overly_complex_fires? (.Or a b) = lint.drops? false a b := by
  show decide (lint.drops? false a b = true) = _
  cases lint.drops? false a b <;> rfl

/-- The four tests of `drops?`, case by case. -/
macro "drop_cases" a:term:max b:term:max c:term:max : tactic => `(tactic|
  (by_cases h1 : lint.absorbs_operand? $c $b $a = true <;> by_cases h2 : lint.absorbs_operand? $c $a $b = true <;>
    by_cases h3 : lint.negates_operand? $a $b = true <;> by_cases h4 : lint.negates_operand? $b $a = true <;>
    simp only [lint.overly_complex_fires?, lint.overly_complex_fix, lint.drop_fix, lint.drops?, h1, h2, h3, h4,
      if_true, if_false, true_or, or_true, or_false, false_or, decide_true, decide_false, Bool.false_eq_true,
      reduceIte] at *))

/-- Where `overly_complex_bool_expr` fires, its fix is an operand or a literal. -/
theorem overly_fix_shape (e : Expr) (h : lint.overly_complex_fires? e = true) :
    ∃ a b, (e = .And a b ∨ e = .Or a b) ∧
      (lint.overly_complex_fix e = a ∨ lint.overly_complex_fix e = b ∨ ∃ v, lint.overly_complex_fix e = .Literal v) := by
  cases e with
  | And a b => refine ⟨a, b, Or.inl rfl, ?_⟩; drop_cases a b true <;> simp_all
  | Or a b => refine ⟨a, b, Or.inr rfl, ?_⟩; drop_cases a b false <;> simp_all
  | _ => simp [lint.overly_complex_fires?] at h

/-- Where `overly_complex_bool_expr` does not fire, its fix is the expression. -/
theorem overly_fix_unfired (e : Expr) (h : lint.overly_complex_fires? e = false) : lint.overly_complex_fix e = e := by
  cases e with
  | And a b => drop_cases a b true <;> simp_all
  | Or a b => drop_cases a b false <;> simp_all
  | _ => simp [lint.overly_complex_fix]

/-- The fix agrees with the expression where it fires. -/
theorem overly_site (env : Env) (e : Expr) (h : lint.overly_complex_fires? e = true) :
    Le (eval i env e) (eval i env (lint.overly_complex_fix e)) := by
  cases e with
  | And a b =>
    rw [fires_and, drops_iff] at h
    simp only [lint.overly_complex_fix, lint.drop_fix]
    by_cases h1 : lint.absorbs_operand? true b a = true
    · rw [if_pos h1]
      obtain ⟨_, q, rfl | rfl⟩ | ⟨h, _⟩ := (absorbs_iff _ _ _).1 h1
      · exact (site_shapes (i := i) env a q).2.2.2.2.1
      · exact (site_shapes (i := i) env a q).2.2.2.2.2.1
      · simp at h
    rw [if_neg h1]
    by_cases h2 : lint.absorbs_operand? true a b = true
    · rw [if_pos h2]
      obtain ⟨_, q, rfl | rfl⟩ | ⟨h, _⟩ := (absorbs_iff _ _ _).1 h2
      · exact (site_shapes (i := i) env b q).2.2.2.2.2.2.1
      · exact (site_shapes (i := i) env b q).2.2.2.2.2.2.2.1
      · simp at h
    rw [if_neg h2]
    have hn : lint.negates_operand? a b = true ∨ lint.negates_operand? b a = true := by
      rcases h with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact Or.inl h
      · exact Or.inr h
    rw [if_pos hn]
    simp only [lint.negates_operand?, decide_eq_true_eq] at hn
    rcases hn with rfl | rfl
    · exact (site_shapes (i := i) env b b).2.2.2.2.2.2.2.2.2.1
    · exact (site_shapes (i := i) env a a).2.2.2.2.2.2.2.2.1
  | Or a b =>
    rw [fires_or, drops_iff] at h
    simp only [lint.overly_complex_fix, lint.drop_fix]
    by_cases h1 : lint.absorbs_operand? false b a = true
    · rw [if_pos h1]
      obtain ⟨h, _⟩ | ⟨_, q, rfl | rfl⟩ := (absorbs_iff _ _ _).1 h1
      · simp at h
      · exact (site_shapes (i := i) env a q).1
      · exact (site_shapes (i := i) env a q).2.1
    rw [if_neg h1]
    by_cases h2 : lint.absorbs_operand? false a b = true
    · rw [if_pos h2]
      obtain ⟨h, _⟩ | ⟨_, q, rfl | rfl⟩ := (absorbs_iff _ _ _).1 h2
      · simp at h
      · exact (site_shapes (i := i) env b q).2.2.1
      · exact (site_shapes (i := i) env b q).2.2.2.1
    rw [if_neg h2]
    have hn : lint.negates_operand? a b = true ∨ lint.negates_operand? b a = true := by
      rcases h with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact Or.inl h
      · exact Or.inr h
    rw [if_pos hn]
    simp only [lint.negates_operand?, decide_eq_true_eq] at hn
    rcases hn with rfl | rfl
    · exact (site_shapes (i := i) env b b).2.2.2.2.2.2.2.2.2.2.2
    · exact (site_shapes (i := i) env a a).2.2.2.2.2.2.2.2.2.2.1
  | _ => simp [lint.overly_complex_fires?] at h

/-! ### `double_neg` -/

/-- Where `double_neg` does not fire, its fix is the expression. -/
theorem dn_unfired (e : Expr) (h : lint.double_neg_fires? e = false) : lint.double_neg_fix e = e := by
  unfold lint.double_neg_fix; split
  · simp [lint.double_neg_fires?] at h
  · rfl

/-- `- -a` is `a` where `a` is an integer, and undefined elsewhere. -/
theorem dn_site (env : Env) (e : Expr) : Le (eval i env e) (eval i env (lint.double_neg_fix e)) := by
  unfold lint.double_neg_fix; split
  · rename_i a
    simp only [eval]
    generalize eval i env a = A
    rcases A with v | _ <;> (try cases v) <;> simp [Le, unary_value]
  · exact Le.refl _

/-! ### `int_plus_one` -/

theorem ipo_fires_le (a b : Expr) : lint.int_plus_one_fires? (.Binary .Le a b) =
    decide (lint.offset_of a = .PlusOne ∨ lint.offset_of b = .MinusOne) := by
  simp [lint.int_plus_one_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]

theorem ipo_fires_other (e : Expr) (h : ∀ a b, e = .Binary .Le a b → False) : lint.int_plus_one_fires? e = false := by
  cases e with
  | Binary op a b => cases op <;> first | exact absurd rfl (h a b) |
      simp [lint.int_plus_one_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]
  | _ => simp [lint.int_plus_one_fires?]

/-- Where `int_plus_one` does not fire, its fix is the expression. -/
theorem ipo_unfired (e : Expr) (h : lint.int_plus_one_fires? e = false) : lint.int_plus_one_fix e = e := by
  unfold lint.int_plus_one_fix; split
  · rename_i a b
    rw [ipo_fires_le, decide_eq_false_iff_not, not_or] at h
    rw [if_neg h.1, if_neg h.2]
  · rfl

/-- Dropping the offset of an operand drops a `+ 1` or a `- 1`. -/
theorem without_offset_cases (a : Expr) :
    (lint.offset_of a = .PlusOne → ∃ x, lint.without_offset a = x ∧
      (a = .Binary .Add x (.Literal (.Integer 1)) ∨ a = .Binary .Add (.Literal (.Integer 1)) x)) ∧
    (lint.offset_of a = .MinusOne → ∃ x, lint.without_offset a = x ∧ a = .Binary .Sub x (.Literal (.Integer 1))) := by
  cases a with
  | Binary op x y =>
    cases op <;> by_cases hy : lint.one? y = true <;> by_cases hx : lint.one? x = true <;>
      simp_all [lint.offset_of, lint.without_offset, lint.one?]
  | _ => simp [lint.offset_of]

/-- The operands of a comparison of integers, at every outcome. -/
macro "compare_cases" env:term:max x:term:max y:term:max : tactic => `(tactic|
  (simp only [eval]; generalize eval _ $env $x = X; generalize eval _ $env $y = Y
   rcases X with v | _ <;> rcases Y with w | _ <;> (try cases v) <;> (try cases w) <;> simp [binary_value]
   all_goals (congr 1; try exact decide_eq_decide.mpr (by omega))))

theorem lt_plus (env : Env) (x b : Expr) :
    eval i env (.Binary .Lt x b) = eval i env (.Binary .Le (.Binary .Add x (.Literal (.Integer 1))) b) := by
  compare_cases env x b

theorem lt_one_plus (env : Env) (x b : Expr) :
    eval i env (.Binary .Lt x b) = eval i env (.Binary .Le (.Binary .Add (.Literal (.Integer 1)) x) b) := by
  compare_cases env x b

theorem lt_minus (env : Env) (a x : Expr) :
    eval i env (.Binary .Lt a x) = eval i env (.Binary .Le a (.Binary .Sub x (.Literal (.Integer 1)))) := by
  compare_cases env a x

/-- Over the integers, `b + 1 <= a` is `b < a`, and `b <= a - 1` is `b < a`;
elsewhere both are undefined. -/
theorem ipo_site (env : Env) (e : Expr) : eval i env (lint.int_plus_one_fix e) = eval i env e := by
  unfold lint.int_plus_one_fix; split
  · rename_i a b
    split
    · rename_i hp
      obtain ⟨x, hx, rfl | rfl⟩ := (without_offset_cases a).1 hp <;> rw [hx]
      · exact lt_plus env x b
      · exact lt_one_plus env x b
    · split
      · rename_i _ hm
        obtain ⟨x, hx, rfl⟩ := (without_offset_cases b).2 hm
        rw [hx]; exact lt_minus env a x
      · rfl
  · rfl

/-! ### Each lint at the place where it fires -/

theorem fires_at_overly (e : Expr) : lint.fires_at? .OverlyComplexBoolExpr e = lint.overly_complex_fires? e := by
  show decide (lint.overly_complex_fires? e = true) = _
  cases lint.overly_complex_fires? e <;> rfl

theorem fires_at_dn (e : Expr) : lint.fires_at? .DoubleNeg e = lint.double_neg_fires? e := by
  show decide (lint.double_neg_fires? e = true) = _
  cases lint.double_neg_fires? e <;> rfl

theorem fires_at_ipo (e : Expr) : lint.fires_at? .IntPlusOne e = lint.int_plus_one_fires? e := by
  show decide (lint.int_plus_one_fires? e = true) = _
  cases lint.int_plus_one_fires? e <;> rfl

/-- Where a lint does not fire, its fix is the expression
(`lint::fix_at_unfired`). Each new arm of `lint::ExprLint` owes this. -/
theorem fix_at_unfired (l : lint.ExprLint) (e : Expr) (h : lint.fires_at? l e = false) : lint.fix_at l e = e := by
  cases l
  · rw [fires_at_overly] at h; exact overly_fix_unfired e h
  · rw [fires_at_dn] at h; exact dn_unfired e h
  · rw [fires_at_ipo] at h; exact ipo_unfired e h

/-- Each lint's fix agrees with the expression, where it fires and where not
(`lint::fix_at_agrees`). Each new arm of `lint::ExprLint` owes this. -/
theorem site_le (l : lint.ExprLint) (env : Env) (e : Expr) : Le (eval i env e) (eval i env (lint.fix_at l e)) := by
  cases l
  · show Le _ (eval i env (lint.overly_complex_fix e))
    cases h : lint.overly_complex_fires? e
    · rw [overly_fix_unfired e h]; exact Le.refl _
    · exact overly_site env e h
  · exact dn_site env e
  · show Le _ (eval i env (lint.int_plus_one_fix e))
    rw [ipo_site env e]; exact Le.refl _

/-! ### Fixing everywhere -/

theorem db (p q : Bool) : decide ((p || q) = true) = (p || q) := by cases p <;> cases q <;> rfl

theorem bor (p q : Bool) : (p = true ∨ q = true) ↔ (p || q) = true := by cases p <;> cases q <;> simp

/-- `lint::operands_fixed?` at an expression whose form is known: its tests
of each form, by the selectors of that form. -/
macro "operands_simp" : tactic => `(tactic|
  simp only [lint.operands_fixed?, reduceCtorEq, if_false, if_true,
    lang.Expr.Let.x0, lang.Expr.Let.x1, lang.Expr.Let.x2, lang.Expr.Unary.x0, lang.Expr.Unary.x1,
    lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2, lang.Expr.And.x0, lang.Expr.And.x1,
    lang.Expr.Or.x0, lang.Expr.Or.x1, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2,
    lang.Expr.Is.x0, lang.Expr.Is.x1, lang.Expr.Match.x0, lang.Expr.Match.x1, lang.Expr.Match.x2,
    lang.Expr.Match.x3, lang.Expr.Match.x4, lang.Expr.Cons.x0, lang.Expr.Cons.x1, lang.Expr.Construct.x0,
    lang.Expr.Construct.x1, lang.Expr.Project.x0, lang.Expr.Project.x1, lang.Expr.Project.x2,
    lang.Expr.Index.x0, lang.Expr.Index.x1, lang.Expr.Method.x0, lang.Expr.Method.x1, lang.Expr.Method.x2,
    lang.Expr.Count.x0, lang.Expr.Count.x1, lang.Expr.Apply.x0, lang.Expr.Apply.x1, lang.Expr.Apply.x2,
    lang.Expr.Apply.x3, lang.Expr.Call.x0, lang.Expr.Call.x1, lang.Expr.Recur.x0, lang.Expr.Recur.x1])

/-- A lint fires within an expression where it fires on it or within an operand. -/
theorem fires_in_eq (l : lint.ExprLint) (e : Expr) :
    lint.fires_in? l e = (lint.fires_at? l e || !lint.operands_fixed? l e) := by
  cases e <;> simp only [lint.fires_in?] <;> operands_simp <;> (generalize lint.fires_at? l _ = F) <;>
    cases F <;> simp

/-- The operands of a binary form are fixed where each is. -/
theorem operands_two (l : lint.ExprLint) (a b : Expr) :
    (lint.operands_fixed? l (.And a b) = true ∨ lint.operands_fixed? l (.Or a b) = true ∨
      ∃ op, lint.operands_fixed? l (.Binary op a b) = true) →
    lint.fires_in? l a = false ∧ lint.fires_in? l b = false := by
  rintro (h | h | ⟨op, h⟩) <;> revert h <;> operands_simp <;> simp

theorem operands_one (l : lint.ExprLint) (op : UnaryOp) (a : Expr) :
    lint.operands_fixed? l (.Unary op a) = true → lint.fires_in? l a = false := by
  operands_simp; simp

/-- Where the lint fires nowhere within an expression, it fires within no operand. -/
theorem operands_of_clean (l : lint.ExprLint) (e : Expr) (h : lint.fires_in? l e = false) :
    lint.operands_fixed? l e = true := by
  rw [fires_in_eq] at h
  cases h1 : lint.operands_fixed? l e
  · rw [h1] at h; simp at h
  · rfl

/-- Dropping the offset writes the operand, or one of its own operands. -/
theorem without_offset_fixed (l : lint.ExprLint) (a : Expr) (h : lint.fires_in? l a = false) :
    lint.fires_in? l (lint.without_offset a) = false := by
  unfold lint.without_offset; split
  · rename_i x y
    have := operands_two l x y (Or.inr (Or.inr ⟨_, operands_of_clean l _ h⟩))
    split
    · exact this.1
    · split
      · exact this.2
      · exact h
  · rename_i x y
    have := operands_two l x y (Or.inr (Or.inr ⟨_, operands_of_clean l _ h⟩))
    split
    · exact this.1
    · exact h
  · exact h

/-- Where the lint fires within no operand, it fires nowhere within the fix
(`lint::fix_at_fixed`). Each new arm of `lint::ExprLint` owes this. -/
theorem clean_at (l : lint.ExprLint) (e : Expr) (ho : lint.operands_fixed? l e = true) :
    lint.fires_in? l (lint.fix_at l e) = false := by
  cases hf : lint.fires_at? l e
  · rw [fix_at_unfired l e hf, fires_in_eq, hf, ho]; rfl
  cases l
  · rw [fires_at_overly] at hf
    show lint.fires_in? _ (lint.overly_complex_fix e) = false
    obtain ⟨a, b, hab, hfix⟩ := overly_fix_shape e hf
    have hk : lint.fires_in? .OverlyComplexBoolExpr a = false ∧ lint.fires_in? .OverlyComplexBoolExpr b = false := by
      rcases hab with rfl | rfl
      · exact operands_two _ a b (Or.inl ho)
      · exact operands_two _ a b (Or.inr (Or.inl ho))
    rcases hfix with h | h | ⟨v, h⟩ <;> rw [h]
    · exact hk.1
    · exact hk.2
    · have : lint.overly_complex_fires? (.Literal v) = false := by simp [lint.overly_complex_fires?]
      rw [fires_in_eq, fires_at_overly, this]; operands_simp; simp
  · rw [fires_at_dn] at hf
    show lint.fires_in? _ (lint.double_neg_fix e) = false
    unfold lint.double_neg_fix; split
    · exact operands_one _ _ _ (operands_of_clean _ _ (operands_one _ _ _ ho))
    · rename_i hne
      exfalso
      unfold lint.double_neg_fires? at hf
      split at hf
      · exact hne _ rfl
      · simp at hf
  · rw [fires_at_ipo] at hf
    show lint.fires_in? _ (lint.int_plus_one_fix e) = false
    unfold lint.int_plus_one_fix; split
    · rename_i a b
      have ho := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      have hlt (x y : Expr) (hx : lint.fires_in? .IntPlusOne x = false) (hy : lint.fires_in? .IntPlusOne y = false) :
          lint.fires_in? .IntPlusOne (.Binary .Lt x y) = false := by
        rw [fires_in_eq, fires_at_ipo, ipo_fires_other _ (fun _ _ h => by cases h)]; operands_simp; simp [hx, hy]
      split
      · exact hlt _ _ (without_offset_fixed _ _ ho.1) ho.2
      · split
        · exact hlt _ _ ho.1 (without_offset_fixed _ _ ho.2)
        · rename_i h1 h2
          rw [ipo_fires_le, decide_eq_true_eq] at hf
          rcases hf with h | h
          · exact absurd h h1
          · exact absurd h h2
    · rename_i hne
      rw [ipo_fires_other e hne] at hf; cases hf

/-- `lint::fix_all_laws::fixed`. -/
theorem fixed (l : lint.ExprLint) (e : Expr) : lint.fires_in? l (lint.fix_all l e) = false := by
  induction e <;> simp only [lint.fix_all] <;> apply clean_at <;> (try operands_simp) <;> (try simp [*])

/-- `lint::fix_all_laws::unchanged`. -/
theorem unchanged (l : lint.ExprLint) (e : Expr) (h : lint.fires_in? l e = false) : lint.fix_all l e = e := by
  induction e <;> simp only [lint.fires_in?, bor, db, Bool.or_eq_false_iff] at h <;>
    simp only [lint.fix_all] <;> (try simp_all only [true_implies]) <;>
    exact fix_at_unfired l _ (by first | exact h | exact h.1)

theorem idempotent (l : lint.ExprLint) (e : Expr) : lint.fix_all l (lint.fix_all l e) = lint.fix_all l e :=
  unchanged l _ (fixed l e)

/-! ### Fixing everywhere keeps the meaning -/

/-- An operand's outcome as written is undefined, which makes the whole
undefined (`left`), or the fixed operand's is the same (`rw`). -/
macro "operand" ih:term:max env:term:max : tactic => `(tactic|
  (rcases $ih $env with h | h
   case inl => (left; simp [h, unary_value, binary_value, method_value, count_value])
   rw [h]))

/-- Cases on a defined `Bool`, or another outcome. -/
macro "truth_cases" o:term:max : tactic => `(tactic|
  (generalize $o = X; rcases X with v | _ <;> (try rcases v) <;> simp only [] <;> (try exact Le.refl _)))

/-- `lint::fix_all_laws::keeps_meaning`, by evaluation being monotone in the
operands: an operand is evaluated in the same environment as written and
fixed, since `fix_all` leaves a `let`'s definition as it is. -/
theorem keeps (l : lint.ExprLint) (e : Expr) (env : Env) :
    Le (eval i env e) (eval i env (lint.fix_all l e)) := by
  induction e generalizing env <;> simp only [lint.fix_all] <;> refine Le.trans ?_ (site_le l env _)
  case Literal | Var | NoMatch | Nil => exact Le.refl _
  case Let x d b _ ihb => simp only [eval]; exact ihb _
  case Unary op a iha => simp only [eval]; operand iha env; exact Le.refl _
  case Binary op a b iha ihb => simp only [eval]; operand iha env; operand ihb env; exact Le.refl _
  case And a b iha ihb =>
    simp only [eval]; operand iha env; truth_cases (eval i env a); exact ihb env
  case Or a b iha ihb =>
    simp only [eval]; operand iha env; truth_cases (eval i env a); exact ihb env
  case If c t f ihc iht ihf =>
    simp only [eval]; operand ihc env; truth_cases (eval i env c)
    · exact iht env
    · exact ihf env
  case Is s p ihs => simp only [eval]; operand ihs env; exact Le.refl _
  case Match s p g b rest ihs ihg ihb ihr =>
    simp only [eval]; operand ihs env
    generalize eval i env s = S
    rcases S with v | _
    · simp only []
      by_cases hm : matches_value? p v = true
      · simp only [hm, if_true]
        operand ihg (lang.bind p v env)
        truth_cases (eval i (lang.bind p v env) g)
        · exact ihb _
        · exact ihr env
      · simp only [hm]; exact ihr env
    · exact Le.refl _
  case Cons a rest iha ihr => simp only [eval]; operand iha env; operand ihr env; exact Le.refl _
  case Construct c args iha => simp only [eval]; operand iha env; exact Le.refl _
  case Project a c k iha => simp only [eval]; operand iha env; exact Le.refl _
  case Index q k ihq ihk => simp only [eval]; operand ihq env; operand ihk env; exact Le.refl _
  case Method m r args ihr iha => simp only [eval]; operand ihr env; operand iha env; exact Le.refl _
  case Count c args iha => simp only [eval]; operand iha env; exact Le.refl _
  case Apply f args ps body iha ihb =>
    simp only [eval]; operand iha env
    generalize eval i env args = A
    rcases A with v | _
    · exact ihb _
    · exact Le.refl _
  case Call f args iha => simp only [eval]; operand iha env; exact Le.refl _
  case Recur f args iha => simp only [eval]; operand iha env; exact Le.refl _

/-! ### The linter's rule over `lang::Expr` -/

/-- An expression of the semantics as `overly_complex_bool_expr` reads it. -/
def layer : Expr → Fren.Core.BoolLayer Expr
  | .And a b => .and a b
  | .Or a b => .or a b
  | .Unary .Not a => .not a
  | _ => .other

/-- `k` is the negation of an operand of `e`. -/
def negatesOperandOf (e k : Expr) : Bool :=
  match e with
  | .And a b | .Or a b => lint.negates_operand? k a || lint.negates_operand? k b
  | _ => false

/-- `Core.overlyComplexRule` over `lang::Expr`, with `=` for being written the
same, and `n` for whether `nonminimal_bool` rewrites the negation, at an
operand that is the negation of an operand, and `false` at any other: so a
rule that asks about the wrong operand does not meet the procedure. -/
def rule (n : Bool) (e : Expr) : Option (Fren.Core.BoolRule × Fren.Core.Kept) :=
  Fren.Core.overlyComplexRule layer (fun a b => decide (a = b)) (fun k => n && negatesOperandOf e k) e

theorem absorbs_eq (c : Bool) (k o : Expr) :
    Fren.Core.absorbsOperand layer (fun a b => decide (a = b)) c k o = lint.absorbs_operand? c k o := by
  cases k <;> cases c <;> simp [Fren.Core.absorbsOperand, layer, lint.absorbs_operand?, lang.Expr.Or.x0,
    lang.Expr.Or.x1, lang.Expr.And.x0, lang.Expr.And.x1]
  all_goals (rename_i op _; cases op <;> rfl)

theorem negates_eq (k o : Expr) :
    Fren.Core.negatesOperand layer (fun a b => decide (a = b)) k o = lint.negates_operand? k o := by
  cases k <;> simp [Fren.Core.negatesOperand, layer, lint.negates_operand?]
  rename_i op _; cases op <;> simp

end RewriteProof

/-- The core's `Kept` as `lint::Kept`. -/
def toKept : Fren.Core.Kept → lint.Kept
  | .left => .Left
  | .right => .Right
  | .constant => .Constant

/-- The four tests of `drops?`, case by case, in the linter's rule and the
procedure's. -/
macro "linter_cases" a:term:max b:term:max c:term:max : tactic => `(tactic|
  (by_cases h1 : lint.absorbs_operand? $c $b $a = true <;> by_cases h2 : lint.absorbs_operand? $c $a $b = true <;>
    by_cases h3 : lint.negates_operand? $a $b = true <;> by_cases h4 : lint.negates_operand? $b $a = true <;>
    simp only [RewriteProof.rule, RewriteProof.negatesOperandOf, Fren.Core.overlyComplexRule, RewriteProof.layer,
      RewriteProof.absorbs_eq,
      RewriteProof.negates_eq, RewriteProof.fires_and, RewriteProof.fires_or, RewriteProof.drops_iff,
      lint.overly_complex_fix, lint.drop_fix, lint.bool_rule, h1, h2, h3, h4, if_true, if_false, true_or, or_true,
      or_false, false_or, Bool.false_eq_true, reduceIte, iff_true, iff_false, Option.isSome_some,
      Option.isSome_none, Option.elim, forall_const, Bool.not_eq_true, imp_self, true_implies] <;>
    simp [lint.kept_fix, toKept, Fren.Impls.toBoolRule]))

open RewriteProof in
-- Both front ends run `Core.overlyComplexRule` (trusted, and checked by the ui
-- tests); this is it over `lang::Expr`, with `=` for being written the same and
-- `n` for whether `nonminimal_bool` rewrites the negation of an operand, for
-- every expression.
impl overly_complex_bool_expr: lint::overly_complex_bool_expr for (e : lang.Expr) (n : Bool) {
  e := e,
  negation_rewritten? := n,
  fires? := (rule n e).isSome,
  kept := toKept ((rule n e).elim .left (·.2)),
  kind := Fren.Impls.toBoolRule ((rule n e).elim .absorption (·.1)),
} by
  intro e n _
  unfold lint.overly_complex_bool_expr.ensures lint.overly_complex_bool_expr.ensure.rule
    lint.overly_complex_bool_expr.ensure.fix lint.overly_complex_bool_expr.ensure.kind_rule
  cases e with
  | And a b => rw [RewriteProof.fires_and, RewriteProof.drops_iff]; cases n <;> linter_cases a b true
  | Or a b => rw [RewriteProof.fires_or, RewriteProof.drops_iff]; cases n <;> linter_cases a b false
  | Unary op a => cases op <;> simp [rule, Fren.Core.overlyComplexRule, layer, lint.overly_complex_fires?]
  | _ => simp [rule, Fren.Core.overlyComplexRule, layer, lint.overly_complex_fires?]

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operands.
impl overly_complex_keeps_meaning: lint::overly_complex_keeps_meaning for (e : lang.Expr) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.overly_complex_keeps_meaning.ensures lint.overly_complex_keeps_meaning.ensure.keeps_meaning
  intro h
  exact (agrees_iff _ _).2 (overly_site env e h)

open RewriteProof in
-- For every lint, expression, interpretation and environment, by `site_le`.
impl fix_at_agrees: lint::fix_at_agrees for (l : lint.ExprLint) (e : lang.Expr) (i : lang.Interp)
    (env : lang.Env) {
  l := l, e := e, i := i, env := env,
} by
  intro l e i env _
  unfold lint.fix_at_agrees.ensures lint.fix_at_agrees.ensure.agrees
  exact (agrees_iff _ _).2 (site_le l env e)

open RewriteProof in
-- For every lint, expression, interpretation and environment, by induction on the expression.
impl fix_all_laws: lint::fix_all_laws for (l : lint.ExprLint) (e : lang.Expr) (i : lang.Interp) (env : lang.Env) {
  l := l, e := e, i := i, env := env,
} by
  intro l e i env _
  unfold lint.fix_all_laws.ensures lint.fix_all_laws.ensure.fixed lint.fix_all_laws.ensure.unchanged
    lint.fix_all_laws.ensure.idempotent lint.fix_all_laws.ensure.keeps_meaning
  refine ⟨by simp [fixed], fun h => unchanged l e (by simpa using h), idempotent l e, (agrees_iff _ _).2 (keeps l e env)⟩

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operand.
impl double_neg_keeps_meaning: lint::double_neg_keeps_meaning for (e : lang.Expr) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.double_neg_keeps_meaning.ensures lint.double_neg_keeps_meaning.ensure.keeps_meaning
  intro _
  exact (agrees_iff _ _).2 (dn_site env e)

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operands.
impl int_plus_one_keeps_meaning: lint::int_plus_one_keeps_meaning for (e : lang.Expr) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.int_plus_one_keeps_meaning.ensures lint.int_plus_one_keeps_meaning.ensure.exact
  intro _
  simpa using ipo_site env e

open RewriteProof in
-- For every lint and expression, by `clean_at`.
impl fix_at_fixed: lint::fix_at_fixed for (l : lint.ExprLint) (e : lang.Expr) {
  l := l, e := e,
} by
  intro l e _
  unfold lint.fix_at_fixed.ensures lint.fix_at_fixed.ensure.fixed
  intro h
  simpa using clean_at l e (by simpa using h)
