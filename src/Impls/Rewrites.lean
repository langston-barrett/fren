-- keep-sorted start
import Impls.Lint
import Reqs.Lint
-- keep-sorted end

/-! # Lints over the syntax of the semantics (`Reqs/Lint/Rewrites`)

`overly_complex_bool_expr`, `double_neg`, `int_plus_one`, `manual_abs`,
`manual_abs_diff`, `unless_not`, `collapsible_when`, `same_branches`,
`neg_multiply`, `identity_op` and `manual_rem_euclid` over `lang::Expr`:
each fix agrees with the expression where it fires, the last three in an
interpretation whose primitive operations are `usual?`; what the messages
of `eq_op`, `erasing_op` and `modulo_one` say agrees with the expression,
the last two in such an interpretation; and the
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

/-- `eval` one step, with the rule of the form evaluated: `lang::eval` gives
each form but `Match` and `Apply` by a function of its operands' outcomes
(`Reqs/Lang/Semantics#connectives-lists-and-calls`). -/
macro "eval_step" : tactic => `(tactic|
  (simp only [eval]
   try simp only [and_value]
   try simp only [or_value]
   try simp only [if_value]
   try simp only [is_value]
   try simp only [cons_value]
   try simp only [construct_value]
   try simp only [project_value]
   try simp only [index_value]
   try simp only [call_value]))

/-- `o'` is at least as defined as `o`, and has its outcome where `o` is defined. -/
def Le (o o' : Outcome) : Prop := o = .Undefined ∨ o' = o

theorem Le.refl (o : Outcome) : Le o o := Or.inr rfl

theorem Le.trans {a b c : Outcome} (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with h | rfl
  · exact Or.inl h
  · exact h2

/-- A generic function of the syntax decides its `Bool`s classically, since
nothing is known of its type parameter but equality (`Reqs/Generated#computable-definitions`);
at `String`, such a decision is the one by `DecidableEq`. -/
theorem decide_classical (p : Prop) [h : Decidable p] : @decide p (Classical.propDecidable p) = decide p := by
  congr

theorem agrees_iff (f o : Outcome) : lint.agrees? f o = true ↔ Le o f := by
  simp [lint.agrees?, Le]

/-- The rows of the table of `overly_complex_bool_expr`: each fix agrees
with the expression, at every outcome of the operands. -/
theorem site_shapes (env : Env) (a b : Expr String) :
    Le (eval i env (.Or a (.And a b))) (eval i env a) ∧ Le (eval i env (.Or a (.And b a))) (eval i env a) ∧
    Le (eval i env (.Or (.And a b) a)) (eval i env a) ∧ Le (eval i env (.Or (.And b a) a)) (eval i env a) ∧
    Le (eval i env (.And a (.Or a b))) (eval i env a) ∧ Le (eval i env (.And a (.Or b a))) (eval i env a) ∧
    Le (eval i env (.And (.Or a b) a)) (eval i env a) ∧ Le (eval i env (.And (.Or b a) a)) (eval i env a) ∧
    Le (eval i env (.And a (.Unary .Not a))) (.Defined .False) ∧
    Le (eval i env (.And (.Unary .Not a) a)) (.Defined .False) ∧
    Le (eval i env (.Or a (.Unary .Not a))) (.Defined .True) ∧
    Le (eval i env (.Or (.Unary .Not a) a)) (.Defined .True) := by
  eval_step
  generalize eval i env a = A
  generalize eval i env b = B
  rcases A with v | _ <;> rcases B with w | _ <;> (try cases v) <;> (try cases w) <;> simp [Le, unary_value]

/-- `absorbs_operand?`, without its selectors. -/
theorem absorbs_iff (c : Bool) (k o : Expr String) : lint.absorbs_operand? String c k o = true ↔
    (c = true ∧ ∃ q, k = .Or o q ∨ k = .Or q o) ∨ (c = false ∧ ∃ q, k = .And o q ∨ k = .And q o) := by
  cases k <;> cases c <;> simp [lint.absorbs_operand?, lang.Expr.Or.x0, lang.Expr.Or.x1, lang.Expr.And.x0,
    lang.Expr.And.x1] <;> grind

theorem drops_iff (c : Bool) (a b : Expr String) : lint.drops? String c a b = true ↔
    lint.absorbs_operand? String c b a = true ∨ lint.absorbs_operand? String c a b = true ∨ lint.negates_operand? String a b = true ∨
      lint.negates_operand? String b a = true := by
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

theorem fires_and (a b : Expr String) : lint.overly_complex_fires? String (.And a b) = lint.drops? String true a b := by
  show decide (lint.drops? String true a b = true) = _
  cases lint.drops? String true a b <;> rfl

theorem fires_or (a b : Expr String) : lint.overly_complex_fires? String (.Or a b) = lint.drops? String false a b := by
  show decide (lint.drops? String false a b = true) = _
  cases lint.drops? String false a b <;> rfl

/-- The four tests of `drops?`, case by case. -/
macro "drop_cases" a:term:max b:term:max c:term:max : tactic => `(tactic|
  (by_cases h1 : lint.absorbs_operand? String $c $b $a = true <;> by_cases h2 : lint.absorbs_operand? String $c $a $b = true <;>
    by_cases h3 : lint.negates_operand? String $a $b = true <;> by_cases h4 : lint.negates_operand? String $b $a = true <;>
    simp only [lint.overly_complex_fires?, lint.overly_complex_fix, lint.drop_fix, lint.drops?, h1, h2, h3, h4,
      if_true, if_false, true_or, or_true, or_false, false_or, decide_true, decide_false, Bool.false_eq_true,
      reduceIte] at *))

/-- Where `overly_complex_bool_expr` fires, its fix is an operand or a literal. -/
theorem overly_fix_shape (e : Expr String) (h : lint.overly_complex_fires? String e = true) :
    ∃ a b, (e = .And a b ∨ e = .Or a b) ∧
      (lint.overly_complex_fix String e = a ∨ lint.overly_complex_fix String e = b ∨ ∃ v, lint.overly_complex_fix String e = .Literal v) := by
  cases e with
  | And a b => refine ⟨a, b, Or.inl rfl, ?_⟩; drop_cases a b true <;> simp_all
  | Or a b => refine ⟨a, b, Or.inr rfl, ?_⟩; drop_cases a b false <;> simp_all
  | _ => simp [lint.overly_complex_fires?] at h

/-- Where `overly_complex_bool_expr` does not fire, its fix is the expression. -/
theorem overly_fix_unfired (e : Expr String) (h : lint.overly_complex_fires? String e = false) : lint.overly_complex_fix String e = e := by
  cases e with
  | And a b => drop_cases a b true <;> simp_all
  | Or a b => drop_cases a b false <;> simp_all
  | _ => simp [lint.overly_complex_fix]

/-- The fix agrees with the expression where it fires. -/
theorem overly_site (env : Env) (e : Expr String) (h : lint.overly_complex_fires? String e = true) :
    Le (eval i env e) (eval i env (lint.overly_complex_fix String e)) := by
  cases e with
  | And a b =>
    rw [fires_and, drops_iff] at h
    simp only [lint.overly_complex_fix, lint.drop_fix]
    by_cases h1 : lint.absorbs_operand? String true b a = true
    · rw [if_pos h1]
      obtain ⟨_, q, rfl | rfl⟩ | ⟨h, _⟩ := (absorbs_iff _ _ _).1 h1
      · exact (site_shapes (i := i) env a q).2.2.2.2.1
      · exact (site_shapes (i := i) env a q).2.2.2.2.2.1
      · simp at h
    rw [if_neg h1]
    by_cases h2 : lint.absorbs_operand? String true a b = true
    · rw [if_pos h2]
      obtain ⟨_, q, rfl | rfl⟩ | ⟨h, _⟩ := (absorbs_iff _ _ _).1 h2
      · exact (site_shapes (i := i) env b q).2.2.2.2.2.2.1
      · exact (site_shapes (i := i) env b q).2.2.2.2.2.2.2.1
      · simp at h
    rw [if_neg h2]
    have hn : lint.negates_operand? String a b = true ∨ lint.negates_operand? String b a = true := by
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
    by_cases h1 : lint.absorbs_operand? String false b a = true
    · rw [if_pos h1]
      obtain ⟨h, _⟩ | ⟨_, q, rfl | rfl⟩ := (absorbs_iff _ _ _).1 h1
      · simp at h
      · exact (site_shapes (i := i) env a q).1
      · exact (site_shapes (i := i) env a q).2.1
    rw [if_neg h1]
    by_cases h2 : lint.absorbs_operand? String false a b = true
    · rw [if_pos h2]
      obtain ⟨h, _⟩ | ⟨_, q, rfl | rfl⟩ := (absorbs_iff _ _ _).1 h2
      · simp at h
      · exact (site_shapes (i := i) env b q).2.2.1
      · exact (site_shapes (i := i) env b q).2.2.2.1
    rw [if_neg h2]
    have hn : lint.negates_operand? String a b = true ∨ lint.negates_operand? String b a = true := by
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
theorem dn_unfired (e : Expr String) (h : lint.double_neg_fires? String e = false) : lint.double_neg_fix String e = e := by
  unfold lint.double_neg_fix; split
  · simp [lint.double_neg_fires?] at h
  · rfl

/-- `- -a` is `a` where `a` is an integer, and undefined elsewhere. -/
theorem dn_site (env : Env) (e : Expr String) : Le (eval i env e) (eval i env (lint.double_neg_fix String e)) := by
  unfold lint.double_neg_fix; split
  · rename_i a
    eval_step
    generalize eval i env a = A
    rcases A with v | _ <;> (try cases v) <;> simp [Le, unary_value]
  · exact Le.refl _

/-! ### `int_plus_one` -/

theorem ipo_fires_le (a b : Expr String) : lint.int_plus_one_fires? String (.Binary .Le a b) =
    decide (lint.offset_of String a = .PlusOne ∨ lint.offset_of String b = .MinusOne) := by
  simp [lint.int_plus_one_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]

theorem ipo_fires_other (e : Expr String) (h : ∀ a b, e = .Binary .Le a b → False) : lint.int_plus_one_fires? String e = false := by
  cases e with
  | Binary op a b => cases op <;> first | exact absurd rfl (h a b) |
      simp [lint.int_plus_one_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]
  | _ => simp [lint.int_plus_one_fires?]

/-- Where `int_plus_one` does not fire, its fix is the expression. -/
theorem ipo_unfired (e : Expr String) (h : lint.int_plus_one_fires? String e = false) : lint.int_plus_one_fix String e = e := by
  unfold lint.int_plus_one_fix; split
  · rename_i a b
    rw [ipo_fires_le, decide_eq_false_iff_not, not_or] at h
    rw [if_neg h.1, if_neg h.2]
  · rfl

/-- Dropping the offset of an operand drops a `+ 1` or a `- 1`. -/
theorem without_offset_cases (a : Expr String) :
    (lint.offset_of String a = .PlusOne → ∃ x, lint.without_offset String a = x ∧
      (a = .Binary .Add x (.Literal (.Integer 1)) ∨ a = .Binary .Add (.Literal (.Integer 1)) x)) ∧
    (lint.offset_of String a = .MinusOne → ∃ x, lint.without_offset String a = x ∧ a = .Binary .Sub x (.Literal (.Integer 1))) := by
  cases a with
  | Binary op x y =>
    cases op <;> by_cases hy : lint.one? String y = true <;> by_cases hx : lint.one? String x = true <;>
      simp_all [lint.offset_of, lint.without_offset, lint.one?]
  | _ => simp [lint.offset_of]

/-- The operands of a comparison of integers, at every outcome. -/
macro "compare_cases" env:term:max x:term:max y:term:max : tactic => `(tactic|
  (eval_step; generalize eval _ $env $x = X; generalize eval _ $env $y = Y
   rcases X with v | _ <;> rcases Y with w | _ <;> (try cases v) <;> (try cases w) <;> simp [binary_value]
   all_goals (congr 1; try exact decide_eq_decide.mpr (by omega))))

theorem lt_plus (env : Env) (x b : Expr String) :
    eval i env (.Binary .Lt x b) = eval i env (.Binary .Le (.Binary .Add x (.Literal (.Integer 1))) b) := by
  compare_cases env x b

theorem lt_one_plus (env : Env) (x b : Expr String) :
    eval i env (.Binary .Lt x b) = eval i env (.Binary .Le (.Binary .Add (.Literal (.Integer 1)) x) b) := by
  compare_cases env x b

theorem lt_minus (env : Env) (a x : Expr String) :
    eval i env (.Binary .Lt a x) = eval i env (.Binary .Le a (.Binary .Sub x (.Literal (.Integer 1)))) := by
  compare_cases env a x

/-- Over the integers, `b + 1 <= a` is `b < a`, and `b <= a - 1` is `b < a`;
elsewhere both are undefined. -/
theorem ipo_site (env : Env) (e : Expr String) : eval i env (lint.int_plus_one_fix String e) = eval i env e := by
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

/-! ### `manual_abs` and `manual_abs_diff` -/

/-- `abs_negated_then?`, without its selectors. -/
theorem negated_then_imp (c t f : Expr String) (h : lint.abs_negated_then? String c t f = true) :
    ∃ op x, (op = .Lt ∨ op = .Le) ∧ c = .Binary op x (.Literal (.Integer 0)) ∧ t = .Unary .Neg x ∧ f = x := by
  cases c <;> simp [lint.abs_negated_then?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2,
    lint.ordering?, lint.zero?] at h
  rename_i op x z
  cases op <;> simp_all

/-- `abs_negated_else?`, without its selectors. -/
theorem negated_else_imp (c t f : Expr String) (h : lint.abs_negated_else? String c t f = true) :
    ∃ op x, (op = .Lt ∨ op = .Le) ∧ c = .Binary op (.Literal (.Integer 0)) x ∧ t = x ∧ f = .Unary .Neg x := by
  cases c <;> simp [lint.abs_negated_else?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2,
    lint.ordering?, lint.zero?] at h
  rename_i op z x
  cases op <;> simp_all

/-- `abs_diff?`, without its selectors. -/
theorem diff_imp (c t f : Expr String) (h : lint.abs_diff? String c t f = true) :
    ∃ op s m, (op = .Lt ∨ op = .Le) ∧ c = .Binary op s m ∧ t = .Binary .Sub m s ∧ f = .Binary .Sub s m := by
  cases c <;> simp [lint.abs_diff?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2,
    lint.ordering?] at h
  rename_i op s m
  cases op <;> simp_all <;> exact ⟨s, m, by simp⟩

/-- `if x OP 0 then -x else x` is `x.abs`, at every outcome of `x`. -/
theorem abs_then (env : Env) (op : BinaryOp) (hop : op = .Lt ∨ op = .Le) (x : Expr String) :
    eval i env (lint.abs_of String x) = eval i env (.If (.Binary op x (.Literal (.Integer 0))) (.Unary .Neg x) x) := by
  eval_step
  generalize eval i env x = X
  rcases hop with rfl | rfl <;> rcases X with v | _ <;> (try cases v) <;> simp [binary_value, unary_value, method_value]
  all_goals (rename_i n; by_cases h0 : n < 0 <;> by_cases h1 : n ≤ 0 <;> simp [truth, h0, h1] <;> omega)

/-- `if 0 OP x then x else -x` is `x.abs`. -/
theorem abs_else (env : Env) (op : BinaryOp) (hop : op = .Lt ∨ op = .Le) (x : Expr String) :
    eval i env (lint.abs_of String x) = eval i env (.If (.Binary op (.Literal (.Integer 0)) x) x (.Unary .Neg x)) := by
  eval_step
  generalize eval i env x = X
  rcases hop with rfl | rfl <;> rcases X with v | _ <;> (try cases v) <;> simp [binary_value, unary_value, method_value]
  all_goals (rename_i n; by_cases h0 : n < 0 <;> by_cases h1 : 0 < n <;> by_cases h2 : 0 ≤ n <;>
    simp [truth, h0, h1, h2] <;> omega)

/-- `if s OP m then m - s else s - m` is `(m - s).abs`, at every outcome of `s` and `m`. -/
theorem abs_diff (env : Env) (op : BinaryOp) (hop : op = .Lt ∨ op = .Le) (s m : Expr String) :
    eval i env (lint.abs_of String (.Binary .Sub m s)) = eval i env (.If (.Binary op s m) (.Binary .Sub m s) (.Binary .Sub s m)) := by
  eval_step
  generalize eval i env s = S
  generalize eval i env m = M
  rcases hop with rfl | rfl <;> rcases S with v | _ <;> rcases M with w | _ <;> (try cases v) <;> (try cases w) <;>
    simp [binary_value, method_value]
  all_goals (rename_i a b; by_cases h0 : a < b <;> by_cases h1 : a ≤ b <;> by_cases h2 : b - a < 0 <;>
    simp [truth, h0, h1, h2] <;> omega)

theorem ma_fires_if (c t f : Expr String) :
    lint.manual_abs_fires? String (.If c t f) = (lint.abs_negated_then? String c t f || lint.abs_negated_else? String c t f) := by
  simp [lint.manual_abs_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2]

theorem mad_fires_if (c t f : Expr String) : lint.manual_abs_diff_fires? String (.If c t f) = lint.abs_diff? String c t f := by
  simp [lint.manual_abs_diff_fires?]

/-- `manual_abs` fires only on a conditional. -/
theorem ma_fires_other (e : Expr String) (h : ∀ c t f, e = .If c t f → False) : lint.manual_abs_fires? String e = false := by
  cases e with
  | If c t f => exact absurd rfl (h c t f)
  | _ => simp [lint.manual_abs_fires?]

/-- `manual_abs_diff` fires only on a conditional. -/
theorem mad_fires_other (e : Expr String) (h : ∀ c t f, e = .If c t f → False) :
    lint.manual_abs_diff_fires? String e = false := by
  cases e with
  | If c t f => exact absurd rfl (h c t f)
  | _ => simp [lint.manual_abs_diff_fires?]

/-- Where `manual_abs` does not fire, its fix is the expression. -/
theorem ma_unfired (e : Expr String) (h : lint.manual_abs_fires? String e = false) : lint.manual_abs_fix String e = e := by
  unfold lint.manual_abs_fix; split
  · rename_i c t f
    rw [ma_fires_if, Bool.or_eq_false_iff] at h
    rw [if_neg (by simp [h.1]), if_neg (by simp [h.2])]
  · rfl

/-- Where `manual_abs_diff` does not fire, its fix is the expression. -/
theorem mad_unfired (e : Expr String) (h : lint.manual_abs_diff_fires? String e = false) : lint.manual_abs_diff_fix String e = e := by
  unfold lint.manual_abs_diff_fix; split
  · rename_i c t f
    rw [mad_fires_if] at h
    rw [if_neg (by simp [h])]
  · rfl

/-- Where `manual_abs` fires, `x.abs` is the conditional; elsewhere the fix is the expression. -/
theorem ma_site (env : Env) (e : Expr String) : eval i env (lint.manual_abs_fix String e) = eval i env e := by
  unfold lint.manual_abs_fix; split
  · rename_i c t f
    split
    · rename_i h
      obtain ⟨op, x, hop, rfl, rfl, rfl⟩ := negated_then_imp c t f h
      exact abs_then env op hop _
    · split
      · rename_i h
        obtain ⟨op, x, hop, rfl, rfl, rfl⟩ := negated_else_imp c t f h
        exact abs_else env op hop _
      · rfl
  · rfl

/-- Where `manual_abs_diff` fires, `(m - s).abs` is the conditional. -/
theorem mad_site (env : Env) (e : Expr String) : eval i env (lint.manual_abs_diff_fix String e) = eval i env e := by
  unfold lint.manual_abs_diff_fix; split
  · rename_i c t f
    split
    · rename_i h
      obtain ⟨op, s, m, hop, rfl, rfl, rfl⟩ := diff_imp c t f h
      exact abs_diff env op hop s m
    · rfl
  · rfl

/-! ### `unless_not` and `collapsible_when` -/

theorem true_iff (e : Expr String) : lint.true? String e = true ↔ e = .Literal .True := by
  simp [lint.true?]

theorem true_lit : lint.true? String (.Literal .True) = true := by simp [lint.true?]

theorem true_if (c t f : Expr String) : lint.true? String (.If c t f) = false := by simp [lint.true?]

theorem and_not_true {p q : Bool} (h : (p && !q) = true) : p = true ∧ ¬q = true := by
  cases p <;> cases q <;> simp_all

theorem and_not_false {p q : Bool} (h : (p && !q) = false) : ¬(p = true ∧ ¬q = true) := by
  cases p <;> cases q <;> simp_all

theorem and_false {p q : Bool} (h : (p && q) = false) : ¬(p = true ∧ q = true) := by
  cases p <;> cases q <;> simp_all

theorem un_fires_not (a t f : Expr String) :
    lint.unless_not_fires? String (.If (.Unary .Not a) t f) = (lint.true? String t && !lint.true? String f) := by
  simp [lint.unless_not_fires?, lint.true?, decide_classical, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2, lang.Expr.Unary.x0,
    lang.Expr.Unary.x1]

/-- `unless_not` fires only on a conditional whose condition is a negation. -/
theorem un_fires_else (e : Expr String) (h : ∀ a t f, e = .If (.Unary .Not a) t f → False) :
    lint.unless_not_fires? String e = false := by
  cases e with
  | If c t f =>
    cases c with
    | Unary op a =>
      cases op
      · exact absurd rfl (h a t f)
      · simp [lint.unless_not_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2, lang.Expr.Unary.x0,
          lang.Expr.Unary.x1]
    | _ => simp [lint.unless_not_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2]
  | _ => simp [lint.unless_not_fires?]

/-- `unless_not` does not fire on a conditional whose `else` branch is `true`. -/
theorem un_fires_else_true (c t : Expr String) : lint.unless_not_fires? String (.If c t (.Literal .True)) = false := by
  by_cases hc : ∃ a, c = .Unary .Not a
  · obtain ⟨a, rfl⟩ := hc
    rw [un_fires_not, true_lit]; simp
  · exact un_fires_else _ (fun a _ _ h => hc ⟨a, by injection h⟩)

/-- Where `unless_not` does not fire, its fix is the expression. -/
theorem un_unfired (e : Expr String) (h : lint.unless_not_fires? String e = false) : lint.unless_not_fix String e = e := by
  unfold lint.unless_not_fix; split
  · rw [un_fires_not] at h
    rw [if_neg (and_not_false h)]
  · rfl

/-- `if not a then true else d` is `if a then d else true`, at every outcome of `a`. -/
theorem un_site (env : Env) (e : Expr String) : eval i env (lint.unless_not_fix String e) = eval i env e := by
  unfold lint.unless_not_fix; split
  · rename_i a t f
    split
    · rename_i h
      obtain rfl := (true_iff _).1 h.1
      eval_step
      generalize eval i env a = A
      rcases A with v | _ <;> (try cases v) <;> simp
    · rfl
  · rfl

theorem cw_fires_if (c t f : Expr String) :
    lint.collapsible_when_fires? String (.If c t f) = (lint.nested_when? String t f || lint.nested_unless? String t f) := by
  simp only [lint.collapsible_when_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2]
  simp

/-- `collapsible_when` fires only on a conditional. -/
theorem cw_fires_other (e : Expr String) (h : ∀ c t f, e = .If c t f → False) :
    lint.collapsible_when_fires? String e = false := by
  cases e with
  | If c t f => exact absurd rfl (h c t f)
  | _ => simp [lint.collapsible_when_fires?]

theorem nw_if (b d g f : Expr String) : lint.nested_when? String (.If b d g) f = (lint.true? String f && lint.true? String g) := by
  simp [lint.nested_when?, lint.true?, decide_classical]

theorem nu_if (t b u d : Expr String) : lint.nested_unless? String t (.If b u d) = (lint.true? String t && lint.true? String u) := by
  simp [lint.nested_unless?, lint.true?, decide_classical]

theorem nu_if_left (b d g f : Expr String) : lint.nested_unless? String (.If b d g) f = false := by
  simp [lint.nested_unless?, lint.true?]

theorem nw_not_if (t f : Expr String) (h : ∀ b d g, t = .If b d g → False) : lint.nested_when? String t f = false := by
  cases t with
  | If b d g => exact absurd rfl (h b d g)
  | _ => simp [lint.nested_when?]

theorem nu_not_if (t f : Expr String) (h : ∀ b u d, f = .If b u d → False) : lint.nested_unless? String t f = false := by
  cases f with
  | If b u d => exact absurd rfl (h b u d)
  | _ => simp [lint.nested_unless?]

/-- Where `collapsible_when` does not fire, its fix is the expression. -/
theorem cw_unfired (e : Expr String) (h : lint.collapsible_when_fires? String e = false) : lint.collapsible_when_fix String e = e := by
  unfold lint.collapsible_when_fix; split
  · rw [cw_fires_if, nw_if, Bool.or_eq_false_iff] at h
    rw [if_neg (and_false h.1)]
  · rw [cw_fires_if, nu_if, Bool.or_eq_false_iff] at h
    rw [if_neg (and_false h.2)]
  · rfl

/-- `when a, when b, d` is `when a and b, d`, and `unless a, unless b, d` is
`unless a or b, d`, at every outcome of `a`. -/
theorem cw_site (env : Env) (e : Expr String) : eval i env (lint.collapsible_when_fix String e) = eval i env e := by
  unfold lint.collapsible_when_fix; split
  · rename_i a b d g f
    split
    · rename_i h
      obtain rfl := (true_iff _).1 h.1
      obtain rfl := (true_iff _).1 h.2
      eval_step
      generalize eval i env a = A
      rcases A with v | _ <;> (try cases v) <;> simp
    · rfl
  · rename_i a t b u d _
    split
    · rename_i h
      obtain rfl := (true_iff _).1 h.1
      obtain rfl := (true_iff _).1 h.2
      eval_step
      generalize eval i env a = A
      rcases A with v | _ <;> (try cases v) <;> simp
    · rfl
  · rfl

/-! ### `same_branches` and `eq_op` -/

theorem sb_fires_if (c t f : Expr String) : lint.same_branches_fires? String (.If c t f) = decide (t = f) := by
  simp [lint.same_branches_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2]

/-- `same_branches` fires only on a conditional. -/
theorem sb_fires_other (e : Expr String) (h : ∀ c t f, e = .If c t f → False) :
    lint.same_branches_fires? String e = false := by
  cases e with
  | If c t f => exact absurd rfl (h c t f)
  | _ => simp [lint.same_branches_fires?]

/-- Where `same_branches` does not fire, its fix is the expression. -/
theorem sb_unfired (e : Expr String) (h : lint.same_branches_fires? String e = false) :
    lint.same_branches_fix String e = e := by
  unfold lint.same_branches_fix; split
  · rename_i c t f
    rw [sb_fires_if] at h
    rw [if_neg (by simpa using h)]
  · rfl

/-- `if c then a else a` is `a` where `c` is a `Bool`, and undefined elsewhere. -/
theorem sb_site (env : Env) (e : Expr String) : Le (eval i env e) (eval i env (lint.same_branches_fix String e)) := by
  unfold lint.same_branches_fix; split
  · rename_i c t f
    split
    · rename_i h
      subst h
      eval_step
      generalize eval i env c = C
      rcases C with v | _ <;> (try cases v) <;> simp [Le]
    · exact Le.refl _
  · exact Le.refl _

/-- Where `eq_op` fires, what its message says agrees with the expression:
`a = a` is `true`, `a < a` `false`, `a - a` `0`, and `a and a`, `a or a`
and `unless a, a` are `a`, where `a` is well-defined and of the type the
form applies to, and the form is undefined elsewhere. -/
theorem eo_said (env : Env) (e : Expr String) (h : lint.eq_op_fires? String e = true) :
    Le (eval i env e) (eval i env (lint.eq_op_said String e)) := by
  cases e with
  | Binary op a b =>
    cases op <;> simp [lint.eq_op_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1,
      lang.Expr.Binary.x2] at h <;> subst h <;> simp only [lint.eq_op_said] <;> eval_step <;>
      simp only [binary_value] <;> generalize eval i env a = A <;> rcases A with v | _ <;> (try cases v) <;>
      simp [Le, truth]
  | Unary op x =>
    cases op <;> cases x <;> simp [lint.eq_op_fires?, lang.Expr.Unary.x0, lang.Expr.Unary.x1,
      lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2] at h
    rename_i op a b
    cases op <;> simp at h
    subst h; simp only [lint.eq_op_said]; eval_step
    simp only [binary_value]
    generalize eval i env a = A
    rcases A with v | _ <;> simp [Le, truth, unary_value]
  | And a b =>
    simp [lint.eq_op_fires?, lang.Expr.And.x0, lang.Expr.And.x1] at h
    subst h; simp only [lint.eq_op_said]; eval_step
    generalize eval i env a = A
    rcases A with v | _ <;> (try cases v) <;> simp [Le]
  | Or a b =>
    simp [lint.eq_op_fires?, lang.Expr.Or.x0, lang.Expr.Or.x1] at h
    subst h; simp only [lint.eq_op_said]; eval_step
    generalize eval i env a = A
    rcases A with v | _ <;> (try cases v) <;> simp [Le]
  | If c t f =>
    simp [lint.eq_op_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [lint.eq_op_said]
      split
      · rename_i ht
        obtain rfl := (true_iff _).1 ht
        eval_step; simp [Le]
      · eval_step
        generalize eval i env t = C
        rcases C with v | _ <;> (try cases v) <;> simp [Le]
    · simp only [lint.eq_op_said, true_lit, if_true]
      eval_step
      generalize eval i env f = C
      rcases C with v | _ <;> (try cases v) <;> simp [Le]
  | _ => simp [lint.eq_op_fires?] at h

/-! ### Primitive operations, `neg_multiply` and `identity_op` -/

/-- A graph that is `usual?` gives each primitive, where it has a point for
the arguments, a value that meets `usual_point?`. -/
theorem usual_apply (g : Graph) (h : lint.usual? g = true) (f : String) (args : Value) :
    apply g f args = .Undefined ∨ ∃ r, apply g f args = .Defined r ∧ lint.usual_point? f args r = true := by
  induction g with
  | Empty => left; simp [apply]
  | Point h' a r rest ih =>
    simp only [lint.usual?] at h
    have h := of_decide_eq_true h
    simp only [apply]
    split
    · rename_i hm
      obtain ⟨rfl, rfl⟩ := hm
      exact Or.inr ⟨r, rfl, h.1⟩
    · exact ih h.2

/-- A primitive at two values agrees with `r` where every value that
`usual_point?` allows there is `r`. -/
theorem prim_le (hu : lint.usual? i.primitives = true) (f : String) (v w r : Value)
    (hr : ∀ r', lint.usual_point? f (.Cons v (.Cons w .Nil)) r' = true → r' = r) :
    Le (primitive i f v w) (.Defined r) := by
  unfold primitive
  rcases usual_apply _ hu f (.Cons v (.Cons w .Nil)) with h | ⟨r', h, hp⟩
  · exact Or.inl h
  · right; rw [h, hr r' hp]

/-- The value at a point of a `usual?` graph, by `usual_point?`. -/
macro "usual_point" : tactic => `(tactic|
  (intro r h
   simp [lint.usual_point?, lang.Value.Cons.x0, lang.Value.Cons.x1, lang.Value.Integer.x0, Fren.Str.lit] at h
   grind))
macro "usual_text" : tactic => `(tactic|
  (intro r h
   simp [lint.usual_point?, lang.Value.Cons.x0, lang.Value.Cons.x1, lang.Value.Text.x0, Fren.Str.lit] at h
   grind))

/-- `x * -1` and `-1 * x` are `-x`, in an interpretation whose primitives are `usual?`. -/
theorem nm_site (hu : lint.usual? i.primitives = true) (env : Env) (e : Expr String) :
    Le (eval i env e) (eval i env (lint.neg_multiply_fix String e)) := by
  unfold lint.neg_multiply_fix; split
  · rename_i a b
    split
    · rename_i h
      simp [lint.minus_one?] at h; subst h
      eval_step; simp only [unary_value, binary_value]
      generalize eval i env a = A
      rcases A with v | _ <;> (try cases v) <;> simp only [] <;> (try exact Or.inl rfl)
      exact prim_le hu _ _ _ _ (by usual_point)
    · split
      · rename_i _ h
        simp [lint.minus_one?] at h; subst h
        eval_step; simp only [unary_value, binary_value]
        generalize eval i env b = B
        rcases B with v | _ <;> (try cases v) <;> simp only [] <;> (try exact Or.inl rfl)
        exact prim_le hu _ _ _ _ (by usual_point)
      · exact Le.refl _
  · exact Le.refl _

/-- An outcome agrees with another: one of them is undefined, they are the
same, or the first is a primitive that `prim_le` gives. -/
macro "le_finish" : tactic => `(tactic| first
  | exact Or.inl rfl
  | exact Le.refl _
  | (right; simp [append]; done)
  | exact prim_le (by assumption) _ _ _ _ (by usual_point)
  | exact prim_le (by assumption) _ _ _ _ (by usual_text))

/-- Cases on the outcomes of two operands, and their values. -/
macro "outcomes" A:term:max B:term:max : tactic => `(tactic|
  (generalize $A = X; generalize $B = Y
   rcases X with v | _ <;> rcases Y with w | _ <;> (try cases v) <;> (try cases w) <;> simp only [] <;> le_finish))

/-- The flip of `identity_op` agrees where the rewrite it writes does. -/
theorem flip_le (env : Env) (op' : BinaryOp) (a b e : Expr String)
    (h : ∀ y, b = .Unary .Neg y → lint.flips? String b = true →
      Le (eval i env e) (eval i env (.Binary op' a y))) :
    Le (eval i env e) (eval i env (lint.flipped String op' a b e)) := by
  unfold lint.flipped; split
  · rename_i y; split
    · rename_i hf; exact h y rfl hf
    · exact Le.refl _
  · exact Le.refl _

/-- Each identity of `identity_op` agrees, in an interpretation whose
primitives are `usual?`. -/
theorem io_site (hu : lint.usual? i.primitives = true) (env : Env) (e : Expr String) :
    Le (eval i env e) (eval i env (lint.identity_op_fix String e)) := by
  unfold lint.identity_op_fix; split
  · rename_i a b
    split
    · rename_i h; simp [lint.zero?] at h; subst h
      eval_step; simp only [binary_value]; outcomes (eval i env a) (eval i env a)
    · split
      · rename_i _ h; simp [lint.zero?] at h; subst h
        eval_step; simp only [binary_value]; outcomes (eval i env b) (eval i env b)
      · refine flip_le env _ a b _ (fun y hb _ => ?_); subst hb
        eval_step; simp only [binary_value, unary_value]; outcomes (eval i env a) (eval i env y)
  · rename_i a b
    split
    · rename_i h; simp [lint.zero?] at h; subst h
      eval_step; simp only [binary_value]; outcomes (eval i env a) (eval i env a)
    · split
      · exact Le.refl _
      · refine flip_le env _ a b _ (fun y hb _ => ?_); subst hb
        eval_step; simp only [binary_value, unary_value]; outcomes (eval i env a) (eval i env y)
  · rename_i a b
    split
    · rename_i h; simp [lint.one?] at h; subst h
      eval_step; simp only [binary_value]; outcomes (eval i env a) (eval i env a)
    · split
      · rename_i _ h; simp [lint.one?] at h; subst h
        eval_step; simp only [binary_value]; outcomes (eval i env b) (eval i env b)
      · exact Le.refl _
  · rename_i a b
    split
    · rename_i h; simp [lint.one?] at h; subst h
      eval_step; simp only [binary_value]; outcomes (eval i env a) (eval i env a)
    · exact Le.refl _
  · rename_i a b
    split
    · rename_i h; simp [lint.empty_text?] at h; subst h
      eval_step; simp only [binary_value]; outcomes (eval i env a) (eval i env a)
    · split
      · rename_i _ h
        rcases h with h | h
        · simp [lint.empty_text?] at h; subst h
          eval_step; simp only [binary_value]; outcomes (eval i env b) (eval i env b)
        · subst h
          eval_step; simp only [binary_value]; outcomes (eval i env b) (eval i env b)
      · exact Le.refl _
  · exact Le.refl _

/-- `neg_multiply` on a product, without its selectors. -/
theorem nm_fires_mul (a b : Expr String) :
    lint.neg_multiply_fires? String (.Binary .Mul a b) = (lint.minus_one? String a || lint.minus_one? String b) := by
  simp [lint.neg_multiply_fires?, lint.minus_one?, decide_classical, lang.Expr.Binary.x0, lang.Expr.Binary.x1,
    lang.Expr.Binary.x2]

/-- `neg_multiply` fires only on a product. -/
theorem nm_fires_other (e : Expr String) (h : ∀ a b, e = .Binary .Mul a b → False) :
    lint.neg_multiply_fires? String e = false := by
  cases e with
  | Binary op a b =>
    cases op <;> first
      | exact absurd rfl (h a b)
      | simp [lint.neg_multiply_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]
  | _ => simp [lint.neg_multiply_fires?]

/-- Where `neg_multiply` does not fire, its fix is the expression. -/
theorem nm_unfired (e : Expr String) (h : lint.neg_multiply_fires? String e = false) :
    lint.neg_multiply_fix String e = e := by
  unfold lint.neg_multiply_fix; split
  · rename_i a b
    rw [nm_fires_mul, Bool.or_eq_false_iff] at h
    rw [if_neg (by simp [h.2]), if_neg (by simp [h.1])]
  · rfl

/-- `flips?`, without its selectors. -/
theorem flips_iff (b : Expr String) : lint.flips? String b = true ↔
    ∃ y, b = .Unary .Neg y ∧ lint.zero? String y = false ∧ ∀ z, y ≠ .Unary .Neg z := by
  cases b with
  | Unary op y =>
    cases op
    · simp [lint.flips?, lang.Expr.Unary.x0, lang.Expr.Unary.x1]
    · cases y with
      | Unary op' z => cases op' <;> simp [lint.flips?, lang.Expr.Unary.x0, lang.Expr.Unary.x1, lint.zero?]
      | _ => simp [lint.flips?, lang.Expr.Unary.x0, lang.Expr.Unary.x1]
  | _ => simp [lint.flips?]

/-- Where `identity_op` fires on an operation, by its operator. -/
theorem io_fires_bin (op : BinaryOp) (a b : Expr String) : lint.identity_op_fires? String (.Binary op a b) =
    match op with
    | .Add => lint.zero? String b || lint.zero? String a || lint.flips? String b
    | .Sub => lint.zero? String b || (!lint.zero? String a && lint.flips? String b)
    | .Mul => lint.one? String b || lint.one? String a
    | .Div => lint.one? String b
    | .Concat => lint.empty_text? String b || lint.empty_text? String a || decide (a = .Nil)
    | _ => false := by
  cases op <;> simp [lint.identity_op_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2] <;>
    (try rw [Bool.eq_iff_iff]) <;> simp [or_assoc]

/-- Where `identity_op` does not fire, its fix is the expression. -/
theorem io_unfired (e : Expr String) (h : lint.identity_op_fires? String e = false) :
    lint.identity_op_fix String e = e := by
  unfold lint.identity_op_fix; split
  · rename_i a b
    simp only [io_fires_bin, Bool.or_eq_false_iff] at h
    obtain ⟨⟨hb, ha⟩, hf⟩ := h
    rw [if_neg (by simp [hb]), if_neg (by simp [ha])]
    unfold lint.flipped; split
    · rw [if_neg (by simp [hf])]
    · rfl
  · rename_i a b
    simp only [io_fires_bin, Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
    obtain ⟨hb, h2⟩ := h
    rw [if_neg (by simp [hb])]
    split
    · rfl
    · rename_i ha
      unfold lint.flipped; split
      · rcases h2 with h2 | h2
        · exact absurd h2 ha
        · rw [if_neg (by simp [h2])]
      · rfl
  · simp only [io_fires_bin, Bool.or_eq_false_iff] at h
    rw [if_neg (by simp [h.1]), if_neg (by simp [h.2])]
  · simp only [io_fires_bin] at h
    rw [if_neg (by simp [h])]
  · rename_i a b
    simp only [io_fires_bin, Bool.or_eq_false_iff] at h
    obtain ⟨⟨hb, ha⟩, hn⟩ := h
    rw [if_neg (by simp [hb]), if_neg (by simp only [ha, Bool.false_eq_true, false_or]; simpa using hn)]
  · rfl

/-! ### `manual_rem_euclid`, `erasing_op` and `modulo_one` -/

/-- A remainder of two integers in a `usual?` graph: undefined, or an
integer that `usual_remainder?` allows. -/
theorem rem_point (hu : lint.usual? i.primitives = true) (m n : Int) :
    primitive i (Fren.Str.lit "mod") (.Integer m) (.Integer n) = .Undefined ∨
      ∃ r, primitive i (Fren.Str.lit "mod") (.Integer m) (.Integer n) = .Defined (.Integer r) ∧
        lint.usual_remainder? m n r = true := by
  unfold primitive
  rcases usual_apply _ hu (Fren.Str.lit "mod") (.Cons (.Integer m) (.Cons (.Integer n) .Nil)) with h | ⟨r, h, hp⟩
  · exact Or.inl h
  · right
    cases r with
    | Integer k =>
      refine ⟨k, h, ?_⟩
      simpa [lint.usual_point?, lang.Value.Cons.x0, lang.Value.Cons.x1, lang.Value.Integer.x0, Fren.Str.lit] using hp
    | _ => simp [lint.usual_point?, lang.Value.Cons.x0, lang.Value.Cons.x1, lang.Value.Integer.x0, Fren.Str.lit] at hp

/-- The remainder by `n` of a remainder `r` by `n`, plus `n`, is `r`. -/
theorem rem_shift {m n r r' : Int} (hn : n ≠ 0) (h : lint.usual_remainder? m n r = true)
    (h' : lint.usual_remainder? (r + n) n r' = true) : r' = r := by
  simp only [lint.usual_remainder?, decide_eq_true_eq] at h h'
  have h := h hn
  have h' := h' hn
  by_cases hs : n < 0 <;> simp only [hs, if_true, if_false] at h h' <;> omega

/-- `remainder_by?`, without its selectors. -/
theorem rby_iff (r o k : Expr String) : lint.remainder_by? String r o k = true ↔ ∃ a, r = .Binary .Mod a k ∧ o = k := by
  cases r with
  | Binary op a d =>
    cases op <;> simp [lint.remainder_by?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]
  | _ => simp [lint.remainder_by?]

/-- `(a mod k + k) mod k` and `(k + a mod k) mod k` are `a mod k`, in an
interpretation whose primitives are `usual?`. -/
theorem mre_shape (hu : lint.usual? i.primitives = true) (env : Env) (a k : Expr String) (left : Bool) :
    Le (eval i env (.Binary .Mod (if left then .Binary .Add (.Binary .Mod a k) k else .Binary .Add k (.Binary .Mod a k)) k))
      (eval i env (.Binary .Mod a k)) := by
  cases left <;> simp only [if_true, if_false, Bool.false_eq_true] <;> eval_step <;>
  generalize eval i env a = A <;> generalize eval i env k = K <;>
  rcases A with v | _ <;> rcases K with w | _ <;> (try cases v) <;> (try cases w) <;>
    simp only [binary_value] <;> (try exact Or.inl rfl)
  all_goals
    rename_i m n
    by_cases hn : n = 0
    · simp only [hn, if_true]; exact Or.inl rfl
    simp only [hn, if_false]
    rcases rem_point hu m n with h | ⟨r, h, hr⟩
    · rw [h]; exact Or.inl rfl
    rw [h]; simp only [hn, if_false]
    first
      | (rcases rem_point hu (r + n) n with h' | ⟨r', h', hr'⟩
         · rw [h']; exact Or.inl rfl
         · rw [h', rem_shift hn hr hr']; exact Le.refl _)
      | (rcases rem_point hu (n + r) n with h' | ⟨r', h', hr'⟩
         · rw [h']; exact Or.inl rfl
         · rw [Int.add_comm] at hr'; rw [h', rem_shift hn hr hr']; exact Le.refl _)

/-- Where `manual_rem_euclid` fires, its fix agrees, in an interpretation
whose primitives are `usual?`. -/
theorem mre_site (hu : lint.usual? i.primitives = true) (env : Env) (e : Expr String) :
    Le (eval i env e) (eval i env (lint.manual_rem_euclid_fix String e)) := by
  unfold lint.manual_rem_euclid_fix; split
  · rename_i p q k
    split
    · split
      · rename_i _ h
        obtain ⟨a, rfl, rfl⟩ := (rby_iff _ _ _).1 h
        exact mre_shape hu env a q true
      · exact Le.refl _
    · split
      · rename_i _ h
        obtain ⟨a, rfl, rfl⟩ := (rby_iff _ _ _).1 h
        exact mre_shape hu env a p false
      · exact Le.refl _
  · exact Le.refl _

/-- An outcome of `div` or `mod` of `0`, or by `1` or `-1`, by cases on
the divisor, and a primitive that `usual_point?` gives. -/
macro "divisor_cases" B:term:max : tactic => `(tactic|
  (generalize $B = Y
   rcases Y with w | _ <;> (try cases w) <;> simp only [] <;> (try exact Or.inl rfl)
   all_goals (split <;> first | exact Or.inl rfl | exact prim_le (by assumption) _ _ _ _ (by usual_point))))

/-- Where `erasing_op` fires, the value that its message says agrees with
the expression: a product with `0`, and a quotient or remainder of `0`,
are `0`, in an interpretation whose primitives are `usual?`, and a
membership in `[]` is `false`. -/
theorem er_said (hu : lint.usual? i.primitives = true) (env : Env) (e : Expr String)
    (h : lint.erasing_op_fires? String e = true) :
    Le (eval i env e) (eval i env (lint.erasing_op_said String e)) := by
  cases e with
  | Binary op a b =>
    cases op <;> simp [lint.erasing_op_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2,
      lint.zero_dividend?, lint.zero?] at h <;> simp only [lint.erasing_op_said]
    · rcases h with rfl | rfl <;> eval_step <;> simp only [binary_value]
      · outcomes (eval i env b) (eval i env b)
      · outcomes (eval i env a) (eval i env a)
    · rcases h with rfl | rfl <;> eval_step <;> simp only [binary_value, unary_value] <;> divisor_cases (eval i env b)
    · rcases h with rfl | rfl <;> eval_step <;> simp only [binary_value, unary_value] <;> divisor_cases (eval i env b)
    · subst h; eval_step; simp only [binary_value]
      generalize eval i env a = A
      rcases A with v | _ <;> simp [Le, lang.element?, lang.truth]
  | _ => simp [lint.erasing_op_fires?] at h

/-- Where `modulo_one` fires, the remainder is `0`, in an interpretation
whose primitives are `usual?`. -/
theorem mo_said (hu : lint.usual? i.primitives = true) (env : Env) (e : Expr String)
    (h : lint.modulo_one_fires? String e = true) :
    Le (eval i env e) (eval i env (.Literal (.Integer 0))) := by
  cases e with
  | Binary op a b =>
    cases op <;> simp [lint.modulo_one_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2,
      lint.one?, lint.minus_one?] at h
    rcases h with rfl | rfl <;> eval_step <;> simp only [binary_value, unary_value] <;>
      generalize eval i env a = A <;> rcases A with v | _ <;> (try cases v) <;> simp only [] <;>
      (try exact Or.inl rfl) <;> exact prim_le hu _ _ _ _ (by usual_point)
  | _ => simp [lint.modulo_one_fires?] at h

/-- `manual_rem_euclid` on a remainder of a sum, without its selectors. -/
theorem mre_fires_mod (p q k : Expr String) : lint.manual_rem_euclid_fires? String (.Binary .Mod (.Binary .Add p q) k) =
    (if lint.remainder? String p = true then lint.remainder_by? String p q k else lint.remainder_by? String q p k) := by
  simp only [lint.manual_rem_euclid_fires?]
  split <;> simp

/-- `manual_rem_euclid` fires only on a remainder of a sum. -/
theorem mre_fires_other (e : Expr String) (h : ∀ p q k, e = .Binary .Mod (.Binary .Add p q) k → False) :
    lint.manual_rem_euclid_fires? String e = false := by
  unfold lint.manual_rem_euclid_fires?
  split
  · rename_i p q k; exact absurd rfl (h p q k)
  · rfl

/-- Where `manual_rem_euclid` does not fire, its fix is the expression. -/
theorem mre_unfired (e : Expr String) (h : lint.manual_rem_euclid_fires? String e = false) :
    lint.manual_rem_euclid_fix String e = e := by
  unfold lint.manual_rem_euclid_fix; split
  · rename_i p q k
    rw [mre_fires_mod] at h
    split <;> rename_i hp <;> simp only [hp, if_true, if_false, Bool.false_eq_true] at h <;> simp [h]
  · rfl

/-! ### The language's own primitives -/

/-- The remainder by a positive `n` of an `m` within `n` of the range from `0` to `n`. -/
theorem emod_window (m n : Int) (_hn : 0 < n) :
    (0 ≤ m ∧ m < n → m % n = m) ∧ (n ≤ m ∧ m < n + n → m % n = m - n) ∧ (-n ≤ m ∧ m < 0 → m % n = m + n) := by
  refine ⟨fun h => Int.emod_eq_of_lt h.1 h.2, fun h => ?_, fun h => ?_⟩
  · have e : m = (m - n) + n * 1 := by omega
    rw [e, Int.add_mul_emod_self_left]; rw [← e]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · have e : m = (m + n) + n * (-1) := by omega
    rw [e, Int.add_mul_emod_self_left]; rw [← e]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- The language's own products, quotients and remainders meet
`usual_point?` at every point. No check of Fren states this, since the
product is not linear; `lint::usual_language` checks the linear points. -/
theorem usual_language_points (m n : Int) :
    lint.usual_point? (Fren.Str.lit "*") (.Cons (.Integer m) (.Cons (.Integer n) .Nil)) (.Integer (m * n)) = true ∧
    lint.usual_point? (Fren.Str.lit "div") (.Cons (.Integer m) (.Cons (.Integer n) .Nil)) (.Integer (m / n)) = true ∧
    lint.usual_point? (Fren.Str.lit "mod") (.Cons (.Integer m) (.Cons (.Integer n) .Nil)) (.Integer (m % n)) = true := by
  simp only [lint.usual_point?, lint.usual_product?, lint.usual_remainder?, lang.Value.Cons.x0, lang.Value.Cons.x1,
    lang.Value.Integer.x0, Fren.Str.lit]
  refine ⟨?_, ?_, ?_⟩ <;> simp
  · refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · by_cases h : n = 1 <;> simp [h]
    · by_cases h : m = 1 <;> simp [h]
    · by_cases h : n = -1 <;> simp [h]
    · by_cases h : m = -1 <;> simp [h]
    · by_cases h : m = 0 <;> by_cases h' : n = 0 <;> simp [h, h']
  · exact ⟨by by_cases h : n = 1 <;> simp [h], by by_cases h : m = 0 <;> simp [h]⟩
  · by_cases hn : n = 0
    · exact Or.inl hn
    right
    generalize hb : (if n < 0 then -n else n) = b
    have hpos : 0 < b := by subst hb; split <;> omega
    have hm : m % n = m % b := by subst hb; split <;> simp [Int.emod_neg]
    have w := emod_window m b hpos
    have h0 := Int.emod_nonneg m (show b ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos m hpos
    rw [hm]
    generalize m % b = r at w h0 h1 ⊢
    omega

/-- So do its concatenations of strings. -/
theorem usual_language_text (s t : String) :
    lint.usual_point? (Fren.Str.lit "++") (.Cons (.Text s) (.Cons (.Text t) .Nil)) (.Text (s ++ t)) = true := by
  simp [lint.usual_point?, lang.Value.Cons.x0, lang.Value.Cons.x1, lang.Value.Text.x0, Fren.Str.lit]

-- The language's products, quotients and remainders are `Int.mul`,
-- `Int.ediv` and `Int.emod`, by `usual_language_points`.
impl usual_primitives: lint::usual_primitives for (m n : Int) (s t : String) {
  m := m, n := n, s := s, t := t,
  product := m * n,
  quotient := m / n,
  remainder := m % n,
} by
  intro m n s t _
  obtain ⟨hp, hq, hr⟩ := usual_language_points m n
  unfold lint.usual_primitives.ensures lint.usual_primitives.ensure.times lint.usual_primitives.ensure.divides
    lint.usual_primitives.ensure.modulo
  simp [lint.integers, hp, hq, hr]

/-! ### Each lint at the place where it fires -/

theorem fires_at_overly (e : Expr String) : lint.fires_at? String .OverlyComplexBoolExpr e = lint.overly_complex_fires? String e := by
  show decide (lint.overly_complex_fires? String e = true) = _
  cases lint.overly_complex_fires? String e <;> rfl

theorem fires_at_dn (e : Expr String) : lint.fires_at? String .DoubleNeg e = lint.double_neg_fires? String e := by
  show decide (lint.double_neg_fires? String e = true) = _
  cases lint.double_neg_fires? String e <;> rfl

theorem fires_at_ipo (e : Expr String) : lint.fires_at? String .IntPlusOne e = lint.int_plus_one_fires? String e := by
  show decide (lint.int_plus_one_fires? String e = true) = _
  cases lint.int_plus_one_fires? String e <;> rfl

theorem fires_at_ma (e : Expr String) : lint.fires_at? String .ManualAbs e = lint.manual_abs_fires? String e := by
  show decide (lint.manual_abs_fires? String e = true) = _
  cases lint.manual_abs_fires? String e <;> rfl

theorem fires_at_mad (e : Expr String) : lint.fires_at? String .ManualAbsDiff e = lint.manual_abs_diff_fires? String e := by
  show decide (lint.manual_abs_diff_fires? String e = true) = _
  cases lint.manual_abs_diff_fires? String e <;> rfl

theorem fires_at_un (e : Expr String) : lint.fires_at? String .UnlessNot e = lint.unless_not_fires? String e := by
  show decide (lint.unless_not_fires? String e = true) = _
  cases lint.unless_not_fires? String e <;> rfl

theorem fires_at_cw (e : Expr String) : lint.fires_at? String .CollapsibleWhen e = lint.collapsible_when_fires? String e := by
  show decide (lint.collapsible_when_fires? String e = true) = _
  cases lint.collapsible_when_fires? String e <;> rfl

theorem fires_at_sb (e : Expr String) : lint.fires_at? String .SameBranches e = lint.same_branches_fires? String e := by
  show decide (lint.same_branches_fires? String e = true) = _
  cases lint.same_branches_fires? String e <;> rfl

theorem fires_at_nm (e : Expr String) : lint.fires_at? String .NegMultiply e = lint.neg_multiply_fires? String e := by
  show decide (lint.neg_multiply_fires? String e = true) = _
  cases lint.neg_multiply_fires? String e <;> rfl

theorem fires_at_io (e : Expr String) : lint.fires_at? String .IdentityOp e = lint.identity_op_fires? String e := by
  show decide (lint.identity_op_fires? String e = true) = _
  cases lint.identity_op_fires? String e <;> rfl

theorem fires_at_mre (e : Expr String) :
    lint.fires_at? String .ManualRemEuclid e = lint.manual_rem_euclid_fires? String e := by
  show decide (lint.manual_rem_euclid_fires? String e = true) = _
  cases lint.manual_rem_euclid_fires? String e <;> rfl

/-- `fits?` of a lint whose fix rests on the primitive operations: they are `usual?`. -/
theorem fits_usual (l : lint.ExprLint) (hl : l = .NegMultiply ∨ l = .IdentityOp ∨ l = .ManualRemEuclid)
    (h : lint.fits? l i = true) : lint.usual? i.primitives = true := by
  rcases hl with rfl | rfl | rfl <;> simpa [lint.fits?, lint.uses_primitives?] using h

/-- Where a lint does not fire, its fix is the expression
(`lint::fix_at_unfired`). Each new arm of `lint::ExprLint` owes this. -/
theorem fix_at_unfired (l : lint.ExprLint) (e : Expr String) (h : lint.fires_at? String l e = false) : lint.fix_at String l e = e := by
  cases l
  · rw [fires_at_overly] at h; exact overly_fix_unfired e h
  · rw [fires_at_dn] at h; exact dn_unfired e h
  · rw [fires_at_ipo] at h; exact ipo_unfired e h
  · rw [fires_at_ma] at h; exact ma_unfired e h
  · rw [fires_at_mad] at h; exact mad_unfired e h
  · rw [fires_at_un] at h; exact un_unfired e h
  · rw [fires_at_cw] at h; exact cw_unfired e h
  · rw [fires_at_sb] at h; exact sb_unfired e h
  · rw [fires_at_nm] at h; exact nm_unfired e h
  · rw [fires_at_io] at h; exact io_unfired e h
  · rw [fires_at_mre] at h; exact mre_unfired e h

/-- Each lint's fix agrees with the expression, where it fires and where not
(`lint::fix_at_agrees`). Each new arm of `lint::ExprLint` owes this. -/
theorem site_le (l : lint.ExprLint) (env : Env) (e : Expr String) (hl : lint.fits? l i = true) :
    Le (eval i env e) (eval i env (lint.fix_at String l e)) := by
  cases l
  · show Le _ (eval i env (lint.overly_complex_fix String e))
    cases h : lint.overly_complex_fires? String e
    · rw [overly_fix_unfired e h]; exact Le.refl _
    · exact overly_site env e h
  · exact dn_site env e
  · show Le _ (eval i env (lint.int_plus_one_fix String e))
    rw [ipo_site env e]; exact Le.refl _
  · show Le _ (eval i env (lint.manual_abs_fix String e))
    rw [ma_site env e]; exact Le.refl _
  · show Le _ (eval i env (lint.manual_abs_diff_fix String e))
    rw [mad_site env e]; exact Le.refl _
  · show Le _ (eval i env (lint.unless_not_fix String e))
    rw [un_site env e]; exact Le.refl _
  · show Le _ (eval i env (lint.collapsible_when_fix String e))
    rw [cw_site env e]; exact Le.refl _
  · exact sb_site env e
  · exact nm_site (fits_usual _ (Or.inl rfl) hl) env e
  · exact io_site (fits_usual _ (Or.inr (Or.inl rfl)) hl) env e
  · exact mre_site (fits_usual _ (Or.inr (Or.inr rfl)) hl) env e

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
theorem fires_in_eq (l : lint.ExprLint) (e : Expr String) :
    lint.fires_in? l e = (lint.fires_at? String l e || !lint.operands_fixed? l e) := by
  cases e <;> simp only [lint.fires_in?] <;> operands_simp <;> (generalize lint.fires_at? String l _ = F) <;>
    cases F <;> simp

/-- The operands of a binary form are fixed where each is. -/
theorem operands_two (l : lint.ExprLint) (a b : Expr String) :
    (lint.operands_fixed? l (.And a b) = true ∨ lint.operands_fixed? l (.Or a b) = true ∨
      ∃ op, lint.operands_fixed? l (.Binary op a b) = true) →
    lint.fires_in? l a = false ∧ lint.fires_in? l b = false := by
  rintro (h | h | ⟨op, h⟩) <;> revert h <;> operands_simp <;> simp

theorem operands_one (l : lint.ExprLint) (op : UnaryOp) (a : Expr String) :
    lint.operands_fixed? l (.Unary op a) = true → lint.fires_in? l a = false := by
  operands_simp; simp

theorem operands_if (l : lint.ExprLint) (c t f : Expr String) :
    lint.operands_fixed? l (.If c t f) = true →
    lint.fires_in? l c = false ∧ lint.fires_in? l t = false ∧ lint.fires_in? l f = false := by
  operands_simp; simp; exact fun hc ht hf => ⟨hc, ht, hf⟩

/-- Where the lint fires nowhere within an expression, it fires within no operand. -/
theorem operands_of_clean (l : lint.ExprLint) (e : Expr String) (h : lint.fires_in? l e = false) :
    lint.operands_fixed? l e = true := by
  rw [fires_in_eq] at h
  cases h1 : lint.operands_fixed? l e
  · rw [h1] at h; simp at h
  · rfl

/-- Dropping the offset writes the operand, or one of its own operands. -/
theorem without_offset_fixed (l : lint.ExprLint) (a : Expr String) (h : lint.fires_in? l a = false) :
    lint.fires_in? l (lint.without_offset String a) = false := by
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

/-- A call of `abs` is fixed where its receiver is, and the lint fires neither
on the call nor on `Nil`. -/
theorem abs_of_fixed (l : lint.ExprLint) (x : Expr String) (hx : lint.fires_in? l x = false)
    (h : lint.fires_at? String l (lint.abs_of String x) = false) (hn : lint.fires_at? String l .Nil = false) :
    lint.fires_in? l (lint.abs_of String x) = false := by
  have hN : lint.fires_in? l .Nil = false := by rw [fires_in_eq, hn]; operands_simp; rfl
  rw [fires_in_eq, h]; simp only [lint.abs_of]; operands_simp; simp [hx, hN]

/-- Where the lint fires nowhere within an expression, it does not fire on it. -/
theorem at_of_clean (l : lint.ExprLint) (e : Expr String) (h : lint.fires_in? l e = false) : lint.fires_at? String l e = false := by
  rw [fires_in_eq] at h
  cases h1 : lint.fires_at? String l e
  · rfl
  · rw [h1] at h; simp at h

/-- Where the lint fires within no operand, it fires nowhere within the fix
(`lint::fix_at_fixed`). Each new arm of `lint::ExprLint` owes this. -/
theorem clean_at (l : lint.ExprLint) (e : Expr String) (ho : lint.operands_fixed? l e = true) :
    lint.fires_in? l (lint.fix_at String l e) = false := by
  cases hf : lint.fires_at? String l e
  · rw [fix_at_unfired l e hf, fires_in_eq, hf, ho]; rfl
  cases l
  · rw [fires_at_overly] at hf
    show lint.fires_in? _ (lint.overly_complex_fix String e) = false
    obtain ⟨a, b, hab, hfix⟩ := overly_fix_shape e hf
    have hk : lint.fires_in? .OverlyComplexBoolExpr a = false ∧ lint.fires_in? .OverlyComplexBoolExpr b = false := by
      rcases hab with rfl | rfl
      · exact operands_two _ a b (Or.inl ho)
      · exact operands_two _ a b (Or.inr (Or.inl ho))
    rcases hfix with h | h | ⟨v, h⟩ <;> rw [h]
    · exact hk.1
    · exact hk.2
    · have : lint.overly_complex_fires? String (.Literal v) = false := by simp [lint.overly_complex_fires?]
      rw [fires_in_eq, fires_at_overly, this]; operands_simp; simp
  · rw [fires_at_dn] at hf
    show lint.fires_in? _ (lint.double_neg_fix String e) = false
    unfold lint.double_neg_fix; split
    · exact operands_one _ _ _ (operands_of_clean _ _ (operands_one _ _ _ ho))
    · rename_i hne
      exfalso
      unfold lint.double_neg_fires? at hf
      split at hf
      · exact hne _ rfl
      · simp at hf
  · rw [fires_at_ipo] at hf
    show lint.fires_in? _ (lint.int_plus_one_fix String e) = false
    unfold lint.int_plus_one_fix; split
    · rename_i a b
      have ho := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      have hlt (x y : Expr String) (hx : lint.fires_in? .IntPlusOne x = false) (hy : lint.fires_in? .IntPlusOne y = false) :
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
  · rw [fires_at_ma] at hf
    show lint.fires_in? _ (lint.manual_abs_fix String e) = false
    have hm (x : Expr String) (hx : lint.fires_in? .ManualAbs x = false) :
        lint.fires_in? .ManualAbs (lint.abs_of String x) = false :=
      abs_of_fixed _ x hx (by rw [fires_at_ma]; rfl) (by rw [fires_at_ma]; rfl)
    revert ho hf
    unfold lint.manual_abs_fix; split
    · rename_i c t f
      intro ho hf
      have ho := operands_if _ c t f ho
      split
      · exact hm _ ho.2.2
      · split
        · exact hm _ ho.2.1
        · rename_i h1 h2
          rw [ma_fires_if, Bool.or_eq_true] at hf
          rcases hf with h | h
          · exact absurd h h1
          · exact absurd h h2
    · rename_i hne
      intro _ hf
      rw [ma_fires_other e hne] at hf; cases hf
  · rw [fires_at_mad] at hf
    show lint.fires_in? _ (lint.manual_abs_diff_fix String e) = false
    revert ho hf
    unfold lint.manual_abs_diff_fix; split
    · rename_i c t f
      intro ho hf
      have ho := operands_if _ c t f ho
      split
      · exact abs_of_fixed _ _ ho.2.1 (by rw [fires_at_mad]; rfl) (by rw [fires_at_mad]; rfl)
      · rename_i h1
        rw [mad_fires_if] at hf
        exact absurd hf h1
    · rename_i hne
      intro _ hf
      rw [mad_fires_other e hne] at hf; cases hf
  · rw [fires_at_un] at hf
    show lint.fires_in? _ (lint.unless_not_fix String e) = false
    revert ho hf
    unfold lint.unless_not_fix; split
    · rename_i a t f
      intro ho hf
      obtain ⟨hc, ht, hf'⟩ := operands_if _ _ _ _ ho
      have ha := operands_one _ _ _ (operands_of_clean _ _ hc)
      split
      · rename_i h
        obtain rfl := (true_iff _).1 h.1
        rw [fires_in_eq, fires_at_un, un_fires_else_true]; operands_simp; simp [ha, hf', ht]
      · rename_i h
        rw [un_fires_not] at hf
        exact absurd (and_not_true hf) h
    · rename_i hne
      intro _ hf
      rw [un_fires_else e hne] at hf; cases hf
  · rw [fires_at_cw] at hf
    show lint.fires_in? _ (lint.collapsible_when_fix String e) = false
    have hlit : lint.fires_in? .CollapsibleWhen (.Literal .True) = false := by
      rw [fires_in_eq, fires_at_cw, cw_fires_other _ (fun _ _ _ h => by cases h)]; operands_simp; rfl
    have hbin (k a b : Expr String) (hk : k = .And a b ∨ k = .Or a b) (ha : lint.fires_in? .CollapsibleWhen a = false)
        (hb : lint.fires_in? .CollapsibleWhen b = false) : lint.fires_in? .CollapsibleWhen k = false := by
      rw [fires_in_eq, fires_at_cw, cw_fires_other _ (fun _ _ _ h => by rcases hk with rfl | rfl <;> cases h)]
      rcases hk with rfl | rfl <;> operands_simp <;> simp [ha, hb]
    revert ho hf
    unfold lint.collapsible_when_fix; split
    · rename_i a b d g f
      intro ho hf
      obtain ⟨ha, hi, _⟩ := operands_if _ _ _ _ ho
      obtain ⟨hb, hd, _⟩ := operands_if _ _ _ _ (operands_of_clean _ _ hi)
      have hni : lint.collapsible_when_fires? String (.If b d g) = false := by
        rw [← fires_at_cw]; exact at_of_clean _ _ hi
      split
      · rename_i h
        obtain rfl := (true_iff _).1 h.1
        obtain rfl := (true_iff _).1 h.2
        have : lint.collapsible_when_fires? String (.If (.And a b) d (.Literal .True)) = false := by
          rw [cw_fires_if] at hni ⊢; exact hni
        rw [fires_in_eq, fires_at_cw, this]; operands_simp
        simp [hbin _ a b (Or.inl rfl) ha hb, hd, hlit]
      · rename_i h
        rw [cw_fires_if, nw_if, nu_if_left, Bool.or_false, Bool.and_eq_true] at hf
        exact absurd hf h
    · rename_i a t b u d hne
      intro ho hf
      obtain ⟨ha, _, hi⟩ := operands_if _ _ _ _ ho
      obtain ⟨hb, _, hd⟩ := operands_if _ _ _ _ (operands_of_clean _ _ hi)
      have hni : lint.collapsible_when_fires? String (.If b u d) = false := by
        rw [← fires_at_cw]; exact at_of_clean _ _ hi
      split
      · rename_i h
        obtain rfl := (true_iff _).1 h.1
        obtain rfl := (true_iff _).1 h.2
        have : lint.collapsible_when_fires? String (.If (.Or a b) (.Literal .True) d) = false := by
          rw [cw_fires_if] at hni ⊢; exact hni
        rw [fires_in_eq, fires_at_cw, this]; operands_simp
        simp [hbin _ a b (Or.inr rfl) ha hb, hd, hlit]
      · rename_i h
        rw [cw_fires_if, nw_not_if _ _ hne, nu_if, Bool.false_or, Bool.and_eq_true] at hf
        exact absurd hf h
    · rename_i h1 h2
      intro _ hf
      exfalso
      cases e with
      | If c t f =>
        rw [cw_fires_if, nw_not_if t f (fun b d g h => h1 c b d g f (by rw [h])),
          nu_not_if t f (fun b u d h => h2 c t b u d (by rw [h]))] at hf
        cases hf
      | _ => rw [cw_fires_other _ (fun _ _ _ h => by cases h)] at hf; cases hf
  · rw [fires_at_sb] at hf
    show lint.fires_in? _ (lint.same_branches_fix String e) = false
    revert ho hf
    unfold lint.same_branches_fix; split
    · rename_i c t f
      intro ho hf
      rw [sb_fires_if] at hf
      rw [if_pos (of_decide_eq_true hf)]
      exact (operands_if _ c t f ho).2.1
    · rename_i hne
      intro _ hf
      rw [sb_fires_other e hne] at hf; cases hf
  · rw [fires_at_nm] at hf
    show lint.fires_in? _ (lint.neg_multiply_fix String e) = false
    have hneg (x : Expr String) (hx : lint.fires_in? .NegMultiply x = false) :
        lint.fires_in? .NegMultiply (.Unary .Neg x) = false := by
      rw [fires_in_eq, fires_at_nm, nm_fires_other _ (fun _ _ h => by cases h)]; operands_simp; simp [hx]
    revert ho hf
    unfold lint.neg_multiply_fix; split
    · rename_i a b
      intro ho hf
      have hab := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      split
      · exact hneg _ hab.1
      · split
        · exact hneg _ hab.2
        · rename_i h1 h2
          rw [nm_fires_mul, Bool.or_eq_true] at hf
          rcases hf with h | h
          · exact absurd h h2
          · exact absurd h h1
    · rename_i hne
      intro _ hf
      rw [nm_fires_other e hne] at hf; cases hf
  · rw [fires_at_io] at hf
    show lint.fires_in? _ (lint.identity_op_fix String e) = false
    -- An operation of fixed operands on which the lint does not fire is fixed.
    have hbin (op : BinaryOp) (x y : Expr String) (hx : lint.fires_in? .IdentityOp x = false)
        (hy : lint.fires_in? .IdentityOp y = false) (h : lint.identity_op_fires? String (.Binary op x y) = false) :
        lint.fires_in? .IdentityOp (.Binary op x y) = false := by
      rw [fires_in_eq, fires_at_io, h]; operands_simp; simp [hx, hy]
    have hflip (op : BinaryOp) (a y : Expr String) (hop : op = .Add ∨ op = .Sub)
        (ha : lint.fires_in? .IdentityOp a = false) (hb : lint.fires_in? .IdentityOp (.Unary .Neg y) = false)
        (hfl : lint.flips? String (.Unary .Neg y) = true) (hza : op = .Add → lint.zero? String a = false) :
        lint.fires_in? .IdentityOp (.Binary op a y) = false := by
      obtain ⟨y', hy', hz, hn⟩ := (flips_iff _).1 hfl
      cases hy'
      have hy := operands_one _ _ _ (operands_of_clean _ _ hb)
      refine hbin _ _ _ ha hy ?_
      have : lint.flips? String y = false := by
        cases h : lint.flips? String y
        · rfl
        · obtain ⟨z, rfl, _⟩ := (flips_iff _).1 h; exact absurd rfl (hn z)
      rcases hop with rfl | rfl <;> rw [io_fires_bin]
      · simp [hz, this, hza rfl]
      · simp [hz, this]
    -- A `b` that is not a negation does not flip.
    have hnf (b : Expr String) (hne : ∀ y, b = .Unary .Neg y → False) : lint.flips? String b = false := by
      cases h : lint.flips? String b
      · rfl
      · obtain ⟨y, rfl, _⟩ := (flips_iff _).1 h; exact absurd rfl (hne y)
    revert ho hf
    unfold lint.identity_op_fix; split
    · rename_i a b; intro ho hf
      have hab := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      simp only [io_fires_bin] at hf
      split
      · exact hab.1
      · rename_i hzb
        split
        · exact hab.2
        · rename_i hza
          unfold lint.flipped; split
          · rename_i y
            split
            · rename_i hfl; exact hflip _ a y (Or.inr rfl) hab.1 hab.2 hfl (fun h => by cases h)
            · rename_i hfl; exfalso; simp [hzb, hza, hfl] at hf
          · rename_i hne; exfalso; simp [hzb, hza, hnf b hne] at hf
    · rename_i a b; intro ho hf
      have hab := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      simp only [io_fires_bin] at hf
      split
      · exact hab.1
      · rename_i hzb
        split
        · rename_i hza; exfalso; simp [hzb, hza] at hf
        · rename_i hza
          unfold lint.flipped; split
          · rename_i y
            split
            · rename_i hfl; exact hflip _ a y (Or.inl rfl) hab.1 hab.2 hfl (fun _ => by simpa using hza)
            · rename_i hfl; exfalso; simp [hzb, hza, hfl] at hf
          · rename_i hne; exfalso; simp [hzb, hza, hnf b hne] at hf
    · rename_i a b; intro ho hf
      have hab := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      simp only [io_fires_bin] at hf
      split
      · exact hab.1
      · rename_i h1
        split
        · exact hab.2
        · rename_i h2; exfalso; simp [h1, h2] at hf
    · rename_i a b; intro ho hf
      have hab := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      simp only [io_fires_bin] at hf
      split
      · exact hab.1
      · rename_i h1; exfalso; simp [h1] at hf
    · rename_i a b; intro ho hf
      have hab := operands_two _ a b (Or.inr (Or.inr ⟨_, ho⟩))
      simp only [io_fires_bin] at hf
      split
      · exact hab.1
      · rename_i h1
        split
        · exact hab.2
        · rename_i h2; exfalso; exact h2 (by simpa [h1] using hf)
    · rename_i h1 h2 h3 h4 h5
      intro _ hf; exfalso
      cases e with
      | Binary op a b =>
        cases op <;> simp only [io_fires_bin, Bool.false_eq_true] at hf <;>
          first
            | exact absurd rfl (h1 a b) | exact absurd rfl (h2 a b) | exact absurd rfl (h3 a b)
            | exact absurd rfl (h4 a b) | exact absurd rfl (h5 a b)
      | _ => simp [lint.identity_op_fires?] at hf
  · rw [fires_at_mre] at hf
    show lint.fires_in? _ (lint.manual_rem_euclid_fix String e) = false
    revert ho hf
    unfold lint.manual_rem_euclid_fix; split
    · rename_i p q k
      intro ho hf
      have hs := (operands_two _ _ k (Or.inr (Or.inr ⟨_, ho⟩))).1
      have hpq := operands_two _ p q (Or.inr (Or.inr ⟨_, operands_of_clean _ _ hs⟩))
      rw [mre_fires_mod] at hf
      split
      · rename_i h1
        rw [if_pos h1] at hf
        rw [if_pos hf]; exact hpq.1
      · rename_i h1
        rw [if_neg h1] at hf
        rw [if_pos hf]; exact hpq.2
    · rename_i hne
      intro _ hf
      rw [mre_fires_other e hne] at hf; cases hf

/-- `lint::fix_all_laws::fixed`. -/
theorem fixed (l : lint.ExprLint) (e : Expr String) : lint.fires_in? l (lint.fix_all l e) = false := by
  induction e <;> simp only [lint.fix_all] <;> apply clean_at <;> (try operands_simp) <;> (try simp [*])

/-- `lint::fix_all_laws::unchanged`. -/
theorem unchanged (l : lint.ExprLint) (e : Expr String) (h : lint.fires_in? l e = false) : lint.fix_all l e = e := by
  induction e <;> simp only [lint.fires_in?, bor, db, Bool.or_eq_false_iff] at h <;>
    simp only [lint.fix_all] <;> (try simp_all only [true_implies]) <;>
    exact fix_at_unfired l _ (by first | exact h | exact h.1)

theorem idempotent (l : lint.ExprLint) (e : Expr String) : lint.fix_all l (lint.fix_all l e) = lint.fix_all l e :=
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
theorem keeps (l : lint.ExprLint) (e : Expr String) (env : Env) (hl : lint.fits? l i = true) :
    Le (eval i env e) (eval i env (lint.fix_all l e)) := by
  induction e generalizing env <;> simp only [lint.fix_all] <;> refine Le.trans ?_ (site_le l env _ hl)
  case Literal | Var | NoMatch | Nil => exact Le.refl _
  case Let x d b _ ihb => eval_step; exact ihb _
  case Unary op a iha => eval_step; operand iha env; exact Le.refl _
  case Binary op a b iha ihb => eval_step; operand iha env; operand ihb env; exact Le.refl _
  case And a b iha ihb =>
    eval_step; operand iha env; truth_cases (eval i env a); exact ihb env
  case Or a b iha ihb =>
    eval_step; operand iha env; truth_cases (eval i env a); exact ihb env
  case If c t f ihc iht ihf =>
    eval_step; operand ihc env; truth_cases (eval i env c)
    · exact iht env
    · exact ihf env
  case Is s p ihs => eval_step; operand ihs env; exact Le.refl _
  case Match s p g b rest ihs ihg ihb ihr =>
    eval_step; operand ihs env
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
  case Cons a rest iha ihr => eval_step; operand iha env; operand ihr env; exact Le.refl _
  case Construct c args iha => eval_step; operand iha env; exact Le.refl _
  case Project a c k iha => eval_step; operand iha env; exact Le.refl _
  case Index q k ihq ihk => eval_step; operand ihq env; operand ihk env; exact Le.refl _
  case Method m r args ihr iha => eval_step; operand ihr env; operand iha env; exact Le.refl _
  case Count c args iha => eval_step; operand iha env; exact Le.refl _
  case Apply f args ps body iha ihb =>
    eval_step; operand iha env
    generalize eval i env args = A
    rcases A with v | _
    · exact ihb _
    · exact Le.refl _
  case Call f args iha => eval_step; operand iha env; exact Le.refl _
  case Recur f args iha => eval_step; operand iha env; exact Le.refl _

/-! ### The linter's rule over `lang::Expr` -/

/-- An expression of the semantics as `overly_complex_bool_expr` reads it. -/
def layer : Expr String → Fren.Core.BoolLayer (Expr String)
  | .And a b => .and a b
  | .Or a b => .or a b
  | .Unary .Not a => .not a
  | _ => .other

/-- `k` is the negation of an operand of `e`. -/
noncomputable def negatesOperandOf (e k : Expr String) : Bool :=
  match e with
  | .And a b | .Or a b => lint.negates_operand? String k a || lint.negates_operand? String k b
  | _ => false

/-- `Core.overlyComplexRule` over `lang::Expr`, with `=` for being written the
same, and `n` for whether `nonminimal_bool` rewrites the negation, at an
operand that is the negation of an operand, and `false` at any other: so a
rule that asks about the wrong operand does not meet the procedure. -/
noncomputable def rule (n : Bool) (e : Expr String) : Option (Fren.Core.BoolRule × Fren.Core.Kept) :=
  Fren.Core.overlyComplexRule layer (fun a b => decide (a = b)) (fun k => n && negatesOperandOf e k) e

theorem absorbs_eq (c : Bool) (k o : Expr String) :
    Fren.Core.absorbsOperand layer (fun a b => decide (a = b)) c k o = lint.absorbs_operand? String c k o := by
  cases k <;> cases c <;> simp [Fren.Core.absorbsOperand, layer, lint.absorbs_operand?, lang.Expr.Or.x0,
    lang.Expr.Or.x1, lang.Expr.And.x0, lang.Expr.And.x1]
  all_goals (rename_i op _; cases op <;> rfl)

theorem negates_eq (k o : Expr String) :
    Fren.Core.negatesOperand layer (fun a b => decide (a = b)) k o = lint.negates_operand? String k o := by
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
  (by_cases h1 : lint.absorbs_operand? String $c $b $a = true <;> by_cases h2 : lint.absorbs_operand? String $c $a $b = true <;>
    by_cases h3 : lint.negates_operand? String $a $b = true <;> by_cases h4 : lint.negates_operand? String $b $a = true <;>
    simp only [RewriteProof.rule, RewriteProof.negatesOperandOf, Fren.Core.overlyComplexRule, RewriteProof.layer,
      RewriteProof.absorbs_eq,
      RewriteProof.negates_eq, RewriteProof.fires_and, RewriteProof.fires_or, RewriteProof.drops_iff,
      lint.overly_complex_fix, lint.drop_fix, lint.bool_rule, lint.kept_by, lint.drop_kept, h1, h2, h3, h4, if_true,
      if_false, true_or, or_true,
      or_false, false_or, Bool.false_eq_true, reduceIte, iff_true, iff_false, Option.isSome_some,
      Option.isSome_none, Option.elim, forall_const, Bool.not_eq_true, imp_self, true_implies] <;>
    simp [lint.kept_fix, toKept, Fren.Impls.toBoolRule]))

open RewriteProof in
-- Both front ends run `Core.overlyComplexRule` (trusted, and checked by the ui
-- tests); this is it over `lang::Expr`, with `=` for being written the same and
-- `n` for whether `nonminimal_bool` rewrites the negation of an operand, for
-- every expression.
impl overly_complex_bool_expr: lint::overly_complex_bool_expr for (e : lang.Expr String) (n : Bool) {
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
impl overly_complex_keeps_meaning: lint::overly_complex_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.overly_complex_keeps_meaning.ensures lint.overly_complex_keeps_meaning.ensure.keeps_meaning
  intro h
  exact (agrees_iff _ _).2 (overly_site env e h)

open RewriteProof in
-- For every lint, expression, interpretation and environment, by `site_le`.
impl fix_at_agrees: lint::fix_at_agrees for (l : lint.ExprLint) (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  l := l, e := e, i := i, env := env,
} by
  intro l e i env _
  unfold lint.fix_at_agrees.ensures lint.fix_at_agrees.ensure.agrees
  intro hl
  exact (agrees_iff _ _).2 (site_le l env e hl)

open RewriteProof in
-- For every lint, expression, interpretation and environment, by induction on the expression.
impl fix_all_laws: lint::fix_all_laws for (l : lint.ExprLint) (e : lang.Expr String) (i : lang.Interp) (env : lang.Env) {
  l := l, e := e, i := i, env := env,
} by
  intro l e i env _
  unfold lint.fix_all_laws.ensures lint.fix_all_laws.ensure.fixed lint.fix_all_laws.ensure.unchanged
    lint.fix_all_laws.ensure.idempotent lint.fix_all_laws.ensure.keeps_meaning
  refine ⟨by simp [fixed], fun h => unchanged l e (by simpa using h), idempotent l e, fun hl => (agrees_iff _ _).2 (keeps l e env hl)⟩

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operand.
impl double_neg_keeps_meaning: lint::double_neg_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.double_neg_keeps_meaning.ensures lint.double_neg_keeps_meaning.ensure.keeps_meaning
  intro _
  exact (agrees_iff _ _).2 (dn_site env e)

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operands.
impl int_plus_one_keeps_meaning: lint::int_plus_one_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.int_plus_one_keeps_meaning.ensures lint.int_plus_one_keeps_meaning.ensure.exact
  intro _
  simpa using ipo_site env e

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operand.
impl manual_abs_keeps_meaning: lint::manual_abs_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.manual_abs_keeps_meaning.ensures lint.manual_abs_keeps_meaning.ensure.exact
  intro _
  simpa using ma_site env e

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operands.
impl manual_abs_diff_keeps_meaning: lint::manual_abs_diff_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.manual_abs_diff_keeps_meaning.ensures lint.manual_abs_diff_keeps_meaning.ensure.exact
  intro _
  simpa using mad_site env e

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the condition.
impl unless_not_keeps_meaning: lint::unless_not_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.unless_not_keeps_meaning.ensures lint.unless_not_keeps_meaning.ensure.exact
  intro _
  simpa using un_site env e

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the outer condition.
impl collapsible_when_keeps_meaning: lint::collapsible_when_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.collapsible_when_keeps_meaning.ensures lint.collapsible_when_keeps_meaning.ensure.exact
  intro _
  simpa using cw_site env e

open RewriteProof in
-- For every lint and expression, by `clean_at`.
impl fix_at_fixed: lint::fix_at_fixed for (l : lint.ExprLint) (e : lang.Expr String) {
  l := l, e := e,
} by
  intro l e _
  unfold lint.fix_at_fixed.ensures lint.fix_at_fixed.ensure.fixed
  intro h
  simpa using clean_at l e (by simpa using h)

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the condition.
impl same_branches_keeps_meaning: lint::same_branches_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.same_branches_keeps_meaning.ensures lint.same_branches_keeps_meaning.ensure.agrees
  intro _
  exact (agrees_iff _ _).2 (sb_site env e)

open RewriteProof in
-- For every expression, interpretation and environment, by evaluating the operands.
impl eq_op_said_agrees: lint::eq_op_said_agrees for (e : lang.Expr String) (i : lang.Interp) (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.eq_op_said_agrees.ensures lint.eq_op_said_agrees.ensure.said
  intro h
  exact (agrees_iff _ _).2 (eo_said env e (by simpa using h))

open RewriteProof in
-- For every expression, environment and interpretation whose primitives are `usual?`, by evaluating the operands.
impl neg_multiply_keeps_meaning: lint::neg_multiply_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.neg_multiply_keeps_meaning.ensures lint.neg_multiply_keeps_meaning.ensure.agrees
  intro h
  exact (agrees_iff _ _).2 (nm_site h.1 env e)

open RewriteProof in
-- For every expression, environment and interpretation whose primitives are `usual?`, by evaluating the operands.
impl identity_op_keeps_meaning: lint::identity_op_keeps_meaning for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.identity_op_keeps_meaning.ensures lint.identity_op_keeps_meaning.ensure.agrees
  intro h
  exact (agrees_iff _ _).2 (io_site h.1 env e)

open RewriteProof in
-- For every expression, environment and interpretation whose primitives are `usual?`, by evaluating the operands.
impl manual_rem_euclid_keeps_meaning: lint::manual_rem_euclid_keeps_meaning for (e : lang.Expr String)
    (i : lang.Interp) (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.manual_rem_euclid_keeps_meaning.ensures lint.manual_rem_euclid_keeps_meaning.ensure.agrees
  intro h
  exact (agrees_iff _ _).2 (mre_site h.1 env e)

open RewriteProof in
-- For every expression, environment and interpretation whose primitives are `usual?`, by evaluating the operands.
impl erasing_op_said_agrees: lint::erasing_op_said_agrees for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.erasing_op_said_agrees.ensures lint.erasing_op_said_agrees.ensure.said
  intro h
  exact (agrees_iff _ _).2 (er_said h.1 env e h.2)

open RewriteProof in
-- For every expression, environment and interpretation whose primitives are `usual?`, by evaluating the operands.
impl modulo_one_said_agrees: lint::modulo_one_said_agrees for (e : lang.Expr String) (i : lang.Interp)
    (env : lang.Env) {
  e := e, i := i, env := env,
} by
  intro e i env _
  unfold lint.modulo_one_said_agrees.ensures lint.modulo_one_said_agrees.ensure.said
  intro h
  exact (agrees_iff _ _).2 (mo_said h.1 env e h.2)
