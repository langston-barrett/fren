-- keep-sorted start
import Fren.Impl
import Reqs.Lint
-- keep-sorted end

/-! # Renaming (`Reqs/Lint/Rewrites#renaming`)

The lints stated over `lang::Expr<V>` don't depend on how names are spelled:
renaming every name of an expression, free and bound alike, by an injective
renaming, changes neither whether a lint fires on it nor, but for the
renaming, what its fix writes. This is not invariance under renaming bound
names alone, to an alpha-variant, which fails (`lint::bound_renaming`).
`fires_at?` and `fix_at` are generic in `V`, but Lean doesn't know that they
use only equality, so each lint is proved invariant at the place where it fires,
for every two types of names, by its definition (`fires_at_rn`,
`fix_at_rn`); `fires_in?` and `fix_all`, which look within the operands, by
induction on the expression (`fires_in_rn`, `fix_all_rn`). `lint::renamed_apart`
is these, for a swap of two names. `int_plus_one`, `double_neg`, `unless_not`,
`collapsible_when`, `neg_multiply`, `identity_op`, `trivial_guard` and
`trivial_match` compare no operands, so they are invariant under every
renaming, injective or not (their lemmas `omit` the injectivity). -/

open Fren.Generated
open lang

namespace Rename
variable {V W : Type}

/-- A pattern with each name `x` renamed `r x`. -/
def pat (r : V → W) : Pattern V → Pattern W
  | .Wildcard => .Wildcard
  | .Binder x => .Binder (r x)
  | .Literal v => .Literal v
  | .AtLeast n => .AtLeast n
  | .AtMost n => .AtMost n
  | .Between a b => .Between a b
  | .Variant c p => .Variant c (pat r p)
  | .Nil => .Nil
  | .Cons a b => .Cons (pat r a) (pat r b)
  | .Or a b => .Or (pat r a) (pat r b)

/-- Parameters with each name `x` renamed `r x`. -/
def params (r : V → W) : Params V → Params W
  | .Nil => .Nil
  | .Cons x rest => .Cons (r x) (params r rest)

/-- An expression with each name `x` renamed `r x`. -/
def expr (r : V → W) : Expr V → Expr W
  | .Literal v => .Literal v
  | .Var x => .Var (r x)
  | .Let x d b => .Let (r x) (expr r d) (expr r b)
  | .Unary op a => .Unary op (expr r a)
  | .Binary op a b => .Binary op (expr r a) (expr r b)
  | .And a b => .And (expr r a) (expr r b)
  | .Or a b => .Or (expr r a) (expr r b)
  | .If c t f => .If (expr r c) (expr r t) (expr r f)
  | .Is s p => .Is (expr r s) (pat r p)
  | .Match s p g b rest => .Match (expr r s) (pat r p) (expr r g) (expr r b) (expr r rest)
  | .NoMatch => .NoMatch
  | .Nil => .Nil
  | .Cons a rest => .Cons (expr r a) (expr r rest)
  | .Construct c args => .Construct c (expr r args)
  | .Project a c k => .Project (expr r a) c k
  | .Index q k => .Index (expr r q) (expr r k)
  | .Method m a args => .Method m (expr r a) (expr r args)
  | .Count c args => .Count c (expr r args)
  | .Apply f args ps body => .Apply f (expr r args) (params r ps) (expr r body)
  | .Call f args => .Call f (expr r args)
  | .Recur f args => .Recur f (expr r args)

variable {r : V → W}

theorem pat_inj (hr : Function.Injective r) : ∀ {a b : Pattern V}, pat r a = pat r b → a = b := by
  intro a; induction a <;> intro b h <;> cases b <;> simp_all [pat] <;> grind
theorem params_inj (hr : Function.Injective r) : ∀ {a b : Params V}, params r a = params r b → a = b := by
  intro a; induction a <;> intro b h <;> cases b <;> simp_all [params] <;> grind
theorem expr_inj (hr : Function.Injective r) : ∀ {a b : Expr V}, expr r a = expr r b → a = b := by
  intro a; induction a <;> intro b h <;> cases b <;> simp_all [expr] <;> grind [pat_inj, params_inj]


theorem expr_eq (hr : Function.Injective r) (a b : Expr V) : expr r a = expr r b ↔ a = b :=
  ⟨expr_inj hr, fun h => h ▸ rfl⟩

theorem expr_lit (e : Expr V) (v : Value) : expr r e = .Literal v ↔ e = .Literal v := by
  cases e <;> simp [expr]
theorem expr_unary (e : Expr V) op (b : Expr W) :
    expr r e = .Unary op b ↔ ∃ a, e = .Unary op a ∧ expr r a = b := by
  cases e <;> simp [expr] <;> grind
theorem expr_binary (e : Expr V) op (b c : Expr W) :
    expr r e = .Binary op b c ↔ ∃ a d, e = .Binary op a d ∧ expr r a = b ∧ expr r d = c := by
  cases e <;> simp [expr] <;> grind
theorem expr_if (e : Expr V) (b c d : Expr W) :
    expr r e = .If b c d ↔ ∃ x y z, e = .If x y z ∧ expr r x = b ∧ expr r y = c ∧ expr r z = d := by
  cases e <;> simp [expr] <;> grind
theorem expr_and (e : Expr V) (b c : Expr W) :
    expr r e = .And b c ↔ ∃ a d, e = .And a d ∧ expr r a = b ∧ expr r d = c := by
  cases e <;> simp [expr] <;> grind
theorem expr_or (e : Expr V) (b c : Expr W) :
    expr r e = .Or b c ↔ ∃ a d, e = .Or a d ∧ expr r a = b ∧ expr r d = c := by
  cases e <;> simp [expr] <;> grind

theorem expr_method (e : Expr V) m (b c : Expr W) :
    expr r e = .Method m b c ↔ ∃ a d, e = .Method m a d ∧ expr r a = b ∧ expr r d = c := by
  cases e <;> simp [expr] <;> grind

/-- A renaming that is injective: it renames two names apart that are apart. -/
class Inj (r : V → W) : Prop where
  inj : Function.Injective r

section
variable [Inhabited V] [Inhabited W] [hr : Inj r]

omit [Inhabited V] [Inhabited W] in
theorem expr_eq' (a b : Expr V) : expr r a = expr r b ↔ a = b := expr_eq hr.inj a b

attribute [local simp] expr expr_eq' expr_lit expr_unary expr_binary expr_if expr_and expr_or expr_method

omit [Inhabited V] [Inhabited W] hr in
@[local simp] theorem one_rn (e : Expr V) : lint.one? W (expr r e) = lint.one? V e := by simp [lint.one?]
omit [Inhabited V] [Inhabited W] hr in
@[local simp] theorem zero_rn (e : Expr V) : lint.zero? W (expr r e) = lint.zero? V e := by simp [lint.zero?]
omit [Inhabited V] [Inhabited W] hr in
@[local simp] theorem true_rn (e : Expr V) : lint.true? W (expr r e) = lint.true? V e := by simp [lint.true?]

omit hr in
@[local simp] theorem offset_rn (e : Expr V) : lint.offset_of W (expr r e) = lint.offset_of V e := by
  cases e <;> simp only [lint.offset_of, expr] <;> try rfl
  rename_i op _ _; cases op <;> simp only [one_rn] <;> rfl

omit hr in
@[local simp] theorem without_rn (e : Expr V) :
    lint.without_offset W (expr r e) = expr r (lint.without_offset V e) := by
  cases e <;> simp only [lint.without_offset, expr] <;> try rfl
  rename_i op a b; cases op <;> simp only [one_rn] <;> (try split) <;> (try split) <;> simp [expr]

omit hr in
theorem ipo_fires_rn (e : Expr V) : lint.int_plus_one_fires? W (expr r e) = lint.int_plus_one_fires? V e := by
  cases e <;> simp [lint.int_plus_one_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]

omit hr in
theorem ipo_fix_rn (e : Expr V) : lint.int_plus_one_fix W (expr r e) = expr r (lint.int_plus_one_fix V e) := by
  cases e <;> simp only [lint.int_plus_one_fix, expr] <;> try rfl
  rename_i op a b; cases op <;> simp only [offset_rn] <;> (try split) <;> (try split) <;> simp [expr, without_rn]

omit hr in
theorem dn_fires_rn (e : Expr V) : lint.double_neg_fires? W (expr r e) = lint.double_neg_fires? V e := by
  cases e <;> simp [lint.double_neg_fires?]
  rename_i op a; cases op <;> cases a <;> simp [expr]
  rename_i op' _; cases op' <;> simp

omit hr in
theorem dn_fix_rn (e : Expr V) : lint.double_neg_fix W (expr r e) = expr r (lint.double_neg_fix V e) := by
  cases e <;> simp only [lint.double_neg_fix, expr] <;> try rfl
  rename_i op a; cases op <;> cases a <;> simp only [expr] <;> try rfl
  rename_i op' _; cases op' <;> rfl

omit [Inhabited V] [Inhabited W] hr in
theorem abs_of_rn (x : Expr V) : lint.abs_of W (expr r x) = expr r (lint.abs_of V x) := rfl

theorem ant_rn (c t f : Expr V) :
    lint.abs_negated_then? W (expr r c) (expr r t) (expr r f) = lint.abs_negated_then? V c t f := by
  cases c <;> simp [lint.abs_negated_then?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]
  rename_i op a b; cases a <;> simp [expr]
  rename_i v; cases v <;> simp

theorem ane_rn (c t f : Expr V) :
    lint.abs_negated_else? W (expr r c) (expr r t) (expr r f) = lint.abs_negated_else? V c t f := by
  cases c <;> simp [lint.abs_negated_else?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]
  rename_i op a b; cases b <;> simp [expr]
  rename_i v; cases v <;> simp

theorem ma_fires_rn (e : Expr V) : lint.manual_abs_fires? W (expr r e) = lint.manual_abs_fires? V e := by
  cases e <;> simp [lint.manual_abs_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2, ant_rn, ane_rn]

theorem ma_fix_rn (e : Expr V) : lint.manual_abs_fix W (expr r e) = expr r (lint.manual_abs_fix V e) := by
  cases e <;> simp only [lint.manual_abs_fix, expr] <;> try rfl
  simp only [ant_rn, ane_rn, apply_ite (expr r)]; rfl

theorem ad_rn (c t f : Expr V) :
    lint.abs_diff? W (expr r c) (expr r t) (expr r f) = lint.abs_diff? V c t f := by
  cases c <;> simp [lint.abs_diff?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]

theorem mad_fires_rn (e : Expr V) : lint.manual_abs_diff_fires? W (expr r e) = lint.manual_abs_diff_fires? V e := by
  cases e <;> simp [lint.manual_abs_diff_fires?, ad_rn]

theorem mad_fix_rn (e : Expr V) : lint.manual_abs_diff_fix W (expr r e) = expr r (lint.manual_abs_diff_fix V e) := by
  cases e <;> simp only [lint.manual_abs_diff_fix, expr] <;> try rfl
  simp only [ad_rn, apply_ite (expr r)]; rfl

omit hr in
theorem un_fires_rn (e : Expr V) : lint.unless_not_fires? W (expr r e) = lint.unless_not_fires? V e := by
  cases e <;> simp [lint.unless_not_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2, lang.Expr.Unary.x0,
    lang.Expr.Unary.x1]
  rename_i c _ _; cases c <;> simp [expr]

omit hr in
theorem un_fix_rn (e : Expr V) : lint.unless_not_fix W (expr r e) = expr r (lint.unless_not_fix V e) := by
  cases e <;> simp only [lint.unless_not_fix, expr] <;> try rfl
  rename_i c _ _; cases c <;> simp only [expr] <;> try rfl
  rename_i op _; cases op <;> simp only [true_rn] <;> (try split) <;> simp [expr]

omit hr in
theorem nw_rn (t f : Expr V) : lint.nested_when? W (expr r t) (expr r f) = lint.nested_when? V t f := by
  cases t <;> simp [lint.nested_when?]

omit hr in
theorem nu_rn (t f : Expr V) : lint.nested_unless? W (expr r t) (expr r f) = lint.nested_unless? V t f := by
  cases f <;> simp [lint.nested_unless?]

omit hr in
theorem cw_fires_rn (e : Expr V) : lint.collapsible_when_fires? W (expr r e) = lint.collapsible_when_fires? V e := by
  cases e <;> simp only [lint.collapsible_when_fires?, expr, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2, nw_rn,
    nu_rn] <;> simp

omit hr in
theorem cw_fix_rn (e : Expr V) : lint.collapsible_when_fix W (expr r e) = expr r (lint.collapsible_when_fix V e) := by
  cases e <;> simp only [lint.collapsible_when_fix, expr] <;> try rfl
  rename_i a t f
  cases t
  case If => simp only [expr, true_rn, apply_ite (expr r)]
  all_goals (cases f <;> simp only [expr] <;> try rfl)
  all_goals (simp only [apply_ite (expr r)]; split <;> split <;> simp_all [lint.true?])

theorem sb_fires_rn (e : Expr V) : lint.same_branches_fires? W (expr r e) = lint.same_branches_fires? V e := by
  cases e <;> simp [lint.same_branches_fires?, lang.Expr.If.x0, lang.Expr.If.x1, lang.Expr.If.x2]

theorem sb_fix_rn (e : Expr V) : lint.same_branches_fix W (expr r e) = expr r (lint.same_branches_fix V e) := by
  cases e <;> simp only [lint.same_branches_fix, expr] <;> try rfl
  rename_i c t f
  by_cases h : t = f <;> simp [h]

omit [Inhabited V] [Inhabited W] hr in
@[local simp] theorem minus_one_rn (e : Expr V) : lint.minus_one? W (expr r e) = lint.minus_one? V e := by
  simp [lint.minus_one?]

omit hr in
theorem nm_fires_rn (e : Expr V) : lint.neg_multiply_fires? W (expr r e) = lint.neg_multiply_fires? V e := by
  cases e <;> simp [lint.neg_multiply_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]

omit hr in
theorem nm_fix_rn (e : Expr V) : lint.neg_multiply_fix W (expr r e) = expr r (lint.neg_multiply_fix V e) := by
  cases e <;> simp only [lint.neg_multiply_fix, expr] <;> try rfl
  rename_i op a b; cases op <;> simp only [minus_one_rn] <;> (try split) <;> (try split) <;> simp [expr]

omit [Inhabited V] [Inhabited W] hr in
theorem expr_nil (e : Expr V) : expr r e = .Nil ↔ e = .Nil := by
  cases e <;> simp [expr]

omit [Inhabited V] [Inhabited W] hr in
@[local simp] theorem empty_text_rn (e : Expr V) : lint.empty_text? W (expr r e) = lint.empty_text? V e := by
  simp [lint.empty_text?]

omit hr in
@[local simp] theorem flips_rn (b : Expr V) : lint.flips? W (expr r b) = lint.flips? V b := by
  cases b <;> simp [lint.flips?, lang.Expr.Unary.x0, lang.Expr.Unary.x1]
  rename_i op y; cases op <;> simp
  cases y <;> simp [expr]
  rename_i op' _; cases op' <;> simp

omit hr in
theorem flipped_rn (op : BinaryOp) (a b e : Expr V) :
    lint.flipped W op (expr r a) (expr r b) (expr r e) = expr r (lint.flipped V op a b e) := by
  have hf := flips_rn (r := r) b
  cases b <;> simp only [lint.flipped, expr] <;> try rfl
  rename_i op' y; cases op' <;> simp only [expr] at hf ⊢ <;> try rfl
  simp only [hf]; split <;> simp [expr]

omit [Inhabited W] hr in
open Classical in
/-- Where `identity_op` fires on an operation, by its operator. -/
theorem io_fires_bin (op : BinaryOp) (a b : Expr V) : lint.identity_op_fires? V (.Binary op a b) =
    match op with
    | .Add => lint.zero? V b || lint.zero? V a || lint.flips? V b
    | .Sub => lint.zero? V b || (!lint.zero? V a && lint.flips? V b)
    | .Mul => lint.one? V b || lint.one? V a
    | .Div => lint.one? V b
    | .Concat => lint.empty_text? V b || lint.empty_text? V a || decide (a = .Nil)
    | _ => false := by
  cases op <;> simp [lint.identity_op_fires?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2] <;>
    (try rw [Bool.eq_iff_iff]) <;> simp [or_assoc]

omit hr in
theorem io_fires_rn (e : Expr V) : lint.identity_op_fires? W (expr r e) = lint.identity_op_fires? V e := by
  cases e
  case Binary op a b =>
    simp only [expr]; rw [io_fires_bin, io_fires_bin]
    cases op <;> simp only [zero_rn, one_rn, flips_rn, empty_text_rn]
    case Concat => congr 1; exact decide_eq_decide.2 (expr_nil a)
  all_goals first | rfl | simp [lint.identity_op_fires?, expr, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]

omit hr in
theorem io_fix_rn (e : Expr V) : lint.identity_op_fix W (expr r e) = expr r (lint.identity_op_fix V e) := by
  cases e <;> simp only [lint.identity_op_fix, expr] <;> try rfl
  rename_i op a b
  cases op <;> simp only [zero_rn, one_rn, empty_text_rn, expr_nil] <;> (try rfl) <;> (repeat' split) <;>
    (first
      | rfl
      | exact flipped_rn _ a b (.Binary _ a b)
      | (exfalso; simp_all [empty_text_rn, expr_nil]; done)
      | (simp [expr]; done))

omit hr in
@[local simp] theorem remainder_rn (e : Expr V) : lint.remainder? W (expr r e) = lint.remainder? V e := by
  cases e <;> try rfl
  rename_i op _ _; cases op <;> rfl

theorem rby_rn (a b k : Expr V) :
    lint.remainder_by? W (expr r a) (expr r b) (expr r k) = lint.remainder_by? V a b k := by
  cases a <;> simp [lint.remainder_by?, lang.Expr.Binary.x0, lang.Expr.Binary.x1, lang.Expr.Binary.x2]

theorem mre_fires_rn (e : Expr V) :
    lint.manual_rem_euclid_fires? W (expr r e) = lint.manual_rem_euclid_fires? V e := by
  cases e <;> try rfl
  rename_i op a k; cases op <;> try rfl
  cases a <;> try rfl
  rename_i op' p q; cases op' <;> try rfl
  simp only [lint.manual_rem_euclid_fires?, expr, remainder_rn, rby_rn]

theorem mre_fix_rn (e : Expr V) :
    lint.manual_rem_euclid_fix W (expr r e) = expr r (lint.manual_rem_euclid_fix V e) := by
  cases e <;> try rfl
  rename_i op a k; cases op <;> try rfl
  cases a <;> try rfl
  rename_i op' p q; cases op' <;> try rfl
  simp only [lint.manual_rem_euclid_fix, expr, remainder_rn, rby_rn]; (repeat' split) <;> simp [expr]

omit hr in
theorem tg_fires_rn (e : Expr V) : lint.trivial_guard_fires? W (expr r e) = lint.trivial_guard_fires? V e := by
  cases e <;> try rfl
  rename_i s p g b rest
  cases g <;> simp [lint.trivial_guard_fires?, lang.Expr.Match.x0, lang.Expr.Match.x1, lang.Expr.Match.x2,
    lang.Expr.Match.x3, lang.Expr.Match.x4, expr]

omit hr in
theorem tg_fix_rn (e : Expr V) : lint.trivial_guard_fix W (expr r e) = expr r (lint.trivial_guard_fix V e) := by
  cases e <;> try rfl
  rename_i s p g b rest
  cases g <;> simp only [lint.trivial_guard_fix, expr] <;> try rfl
  rename_i v
  by_cases h : v = .False <;> simp [h, expr]

omit hr in
theorem tm_fires_rn (e : Expr V) : lint.trivial_match_fires? W (expr r e) = lint.trivial_match_fires? V e := by
  cases e <;> try rfl
  rename_i s p g b rest
  cases g <;> cases rest <;> simp [lint.trivial_match_fires?, lang.Expr.Match.x0, lang.Expr.Match.x1,
    lang.Expr.Match.x2, lang.Expr.Match.x3, lang.Expr.Match.x4, expr] <;>
    cases p <;> simp [pat] <;> rename_i ps <;> cases ps <;> simp [pat]

omit hr in
theorem tm_fix_rn (e : Expr V) : lint.trivial_match_fix W (expr r e) = expr r (lint.trivial_match_fix V e) := by
  cases e <;> try rfl
  rename_i s p g b rest
  cases g <;> cases rest <;> simp [lint.trivial_match_fix, expr]
  rename_i v
  by_cases h : v = Value.True
  · cases p <;> simp [h, pat, expr] <;> rename_i ps <;> cases ps <;> simp [pat, expr]
  · simp [h, expr]

omit hr in
theorem tests_rn (p : Pattern V) : lint.tests_only? W (pat r p) = lint.tests_only? V p := by
  cases p <;> try rfl
  rename_i c ps; cases ps <;> rfl

omit [Inhabited V] [Inhabited W] hr in
theorem expr_nomatch (e : Expr V) : expr r e = .NoMatch ↔ e = .NoMatch := by cases e <;> simp

omit [Inhabited V] [Inhabited W] hr in
theorem pat_true (p : Pattern V) : pat r p = .Literal .True ↔ p = .Literal .True := by cases p <;> simp [pat]

omit hr in
theorem sme_fires_match {U : Type} [Inhabited U] (s : Expr U) (p : Pattern U) (g a rest : Expr U) :
    lint.single_match_else_fires? U (.Match s p g a rest) =
      (lint.tests_only? U p && lint.true? U g && lint.wildcard_arm? U s rest) := by
  cases rest <;> simp [lint.single_match_else_fires?, lint.tests_only?, lint.true?, lint.wildcard_arm?, lang.Expr.Match.x0, lang.Expr.Match.x1, lang.Expr.Match.x2, lang.Expr.Match.x3,
    lang.Expr.Match.x4]

theorem wildcard_arm_rn (s rest : Expr V) :
    lint.wildcard_arm? W (expr r s) (expr r rest) = lint.wildcard_arm? V s rest := by
  cases rest <;> simp [lint.wildcard_arm?, expr_nomatch, lang.Expr.Match.x0, lang.Expr.Match.x1, lang.Expr.Match.x2,
    lang.Expr.Match.x3, lang.Expr.Match.x4]
  rename_i q _ _ _; cases q <;> simp [pat]

omit hr in
theorem arm_body_rn (rest : Expr V) : lint.arm_body W (expr r rest) = expr r (lint.arm_body V rest) := by
  cases rest <;> simp [lint.arm_body]

theorem sme_fires_rn (e : Expr V) :
    lint.single_match_else_fires? W (expr r e) = lint.single_match_else_fires? V e := by
  cases e <;> try rfl
  rename_i s p g a rest
  simp only [expr, sme_fires_match, tests_rn, true_rn, wildcard_arm_rn]

theorem sme_fix_rn (e : Expr V) :
    lint.single_match_else_fix W (expr r e) = expr r (lint.single_match_else_fix V e) := by
  cases e <;> try rfl
  rename_i s p g a rest
  have hf := sme_fires_rn (r := r) (.Match s p g a rest)
  simp only [expr] at hf
  simp only [lint.single_match_else_fix, expr, hf]
  split <;> simp [expr, arm_body_rn]

omit hr in
theorem mb_fires_match {U : Type} [Inhabited U] (s : Expr U) (p : Pattern U) (g a rest : Expr U) :
    lint.match_bool_fires? U (.Match s p g a rest) = (lint.true? U g && lint.bool_arm? U s p rest) := by
  cases rest <;> simp [lint.match_bool_fires?, lint.true?, lint.bool_arm?, lint.bool_pair?, lang.Expr.Match.x0, lang.Expr.Match.x1, lang.Expr.Match.x2, lang.Expr.Match.x3,
    lang.Expr.Match.x4]

theorem bool_arm_rn (s : Expr V) (p : Pattern V) (rest : Expr V) :
    lint.bool_arm? W (expr r s) (pat r p) (expr r rest) = lint.bool_arm? V s p rest := by
  cases rest <;> simp [lint.bool_arm?, lint.bool_pair?, expr_nomatch, lang.Expr.Match.x0, lang.Expr.Match.x1, lang.Expr.Match.x2, lang.Expr.Match.x3,
    lang.Expr.Match.x4]
  rename_i q _ _ _; cases p <;> cases q <;> simp [pat]

theorem mb_fires_rn (e : Expr V) : lint.match_bool_fires? W (expr r e) = lint.match_bool_fires? V e := by
  cases e <;> try rfl
  rename_i s p g a rest
  simp only [expr, mb_fires_match, true_rn, bool_arm_rn]

theorem mb_fix_rn (e : Expr V) : lint.match_bool_fix W (expr r e) = expr r (lint.match_bool_fix V e) := by
  cases e <;> try rfl
  rename_i s p g a rest
  have hf := mb_fires_rn (r := r) (.Match s p g a rest)
  simp only [expr] at hf
  simp only [lint.match_bool_fix, expr, hf]
  by_cases h1 : lint.match_bool_fires? V (.Match s p g a rest) = true
  · simp only [h1, not_true_eq_false, if_false, pat_true]
    by_cases h2 : p = .Literal .True <;> simp [h2, pat_true, pat, expr, arm_body_rn]
  · simp [h1, expr]

theorem absorbs_rn (c : Bool) (k o : Expr V) :
    lint.absorbs_operand? W c (expr r k) (expr r o) = lint.absorbs_operand? V c k o := by
  cases k <;> simp [lint.absorbs_operand?, lang.Expr.Or.x0, lang.Expr.Or.x1, lang.Expr.And.x0, lang.Expr.And.x1]

omit [Inhabited V] [Inhabited W] in
theorem negates_rn (k o : Expr V) : lint.negates_operand? W (expr r k) (expr r o) = lint.negates_operand? V k o := by
  simp [lint.negates_operand?]

theorem drops_rn (c : Bool) (a b : Expr V) : lint.drops? W c (expr r a) (expr r b) = lint.drops? V c a b := by
  simp only [lint.drops?, absorbs_rn, negates_rn]

theorem drop_fix_rn (c : Bool) (a b e : Expr V) :
    lint.drop_fix W c (expr r a) (expr r b) (expr r e) = expr r (lint.drop_fix V c a b e) := by
  simp only [lint.drop_fix, absorbs_rn, negates_rn]; (repeat' split) <;> simp [expr]

theorem oc_fires_rn (e : Expr V) : lint.overly_complex_fires? W (expr r e) = lint.overly_complex_fires? V e := by
  cases e <;> simp only [lint.overly_complex_fires?, expr, drops_rn] <;> simp

theorem oc_fix_rn (e : Expr V) : lint.overly_complex_fix W (expr r e) = expr r (lint.overly_complex_fix V e) := by
  cases e <;> simp only [lint.overly_complex_fix, expr] <;> try rfl
  all_goals (rw [← expr, drop_fix_rn])

/-- Renaming invariance at the place where a lint fires: renaming apart
changes neither whether it fires nor, but for the renaming, what its fix
writes. -/
theorem fires_at_rn (l : lint.ExprLint) (e : Expr V) : lint.fires_at? W l (expr r e) = lint.fires_at? V l e := by
  cases l <;> simp only [lint.fires_at?, oc_fires_rn, dn_fires_rn, ipo_fires_rn, ma_fires_rn, mad_fires_rn,
    un_fires_rn, cw_fires_rn, sb_fires_rn, nm_fires_rn, io_fires_rn, mre_fires_rn, tg_fires_rn,
    tm_fires_rn, sme_fires_rn, mb_fires_rn]

theorem fix_at_rn (l : lint.ExprLint) (e : Expr V) : lint.fix_at W l (expr r e) = expr r (lint.fix_at V l e) := by
  cases l <;> simp only [lint.fix_at, oc_fix_rn, dn_fix_rn, ipo_fix_rn, ma_fix_rn, mad_fix_rn, un_fix_rn, cw_fix_rn,
    sb_fix_rn, nm_fix_rn, io_fix_rn, mre_fix_rn, tg_fix_rn, tm_fix_rn,
    sme_fix_rn, mb_fix_rn]

end

variable {r : String → String} [Inj r]

/-- Renaming invariance of fixing everywhere: renaming the names of `e`
apart changes neither where a lint fires within it nor, but for the
renaming, what fixing it everywhere writes. -/
theorem fires_in_rn (l : lint.ExprLint) (e : Expr String) : lint.fires_in? l (expr r e) = lint.fires_in? l e := by
  induction e <;> (conv => lhs; rw [lint.fires_in?.eq_def]) <;> rw [fires_at_rn] <;>
    simp only [expr, lint.fires_in?, *] <;> exact decide_eq_decide.2 Iff.rfl

theorem fix_all_rn (l : lint.ExprLint) (e : Expr String) : lint.fix_all l (expr r e) = expr r (lint.fix_all l e) := by
  induction e <;> simp only [lint.fix_all, expr] <;> (try simp only [*]) <;> rw [← fix_at_rn] <;> rfl

/-- A swap of two names renames them apart. -/
instance swapped_inj (a b : String) : Inj (lint.swapped a b) where
  inj x y h := by
    simp only [lint.swapped] at h
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hya : y = a <;> by_cases hyb : y = b <;>
      simp_all <;> grind

theorem swap_pattern_eq (a b : String) (p : Pattern String) :
    lint.swap_pattern a b p = pat (lint.swapped a b) p := by
  induction p <;> simp_all [lint.swap_pattern, pat]

theorem swap_params_eq (a b : String) (ps : Params String) :
    lint.swap_params a b ps = params (lint.swapped a b) ps := by
  induction ps <;> simp_all [lint.swap_params, params]

theorem swap_names_eq (a b : String) (e : Expr String) :
    lint.swap_names a b e = expr (lint.swapped a b) e := by
  induction e <;> simp_all [lint.swap_names, expr, swap_pattern_eq, swap_params_eq]

end Rename

open Fren.Lang

-- For every lint, expression and two names, by `Rename.fires_at_rn`,
-- `Rename.fix_at_rn`, `Rename.fires_in_rn` and `Rename.fix_all_rn`.
impl renamed_apart: lint::renamed_apart for (l : lint.ExprLint) (e : lang.Expr String) (a b : String) {
  l := l, e := e, a := a, b := b,
} by
  intro l e a b _
  unfold lint.renamed_apart.ensures lint.renamed_apart.ensure.fires_at lint.renamed_apart.ensure.fix_at
    lint.renamed_apart.ensure.fires_in lint.renamed_apart.ensure.fix_all
  simp only [Rename.swap_names_eq, Rename.fires_at_rn, Rename.fix_at_rn, Rename.fires_in_rn, Rename.fix_all_rn,
    and_self]
