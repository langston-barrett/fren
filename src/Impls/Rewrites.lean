-- keep-sorted start
import Impls.Lint
import Reqs.Lint
-- keep-sorted end

/-! # Lints over the syntax of the semantics (`Reqs/Lint/Rewrites`)

`overly_complex_bool_expr` over `lang::Expr`: its fix agrees with the
expression where it fires, and the linter's rule, `Core.overlyComplexRule`,
meets `lint::overly_complex_bool_expr` at `lang::Expr`. Then the laws of fixing every lint
everywhere (`lint::fix_all_laws`), by induction on the expression, from two
facts about each lint where it fires: its fix agrees there, and it writes an
operand or a literal on which the lint does not fire. `Le o o'` says that
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

/-! ### Each lint at the place where it fires -/

/-- Each lint, where it does not fire, writes the expression
(`lint::fix_at_unfired`); where it fires, an operand of an `and` or an `or`,
or a literal (`lint::fix_at_operand`). Each new arm of `lint::ExprLint` owes
this. -/
theorem fix_at_cases (l : lint.ExprLint) (e : Expr) :
    (lint.fires_at? l e = false ∧ lint.fix_at l e = e) ∨
    (lint.fires_at? l e = true ∧ ∃ a b, (e = .And a b ∨ e = .Or a b) ∧
      (lint.fix_at l e = a ∨ lint.fix_at l e = b ∨ ∃ v, lint.fix_at l e = .Literal v)) := by
  cases l
  have hf : lint.fires_at? .OverlyComplexBoolExpr e = lint.overly_complex_fires? e := by
    show decide (lint.overly_complex_fires? e = true) = _
    cases lint.overly_complex_fires? e <;> rfl
  have hx : lint.fix_at .OverlyComplexBoolExpr e = lint.overly_complex_fix e := rfl
  rw [hf, hx]
  cases h : lint.overly_complex_fires? e
  · exact Or.inl ⟨rfl, overly_fix_unfired e h⟩
  · exact Or.inr ⟨rfl, overly_fix_shape e h⟩

/-- Each lint's fix agrees with the expression, where it fires and where not
(`lint::fix_at_agrees`). Each new arm of `lint::ExprLint` owes this. -/
theorem site_le (l : lint.ExprLint) (env : Env) (e : Expr) : Le (eval i env e) (eval i env (lint.fix_at l e)) := by
  cases l
  have hx : lint.fix_at .OverlyComplexBoolExpr e = lint.overly_complex_fix e := rfl
  rw [hx]
  cases h : lint.overly_complex_fires? e
  · rw [overly_fix_unfired e h]; exact Le.refl _
  · exact overly_site env e h

/-! ### Fixing everywhere -/

theorem db (p q : Bool) : decide ((p || q) = true) = (p || q) := by cases p <;> cases q <;> rfl

theorem bor (p q : Bool) : (p = true ∨ q = true) ↔ (p || q) = true := by cases p <;> cases q <;> simp

/-- Where the operands are fixed, the fix at the expression leaves nothing to fix. -/
theorem clean_at (l : lint.ExprLint) (e : Expr)
    (hk : ∀ a b, (e = .And a b ∨ e = .Or a b) → lint.fires_in? l a = false ∧ lint.fires_in? l b = false)
    (hn : lint.fires_at? l e = false → lint.fires_in? l e = false) :
    lint.fires_in? l (lint.fix_at l e) = false := by
  rcases fix_at_cases l e with ⟨hf, he⟩ | ⟨_, a, b, hab, hfix⟩
  · rw [he]; exact hn hf
  · have := hk a b hab
    rcases hfix with h | h | ⟨v, h⟩ <;> rw [h]
    · exact this.1
    · exact this.2
    · simp [lint.fires_in?]

/-- `lint::fix_all_laws::fixed`. -/
theorem fixed (l : lint.ExprLint) (e : Expr) : lint.fires_in? l (lint.fix_all l e) = false := by
  induction e <;> simp only [lint.fix_all] <;> apply clean_at <;>
    first
    | (intro a b h; simp only [reduceCtorEq, or_false, false_or, Expr.And.injEq, Expr.Or.injEq] at h
       try (obtain ⟨rfl, rfl⟩ := h; constructor <;> assumption))
    | (intro hf; simp only [lint.fires_in?, hf]; simp [*])

theorem fix_at_unfired (l : lint.ExprLint) (e : Expr) (h : lint.fires_at? l e = false) : lint.fix_at l e = e := by
  rcases fix_at_cases l e with ⟨_, he⟩ | ⟨hf, _⟩
  · exact he
  · rw [h] at hf; cases hf

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

/-- `Core.overlyComplexRule` over `lang::Expr`, with `=` for being written the
same, and `n` for whether `nonminimal_bool` rewrites the negation. -/
def rule (n : Bool) (e : Expr) : Option (Fren.Core.BoolRule × Fren.Core.Kept) :=
  Fren.Core.overlyComplexRule layer (fun a b => decide (a = b)) (fun _ => n) e

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
    simp only [RewriteProof.rule, Fren.Core.overlyComplexRule, RewriteProof.layer, RewriteProof.absorbs_eq,
      RewriteProof.negates_eq, RewriteProof.fires_and, RewriteProof.fires_or, RewriteProof.drops_iff,
      lint.overly_complex_fix, lint.drop_fix, lint.bool_rule, h1, h2, h3, h4, if_true, if_false, true_or, or_true,
      or_false, false_or, Bool.false_eq_true, reduceIte, iff_true, iff_false, Option.isSome_some,
      Option.isSome_none, Option.elim, forall_const, Bool.not_eq_true, imp_self, true_implies] <;>
    simp [lint.kept_fix, toKept, Fren.Impls.toBoolRule]))

open RewriteProof in
-- Both front ends run `Core.overlyComplexRule` (trusted, and checked by the ui
-- tests); this is it over `lang::Expr`, with `=` for being written the same and
-- `n` for whether `nonminimal_bool` rewrites the negation, for every expression.
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
