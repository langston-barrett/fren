import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.Expressions

open Fren.Lang

#fren_md "PropertiesAndChecks.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.Verification

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification

/-- Collecting a condition's obligations preserves its meaning in every assignment. -/
theorem collect_exact (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (condition : Condition) :
    ∀ (hyps : Snoc Fact) (found : Snoc Obligation),
      all_satisfied? prog rows env (collect condition hyps found) =
        (all_satisfied? prog rows env found &&
          (some_refuted? rows env hyps || condition_holds? prog rows env condition)) := by
  induction condition with
  | Trivial => intro hyps found; simp [collect, condition_holds?]
  | Check goal =>
    intro hyps found
    simp [collect, all_satisfied?, satisfied?, condition_holds?, fren_spec]
  | Both first second ihf ihs =>
    intro hyps found
    simp only [collect, condition_holds?, ihf, ihs]
    cases all_satisfied? prog rows env found <;> cases some_refuted? rows env hyps <;>
      cases condition_holds? prog rows env first <;>
      cases condition_holds? prog rows env second <;> rfl
  | Branch guard yes no ihy ihn =>
    intro hyps found
    simp only [collect, condition_holds?, ihy, ihn, some_refuted?]
    cases all_satisfied? prog rows env found <;> cases some_refuted? rows env hyps <;>
      cases fact_refuted? rows env (.Holds guard) <;>
      cases fact_refuted? rows env (.Fails guard) <;>
      cases condition_holds? prog rows env yes <;> cases condition_holds? prog rows env no <;> rfl
  | Case scrutinee constructor body ih =>
    intro hyps found
    simp only [collect, condition_holds?, ih, some_refuted?]
    cases all_satisfied? prog rows env found <;> cases some_refuted? rows env hyps <;>
      cases fact_refuted? rows env (.Is scrutinee constructor) <;>
      cases condition_holds? prog rows env body <;> rfl
  | Bind value body ih =>
    intro hyps found
    simp only [collect, condition_holds?, ih, some_refuted?]
    cases all_satisfied? prog rows env found <;> cases some_refuted? rows env hyps <;>
      cases fact_refuted? rows env (.Bound value) <;>
      cases condition_holds? prog rows env body <;> rfl

theorem weaken_length (rows : Snoc Row) (cutoff : Int) (extra : Ty) :
    length Row (weaken rows cutoff extra) = length Row rows := by
  induction rows with
  | Empty => simp [weaken]
  | Extend earlier row ih => simp [weaken, length, ih]

/-- Shifting a local changes no condition: generation never reads a local. -/
theorem generate_shift (prior : Snoc Condition) (pos : Int) (form : ExprF Int) (cutoff : Int) :
    generate prior pos (shift_form form cutoff) = generate prior pos form := by
  cases form <;> simp [generate]

theorem conditions_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) :
    conditions (weaken rows cutoff extra) = conditions rows := by
  induction rows with
  | Empty => simp [weaken]
  | Extend earlier row ih =>
    simp [weaken, conditions, ih, weaken_length, generate_shift]

/-- An assumption has no hypotheses. -/
theorem assumption_hyps (members : Snoc Member) (keyword : Keyword)
    (h : assumption? keyword = true) : member_hyps members keyword = .Empty := by
  induction members with
  | Empty => simp [member_hyps]
  | Extend earlier member ih =>
    cases keyword <;> simp_all [member_hyps, uses?, goal?, assumption?, fren_spec]

end Spec.Language.Verification

/-! ## Laws bound to their procedures -/

pub mod spec::verification

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification in
impl flattening_proof: flattening for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (condition : Condition) (hyps : Snoc Fact) (found : Snoc Obligation) {
  prog := prog, rows := rows, env := env, condition := condition, hyps := hyps, found := found,
  holds? := true
} by
  intro prog rows env condition hyps found _
  simp only [flattening.ensures, flattening.ensure.output, flattening.ensure.exact]
  refine ⟨trivial, ?_⟩
  rw [Spec.Language.Verification.collect_exact prog rows env condition hyps found]
  simp [fren_spec]

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.verification in
impl context_weakening_proof: context_weakening for (rows : Snoc Row) (cutoff : Int) (extra : Ty) {
  rows := rows, cutoff := cutoff, extra := extra, holds? := true
} by
  intro rows cutoff extra _
  simp only [context_weakening.ensures, context_weakening.ensure.output,
    context_weakening.ensure.unchanged]
  refine ⟨trivial, ?_⟩
  simp [Spec.Language.Verification.conditions_weaken rows cutoff extra]

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification in
impl strictness_proof: strictness for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (op : BinaryOp) (left right : Condition) (row : Int) {
  prog := prog, rows := rows, env := env, op := op, left := left, right := right, row := row,
  holds? := true
} by
  intro prog rows env op left right row _
  simp only [strictness.ensures, strictness.ensure.output, strictness.ensure.right_required,
    strictness.ensure.left_required, strictness.ensure.unused_value]
  refine ⟨trivial, ?_⟩
  cases op <;> simp [fren_spec, operator_condition, partial?, condition_holds?] <;>
    grind

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification in
impl guards_proof: guards for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (condition : Condition) (guard : Int) (yes no : Condition) {
  prog := prog, rows := rows, env := env, condition := condition, guard := guard, yes := yes,
  no := no, holds? := true
} by
  intro prog rows env condition guard yes no _
  simp only [guards.ensures, guards.ensure.output, guards.ensure.untaken, guards.ensure.taken,
    guards.ensure.undetermined]
  refine ⟨trivial, ?_⟩
  simp [fren_spec, condition_holds?] <;> grind

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification in
impl divisor_proof: divisor for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (op : BinaryOp) (row : Int) (d : Int) {
  prog := prog, rows := rows, env := env, op := op, row := row, d := d, holds? := true
} by
  intro prog rows env op row d _
  simp only [divisor.ensures, divisor.ensure.output, divisor.ensure.sound, divisor.ensure.complete]
  refine ⟨trivial, ?_⟩
  cases op <;> simp [fren_spec, goal_holds?, integer_domain?, partial?] <;> grind

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification in
impl hypotheses_proof: hypotheses for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (hyps : Snoc Fact) (fact : Fact) (goal : Goal) (row : Int) {
  prog := prog, rows := rows, env := env, hyps := hyps, fact := fact, goal := goal, row := row,
  holds? := true
} by
  intro prog rows env hyps fact goal row _
  simp only [hypotheses.ensures, hypotheses.ensure.output, hypotheses.ensure.weakening,
    hypotheses.ensure.strengthening, hypotheses.ensure.exclusive]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · simp [satisfied?, some_refuted?, fren_spec] <;> grind
  · simp [satisfied?, some_refuted?, fren_spec] <;> grind
  · simp [fact_refuted?, fren_spec] <;> grind

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification in
impl cut_proof: cut for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (hyps : Snoc Fact) (root : Int) (goal : Goal) {
  prog := prog, rows := rows, env := env, hyps := hyps, root := root, goal := goal, holds? := true
} by
  intro prog rows env hyps root goal _
  simp only [cut.ensures, cut.ensure.output, cut.ensure.asserted]
  refine ⟨trivial, ?_⟩
  simp [satisfied?, some_refuted?, fact_refuted?, goal_holds?, fren_spec] <;> grind

open spec.surface (BinaryOp UnaryOp)
open spec.types spec.expressions spec.verification in
impl member_scope_proof: member_scope for (rows : Snoc Row) (env : Snoc Value)
    (members : Snoc Member) (member other : Member) (keyword : Keyword) {
  rows := rows, env := env, members := members, member := member, other := other,
  keyword := keyword, holds? := true
} by
  intro rows env members member other keyword _
  simp only [member_scope.ensures, member_scope.ensure.output, member_scope.ensure.expect_unused,
    member_scope.ensure.own, member_scope.ensure.assumptions_independent,
    member_scope.ensure.order]
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩
  · intro h
    cases keyword <;> simp [member_hyps, uses?, goal?, assumption?, h, fren_spec]
  · intro h
    cases keyword <;> simp [member_hyps, uses?, goal?, assumption?, h, fren_spec]
  · intro h
    exact Spec.Language.Verification.assumption_hyps members keyword (by simpa [fren_spec] using h)
  · simp only [member_hyps]
    cases uses? keyword member.keyword <;> cases uses? keyword other.keyword <;>
      simp [some_refuted?, fren_spec] <;> grind

open spec.verification in
impl verification_examples_proof: worked_examples { holds? := true } by
  intro _
  simp only [worked_examples.ensures, worked_examples.ensure.output, worked_examples.ensure.guarded,
    worked_examples.ensure.conjunction, worked_examples.ensure.unused, worked_examples.ensure.bound,
    worked_examples.ensure.shared, worked_examples.ensure.call, worked_examples.ensure.negation,
    worked_examples.ensure.matched]
  decide

open spec.verification in
impl at_assignments_proof: at_assignments { holds? := true } by
  intro _
  simp only [at_assignments.ensures, at_assignments.ensure.output, at_assignments.ensure.guarded,
    at_assignments.ensure.unguarded, at_assignments.ensure.bound, at_assignments.ensure.first,
    at_assignments.ensure.second, at_assignments.ensure.arm]
  decide

open spec.verification in
impl scopes_proof: scopes { holds? := true } by
  intro _
  simp only [scopes.ensures, scopes.ensure.output, scopes.ensure.derived, scopes.ensure.first,
    scopes.ensure.second, scopes.ensure.refuted]
  decide

open spec.verification in
impl member_examples_proof: member_examples { holds? := true } by
  intro _
  simp only [member_examples.ensures, member_examples.ensure.output,
    member_examples.ensure.rejected, member_examples.ensure.refuted,
    member_examples.ensure.accepted, member_examples.ensure.satisfied]
  decide

open spec.verification in
impl domains_proof: domains { holds? := true } by
  intro _
  simp only [domains.ensures, domains.ensure.output, domains.ensure.within,
    domains.ensure.outside, domains.ensure.undeclared]
  decide

/-! ## The interface: validity is satisfaction by every assignment -/

pub mod spec::validity

open Classical in
interp valid? := fun symb prog rows obligation =>
  decide (∀ env, spec.verification.assignment? symb rows obligation env = true →
    spec.verification.satisfied? prog rows env obligation = true)
interp check := fun _ _ _ _ => spec.verification.Verdict.Unknown

impl verdicts_proof: verdicts for (symb : spec.types.Snoc spec.types.Entry)
    (prog : spec.types.Snoc spec.verification.Declared) (rows : spec.types.Snoc spec.types.Row)
    (obligation : spec.verification.Obligation) (env : spec.types.Snoc spec.expressions.Value) {
  symb := symb, prog := prog, rows := rows, obligation := obligation, env := env, holds? := true
} by
  intro symb prog rows obligation env _
  simp only [spec.validity.verdicts.ensures, spec.validity.verdicts.ensure.output,
    spec.validity.verdicts.ensure.satisfied, spec.validity.verdicts.ensure.proved,
    spec.validity.verdicts.ensure.refuted]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · simp [fren_spec, spec.validity.valid?]
    intro h hassign
    exact h env hassign
  · simp [fren_spec, spec.validity.check]
  · simp [fren_spec, spec.validity.check]

set_option fren.requireEvidence "trusted" in
#fren_trace
