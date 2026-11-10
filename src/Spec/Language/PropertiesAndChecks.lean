import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.DynamicSemantics

open Fren.Lang

#fren_md "PropertiesAndChecks.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.Verification

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification

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
theorem generate_shift (prior : Snoc Condition) (pos : Int) (form : CoreF Int) (cutoff : Int) :
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

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
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

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.verification in
impl context_weakening_proof: context_weakening for (rows : Snoc Row) (cutoff : Int) (extra : Ty) {
  rows := rows, cutoff := cutoff, extra := extra, holds? := true
} by
  intro rows cutoff extra _
  simp only [context_weakening.ensures, context_weakening.ensure.output,
    context_weakening.ensure.unchanged]
  refine ⟨trivial, ?_⟩
  simp [Spec.Language.Verification.conditions_weaken rows cutoff extra]

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
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

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
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

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
impl divisor_proof: divisor for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (op : BinaryOp) (row : Int) (d : Int) {
  prog := prog, rows := rows, env := env, op := op, row := row, d := d, holds? := true
} by
  intro prog rows env op row d _
  simp only [divisor.ensures, divisor.ensure.output, divisor.ensure.sound, divisor.ensure.complete]
  refine ⟨trivial, ?_⟩
  cases op <;> simp [fren_spec, goal_holds?, integer_domain?, partial?] <;> grind

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
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

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
impl cut_proof: cut for (prog : Snoc Declared) (rows : Snoc Row) (env : Snoc Value)
    (hyps : Snoc Fact) (root : Int) (goal : Goal) {
  prog := prog, rows := rows, env := env, hyps := hyps, root := root, goal := goal, holds? := true
} by
  intro prog rows env hyps root goal _
  simp only [cut.ensures, cut.ensure.output, cut.ensure.asserted]
  refine ⟨trivial, ?_⟩
  simp [satisfied?, some_refuted?, fact_refuted?, goal_holds?, fren_spec] <;> grind

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
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
  simp only [spec.verification.worked_examples.ensures, spec.verification.worked_examples.ensure.output, spec.verification.worked_examples.ensure.guarded,
    spec.verification.worked_examples.ensure.conjunction, spec.verification.worked_examples.ensure.unused, spec.verification.worked_examples.ensure.bound,
    spec.verification.worked_examples.ensure.shared, spec.verification.worked_examples.ensure.call, spec.verification.worked_examples.ensure.negation,
    spec.verification.worked_examples.ensure.matched]
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

open spec.verification in
impl tables_proof: tables { holds? := true } by
  intro _
  simp only [tables.ensures, tables.ensure.output, tables.ensure.omitted,
    tables.ensure.present, tables.ensure.extra, tables.ensure.separate,
    tables.ensure.unmoved]
  decide

open spec.surface (BinaryOp UnaryOp Snoc)
open spec.names hiding collect
open spec.types spec.statics spec.denotation spec.dynamics spec.verification in
impl represented_proof: represented for (symb : Snoc Entry) (decls : Snoc Decl)
    (prog : Snoc Declared) (item : Fren.Seq String) (body : Snoc Row) {
  symb := symb, decls := decls, prog := prog, item := item, body := body, holds? := true
} by
  intro symb decls prog item body _
  simp only [represented.ensures, represented.ensure.output, represented.ensure.kept,
    represented.ensure.none]
  refine ⟨trivial, ?_, ?_⟩
  · cases hd : declaration_of prog item with
    | none => simp [represents?, all_tabled?, tabled?, has_body?, hd, fren_spec]
    | some found =>
      cases h : found.body <;> simp [represents?, all_tabled?, tabled?, has_body?, hd, h, fren_spec]
  · simp [represents?, all_tabled?, tabled?, declaration_of, fren_spec]

set_option fren.requireEvidence "trusted" in
#fren_trace
