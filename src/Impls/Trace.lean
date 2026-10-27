-- keep-sorted start
import Impls.Impl
import Impls.View
import Reqs.Eval
import Reqs.Fmt
import Reqs.Lint
import Reqs.Modules
import Reqs.Trace
-- keep-sorted end
open Fren.Lang

/-!
# Traceability (`Reqs/Trace`)

The evidence for Fren's components that cannot be proved in Lean, and the
links for the traceability rules themselves.
-/

namespace Fren.Impls

/-! ## Claims

A `tested` claim reads the tests, so Lake must rebuild its module when a
test changes: such claims are only here and in `Impls.Lint`, the modules of
Impls whose library says so, with `Impls` (`lakefile.lean`). -/

tested cli::agreement: "src/FrenTestMain.lean"
tested eval::backjumping: "src/FrenTestMain.lean"
tested cli::accepts: "test/ui/lean/lean_code.fren", "test/ui/lean/lean_impl.fren"
tested modules::two_segments: "test/ui/lang/scoping.fren", "test/ui/lang/prelude.fren"
-- The sorts and declarations that the `fren` command gives the solver are
-- strings, which Lean does not reduce far enough to compare: the snapshot of
-- `--dump-smt` shows them for the examples.
tested lang::smt_encoding: "test/cli/args/dump_smt_generic.fren"
tested lang::prelude_smt: "test/cli/args/dump_smt_prelude.fren"
tested lang::operand: "test/ui/lang/precedence.fren", "test/cli/syntax/f0107_iff.fren", "test/cli/syntax/f0109_operand.fren"
-- `neededDefs` reads the names that each expression's tokens mention; the
-- tests check the definitions it gives each expression against the spec.
tested lang::fn_definitions: "test/ui/lang/function_blocks.fren", "test/ui/syntax/fn_block_mentions_result.fren"
tested lang::operator_type: "test/ui/lang/types.fren", "test/ui/lang/ordered_enums_static.fren",
  "test/cli/types/f0304_arith.fren", "test/cli/types/f0304_operand.fren",
  "test/cli/types/f0305_bool_int.fren", "test/cli/types/f0305_enum_int.fren", "test/cli/types/f0306_branches.fren",
  "test/ui/lang/nat.fren", "test/ui/lang/nat_static.fren", "test/cli/types/f0304_narrowing.fren",
  "test/ui/lang/newtypes.fren", "test/ui/lang/newtypes_static.fren", "test/ui/lang/membership_static.fren",
  "test/ui/lang/ordered_structs.fren", "test/ui/lang/ordered_structs_static.fren"
tested lang::widening: "test/ui/lang/nat.fren", "test/ui/lang/nat_static.fren", "test/cli/types/f0304_narrowing.fren"
tested lang::literal_type: "test/ui/lang/nat.fren", "test/ui/lang/nat_static.fren"
tested lang::nat_variable: "test/ui/lang/nat.fren"
tested lang::pattern_place: "test/ui/lang/pattern_types_static.fren"
tested lang::pattern_binding: "test/ui/lang/pattern_binders.fren", "test/ui/checks/pattern_binders.fren"
tested lang::pattern_finite: "test/ui/lang/pattern_types_meaning.fren"
tested lang::pattern_widening: "test/ui/checks/pattern_obligations.fren"
tested check::pattern_obligation: "test/ui/checks/pattern_obligations.fren", "test/ui/checks/pattern_obligations_elements.fren"
tested lang::nat_place: "test/ui/lang/nat_static.fren", "test/cli/types/f0338_payload.fren", "test/ui/lang/pattern_types_static.fren",
  "test/ui/lang/pattern_types_meaning.fren", "test/ui/lang/nat_fields.fren",
  "test/cli/types/f0338_element.fren", "test/ui/lang/let_types.fren"
tested lang::modifiers: "test/cli/syntax/f0110_pub_param.fren", "test/cli/syntax/f0110_det_param.fren", "test/cli/syntax/f0113_det_assume.fren", "test/cli/syntax/f0113_pub_inst.fren"
tested lang::function_body: "test/ui/lang/defined_functions_static.fren", "test/cli/types/f0331_recursive.fren"
tested lang::structural_recursion: "test/ui/lang/structural_recursion_static.fren", "test/cli/types/f0447_count.fren"
tested lang::recursive_kind: "test/ui/checks/recursion.fren"
tested lang::recursive_decided: "test/ui/checks/recursion.fren", "test/ui/checks/recursion_undecidable.fren"
tested lang::recursive_match: "test/ui/lang/structural_recursion_static.fren", "test/cli/types/f0449_literal.fren"
tested lang::argument: "test/ui/lang/defined_functions.fren", "test/ui/lang/functions_static.fren"
tested lang::cardinality_args: "test/ui/lang/cardinality_static.fren", "test/cli/types/f0304_cardinality.fren",
  "test/cli/types/f0367_no_arguments.fren"
tested lang::relation_op: "test/ui/lang/relations.fren", "test/ui/lang/relations_static.fren", "test/cli/types/f0328_join.fren"
tested lang::pair_membership: "test/ui/lang/relations.fren", "test/ui/lang/relations_static.fren", "test/cli/types/f0329_pair.fren"
tested lang::quantifier: "test/ui/lang/quantifiers.fren", "test/ui/lang/quantifiers_places.fren"
tested lang::quantified_type: "test/ui/lang/quantifiers.fren", "test/ui/lang/quantifiers_static.fren",
  "test/ui/lang/quantifiers_unbounded.fren", "test/ui/lang/type_facts.fren"
tested lang::quantifier_size: "test/ui/lang/quantifiers.fren", "test/ui/lang/quantifiers_static.fren"
tested lang::quantifier_binder: "test/ui/lang/quantifiers_global.fren"
tested check::minimal: "test/ui/checks/redundancy.fren", "test/ui/checks/self_conflict.fren"
tested check::clash_notes: "test/ui/checks/forced_outputs.fren", "test/ui/checks/forced_variants.fren",
  "test/cli/results/f0601_forced.fren", "test/cli/results/f0601_forced_all.fren",
  "test/cli/results/f0601_forced_none.fren", "test/cli/results/f0601_forced_variant.fren",
  "test/cli/results/f0601_forced_variant_all.fren", "test/cli/results/f0601_forced_variant_none.fren",
  "test/cli/results/f0601_forced_variants_both.fren"
tested lang::path_shape: "test/ui/lang/scoping.fren"
tested lang::declared_before: "test/ui/lang/scoping.fren"
tested lang::definition_order: "test/ui/lang/let.fren", "test/ui/lang/let_static.fren",
  "test/cli/types/f0341_defined_later.fren", "test/cli/types/f0341_itself.fren"
tested lang::definition_type: "test/ui/lang/let.fren", "test/ui/lang/let_static.fren", "test/ui/lang/let_types.fren",
  "test/cli/types/f0342_definition_type.fren"
tested lang::definition_form: "test/ui/lang/let.fren", "test/ui/lang/quantifiers_let.fren", "test/ui/syntax/let_quantifier.fren",
  "test/ui/syntax/where_quantifier.fren", "test/ui/syntax/let_operand.fren", "test/ui/syntax/let_definition.fren",
  "test/cli/types/f0302_let_membership.fren", "test/cli/syntax/f0109_let.fren"
tested call::earlier: "test/ui/lang/instances_static.fren"
tested lint::history: "test/cli/lints/settings/f0709_forbid.fren", "test/cli/lints/settings/f0709_forbid_in_file.fren"
tested lint::stepwise: "test/cli/lints/settings/f0709_forbid_in_file.fren"
tested lang::identifier: "test/ui/syntax/lexical.fren", "test/ui/syntax/identifier.fren",
  "test/ui/syntax/identifier_letters.fren", "test/ui/syntax/identifier_quoted.fren", "test/ui/syntax/identifier_claim.fren",
  "test/ui/syntax/identifier_token.fren", "test/ui/syntax/identifier_unclosed.fren",
  "test/ui/syntax/identifier_check.fren", "test/cli/syntax/f0119_identifier.fren"
tested lang::identifier_shape: "test/ui/syntax/lexical.fren"
tested lang::longest_identifier: "test/ui/syntax/lexical.fren"
tested lang::escape_sequence: "test/ui/syntax/lexical.fren", "test/cli/syntax/f0115_escape.fren"
tested lang::punctuator_end: "test/ui/syntax/lexical.fren", "test/cli/syntax/f0105_eqeq.fren"
tested lang::escape_text: "test/ui/syntax/lexical.fren"
tested lang::escape_start: "test/ui/syntax/lexical.fren", "test/cli/syntax/f0115_escape.fren"
tested lang::longest_punctuator: "test/ui/syntax/lexical.fren"
tested lang::type_facts: "test/ui/lang/relations_static.fren", "test/ui/lang/sets.fren",
  "test/ui/lang/datatypes_static.fren", "test/ui/lang/type_facts.fren"
tested fmt::safe: "src/FrenTestMain.lean"
-- `lake test` checks that every code is well formed and in its group.
tested view::code_group: "src/FrenTestMain.lean"

trusted view::build: "Lake fails a build whose modules log an error, and with `--wfail` one whose modules log a warning"

/-! ## Implementations -/

open Fren.Core (Level directLevel evidenceLevel traceSeverity testedFileAccepted
  coversLineAccepted trustedAccepted traceExitCode)

instance : Fren.Finite Level :=
  ⟨[.missing, .trusted, .tested, .solver, .proved], by intro x; cases x <;> simp⟩

def toTraceLevel : Level → trace.Level
  | .missing => .Missing
  | .trusted => .Trusted
  | .tested => .Tested
  | .solver => .Solver
  | .proved => .Proved

impl rank: trace::rank for (l : Level) {
  level := toTraceLevel l,
  r := l.rank,
}

impl direct: trace::direct for (p s t u : Bool) {
  proved? := p,
  solver? := s,
  tested? := t,
  trusted? := u,
  level := toTraceLevel (directLevel p s t u),
}

-- The instances' ranks are internal, so they are given: `decide` cannot
-- choose integers.
impl evidence: trace::evidence for (own : Level) (o : Bool) (w : Level) {
  own := toTraceLevel own,
  has_outputs? := o,
  weakest := toTraceLevel w,
  level := toTraceLevel (evidenceLevel own o w),
} by
  intro own o w _
  refine ⟨_, own.rank, _, w.rank, ?_, ⟨rfl, trivial, ?_⟩, ⟨rfl, trivial, ?_⟩⟩ <;>
    cases own <;> cases w <;> cases o <;> decide

impl required: trace::required for (l t : Level) (e : Bool) {
  level := toTraceLevel l,
  threshold := toTraceLevel t,
  enforced? := e,
  severity := toLevel (traceSeverity l t e),
} by
  intro l t e _
  refine ⟨_, l.rank, _, t.rank, ?_, ⟨rfl, trivial, ?_⟩, ⟨rfl, trivial, ?_⟩⟩ <;>
    cases l <;> cases t <;> cases e <;> decide

impl tested_file: trace::tested_file for (e c : Bool) {
  exists? := e,
  covers? := c,
  accepted? := testedFileAccepted e c,
}

impl covers_line: trace::covers_line for (e c : Bool) {
  component_exists? := e,
  claimed? := c,
  accepted? := coversLineAccepted e c,
}

-- For every justification, with `checkTrusted`, which both front ends use;
-- the spec's justification is trimmed.
impl trusted_claim: trace::trusted_claim for (s : String) {
  why := Fren.Core.trimmedWhy s,
  accepted? := (Fren.Core.checkTrusted s).isOk,
} by
  intro s _
  by_cases h : Fren.Core.trimmedWhy s = "" <;>
    simp [fren_spec, Fren.Core.checkTrusted, trustedAccepted, Fren.Str.lit, h, Except.isOk, Except.toBool] <;> rfl

impl trace_exit: trace::trace_exit for (ran below stray : Bool) {
  ran? := ran,
  below? := below,
  stray? := stray,
  code := (traceExitCode ran below stray).toNat,
}

end Fren.Impls
