-- keep-sorted start
import Impls.Impl
import Impls.View
-- keep-sorted end
open Fren.Lang

/-!
# Traceability (`Reqs/Trace`)

The evidence for Fren's components that cannot be proved in Lean, and the
links for the traceability rules themselves.
-/

namespace Fren.Impls

/-! ## Claims -/

tested cli::agreement: "src/FrenTestMain.lean"
tested cli::accepts: "test/ui/lean_code.fren", "test/ui/lean_impl.fren"
tested modules::two_segments: "test/ui/scoping.fren"
tested lang::operand: "test/ui/precedence.fren", "test/cli/f0107_iff.fren", "test/cli/f0108_chain.fren",
  "test/cli/f0109_operand.fren"
tested lang::operator_type: "test/ui/types.fren", "test/cli/f0304_arith.fren", "test/cli/f0304_operand.fren",
  "test/cli/f0305_bool_int.fren", "test/cli/f0305_enum_int.fren", "test/cli/f0306_branches.fren"
tested lang::modifiers: "test/cli/f0110_pub_in.fren", "test/cli/f0114_input_definition.fren", "test/cli/f0113_det_in.fren", "test/cli/f0113_pub_inst.fren"
tested lang::function_body: "test/ui/defined_functions_static.fren", "test/cli/f0331_recursive.fren"
tested lang::argument: "test/ui/defined_functions.fren", "test/ui/functions_static.fren"
tested lang::relation_op: "test/ui/relations.fren", "test/ui/relations_static.fren", "test/cli/f0328_join.fren"
tested lang::pair_membership: "test/ui/relations.fren", "test/ui/relations_static.fren", "test/cli/f0329_pair.fren"
tested lang::finite: "test/ui/relations_static.fren", "test/ui/sets.fren"
tested check::minimal: "test/ui/redundancy.fren", "test/ui/self_conflict.fren"
tested lang::path_shape: "test/ui/scoping.fren"
tested lang::declared_before: "test/ui/scoping.fren"
tested inst::earlier: "test/ui/instances_static.fren"
tested lint::history: "test/cli/f0709_forbid.fren"
tested lang::identifier: "test/ui/syntax_lexical.fren", "test/ui/syntax_identifier.fren",
  "test/ui/syntax_identifier_letters.fren", "test/ui/syntax_identifier_quoted.fren", "test/ui/syntax_identifier_claim.fren",
  "test/ui/syntax_identifier_token.fren", "test/ui/syntax_identifier_unclosed.fren", "test/cli/f0119_identifier.fren"
tested lang::escape_sequence: "test/ui/syntax_lexical.fren", "test/cli/f0115_escape.fren"
tested lang::punctuator_end: "test/ui/syntax_lexical.fren", "test/cli/f0105_eqeq.fren"
tested lang::unbounded: "test/ui/relations_static.fren", "test/ui/datatypes_static.fren"

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
