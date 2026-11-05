-- The `tested` claims of Fren's own code, and the evidence for each of
-- Fren's components. It imports every module of `Impls`, and every
-- requirement, as `Reqs` does, so that `#fren_trace` sees the components of
-- those that no module implements. It reads the tests, so its library is
-- `ImplsTested`, which needs them; it is not the root module `Impls`, which
-- the library `Impls` builds (`lakefile.lean`).
-- keep-sorted start
import Impls.Assumptions
import Impls.Calls
import Impls.Chains
import Impls.Check
import Impls.Cli
import Impls.Elements
import Impls.Enumeration
import Impls.Eval
import Impls.Fmt
import Impls.Generated
import Impls.Global
import Impls.GroundMatching
import Impls.Guards
import Impls.HigherOrder
import Impls.Impl
import Impls.Induction
import Impls.Lang
import Impls.Lint
import Impls.Markdown
import Impls.Models
import Impls.Modules
import Impls.Mutate
import Impls.PassEvidence
import Impls.PatternTests
import Impls.Procedures
import Impls.QueryCache
import Impls.Renaming
import Impls.Repeats
import Impls.Rewrites
import Impls.Scope
import Impls.Semantics
import Impls.SubsetTypes
import Impls.Testing
import Impls.Theories
import Impls.Trace
import Impls.TypeFacts
import Impls.View
import Reqs
-- keep-sorted end

open Fren.Lang

tested cli::fix_static_errors: "src/FrenTestMain.lean"

tested lang::global_checks: "test/ui/lang/global.fren", "test/ui/lang/global_preconditions.fren"
tested lang::global_successor: "test/ui/lang/global_preconditions.fren"
tested lang::induction_candidate: "test/ui/checks/induction.fren"
tested lang::induction_hypotheses: "test/ui/checks/induction.fren"
tested lang::induction_verdict: "test/ui/checks/induction.fren"
tested lang::trait_expectation: "test/ui/lang/traits.fren"
tested view::inconclusive_reported: "src/FrenTest/InconclusiveReported.lean", "test/ui/lang/traits.fren", "test/ui/lang/traits_frontends.fren"
tested refinement::positional_refinement: "test/ui/lang/refines.fren", "src/FrenTest/RefinesTests.lean"
tested refinement::block_refinement: "test/ui/lang/refines.fren", "src/FrenTest/RefinesTests.lean"
tested refinement::refinement_computed_local: "test/ui/lang/refines.fren", "src/FrenTest/RefinesTests.lean"
tested refinement::refinement_result_domain: "test/ui/lang/refines_pattern.fren"
tested refinement::refinement_singleton_domain: "test/ui/checks/refines_tested.fren"

-- Concrete feature regressions and exhaustive finite backend checks.
tested check::decidable_unknown: "src/FrenTest/InconclusiveReported.lean"
tested check::output_query_core: "src/FrenTest/InconclusiveReported.lean",
  "src/FrenTest/OutputQueryCore.lean", "test/ui/checks/output_query_core.fren"
tested check::branch_forcing: "src/FrenTest/BranchForcing.lean"
tested check::branch_member_polarity: "src/FrenTest/BranchForcing.lean"
tested check::branch_query_count: "src/FrenTest/BranchForcing.lean"
tested check::branch_query_families: "src/FrenTest/BranchForcing.lean"
tested check::conditional_branch_core: "src/FrenTest/BranchForcing.lean"
tested check::disjunction_core: "src/FrenTest/BranchForcing.lean"
tested check::fact_applications: "test/ui/checks/fact_scope.fren", "test/cli/args/dump_smt_fact_scope.fren", "src/FrenTest/AppFacts.lean"
tested lang::block_evaluation: "src/FrenTest/BooleanSubsets.lean", "src/FrenTest/BooleanModels.lean"
tested lang::block_result: "test/cli/results/boolean_block_members.fren"
tested lang::block_values: "src/FrenTest/BooleanModels.lean", "test/cli/results/boolean_block_members.fren"
tested lang::boolean_block: "src/FrenTest/BooleanSubsets.lean"
tested lang::clause_leaf_path: "src/FrenTest/NamedPredicateExpansion.lean"
tested lang::clause_partition: "src/FrenTest/NamedPredicateExpansion.lean", "src/FrenTest/CoverMembers.lean"
tested lang::distributed_guard: "src/FrenTest/NamedPredicateExpansion.lean", "src/FrenTest/CoverMembers.lean"
tested lang::equivalence_branches: "src/FrenTest/BranchForcing.lean", "test/ui/checks/quantified_iff_definition.fren"
tested lang::equivalence_three: "src/FrenTest/BooleanSubsets.lean"
tested lang::exactly_one_branch: "src/FrenTest/BranchForcing.lean"
tested lang::exactly_one_reach: "src/FrenTest/BooleanSubsets.lean", "src/FrenTest/BooleanModels.lean"
tested lang::exactly_one_result: "src/FrenTest/BooleanSubsets.lean", "test/cli/results/boolean_block_members.fren"
tested lang::fixed_inhabitation: "src/FrenTest/SubsetInhabitation.lean", "src/FrenTest/SubsetObligations.lean"
tested lang::named_conjunction: "src/FrenTest/NamedPredicateExpansion.lean", "test/cli/results/boolean_block_members.fren"
tested lang::named_identity: "src/FrenTest/NamedPredicateExpansion.lean", "src/FrenTest/BooleanModels.lean"
tested lang::named_node: "src/FrenTest/NamedPredicateExpansion.lean", "test/cli/results/boolean_block_members.fren"
tested lang::query_purpose: "src/FrenTest/SubsetInhabitation.lean"
tested lang::refinement_subset_domain: "src/FrenTest/SubsetObligations.lean"
tested lang::subset_closed: "test/cli/types/f0373_subset_closed.fren"
tested lang::subset_earlier: "src/FrenTest/SubsetObligations.lean"
tested lang::subset_inhabitation: "src/FrenTest/SubsetInhabitation.lean", "src/FrenTest/SubsetObligations.lean"
tested lang::subset_inheritance: "test/cli/types/subset_inheritance.fren", "src/FrenTest/NestedSubsetEnumeration.lean"
tested lang::subset_labels: "test/cli/types/f0372_subset_labels.fren", "src/FrenTest/EmptySubset.lean"
tested lang::subset_membership: "src/FrenTest/BooleanSubsets.lean", "src/FrenTest/NestedSubsetEnumeration.lean"
tested lang::subset_obligations: "src/FrenTest/SubsetObligations.lean", "src/FrenTest/NestedSubsetEnumeration.lean"
tested lang::varying_inhabitation: "src/FrenTest/SubsetInhabitation.lean", "src/FrenTest/SubsetObligations.lean"
tested lang::recursive_post_result: "test/ui/checks/recursive_subsets.fren"
tested lint::duplicate_scrutinee: "test/ui/lints/duplicate_scrutinee.fren"

-- The dynamic semantics (`Reqs/Lang/Semantics`). `lang::coincidence` and
-- `lang::closed` are proved in `Impls/Semantics.lean`, and
-- `lint::written_scopes` and `lint::manual_at_most_one_defined` in
-- `Impls/Lint.lean`, for every input; these tests are cross-checks, by random
-- expressions evaluated with what they do not mention changed, and the
-- binary's evaluator against `lang::eval`.
tested lang::coincidence: "src/FrenTest/Semantics.lean"
tested lang::closed: "src/FrenTest/Semantics.lean"
tested lint::written_scopes: "src/FrenTest/Semantics.lean"
tested lint::ifs_same_cond_taken: "src/FrenTest/Semantics.lean"
tested lint::manual_at_most_one_defined: "src/FrenTest/Semantics.lean"
-- Both front ends' fill rules, on five types, against `model::default_value`.
tested model::fill_rule: "src/FrenTest/ModelDefaults.lean"
-- No front end elaborates a name into the semantics' abstract syntax yet,
-- so there is no code to bind `lang::named` to; its expectations are
-- checked by the solver.
trusted lang::named: "no front end elaborates a name into the semantics' abstract syntax yet, so there is no code to bind it to; its expectations are checked by the solver"

-- The eight theory-core requirements below have `impl`s proved for every
-- input in `Impls/Theories.lean`; these tests are regression cross-checks.
-- Front ends adopt the structural core in later units of #761.
tested lang::theory_signature: "src/FrenTest/Theories.lean"
tested lang::theory_term_translation: "src/FrenTest/Theories.lean"
tested lang::theory_term_substitution: "src/FrenTest/Theories.lean"
tested lang::theory_ground_term: "src/FrenTest/Theories.lean"
tested lang::theory_variable_images: "src/FrenTest/Theories.lean"
tested lang::theory_term_list: "src/FrenTest/Theories.lean"
tested lang::theory_translation: "src/FrenTest/Theories.lean"
tested lang::theory_instance: "src/FrenTest/Theories.lean"

-- Structural matching equations are proved for every input; these tests
-- exercise their composition before front-end integration in unit 10.
tested lang::ground_match_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_parameter_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_extension_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_normalization: "src/FrenTest/GroundMatching.lean"
tested lang::ground_shape_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_subject_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_selection_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_variables_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_join_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_listed_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_sentence_lists_step: "src/FrenTest/GroundMatching.lean"
tested lang::ground_rule_step: "src/FrenTest/GroundMatching.lean"

-- Implementations, dispatch and what each check rests on
-- (`Reqs/Lang/Implementations`), and the verdicts of today's forms under
-- them (`Reqs/ModuleReports`), are a design that no front end implements
-- yet (#669, stage 3), so there is no code to bind them to.
trusted lang::module_sentence: "the design of implementations (#669, stage 3); no front end reads a module as this model yet, and its examples are checked by testing"
trusted lang::module_rests_on: "the design of what each check rests on (#669, stage 3); the solver proves its cases ranked and the enumeration of small modules checks them acyclic"
trusted lang::dispatch: "the design of dispatch (#669, stage 3); no front end dispatches to implementations yet, and its expectations are checked by the solver"
trusted lang::sentence_instantiation: "the design of instantiation (#669, stage 3); no front end instantiates these items yet, and its examples are checked by testing"
trusted lang::ensure_clause: "the design of contracts as sentences (#669, stage 3); nothing reads an ensure clause as a sentence yet, and its expectations are checked by testing"
trusted lang::sentence_use: "the design of instantiation (#669, stage 3); no front end chooses what a check uses yet, and its examples are checked by testing"
trusted expansion::premise_verdicts: "the design of premise verdicts under instantiation (#669, stage 3); the solver checks that expansion only settles checks, from each check's own query inputs"
trusted expansion::today_verdict: "the design of the verdicts of today's forms under instantiation (#669, stage 3); the solver checks strict expansion of it over every model and kind"
trusted lang::arm_decided: "the design of induction by unfolding (#669, stage 4); nothing implements unfolding yet, and its expectations are checked by testing"
trusted lang::caveat_premise: "the design of what a check reports of the axioms it rests on (#669, stage 3); the solver checks it against today's reports of modules of today's forms"

-- Modules as theories, and the items that state claims
-- (`Reqs/Lang/ModulesAndInterfaces`), are a design that no front end
-- implements yet (#669), so there is no code to bind them to.
trusted lang::sentence_place: "the design of the places of claim items and clauses (#669); no front end decides acceptance by it yet, and its expectations are checked by enumeration"
trusted lang::sentence_member: "the design of the blocks of lemma and assume items (#669); no front end decides block members by it yet, and its expectations are checked by enumeration"
trusted lang::sentence_role: "the design of the roles of sentences (#669); no front end decides roles by it yet, and its expectations are checked by testing"
trusted lang::lemma_order: "the design of the order of lemma items (#669, stage 3); nothing reads lemma items yet, and its expectations are checked by testing"

-- The matrix of what each method can conclude is a design, refined by
-- what runs today (`check::method_run`), which is bound to `dispatchOf`.
trusted check::method_cell: "the design of the proof methods; check::today_within_matrix checks check::method_run, bound to dispatchOf, against it, and check::enumeration_within_matrix and eval::random_within_matrix the verdicts of enumeration and testing"
-- No code combines verdicts yet: `fren.evidence` takes no sets (#368).
trusted check::combined: "no front end combines the verdicts of several methods yet; its expectations are checked by the solver"
-- Both front ends run every premise of what they report, `#fren_check`
-- those of the items it names too, and keep their evidence
-- (`Reqs/Evidence`); what `#fren_check` reports of them is proved
-- (`check::hosted_runs`, `Impls/PassEvidence`). The ui tests run through
-- both front ends; `EvidenceClient` checks a caller of a procedure that an
-- imported module checked.
tested check::runs_premises: "test/ui/checks/evidence_premises.fren", "test/ui/checks/evidence_missing_premise.fren", "test/ui/checks/evidence_refinement.fren", "test/ui/checks/evidence_contracts.fren", "src/FrenTest/EvidencePremises.lean", "src/FrenTest/EvidenceLib.lean", "src/FrenTest/EvidenceClient.lean"

tested eval::outputs_seen: "src/FrenTest/OutputsSeen.lean"
-- The search of the evaluator's realizability goal (`FrenCli.Confirm`,
-- `Fm.exOutputs`) is not a function of the sets that the Req takes, so the
-- ui test checks it through the `fren` command.
tested eval::outputs_confirm: "test/ui/checks/realizable_subset_outputs.fren"

tested check::general_branch_explanation: "src/FrenTest/BranchForcing.lean"
tested check::retry_alternatives_general: "src/FrenTest/BranchForcing.lean"

-- Multi-column matching is checked against actual frontend programs and all Boolean vector worlds.
tested lang::match_namespace: "test/ui/lang/multi_match_names.fren", "src/FrenTestFiles/LambdaMatch.lean"
tested lang::match_vector: "test/ui/lang/lambda_match.fren", "test/ui/lang/multi_match_errors.fren", "src/FrenTestFiles/LambdaMatch.lean", "src/FrenTestMain.lean"
tested lang::match_vector_coverage: "test/ui/lang/multi_match_errors.fren", "src/FrenTestFiles/LambdaMatch.lean"

-- The evidence for each of Fren's components, and the converse of the
-- `tested` claims over the tests. Every requirement must be traced somehow:
-- a component without evidence is a warning, which fails CI's
-- `lake build --wfail`.
set_option fren.requireEvidence "trusted" in
set_option fren.testGlobs "test/**/*.fren src/FrenTest/*.lean src/FrenTestFiles/*.lean src/FrenTestMain.lean" in
#fren_trace
