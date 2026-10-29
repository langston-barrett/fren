-- Fren's own code, linked to its requirements with `impl`. `lake build`
-- proves each link. It imports every requirement, as `Reqs` does, so that
-- `#fren_trace` sees the components of those that no module implements.
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
import Impls.HigherOrder
import Impls.Impl
import Impls.Lang
import Impls.Lint
import Impls.Modules
import Impls.Mutate
import Impls.PatternTests
import Impls.PatternTypes
import Impls.Procedures
import Impls.Repeats
import Impls.Scope
import Impls.Trace
import Impls.TypeFacts
import Impls.View
import Reqs
-- keep-sorted end

open Fren.Lang

tested cli::fix_static_errors: "src/FrenTestMain.lean"

tested lang::global_checks: "test/ui/lang/global.fren", "test/ui/lang/global_preconditions.fren"
tested lang::global_successor: "test/ui/lang/global_preconditions.fren"
tested refinement::positional_refinement: "test/ui/lang/refines.fren", "src/FrenTest/RefinesTests.lean"
tested refinement::block_refinement: "test/ui/lang/refines.fren", "src/FrenTest/RefinesTests.lean"
tested refinement::refinement_computed_local: "test/ui/lang/refines.fren", "src/FrenTest/RefinesTests.lean"
tested refinement::refinement_result_domain: "test/ui/lang/refines_pattern.fren"
tested refinement::refinement_singleton_domain: "test/ui/checks/refines_tested.fren"

-- Concrete feature regressions and exhaustive finite backend checks.
tested check::branch_forcing: "src/FrenTest/BranchForcing.lean"
tested check::branch_member_polarity: "src/FrenTest/BranchForcing.lean"
tested check::branch_query_count: "src/FrenTest/BranchForcing.lean"
tested check::branch_query_families: "src/FrenTest/BranchForcing.lean"
tested check::conditional_branch_core: "src/FrenTest/BranchForcing.lean"
tested check::disjunction_core: "src/FrenTest/BranchForcing.lean"
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

-- The dynamic semantics (`Reqs/Lang/Semantics`): its coincidence lemma, by
-- random expressions evaluated with a variable that they do not mention
-- rebound, and the binary's evaluator against `lang::eval`.
tested lang::coincidence: "src/FrenTest/Semantics.lean"
tested lang::closed: "src/FrenTest/Semantics.lean"
tested lint::written_scopes: "src/FrenTest/Semantics.lean"
tested lint::manual_at_most_one_defined: "src/FrenTest/Semantics.lean"
-- No front end elaborates a name into the semantics' abstract syntax yet,
-- so there is no code to bind `lang::named` to; its expectations are
-- checked by the solver.
trusted lang::named: "no front end elaborates a name into the semantics' abstract syntax yet, so there is no code to bind it to; its expectations are checked by the solver"

tested check::general_branch_explanation: "src/FrenTest/BranchForcing.lean"
tested check::retry_alternatives_general: "src/FrenTest/BranchForcing.lean"

-- Multi-column matching is checked against actual frontend programs and all Boolean vector worlds.
tested lang::match_namespace: "test/ui/lang/multi_match_names.fren", "src/FrenTest/LambdaMatch.lean"
tested lang::match_vector: "test/ui/lang/lambda_match.fren", "test/ui/lang/multi_match_errors.fren", "src/FrenTest/LambdaMatch.lean", "src/FrenTestMain.lean"
tested lang::match_vector_coverage: "test/ui/lang/multi_match_errors.fren", "src/FrenTest/LambdaMatch.lean"

-- The evidence for each of Fren's components, and the converse of the
-- `tested` claims over the tests. Every requirement must be traced somehow:
-- a component without evidence is a warning, which fails CI's
-- `lake build --wfail`.
set_option fren.requireEvidence "trusted" in
set_option fren.testGlobs "test/**/*.fren src/FrenTest/*.lean src/FrenTestMain.lean" in
#fren_trace
