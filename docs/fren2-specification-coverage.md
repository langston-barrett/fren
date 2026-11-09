# Fren2 specification implementation and proof coverage

The normative reference is `src/Spec/`. It defines a precise source domain:
Booleans, mathematical integers, payload-free nominal enums, named functions,
lets, conditionals, constructor matches and global assumption/expectation
members. Implementation status, checklists and historical evidence belong here.
Neither the reference's scope nor a successful example asserts that the whole
Fren language or compiler has been verified.

## Language core correspondence

`Spec/Language/Types.md` defines `Ty`, `Value`, canonical source `ItemId`,
`Context`, signatures, constructor ownership, operator typing and a finite
postorder expression derivation. Its predicates compute decisions from raw
forms, child indices, exact contexts and symbols; candidate row types are
checked witnesses, never assumed judgments. Guarded integer quantifiers range
over supplied finite sequences. Fren1's `undecidable` lint opt-outs reflect
its solver fragment and sequence encoding, not mathematical undecidability
of checking a finite derivation. Universal SMT validity and unbounded witness
search are not claimed decidable. General multiplication and Euclidean value
laws remain mathematical reference rules: the current checker accepts linear
arithmetic and fixed divisors only.

The source representation uses canonical sequences of named components.
Production `FrenBase.ItemId` also admits generated components; they are not
source declarations in this domain. No display string or hash is an identity.
The existing integer-atom `ValueKind` contracts and all three genuine `impl`
bindings are retained unchanged as adapters for `FrenExpr`'s generic primitive
compatibility/unary/binary functions. They are not the normative type data.
The type wrapper proves injectivity of the new `Ty` adapter and exact
compatibility, unary and binary typing through the production generic type
carrier. These proofs cover arbitrary canonical identity sequences and all
operators, rather than bounded enum samples. The `local_rule?`
judgment is not yet bound to the entire production traversal. `FrenHirToThir.HasValue` states recursive
typing over the real retained AST, and `FrenHirToThir.TypingSound` remains an
unproved universal obligation. Finite examples, native tests, Plausible and
local derivation equations cannot discharge it. The postorder induction and
converse tree-flattening arguments in the reference describe the mathematical
closure; they are not claimed here as checked Lean proofs of the source adapter.

- [ ] Prove a complete occurrence/context-preserving source-to-derivation
  correspondence and the actual checker's `TypingSound` theorem.
- [ ] Prove universal match-coverage and call-graph correspondence separately
  from typing, preserving all branch bodies and unused definitions.
- [ ] Formalize interpretation/free-local/mentioned-item recursive closure
  against actual binding and expression code, including capture avoidance.
- [ ] Establish universal value and declarative source-obligation preservation
  for each actual lowering stage under independently justified domains.
- [ ] Resolve mutually partial assumption dependencies before claiming a
  supported verification result for that class. This reference change does
  not choose that semantics.

Runtime evaluation can be left-to-right and short-circuiting on well-defined
values. It does not choose static obligations. Both ordinary Boolean operands
and unused written definitions retain checks; explicit if/match guards supply
conditional contexts. Unknown, exhaustion and unsupported checks are not
proof or undefinedness. No unproved goal is its own premise.

The type and expression wrappers prove every concrete example constant by expanding
its actual finite index domains and simplifying the generated Fren definitions.
The finite-bound lemmas apply to arbitrary integer upper bounds, including
empty/negative ranges. These closed examples are exact checked cases, not
bounded enumeration or sampled traversal soundness.

## Compiler correction units

The shared-core correction's first Compiler unit is THIR: the wrapper
states `ChildContext`, `AtContext`, `Produces`, `BodyTyping`,
`OccurrenceTyping`, `DeclaresBody`, `BodyEntry`, `BodyInventory`,
`TypePassContract`, `MatchCoverage`, `Calls`, `CallPath`,
`Nonrecursive`, `CoverageContract` and `NonrecursionContract` over real code.
It proves retention/admission, uniqueness, failure exclusion, static-boundary
factorization and equivalence of the body obligation to `TypingSound`.
It does not prove `TypePassContract`, `CoverageContract` or
`NonrecursionContract`, or a complete source-to-Fren-derivation bridge.
The desugaring unit below adds its own actual-code contracts. The MIR unit
below adds theory-construction and semantic contracts. The remaining
LIR/OIR/SMT narrative edits do not complete their formal specifications.

Continue the same correction objective with these separate chapter units:

1. **Desugaring extensions** (`SCdesugar`, queued edit 1012): the core identity
   relation and actual API correspondence are specified below. Each additional
   sugar still needs Language semantics, its own transformation rule, typing
   and scoped-obligation/value preservation. No additional sugar is admitted.
2. **MIR extensions** (`SCmir`, 1018): the core formal chapter and conditional
   correspondence laws are specified below. Prove its universal producer
   inventories and recursive semantic premises; extend to procedures/views
   only with their Language semantics.
3. **LIR** (`SClir`, 1024): actual term sorting and scoped verification
   relations, equations/closed sharing/local-let laws and preservation of
   ordinary operands and unused definitions; keep execution strategy separate.
4. **OIR** (`SCoir`, 1026): actual contextual question/extraction judgments,
   independent prerequisite evidence, owner/origin/context completeness,
   polarity and two-way validity correspondence. Keep the mutually partial
   assumption dependency rule unresolved until separately justified.
5. **SMT** (`SCsmt`, 1027): actual query/answer relation, symbol freshness,
   environment and polarity preservation, unknown/resource outcomes, model
   decoding and static source confirmation. Solver responses alone do not
   establish source-level verification.

These are retained substantive obligations, not completed chapters or a
separate plan replacing the implemented shared-core and THIR correction.

## MIR contracts and proof boundary

`Spec/Compiler/Mir.md` now defines a substantive theory-construction chapter
with numbered semantic objects, admission, declaration/member ordering,
owned assumptions and requests, static definedness, interpretation and
confirmation. Its displayed Lean definitions are the wrapper's exact compiled
reference block. They reuse production `Program`, `Typed`, `Theory`, bodies,
contexts, syntax and request data, together with the shared THIR and
Desugaring judgments. No executable compiler or IR is duplicated. The
pointwise Fren question matrix is checked independently of the Lean laws.
The former Light/arithmetic example and its unreferenced `mir.primitive.offset`,
`mir.primitive.implication` and `mir.primitive.amber` identifiers have been
retired from the normative chapter; their old example-only evidence never
established MIR correctness. The historical S1 acceptance record below remains.

`DeclarationFor`, `MemberOrder` and `DeclarationOrder` specify exact source
origins, parameter/result annotations and contexts, body identity, enum
constructor ownership and written order. `DefinitionInventory` and
`RootInventory` state bidirectional completeness over the actual producer
input/output. `RequestFor`, `BlockLayout` and `RequestOrder` specify complete
request fields, indexed multiplicity, all assumptions including later ones,
satisfiability first, one validity question per goal, and block order.
`Constructs` combines these requirements. `PassContract`, the universal claim
that actual production satisfies `Constructs`, remains unproved.

The wrapper proves actual retention/admission, uniqueness, error exclusion,
source-entry success factorization, unchanged admission errors, every actual
request's complete owning context, `BlockLayout` for the real block helper,
and `RequestOrder` for actual producer results. It proves scoped-site retention
under the explicit `RootInventory` premise and bidirectional `ValueOf` and
check meaning under `DefinitionInventory`. Actual evaluator results, including
all negative outcomes and depths, are preserved by equality of the retained
source. These proofs do not assume that finite tests establish the inventories.

`ValueOf` is a declarative defined-value relation on real syntax and named
definitions, including parenthesized callees, exact local slots and fresh
callee parameter environments. It does not specify an outside-domain value.
`StaticAt` traverses ordinary operands and unused let definitions independently
of lazy execution; explicit guards use their original lexical environments.
Its projection to shared scoped traversal is proved. `BodySafe` requires the
actual divisor's nonzero value in every applicable static context.
`VerificationDomain` demands safety of every function definition on every
typed argument assignment, independently safe assumptions, and request demand
roots under those assumptions. It is a sufficient verification domain; the
unresolved mutually partial-assumption dependency class is not silently admitted.

`SemanticDomain` states the shared source static judgments and functionality
of `ValueOf`; no universal proof is claimed. `ConfirmedCounterexample` requires
actual admission/production, construction correspondence, this semantic domain,
request membership, static safety, typed arguments, true assumptions and a
false goal. `counterexample_refutes` proves that these premises refute validity.
A solver SAT answer by itself does not establish source confirmation.

The wrapper checks a real source with three complete function roots and four
ordered requests, then rejects twelve raw request changes, deletion of an
unused function and substitution of another file's origins. A generic request
observation law explains why exact relational fields constrain all such
observations; printed-record comparisons are finite controls, with no universal
injectivity claim. The existing real producer cases and direct Plausible job
also exercise nominal enums, multiple/empty blocks, later assumptions, false
goals, partial expressions, rejections and edited raw outputs. No production
pass, driver, Lake configuration or global compiler budget changes here.

- [ ] Prove `PassContract`, including complete ordered source declaration/member
  correspondence and both definition and static-root inventories, over every
  successful actual producer result.
- [ ] Prove the shared THIR static contracts and defined-value functionality
  that `SemanticDomain` requires; prove actual evaluator adequacy for `ValueOf`
  under independent static verification and sufficient depth.
- [ ] Prove completeness of the recursive static interpretation, including
  all bindings and guard environments, before claiming universal verification
  or source-model confirmation from implementation output.
- [ ] Bind LIR/OIR/SMT preservation and model decoding to these actual relations;
  no solver or lowering correctness is supplied by this MIR chapter.
- [ ] Restate the recursive relations in Fren when it can quantify over the
  real recursive syntax and evidence-carrying program objects. The finite
  question matrix is expressible now; no new Fren1 recursion gate is required.

Primary-reference organization remains the first core unit's actual research
record: FLS [method and subchapter segments](https://rust-lang.github.io/fls/general.html),
[expression rules](https://rust-lang.github.io/fls/expressions.html), and
[The Definition of Standard ML (Revised)](https://smlfamily.github.io/sml97-defn.pdf)
sections 4.1–4.3, 4.10 and 6.1–6.7. The MIR chapter applies the semantic-object,
environment and judgment composition discipline: it defines exact contexts
before rules, separates static premises from value judgments, and states
preservation with its actual hypotheses. The immutable core research receipt
is `out/fren2-language-core/phases/001-author-75cb4488-a40c-4027-a2d1-2a7548ffc302/references.json`;
this unit uses that supplied record while network access is paused.

## Desugaring contracts and proof boundary

`Spec/Compiler/Desugaring.md` displays the exact compiled definitions in its
wrapper: `Program`, `Desugars`, `Produces`, `Rejects`, `Retains`, `Guard`,
`ScopedChild`, `ScopedAt`, `DomainSite`, `Members`, `StaticPreservation`,
`Evaluator`, `InterpretationPreservation`, `ObligationPreservation` and
`PassContract`. These use actual production IR and the shared THIR judgments;
there is no copied executable compiler. Recursive source/typed carriers and
proof-carrying admission are stated in Lean because the current Fren subset
cannot quantify over those actual recursive objects. The existing Fren
example checks its arithmetic/check claims separately. It is not evidence
for the Lean pass contracts.

The wrapper proves the actual `desugar` implements the specified relation,
the complete identity pass contract, exact resolved success and failure,
the type/coverage/non-recursion admission factorization, failure exclusion,
source-result projection, and exact output admission/retention/static facts.
`observation` transfers any predicate or interpretation on the whole retained
resolved/typed pair. `ScopedChild` and its closure project to the shared THIR
context relations. These are universal Lean proofs, not Plausible samples.
The admitted identity transfers properties without proving them true initially.

`DomainSite` states a structural source-obligation inventory over the actual
AST. It includes unused let values and both ordinary Boolean operands;
branch guards retain the context of their subject across later binders.
It records candidate division/remainder sites, not discharged nonzero-divisor
proofs or a complete verification engine. Ordered `Members` observations keep
all assumptions and expectations of a canonical block, including assumptions
written after goals. Full retention separately covers empty blocks and all
source/origin data. Interpreter equality includes all depths, requests and
argument arrays, including negative cases. Neither it nor the generic
observation law proves declarative verification soundness.

The wrapper's structural positive/negative controls distinguish explicit
branches, unguarded ordinary operands, unused let definitions and guard
contexts across binders. Its actual-source control retains bodies, ordered
members, signatures, references and file origins, and rejects type, coverage,
recursion, parse and unsupported-syntax inputs. The existing actual-code
`FrenThirDesugarTests` Plausible and finite tests remain separate bounded
evidence; they do not prove a universal recursive bridge. Exact executions
and deliberate failing mutations are recorded in the external check receipts.

- [ ] Prove `TypePassContract`, `CoverageContract` and `NonrecursionContract`
  for actual THIR production. Identity's static transfer does not discharge
  these antecedent contracts.
- [x] Specify reverse output-to-source soundness, exact occurrence multiplicity
  and written-child postorder in the independently reviewed THIR contract,
  with surplus/wrong-type/context/duplicate and order mutation controls.
  The actual producer's universal `TypePassContract` correspondence remains
  unproved, as recorded above; the strengthened relation and finite controls
  do not discharge that theorem.
- [ ] Prove the converse context projection and the complete scoped-traversal
  bridge to Language free-local/mentioned-item/interpretation semantics,
  including guard evaluation under lexical lets and call substitution.
- [ ] Relate the structural `DomainSite` inventory and retained members to
  declarative source verification and each MIR/LIR/OIR request inventory in
  both directions; prove completeness across all definitions and members.
  Do not infer it from an interpreter's execution trace.
- [ ] Justify the dependency semantics of mutually partial assumptions before
  claiming a verification result for them. No rule in this unit chooses it.
- [ ] Specify each additional sugar and prove its typing, origin and scoped
  obligation/value correspondence, including tables' disjointness marker.
- [ ] Restate these recursive actual-code relations in Fren when its recursive
  types/judgments permit them, without extending Fren1 as a prerequisite.

MIR, LIR, OIR and SMT remain separate substantive correction units above.
No production pass or broader source admission changes in this unit.

## Residual technical spellings

Public rule IDs containing `.walking.` are stable identifiers, not maturity
claims. Actual APIs such as `checkWalking`, `checkWalkingSource`,
`WalkingCoverage`, `WalkingNonrecursive`, and source-file paths ending in
`Walking.lean` remain technical citations. Positive example modules use `signals`; the resolver wrapper uses the same
fixture identity. The
`scratch/expr/Prototype.lean` module name remains only in technical citations
or the retained development records below. No production compiler API was
renamed. The original Fren1-checked Spec wrappers remain outside the Fren2
runtime size-check inventory; changed wrappers preserve that compatibility. A direct module-mode build
rejects their non-module `Fren.Impl` import; this unit does not convert that
separately owned dependency.

## Retained implementation records from the base

The following material was moved from the reference at base
`a49cf93dfd63ca9a38e40029d1cf191ca84b4523`. It preserves the exact earlier
obligations, links, implementation provenance and finite-evidence boundaries.
Its historical unchecked items may precede implementations already present
at that base; the transfer does not turn them into fresh test results or
universal proofs. New exact-source validation receipts are recorded in the
author report, outside the repository. In particular, old partial-operation
or lazy-demand wording is superseded by the declarative rules above.

## Retained record: src/Spec/Compiler/Desugaring.md

## Evidence still needed

`FrenThirDesugar.Program` carries the actual successful `checkWalking`
result as evidence. `desugar` returns that program unchanged. The Lean
`identity`, `static`, `admitted`, `rejected` and `deterministic` theorems
state properties of this stage. The test-only `FrenThirDesugarTests.evaluation`
theorem equates actual `FrenEval.evaluate` calls at the same operational depth.
Finite property tests exercise actual admitted, rejected and partial inputs;
the checked Fren1 example does not prove these properties.

- [x] Implement the identity on admitted walking typed data, with producer
  evidence and failure at the actual admission boundary.
- [x] Establish identity-specific admission, static and evaluator correspondence
  and test actual producer inputs, including failure and partial outcomes.
- [ ] Establish universal traversal and checker soundness beyond these identity
  laws and finite tests.
- [ ] Specify and implement each future sugared form before admitting it, and
  establish its typing and meaning preservation, including table disjointness.
- [ ] Build the MIR path and establish assumption-to-goal preservation.
- [ ] Restate recursive correspondence in Fren when it can express the actual
  recursive syntax and judgments, without copying the IR or pass into Fren.

## Retained record: src/Spec/Compiler/Mir.md

## Implementation evidence and remaining obligations

`FrenThirToMir.produce` consumes `FrenThirDesugar.Program`, whose equality
witness certifies actual walking admission. `fromSource` uses that same
parser, resolver and checked desugaring boundary. Rejected sources retain
their admission diagnostics. Internal missing-table failures are explicit;
construction never silently omits a declaration after such a failure.

`FrenMir.Theory` retains the complete `Typed` source. Its ordered declarations
separate nominal enums, function signatures and defining bodies, and global
expectation blocks. Blocks retain their written declaration, ordered typed
parameters, nearest-first context and ordered typed members, even when there
are no members. This is a small walking representation, not the final theory
schema for the full language.

`Block.requests` always emits an assumption-satisfiability request, then one
validity request per written goal. Every request carries all and only its
block's assumptions, including later assumptions, with the block's parameters
and context. Each request also carries structured `Demand` roots: complete
assumption bodies, plus the goal body for validity. Their original syntax,
occurrences, lexical contexts and call targets remain available. Definedness
is requested by static source verification before interpreting Boolean
results; no conditional operation is flattened into an unguarded assertion.
The legacy `Demand` name denotes retained source roots, not an instruction
to use the raw evaluator's demand trace as the verification policy.
Definitions remain definitions in the same theory. These data are unresolved
requests, not discharged obligations, logical formulas or solver verdicts.

The Lean `retains`, `admission`, `rejected` and `deterministic` laws constrain
the actual producer. `requests_from_blocks` connects its output requests to
the retained blocks. `assumptions_exact`, `goals_exact`, `request_context`,
`satisfiability_first`, `request_count` and `validity_member` constrain the
actual request helper. These laws establish data retention and request
selection, not logical validity or general definedness correspondence.

Direct Plausible and native cases run source through actual admission and
construction, with mandatory admitted, rejected and partial classes and
reported counts. Independent expected request identities, counts, member
roles, ordering and contexts cover S1, later assumptions, multiple owners,
no assumptions, empty blocks, contradictory assumptions, nominal spellings
and unused definitions. Negative controls omit assumptions or declarations,
change roles, reorder declarations, substitute owners, parameters, contexts
or local slots, remove demand roots and alter guards. Concrete probes of the
retained source cover the raw value strategy's lazy lets and Boolean demand,
strict operators and call arguments, and exact failure provenance. Those
operational probes are not evidence of static obligation completeness.
These tests are finite evidence;
concrete false results are not solver counterexamples.

The three primitive facts above retain their independent Fren1 checks.
They are not production `impl` bindings. The eleven `mir.walking.*` rules
remain normative: the retention and request-selection laws above address
parts of them, while the general semantic correspondence laws remain open.

- [x] Implement the actual admitted walking producer and its retained theory
  information, with explicit failure data and deterministic declaration order.
- [x] Bind actual admission, retention and request selection to Lean laws,
  with finite checks of definitions, contexts and members.
- [ ] Establish actual value, assumption and obligation correspondence,
  including satisfiability and definedness in downstream encodings.
- [x] Test the real code directly with Plausible, reporting premise counts
  for admitted, rejected and partial inputs, and independent negative controls.
- [ ] Connect downstream requests to real LIR/OIR/SMT and confirm source
  counterexamples, including S1's Amber result. A Fren1 negative control
  demonstrates sensitivity of the example, not solver evidence for this pass.

Interfaces, views, morphisms, recursive groups, subset erasure, procedure
relations, generic and closure elimination, a full MIR schema and Lean
emission remain future scope. This slice does not implement OIR or claim
that current requests have already been solved.

## Retained record: src/Spec/Compiler/Oir.md

## Actual producer evidence and remaining laws

`FrenLirToOir.retains_lir`, `admission`, `retains_source` and `scoped_input`
prove that successful production retains actual admitted, well-scoped LIR;
`deterministic` and `lowering_rejected` constrain the real entry point.
`retained_equations` proves that every function keeps its actual equations.
`walk_empty`, `walk_check`, `walk_both`, `walk_branch`, `walk_binding` and
`walk_at` state equations for all actual traversal constructors.
`FrenOir.scoped_binding`, `scoped_guard` and `search_counterexample` constrain
scope reconstruction and the negated-condition search formula. These local
laws do not prove a whole-pass source correspondence.

The producer retains complete typed domains, actual definition value/domain
equations, ordered requests, per-occurrence paths, interleaved lexical frames
and question/definition dependency edges. Free parameters are total values of
their declared domains; their LIR local-domain components mean true. A
conservative structural domain check recognizes independently total
assumptions, including parameter comparisons. Their trivial domain questions
need no hypotheses. Partial assumptions retain the other assumptions and
explicit edges to their checks. When those others are also partial, the
questions and dependent requests carry an unresolved reason. `ready` means
this dependency rule is supported, not that any question has been proved.
Guard and binding entries conservatively depend on earlier checks in their
body; these edges are prerequisites, never Boolean premises. No aggregate
verification success is produced.

The native `oir`, `oirControls` and `oirProperties` jobs exercise actual
source production. The fixed source checks unused functions, both Boolean
operands, lets and shadowing, calls and actual equations, nominal match
guards, later assumptions, empty/contradictory blocks and unresolved mutual
partiality. Direct Plausible runs 100 samples with mandatory admitted,
partial, contradictory and rejected classes and no discarded premises; a
19-source census records the same classes. Independent negative controls
remove a question, change an owner/origin or local slot, add an ordinary
operand guard, move a let check, insert the goal as a premise, flip polarity
and remove equations. Missing and wrong-origin obligations remain well-sorted
but fail the source controls. Finite formula observations use the existing
test-only LIR observer, not extraction as their oracle or a solver backend.

The checked test item below is finite evidence. All eight `oir.walking.*`
rules still require universal actual-pass laws; neither the primitive facts
nor these tests prove the unchecked statements:

- [ ] For every actual successful admitted LIR production, extraction either
  produces well-formed contextual questions for every retained verification
  occurrence and MIR request, or reports the exact unsupported boundary.
  Establish the partial-assumption dependency rule before claiming success
  for that class of inputs.
- [ ] Prove both directions of correspondence between those questions and
  declarative source obligations, under related typed environments and actual
  definition interpretations. Preserve let substitution, explicit guards,
  unused bodies, ordinary operands, owners and every diagnostic occurrence.
- [ ] Prove that after independently established applicable domains, each
  owned Sat and validity request agrees in both directions with the formulas
  above over the complete parameter domains. Never infer validity from its
  own goal or consistency from bounded search.
- [x] Test the actual producer directly, with premise counts for admitted,
  partial, contradictory and unsupported classes. Delete a check, use the
  wrong owner or slot, guard an ordinary operand, move a let check, insert a
  goal as a premise and flip counterexample polarity as negative controls.
- [ ] Bind solver translation and later source-model confirmation to the
  actual code, retaining unknown and exhaustion. Restate recursive scoped
  laws in Fren when it can express them against that code. No copied Fren
  pass model or plausible-only `impl` substitutes for these laws.

The existing MIR request laws and LIR constructor equations establish useful
retention and local structure. They are not OIR extraction proofs. This
chapter leaves universal extraction and pipeline soundness to later units;
the producer evidence above establishes the current implementation boundary.

## Retained record: src/Spec/Compiler/Lir.md

## Actual-producer evidence and remaining laws

[Producer laws](../src/FrenFlatToLir/Walking.lean) prove actual admission,
retention of the complete MIR and typed source, determinism, rejection
propagation and success of the output scope/retention checker. The latter
includes Boolean declaration/request retention certificates; it is not a
proof of their equality from unproved lawful-equality instances.
[Combinator laws](../src/FrenLir/Walking.lean) prove the actual branch, let,
ordinary-operator and call domain equations, including both Boolean operands
and unused definitions. The retained `Verification` tree is the source of
the formula summary; no independently supplied definedness bit is accepted.
[Direct Plausible
properties](../src/FrenFlatToLirTests/Properties.lean) exercise the actual
producer on mandatory admitted, rejected and partial classes, with explicit
premise counts and independent arithmetic/request expectations. Native
controls retain nominal identities, owned request roots and lexical origins,
and kill source, domain and retention mutants.

The universal laws below remain obligations, beyond those checked facts.

For every `p : FrenThirDesugar.Program` and `t : FrenMir.Theory` with
`FrenThirToMir.produce p = .ok t`, the logical-lowering producer must
succeed on this walking domain and return a well-formed program satisfying
the retention, requests, verification and sharing rules above.
For every retained value body or occurrence, in its recorded lexical
context, relate source and logical environments slot by slot at their
actual Bool, Int or canonical enum types. Under corresponding definition
interpretations and environments, declarative source obligations and LIR
verification information must correspond in both directions. Where those
obligations hold, values must correspond at the recorded result type. Raw
interpreter comparisons additionally require sufficient operational depth;
their undefinedness is not the source verification judgment. Lets require
exact scoped value/domain bindings, not just lists of unscoped values.

After the applicable definedness obligations are accounted for, assumption
satisfiability and each owned validity question must agree in both
directions over the same parameter domains. This includes empty blocks,
contradictory assumptions, assumptions after goals, nominal enums, unused
definitions and the declarative regressions above. These are laws about the
actual eventual producer and evaluators, not universal simulation theorems
proved by the six primitive facts.

- [x] Implement the walking representation and producer, with actual-code
  structural laws, direct Plausible over admitted, rejected and partial inputs,
  reported premise counts and independent native verification/context controls.
- [ ] Establish whole-term value, definedness and request preservation,
  beyond the actual static-scope audits and negative controls already tested.
- [ ] Restate these laws in Fren when recursive typed syntax, scoped
  outcome environments and recursive evaluation judgments can be expressed
  against the real code. No general quantifier or recursive-unfolding model
  is needed to deliver this nonrecursive walking slice.

The next OIR step must generate conditions from the retained scoped
verification information, separating each goal from its active assumptions
and branch guards. It must follow the existing
[definedness hypotheses](../src/Reqs/Check.md#definedness),
including other assumptions when checking an assumption, rather than let
an undefined predicate disappear as false. Solver translation, Sat/validity
polarity, limits, unknown results and source-model confirmation then need
their own actual-path evidence. This chapter does not deliver OIR condition
generation, recursive unfolding, general quantifier expansion, an SMT
backend or a completed S1 solver result.

## Retained record: src/Spec/Compiler/Smt.md

## Evidence and pending laws

`FrenOirToSmt.retains_oir`, `retains_questions` and `admission` prove that
successful production retains the actual admitted OIR and every original
question. `deterministic`, `distinct_components`, `parameter_domain`,
`classify_nonzero` and `classify_resource` state small actual-code laws.
Native `smt`, `smtControls` and `smtProperties` jobs exercise source-to-query
to-real-solver behavior and nonanswers. The fixed fixture independently checks
32 written requests, signed arithmetic, unused/guarded domains, forward calls,
shadowing, nominal enums and unresolved mutual assumptions. Owned controls
exercise invalid protocols, nonzero exits, exact invalid bytes, time/output
limits, suspended children and repeated cancellation at cleanup. The ownership
regression checks that the direct leader is still waitable at every group
signal, including normal solver exit and repeated cancellation. These tests
and raw receipts are finite evidence, not proofs of universal translation
correctness or SMT soundness, or a new crossover prerequisite.

The following universal obligations remain pending:

- Prove translation preserves each actual typed logical term in related
  complete environments, including nominal identity, Euclidean arithmetic,
  function equations and interleaved lexical frames.
- Prove query correspondence in both directions with the declarative source
  obligations after independently justified applicable domains. OIR's general
  extraction/source correspondence remains pending too.
- Prove injectivity and freshness of every rendered symbol family and
  substitution/capture preservation over all admitted source programs.
- Establish the unresolved mutually partial assumption rule before claiming
  supported source results for that class.
- Bind later model decoding and static source confirmation to actual code;
  raw SAT/UNSAT, bounded tests and solver trust do not close this obligation.

## Retained record: src/Spec/Compiler/Hir.md

## 6. Remaining implementation evidence

- [ ] Implement only the walking resolved interface and actual collection and
  traversal in `FrenAstToHir`, then state the pass laws over those concrete
  APIs in Lean or bind expressible uninterpreted Fren laws with genuine
  `impl` proofs. Reuse `ItemId` and the binding core.
- [ ] Run direct Plausible on actual code, including unknown, duplicate,
  ill-typed-but-resolvable and partial inputs. Report premise counts for
  successful parsing, walking shape, duplicate-free collection, lookup
  success/failure and in-scope indices; rejection must not make a law vacuous.
- [ ] Add textual resolver cases for every row above, both qualified path
  spellings, missing members, blocked qualifiers, parameter and member-label
  duplicates, annotation forward references, span retention and deterministic
  source-order failure reporting. Test deliberate wrong-slot, let-value and
  sibling-leak controls. Prove simple collection/lookup lemmas where cheap.
- [ ] Keep recursion validation, dependency SCCs, imports and module DAGs,
  cross-module visibility and body access, generics, payload patterns, full
  HIR serialization and the remaining compiler passes for later slices.
  Self and mutual references may resolve to collected item identities;
  success is not permission to evaluate recursion or a recursion proof.

The checked primitives establish independent scope and identity facts. The
wrapper's parser controls establish input availability and a source anchor.
Whole-pass semantic correctness, alpha-invariance and source preservation
remain obligations until tested or proved over the actual resolver. No
recursive Fren feature or general generator framework is needed to start it.

## Retained record: src/Spec/Compiler/AstAndParsing.md

The chapter wrapper checks these primitives and the successful walking
example. The parser, AST and shared typed-context adapter are not implemented
by this chapter. The rules labelled **Proof obligations** remain requirements,
not discharged theorems about an empty library or assumed parser.

- [ ] State the complete-input, ownership, boundary, determinism and roundtrip
  laws in Lean over the actual `FrenParse`/`FrenAst` APIs, or bind uninterpreted
  Fren laws to them with genuine `impl` proofs where expressible.
- [ ] Bind the actual byte classifiers to the primitive meanings above; reuse
  the existing Span bounds/translation laws rather than duplicating them.
- [ ] Exercise the actual parser directly with Plausible and textual tests:
  successful, ill-typed-but-parsable, malformed and truncated text; Unicode
  comments, empty input, trailing junk, EOF and alternate trivia. Report
  accepted/rejected grammar premises and test deliberately perturbed bounds,
  byte classification and grouping. Sampled properties are not proofs.
- [ ] Check driver and typed-context adapter agreement on the same extracted
  text, preserving source-map and callback-input bytes.

Full-language syntax, payload patterns, generics, closures, procedures,
interfaces, views, broader lexical forms and editor recovery require later
chapter extensions before their implementation. This walking slice supplies
no recursive Fren parser model, no semantic pass implementation and no
prerequisite to extend Fren's recursive specification features.

## Retained record: src/Spec/Language/NamesAndScope.md

The full lookup and traversal properties need evidence over the actual
resolver, not a roundtrip or agreement between two copies of lookup.

- [ ] Bind the future nearest-name primitive to the finite facts and the
  wrapper's arbitrary-context law, with a genuine Lean proof where cheap.
- [ ] Test actual collection under declaration permutations, including
  forward type, function and expectation references and all duplicate kinds.
- [ ] Test actual lexical traversal on parameters, nested lets, each arm and
  siblings, including unknown names in let values and uses outside a let.
- [ ] Use direct Plausible on actual lookup and resolution, with accepted and
  rejected inputs and counts for successful parse, walking-domain membership,
  duplicate-free collection and lookup-hit/miss premises. No sampled test is
  classified as a universal proof or discharged with `impl ... by plausible`.
- [ ] Extend this chapter before imports, multiple modules, visibility across
  modules, payload binders, generics, recursion policy or body visibility are
  implemented. These are remaining obligations, not prerequisites for the
  single-file resolver.

## Retained record: src/Spec/Compiler/Thir.md

The actual Lean laws `validateWalking_iff`, `walking_success`,
`walking_failure_iff`, `walking_retains` and `walking_deterministic` establish
the executable success/failure boundary, admission, preservation and
uniqueness. They do not prove a universal correspondence between traversal
and the declarative coverage or graph obligations. Direct Plausible and
native tests exercise actual generated programs with successful, partial,
repeated, ill-typed, cyclic and edited-provider variants, requiring explicit
nonzero premise counts and no discards. Finite tests are evidence rather
than recursive universal soundness proofs.

## Retained record: src/Spec/Compiler/Thir.md

The S1 `wrong` expectation remains a well-typed goal for later lowering and
solver checking. The S1 unknown `y` remains a resolver failure. Accepting
syntax and names for the enum arithmetic example must not turn it into a
successful typed result or an empty set of goals.

- [x] Implement actual walking typing and admission in `FrenHirToThir`, with
  genuine admission, erasure, lookup, primitive and determinism proofs.
  The wrapper's `Admitted` is the actual pass's relation.
- [x] Test every expression/operator, annotation/suffix, local/let/sibling
  context, forward call, arity, callability, enum identity, constructor owner,
  branch and member, with independent S1 type/target/span expectations and
  the exact `F0304` code/text/span above.
- [x] Reject edited resolved inputs with deleted/duplicate entries and changed
  role, target, context, scope, constructor owner, source, tape or AST.
- [x] Run direct Plausible on the actual recursive checker with required
  success, typing failure and partial-table admission failure per sample.
  Native census counts admission, signatures, lookup hit/miss and typing
  success/failure without discarded premises.
- [ ] Prove the declarative `HasValue` relation for every successful actual
  traversal (`TypingSound`). The finite native and Plausible cases do not
  establish universal soundness or complete traversal correctness.
- [x] Implement and test `WalkingCoverage` and `WalkingNonrecursive` over
  actual typed syntax, and provide the admitted whole walking static entry.
  S1 retains all four Bool members, including the false `never_red` goal.
- [ ] Prove universal declarative coverage/call-graph correspondence for the
  actual validators; finite tests and executable boundary laws do not prove it.
- [ ] Restate recursive coverage traversal and call-graph laws in Fren once
  recursive syntax and graph reachability can be expressed there.
- [ ] Restate the recursive typing/preservation relation in Fren once Fren2
  supports recursive expression datatypes and recursive judgments over
  their children and binder contexts. State it in Lean over the real pass
  meanwhile; it does not require a copied executable Fren IR.

These existing Spec wrappers remain compatibility documentation checked by
Fren1. They introduce no Fren2 runtime/test module and are outside the
runtime module/header and physical-size guard's inventory.

## Retained record: src/Spec/Compiler/Evaluator.md

- [x] Check the small arithmetic and demand contracts independently with Fren.
- [x] Implement the walking evaluator on actual admitted typed syntax in
  `FrenEval`, with actual-code arithmetic and outcome boundary laws in Lean.
- [x] Exercise actual code with direct Plausible and concrete controls on
  accepted, rejected, undefined and invalid inputs, with premise counts.
- [ ] Prove universal traversal soundness, result completeness and definedness
  correspondence; the output type check and finite controls do not prove these.
- [ ] Establish the future desugared THIR correspondence when that producer
  and evaluator exist.

## Implemented walking boundary

`FrenEval.Program` stores the actual `Typed` value and proof that
`checkWalking input = .ok typed`. `fromResolved` runs that producer;
`fromSource` runs the real parser and resolver before it. `fromTyped` requires
proof of actual typing before running walking validation. An edited record
or a supplied Boolean cannot create this evidence. `Program.retains`,
`Program.static` and `fromResolved_success` bind this boundary to the actual
producer and its retained document, coverage and non-recursion results.

`evaluate` selects a retained body by canonical owner and optional member
label. Its positional concrete arguments must match the body's parameters;
they are reversed into the existing nearest-first context. Enum inputs must
name an actual declared constructor of their recorded canonical owner.
The interpreter walks the existing syntax and resolved references, using
typed callable occurrences to enter a named body with only its arguments.
There is no second syntax tree, executable Fren pass model or solver call.
The result retains the original body and complete check member, including
whether it is an assumption or expectation, its label and its source spans.
Clients must keep assumptions when interpreting check assignments.

An outcome is a concrete `Value`, semantic `Failure.undefined` (zero divisor),
`Failure.exhausted`, or an invalid/unsupported diagnostic. Missing requests
are invalid; bad arguments are invalid outcomes associated with the retained
body. These failures carry source spans and details; undefinedness also
retains its operator. They are never converted to false or a solver verdict.

The total implementation uses the static walker's depth approach: each
visited expression, including entry into a callee body, consumes one unit.
Siblings receive the same remaining depth; the bound does not count total
steps. Let definitions are computed once in the incoming environment at the
let's remaining depth and stored as complete outcomes, without a thunk or
closure machine. Reading a slot consumes the name's unit and returns that
stored outcome; it does not reevaluate the definition at the use site's depth.
An unused slot's undefined, exhausted, invalid or unsupported outcome does
not escape. A read returns that exact outcome and its original diagnostic.
Thus an unused definition may still cost work. A definition exhausted at
binding depth remains exhausted at every read; slot reads do not retry it.
Skipped `and`/`or` right expressions consume no depth or evaluation work.
`defaultDepth` multiplies the largest body token count plus one by the function
count plus one. Callers may supply another depth, including
zero. Exhaustion is explicitly separate from semantic undefinedness. No
theorem currently proves that this default suffices for every admitted
program, or bounds total execution time, memory or integer magnitude.

`binary_add`, `binary_sub`, `binary_mul`, `binary_div`, `binary_mod`,
`div_zero`, `mod_zero` and `euclidean` prove the actual primitive arithmetic
decisions. The independent Fren contract above remains checked separately;
changing its addition to subtraction must fail. Native controls also mutate
operators in actual admitted source and require the changed concrete results.
`evaluate_selected` proves retained body selection, `evaluate_type` proves
that a returned value matches the retained body's type and constructor
inventory, and `evaluate_deterministic` proves uniqueness at fixed depth.
The type theorem follows from an explicit output check, not a universal
preservation proof of the recursive interpreter.

`walk_and_false` and `walk_or_true` prove the current strategy's deciding-left facts
about the actual recursive walker for every right expression. `walk_let`
proves its outcome-binding equation at explicit depth, and `walk_local`
proves exact retrieval of any stored outcome. `walk_strict_failure` preserves
complete demanded right failures; `shortCircuit_strict` excludes every other
operator from skipping. The wrapper also checks admitted source against
independent lazy-let and Boolean outcomes. These laws and regressions close
the earlier concrete strategy regression. They do not establish declarative
source-obligation completeness, universal value correspondence or completeness
at `defaultDepth`.

Direct Plausible generates source programs and concrete values, then runs
the real producer and evaluator. Every source sample requires defined,
undefined, invalid, exhausted and rejected cases; no failed premise is
discarded. The separate fixed census reports each class explicitly. These
tests include S1's three concrete results above, unused/used/guarded lets,
lexical shadowing, skipped/demanded `and`/`or` operands, strict `iff`, equality,
inequality and calls, both check-member roles, depth controls, nominal input
rejection and operator mutation sensitivity. The 24-source evaluator census
requires 216 defined and 120 undefined outcomes, 96 invalid arguments, 24
exhaustions, 120 rejected sources, 24 rejected edited producers and 24 operator
mutants, with no discarded premises. These remain finite evidence.

- [ ] Restate recursive evaluation and its correspondence laws in Fren once
  Fren2 can express recursive syntax and judgments, without copying the IR.

## Retained record: src/Spec/Compiler/Bindings.md

The reference implementation used here is the successful raw-index
[expression prototype](../scratch/expr/Prototype.lean). Its `Expr p`
is a small Lean test representation, not the production IR datatype.
The equations below constrain the future shared library without fixing
production constructors. `V i`, `All b`, `Let v b`, and `Array xs` abbreviate
prototype variable, quantifier, let and array nodes. They are mathematical
notation, not additional Fren syntax.

## Retained record: src/Spec/Compiler/Bindings.md

> **Rationale:** The prototype keeps arrays and raw indices after two
> particular intrinsic scope-indexed array encodings were rejected by
> Lean's kernel. Those failures do not establish that all intrinsic
> encodings are impossible. The accepted implementation uses extrinsic
> `Scoped` and an equivalent executable `scopeCheck`.

## Retained record: src/Spec/Compiler/Bindings.md

The equations use one fixed prototype phase `p` and its actual operations.
`V`, `upRen`, `upSub`, `rename`, `shift`, `subst`, `substTop`, `Scoped` and
`scopeCheck` refer to `ExprPrototype`. Symbols for free indices, closing,
alpha-equivalence and `substAt` denote the definitions above, with no claim
of existing production declarations.

## Retained record: src/Spec/Compiler/Bindings.md

The existing universal proofs are `rename_scoped`, `subst_scoped`,
`scoped_mono`, `substTop_closed_scoped`, and `scopeCheck_iff` in the prototype.
In particular, `Scoped 0 s → Scoped (n + 1) b → Scoped n (substTop s b)`
is already proved for every depth and every array member. Open replacements
are covered by the stronger `subst_scoped`; the additional chapter test
proves that specialization directly. These proofs use real induction on
scope evidence, not a solver abstraction or a test classified as a proof.

[Chapter checks](../scratch/expr/BindingsLaws.lean) add direct Plausible
checks of actual prototype composition and shift/substitution operations on
bounded raw terms, and concrete capture/cutoff controls. They include open
and dangling terms and nonzero cutoffs. They do not implement a production
binder library. The prototype has no type checker or hole constructor;
raw malformed terms exercise scope failure, not all future partial IR forms.
The original [prototype tests](../scratch/expr/Tests.lean) also cover
both phases, let-value/body distinctions, arrays and deliberately bad lifts.

The production index foundation is now
[`FrenBase.Binding`](../src/FrenBase/Binding.lean), exported by `FrenBase`.
It is independent of any expression datatype. `Context` stores caller-owned
entries newest first; `lookup` returns `none` outside the context, and
`HasType` compares the actual type entry at an index. `InScope` states the
raw index bound separately. This does not make an arbitrary renaming
type-preserving, or identify slots of unrelated contexts of equal length.

`shiftIndex` implements upward cutoff insertion. `liftRen` and `liftRenN`
protect one or several fresh binders. `liftSub` extends a generic environment
using caller-supplied variable construction and weakening. Its scope theorem
requires those actions to preserve the caller's scope predicate; the caller
must also establish that weakening has the intended capture-avoiding meaning.
No downward shift or expression traversal is supplied.

The [production checks](../src/FrenBaseTests/Binding.lean), imported by the
normal Fren2 test driver, connect these functions to the primitive scope,
shift and lift contracts with Lean laws and rule references. This is direct
Lean evidence, not an `impl` binding or a proof from Plausible. Universal
proofs cover fresh/older lookup, membership bounds and completeness, shift
boundaries, injectivity and same-cutoff composition, bounded lifted maps,
the nested cutoff equation, and conditional scope preservation for lifted
substitution environments. Direct Plausible tests additionally compare
shifted lookup with concrete context insertion, check raw indices and nested
lifts, count accepted/rejected scope premises, and falsify deliberately bad
cutoffs, renaming lifts and substitution weakening. Lists of references test
the generic environment carrier; they are not a production expression IR.

The evidence boundary is explicit:

| Obligation | Evidence now | Remaining work |
| --- | --- | --- |
| Index and environment primitives | Universal Lean production proofs and direct Plausible checks | Instantiate weakening with each actual IR |
| Whole-term scope preservation and checker equivalence | Universal Lean prototype proofs | Bind to shared structural operations when implemented |
| Whole-term identity, composition, shift/substitution | Bounded executable tests on prototype operations | Shared structural operations and universal composition/commutation proofs |
| Free indices, alpha-equivalence, opening/closing inverses | Definitions and laws in this chapter | Actual APIs, formalization and tests |
| Generic fold induction/fusion | Prototype has a total fold | Prove the reusable theorem once and instantiate it |
| Production pass simulations | Overview's requirements | Relate values, assumptions and obligations for each pass |

- [ ] Formalize the composition and commutation equations in Lean over the
  shared implementation, using real induction where the fold theorem
  does not suffice.
- [ ] Prove free-index, alpha and open/close laws over their actual APIs.
- [ ] Instantiate the planned generic fold theorem for simple traversal
  laws; it is not an existing proof delivered by the prototype.
- [ ] Bind the future shared code with `impl` where applicable, without
  using `impl … by plausible` as proof evidence.
- [ ] Test actual future IR forms with direct Plausible, including invalid,
  ill-typed and partial inputs; report accepted/rejected premise counts.
- [ ] Restate recursive laws in Fren after crossover when it supports
  recursive functions over array children and the required environments.
  No Fren 1 recursive feature is a prerequisite for this chapter.

## Retained record: src/Spec/Language/Types.md

Today's solver checks consequences of these independent contracts. The Lean
wrapper binds all three procedures to the actual generic `FrenExpr`
primitives with proofs. The equality-atom instance uses `Int`; the walker
uses the same definitions with canonical `ItemId`. The generic
`compatible_iff`, `unary_accepts`, `binary_accepts` and `binary_result` laws
cover actual nominal equality and operator decisions without rendering or
hash encoding. The wrapper also proves uniqueness and scope of actual local
context entries. These are primitive proofs, not whole-traversal soundness.


- [x] Bind real generic compatibility and operator decisions with genuine
  proofs, covering every AST operator and builtin/nominal distinctions.
- [x] Exercise actual whole traversal, including rejected terms, context
  alignment, every operator/type-family pair and retained source data.
- [ ] Prove the universal recursive `FrenHirToThir.TypingSound` obligation;
  native cases and direct Plausible are finite evidence, not that proof.
- [ ] Restate recursive expression typing in Fren once Fren2 supports
  recursive expression datatypes and structurally recursive judgments over
  their ordered children; no Fren1 recursion extension is a prerequisite.

## Retained record: src/Spec/Compiler/Mir.md

The original S1 adds this deliberately false block, shown as text so that
the book's checked examples remain successful:

```text
expect wrong(l: Light) {
    expect never_red: next(l) != Light::Red
}
```

For S1's three blocks alone, the intended future Fren2 solver output is
exactly **5 passed, 1 failed**: `back` and `at_most` pass, each of the three
blocks' assumption-satisfiability checks passes, and `never_red` fails with
`l = Light::Amber`. This is an acceptance target for the future complete
pipeline, not solver evidence currently computed by Fren2. In particular,
a concrete interpreter returning false at Amber is not delivery of a solver
counterexample. Removing `bounded` is a separate negative control:
`l = Light::Red, base = 101` makes `at_most` false. The chapter's positive
Fren fences do not contain either deliberate failure.

Implementation correspondence and proof coverage are recorded in the
[development coverage document](fren2-specification-coverage.md).

## Retained base-library evidence note

> **Note:** The checked cases above establish only arithmetic facts about the
> examples. The base, source and diagnostic libraries and their bindings to
> contracts are future work. The remaining rules are listed as pending
> formalization; no production implementation or property test is claimed.
