# Fren2 specification implementation and proof coverage

The normative reference is `src/Spec/`. It defines a precise source domain:
Booleans, mathematical integers, payload-free nominal enums, named functions,
lets, conditionals, constructor matches and global assumption/expectation
members. Implementation status, checklists and historical evidence belong here.
Neither the reference's scope nor a successful example asserts that the whole
Fren language or compiler has been verified.

## Language core correspondence

The [Core typing chapter](../src/Spec/Language/Types.md) defines semantic
objects first, then `ExprF<E>` and `ArmF<E>`, judgment forms, one rule per
expression constructor, layer properties, primitive contracts, an optional
postorder witness and examples. It contains no Lean code. The
[style guide](../src/Spec/dev/Style.md) specifies the chapter template and
standalone `<!-- status: STATUS -->` metadata after each rule paragraph.
This is the pilot; the rest of the reference has not yet adopted the syntax.
No mechanical status checker is delivered by this unit.

`layer_rule?` is the single one-layer relation. It takes `ExprF<Judgment>`,
whose child positions hold each child's exact context and type. The
postorder table replaces each child's row position by that row's judgment,
looking only among earlier rows, and calls the same relation; it does not
repeat the typing decisions. A finite derivation tree justifies every child
judgment, including unused let values and all branches. The
postorder-to-tree argument is mathematical; a checked source-occurrence
adapter theorem is still needed.

Contexts, call arguments, match arms, parameter lists, the symbol
environment and derivation tables are snoc sequences (`Snoc<T>`), read by
structural recursion. The symbol environment is a map by construction: its
lookup returns the newest binding, so no validity predicate is stated. The
chapter has no `fren.lint.undecidable` opt-out. Its recursive definitions
are opaque to the solver past one unfolding; the properties that need
induction over them are proved in the wrapper or by Fren's induction over
an expectation's parameters. Unbounded SMT witness search is not claimed
decidable. The reference's dynamic semantics has a verified, well-typed
domain; partial-operation and strategy notes in historical records below
describe implementations and do not extend that semantic domain.

Locals use de Bruijn levels, counted from the oldest entry of a snoc
context, so context extension leaves every existing level unchanged.
Production code, including `FrenBase.Binding`, `FrenHirToThir` and the
compiler chapters, numbers the same entries nearest first. The conversion,
nearest-first index `|Γ| - 1 - i` for level i, is part of the
erasure/refinement relation between the Core and the compiler, which is
specified later. `Spec.Language.Types.lookup_nearest` proves that lookup
agrees under this conversion; the rest of the relation, including the
traversal correspondence of `types.derivation.correspondence`, is open.
A local's level is an `Int`: Fren1 rejects a `Nat` within a recursive
enumeration's payload, where derivation rows hold forms. A negative level
names no entry, so no rule has a `0 ≤ i` premise.

The source representation uses canonical sequences of named components.
Production `FrenBase.ItemId` also admits generated components, which are not
source declarations in this domain. Display strings and hashes are not
identities. The three genuine primitive `impl` bindings remain in
`Types.lean`, using integer equality atoms to instantiate the generic
production compatibility/unary/binary operations. They are adapters, not
the normative type representation. The operator enums `UnaryOp` and
`BinaryOp` are defined locally with the Syntax chapter's names and
constructors; they move to `spec::syntax` when that chapter lands.

| Rule or obligation | Evidence and limit |
| --- | --- |
| `types.walking.identity`, `types.walking.compatibility` | Fren expectation for disjointness and exact nominal equality |
| `types.context.bound`, `types.context.weakening` | Fren expectations over arbitrary contexts; `lookup_bound` uses Fren's induction |
| `types.context.indices` | `Spec.Language.Types.lookup_nearest` proves level lookup equals production nearest-first lookup at index `\|Γ\| - 1 - i` |
| `types.symbols.lookup` | Fren expectation: a new binding determines its item and leaves others unchanged |
| `types.layer.operators`, `types.operator.unary-unique`, `types.operator.binary-unique` | Fren expectations for result uniqueness at fixed operand types |
| `types.layer.determinism`, `types.layer.unique-*` (ten forms) | One Fren expectation per form, for arbitrary symbol environments, contexts and child judgments |
| `types.layer.context`, `types.layer.context-*` (six forms) | One Fren expectation per form for exact child contexts, including let extension and binder-free match arms |
| `types.layer.children-each` | Fren expectation, by induction over the child sequence |
| `types.layer.arms-each`, `types.layer.call-arity` | `Spec.Language.Types.arms_each` and `argument_types_length`, by induction in Lean |
| `types.value.examples` | Fren expectation for the stated arithmetic examples only; the general operator meanings are not checked here |
| `types.operator.unary`, `types.operator.binary` | `Spec.Language.Types.core_unary` and `core_binary` prove agreement with the actual generic primitives for every operator and arbitrary canonical identities |
| `types.primitive.compatibility`, `types.primitive.unary`, `types.primitive.binary` | Existing universal `impl` proofs of the primitive contracts |
| Context lookup | `local_type_unique` and `local_type_scoped` prove actual production binding laws |
| Concrete derivations | Wrapper checks every public example constant by `decide`; finite evidence only |
| `types.derivation.unique` | Open: lift the layer step to uniqueness of whole derivations by induction, comparing recursively derived child types |
| `types.derivation.weakening` | Open: define the level shift of bound locals and prove typing under context extension by induction |
| `types.derivation.correspondence` | Open: prove both directions between this Core relation and the production checker in its admitted domain, through the level-to-index conversion |

The theorem names used in rule metadata belong to `Spec.Language.Types`.
The `definition` rules introduce objects and relations; their status is not
an implementation proof. Whole-term laws marked `open` remain normative
obligations. Existing production `FrenHirToThir.HasValue` and
`FrenHirToThir.TypingSound` concern the retained AST. Native tests, Plausible,
closed examples and layer step cases do not establish `TypingSound`, its
converse, or a complete source-to-Core occurrence correspondence.

- [ ] Prove whole-derivation uniqueness and weakening with the level shift of bound locals.
- [ ] Specify the erasure/refinement relation between the Core and the
  compiler representations, including the level-to-index conversion.
- [ ] Prove the complete occurrence/context-preserving source-to-Core
  correspondence and actual checker's `TypingSound` theorem and converse.
- [ ] Prove universal match-coverage and call-graph correspondence separately
  from typing, preserving all branch bodies and unused definitions.
- [ ] Formalize interpretation/free-local/mentioned-item recursive closure
  against actual binding and expression code, including capture avoidance.
- [ ] Establish universal value and declarative source-obligation preservation
  for each actual lowering stage under independently justified domains.
- [ ] Resolve mutually partial assumption dependencies before claiming a
  supported verification result for that class.

The type wrapper checks the public concrete example constants by expanding
their finite index domains and simplifying the generated Fren definitions.
The finite-bound lemmas apply to arbitrary integer upper bounds, including
empty/negative ranges. These are exact closed cases, not sampled traversal
soundness. The expression wrapper also checks the examples it imports.
Historical requests below to wait for recursive Fren datatypes before
restating typing are superseded by the one-layer definition; its inductive
closure and implementation correspondence still need universal proofs.

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
below adds theory-construction and semantic contracts. The LIR unit below
adds actual term, scope and interpretation contracts.
The OIR unit below adds contextual extraction, request and interpretation
contracts. The SMT unit below adds concrete encoding, interpretation and
raw response contracts; universal preservation and source confirmation remain
open.

Continue the same correction objective with these separate chapter units:

1. **Desugaring extensions** (`SCdesugar`, queued edit 1012): the core identity
   relation and actual API correspondence are specified below. Each additional
   sugar still needs Language semantics, its own transformation rule, typing
   and scoped-obligation/value preservation. No additional sugar is admitted.
2. **MIR extensions** (`SCmir`, 1018): the core formal chapter and conditional
   correspondence laws are specified below. Prove its universal producer
   inventories and recursive semantic premises; extend to procedures/views
   only with their Language semantics.
3. **LIR extensions** (`SClir`, 1024): the core formal relations and actual
   constructor laws are specified below. Prove their universal producer,
   interpretation and request contracts. Closed sharing, quantifiers and
   additional source forms require their own specified extensions.
4. **OIR extensions** (`SCoir`, 1026): the formal core contracts below specify
   actual extraction and owned contextual questions. Prove the remaining
   whole-pass construction, sorting, model and semantic correspondence laws.
   Keep mutually partial assumption dependencies unresolved until justified.
5. **SMT extensions** (`SCsmt`, 1027): the core encoding and response
   contracts below are specified. Prove universal symbol freshness, encoding
   and environment preservation, solver adequacy and trust; implement and
   justify model decoding and static source confirmation. Raw responses
   alone do not establish source verification.

These are retained substantive obligations, not completed chapters or a
separate plan replacing the implemented shared-core and THIR correction.

## SMT contracts and proof boundary

`Spec/Compiler/Smt.md` displays the exact compiled reference block of its
wrapper. It uses the accepted source witness, OIR program/questions/definitions,
LIR terms, shared sorts, `Lir.Sorted`, `Meaning`, `Primitive`, `Slots`, `Symbols`,
`ZeroValues`, and OIR assignment/equation judgments. It defines no duplicate
executable compiler or toy logical IR. The five retained primitive expectations
remain separate checked arithmetic/polarity facts, never pass proofs.

`Encoded` is proved for actual `produce`: every original question is retained
in order and its script is exactly actual prelude generation followed by
actual query printing, including errors. `SortFor`, `ContextFor`, `ParametersFor`, `Names`,
`Renders`, `TermFor`, `DefinitionFor`, `DefinitionsFor`, `EnumerationFor`,
`PreludeFor` and `QueryFor` state independent unbounded grammar, typing,
canonical-reference, declaration-order and complete-script requirements.
`DefinitionsFor` uses structural `Oir.Uses` on actual value/domain bodies;
it does not consume a supplied dependency decision. `VariableName`, `Naming`,
`EnvironmentFor`, `Interprets` and `Model` state legal symbol environments,
simultaneous-let scope, positional calls and actual retained definition
interpretation. The text interpretation is restricted to well-sorted declared
terms; its name rule cannot override literal meanings. Euclidean operators
reuse the shared primitive semantics and arbitrary zero totalizations.

`EncodingContract`, `InterpretationContract` and `ValidationContract` are named
universal obligations, not proved claims. `ValidationContract` refers to the
actual bounded `Term.infer` checker and the shared unbounded sort judgment.
Low-level printing deliberately does not typecheck arbitrary hand-built OIR:
a wrong-sort arithmetic term still prints, but is rejected by `Term.infer`
and public source admission. Missing enum/constructor/canonical signature and
open-local references fail in the printer; missing/cyclic equations are
unsupported. The chapter states this boundary instead of inventing a new
validator or implying low-level success establishes wellformedness.

The wrapper proves actual OIR/question retention, exact encoding, error
exclusion, local slot translation, all 14 binary operator spellings, distinct
rendered function components, wrong local/operator-sort rejection and zero
translation-budget failure. The two closed multiple-answer/unknown equalities
use `native_decide`; their printed native reduction axioms are retained
separately from the kernel proofs of the general laws. It proves raw nonzero exit, multiple-answer and
unknown laws, and both OIR evidence polarities. `false_goal_render`,
`false_goal_sorted` and `false_goal_model` give independent concrete-text,
sort and interpretation witnesses for an admitted false expectation's actual
search. `empty_model` constructs a compatible model when no definitions are
present; `false_goal_satisfiable` supplies a typed empty assignment and search
witness for that admitted shape, without assuming a universal encoding or
source preservation contract. `false_goal_query` proves its complete independent `QueryFor` script relation;
`parameter_domain_total` excludes overriding the literal parameter domain
through a name map. `flipped_goal_model` independently interprets
the polarity mutant at false. A separate admitted constant definition and
later assumption check exact declaration, parameter and assumption layout.
These are finite/constrained witnesses, not universal metatheory.

`SearchSatisfiable` quantifies over compatible interpretations and typed
assignments. `AnswerSound` states what trusted Sat/Unsat would need to establish;
actual `classify` is only protocol recognition. The typed readback unit adds
`solveModels`, strict finite parameter decoding and actual source interpreter
observations that strict evaluation of the retained static obligations must
reproduce. The checker adds conservative
whole-program reports; it adds no cache, selectors or incremental solver API. The previous OIR checklist's separate SMT
chapter correction is supplied here; its remaining source-confirmation and
upstream universal proof obligations are preserved in full.

- [ ] Prove `EncodingContract`, including canonical name lookup/uniqueness,
  sort/arity/declaration references, complete stable definition order and
  exact query polarity/context for every admitted producer result.
- [ ] Prove `ValidationContract` and depth adequacy where appropriate; do not
  infer them from finite wrong-sort/name/arity controls.
- [ ] Prove all rendered symbol families are injective and mutually disjoint,
  and `Naming` preserves active-scope freshness and capture freedom.
- [ ] Prove `InterpretationContract` in both directions, including function
  equations and lets, under independently justified sufficient domains.
- [ ] Establish model existence and total typed model readback, relate the
  concrete-text interpretation to SMT-LIB and the actual solver, and justify
  the trust bridge expressed by `AnswerSound` rather than deriving it from
  a status token. Prove source/encoding preservation through the accepted
  MIR/LIR/OIR contracts, whose outstanding inventories are unchanged.
- [x] Implement strict Bool/Int/enum parameter readback using the canonical
  generated names, bounded cvc5 transport and both physical receipts. Retain
  the source witness and unfiltered ordered question/results envelope.
- [x] Check concrete premise witnesses and false-goal counterexamples through
  `FrenEval.evaluate` and an agreeing `strictBody`, with explicit rejected and
  unconfirmed statuses. Preserve static questions and unresolved readiness;
  a consumed body whose strict evaluation is undefined at the model remains
  unconfirmed.
- [ ] Prove `ReadbackContract`, `ConfirmationContract`, adequacy of
  `strictBody` to `Lir.SourceValue`/`Mir.ValueOf` (so that `SourceBoolean`
  can be stated through that judgment rather than the implementation) and
  evaluator adequacy.
  Justify mutually partial assumptions.
- [x] Deliver a conservative actual-source checker report with complete ordered
  inventory, receipt provenance, dependency discharge and confirmed nonvacuity.
- [ ] Prove `CheckerContract` and the universal source-soundness bridges; actual
  positive reports are conditional on the stated solver/encoding trust boundary.
- [ ] Restate the recursive grammar/interpretation contracts in Fren when it
  can quantify over the real recursive production objects. Current primitive
  Fren arithmetic and polarity contracts do not replace those relations.

Checks are bounded to the affected hosted wrapper/chapter, wrong-law controls,
actual hosted/rule/library/source-discovery audits, formatting and exact-source
artifact provenance. Existing 81-answer backend/protocol tests and native
SMT properties remain the base implementation record below; this correction
launches no new solver campaign or full suite. The cached primary FLS
scope/method/types/expression excerpts and Standard ML Revised sections
4.1–4.2, 4.10 and 6.1–6.3/6.7 supply semantic-object/environment and judgment
organization; no Rust/ML semantic rule is imported into Fren.

## OIR contracts and proof boundary

`Spec/Compiler/Oir.md` now defines actual OIR domains, parameters, definition
pairs, contextual questions, dependencies, readiness and answer polarity over
the accepted LIR objects. Its displayed reference block is exactly the
wrapper's compiled definitions. `DomainFor`/`ParametersFor` preserve nominal
inventories and ordered typed parameters. `Extracts` is an unbounded ordered
judgment on real verification trees and real extraction leaves, not a second
executable pass. `SiteFor`/`FramesFor` connect each leaf to accepted LIR sites,
including the original lexical contexts through interleaved guards/binders.
`BodyQuestionFor`, `BodyGroup`, `AssumptionGroups`, `RequestGroup`,
`RequestGroups` and `DeclarationGroups` constrain complete question layout,
owner/member/source identity, conditions, hypotheses, scopes and prerequisite
IDs. `Constructs` requires both exact declaration inventories and complete
ordered question groups, independently of producer equality.

`Uses` defines structural application occurrences, including unused let
value/domain terms. `DefinitionEdges` requires exact support of definition
dependencies while allowing repeated edges from the assumption update.
`LocalEdges` preserves ordered earlier-context prerequisites. `Others`,
`AssumptionState` and `RequestState` compute the actual dependency policy from
retained bodies/questions; they do not take supplied decisions or proofs.
Structurally total assumptions need no hypotheses; a partial assumption keeps
its other owning assumptions. Mutually partial groups and dependent requests
remain explicitly unresolved. OIR extraction itself returns no aggregate verdict;
the downstream source checker preserves those unresolved states.

`Active`, `SearchHolds`, `Violation`, `ConditionValid`, `QuestionTrue`,
`EquationsHold` and `RequestMeaning` use the same `Lir.Meaning`, slot pairs,
symbols, zero-divisor totalizations and typed assignments as LIR.
`PassContract`, `SearchContract` and `RequestContract` state separate
construction, formula/frame and two-way request obligations. The request
contract also requires the relevant domain questions under the independently
stated sufficient LIR safety domain. It does not assume source functionality
on fabricated expressions or OIR soundness as a premise. `request_to_source`
proves conditional composition with the named LIR request contract; neither
upstream contract is silently discharged.

The wrapper proves actual producer retention/admission, uniqueness, source
success factorization, failure exclusion, definition-equation retention and
search polarity. `walk_extracts` proves, by induction on the actual bounded
traversal, that every successful walk has its unbounded ordered extraction
derivation. It covers every constructor and threads exact origin, path,
frames, availability and prerequisites. It proves neither converse depth
adequacy nor the complete whole-pass contract. Actual ordinary/binding
extraction equations retain both checks and preserve the let-value location
and prerequisite. `active_nil`, `false_guard_inactive` and `literal_search`
prove contextual/interpretation facts, not solver claims.

`empty_witness_constructs` constructively proves the entire OIR `Constructs`
relation for a complete empty-block production shape; `empty_witness_sat`
exhibits its typed empty assignment and search meaning. The real source
producer admits such a block, and the wrapper requires its entire output to
match that proved shape. A separate admitted function `1 div 2` generates a
nonempty divisor question. Matching its actual condition supplies equality
evidence to `constant_divisor_valid`, which proves `ConditionValid` for that
question over every assignment, lexical continuation and zero-divisor
totalization, without an assumed universal pass theorem. Another admitted
source has two nonempty function bodies, three divisor sites, unused-let
and explicit-guard contexts, and a
goal with its later assumption and safety dependency. These finite checks
show the intended domain is usable; they do not establish general source
semantic preservation. `wrong_condition_rejected` and `wrong_frame_rejected`
prove that independently changed condition/context records fail `SearchFor`.
Three well-sorted output edits are additionally checked against the retained
LIR request as an independent oracle: deleted hypotheses, changed condition
and an inserted false guard. External failed-proof and Fren controls retain
their physical failures. Existing direct actual-code OIR native, control and
Plausible jobs remain bounded evidence with explicit premise counts.

- [ ] Prove whole-pass `PassContract`, including extraction-to-LIR `SiteFor`,
  source correspondence, complete group layout and dependency construction.
- [ ] Prove bounded sort-checker correspondence and structural-totality
  recognizer soundness for actual admitted bodies; neither is established by
  `walk_extracts` or the empty-block witness.
- [ ] Prove `SearchContract` and `RequestContract`, including typed Boolean
  completeness/functionality of term/frame interpretation, guarded and bound
  environments, and complete domains. Do not infer them from finite tests.
- [ ] Prove compatibility/existence of actual LIR equation/source models and
  the upstream LIR/MIR semantic premises, preserving their existing proof
  inventories. The empty-definition witness does not prove general models.
- [ ] Justify mutually partial assumption dependencies separately before
  reporting verified results for them. Retain their unresolved edges/reasons.
- [ ] Restate recursive extraction and interpretation contracts in Fren once
  Fren2 supports their actual recursive carriers and judgments. No Fren1
  recursion extension or copied executable pass is a prerequisite.
- [x] Supply SMT normative contracts, bounded model/source confirmation and
  conservative checker reports; their universal semantic bridges remain pending.

The FLS/SML primary-source material already consulted for the Language/LIR
correction was read from its retained cache while network access was paused:
FLS 1.1.1/1.1.2/1.1.4 and expression legality/evaluation structure; SML Revised
4.1/4.2 semantic objects, 4.10 context judgments and 6.2/6.3/6.7 dynamic
objects/environments/inference conventions. OIR uses the separation of
semantic objects, judgments and side conditions without adopting Rust or ML
language behavior. The exact consulted excerpts and hashes are recorded in
the external phase provenance.

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

`SemanticDomain` states the shared source static judgments and
`SourceFunctionality` of actual retained body roots in their own lexical
contexts; no universal proof is claimed. It does not demand uniqueness for
arbitrary caller-created expressions, which may have duplicate matching arms.
The shared match-coverage judgment, separately from typing, constrains source
roots and descendants. Functionality compares derivations in the same environment;
confirmation additionally requires typed arguments.
`ConfirmedCounterexample` requires actual admission/production, construction
correspondence, this semantic domain, request membership, static safety, typed
arguments, true assumptions and a false goal. `produced_goal_root` proves the
goal is an actual MIR root; `counterexample_refutes` uses `RootInventory` to
establish source membership before invoking functionality. A solver SAT answer
by itself does not establish source confirmation.

The R1 regression proves a sufficient executable condition for
`SourceFunctionality`: every retained root is a singleton match with a false
Boolean arm. The real producer admits an enum program with one function and
one false expectation satisfying that condition. A separate construction proves
such matches have a defined value from the actual resolved local/constructor
premises, avoiding vacuous uniqueness. Fabricated two-arm matches retain both
raw value derivations, but a proof excludes them from roots satisfying the
condition. A written duplicate-arm source must fail specifically with the
expected repeated-constructor coverage diagnostic. These checks repair the
review's impossible unrestricted premise; they do not prove all of
`SemanticDomain` or universal recursive functionality. The previous controls
checked record retention and theorem consequences under an assumed semantic
premise, so they did not detect that the premise itself excluded valid enums.

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

MIR, LIR, OIR and SMT now have substantive formal core contracts. Universal pass proofs remain
open at all non-identity boundaries.
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
body; these edges are prerequisites, never Boolean premises. OIR itself produces
no aggregate verdict; the downstream source checker discharges these edges.

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

The checked test item below is finite evidence. The eight `oir.walking.*`
rules now have the formal relations and partial proofs inventoried above;
the remaining universal whole-pass laws are still unproved. Neither the
primitive facts nor these tests prove the unchecked statements:

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
retention and local structure. They are not OIR extraction proofs.
`walk_extracts` now proves successful traversal satisfies its extraction
judgment. Whole-pass construction and pipeline soundness remain unproved;
that theorem does not change the source/solver proof boundary.

## LIR contracts and proof boundary

`Spec/Compiler/Lir.md` specifies actual `FrenLir.Term`, `Verification`,
`Lowered`, `Body`, declarations, questions and requests. Its displayed Lean
block is byte-for-byte the wrapper's compiled reference block. It reuses
shared production types, contexts, source expressions, canonical signatures,
MIR definitions and static judgments. No executable compiler or recursive IR
is copied into Fren. The old Light example and its five example-only rules
`lir.primitive.polarity`, `lir.primitive.guards`, `lir.primitive.strict`,
`lir.primitive.integers` and `lir.primitive.enum` are retired. They never
established logical-lowering correctness. A smaller finite Fren verification
algebra is checked alongside the substantive actual-code relations.

`Sorted` specifies unbounded sort derivations, with exact slots, canonical
signatures, nominal constructor validity, lexical lets and origin contexts.
`Assigned` relates typed lexical slots to value/domain pairs. `Meaning`
interprets actual terms using actual strict primitives and symbol components;
only zero-divisor values are supplied by `ZeroValues`. `Models` constrains
actual source definitions on typed argument assignments, independently of
any lowered output. `SourceValue` is the shared declarative strict relation,
not the lazy evaluator. This unit assumes no global functionality claim over
fabricated expressions. `Mir.SemanticDomain` retains its accepted restriction
to actual source roots, with match coverage separate from typing.

`Holds` specifies scoped verification. `Site` records every static check's
child-index address, nearest written origin, lexical context and ordered
branch/binder frames. It visits both alternatives without evaluating guards;
equal formulas do not merge distinct paths. Guards retain incoming contexts
across inner binders. `Lowers` gives every admitted expression form an exact
source-to-actual-LIR relation, including local domain checks, both ordinary
operands, unused let values, strict call argument/domain checks, all match
arms and actual final-arm fallback. It uses the production combinators;
it is an inductive specification, not a second executable lowering pass.
`BodyFor`, `DeclarationFor`, `QuestionFor`, `RequestFor` and `Constructs`
retain ordered complete source/IR pairs, including all unused definition and
owned member roots. The actual admitted syntax has no local assert/assume
or subset constructors. Their extension obligations remain explicit rather
than inventing an implementation or erasing supported global members.

`BodyMeaning` states two-way definedness correspondence and value
correspondence on verified typed root assignments. `VerificationDomain`
requires all definitions and independent assumption safety before demand
roots under true assumptions. `QuestionMeaning` separates Sat and validity.
`PassContract`, `InterpretationContract` and `RequestContract` name the
universal correspondence obligations; none is asserted as a proved theorem.
The symbol premise describes source definitions, not an assumed successful
lowered model. Its existence is an additional open obligation, so conditional
correspondence alone cannot establish whole-pipeline soundness.

The wrapper proves exact success factorization, rejection propagation,
failure exclusion, uniqueness and source/MIR/checker retention. Boolean
retention certificates remain Boolean certificates; no unproved lawful-BEq
instance is used to turn them into record equalities. Constructor equations
cover every ordinary binary operator, division, remainder, branch, let and
call. Universal site laws preserve ordinary right operands, incoming let
values and guards across binders. `holds_both` and `summary_sound` connect
verification to its actual constructors and formula summary.
`zero_check_fails` and `unused_false_rejected` exclude false obligations.
`literal_body_for` and `literal_meaning` prove complete sufficient literal
contracts; `true_definition_model` constructively supplies symbols for all
actual definitions whose bodies are true literals. These proofs establish
nonvacuous witnesses without assuming a universal source functionality law.

An actual admitted program has one true-literal function definition, a false
validity goal, a later true assumption and an empty block. The wrapper checks
its exact lowered literal shapes, to which those proved contracts apply,
and its three ordered requests. It rejects three raw retention changes and
requires duplicate-arm and recursive-source failures to propagate unchanged.
The existing source-matched `lir` and `lirProperties` jobs add actual enums,
calls, lets, shadowing, explicit branches, strict operands, false domains,
unused definitions, source identity and mandatory invalid classes. These are
finite controls, not universal producer or interpretation proofs. Changed-law
negative checks must reject dropped operands/let checks, lost remainder checks,
wrong scope contexts and reversed verification algebra in their intended laws.

- [ ] Prove `PassContract`, including all `Lowers` cases and ordered complete
  declaration, member, assumption, goal and demand correspondence, for every
  successful production. Bounded-checker failures are explicit errors; do not
  assume every admitted input succeeds regardless of output/depth budgets.
- [ ] Prove sorting/checker correspondence under the actual source static
  premises, typed interpretation closure, origin validity and scope laws.
- [ ] Prove existence of `Models` for the full admitted nonrecursive definition
  domain from independently justified source functionality and totality on
  the verification domain; the true-literal model proof covers only its class.
- [ ] Prove `InterpretationContract`, both directions of verification/formula
  correspondence, complete source-site correspondence and lexical binding/
  substitution laws. Preserve every origin and path, not just set membership.
- [ ] Prove `RequestContract`, including independent safety and both question
  polarities over complete parameter domains. The mutually partial-assumption
  dependency semantics remains unresolved outside this sufficient domain.
- [ ] Specify closed sharing, quantifiers, recursive equations and local
  assert/assume/subset extensions only with their actual source/IR semantics.
  No such feature or new recursion/crossover prerequisite is delivered here.
- [ ] Restate recursive contracts in Fren when it can quantify over these
  actual recursive syntax, environment and evidence-carrying objects. The
  current Lean specification and finite Fren algebra do not require that gate.

OIR condition extraction and SMT translation/answers/model confirmation remain
separate substantive correction units. Existing OIR/SMT executable tests and
primitive laws are not proofs of these new LIR contracts or completion of
those chapters. No full book/build/test campaign or new production behavior
is part of this correction. Primary-reference structure follows the cached
FLS method/construct rules and Standard ML semantic-object/environment and
inference-rule excerpts read from the original core research record; this
unit performs no network research while access is paused.

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
- Prove the remaining general model decoding and static source correspondence;
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

## Typed model readback boundary

`FrenOirToSmt.Model` decodes actual bounded cvc5 `get-value` responses to
source-order Bool/Int/nominal-enum parameters. `Confirm` retains both physical
requests/receipts, the exact source witness and question envelope, then calls
`FrenEval.evaluate` for all retained premises and the original goal polarity.
The original raw `solve` and ordinary status protocol are unchanged.
`FrenOirToSmtTests.Model` is called from the existing `runControls` runner.
It tests solver-generated models, decoder rejection, a solver-produced model
for changed SMT rejected by the source interpreter, conservative static-domain
rejection, unresolved prerequisites, and bounded transport failures. Direct
Plausible tests the actual assignment boundary with accepted/rejected counts
and deterministic regressions. These checks are finite evidence, not proofs
of the named universal contracts or all-language verification.

The shared library dependency table must explicitly permit the actual source
evaluator import; it must not be bypassed or replaced with a copied evaluator.


## Source checker result coverage

`FrenOirToSmt.Checker.checkSource` runs actual parsing, admission, production,
bounded solving, typed readback and source confirmation. The pure `summarize`
boundary regenerates the admitted program's inventory, validates exact ordered
source/question envelopes and run/question/request/limits/process bindings,
and recomputes model decoding and source observations. A bounded dependency
fixed point and confirmed owner nonvacuity gate conservative verification.
Verified, refuted, inconsistent, inconclusive, no-checks and input-failure
reports retain original questions, source spans, reasons and physical evidence
references. Divisor definedness sites are confirmed at their source prefix;
consumed bodies are confirmed only when strict evaluation at the model is
defined and agrees with the interpreter.

`FrenOirToSmtTests.Checker` runs through normal `smtControls` and parent dispatch.
Real source cases cover supported verification, source-confirmed refutation,
all-Unsat inconsistent/vacuous assumptions, static undefinedness in unused
bindings/definitions and both Boolean operands, lexical guards/binders,
unresolved readiness, no-checks, admission, unsupported confirmation,
input/resource and bounded unknown failures. Owned process/protocol failures enter the actual
consumer. Direct Plausible tests actual successful run aggregation with 100
accepted cases and 1000 rejected inventory/receipt mutations, without discarded
premises; deterministic mutations supplement it. Model absence, staleness and
conflict and cross-owner/program/source records are rejected. These are finite
checks and cheap actual-code verdict laws, not proofs of `CheckerContract`,
source/encoding preservation, solver trust or the existing universal model and
evaluator contracts. Process bindings are retained IO evidence, not signatures.
