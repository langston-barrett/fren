# Fren2 specification implementation and proof coverage

The normative reference is `src/Spec/`. It defines a precise source domain:
Booleans, mathematical integers, payload-free nominal enums, named functions,
lets, conditionals, constructor matches and global assumption/expectation
members. Implementation status, checklists and historical evidence belong here.
Neither the reference's scope nor a successful example asserts that the whole
Fren language or compiler has been verified.

## Language core correspondence

The [Core typing chapter](../src/Spec/Language/Types.md) opens with an
overview: a table of its judgment forms and a figure of its main relation
and laws. It ends with an interface of uninterpreted functions whose
contract states that a derivation records its type, which it therefore
determines, and regularity, interpreted in the wrapper by the detailed
definitions. That an expression's type is unique, whatever table types it,
is open (`types.derivation.unique-expression`). The semantic objects and their
well-formedness, the Core's grammar and its one-layer view `CoreF<E>` are
defined by the resolution chapter, which comes before it and produces
them. The chapter imports them and then defines one Fren
function per typing rule with a small figure, derivation tables and what a
table's root unfolds to, the judgment over tables, declarations and
programs, the metatheory and
examples. It contains no Lean code. The [style guide](../src/Spec/dev/Style.md)
specifies the standard, of which this chapter is an example and not a
template. Most of the reference has not yet adopted it.

Evidence is Fren's own. A property the solver proves is an `expect`. A
property proved in Lean is a procedure bound by an `impl` in the wrapper,
and one that is open is a procedure without one; `#fren_trace` in the
wrapper reports their levels. For this chapter it reports the following;
11 of the proved procedures and one trusted are its own, and the rest
belong to the syntax and resolution chapters, which it imports:

```text
evidence: 30 proved, 0 solver, 5 tested, 3 trusted, 0 missing
tested: `spec::lexical::division`, `spec::surface::accepted_trees_well_formed`, `spec::surface::extent`, `spec::surface::grammar_terminals`, `spec::surface::print_parse`
trusted: `spec::names::naming_order`, `spec::names::table_weakening`, `spec::types::expression_uniqueness`
```

Of the three `trusted` procedures, the chapter's own is the open
`types.derivation.unique-expression`. The other two are the resolution
chapter's open `names.expression.table-weakening` and
`names.collection.permutation`. Each claim's reason starts `open:`. Types.md, StaticSemantics.md,
DenotationalSemantics.md, DynamicSemantics.md,
NamesAndScope.md, LexicalStructure.md, Syntax.md, AstAndParsing.md,
[PropertiesAndChecks.md](#definedness-and-verification-correspondence) and the THIR
chapter are the converted chapters: their wrappers trace with `trusted` as the required
level, so a property that loses all its evidence fails `lake build --wfail`,
and the `ruleReqs` job checks that they do. The build does not notice a
check that moves from the solver to random testing: that shows only as an
`fren.evidence` option in the chapter. `types.context.bound` keeps its
solver check across the move of `Snoc` to the syntax chapter's module,
because `lookup` states the bound as its postcondition
(`names.sequence.snoc`), which resolution's module checks by induction:
`fren check --dump=obligations` lists it as `postcondition lookup.bound`
with solver evidence and the hypothesis at the recursive application in
its context, and the check passes. The limit of #669 does not apply, since
the induction is over `lookup`'s own recursion and not one that a check
of another procedure would have to find. The `ruleReqs` job also checks, for all of
them but the THIR chapter, that every Fren item is linked by the nearest rule
before it and every linking rule is followed by its Fren. The THIR
chapter's correspondence theorems over production Lean types are named in
its prose: Fren cannot state them as procedures. The other Spec chapters
are not yet converted.

### Fren1 limits that shape the chapter

- **No nested recursive datatype.** Fren1 refuses a recursive occurrence
  inside another type instance and has no mutual datatypes
  ([generic types](../src/Reqs/Lang/Generics.md)), so a Core expression
  tree, whose call arguments and match arms are sequences of expressions,
  cannot be declared. The chapter presents expressions through their
  one-layer view `CoreF<E>`, defines the judgment over derivation tables,
  and says which expression a table's root unfolds to. A direct recursive
  form will come with nested recursive types in Fren2 (or a Fren 2.5
  checker); `CoreF<E>` is that form's one-layer view, so the rules will not
  change. The wrapper's Lean theorems are stated over tables too.
- **Recursion is opaque to the solver past one step.** Snoc sequences are
  read by structural recursion. Properties that need induction with a
  generalized argument (call arity, table determinism, scoping, regularity
  and weakening, the lookup shift) are proved in the wrapper.
- **`Nat` inside recursive payloads.** Fren1 rejects a `Nat` within a
  recursive enumeration's payload (`F0389`, `F0714`), and derivation rows hold
  forms, so a local's level is an `Int`. A negative level names no entry, so
  no rule needs a `0 ≤ i` premise.
- **Nonlinear arithmetic.** A product of two variables, or a quotient by
  one, is an error in Fren1, and a defined function cannot apply an
  uninterpreted one, so the denotational chapter's `binary_meaning?` states
  the result's sort for `*` and `div` and the remainder's range for `%`,
  and its prose gives their equations.
- **Chapter order.** The own-spec check reads `src/Spec` in the book's
  reading order, that of `SUMMARY.md` (`specReadingOrder` in
  `FrenTestMain`), so a chapter's Fren may use what the chapters before it
  declare, and each chapter owns its definitions.
- **Vacuity of the coverage expectation.** `coverage_separate` states its
  claims as disjunctions: the solver proves them, but cannot exhibit a typed
  match with an opaque earlier arm sequence, which a guarded claim's vacuity
  check needs.
- **Operator enums.** `UnaryOp` and `BinaryOp` are the Syntax chapter's, in
  `spec::surface`, which the Types and semantics chapters import.
- **Undecidable parts.** The chapter has no `undecidable` opt-out; this is
  a consequence of the representation, not a rule.
- **Evidence for Lean-proved laws.** A law that Lean proves has, as a
  procedure, its own realizability check, which asks the solver for the law
  itself; the solver cannot do the induction. So each law's procedure sets
  `fren.evidence "random"`, only so that the solver is not asked for that
  induction, and states its hypotheses in its `ensure` with `when`. Random
  inputs rarely meet the hypotheses, so the testing is weak and is not
  claimed as evidence. A procedure without outputs and calls is reported
  `proved` without evidence, so each law's procedure has one output,
  `holds?`. Two Fren gaps to file: `fren trace` does not take into account
  that a procedure's own checks ran only by random testing, and there is no
  `fren.evidence` setting that defers a procedure's checks to its `impl`
  (no `"lean"`; see [Methods](../src/Reqs/Methods.md)). Once either is
  fixed, the template drops `holds?` and the random setting.
- **Interface.** A contract on a function returning a derivation has a
  realizability check outside the decidable core, so the interface cannot
  state weakening as a contract of a `weaken` function; the overview links
  to the procedure instead. The interface uses the chapter's concrete types,
  not abstract ones, and so comes at the end: with four abstract types in
  the reference, the random test of the unrelated `lang::element_witness`
  in `src/Reqs/Lang/ElementQuantifiers.md` found no outputs (`F0609`) and
  `ownSpec` failed. A procedure's random tests should not depend on
  unrelated declarations; that is a Fren bug to file. Fren1 also
  cannot name constructors of `Ty` `Bool` and `Int`, which are built-in
  types, so `Ty::Boolean` and `Ty::Integer` remain.
- **Lean-only correspondence.** The THIR chapter's level-to-index and
  operator correspondence theorems are over production Lean types, which
  Fren cannot name, so those rules name their theorems in prose.

### Correspondence with production

The level-to-index conversion, the operator correspondence, the primitive
contracts and their `impl` bindings, and the open traversal correspondence
are in the [THIR chapter](../src/Spec/Compiler/Thir.md), proved in its
wrapper. Production code, including `FrenBase.Binding`, `FrenHirToThir` and
the compiler chapters, numbers locals nearest first; the Core uses levels.
The rest of the erasure/refinement relation between the Core and the
compiler is specified later.

| Rule | Evidence |
| --- | --- |
| `types.overview.interface`, `types.overview.determinism` | The interface's contract, checked for realizability by the solver and proved for the detailed definitions by the wrapper's `interp`; that a derivation determines its type follows by the solver, because a table records its root's type |
| `types.context.bound`, `types.context.weakening`, `types.layer.operators`, `types.layer.determinism`, `types.layer.inference`, `types.judgment.coverage-separate`, `types.examples.rejected` | Fren expectations |
| `types.layer.call-arity`, `types.layer.regularity`, `types.derivation.regularity`, `types.judgment.regularity`, `types.derivation.scoped`, `types.derivation.unique`, `types.layer.weakening`, `types.derivation.weakening-lookup`, `types.derivation.weakening`, `types.judgment.weakening`, `types.examples.derivations` | Procedures bound by `impl` in the wrapper: `proved` |
| `types.derivation.unique-expression` | A procedure with no `impl` and a `trusted` claim whose reason starts `open:` |
| `types.judgment.adequacy`, `types.judgment.decidability`, `types.symbols.resolution`, `types.safety`, `expressions.value.denotation` | Open, stated in prose: Fren cannot state them |
| `thir.core.levels`, `thir.core.unary`, `thir.core.binary` | Lean theorems named in the rules' prose |
| `thir.primitive.compatibility`, `thir.primitive.unary`, `thir.primitive.binary` | Procedures bound by `impl` in the THIR wrapper |
| `thir.algorithmic.layer`, `thir.algorithmic.embedding`, `thir.algorithmic.outcome`, `thir.algorithmic.modes`, `thir.algorithmic.operators`, `thir.algorithmic.literal`, `thir.algorithmic.local`, `thir.algorithmic.constructor`, `thir.algorithmic.unary`, `thir.algorithmic.binary`, `thir.algorithmic.call`, `thir.algorithmic.let`, `thir.algorithmic.if`, `thir.algorithmic.match`, `thir.algorithmic.paren`, `thir.algorithmic.synthesis`, `thir.algorithmic.local-callee`, `thir.algorithmic.declaration`, `thir.algorithmic.table`, `thir.algorithmic.unfolding`, `thir.algorithmic.judgment` | Definitions: each form's rule is a function from its children's typings to an outcome, a type or the first blamed premise and its fault |
| `thir.algorithmic.outcomes`, `thir.algorithmic.example`, `thir.algorithmic.unfaithful` | Procedures bound by `impl` in the THIR wrapper and proved by evaluation: one outcome for each fault of each rule, the two tables of `(true)`, and the table that shows the second condition of reflection is needed |
| `thir.algorithmic.agreement`, `thir.algorithmic.parens` | Fren expectations, one layer at a time, for every form but a match; the match case is a procedure bound by `impl` in the THIR wrapper: `proved`, with no assumption about the first arm |
| `thir.algorithmic.first-arm`, `thir.algorithmic.sequences`, `thir.algorithmic.rows`, `thir.algorithmic.preservation`, `thir.algorithmic.reflection`, `thir.algorithmic.unique`, `thir.algorithmic.expression-sound`, `thir.algorithmic.expression-unique` | Procedures bound by `impl` in the THIR wrapper: `proved`, for supplied tables. Soundness and uniqueness for an expression relate two tables by a supplied pairing of their rows |
| `thir.algorithmic.primitive` | Fren expectations against the primitive contracts, and Lean theorems named in the rule's prose |
| `thir.algorithmic.step` | Lean theorems named in the rule's prose: the production `step` returns the outcome of the rule of a unary operation, a binary operation, a conditional, a let and a parenthesis, and `typeBody` that of a body, with a mismatch at the origin of the blamed premise |
| `thir.core.derivation` | Open for expressions. The `thir.algorithmic` rules prove the part for supplied derivation tables; the production half is open but for the five forms of `thir.algorithmic.step` |
| `thir.algorithmic.desugared-unfolding`, `thir.algorithmic.tree-lift`, `thir.algorithmic.expression-complete` | Open, stated in prose. They depend on instantiating the generic table theorems `Spec.Tables.Valid.derives`, `Spec.Tables.Derives.table` and `Spec.Tables.Unfolds.unique` at HIR layers, and on the Core's `Spec.Language.Types.judgment_adequate` |
| `thir.algorithmic.production` | Open, stated in prose: the other forms of `step`, that a child's failure is the node's when every earlier child and check succeeds, and that the traversal yields a valid HIR table |

Definitions carry no evidence; they are not implementation proofs. Open
laws remain normative obligations. Existing production `FrenHirToThir.HasValue`
and `FrenHirToThir.TypingSound` concern the retained AST. Native tests,
Plausible, closed examples and layer step cases do not establish
`TypingSound`, its converse, or a complete source-to-Core occurrence
correspondence. The informative source examples' diagnostics, such as
`l + 1` at line 5 column 28, byte span `[71, 72)`, are today's checker's.

- [ ] Represent an expression as a term table (forms and a root) and define
  the judgment as `derivation?` plus `alike?` between the term table and
  the typing table, so that `types.derivation.unique-expression` and
  `types.judgment.decidability` become Fren statements.
- [ ] Prove `types.judgment.adequacy` in Lean against a nested inductive
  Lean expression type with `ofLayer`/`layer`, as in the Syntax wrapper; it
  would turn every table result into an expression result.
- [ ] Prove `types.derivation.unique-expression` and
  `types.judgment.decidability`.
- [ ] Generate this section's evidence inventory from `#fren_trace` output
  rather than copying it.
- [ ] Replace the per-form maps over `CoreF` (`annotate`, `weaken_layer`,
  `children`, `layers_paired?` and their sequence helpers) with one generic
  traversal using Fren's second-class higher-order functions, and derive
  `infer_layer` from the rules instead of restating them.
- [ ] State the dynamic semantics as a Fren definition and prove `types.safety`.
- [ ] Restate the judgment over recursive expression trees once Fren
  supports nested recursive types.
- [ ] Move the surface-elaboration section, which is now in the resolution
  chapter (`names.surface.*`), to the derived-forms chapter.
- [ ] Drop the THIR chapter's `spec::thir` primitive operator contracts,
  which duplicate `binary_type?` and production, once `core_unary` and
  `core_binary` cover their `impl` uses.
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

The type wrapper checks the public concrete example constants by evaluating
the generated Fren definitions with `decide`. These are exact closed cases,
not sampled traversal soundness. The expression wrapper checks the examples
of the definitions it owns.
Historical requests below to wait for recursive Fren datatypes before
restating typing are superseded by the one-layer definition; its inductive
closure and implementation correspondence still need universal proofs.

## Definedness and verification correspondence

The [definedness and verification chapter](../src/Spec/Language/PropertiesAndChecks.md)
defines, over the derivation tables of Core typing, the condition of each
layer, the obligations collected from a condition with their hypotheses,
a declaration's table of members with the obligations of each,
satisfaction at an assignment, validity, verdicts, and defined and
verified programs. Satisfaction reads row values from the table evaluator of the
[dynamic semantics](../src/Spec/Language/DynamicSemantics.md#the-table-evaluator).
Its wrapper's `#fren_trace` reports the following; 13 of the proved
procedures, the five tested and three trusted belong to the chapters it
imports, and 15 proved and one trusted are its own:

```text
evidence: 47 proved, 0 solver, 5 tested, 4 trusted, 0 missing
tested: `spec::lexical::division`, `spec::surface::accepted_trees_well_formed`, `spec::surface::extent`, `spec::surface::grammar_terminals`, `spec::surface::print_parse`
trusted: `spec::names::naming_order`, `spec::names::table_weakening`, `spec::types::expression_uniqueness`, `spec::verification::complete`
```

| Rule | Evidence |
| --- | --- |
| `verification.generation.strict`, `verification.generation.guarded`, `verification.generation.divisor`, `verification.obligation.hypotheses`, `verification.obligation.cut`, `verification.member.scope`, `verification.program.represented`, `verification.obligation.flattening`, `verification.generation.context-independent` | Laws for all inputs, bound by `impl` in the wrapper: `proved` |
| `verification.examples.obligations`, `verification.examples.assignments`, `verification.examples.scopes`, `verification.examples.members`, `verification.examples.domain`, `verification.examples.tables` | Constant examples that the wrapper evaluates with `decide`: `proved` |
| `verification.validity.interface` | Definitions with no law of their own: `valid?` is defined as satisfaction by every assignment of the obligation, and `sound?` says when a verdict answers an obligation soundly. `fren check` reads them; nothing is tested or proved, since the definitions state the whole meaning |
| `verification.generation.complete` | Stated as a procedure over tables, `trusted` and open |
| `verification.program.tables` | A definition, `represents?`, with the law and the examples above. Typed tables are found in a declaration's table by position, with their row references moved. The correspondence does not count occurrences of equal conditions. That each member has its source keyword and declaration, and that every typed program has representing tables, are not stated |
| `verification.validity.meaning`, `verification.validity.uncomputed`, `verification.program.defined`, `verification.program.verified`, `verification.program.assumptions`, `verification.generation.function`, `verification.keyword.evidence`, `verification.soundness` | Prose. Soundness is open |

What shapes the chapter:

- **The evaluator.** `eval` of the dynamic semantics chapter gives a row its
  value in an assignment, so an assignment is only the values of the
  locals, a counterexample is checkable, and the examples' values are
  computed. It gives no value to a product, a quotient, a remainder or a
  call, because a defined Fren function may not multiply or divide two
  variables or apply an uninterpreted function. Satisfaction is therefore
  conservative: a `NonZero` or `Asserted` goal of such a row never holds,
  and a hypothesis that depends on one is never refuted
  (`verification.validity.uncomputed`). A `Defined` goal of a call row can
  hold: it reads the arguments' values and the callee's `require` roots,
  not the value of the call. The law that `Proved` implies
  validity is, for such obligations, stronger than a solver that knows
  these operators can honour; it becomes exact when the evaluator
  computes them.
- **Recursive definitions.** The solver unfolds `condition_holds?`,
  `some_refuted?`, `eval` and `lookup` one step, and decides neither the
  laws about them nor their vacuity checks. So the laws are procedures
  whose own checks are set to random testing, which is not claimed as
  evidence, and the wrapper proves them. Core typing does the same.
- **Members.** A declaration is one table, an optional body row and a
  sequence of members, each a keyword and a root. `member_hyps` folds over
  the members, so the hypotheses of a member and of a body are
  definitions, and `declared_obligations` yields `Asserted` goals. The
  `Decl` of Core typing has no keyword and one table for each condition.
  `represents?` (`verification.program.tables`) ties the two: every typed
  function has a table with its signature's parameters and its body, every
  typed condition is a member of a table, and every member is a typed
  condition. Core typing types each body and condition in a table of its
  own, so a typed table is found in the declaration's one table at the
  rows that end at its root, with its row references moved by the number
  of rows before it. A defined program requires `represents?`, so tables
  that omit a function body, or omit every occurrence of a condition, or
  have a member that is no typed condition, make no program defined. The
  correspondence does not count: one member may stand for several equal
  typed conditions, and several equal members for one. Typing gives
  a condition no keyword and no owner, so definedness is relative to the
  keywords and owners that the tables state; that these are the source's
  is open.
- **Calls.** `Defined(r)` holds where every `require` root of the callee
  evaluates to true at the argument values. The program is a sequence of
  declarations that satisfaction takes as an argument.
- **Keywords.** The source grammar has `assume` and `expect` members only;
  `require` and `assert` members are specified here ahead of it. The `law`
  keyword of Fren1 is retired: `expect` takes its place. The chapter says
  nothing of `assert` or `assume` inside an expression, which the Core
  does not have.
- **The check.** No function `check` is declared. `valid?` is a quantified
  definition and `sound?` a definition over a verdict, and a check is, in
  prose, any function whose answers are all sound. An earlier text
  declared `valid?`, `counterexample` and `check` as uninterpreted
  functions and stated laws about them as a procedure's guarantees.
  `fren check` reads such a guarantee as holding for every interpretation
  of the functions, which is false, so `ownSpec` failed: with `valid?`
  false of an obligation that has no assignment, no counterexample
  exists. The wrapper had proved the laws only for one `interp`, a
  different statement. Laws that constrain an uninterpreted function
  belong in that function's own contract, not in a procedure about it.
  The quantifier of `valid?` has no domain, so random testing cannot
  evaluate it, and no tested law mentions it.

Production: the [LIR chapter](../src/Spec/Compiler/Lir.md) states and
proves, in `lir.walking.demand`, what the compiler's lowering of a binary
operator adds to its operands' verification, for every operand
(`ordinary_checks`, `division_checks`, `remainder_checks`). This chapter
no longer binds a sample of it. `FrenLir.Verification` has the
constructors of `Condition` (`empty`, `check`, `both`, `branch`, `letE`)
and a source-origin marker; it has no constructor case. That the
compiler's whole condition for an expression is the chapter's, the
commuting square with OIR condition generation, is open
(`oir.contract.correspondence`).

- [ ] Prove `verification.generation.complete`: it needs that a row's
  condition in a table is generated from the conditions of the rows
  before it.
- [ ] State as a property that each goal occurs once for each written
  path to it, with exactly the hypotheses of the enclosing branches,
  cases and bindings.
- [ ] Give the evaluator values for products, quotients, remainders and
  calls, then state and prove `verification.soundness`.
- [ ] Give the `Decl` of Core typing each condition's keyword and owner,
  so that `represents?` states that a member has its source keyword, or
  make `Decl` and the member table one definition.
- [ ] State and prove that every well-typed program has tables that
  represent it, and decide whether `represents?` should count the
  occurrences of equal conditions.
- [ ] Rename `PropertiesAndChecks.md` to match the chapter's title.
- [ ] Bind `Lowered.branch`, `Lowered.bind` and `Lowered.call` to
  `if_condition`, `let_condition` and `call_condition` through an
  erasure of `FrenLir.Verification` to `Condition`.

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

1. **Desugaring extensions** (`SCdesugar`, queued edit 1012): parenthesis
   removal and its correspondence with the actual pass are specified below. Each additional
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
observations. Strict evaluation of the retained static obligations must
reproduce an observation only when its body or a function that it transitively
calls mentions division or remainder; any other body is observed by the
interpreter alone. The checker adds conservative
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
  `FrenEval.evaluate` and, when the body or a transitive callee mentions
  division or remainder, an agreeing budgeted strict evaluation, with explicit
  rejected and unconfirmed statuses. Preserve static questions and unresolved
  readiness; a consumed body whose strict evaluation is undefined at the model
  remains unconfirmed. Check divisor definedness counterexamples by evaluating
  the let values and guards on the path to the site, and the divisor, through
  the interpreter and an agreeing strict evaluation.
- [x] State `SourceBoolean` through `Lir.SourceValue`/`Mir.ValueOf` and a
  definedness counterexample through `Mir.StaticAt` and a zero divisor, a
  witness against `Mir.BodySafe`, so that `SourceCandidate` covers validity
  and definedness rows without naming the evaluators or a model.
  `confirmed_ready` proves a part of `ConfirmationContract` that does not
  depend on evaluation: a confirmed answer names a ready question of an entry
  of the regenerated program.
- [ ] Prove `ReadbackContract` and the rest of `ConfirmationContract`. Three
  obligations do not depend on evaluation: membership of the entry's question
  in `out.oir.questions`, `ModelAssignment` from the arity, type and enum
  checks, and the pairing of the answer with the question's kind. Three need
  inductions: adequacy of the budgeted strict evaluator to
  `Lir.SourceValue`/`Mir.ValueOf`, adequacy of the interpreter alone on
  well-typed nonrecursive bodies that reach no division or remainder, and
  that the path followed to a definedness site is a `Mir.StaticAt` traversal.
  Justify mutually partial assumptions.
- [ ] Prove that a `SourceCandidate` gives an `Oir.Violation` of its question:
  that the hypotheses are `Lir.AllTrue` in every `Smt.Model` (from
  `Lir.InterpretationContract` and every `Smt.Model` satisfying `Lir.Models`),
  that the question's frames are active at the site, and model existence,
  without which a statement about every model is vacuous.
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
walking-program judgments. No executable compiler or IR is duplicated. The
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

## The typed module: rules and evidence

The separated type checker's module rules are in
`Spec/Compiler/Thir.md`, proved in its wrapper over the production
`FrenHirToThir.Pass.typeModule` and `typeItem`.

| Rule | Evidence |
| --- | --- |
| `thir.module.items` | `Alone` types one item against the module's signatures and constructor owners. `alone_reads_signatures` proves that modules with the same signatures and constructor owners give an item the same result. `function_params_first` and `check_params_first` prove that a parameter error is the item's error. |
| `thir.module.errors` | `ModuleResult` states the rule without the production module function. `typed_module_sound` proves that the production result satisfies it, and `typed_module_unique` that a result satisfying it is the production result. `item_error_reported` and `reported_error_alone` prove that the error list holds exactly the errors of the items that fail alone. |

These are universal Lean proofs. The `typingProperties` job adds a generated
property: it takes a generated module with one injected fault, breaks further
items of it, and requires exactly the error of each failing item, in
declaration order. Its census fails unless some samples have two or more
failing items. The agreement test with the legacy checker cannot show this,
since the legacy checker stops at the module's first error and the test
compares only single-error results. Two parts are covered only by tests: that
a check's members are typed in written order and its first failing member
gives the error, and that each error names the origin of the offending node.

Spec gap. Before this change both rules were stated only in prose under
"Proof obligations", with no relation, theorem or binding in the wrapper, and
were checked by one hand-written module. The generated properties injected a
single fault, so no generated case had two failing items. The relation and
theorems above now state the rules, and the generated property checks them
with several failing items.

## Desugaring contracts and proof boundary

`FrenThirDesugar.desugar` takes the THIR module and returns the desugared
THIR module. It removes parentheses and nothing else. That it reads only its
argument follows from its type, a pure function from the THIR module to the
desugared module. The `layering` test checks one further thing: that no pass
(the parser, the resolver, the type checker or any later pass) is reachable
from its imports. It does not check that the syntax tree or the legacy tables
are out of reach, since the shared module library the pass imports defines
them too. The wrapper of
`Spec/Compiler/Desugaring.md` proves, for every input, that the pass
is related to its input by `Erases` and `ErasesModule`, relations stated
without the production functions: a parenthesis has the result of its body,
every other node keeps its origin, type and data over related children, and
the module keeps its identity, its items in order, each enum, each function's
and check's identity, origin, parameters and result type, each member's kind,
label and origin, and each origin table. It also proves that anything so
related to an input is the pass's output, and that no output node is a
parenthesis. These are universal Lean proofs.

`FrenThirDesugarTests` holds Plausible properties over generated inputs:
well-typed modules from `FrenGen.Thir`, with zero to two parentheses added
around every node by `FrenGen.parens`, and the same modules with one injected
fault. They check that the output is the input with only its parentheses
removed, against an oracle on the printed form; that typing the
parenthesis-free erasure of the input gives the output; that added
parentheses do not change the output's bodies; that the node count falls by
one for each parenthesis and scoping is unchanged; and, as a check of the
generator, that the input with added parentheses is well typed. This is
bounded evidence. No theorem yet states that desugaring preserves the typing
judgment or evaluation; the evaluator still reads the walking program.

The walking program's definitions, which MIR construction reads, are in a
chapter of their own, `Spec/Compiler/Walking.md`, with rule ids
`walking.program.*`, so that removing the walking program deletes that chapter
and leaves the desugaring chapter alone. Its wrapper holds `Program`, `Produces`, `Rejects`, `Guard`, `ScopedChild`,
`ScopedAt`, `DomainSite`, `Members` and `Evaluator`, and proves exact resolved
success and failure, the type/coverage/non-recursion admission factorization,
failure exclusion, source-result projection and the output's
admission/retention/static facts. `ScopedChild` and its closure project to the
shared THIR context relations. `DomainSite` records candidate
division/remainder sites, including unused let values and both ordinary
Boolean operands; it does not discharge them. The walking program is the
legacy checker's boundary, not an output of desugaring;
`docs/fren2-walking-removal.md` plans its removal.

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

`FrenThirDesugar.desugar` maps the THIR module to the desugared THIR module
by removing parentheses. The wrapper proves the pass's defining equation and
its uniqueness; generated-input property tests check its whole-module
consequences. `FrenWalking.Program` separately carries the actual successful
`checkWalking` result as evidence for the later passes, with the `static`,
`rejected` and `deterministic` theorems.

- [x] Implement desugaring over the THIR module alone, with no source front
  end, and forbid the dependency in the `layering` test.
- [x] Test it on generated well-typed modules and on faulted ones.
- [ ] Prove that desugaring preserves the typing judgment and evaluation, once
  both are stated over the shared expression representation.
- [ ] Move MIR construction and the later passes to the desugared module, then
  remove the walking program (`docs/fren2-walking-removal.md`).
- [ ] Specify and implement each future sugared form before admitting it, and
  establish its typing and meaning preservation, including table disjointness.
- [ ] Restate recursive correspondence in Fren when it can express the actual
  recursive syntax and judgments, without copying the IR or pass into Fren.

## Retained record: src/Spec/Compiler/Mir.md

## Implementation evidence and remaining obligations

`FrenThirToMir.produce` consumes `FrenWalking.Program`, whose equality
witness certifies actual walking admission. `fromSource` uses that same
parser, resolver and walking admission boundary. Rejected sources retain
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

The chapter is converted: it defines resolution in Fren as total functions
from the syntax chapter's tree (`SurfaceF<E>`) to the Core, and its wrapper
traces its evidence. It comes before Core typing and defines what
resolution produces: item identities, types, contexts, the symbol
environment and their well-formedness, snoc-sequence lookup, and the
Core's one-layer forms `CoreF<E>`. It has no expression type of its own;
its source table is rows of the syntax chapter's nodes. Its declarations
(`SrcDecl`) are still its own type, with snoc sequences where the syntax
chapter's declarations have `Seq`s.
The wrapper proves in Lean the laws of local lookup, weakening by an
unmentioned name, the resolved table's scoping and alignment, the item
kinds that each resolved position names, sibling scopes, the parallel
parameter context, that collection yields a well-formed symbol
environment, that exchanging the last two declarations changes
nothing that collection binds, that two sequences of the same
admitted declarations collect alike, that a clear written type, one whose first name is no function of the
module, resolves in the environment of enumerations exactly as in the
collected one (`names.collection.agreement`); admission makes every
signature type clear, that a resolved `let` and a
resolved parameter satisfy the `?` suffix rule of typing and that one
breaking it is refused (`names.expression.layer`,
`names.collection.parameters`), that an item shadows the module's name,
and exactly when a first name denotes nothing (`names.paths.unknown`). It binds the production resolver's
nearest-name search and name equality (`FrenAstToHir.nearest`,
`FrenAstToHir.sameName`) to their rules. Two of the chapter's claims are `trusted` and open: `naming_order`
and `table_weakening`. A third is open and stated in prose only:
`names.expression.unique-expression`, that two source tables denoting the
same expression resolve to tables that unfold alike. The wrapper proves
determinism for one source table, not for the expression it denotes.

The chapter's functions return no diagnostic, so the codes its prose
names are untraced: F0201, F0203, F0204, F0206, F0210, F0212 and F0213
have no Fren item and no evidence. Its rules decide only that the
construct has no resolution.

What production does differently, recorded here rather than in the
chapter: the resolver numbers locals by index from the newest binder,
not by level; it may find a path's target before it knows the position,
and reports a function used as a value or a local used as a callee when
it forms the typed term; it collects expectations into the item namespace and resolves
their parameter types and bodies, which the chapter's domain leaves
out; and
it collects names only, while the chapter's `collect` also resolves
signature types.

- [x] Bind the nearest-name primitive to its rule with a genuine Lean
  proof over every scope.
- [x] Prove in Lean that collection yields a well-formed symbol
  environment (`names.handoff.environment`), which is what
  `types.symbols.resolution` assumes.
- [x] Prove the exchange law of collection (`names.collection.order`).
- [x] State the order law for every reordering of the declarations
  (`names.collection.permutation`) and prove that sequences of the same
  admitted declarations collect alike.
- [ ] Prove `naming_order`: a reordering of admitted declarations is
  admitted. It is `trusted` and open.
- [ ] Prove `table_weakening` (`names.expression.table-weakening`), which
  is `trusted` and open; `names.expression.weakening` proves the law for
  one layer.
- [ ] Read declarations as the syntax chapter's `Function` and
  `Enumeration` rather than `SrcDecl`, with an explicit conversion from
  `Seq` to `Snoc`.
- [ ] Decide the `let` annotation. The Fren2 parser's `let` has no written
  type, so the syntax tree's `Let` has none and resolution gives a Core
  `let` an annotation only for a `?` binder. Core typing's annotated `let`
  (`types.expression.let-annotated`, with its informative example
  `let b: Bool := n in 0`) and the written-type case of `let_annotation?`
  (`names.surface.suffix`) still state rules for a written annotation,
  which no Fren2 source can write. `names.surface.suffix` records this as
  open, and `names.expression.layer` records that `let_handoff`'s `kept`
  and `refused` and the examples `ANNOTATED_LET` and
  `QUESTION_LET_REFUSED` were removed with the written type.
- [ ] State in resolution the rejection of a module, a global expectation
  and a member label named `Bool` or `Int`. `syntax.name.reserved`
  reserves the names for them and the implementation rejects them, but
  resolution's domain has no expectation and `collect` does not inspect
  the module's name (`names.paths.reserved`).
- [ ] Let `types.examples.rejected` drop the extra fact of its call
  example, that one argument does not fit an empty parameter list. The
  solver needs it since `Snoc` moved to the syntax chapter's module: Fren
  tries no induction over an enumeration of another module (#669), and
  the induction's deeper unfolding used to supply the step.
- [ ] Define resolution for expectations, which the production resolver
  collects into the item namespace and resolves; the chapter's domain
  (`names.overview.domain`) leaves them out.
- [ ] State in Fren and prove `names.expression.unique-expression`, which
  needs the relation "unfold alike" on source tables.
- [ ] Return the diagnostic from `head`, `descend` and the naming checks,
  so that the F02xx codes are traced.
- [ ] State that a module's resolution is invariant under reordering its
  declarations, bodies included, with a forward-call example; the order
  laws stop at collection.
- [ ] Return the environment and each function's resolved body from the
  module judgment, and state that every function has exactly one body.
- [ ] Bind path-head and member lookup and collection to the production
  resolver, whose functions read production scope and token structures
  that Fren does not yet state.
- [ ] State the correspondence between source text and the source table
  that this chapter resolves, once the Syntax chapter defines the table.
- [ ] Extend this chapter before imports, multiple modules, visibility across
  modules, payload binders, generics, recursion policy or body visibility are
  implemented.

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
a consumed body that reaches division or remainder is confirmed only when
strict evaluation at the model is defined and agrees with the interpreter,
and any other consumed body by the interpreter alone.

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

## Syntax decisions and design debt

These entries are the decisions and the design debt that the chapters
[Lexical structure](../src/Spec/Language/LexicalStructure.md) and
[Syntax](../src/Spec/Language/Syntax.md) cite.

Decisions:

- **L1.** `<-` is rejected text, reserved for a possible future operator;
  `x<-1` is an error rather than `x < -1`.
- **L2.** The keywords of today's Fren that the Fren 2 grammar does not use
  are reserved, and `true`, `false` and `not` are keywords.
- **S1.** Every comma-separated list allows a trailing comma; only an
  expectation's parameters and a match's arms may be empty.
- **S2.** The remainder is written `%`, and `mod` is only the module keyword.

- **D2.** `Bool` and `Int` are reserved names: no module, enumeration,
  variant, function, expectation, parameter or member label is named by
  one, and no `let` binds one. Name resolution enforces it (F0212).
- **G1.** Decided: deferred to Fren 2.5's nested types and element
  constraints, with no new features in today's Fren. Today's Fren has no
  recursive datatype whose recursion passes through a `Seq`, so the
  abstract syntax is the one-layer `SurfaceF<E>`. A `Seq` whose element type
  has a constraint is outside the decidable core, so a name is a `String`,
  and a type with a constraint cannot be an argument of a recursive
  enumeration, so an integer literal carries an `Int`,
  and `syntax.tree.well-formed` states the conditions on names as Fren
  functions of one node or declaration, whose subexpressions have the
  one-value type `Elided`. Two of them, over arms and parameters, are
  definitions outside the decidable core. They take `Elided` rather than
  any type `E` because today's Fren compiles a truth-valued `match` over
  a generic enumeration to a definition that cannot run.
- **G2.** The grammar's productions are EBNF, with no second statement in
  Fren: `syntax.tree.productions` binds `type_name`, and a test abstracts
  the parser's trees to `SurfaceF`, checking each operator's written token
  against `unary_spelling` and `binary_spelling`.

`BinaryOp::Rem` names the remainder, which is written `%` (S2).

Evidence of these chapters, and its bounds; the compiled `syntaxChapters`
job of `fren_test` runs these checks in about 20 seconds, and `ruleReqs`
checks that each rule of the three chapters links the Fren items after it:

- [ ] The lexer's pieces are those that folding `next_piece?` gives, the
  start of the text and each position where a piece ends having exactly
  one next piece and no longer text of a class than
  `lexical.piece.division` allows, on every text of up to three characters
  over 24 characters, of up to four over ten, a corpus and 500 seeded
  random texts (`lexer_agrees`); positions inside a piece are checked
  only for the exhaustive texts, which include their own suffixes, and
  nothing is proved for all texts.
- [ ] The tree of each accepted text is well formed on the first 80000
  inputs of the grammar comparison (`trees_agree`).
- [ ] The parser's numerals have their decimal values on listed numerals,
  among them 2^64, 2^128 + 1 and 10^40, and 200 seeded random numerals of
  up to 80 digits (`numerals_agree`); not proved for all numerals.
- [ ] The grammar agrees with the parser on exhaustive token sequences of
  up to three, four or five pieces, seeded random sequences, printed random
  trees and files, and the texts near them (`grammar_agrees`), and a
  mutation control of 34 wrong grammars is caught (`mutants_caught`); not
  proved for all texts.
- [ ] Printing by `place`, `shape` and `fits?` and then parsing gives the
  same tree, the printed tokens are the lexer's, removing any pair of
  parentheses changes the tree, and a text that parses to a tree has the
  tokens of its printed text once redundant parentheses, trailing commas
  and leading zeros are removed, on 1000 seeded random trees, every
  operator pair and the texts near 300 trees, of at most six and five
  levels (`roundtrip_agrees`); not
  proved for all trees.
- [ ] Every generated declaration is well formed;
  `declaration_well_formed?` refuses seven ill-formed declaration trees,
  and `node_well_formed?` seven ill-formed expression trees and the
  ill-formed body of an eighth declaration (`declarations_agree`,
  `roundtrip_agrees`).
- [ ] The limits of today's Fren that the chapters work around: a
  `forall` inside `and` or a match arm needs parentheses, a structure
  literal cannot directly follow `=>`, and a slice or concatenation at a
  position that is not a constant is outside the decidable core.
- [ ] `parsing.shared.drivers` is open: the command line and the hosted
  reader do not yet call `FrenParse`.
- [ ] `parsing.primitive.boundary` is open: no theorem relates continuation
  bytes to character boundaries.
- [ ] `parsing.diagnostic.first` is open: tests check diagnostic positions
  of chosen texts, not that each is the first point where the grammar
  cannot continue.
