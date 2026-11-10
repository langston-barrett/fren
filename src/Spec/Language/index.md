# Language

A Fren specification declares values and functions, states assumptions and
asks whether its expectations follow. This part defines the source forms,
their meanings, and the obligations that checking them produces.

Start with source text and [syntax](Syntax.md), which defines the tree
that the parser gives. [Resolution](NamesAndScope.md) reads that tree. It
maps the names of source forms to canonical item identities and local
levels, and collects a module's declarations into the symbol environment.
It defines what it produces: canonical item identities, Boolean, integer
and nominal enum types, local contexts indexed by de Bruijn level, a symbol
environment of signatures, constructors and enumerations, and the Core's
complete one-layer expression forms. [Core typing](Types.md) defines the
typing judgment over that Core.
Source constructs are defined by derived forms that translate into this Core.
Three chapters give the Core its semantics. The
[static semantics](StaticSemantics.md) comprises resolution, typing,
definedness, contracts and termination; a program that is typed, is
defined, meets its contracts and passes the termination check is
verified. The
[denotational semantics](DenotationalSemantics.md) gives a
set-theoretic meaning to each function that is verified together with
the functions that it depends on, where their assumptions are true. The
[dynamic semantics](DynamicSemantics.md) evaluates every well-typed
program by a small-step relation, with error states and one fixed order
of evaluation; a run ends in a value, ends in an error, or diverges.
[Definedness and verification](PropertiesAndChecks.md) defines the obligations
of a typed expression, the hypotheses under which each must be proved, and
what a solver's answer establishes. Later chapters build on these
same identities, contexts and judgments rather than assuming precomputed
resolution or typing decisions.
[Patterns and matching](Patterns.md) defines how a match selects an arm, the
coverage check that every constructor has at least one arm, and the
separate check that rejects unreachable (repeated) arms.

The defined source domain has Booleans, mathematical integers, payload-free
nominal enums, named functions, locals and lets, conditionals, constructor
matches, and the conditions of declarations, among them assumptions and expectations. The [source grammar](Syntax.md)
fixes its concrete forms. Static semantics comprises resolution, typing,
definedness, contracts and termination. Match coverage is part of
definedness, and a match with two arms for one constructor is a
[static error](StaticSemantics.md#r-statics.match.distinct). [Termination](StaticSemantics.md#termination), a sub-chapter of Static
semantics, defines the termination check. A function
declaration
[passes the termination check](StaticSemantics.md#r-statics.termination)
when it has not
[opted out](StaticSemantics.md#r-statics.termination.optional) of the
check and its function is in no recursive group, or when it has not
opted out and its recursive group is
[structurally recursive](StaticSemantics.md#r-statics.termination.structural):
each function of the group has a decreasing parameter, and every call of
the group in a body of the group passes, at the callee's decreasing
parameter, a
[local of size `smaller`](StaticSemantics.md#r-statics.termination.size). An
expectation declaration passes. The check reads the text of the
bodies and has no premise of entailment; that it is
[decidable](StaticSemantics.md#r-statics.property.decidable) is argued
and not yet proved. It rejects some
functions whose every call ends. A declaration opts out
with a mark, which covers its function's whole recursive group; a
declaration that has opted out does not pass the check, and a
declaration that has not passed it is not verified. Not passing the
check is not a
[static error](StaticSemantics.md#r-statics.scope): the declaration may
still be defined and meet its contract. The present
Core has no constructor with arguments, so
[no group whose bodies call it passes](StaticSemantics.md#r-statics.property.subterms). A
contract is a precondition and a postcondition
that relate a function's whole argument tuple to its result; it is not
part of a type. A contract and an assumption
[mention only functions that pass the termination check hereditarily](StaticSemantics.md#r-statics.condition.terminating):
the mentioned function and every function that it reaches have passed
the termination check, and none has opted out. That alone does not make
a condition total. It
[has a truth value](StaticSemantics.md#r-statics.property.conditions)
where those functions are also defined and meet their contracts, with
true assumptions. An assumption is a hypothesis only within its own
declaration.
Verification obligations are discharged by SMT. Passing typing does not
establish verification. The termination check is of one declaration,
and passing it does not state that the declaration's function
terminates: a verified declaration that is in no recursive group may call a function
that has opted out of the check and diverges. So the denotational
semantics gives a function a meaning only when its declaration and the
declaration of every function that it depends on are verified and their
assumptions are true; the function then
[has a denotation](DenotationalSemantics.md#r-denotation.domain). It
assigns no meaning to an undefined
operation and prescribes no evaluation order. The dynamic semantics is
defined for every well-typed program: an undefined operation evaluates to
an error, in one fixed order, and unbounded recursion diverges.
[Adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy) states where
the two agree: an expression over functions that have denotations,
evaluated where its hypotheses are true, ends in a value, which
is its denotation. So a function that has a denotation is
[totally correct](DynamicSemantics.md#r-dynamics.theorem.total-correctness).
A function that is defined and meets its contract
without the termination check has no denotation. It is
[partially correct](DynamicSemantics.md#r-dynamics.theorem.partial-correctness)
where the declarations that it depends on are defined and meet their
contracts too, and all their assumptions are true.
A solver limit or unknown
result proves neither a goal nor its negation.

Numbered rules state the reference requirements. Core typing uses
the rule status syntax defined by the
[style guide](../dev/Style.md#rule-evidence-metadata). Links on each `r[...]`
line identify its checked Fren contracts. Normative definitions precede their
worked examples; a checked example tests those definitions, and does not
replace their full-domain meaning. The [tooling part](../Tooling/index.md)
covers evidence, diagnostics and formatting, which are not part of the
language's meaning. The [compiler part](../Compiler/index.md)
relates source constructs to representations and passes. Implementation
correspondence, finite testing and unproved universal laws are recorded in
[development coverage](../../../docs/fren2-specification-coverage.md).
