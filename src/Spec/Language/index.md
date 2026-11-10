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
[denotational semantics](DenotationalSemantics.md) gives each verified
program a set-theoretic meaning. The
[dynamic semantics](DynamicSemantics.md) evaluates every well-typed
program by a small-step relation, with error states and one fixed order
of evaluation; a run ends in a value, ends in an error, or diverges.
[Definedness and verification](PropertiesAndChecks.md) defines the obligations
of a typed expression, the hypotheses under which each must be proved, and
what a solver's answer establishes. Later chapters build on these
same identities, contexts and judgments rather than assuming precomputed
resolution or typing decisions.

The defined source domain has Booleans, mathematical integers, payload-free
nominal enums, named functions, locals and lets, conditionals, constructor
matches and global assumptions and expectations. The [source grammar](Syntax.md)
fixes its concrete forms. Static semantics comprises resolution, typing,
definedness, contracts and termination. Match coverage is part of
definedness. The termination check is a judgment of its own, which need
not be applied; a program that has not passed it is not verified. A
contract is a precondition and a postcondition
that relate a function's whole argument tuple to its result; it is not
part of a type.
Verification obligations are discharged by SMT. Passing typing does not
establish verification. The denotational semantics is defined only for
verified programs, which terminate: it assigns no meaning to an undefined
operation and prescribes no evaluation order. The dynamic semantics is
defined for every well-typed program: an undefined operation evaluates to
an error, in one fixed order, and unbounded recursion diverges.
[Adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy) states where
the two agree: in a verified program whose assumptions hold, an
expression evaluated where its hypotheses are true ends in a value, which
is its denotation. A program that is defined and meets its contracts
without the termination check has no denotation and is
[partially correct](DynamicSemantics.md#r-dynamics.theorem.partial-correctness).
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
