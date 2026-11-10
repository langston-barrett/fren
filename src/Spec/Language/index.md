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
[Expressions](Expressions.md) uses those definitions for meaning, mentioned
names and operator domains.
[Definedness and verification](PropertiesAndChecks.md) defines the obligations
of a typed expression, the hypotheses under which each must be proved, and
what a solver's answer establishes. Later chapters build on these
same identities, contexts and judgments rather than assuming precomputed
resolution or typing decisions.

The defined source domain has Booleans, mathematical integers, payload-free
nominal enums, named functions, locals and lets, conditionals, constructor
matches and global assumptions and expectations. The [source grammar](Syntax.md)
fixes its concrete forms. Static semantics comprises resolution, typing and
verification, including definedness, match coverage and the absence of
recursive call cycles.
Verification hypotheses are discharged by SMT. Passing typing does not
establish verification. Dynamic semantics applies only to well-typed,
verified programs. It assigns no behavior to undefined operations and does
not prescribe evaluation order. A solver limit or unknown result
proves neither a goal nor its negation.

Numbered rules state the reference requirements. Core typing uses
the rule status syntax defined by the
[style guide](../dev/Style.md#rule-evidence-metadata). Links on each `r[...]`
line identify its checked Fren contracts. Normative definitions precede their
worked examples; a checked example tests those definitions, and does not
replace their full-domain meaning. The [compiler part](../Compiler/index.md)
relates source constructs to representations and passes. Implementation
correspondence, finite testing and unproved universal laws are recorded in
[development coverage](../../../docs/fren2-specification-coverage.md).
