# Language

A Fren specification declares values and functions, states assumptions and
asks whether its expectations follow. This part defines the source forms,
their meanings, and the obligations that checking them produces.

Start with source text and [syntax](Syntax.md), then [names and scope](NamesAndScope.md).
The shared semantic core in [types and expression typing](Types.md) defines
canonical item identities, Boolean, integer and nominal enum types, local
contexts, signatures, values and a compositional typing judgment.
[Expressions](Expressions.md) uses those definitions for meaning, mentioned
names and declarative domain obligations. Later chapters build on these
same identities, contexts and judgments rather than assuming precomputed
resolution or typing decisions.

The defined source domain has Booleans, mathematical integers, payload-free
nominal enums, named functions, locals and lets, conditionals, constructor
matches and global assumptions and expectations. The [source grammar](../Compiler/AstAndParsing.md#source-forms)
fixes its concrete forms. Typing, match coverage, absence of recursive call
cycles, operation domains and logical truth are separate judgments. Passing
one does not establish the others. A solver limit or unknown result proves
neither a goal nor its negation.

Numbered rules state the reference requirements. Links on each `r[...]` line
identify its checked Fren contracts. Normative definitions precede their
worked examples; a checked example tests those definitions, and does not
replace their full-domain meaning. The [compiler part](../Compiler/index.md)
relates source constructs to representations and passes. Implementation
correspondence, finite testing and unproved universal laws are recorded in
[development coverage](../../../docs/fren2-specification-coverage.md).
