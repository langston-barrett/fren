# Summary

[Introduction](README.md)

# Language

- [Overview](Lang/Overview.md)
- [Lexical structure](Lang/Lexical.md)
- [Types](Lang/Types.md)
- [Items](Lang/Items.md)
  - [Generic types](Lang/Generics.md)
  - [Generic functions](Lang/GenericFunctions.md)
  - [The prelude](Lang/Prelude.md)
- [Scope](Lang/Scope.md)
  - [Laws of scope](Lang/ScopeLaws.md)
- [Procedures](Lang/Procedures.md)
- [Meaning](Lang/Meaning.md)
  - [Laws of meaning](Lang/MeaningLaws.md)
- [Expressions](Lang/Expressions.md)
  - [Local definitions](Lang/Let.md)
- [Patterns](Lang/Patterns.md)
- [Quantifiers](Lang/Quantifiers.md)
  - [Quantifiers over elements](Lang/ElementQuantifiers.md)
- [Modules and visibility](Lang/Modules.md)
- [Calls](Lang/Calls.md)
- [Global expectations](Lang/Global.md)
- [Refinement](Lang/Refinement.md)
- [Decidability](Lang/Decidability.md)

# Checking

- [Checks](Check.md)
- [Diagnostics](View.md)
- [Lints](Lint.md)
  - [Meaning](Lint/Meaning.md)
  - [Unused](Lint/Unused.md)
  - [Nonstandard style](Lint/NonstandardStyle.md)
  - [Style](Lint/Style.md)
    - [Pattern tests and chained comparisons](Lint/Style/Comparisons.md)
    - [Records](Lint/Style/Records.md)
    - [Natural numbers](Lint/Style/Naturals.md)
    - [Matches](Lint/Style/Matches.md)
    - [Local definitions and quantifiers](Lint/Style/Let.md)
  - [Complexity](Lint/Complexity.md)
    - [Comparisons](Lint/Complexity/Comparisons.md)
    - [Operators](Lint/Complexity/Operators.md)
    - [Methods](Lint/Complexity/Methods.md)
    - [Matches](Lint/Complexity/Matches.md)
    - [Record updates](Lint/Complexity/Updates.md)
    - [Integers](Lint/Complexity/Integers.md)
    - [Patterns](Lint/Complexity/Patterns.md)
  - [Suspicious](Lint/Suspicious.md)
    - [Expressions](Lint/Suspicious/Expressions.md)
    - [Methods and indexes](Lint/Suspicious/Methods.md)
    - [Literals](Lint/Suspicious/Literals.md)
    - [Comparisons](Lint/Suspicious/Comparisons.md)
    - [Integers](Lint/Suspicious/Integers.md)
  - [Pedantic](Lint/Pedantic.md)
    - [Matches](Lint/Pedantic/Matches.md)
    - [Records and functions](Lint/Pedantic/Records.md)
    - [Source text](Lint/Pedantic/Text.md)
    - [Comparisons](Lint/Pedantic/Comparisons.md)
    - [Conditionals](Lint/Pedantic/Conditionals.md)
  - [Restriction](Lint/Restriction.md)
  - [Decidability](Lint/Decidability.md)

# Using Fren

- [Lean embedding](Lean.md)
  - [Generated Lean declarations](Generated.md)
  - [Implementations](Impl.md)
- [Markdown specs](Markdown.md)
- [The `fren` command](Cli.md)
  - [Formatting](Fmt.md)
  - [Evaluation and testing](Eval.md)
  - [Mutation testing](Mutate.md)
- [Traceability](Trace.md)

# Appendices

- [Grammar](Grammar.md)
- [Glossary](Glossary.md)

# Contributing to Fren

- [Overview](dev/Overview.md)
- [Architecture](dev/Architecture.md)
- [Testing](dev/Testing.md)
- [Roadmap](dev/Roadmap.md)
