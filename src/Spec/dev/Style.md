# Writing the Fren 2 specification

The [reference style guide](../../Reqs/dev/Style.md) applies to both parts
of this specification. It describes the audience, rule format, checked
blocks, and section order.

For a compiler intermediate representation (IR), its chapter states the
IR's datatypes, printed form, well-formedness rules, and what its random
generator is guaranteed to produce, such as only well-formed terms. For a
compiler pass, its chapter states what the pass does and the properties it
preserves.

Compiler models use the Fren constructs available today. Model a recursive
expression one layer at a time, with the recursive positions as a type
parameter. State properties that need unavailable recursion or are not
decidable in Lean and test them with Plausible. For each such property,
record a checklist item to restate it in Fren once Fren 2 supports the
specific missing feature.
