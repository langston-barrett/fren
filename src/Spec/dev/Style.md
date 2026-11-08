# Writing the Fren 2 specification

The [reference style guide](../../Reqs/dev/Style.md) applies to both parts
of this specification. It describes the audience, rule format, checked
blocks, and section order.

For a compiler intermediate representation (IR), its chapter states the
IR's datatypes, printed form, well-formedness rules, and what its random
generator is guaranteed to produce, such as only well-formed terms. For a
compiler pass, its chapter states what the pass does and the properties it
preserves.

Compiler laws concern the actual deciding code, stated in Lean or as
uninterpreted Fren functions later bound to that code by `impl`. Do not copy
IR datatypes or executable passes into Fren. Test the real code directly
with Plausible, including ill-typed and partial inputs, and report premise
counts; `FrenProp` is a thin layer over Plausible. Prove laws in Lean where
cheap and use the generic Lean fold theorem where applicable. Independently
checked primitive Fren contracts fix facts such as lookup choices and
operator meanings. Neither roundtrips nor agreement between models replace
those facts. Properties that are not solver-decidable remain explicit Lean
proof or direct Plausible obligations; testing is not a proof and supplies
no `impl ... by plausible` or `sorry`. Record any missing language feature
needed to restate a Language law in Fren after crossover, without making it
a prerequisite for a compiler chapter.
