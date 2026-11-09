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
needed to express a Language law in Fren in the separate development
coverage document.

The [FLS chapter structure](https://rust-lang.github.io/fls/general.html#subchapter-segments)
separates syntax, legality, dynamic semantics and examples. Define shared
semantic objects and environments before judgments, as in sections 4.1–4.3
and 4.10 of [The Definition of Standard ML (Revised)](https://smlfamily.github.io/sml97-defn.pdf).
A judgment's premises must derive its children's facts in their exact
contexts; side conditions cannot be replaced by a caller's success Boolean.
State which relation is specified, which decision procedure implements it,
and which correspondence is proved. Put implementation status and unproved
law inventories in [development coverage](../../../docs/fren2-specification-coverage.md).
