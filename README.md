# Fren

Fren is a language for **f**ormal **r**equirements **en**gineering. Fren
consists of a DSL for writing requirements, and a suite of tools for checking
properties of DSL programs such as consistency, vacuity, and determinism.

There are two ways to use Fren:

- As a standalone binary, with properties checked by an SMT solver
- As an embedded DSL in [Lean], with properties proved by [lean-smt] or by hand

[Lean]: https://lean-lang.org/
[lean-smt]: https://github.com/verse-lab/lean-smt

Fren is itself specified in Fren.

Fren can be considered a pleasant DSL and associated tooling for working with
rely/guarantee reasoning in `QF_UFDTLIA`, just as [Cryptol] can be considered [a
frontend for `QF_BV`].

[Cryptol]: https://tools.galois.com/cryptol
[a frontend for `QF_BV`]: https://www.galois.com/articles/cryptol-as-an-smt-frontend

## Example

TODO

## Why Fren?

- Automation via a decidable logic (`QF_UFDTLIA`)

## Documentation

TODO

## Comparison to other tools

- FRET
- Alloy

## TODO

- Lean API
- Test generation
- Alloy-style `run`
