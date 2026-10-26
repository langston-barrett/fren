# Introduction

Fren is a language for formal requirements engineering. A Fren spec
describes a system as *components*. Each component has inputs, chosen by its
environment, and outputs, chosen by the system. *Assumptions* say what the
environment promises, *guarantees* say what the system must do, and
*expectations* state consequences that the author believes follow from them.
Fren checks a spec with an SMT solver: that the guarantees can always be
met, that the expectations follow, that no guarantee holds only vacuously,
that components used inside other components get the inputs they assume,
that no assumption or guarantee is redundant, and that outputs declared
deterministic are determined by the inputs (see [Checks](Check.md)).

A spec can be checked in two ways:

- **In Lean.** A spec is a Lean file, checked when it is built. Components
  also become Lean definitions, so Lean code can be proved to implement them
  (see [Lean embedding](Lean.md)).
- **With the `fren` command**, a standalone executable that checks spec files
  without Lean (see [The `fren` command](Cli.md)).

Specs can also be written as Markdown documents, as this manual is (see
[Markdown specs](Markdown.md)).

## How to read this manual

[Language](Lang/Overview.md) defines the language: its syntax, types,
components, expressions, modules and instances. [Checking](Check.md)
defines what each check proves and how results are reported. *Using Fren*
covers the Lean embedding, Markdown specs and the `fren` command. The
appendices collect the [grammar](Grammar.md) and a [glossary](Glossary.md).

Grammar is written in the notation described in [Grammar](Grammar.md).
"Must" marks a rule that Fren enforces with an error.

## Requirements in this manual

This manual is also Fren's own specification. Code in `fren` blocks, such as

```
pub comp bool_naming {
  in ends_in_q?          -- the name ends in `?`
  in annot: Annot        -- whether and how the type is annotated
  pub out accepted?
  ...
}
```

is written in Fren and checked with Fren whenever Fren is built. Each such
component models one rule of the language as a decision. Its inputs describe
a situation (here: whether a variable's name ends in `?`, and what type
annotation it has), and its outputs are Fren's response (whether the
declaration is accepted). Enumerations such as `Annot` exist only to
describe these situations; they are not part of the language. The rule is
always also stated in prose, and the component makes it precise. Code blocks
not marked `fren` are illustrations and are not checked.
