# The prelude

Fren's *prelude* is a small library, written in Fren, whose items every
spec can use without declaring or importing them, as Rust's
`std::prelude` and Lean's `Init` are. It holds two [generic
types](Generics.md):

```text
pub enum Option<T> { None, Some(T) }      -- a value, or none
pub enum Result<T, E> { Ok(T), Err(E) }   -- a value, or an error
```

So a spec can write `in x: Option<Int>`, `x = Option::Some(3)`, or
`match x { Some(n) => n, None => 0 }` without declaring `Option`. Every
item of the prelude is a name taken from every spec, so it is kept small.

## Loading

The prelude is one file, `FrenCore/Prelude.fren`, which both front ends
load before every spec: the `fren` command before the first file it is
given, and the Lean-hosted front end in `Fren.Spec`, which every spec
imports. Its items are declared in a module of their own, the prelude's,
which no path can name: a path reaches them only by
[resolution](Modules.md#resolution), so `use` cannot import them, and a
module that [shadows](Modules.md#shadowing-the-prelude) one of them
cannot name the prelude's. A message, note or witness names them as if
they were declared at the root module: `Option`, `Option::Some`.

## Names

The prelude is the outermost layer of every scope (see
[Resolution](Modules.md#resolution)), as Rust's is: its types `Option` and
`Result`, and their variants `None`, `Some`, `Ok` and `Err`, are in scope
everywhere, below the items that a module declares or imports and the
variants that it opens. So both `Option::Some(3)` and `Some(3)` are the
prelude's variant, unless the module gives `Some` another meaning.

- An import, by name or with `*`, takes precedence over the prelude
  without `!`: it is a rule of resolution, between two layers, as a
  component's imports take precedence over its module's scope.
- A declared item takes precedence too, but shadows, and is written with
  `!`: `enum Option!<T> { ... }` (see [Shadowing the
  prelude](Modules.md#shadowing-the-prelude)). Without it, the declaration
  is an error (`F0217`).
- A variable, binder or parameter named like a variant of the prelude,
  `None`, hides it, and is written `None!`, as for any variant in scope
  (see [Shadowing](Components.md#shadowing)).

## Values

`Option` and `Result` are generic enumerations like any other: their
values, patterns, type arguments and finiteness are those of [generic
types](Generics.md). `Option<T>` has one more value than `T`, so
`Option<Bool>`, with `Option::None`, `Option::Some(false)` and
`Option::Some(true)`, is finite, and a quantifier over it is expanded;
`Result<T, E>` is finite exactly when both its arguments are. A type prints as written,
`Option<Int>` and `Result<Int, Bool>`, and a value as Fren builds it,
`Option::Some(3)` and `Result::Err(true)`, in every message, note and
witness, in both front ends. Where a message names two different types
that would print alike, as a root module's `Option!<Int>` and the
prelude's `Option<Int>`, it qualifies the prelude's, as
`prelude::Option<Int>`, which no spec can write.

## Lean

The prelude's types are Lean's own, as `Int` and `Nat` are: `Option<T>` is
Lean's `Option T`, and `Result<T, E>` Lean's `Except E T`, whose parameters
are swapped, and whose constructors `Except.ok` and `Except.error` are
`Ok` and `Err` (see [Generated Lean](../Generated.md#the-preludes-types)).
Lean code that uses a spec uses Lean's types and their library.

## Meaning

Both front ends give the solver the same declarations for the prelude's
types, with the same symbols: those that lean-smt gives it for Lean's
`Option` and `Except`, a parametric datatype named after the Lean type,
its constructors after Lean's, in Lean's order, and its selectors after
their fields, or `fieldk` for a field without a name, as `Except`'s are.
An instance is the Lean type's sort applied to its arguments in the Lean
type's order, so `Result<Int, Bool>` is `(Except Bool Int)`. The `fren`
command writes these symbols as lean-smt does, without `|`s, and every
other symbol as before.

A user's type whose path is `Option` or `Except`, which the root module
may declare (`enum Option!<T>`), has the sort `|::Option|` or
`|::Except|`, its path after `::`, as an abstract type's sort is, so that
it is apart from the Lean type's. No other symbol of a user's type has a
`.`, since no Fren name does, so none is one of lean-smt's.

`lang::prelude_sort` states a user's type's sort, from its path as it
prints:

```fren
pub mod lang

set_option fren.lint.undecidable "allow" in
pub comp prelude_sort {
    in path: String
    pub det out sort: String := if path in {"Option", "Except"} then "|::" ++ path ++ "|" else "|" ++ path ++ "|"

    expect apart: not sort is "|Option|" | "|Except|"
}
```

`lang::prelude_smt` states what the `fren` command gives the solver for
the prelude's types:

```fren
-- The declarations are the same whatever the arguments are, as they should
-- be: one for every instance.
set_option fren.lint.undecidable "allow" in
set_option fren.lint.constant_output "allow" in
pub comp prelude_smt {
    in a: String                   -- the sort of the first type argument
    in b: String                   -- of the second, for `Result`
    pub det out option_sort: String := "(Option " ++ a ++ ")"
    pub det out result_sort: String := "(Except " ++ b ++ " " ++ a ++ ")"
    pub det out option_declaration: String :=
        "(declare-datatypes ((Option 1)) ((par (|α|) ((Option.none) (Option.some (Option.some.val |α|))))))\n"
    pub det out result_declaration: String :=
        "(declare-datatypes ((Except 2)) ((par (|ε| |α|) ((Except.error (Except.error.field1 |ε|)) (Except.ok (Except.ok.field1 |α|))))))\n"
}
```
