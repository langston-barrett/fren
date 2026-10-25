# Types

Fren has seven kinds of type:

- `Bool`, with the values `true` and `false`.
- `Int`, the mathematical integers. Values are unbounded and arithmetic
  never overflows.
- `String`, finite sequences of characters (see [Strings](#strings)).
- `Set(T)`, finite sets of values of `T` (see [Sets](#sets)).
- Enumerations, declared with `enum` (see [Items](Items.md#enumerations)).
  Each value of an enumeration is one of its variants, together with the
  values of the variant's payload, if it has one.
- Records, declared with `struct` (see [Items](Items.md#records)). Each
  value of a record has a value for each of the record's fields.
- Abstract types, declared with `type` (see [Items](Items.md#abstract-types)).
  Their values are not described by the spec (see [Abstract
  types](#abstract-types)).

```
type := "Bool" | "Int" | "String" | "Set" "(" type ")" | path
```

A type written as a path must name an enumeration, a record or an abstract
type. `Bool`, `Int`, `String` and `Set` are built in and cannot be
redeclared.

Every expression has exactly one type, and there are no conversions between
types. Comparing values of different types, such as an `Int` with an
enumeration, is an error. Which operators apply to which types is given in
[Expressions](Expressions.md). Two values of an enumeration or a record
are equal if they are built alike: the same variant with equal payloads,
or equal values for every field.

`lang::ValueType` classifies types, for the rules of this chapter:

```fren
pub mod lang

pub enum ValueType { BoolTy, IntTy, StringTy, EnumTy, RecordTy, AbstractTy, SetTy, RelTy, SeqTy }
```

`lang::Ty` is the types themselves, `lang::kind` gives the kind of
each, `lang::elem` the element type of a set type, and `lang::left` and
`lang::right` the types of a relation's pairs. Two enumerations, two
records, two abstract types, two set types or two relation types may have
the same kind and still be different types:

```fren
pub type Ty

pub fn kind(Ty): ValueType
pub fn elem(Ty): Ty      -- the element type of a set or a sequence
pub fn left(Ty): Ty      -- the type of the first element of a relation's pairs
pub fn right(Ty): Ty     -- the type of the second
```

## Recursive and unbounded types

An enumeration is *recursive* if the payload of one of its variants has
the enumeration's own type, as in `enum List { Nil, Cons(Int, List) }`.
A type is *unbounded* if its values can be arbitrarily large: it is
`String`, a set, relation or sequence type, a recursive enumeration, or an enumeration or
record with a payload or field of an unbounded type. `Bool`, `Int` and abstract types are
not unbounded: an `Int` is arbitrarily large, but it is one value.

Values of an unbounded type are built from finitely many variants, so
every recursive enumeration has a variant whose payload does not have its
own type (see [Items](Items.md#enumerations)). An output may not have an
unbounded type (see [Components](Components.md#members)), so that the
[realizability check](../Check.md#realizability), the only check that asks
whether outputs exist, never asks for an unbounded value.

## Strings

A `String` is a finite sequence of characters. Two strings are equal if
they have the same characters in the same order, and `<` orders them
lexicographically, by the characters' code points. Strings are written as
[literals](Lexical.md#literals), joined with `++`, and examined with
[methods](Expressions.md#methods), such as `s.len` and
`s.starts_with?("x")`.

A character is a code point from `0` to `U+2FFFF`, as in the solver's
theory of strings, so a literal may contain only those. In Lean, a
`String` may contain any Unicode scalar value, up to `U+10FFFF`: an
[implementation](../Impl.md) is proved for every Lean string. A check
could tell the two alphabets apart only with a spec that needs more than
196,608 distinct characters. `lang::string_char` states which characters
a literal may contain:

```fren
-- U+2FFFF, the last character of the solver's strings.
pub const MAX_CHAR: Int := 196607

pub comp string_char {
    in code: Int         -- the code point of a character of a literal
    pub det out accepted?

    assume scalar: code >= 0

    req rule: accepted? iff code <= MAX_CHAR

    expect ascii: when code < 128, accepted?
}
```

## Sets

A value of `Set(T)` is a finite set of values of `T`. Two sets are equal
if they have the same members. The element type may be any type,
including another set type. Sets are written as
[literals](Expressions.md#sets), such as `{1, 2}` and `{}`, and combined
with the [operators](Expressions.md#operators) `in`, `union`, `inter`,
`minus` and `subset`. `s.card` is the number of members. There is no
complement, since the complement of a finite set of an infinite type is
not finite.

A set type is unbounded, so a set is never an output, unless it is
[defined](Components.md#defined-outputs). A field or payload may not have
a set type whose element type is, or contains, an abstract type, and an
enumeration may not contain itself within a set.

## Relations

A value of `Rel(A, B)` is a finite set of pairs `(a, b)`, with `a` of type
`A` and `b` of type `B`. Two relations are equal if they have the same
pairs. A relation is not a set of any type, since there is no type of
pairs, but every operator on sets applies to relations, and the
[relational operators](Expressions.md#relations) `join`, `inverse`,
`closure`, `image`, `domain` and `range` apply only to them. Like a set
type, a relation type is unbounded, and has the same rules for fields and
payloads.

## Sequences

A value of `Seq(T)` is a finite sequence of values of `T`, indexed from
`0`. Two sequences are equal if they have the same length and equal
elements at each index. Sequences are written as
[literals](Expressions.md#sequences), such as `[1, 2]` and `[]`, joined
with `++`, indexed with `q[i]`, and examined with the
[methods](Expressions.md#methods) that strings have, such as `q.len` and
`q.starts_with?(p)`. `x in q` says that `x` is an element of `q`. A
`String` is not a sequence: there is no type of characters, so the two
share methods and operators instead.

A sequence type is unbounded, so a sequence is never an output, unless it
is [defined](Components.md#defined-outputs). A field or payload may have a
sequence type, unless an abstract type occurs within it, and an
enumeration may not contain itself within a sequence.

## Finite types

A type is *finite* if it has finitely many values: `Bool`, an
enumeration that is not recursive and whose payloads have finite types, a
record whose fields have finite types, and a set or relation type whose
element types are finite. `Int`, `String` and abstract types are not
finite, and neither is any sequence type. Where a type is built from others, its *parts* are the types of
its fields, payloads and elements, and a type is built from everything
that the closure of the parts relation reaches from it. `lang::finite`
and `lang::unbounded` state the two notions by that reachability:

```fren
set_option fren.lint.undecidable "allow" in
pub comp finite {
    in ty: Ty
    in parts: Rel(Ty, Ty)    -- (t, u): t has a field, payload or element of type u
    in infinite: Set(Ty)     -- `Int`, `String`, every sequence type and every abstract type
    in recursive: Set(Ty)    -- the recursive enumerations
    in part: Ty              -- any type, for `finite_parts`
    pub det out finite?

    req rule: finite? iff ((parts.closure.image({ty}) union {ty}) inter (infinite union recursive)) = {}

    expect not_infinite: when finite?, not ty in infinite
    -- A type that a finite type is built from is not infinite.
    expect finite_parts: when finite? and (ty, part) in parts, not part in infinite and not part in recursive
}

set_option fren.lint.undecidable "allow" in
pub comp unbounded {
    in ty: Ty
    in parts: Rel(Ty, Ty)
    in growing: Set(Ty)      -- `String`, every recursive enumeration, and every set, relation or sequence type
    pub det out unbounded?

    req rule: unbounded? iff ((parts.closure.image({ty}) union {ty}) inter growing) != {}

    expect growing_unbounded: when ty in growing, unbounded?
}
```

Both are about reachability over the graph of all types, which is not
finite, so they are outside the [decidable core](Decidability.md#relations)
and opt out.

## Abstract types

An abstract type stands for values that the spec does not describe, such as
the names in a program or the users of a system. All that is known of them
is that there is at least one, and whether two of them are equal. So the
only operators that apply to an abstract type are `=` and `!=`, and a
conditional's branches may have one (see
[Expressions](Expressions.md#types-of-operators)). There are no literals of
an abstract type: its values are those of variables and of [function
applications](Expressions.md#function-applications). Each abstract type is
distinct from every other type, including other abstract types. No field
of a record, nor payload of a variant, has an abstract type (see
[Items](Items.md#records)).

What the values of an abstract type are is given by an
[interpretation](Components.md#interpretations). The checks hold for
every interpretation, and in Lean an [implementation](../Impl.md#interpretations)
fixes one.

## Boolean names

A variable's name ends in `?` if and only if its type is `Bool`. So a
`Bool` variable's type need not be written: `in ready?` and `in ready?:
Bool` declare the same input. Any other variable must have its type written,
and its name must not end in `?`. The same goes for a
[function](Items.md#functions) and its result type. The same goes for a field of a [record](Items.md#records), and for a
binder of a [`match` pattern](Expressions.md#matches) and the payload it
names. Names of modules, enumerations, records, variants,
components, constraints and instances never end in `?`, and the names of
[constants](Items.md#constants) are in uppercase, whatever their type.

`lang::bool_naming` decides whether a variable, field or function
declaration is accepted, from its name and its type annotation, which for
a function is that of its result. A binder of a pattern is accepted as a
declaration whose annotation is the type of its payload, so never
`Missing`:

```fren
pub enum Annot { Missing, BoolTy, IntTy, StringTy, NamedTy }

use self::Annot::{BoolTy, IntTy, Missing, NamedTy, StringTy}

pub comp bool_naming {
    in name: String      -- the declared name
    in annot: Annot      -- `Missing` when there is no `: type`
    pub out accepted?

    assume identifier: name.matches?(r"[A-Za-z_][A-Za-z0-9_']*\??")

    req q_is_bool: when name.ends_with?("?"), accepted? iff (annot = Missing or annot = BoolTy)
    req bool_is_q: unless name.ends_with?("?"), accepted? iff (annot = IntTy or annot = StringTy or annot = NamedTy)

    expect bool_needs_q: when annot = BoolTy and accepted?, name.ends_with?("?")
    expect untyped_needs_q: when annot = Missing and accepted?, name.ends_with?("?")
    expect not_only_q: name != "?"
}
```

## Checking and synthesis

Every expression has a type. Most *synthesize* theirs from their parts,
as `x + 1` is an `Int` because `x` is. Some, where they are written, are
*checked* against a type that is given to them instead. `{}` and `[]` have
no part to give them a type, so they can only be checked, and are an error
wherever an expression must synthesize its type.

Where an expression is written decides whether it is checked:

- **Declared.** It is checked against a type that is declared: a binding
  of an instance or of a refinement, a field of a record literal, an
  argument of a function application, a variant's payload, an argument of
  a sequence's method, a defined output's definition, and a constant's
  value.
- **Shared.** Its type follows from that of the expression it is a part
  of, and from that of the expression's other such parts. It is checked if
  that expression is, or if one of those parts synthesizes its type. These
  are the operands of `union`, `inter`, `minus` and `++`, the branches of a
  conditional, the bodies of a `match`'s arms, the elements of a set or
  sequence literal, and an expression in parentheses, which is the only
  such part. The members of a pair are also shared, but give each other
  nothing: each is checked if the pair is, as in `{(1, {}), (2, s)}`.
- **Compared.** Its type follows from the other operand's: it is the same,
  or, for the right of `in`, a set or sequence of it, as it is written. It
  is checked if the other synthesizes its type. These are the operands of
  `=`, `!=` and `subset`, and the right of `in`.
- **Synthesized.** Anywhere else, as the left of `in`, an operand of
  `join`, an argument of a method of anything but a sequence, as in
  `r.image({})`, a receiver, a scrutinee and the sequence that is indexed,
  it synthesizes its type.

`lang::checked` states this, from where an expression is written, whether
the expression it is a part of is checked, and whether one of the parts
that share its type synthesizes one. So `s = {} union {}`,
`s = (if c? then {} else {})`, `x in []`, `{{}, s}`, `[[], q]`,
`{(1, {}), (2, s)}` and a `match` with an arm `E::W => {}` beside an arm
of a known type are all accepted, and `{} = {}`, `({} inter {}).card`,
`{} in z`, `r join {}`, `r.image({})`, `{{}}.card` and `s = [{}][0]` are
not.

```fren
pub enum Position { Declared, Shared, Compared, Synthesized }

pub comp checked {
    use self::Position::{Compared, Declared, Shared, Synthesized}
    in position: Position
    in expected?        -- the expression it is a part of is checked against a type
    in sibling?         -- another part that shares its type synthesizes one
    pub det out checked?

    req rule: checked? iff match position {
        Declared => true,
        Shared => expected? or sibling?,
        Compared => sibling?,
        Synthesized => false,
    }

    expect declared_always: when position = Declared, checked?
    expect synthesized_never: when position = Synthesized, not checked?
    expect sibling_suffices: when (position = Shared or position = Compared) and sibling?, checked?
}
```

An expression synthesizes its type unless it is `{}` or `[]`, or it is
made of shared parts none of which synthesizes one, as `{{}}`,
`if c? then {} else []` and `({})` are, or it is a pair, `(a, b)`, one of
whose members does not. `lang::synthesizes` states this, from the
expression's shape and how many of its shared parts, or of a pair's two
members, synthesize their types.

```fren
-- `EmptyLiteral` is `{}` or `[]`; `SharedParts` is an expression whose type
-- is that of its shared parts; `Pair` is a pair; `Other` is any other.
pub enum Shape { EmptyLiteral, SharedParts, Pair, Other }

pub comp synthesizes {
    use self::Shape::{EmptyLiteral, Other, Pair, SharedParts}
    in shape: Shape
    in parts: Int            -- how many shared parts it has, or members, for a pair
    in synthesizing: Int     -- how many of them synthesize their types
    pub det out synthesizes?

    assume counted: 0 <= synthesizing and synthesizing <= parts
    assume pair: when shape = Pair, parts = 2

    req rule: synthesizes? iff match shape {
        EmptyLiteral => false,
        SharedParts => synthesizing > 0,
        Pair => synthesizing = parts,
        Other => true,
    }

    expect one_part_suffices: when shape = SharedParts and synthesizing > 0, synthesizes?
    expect pair_needs_both: when shape = Pair and synthesizing < 2, not synthesizes?
}
```
