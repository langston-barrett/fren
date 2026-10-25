# Types

Fren has eight kinds of type:

- `Bool`, with the values `true` and `false`.
- `Int`, the mathematical integers. Values are unbounded and arithmetic
  never overflows.
- `Nat`, the natural numbers: the integers that are at least 0 (see
  [Natural numbers](#natural-numbers)).
- `String`, finite sequences of characters (see [Strings](#strings)).
- `Set(T)`, finite sets of values of `T` (see [Sets](#sets)).
- Enumerations, declared with `enum` (see [Items](Items.md#enumerations)).
  Each value of an enumeration is one of its variants, together with the
  values of the variant's payload, if it has one. An enumeration declared
  `ordered` orders its variants as they are declared.
- Records, declared with `struct` (see [Items](Items.md#records)). Each
  value of a record has a value for each of the record's fields. A
  [newtype](Items.md#newtypes), such as `struct Ms(Int)`, is a record with
  one field, which has no name: it has the values of that field's type, its
  underlying type, but is a type of its own.
- Abstract types, declared with `type` (see [Items](Items.md#abstract-types)).
  Their values are not described by the spec (see [Abstract
  types](#abstract-types)).

```
type := "Bool" | "Int" | "Nat" | "String" | "Set" "(" type ")" | "Seq" "(" type ")"
      | "Rel" "(" type "," type ")" | path
```

A type written as a path must name an enumeration, a record or an abstract
type. `Bool`, `Int`, `Nat`, `String` and `Set` are built in and cannot be
redeclared, nor can the built-in functions `exactly_one?` and
`at_most_one?` (see [Functions](Items.md#functions)).

Every expression has exactly one type, and the only conversion between
types is *widening*: a `Nat` is accepted where an `Int` is expected (see
[Natural numbers](#natural-numbers)). Comparing values of other different
types, such as an `Int` with an enumeration, is an error. Which operators apply to which types is given in
[Expressions](Expressions.md). Two values of an enumeration or a record
are equal if they are built alike: the same variant with equal payloads,
or equal values for every field.

`lang::ValueType` classifies types, for the rules of this chapter. Each
variant ends in `Ty`, which [`enum_variant_names`](../Lint/Style.md#names)
would remove, since a variant cannot be named after a built-in type such as
`Bool`:

```fren
pub mod lang

set_option fren.lint.enum_variant_names "allow" in
pub enum ValueType { BoolTy, IntTy, NatTy, StringTy, EnumTy, RecordTy, AbstractTy, SetTy, RelTy, SeqTy }
```

`lang::Ty` is the types themselves, `lang::kind` gives the kind of
each, `lang::elem` the element type of a set type, `lang::left` and
`lang::right` the types of a relation's pairs, and `lang::ordered_enum?`
whether a type is an [ordered enumeration](Items.md#enumerations). Two
enumerations, two records, two abstract types, two set types or two
relation types may have the same kind and still be different types:

```fren
pub type Ty

pub fn kind(Ty): ValueType
pub fn elem(Ty): Ty      -- the element type of a set or a sequence
pub fn left(Ty): Ty      -- the type of the first element of a relation's pairs
pub fn right(Ty): Ty     -- the type of the second
pub fn ordered_enum?(Ty)  -- an enumeration declared `ordered`
```

`lang::newtype?` says whether a type is a [newtype](Items.md#newtypes),
whose kind is `RecordTy`, and `lang::under` gives a newtype's underlying
type:

```fren
pub fn newtype?(Ty)
pub fn under(Ty): Ty     -- the underlying type of a newtype
```

## Recursive and unbounded types

An enumeration is *recursive* if the payload of one of its variants has
the enumeration's own type, as in `enum List { Nil, Cons(Int, List) }`.
A type is *unbounded* if its values can be arbitrarily large: it is
`String`, a set, relation or sequence type, a recursive enumeration, or an enumeration or
record with a payload or field of an unbounded type, such as a newtype
whose underlying type is unbounded. `Bool`, `Int`, `Nat` and abstract types are
not unbounded: an `Int` is arbitrarily large, but it is one value.

Values of an unbounded type are built from finitely many variants, so
every recursive enumeration has a variant whose payload does not have its
own type (see [Items](Items.md#enumerations)). An output may not have an
unbounded type (see [Components](Components.md#members)), so that the
[realizability check](../Check.md#realizability), the only check that asks
whether outputs exist, never asks for an unbounded value.

## Natural numbers

A `Nat` is a natural number: an integer that is at least 0. Every `Nat`
is an `Int`, so a `Nat` is accepted wherever an `Int` is expected, as an
argument, a binding, a definition or an operand: it is *widened* to an
`Int`. An `Int` is never accepted where a `Nat` is expected, even where it
happens to be at least 0: there is no conversion that narrows. So with `in
n: Nat`, `n + 1` is a `Nat`, but `n - 1` is an `Int`, and `out m: Nat := n
- 1` is an error (see [Natural numbers](Expressions.md#natural-numbers)
for the types of the operators and literals). Arithmetic never truncates.

`lang::widening` states when an expression is accepted where a type is
expected, from the expression's type and the expected type:

```fren
pub comp widening {
    use self::ValueType::{IntTy, NatTy}
    in found: Ty         -- the expression's type
    in expected: Ty      -- the type its place expects
    pub det out accepted?

    req rule: accepted? iff (found = expected or (kind(found) = NatTy and kind(expected) = IntTy))

    expect same_type: when found = expected, accepted?
    expect never_narrows: when kind(found) = IntTy and kind(expected) = NatTy, not accepted?
    expect only_numbers: when accepted? and found != expected, kind(found) = NatTy
}
```

This is the rule wherever a type is declared: an argument of a function
application, a value of a variant's payload, a field of a record literal
or of a record update, a binding of an instance or of a refinement, a
defined output's definition, a constant's value, and a defined function's
body. An assumption, requirement, expectation or cover goal, and a global
expectation, is declared a `Bool`. An expression that is not accepted is
reported at the expression (`F0304`), with its type, the declared one, and
a note that says where the type is declared, as in "`x` of `sub` has type
`Int`". Both front ends check with the same function, so they report the
same error at the same expression.

A variable of type `Nat` brings the constraint that it is at least 0 (see
[Components](Components.md#natural-numbers)), and so does each application
of an uninterpreted function whose result is a `Nat` (see
[Items](Items.md#uninterpreted-functions)). In Lean, a `Nat` is Lean's
`Nat`, and widening is Lean's coercion `↑` to `Int`.

For now, `Nat` is the type of a variable, a function's parameter or
result, a constant, or a [`let` or `where`](Let.md) definition, which is
substituted, and nothing else: it is not the type of a field or
a payload, nor the element type of a set, relation or sequence, where an
`Int` and a constraint serve instead. So a `Nat` is never inside another
value, and the constraints that it brings are always on a variable or an
application. `Nat` written anywhere else is an error (`F0338`).
`lang::nat_place` states where `Nat` may be written:

```fren
pub enum TypePlace { Variable, Parameter, Result, Constant, Definition, Field, Payload, Element }

pub comp nat_place {
    use self::TypePlace::{Element, Field, Payload}
    in place: TypePlace      -- where the type `Nat` is written
    pub det out accepted?

    req rule: accepted? iff not place in {Field, Payload, Element}

    expect variables: when place = TypePlace::Variable, accepted?
    expect definitions: when place = TypePlace::Definition, accepted?
    expect not_in_collections: when place = Element, not accepted?
}
```

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
    in code: Nat         -- the code point of a character of a literal
    pub det out accepted?

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
element types are finite. `Int`, `Nat`, `String` and abstract types are not
finite, and neither is any sequence type. Where a type is built from others, its *parts* are the types of
its fields, payloads and elements, and a type is built from everything
that the closure of the parts relation reaches from it. `lang::finite`
and `lang::unbounded` state the two notions by that reachability:

```fren
set_option fren.lint.undecidable "allow" in
pub comp finite {
    in ty: Ty
    in parts: Rel(Ty, Ty)    -- (t, u): t has a field, payload or element of type u
    in infinite: Set(Ty)     -- `Int`, `Nat`, `String`, every sequence type and every abstract type
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
pub enum Annot { Missing, BoolTy, IntTy, NatTy, StringTy, NamedTy }

use self::Annot::{BoolTy, IntTy, Missing, NamedTy, NatTy, StringTy}

pub comp bool_naming {
    in name: String      -- the declared name
    in annot: Annot      -- `Missing` when there is no `: type`
    pub out accepted?

    assume identifier: name.matches?(r"[A-Za-z_][A-Za-z0-9_']*\??")

    req q_is_bool: when name.ends_with?("?"), accepted? iff (annot = Missing or annot = BoolTy)
    req bool_is_q: unless name.ends_with?("?"),
        accepted? iff (annot = IntTy or annot = NatTy or annot = StringTy or annot = NamedTy)

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
  of an instance or of a refinement, a field of a record literal or of a
  record update, the value of a [newtype](Items.md#newtypes), as in
  `Ms(e)`, an argument of a function application, a variant's payload,
  an argument of a sequence's method, a defined output's definition, a
  constant's value, and a definition of a [`let` or `where`](Let.md)
  whose type is written.
- **Shared.** Its type follows from that of the expression it is a part
  of, and from that of the expression's other such parts. It is checked if
  that expression is, or if one of those parts synthesizes its type. These
  are the operands of `union`, `inter`, `minus` and `++`, the branches of a
  conditional, the bodies of a `match`'s arms, the elements of a set or
  sequence literal, an expression in parentheses, and the body of a
  `let`, each of which is the only such part. The members of a pair are also shared, but give each other
  nothing: each is checked if the pair is, as in `{(1, {}), (2, s)}`.
- **Compared.** Its type follows from the other operand's: it is the same,
  or, for the right of `in`, a set or sequence of it, as it is written. It
  is checked if the other synthesizes its type. These are the operands of
  `=`, `!=` and `subset`, and the right of `in`.
- **Synthesized.** Anywhere else, as the left of `in`, an operand of
  `join`, an argument of a method of anything but a sequence, as in
  `r.image({})`, a receiver, the scrutinee of a `match` or of `e is P`,
  the sequence that is indexed, the updated value of a record update, and
  a definition of a `let` or `where` whose type is not written, it
  synthesizes its type.

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
    in synthesizing: Nat     -- how many of them synthesize their types
    pub det out synthesizes?

    assume counted: synthesizing <= parts
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

A checked expression is checked against the type expected of it. That is
its declared type, or, for a shared or compared part, the type of the part
it shares its type with, if that one synthesizes it, and otherwise the
whole's. So in `if c? then {} else t`, `{}` takes `t`'s type first, and
`s = match m { E::W => {}, E::V(t) => t }` checks each arm in order
against `s`'s. A `match` with no type expected of it checks each arm
against the arms before it. An arm that does not synthesize its type, before
any arm has one, waits for a later arm that does, and then has the type it
is checked against. A member of a set or sequence literal is expected to
have the literal's element type, or that of the first member that
synthesizes one. The right of `in` is expected to be a set of the left's
type, or a sequence of it if it is written as one, or a relation of a
pair's members' types. A `Nat` is widened to an `Int` in all of these, unless
a `Nat` is expected of the whole.

`{}` and `[]` have no type but this one. `{}` takes a set or relation type,
and `[]` a sequence type. With no type expected of it, or one that is not
a collection, its type cannot be known (`F0324`). A collection of the other
kind, as in `t = []` where `t` is a set, is a type mismatch (`F0304`).
`lang::empty_literal` states this, from which literal it is and what is
expected of it:

```fren
-- What is expected of an empty literal: no type, one that is no
-- collection, a set or relation, or a sequence.
pub enum Expected { NoType, NotCollection, SetOrRelation, Sequence }
-- Its outcome: it has the expected type, its type cannot be known, or it is
-- a collection of the other kind.
pub enum EmptyOutcome { Typed, Unknown, OtherKind }

pub comp empty_literal {
    use self::EmptyOutcome::{OtherKind, Typed, Unknown}
    use self::Expected::{NoType, NotCollection, Sequence, SetOrRelation}
    in seq?                  -- it is `[]`, not `{}`
    in expected: Expected
    pub det out outcome: EmptyOutcome

    req rule: outcome = match expected {
        NoType => Unknown,
        NotCollection => Unknown,
        SetOrRelation => if seq? then OtherKind else Typed,
        Sequence => if seq? then Typed else OtherKind,
    }

    expect needs_a_type: when expected = NoType, outcome != Typed
    cover typed_set: not seq? and outcome = Typed
    cover typed_seq: seq? and outcome = Typed
}
```
