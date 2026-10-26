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

A [pattern type](#pattern-types), such as `Int is 0..=255`, has the values
of a type of one of these kinds that match a pattern, and a [type
alias](Items.md#type-aliases) names a type, so that `type Byte := Int is
0..=255` is written once.

```
type := base ["is" pattern]
base := "Bool" | "Int" | "Nat" | "String" | "Set" "(" type ")" | "Seq" "(" type ")"
      | "Rel" "(" type "," type ")" | path
```

A type written as a path must name an enumeration, a record, an abstract
type or a type alias, which stands for the type that it names. `Bool`, `Int`, `Nat`, `String` and `Set` are built in and cannot be
redeclared, nor can the built-in functions `exactly_one?` and
`at_most_one?` (see [Functions](Items.md#functions)).

Every expression has exactly one type, and the only conversion between
types is *widening*: a `Nat` is accepted where an `Int` is expected (see
[Natural numbers](#natural-numbers)), and a pattern type where its base
type is (see [Pattern types](#pattern-types)). Comparing values of other different
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
each, `lang::elem` the element type of a set or a sequence type,
`lang::left` and `lang::right` the types of the first and second elements
of a relation's pairs, and `lang::ordered_enum?` whether a type is an
[ordered enumeration](Items.md#enumerations). Two enumerations, two
records, two abstract types, two set types or two relation types may have
the same kind and still be different types. The
[preconditions](Items.md#contracts) of `elem`, `left` and `right` say
which types have element types:

```fren
pub type Ty

pub fn kind(Ty): ValueType
pub fn elem(t: Ty): Ty
    assume collection: kind(t) in {ValueType::SetTy, ValueType::SeqTy}
pub fn left(t: Ty): Ty
    assume relation: kind(t) = ValueType::RelTy
pub fn right(t: Ty): Ty
    assume relation: kind(t) = ValueType::RelTy
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

A `Nat` is a natural number: an integer that is at least 0. Its values
are those of the [pattern type](#pattern-types) `Int is 0..`, and it
follows the same rules for what a variable of it brings, and for where it
may be written, but it is a type of its own, closed under `+` and `*`:
`n + 1` is a `Nat` where `n` is, while the result of an operator on an
`Int is 0..` is an `Int`, and an `Int` given where a `Nat` is expected is
an error rather than an obligation. Lean has `Nat`, and the solver has
`Int`, so it is the one pattern type that both know. Every `Nat`
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

    ensure rule: accepted? iff (found = expected or (kind(found) = NatTy and kind(expected) = IntTy))

    expect same_type: when found = expected, accepted?
    expect never_narrows: when kind(found) = IntTy and kind(expected) = NatTy, not accepted?
    expect only_numbers: when accepted? and found != expected, kind(found) = NatTy
}
```

This is the rule wherever a type is declared: an argument of a function
application, a value of a variant's payload, a field of a record literal
or of a record update, a binding of an instance or of a refinement, a
defined output's definition, a constant's value, and a defined function's
body. An assumption, guarantee, expectation or cover goal, and a global
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

`Nat` may be written where a pattern type may (see [Pattern
types](#pattern-types)), with two exceptions for now: it is not the
element type of a set, relation or sequence, nor the type of a payload of a
recursive enumeration, where an `Int` and a constraint serve instead.
There its constraint would hold of every element, which quantifies, as
a pattern type's does there, and Fren does not yet carry it there for
`Nat`, whose values Lean and the solver represent differently: `Int is
0..` serves instead. `Nat` written there is an error (`F0338`). In a record's field or a payload of an
enumeration that is not recursive, it is Lean's `Nat` and the solver's
`Int`, with the constraint that it is at least 0, which a value of the
record or enumeration brings, as it brings a pattern type's. `lang::nat_place` states where `Nat`
may be written:

```fren
pub enum TypePlace { Variable, Parameter, Result, Constant, Definition, Field, Payload, RecursivePayload, Element }

pub comp nat_place {
    use self::TypePlace::{Element, Field, Payload, RecursivePayload}
    in place: TypePlace      -- where the type `Nat` is written
    pub det out accepted?

    ensure rule: accepted? iff not place in {RecursivePayload, Element}

    expect variables: when place = TypePlace::Variable, accepted?
    expect definitions: when place = TypePlace::Definition, accepted?
    expect fields: when place in {Field, Payload}, accepted?
    expect not_in_collections: when place = Element, not accepted?
}
```

## Pattern types

A *pattern type* `T is P` has the values of its *base type* `T` that
match the pattern `P`, after Rust's: `Int is 0..=255` has the integers from
0 to 255, `Int is 1..` the positive ones, and `Severity is Severity::Warning
| Severity::Error` two variants of an enumeration. `P` is a
[pattern](Patterns.md) of `match` and `is`, of a value of `T`, as in a
[pattern test](Expressions.md#pattern-tests), that binds no names: a
binder, which would match every value and name it, is an error (`F0370`,
which names a binder `n!` as `n`), and `_` is written instead. Pattern types are not nested: the base type is
never itself a pattern type, so `Int is 0.. is ..=9` does not parse, and a
pattern on a type alias that names a pattern type is an error (`F0369`).

A pattern type is named with a [type alias](Items.md#type-aliases), which
is not a new type: `Byte` and `Int is 0..=255` are the same type. A type
whose values are restricted and that is distinct from its base type is a
[newtype](Items.md#newtypes) of a pattern type, as `struct Byte(Int is
0..=255)`.

### Typing

The static semantics of a pattern type is its base type's: Fren never
decides from the types alone whether a value matches a pattern, which
the solver does instead. An expression's type is never a pattern type: a
variable of type `Int is 0..=9` is an `Int` where it is used, so `x + 1` is
an `Int`, and so is every result of an operator. Every value of `T is P`
is a `T`, so it is accepted wherever a `T` is expected: it is widened. A
`T` is accepted where a `T is P` is expected too, with an *obligation*: the
value must match `P`, which a [check](../Check.md#pattern-types) confirms
with the solver, where the type is declared:

- a defined output's definition, a defined function's body, a constant's
  value, a field of a record literal or of a record update, a value of a
  variant's payload, a newtype's constructor's argument, a written type of
  a [`let` or `where`](Let.md) definition, and an argument of a function
  application, each by the pattern-type check, under the hypotheses of
  where it is written, as an index's definedness is;
- a binding of an instance, by the [instance
  check](../Check.md#instance-assumptions), since the instantiated
  component assumes what its input's pattern type brings.

Two types are compared with their patterns left out, wherever they are
compared: so `Set(Int is 1..)` is accepted where a `Set(Int)` is
expected, and where a `Set(Int is 0..)` is, with the obligation that each
member matches `0..`. The obligation is asked wherever the declared type has
a pattern, at the top or in an element type, even where the value is a
variable of the same pattern type, whose constraint then proves it.
`lang::pattern_widening` states this, from whether `widening` accepts
the expression's type where the declared type without its patterns is
expected, and whether the declared type has a pattern:

```fren
pub comp pattern_widening {
    in patterned?            -- the declared type has a pattern, at the top or in an element type
    in widened?              -- `widening` accepts the expression's type, which has no pattern, where the declared type without its patterns is expected
    pub det out accepted?
    pub det out obliged?     -- a check confirms that the value matches

    ensure rule: accepted? iff widened?
    ensure obligation: obliged? iff (accepted? and patterned?)

    expect never_by_type: when widened?, accepted?
    expect only_patterns: unless patterned?, not obliged?
}
```

What an obligation asks follows the declared type: that the value matches
its pattern, if it has one, and for a set, relation or sequence, that each
element, or each member of each pair, meets the obligation of its element
type, which is that of an element type alone. A record's, newtype's or
enumeration's own fields and payloads ask nothing more: its values were
built to meet them. At an instance's binding, the value asks nothing where
it is given, since the instance check asks the same of the binding. Where
`lang::ValuePlace` is where a value is given and `lang::Duty` what an
obligation asks of it, `lang::obligation` states this:

```fren
pub enum ValuePlace { Definition, Argument, Field, Payload, Construction, Let, Body, Constant, Binding }

-- Nothing; that the value matches the pattern; that each element meets
-- its element type's obligation; or both.
pub enum Duty { Nothing, Matches, Each, MatchesAndEach }

pub comp obligation {
    use self::ValueType::{RelTy, SeqTy, SetTy}
    in place: ValuePlace         -- where the value is given
    in type_kind: ValueType      -- the declared type's kind
    in pattern?                  -- the declared type has a pattern at the top
    in element: Duty             -- for a set, relation or sequence, its element type's obligation
    pub det out duty: Duty

    ensure rule: duty = (if place = ValuePlace::Binding then Duty::Nothing
        else if pattern? and each? then Duty::MatchesAndEach
        else if pattern? then Duty::Matches
        else if each? then Duty::Each
        else Duty::Nothing)
        where each? := type_kind in {SetTy, RelTy, SeqTy} and element != Duty::Nothing

    expect by_instances: when place = ValuePlace::Binding, duty = Duty::Nothing
    expect records_built: when type_kind = ValueType::RecordTy and not pattern?, duty = Duty::Nothing
}
```

`lang::obligation` is the detailed statement of `lang::pattern_widening`:
a value has an obligation exactly where its declared type has a pattern,
at the top or in an element type, and it is not given at an instance's
binding, which the instance check asks instead:

```fren
refine obligation_widening: obligation refines pattern_widening {
    patterned? := place != ValuePlace::Binding
        and (pattern? or (type_kind in {ValueType::SetTy, ValueType::RelTy, ValueType::SeqTy} and element != Duty::Nothing)),
    widened? := true,
    accepted? := true,
    obliged? := duty != Duty::Nothing,
}
```

### Meaning

A variable, a parameter or an application of an uninterpreted function
whose type is a pattern type brings the constraint that its value
matches the pattern, as a [`Nat`](#natural-numbers) brings that it is at
least 0 (see [Components](Components.md#pattern-types)). A record whose
field, or an enumeration whose payload, has a pattern type or is a `Nat`
brings the constraints of those on its fields and payloads, and so on
within them: a variable `p` of `struct Packet { length: Byte }` brings `p.length
is 0..=255`, and one of `enum Reading { Raw(Byte), Missing }` brings that
when it is `Raw`, its payload is in range. These are quantifier-free, one
for each field or payload, since a record or an enumeration that is not
recursive has finitely many of them, however deep. They are brought where the value comes
from, a variable or an application, rather than where a field is read,
since two values can be compared without reading their fields: with `struct
Flag { on?: Bool is true }`, which has one value, `a = b` holds of any two
`Flag`s `a` and `b`, though neither reads `on?`.

Within a set's, relation's or sequence's element type, a pattern type
brings a constraint on every element, which quantifies over them, and
within a recursive enumeration's payload, a constraint on every payload of
every value that the query reads from it, since its values have payloads of
every depth. Both are allowed, but they are outside the [decidable
core](Decidability.md#pattern-types), so the [`undecidable`
lint](../Lint/Decidability.md#undecidable-constructs) reports the type
where it is written.

`lang::pattern_place` states which written pattern types are within the
decidable core, from where the type is written and whether that
enumeration is recursive:

```fren
pub enum PatternPlace { Top, Field, Payload, Element }

pub comp pattern_place {
    use self::PatternPlace::{Element, Payload, Top}
    in place: PatternPlace       -- where the pattern type is written: the top of a declared type, a record's field, a variant's payload, or an element type
    in recursive?                -- for a payload: its enumeration is recursive
    pub det out decidable?

    assume payloads_only: when recursive?, place = Payload

    ensure rule: decidable? iff not (place = Element or (place = Payload and recursive?))

    expect top_decided: when place = Top, decidable?
    expect elements_quantify: when place = Element, not decidable?
}
```

In Lean, a pattern type is its base type, and the constraints are
hypotheses of the checks, as a `Nat` function's results are (see
[Generated declarations](../Generated.md#components)). To the solver, it is
its base type, with the constraints among each query's hypotheses and the
obligations as queries of their own (see [Checks](../Check.md)), so both
front ends report the same verdicts and minimal sets.

### Bounded and finite

A pattern type is [unbounded](#recursive-and-unbounded-types) exactly when
its base type is, and [finite](#finite-types) when its base type is, or
when its base type is `Int` or `Nat` and every alternative of its pattern
is a bounded range or an integer, as `Int is 0..=7` and `Int is 1 | 3 |
5` are. So a [quantifier](Quantifiers.md) can range over `Int is 0..=7`,
and has one instance for each integer that matches, in increasing order. A
pattern type of an enumeration or a record ranges over the values of its
base type that match, in their order. `lang::pattern_finite` states this:

```fren
pub comp pattern_finite {
    in base_finite?          -- the base type is finite
    in integers?             -- the base type is `Int` or `Nat`
    in bounded?              -- every alternative of the pattern is a bounded range or an integer
    pub det out finite?

    assume not_both: when integers?, not base_finite?

    ensure rule: finite? iff (base_finite? or (integers? and bounded?))

    expect ranges: when integers? and bounded?, finite?
    expect unbounded_range: when integers? and not bounded?, not finite?
}
```

### Integer patterns

An integer pattern, of `Int` or `Nat`, is an or-pattern of *alternatives*,
each a range with or without a lower and an upper bound, or an integer
`n`, which is the range `n..=n`; `a..b` is `a..=b - 1`. `lang::Alternative`
is one, and `lang::above?` and `lang::below?` say whether an integer is
within its bounds:

```fren
pub enum Bound { Open, At(Int) }

-- A range from `lo` to `hi`, both included; `Bound::Open` is no bound.
pub struct Alternative { lo: Bound, hi: Bound }

pub fn above?(b: Bound, x: Int) := match b { Bound::Open => true, Bound::At(l) => l <= x }

pub fn below?(b: Bound, x: Int) := match b { Bound::Open => true, Bound::At(h) => x <= h }
```

An integer matches the pattern if it is within the bounds of one of its
alternatives. `lang::pattern_member` states this, with a witness: the
alternative that it is within, which every check, constraint and
obligation of a pattern type, and the evaluator, decide by. The witness is
an output that the guarantees index by, which is outside the decidable
core, so it opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub comp pattern_member {
    in alts: Seq(Alternative)    -- the pattern's alternatives, in order
    in x: Int
    in k: Int                    -- any position among the alternatives
    pub out member?
    pub out witness: Int         -- the position of an alternative that `x` is within, if it matches

    ensure within: when 0 <= k < alts.len and above?(alts[k].lo, x) and below?(alts[k].hi, x), member?
    ensure witnessed: when member?,
        0 <= witness < alts.len and above?(alts[witness].lo, x) and below?(alts[witness].hi, x)

    expect no_alternatives: when alts = [], not member?
}
```

The pattern matches finitely many integers when each alternative has both
bounds, and then how many it matches is counted from the bounds, without
listing them: an alternative from `lo` to `hi` has `hi - lo + 1` integers,
or none if `hi < lo`, and alternatives that overlap count their integers
once. `lang::pattern_count` states this for up to two alternatives, which
is how the solver and both front ends count them for any number:

```fren
-- A bound's integer, and 0 for no bound.
pub fn bound_value(b: Bound): Int := match b { Bound::At(v) => v, Bound::Open => 0 }

pub fn bounded?(a: Alternative) := a.lo != Bound::Open and a.hi != Bound::Open

-- How many integers a bounded alternative has.
pub fn width(a: Alternative): Int := if bounded?(a) and bound_value(a.lo) <= bound_value(a.hi) then bound_value(a.hi) - bound_value(a.lo) + 1 else 0

pub comp pattern_count {
    in alts: Seq(Alternative)
    pub det out finite?
    pub out count: Nat           -- how many integers it matches, when finitely many

    assume few: alts.len <= 2

    ensure bounds: finite? iff ((alts = [] or bounded?(alts[0])) and (alts.len < 2 or bounded?(alts[1])))
    ensure none: when alts = [], count = 0
    ensure one: when finite? and alts.len = 1, count = width(alts[0])
    ensure apart: when finite? and alts.len = 2 and width(alts[0]) > 0 and width(alts[1]) > 0
        and (bound_value(alts[0].hi) + 1 < bound_value(alts[1].lo) or bound_value(alts[1].hi) + 1 < bound_value(alts[0].lo)),
        count = width(alts[0]) + width(alts[1])
    -- Alternatives that overlap or touch count as their union, once.
    ensure joined: when finite? and alts.len = 2 and width(alts[0]) > 0 and width(alts[1]) > 0
        and not (bound_value(alts[0].hi) + 1 < bound_value(alts[1].lo) or bound_value(alts[1].hi) + 1 < bound_value(alts[0].lo)),
        count = bound_value(alts[0].hi).max(bound_value(alts[1].hi)) - bound_value(alts[0].lo).min(bound_value(alts[1].lo)) + 1
    ensure empty_first: when finite? and alts.len = 2 and width(alts[0]) = 0, count = width(alts[1])
    ensure empty_second: when finite? and alts.len = 2 and width(alts[1]) = 0, count = width(alts[0])
}
```

For any number of alternatives, `lang::pattern_bounds` states when they
are counted: exactly when each has both bounds, which it says of their
lower and upper bounds, each a sequence in the alternatives' order.
Membership in a sequence is outside the decidable core, so it opts out,
and so does its refinement:

```fren
set_option fren.lint.undecidable "allow" in
pub comp pattern_bounds {
    in los: Seq(Bound)       -- the alternatives' lower bounds, in order
    in his: Seq(Bound)       -- their upper bounds, in the same order
    pub det out finite?      -- the pattern matches finitely many integers
    pub det out counted?     -- how many integers it matches is counted from the bounds

    ensure finite: finite? iff not (Bound::Open in los or Bound::Open in his)
    ensure counts: counted? iff finite?

    expect no_alternatives: when los = [] and his = [], finite?
    expect one_open: when Bound::Open in his, not counted?
}
```

It refines `lang::pattern_finite` for an integer base type, whose pattern
is bounded exactly when no alternative lacks a bound:

```fren
set_option fren.lint.undecidable "allow" in
refine bounds_finite: pattern_bounds refines pattern_finite {
    base_finite? := false,
    integers? := true,
    bounded? := not (Bound::Open in los or Bound::Open in his),
    finite? := finite?,
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

    ensure rule: accepted? iff code <= MAX_CHAR

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
record whose fields have finite types, a set or relation type whose
element types are finite, and a pattern type that `lang::pattern_finite`
says is. `Int`, `Nat`, `String` and abstract types are not
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

    ensure rule: finite? iff ((parts.closure.image({ty}) union {ty}) inter (infinite union recursive)) = {}

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

    ensure rule: unbounded? iff ((parts.closure.image({ty}) union {ty}) inter growing) != {}

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
[function](Items.md#functions) and its result type. The same goes for a field of a [record](Items.md#records), for a
binder of a [`match` pattern](Expressions.md#matches) and the payload it
names, and for a [quantifier's](Quantifiers.md#names) bound name and its
type. Names of modules, enumerations, records, variants,
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

    ensure q_is_bool: when name.ends_with?("?"), accepted? iff (annot = Missing or annot = BoolTy)
    ensure bool_is_q: unless name.ends_with?("?"),
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
  conditional, the bodies of a `match`'s arms, the values of a
  [table](Expressions.md#tables)'s rows, the elements of a set or
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
  the condition of a table's row, the sequence that is indexed, the updated value of a record update, and
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

    ensure rule: checked? iff match position {
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

    ensure rule: synthesizes? iff match shape {
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

    ensure rule: outcome = match expected {
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
