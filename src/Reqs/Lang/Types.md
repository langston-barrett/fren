# Types

Fren has eight kinds of type:

- `Bool`, with the values `true` and `false`.
- `Int`, the mathematical integers. Values are unbounded and arithmetic
  never overflows.
- `Nat`, the natural numbers: the integers that are at least 0 (see
  [Natural numbers](#natural-numbers)).
- `String`, finite sequences of characters (see [Strings](#strings)).
- `Set<T>`, finite sets of values of `T` (see [Sets](#sets)).
- Enumerations, declared with `enum` (see [Items](Items.md#enumerations)).
  Each value of an enumeration is one of its variants, together with the
  values of the variant's payload, if it has one. An enumeration declared
  `ordered` orders its variants as they are declared.
- Records, declared with `struct` (see [Items](Items.md#records)). Each
  value of a record has a value for each of the record's fields. A
  [newtype](Items.md#newtypes), such as `struct Ms(Int)`, is a record with
  one field, which has no name: it has the values of that field's type, its
  underlying type, but is a type of its own. A record declared `ordered`
  orders its values by their fields, in the order declared.
- Abstract types, declared with `type` (see [Items](Items.md#abstract-types)).
  Their values are not described by the spec (see [Abstract
  types](#abstract-types)).

A [subset type](SubsetTypes.md) names the values of a base type that satisfy
its labelled invariants. Ordinary [type aliases](Items.md#type-aliases)
name existing types without adding invariants.

An enumeration or record may have type parameters, as in `enum Option<T>
{ None, Some(T) }`: it is then [generic](Generics.md), and each of its
instances, such as `Option<Int>`, is a type of its own kind.

```
type := base
base := "Bool" | "Int" | "Nat" | "String" | "Set""<" type ">" | "Seq""<" type ">"
      | "Rel""<" type "," type ">" | path ["<" type ("," type)* ">"]
```

A type written as a path must name an enumeration, a record, an abstract
type or a type alias, which stands for the type that it names, with [type
arguments](Generics.md#type-arguments) exactly when it names a generic type. `Bool`, `Int`, `Nat`, `String` and `Set` are built in and cannot be
redeclared, nor can the built-in functions `exactly_one?` and
`at_most_one?` (see [Functions](Items.md#functions)).

Every expression has exactly one type, and the only conversion between
types is *widening*: a `Nat` is accepted where an `Int` is expected (see
[Natural numbers](#natural-numbers)). A subset type needs no conversion:
it is its base type to the type checker, so a value of either is accepted
where the other is expected, with an obligation where the subset type is
(see [Subset types](#subset-types)). Comparing values of other different
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
of a relation's pairs (see [Ordered types](#ordered-types) for which are
ordered). Two enumerations, two
records, two abstract types, two set types or two relation types may have
the same kind and still be different types. The
[preconditions](Items.md#contracts) of `elem`, `left` and `right` say
which types have element types:

```fren
pub type Ty

pub fn kind(Ty): ValueType
pub fn elem(t: Ty): (r: Ty) {
    assume collection: kind(t) in {ValueType::SetTy, ValueType::SeqTy}
}
pub fn left(t: Ty): (r: Ty) {
    assume relation: kind(t) = ValueType::RelTy
}
pub fn right(t: Ty): (r: Ty) {
    assume relation: kind(t) = ValueType::RelTy
}
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
An instance of a generic enumeration whose payload has the enumeration's
type, as `List<T>` within `enum List<T> { Nil, Cons(T, List<T>) }`, is
recursive too, whatever its arguments (see [Generic
types](Generics.md#recursive-unbounded-and-finite-instances)).
A type is *unbounded* if its values can be arbitrarily large: it is
`String`, a set, relation or sequence type, a recursive enumeration, or an enumeration or
record with a payload or field of an unbounded type, such as a newtype
whose underlying type is unbounded. `Bool`, `Int`, `Nat` and abstract types are
not unbounded: an `Int` is arbitrarily large, but it is one value.

Values of an unbounded type are built from finitely many variants, so
every recursive enumeration has a variant whose payload does not have its
own type (see [Items](Items.md#enumerations)). An output may not have an
unbounded type (see [Procedures](Procedures.md#members)), so that the
[realizability check](../Check.md#realizability), the only check that asks
whether outputs exist, never asks for an unbounded value.

## Natural numbers

A `Nat` is a natural number: an integer that is at least 0. Its values
are those of the [subset type](#subset-types)
`type Nonnegative = n: Int where range: n is 0..`, and it
follows the same rules for what a variable of it brings, and for where it
may be written, but it is a type of its own, closed under `+` and `*`:
`n + 1` is a `Nat` where `n` is, while the result of an operator on an
`Nonnegative` is an `Int`, and an `Int` given where a `Nat` is expected is
an error rather than an obligation. Lean has `Nat`, and the solver has
`Int`, so it is the one subset of `Int` that both know. Every `Nat`
is an `Int`, so a `Nat` is accepted wherever an `Int` is expected, as an
argument, a binding, a definition or an operand: it is *widened* to an
`Int`. An `Int` is never accepted where a `Nat` is expected, even where it
happens to be at least 0: there is no conversion that narrows. So with the
parameter `n: Nat`, `n + 1` is a `Nat`, but `n - 1` is an `Int`, and `let
m: Nat := n - 1` is an error (see [Natural numbers](Expressions.md#natural-numbers)
for the types of the operators and literals). Arithmetic never truncates.

`lang::widening` states when an expression is accepted where a type is
expected, from the expression's type and the expected type:

```fren
pub proc widening(
    found: Ty,           -- the expression's type
    expected: Ty,        -- the type its place expects
): (det accepted?) {
    use self::ValueType::{IntTy, NatTy}

    ensure rule: accepted? iff (found = expected or (kind(found) = NatTy and kind(expected) = IntTy))

    expect same_type: when found = expected, accepted?
    expect never_narrows: when kind(found) = IntTy and kind(expected) = NatTy, not accepted?
    expect only_numbers: when accepted? and found != expected, kind(found) = NatTy
}
```

This is the rule wherever a type is declared: an argument of a function
application, a value of a variant's payload, a field of a record literal
or of a record update, an argument of a call, a binding of a refinement, a
definition of a result or `let` variable, a constant's value, and a defined function's
body. An assumption, guarantee, expectation or cover goal, and a global
expectation, is declared a `Bool`. An expression that is not accepted is
reported at the expression (`F0304`), with its type, the declared one, and
a note that says where the type is declared, as in "`x` of `sub` has type
`Int`". Both front ends check with the same function, so they report the
same error at the same expression.

A variable of type `Nat` brings the constraint that it is at least 0 (see
[Procedures](Procedures.md#natural-numbers)), and so does each application
of an uninterpreted function whose result is a `Nat` (see
[Items](Items.md#uninterpreted-functions)). In Lean, a `Nat` is Lean's
`Nat`, and widening is Lean's coercion `↑` to `Int`.

`Nat` may be written where a subset type may (see [Subset
types](#subset-types)), with two exceptions for now: it is not the
element type of a set, relation or sequence, nor the type of a payload of a
recursive enumeration, where an `Int` and a constraint serve instead. Nor
is it a [type argument](Generics.md#type-arguments), which a construction
infers widened, so that `Option<Int>` serves.
There its constraint would hold of every element, which quantifies, as
a subset type's does there, and Fren does not yet carry it there for
`Nat`, whose values Lean and the solver represent differently: the subset
type `Nonnegative` serves instead. `Nat` written there is an error (`F0338`). In a record's field or a payload of an
enumeration that is not recursive, it is Lean's `Nat` and the solver's
`Int`, with the constraint that it is at least 0, which a value of the
record or enumeration brings, as it brings a subset type's. `lang::nat_place` states where `Nat`
may be written:

```fren
pub enum TypePlace { Variable, Parameter, Result, Constant, Definition, Field, Payload, RecursivePayload, Element, Argument }

set_option fren.evidence "enumerated" in
pub proc nat_place(
    place: TypePlace,        -- where the type `Nat` is written
): (det accepted?) {
    use self::TypePlace::{Argument, Element, Field, Payload, RecursivePayload}

    ensure rule: accepted? iff not place in {RecursivePayload, Element, Argument}

    expect variables: when place = TypePlace::Variable, accepted?
    expect definitions: when place = TypePlace::Definition, accepted?
    expect fields: when place in {Field, Payload}, accepted?
    expect not_in_collections: when place = Element, not accepted?
}
```

## Subset types

[Declared subset types](SubsetTypes.md) replace the inline pattern types
`T is P` of earlier versions of Fren.
A declaration such as `type Byte = b: Int where low: b >= 0 and high:
b <= 255` names a reusable conjunction of invariants of its base type.
Only named declarations introduce restrictions. `T is P` is valid only
as the right-hand side of such a declaration, `type Byte = Int is 0..=255`,
which is shorthand for `type Byte = b: Int where pattern: b is 0..=255`
(see [The pattern shorthand](SubsetTypes.md#the-pattern-shorthand));
in every other type position it is a syntax error. Expression pattern
tests retain their syntax.
The syntax, scope, interpretation, obligations, declaration checks,
named-conjunct diagnostics and migration are specified in that chapter.

### Widening, obligations and placement

The following rules apply to every subset type, whatever its invariants.
`subset_widening` states when a value is accepted where a type is
declared, and when it has an obligation; `obligation` states what that
obligation asks, with `Matches` meaning that the value satisfies every
named invariant of the declared subset type. `subset_place` states only
whether the place where a subset type is written introduces a
quantifier; a constraint is in the core only if each of its invariants is
too (see [Decidability](Decidability.md#subset-types)).

```fren
set_option fren.evidence "enumerated" in
pub proc subset_widening(
    restricted?,             -- the declared type is a subset type, or has one as an element type
    widened?,                -- `widening` accepts the expression's type, which is never a subset type, where the declared type with its base types for its subset types is expected
): (
    det accepted?,
    det obliged?,            -- a check confirms that the value satisfies the invariants
) {
    ensure rule: accepted? iff widened?
    ensure obligation: obliged? iff (accepted? and restricted?)

    expect never_by_type: when widened?, accepted?
    expect only_subsets: unless restricted?, not obliged?
}
```

```fren
pub enum ValuePlace { Definition, Argument, Field, Payload, Construction, Let, Body, Constant, Binding }

-- Nothing; that the value satisfies the invariants of the declared subset
-- type; that each element meets its element type's obligation; or both.
pub enum Duty { Nothing, Matches, Each, MatchesAndEach }

pub proc obligation(
    place: ValuePlace,           -- where the value is given
    type_kind: ValueType,        -- the declared type's kind
    restricted?,                 -- the declared type is a subset type at the top
    element: Duty,               -- for a set, relation or sequence, its element type's obligation
): (det duty: Duty) {
    use self::ValueType::{RelTy, SeqTy, SetTy}

    ensure rule: duty = (if place = ValuePlace::Binding then Duty::Nothing
        else if restricted? and each? then Duty::MatchesAndEach
        else if restricted? then Duty::Matches
        else if each? then Duty::Each
        else Duty::Nothing)
        where each? := type_kind in {SetTy, RelTy, SeqTy} and element != Duty::Nothing

    expect by_instances: when place = ValuePlace::Binding, duty = Duty::Nothing
    expect records_built: when type_kind = ValueType::RecordTy and not restricted?, duty = Duty::Nothing
}
```

```fren
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.lint.eq_op "allow" in
set_option fren.lint.absurd_extreme_comparisons "allow" in
expect obligation_widening(
    place: lang::ValuePlace,
    type_kind: lang::ValueType,
    restricted?,
    element: lang::Duty,
) {
    use lang
    call concrete := obligation(place, type_kind, restricted?, element)
    expect rule: true
    expect obligation: ((concrete.duty) != lang::Duty::Nothing) iff ((true) and ((place) != lang::ValuePlace::Binding
        and ((restricted?) or ((type_kind) in {
            lang::ValueType::SetTy,
            lang::ValueType::RelTy,
            lang::ValueType::SeqTy,
        } and (element) != lang::Duty::Nothing))))
}
```

```fren
pub enum SubsetPlace { Top, Field, Payload, Element }

set_option fren.evidence "enumerated" in
pub proc subset_place(
    place: SubsetPlace,          -- where the subset type is written: the top of a declared type, a record's field, a variant's payload, or an element type
    recursive?,                  -- for a payload: its enumeration is recursive
): (det decidable?) {
    use self::SubsetPlace::{Element, Payload, Top}

    assume payloads_only: when recursive?, place = Payload

    ensure rule: decidable? iff not (place = Element or (place = Payload and recursive?))

    expect top_decided: when place = Top, decidable?
    expect elements_quantify: when place = Element, not decidable?
}
```

### Pattern-test invariant fragment

The rules named `pattern_*` below describe the special case in which a
subset type's invariant is one pattern test on its binder, as in `type
Byte = n: Int where range: n is 0..=255`. They name that fragment, not a
kind of type of its own: `pattern_finite` states when such a subset type
is finite, and `pattern_member`, `pattern_count` and `pattern_bounds`
state the integers that the pattern of the test matches. These
bounded-range algorithms describe recognized pattern-test invariants: an
integer subset type whose invariants are other Boolean expressions, such
as `low: b >= 0 and high: b <= 255`, is not finite by them.

```fren
set_option fren.evidence "enumerated" in
pub proc pattern_finite(
    base_finite?,            -- the base type is finite
    integers?,               -- the base type is `Int` or `Nat`
    bounded?,                -- the invariant is a pattern test, every alternative of whose pattern is a bounded range or an integer
): (det finite?) {
    assume not_both: when integers?, not base_finite?

    ensure rule: finite? iff (base_finite? or (integers? and bounded?))

    expect ranges: when integers? and bounded?, finite?
    expect unbounded_range: when integers? and not bounded?, not finite?
}
```

```fren
pub enum Bound { Open, At(Int) }

-- A range from `lo` to `hi`, both included; `Bound::Open` is no bound.
pub struct Alternative { lo: Bound, hi: Bound }

pub fn above?(b: Bound, x: Int) := match b {
    Bound::Open => true,
    Bound::At(l) => l <= x,
}

pub fn below?(b: Bound, x: Int) := match b {
    Bound::Open => true,
    Bound::At(h) => x <= h,
}
```

```fren
set_option fren.lint.undecidable "allow" in
pub proc pattern_member(
    alts: Seq<Alternative>,      -- the alternatives of the pattern test's pattern, in order
    x: Int,
    k: Int,                      -- any position among the alternatives
): (
    member?,
    witness: Int,                -- the position of an alternative that `x` is within, if it matches
) {
    ensure within: when 0 <= k < alts.len and above?(alts[k].lo, x) and below?(alts[k].hi, x), member?
    ensure witnessed: when member?,
        0 <= witness < alts.len and above?(alts[witness].lo, x) and below?(alts[witness].hi, x)

    expect no_alternatives: when alts = [], not member?
}
```

```fren
-- A bound's integer, and 0 for no bound.
pub fn bound_value(b: Bound): Int := match b {
    Bound::At(v) => v,
    Bound::Open => 0,
}

pub fn bounded?(a: Alternative) := a.lo != Bound::Open and a.hi != Bound::Open

-- How many integers a bounded alternative has.
pub fn width(a: Alternative): Int := if bounded?(a) and bound_value(a.lo) <= bound_value(a.hi) then bound_value(a.hi) - bound_value(a.lo) + 1 else 0

pub proc pattern_count(alts: Seq<Alternative>): (
    det finite?,
    count: Nat,                  -- how many integers it matches, when finitely many
) {
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

```fren
set_option fren.lint.undecidable "allow" in
pub proc pattern_bounds(
    los: Seq<Bound>,         -- the alternatives' lower bounds, in order
    his: Seq<Bound>,         -- their upper bounds, in the same order
): (
    det finite?,             -- the pattern matches finitely many integers
    det counted?,            -- how many integers it matches is counted from the bounds
) {
    ensure finite: finite? iff not (Bound::Open in los or Bound::Open in his)
    ensure counts: counted? iff finite?

    expect no_alternatives: when los = [] and his = [], finite?
    expect one_open: when Bound::Open in his, not counted?
}
```

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.lint.eq_op "allow" in
set_option fren.lint.absurd_extreme_comparisons "allow" in
expect bounds_finite(los: Seq<lang::Bound>, his: Seq<lang::Bound>) {
    use lang
    assume spec_not_both: not (false)
    call concrete := pattern_bounds(los, his)
    expect rule: (concrete.finite?) iff ((false) or ((true) and (not (lang::Bound::Open in (los) or lang::Bound::Open in (his)))))
}
```

## Ordered types

A type is *ordered* when its values can be compared with the
[orderings](Expressions.md#operators) `<`, `<=`, `>` and `>=`, in
[chains](Expressions.md#chained-comparisons) too, and have the
[methods](Expressions.md#methods) `min` and `max`. `Int`, `Nat` and
`String` are ordered, by their own orders; so is an enumeration, a record
or a newtype declared `ordered` (see [Ordered
declarations](Items.md#ordered-declarations)), whose fields' types are then
ordered too, and no other type: not `Bool`, a set, a relation, a sequence,
an abstract type, nor an enumeration, record or newtype declared without
`ordered`, even one whose fields' types are ordered. A subset type is
ordered exactly when its base type is, since it is its base type to the
type checker, and a type alias exactly when the type it names is, since
it is that type. So `ordered struct Seconds(Nat)`, `ordered struct
Status(HttpCode)` with `type HttpCode = n: Nat where range: n is 100..=599`,
and `ordered struct Timeout(Seconds)` are each
ordered, and `struct Ms(Int)` is not.

Being ordered is a property of the type, and every rule that orders
values asks it: an ordering's operands, a chain's, the receiver of `min`
and `max`, and the fields of an ordered declaration. Comparing values of
a type that is not ordered is an error (`F0352`), as is `min` or `max` of
one (`F0354`); for an enumeration, a record or a newtype, the message says
to declare it `ordered`.

`lang::TypeName` is the path of an enumeration, record or newtype, which
`lang::type_name` gives of its type, and `lang::ordered_in?` is the rule,
from a type's kind and, for an enumeration, a record or a newtype, whether
its name is among those declared `ordered`. `lang::ordered_type` states it
of a declared type, from its *base*, the type that the type checker sees:
a subset type's base type, or the type that an alias names. Whether the
type is a subset type, `restricted?`, does not change the rule, which
`subsets_by_base` says:

```fren
pub type TypeName

pub fn type_name(Ty): TypeName  -- the path of an enumeration, record or newtype

-- Whether a type of the kind `k`, named `name` if it is an enumeration, a
-- record or a newtype, is ordered.
pub fn ordered_in?(k: ValueType, name: TypeName, ordered_items: Set<TypeName>) := match k {
    ValueType::IntTy | ValueType::NatTy | ValueType::StringTy => true,
    ValueType::EnumTy | ValueType::RecordTy => name in ordered_items,
    _ => false,
}

pub proc ordered_type(
    base: Ty,                         -- the type without its invariants: a subset type's base, an alias's type
    restricted?,                      -- a subset type, directly or through an alias
    ordered_items: Set<TypeName>,     -- the enumerations, records and newtypes declared `ordered`
): (det ordered?) {
    use self::ValueType::{
        AbstractTy,
        BoolTy,
        EnumTy,
        IntTy,
        NatTy,
        RecordTy,
        RelTy,
        SeqTy,
        SetTy,
        StringTy,
    }

    ensure rule: ordered? iff ordered_in?(kind(base), type_name(base), ordered_items)

    expect numbers: when kind(base) in {IntTy, NatTy}, ordered?
    expect strings: when kind(base) = StringTy, ordered?
    expect opt_in: when kind(base) in {EnumTy, RecordTy}, ordered? iff type_name(base) in ordered_items
    expect never_unordered: when kind(base) in {BoolTy, SetTy, RelTy, SeqTy, AbstractTy}, not ordered?
    expect by_base: when restricted?, ordered? iff ordered_in?(kind(base), type_name(base), ordered_items)
}

expect subsets_by_base(
    a_base: Ty,
    a_restricted?,
    a_ordered_items: Set<TypeName>,
    b_base: Ty,
    b_restricted?,
    b_ordered_items: Set<TypeName>,
) {
    call a := ordered_type(a_base, a_restricted?, a_ordered_items)
    call b := ordered_type(b_base, b_restricted?, b_ordered_items)
    expect subsets_by_base: when a.base = b.base and a.ordered_items = b.ordered_items, a.ordered? iff b.ordered?
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

pub proc string_char(
    code: Nat,           -- the code point of a character of a literal
): (det accepted?) {
    ensure rule: accepted? iff code <= MAX_CHAR

    expect ascii: when code < 128, accepted?
}
```

## Sets

A value of `Set<T>` is a finite set of values of `T`. Two sets are equal
if they have the same members. The element type may be any type,
including another set type. Sets are written as
[literals](Expressions.md#sets), such as `{1, 2}` and `{}`, and combined
with the [operators](Expressions.md#operators) `in`, `union`, `inter`,
`minus` and `subset`. `s.card` is the number of members. There is no
complement, since the complement of a finite set of an infinite type is
not finite.

A set type is unbounded, so a set is never an output, unless it is
[defined](Procedures.md#definitions). A field or payload may not have
a set type whose element type is, or contains, an abstract type, and an
enumeration may not contain itself within a set.

## Relations

A value of `Rel<A, B>` is a finite set of pairs `(a, b)`, with `a` of type
`A` and `b` of type `B`. Two relations are equal if they have the same
pairs. A relation is not a set of any type, since there is no type of
pairs, but every operator on sets applies to relations, and the
[relational operators](Expressions.md#relations) `join`, `inverse`,
`closure`, `image`, `domain` and `range` apply only to them. Like a set
type, a relation type is unbounded, and has the same rules for fields and
payloads.

## Sequences

A value of `Seq<T>` is a finite sequence of values of `T`, indexed from
`0`. Two sequences are equal if they have the same length and equal
elements at each index. Sequences are written as
[literals](Expressions.md#sequences), such as `[1, 2]` and `[]`, joined
with `++`, indexed with `q[i]`, and examined with the
[methods](Expressions.md#methods) that strings have, such as `q.len` and
`q.starts_with?(p)`. `x in q` says that `x` is an element of `q`. A
`String` is not a sequence: there is no type of characters, so the two
share methods and operators instead.

A sequence type is unbounded, so a sequence is never an output, unless it
is [defined](Procedures.md#definitions). A field or payload may have a
sequence type, unless an abstract type occurs within it, and an
enumeration may not contain itself within a sequence.

## Finite types

A type is *finite* if it has finitely many values: `Bool`, an
enumeration that is not recursive and whose payloads have finite types, a
record or newtype whose fields have finite types, a set or relation type
whose element types are finite, and a subset type whose base type is
finite or whose invariant is a pattern test that matches finitely many
integers, as `lang::pattern_finite` says. `Int`, `Nat`, `String` and abstract types are
not finite, and neither is any sequence type. With subset types `Four`,
`Three` and `Two` of `Int`, whose invariants are the pattern tests
`0..=3`, `0..=2` and `1..=2`, respectively, `struct P { x: Four }`,
`enum Small { S(Three), T }`, `Option<Three>` and
`Pair<Bool, Two>` are finite.

These facts are of a type as it is declared, with its subset types, which
`lang::DeclaredTy` stands for: `lang::declared_kind` gives its kind, that
of its base type for a subset type, and `lang::pattern_bounded?` whether it
is a subset type whose invariant is a pattern test that matches finitely
many integers. A type's
*constituents* are the declared types of its fields, payloads and elements,
those of an instance of a generic type with its arguments for its
parameters, and a newtype's underlying type: the types that its values are
made of. They are not its [parts](Generics.md#instantiation), the types
that it is written with: with `struct Tagged<T> { n: Int }`,
`Tagged<Bool>` has the constituent `Int`, and not `Bool`. A type is *built
from* itself and every type that the closure of the constituent relation
reaches from it, as `lang::built_from` gives, and it is *recursive* when
that closure reaches it from itself, as it reaches `List` from `List`.
Every fact of this section is a fact of a type's kind, its *former*, closed
over the types it is built from: a type is finite when each of them is
finite by itself and none is recursive, and unbounded when one of them has
a growing former or is recursive.

`lang::former` gives what a former gives a type by itself, whatever its
constituents: whether a type of it is finite when its constituents are
(`finite?`), whether its values can be arbitrarily large whatever its
constituents (`growing?`), and whether it may have constituents at all
(`composite?`). A subset type has its base type's former, and is finite
by itself when its former is or a pattern-test invariant bounds it
(`own_finite?`). A
new type former is one more variant of `ValueType` and one more arm of
`former`: what is finite, unbounded or [listed](Quantifiers.md#types), and
so which [outputs](Procedures.md#members), [newtypes](Items.md#newtypes)
and [enumerations](Items.md#enumerations) are accepted, follows from it.
A [function type](HigherOrder.md#function-types) is not a `ValueType`: it
is never a value's type, only a defined function's parameter's, so no
output, newtype, enumeration or quantifier has one, and none of these facts
is asked of it:

```fren
pub type DeclaredTy

pub fn declared_kind(DeclaredTy): ValueType
pub fn pattern_bounded?(DeclaredTy)     -- a subset type whose pattern-test invariant matches finitely many integers

pub struct Former {
    finite?,
    growing?,
    composite?,
}

pub fn former(k: ValueType): Former := match k {
    ValueType::BoolTy => Former {
        finite? := true,
        growing? := false,
        composite? := false,
    },
    ValueType::IntTy => Former {
        finite? := false,
        growing? := false,
        composite? := false,
    },
    ValueType::NatTy => Former {
        finite? := false,
        growing? := false,
        composite? := false,
    },
    ValueType::StringTy => Former {
        finite? := false,
        growing? := true,
        composite? := false,
    },
    ValueType::EnumTy => Former {
        finite? := true,
        growing? := false,
        composite? := true,
    },
    ValueType::RecordTy => Former {
        finite? := true,
        growing? := false,
        composite? := true,
    },
    ValueType::AbstractTy => Former {
        finite? := false,
        growing? := false,
        composite? := false,
    },
    ValueType::SetTy => Former {
        finite? := true,
        growing? := true,
        composite? := true,
    },
    ValueType::RelTy => Former {
        finite? := true,
        growing? := true,
        composite? := true,
    },
    ValueType::SeqTy => Former {
        finite? := false,
        growing? := true,
        composite? := true,
    },
}

-- A type of the kind `k` is finite by itself: its former is, or it is an
-- integer subset type whose pattern-test invariant bounds it
-- (`lang::pattern_finite`).
pub fn own_finite?(k: ValueType, invariant_bounded?) :=
    former(k).finite? or (invariant_bounded? and k in {ValueType::IntTy, ValueType::NatTy})

-- The types that `ty` is built from, where `(t, u)` is in `constituents`
-- when `t` has a field, payload or element of type `u`.
set_option fren.lint.undecidable "allow" in
pub fn built_from(ty: DeclaredTy, constituents: Rel<DeclaredTy, DeclaredTy>): Set<DeclaredTy> :=
    constituents.closure.image({ty}) union {ty}
```

`lang::type_facts` states the three facts by that closure:

```fren
set_option fren.lint.undecidable "allow" in
pub proc type_facts(
    ty: DeclaredTy,
    constituents: Rel<DeclaredTy, DeclaredTy>,      -- (t, u): t has a field, payload or element of type u
): (det recursive?, det finite?, det unbounded?) {
    ensure recursion: recursive? iff (ty, ty) in constituents.closure
    ensure finiteness: finite? iff (forall (u: DeclaredTy), when u in built_from(ty, constituents),
        own_finite?(declared_kind(u), pattern_bounded?(u)) and not (u, u) in constituents.closure)
    ensure bounds: unbounded? iff (exists (u: DeclaredTy), u in built_from(ty, constituents)
        and (former(declared_kind(u)).growing? or (u, u) in constituents.closure))

    expect own_infinite: unless own_finite?(declared_kind(ty), pattern_bounded?(ty)), not finite?
    expect own_growing: when former(declared_kind(ty)).growing?, unbounded?
    expect recursive_unbounded: when recursive?, unbounded? and not finite?
    -- Each constituent of a finite type is finite by itself and is not recursive.
    expect finite_constituents: when finite?, (forall (u: DeclaredTy), when u in constituents.image({ty}),
        own_finite?(declared_kind(u), pattern_bounded?(u)) and not (u, u) in constituents.closure)
    -- A type of a former that has no constituents has the former's facts.
    expect leaves: when not former(declared_kind(ty)).composite? and constituents.image({ty}) = {},
        (finite? iff own_finite?(declared_kind(ty), pattern_bounded?(ty)))
        and (unbounded? iff former(declared_kind(ty)).growing?)
}
```

The graph of all types is not finite, so these are outside the [decidable
core](Decidability.md#relations) and opt out. Each fact is also one layer
over the facts of its constituents, since a type is built from itself and
from what each of them is built from. Both front ends compute the facts by
one shared function, from their declarations, by the closure of the
constituents that the declarations give, and the `impl`s of the components
that use them prove the facts it gives against this closure. Where a
declaration is missing, or the closure takes more steps than the function
allows, the facts are unknown, and both front ends take those that accept
the least: unbounded, not finite and not listed.

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
[interpretation](Procedures.md#interpretations). The checks hold for
every interpretation, and in Lean an [implementation](../Impl.md#interpretations)
fixes one.

## Boolean names

A variable's name ends in `?` if and only if its type is `Bool`. So a
`Bool` variable's type need not be written: the parameters `ready?` and
`ready?: Bool` are the same. Any other variable must have its type written,
and its name must not end in `?`. The same goes for a
[function](Items.md#functions) and its result type. The same goes for a field of a [record](Items.md#records), for a
binder of a [`match` pattern](Expressions.md#matches) and the payload it
names, and for a [quantifier's](Quantifiers.md#names) bound name and its
type. Names of modules, enumerations, records, variants,
procedures, constraints and calls never end in `?`, and the names of
[constants](Items.md#constants) are in uppercase, whatever their type.

`lang::bool_naming` decides whether a variable, field or function
declaration is accepted, from its name and its type annotation, which for
a function is that of its result. A binder of a pattern is accepted as a
declaration whose annotation is the type of its payload, so never
`Missing`:

```fren
pub enum Annot { Missing, BoolTy, IntTy, NatTy, StringTy, NamedTy }

use self::Annot::{BoolTy, IntTy, Missing, NamedTy, NatTy, StringTy}

pub proc bool_naming(
    name: String,        -- the declared name
    annot: Annot,        -- `Missing` when there is no `: type`
): (accepted?) {
    assume identifier: name.matches?(r"[A-Za-z_][A-Za-z0-9_']*\??")

    ensure q_is_bool: when name.ends_with?("?"), accepted? iff annot is Missing | BoolTy
    ensure bool_is_q: unless name.ends_with?("?"),
        accepted? iff annot is IntTy | NatTy | StringTy | NamedTy

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

- **Declared.** It is checked against a type that is declared: an
  argument of a call, a binding of a refinement, a field of a record literal or of a
  record update, the value of a [newtype](Items.md#newtypes), as in
  `Ms(e)`, an argument of a function application, a variant's payload,
  an argument of a sequence's method, the argument of an enumeration's or
  record's `min` or `max`, against the receiver's type, a defined
  output's definition, a
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
  `=`, `!=`, `subset` and the orderings, and the right of `in`. In a chain
  of orderings, as `a < b <= c`, each operand after the first is checked
  against the first's type, and the first against the type of the first
  operand that synthesizes one, as in `E::A < x`.
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

set_option fren.evidence "enumerated" in
pub proc checked(
    position: Position,
    expected?,          -- the expression it is a part of is checked against a type
    sibling?,           -- another part that shares its type synthesizes one
): (det checked?) {
    use self::Position::{Compared, Declared, Shared, Synthesized}

    ensure rule: checked? iff match position {
        Declared => true,
        Shared => expected? or sibling?,
        Compared => sibling?,
        Synthesized => false,
    }

    expect declared_always: when position = Declared, checked?
    expect synthesized_never: when position = Synthesized, not checked?
    expect sibling_suffices: when position is Shared | Compared and sibling?, checked?
}
```

An expression synthesizes its type unless it is `{}` or `[]`, or it is
made of shared parts none of which synthesizes one, as `{{}}`,
`if c? then {} else []` and `({})` are, or it is a pair, `(a, b)`, one of
whose members does not, or it is a variant or record of a generic type, one
of whose type parameters no value of its payload or fields that
synthesizes its type gives an argument, as `Option::None` (see [Type
arguments](Generics.md#type-arguments)). `lang::synthesizes` states this, from the
expression's shape and how many of its shared parts, or of a pair's two
members, synthesize their types.

```fren
-- `EmptyLiteral` is `{}` or `[]`; `SharedParts` is an expression whose type
-- is that of its shared parts; `Pair` is a pair; `Construction` is a variant
-- or record of a generic type; `Other` is any other.
pub enum Shape { EmptyLiteral, SharedParts, Pair, Construction, Other }

pub proc synthesizes(
    shape: Shape,
    parts: Int,              -- how many shared parts it has, members, for a pair, or type parameters, for a construction
    synthesizing: Nat,       -- how many of them synthesize their types, or, for a construction, are given an argument
): (det synthesizes?) {
    use self::Shape::{Construction, EmptyLiteral, Other, Pair, SharedParts}

    assume counted: synthesizing <= parts
    assume pair: when shape = Pair, parts = 2

    ensure rule: synthesizes? iff match shape {
        EmptyLiteral => false,
        SharedParts => synthesizing > 0,
        Pair => synthesizing = parts,
        Construction => synthesizing = parts,
        Other => true,
    }

    expect one_part_suffices: when shape = SharedParts and synthesizing > 0, synthesizes?
    expect pair_needs_both: when shape = Pair and synthesizing < 2, not synthesizes?
    expect construction_needs_all: when shape = Construction and synthesizing < parts, not synthesizes?
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

set_option fren.evidence "enumerated" in
pub proc empty_literal(
    seq?,                    -- it is `[]`, not `{}`
    expected: Expected,
): (det outcome: EmptyOutcome) {
    use self::EmptyOutcome::{OtherKind, Typed, Unknown}
    use self::Expected::{NoType, NotCollection, Sequence, SetOrRelation}

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
