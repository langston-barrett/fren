# Patterns

A *pattern* is written in a [`match` arm](Expressions.md#matches) and in a
[pattern test](Expressions.md#pattern-tests), and matches some values of
one type: that of the `match`'s scrutinee, or of a value of a variant's
payload.

```
pattern      := ["|"] or-pattern
or-pattern   := primary ("|" primary)*
primary      := "_" | DECL | literal | range
              | path ["(" or-pattern ("," or-pattern)* ")"]
literal      := ["-"] INT | STRING | "true" | "false"
range        := bound "..=" bound | bound ".." [bound] | "..=" bound
bound        := ["-"] INT | path
```

The `..=` and `..` of a range are written without spaces around them, as
in `0..=9`, `-5..0` and `..=MAX`, as the `.` of a field read is (`F0128`).
An upper bound is part of a range only when it touches the `..`: in `n is
0.. and ok?`, the range is `0..`, and so it is in `n is 1.. ensure r: ...`,
where the next member follows on the same line.

## Kinds of pattern

- `_` matches any value.
- A *binder*, an identifier, matches any value, and names it within the
  arm's guard and body, or, in a pattern test, in what follows the test
  where it holds (see [Binding names](Expressions.md#binding-names)). A
  binder is not a variable: see [Matches](Expressions.md#matches) for what
  it may shadow and mention.
- A *literal* matches the value it denotes: `0`, `-1` and `0x10` match an
  `Int` or a `Nat`, `"a"` a `String`, and `true` and `false` a `Bool`.
- A *range* matches the integers between its bounds: `a..=b` those from `a`
  to `b`, `a..b` those from `a` to `b - 1`, `a..` those from `a`, and `..=b`
  those up to `b`. It matches an `Int` or a `Nat`. Each bound is an integer
  literal, possibly negated, or a [constant](Items.md#constants) of type
  `Int` or `Nat` (`F0350`) whose value is an [integer constant
  expression](Expressions.md#division-and-remainder) (`F0351`), so that it
  is known when the spec is read. A range that matches
  no integer, such as `5..=3` or `3..3`, is an error (`F0349`).
- `E::V(p, q)` matches the variant `V` of the enumeration `E` whose payload's
  values `p` and `q` match, so patterns nest to any depth, as in
  `Reply::Ok(Shape::Circle(_))`. A variant with a payload has a pattern for
  each of its values, and one without a payload has none, as in
  `Shape::Empty` (see [Variants with
  payloads](Expressions.md#variants-with-payloads)).
- `A | B`, an *or-pattern*, matches what any of its *alternatives* `A` and
  `B` matches, the first of them first. Its alternatives bind no names
  (`F0333`), at any depth: when another alternative matches, the name would
  have no value. Or-patterns nest too, as in `E::V(A | B, _)`.

A pattern of each kind matches values of one type, and a pattern of
another type than the value it matches is an error (`F0348`), but `_` and
binders match a value of any type. A variant of another enumeration than
the value's is `F0319`.

Each part of a pattern is read as a variant, a literal or a binder from what
it is: a path of more than one segment, or one that is applied, names a
variant. An identifier of one segment, not applied, is the literal `true`
or `false`, a variant if it resolves to one among the items and imports in
scope (scopes 4 and 5 of [Scopes](Scope.md#scopes)), as `V` does after
`use E::*`, and a binder otherwise. The names that the constructs around
the pattern declare, and the component's variables, are not looked up, so
a binder or a variable named like a variant does not stop the identifier
naming the variant. A binder that shadows a name in scope is
written with `!` (see [Shadowing](Components.md#shadowing)), and an
identifier with `!` is always a binder, even if, without it, it would name
a variant; `true!` and `false!` are binders too, which, as declarations of
`true` and `false`, are errors. So `MAX` in a pattern, where `MAX` is a constant, is an error
unless written `MAX!`: it would be a binder, not a comparison with the
constant. `lang::pattern_name` states this, with an instance of
[`lang::scope`](Scope.md#resolution) over the items and imports in scope:

```fren
pub mod lang

-- What an identifier of one segment, not applied, is in a pattern.
pub enum PatternName { BoolLiteral, Variant, Binder }

-- It instantiates `lang::scope`, which quantifies over bindings.
set_option fren.lint.undecidable "allow" in
pub comp pattern_name {
    in items: Set<Binding>   -- the items and imports in scope where it is written
    in name: Id              -- the identifier, without its `!`
    in bang?                 -- it ends in `!`

    pub det out bool_word? := name in {"true", "false"}
    -- Without the `!`, it resolves to a variant in scope.
    pub det out variant? := match found.result {
        Lookup::Found(k) => names_variant?(k),
        _ => false,
    }
    pub det out reading: PatternName

    inst found: scope { bindings := items, name }

    ensure rule: reading = if bool_word? and not bang? then PatternName::BoolLiteral
        else if variant? and not bang? then PatternName::Variant else PatternName::Binder

    expect explicit_shadowing: when bang?, reading = PatternName::Binder
    expect unresolved: when not bool_word? and not variant?, reading = PatternName::Binder
    expect literals: when name in {"true", "false"} and not bang?, reading = PatternName::BoolLiteral
    expect no_items: when items = {} and not bool_word?, reading = PatternName::Binder
    -- A constant is no variant: without `!`, it is read as a binder.
    expect constant: when found.result = Lookup::Found(BindingKind::Constant) and not bool_word?,
        reading = PatternName::Binder
    expect imported: when found.result = Lookup::Found(BindingKind::Variant) and not bool_word? and not bang?,
        reading = PatternName::Variant
    expect function: when found.result = Lookup::Found(BindingKind::Function) and not bool_word?,
        reading = PatternName::Binder
    expect opened: when found.result = Lookup::Found(BindingKind::Opened) and not bool_word? and not bang?,
        reading = PatternName::Variant
}
```

`lang::range_pattern` states which integers a range matches, and when it
matches none, from its bounds:

```fren
pub comp range_pattern {
    in has_lower?            -- it has a lower bound
    in lower: Int
    in has_upper?            -- it has an upper bound
    in upper: Int
    in inclusive?            -- its upper bound is included: written `..=` rather than `..`
    in value: Int            -- an integer it is tested against
    pub det out matches?
    pub det out empty?       -- it matches no integer

    ensure matching: matches? iff ((not has_lower? or lower <= value)
        and (not has_upper? or (if inclusive? then value <= upper else value < upper)))
    ensure empty: empty? iff (has_lower? and has_upper? and (if inclusive? then upper < lower else upper <= lower))

    expect empty_matches_nothing: when empty?, not matches?
    expect literal: when has_lower? and has_upper? and inclusive? and lower = upper, matches? iff value = lower
    expect exclusive_end: when has_upper? and not inclusive?, not (value = upper and matches?)
}
```

## Usefulness

Whether a `match` is exhaustive, and which of its arms and alternatives are
reachable, is decided by the *usefulness* of patterns, as in Maranget,
"Warnings for pattern matching" (JFP 2007). The patterns are taken in
*vectors*, one pattern for each value of a list of values of given types,
and a *matrix* is a list of vectors of the same types, its *rows*. A vector
is *useful* with respect to a matrix when some list of values matches the
vector and no row of the matrix. So an arm is reachable when its pattern,
as a vector of one pattern, is useful with respect to the patterns of the
arms before it that have no [guard](Expressions.md#matches), and a `match`
is exhaustive when `_` is not useful with respect to the patterns of all
its arms, guards ignored (see [Matches](Expressions.md#matches)). Whether
a guard holds is left to the [checks](../Check.md#reachability).

Usefulness is decided one column at a time, from the first pattern of the
vector, its *head*, and the heads of the rows. The values of a type are
built by its *constructors*: the variants of an enumeration, whose
arguments are the values of their payloads, `true` and `false`, each
integer and each string, which have no arguments. A literal pattern is the
constructor it denotes, and a range is the or-pattern of the integers it
matches.

- To *specialize* a matrix by a constructor `c` of arity `n`, each row whose
  head matches every value that `c` builds is kept, with the head replaced
  by `n` patterns: its arguments, or `n` wildcards for a wildcard. The other
  rows are dropped. An or-pattern at the head of a row is first split into
  one row for each alternative, in order. A vector whose head is `c`'s
  pattern is specialized the same way. `lang::specialize` states this for
  one row.
- The *default matrix* is the rows whose head is a wildcard, `_` or a
  binder, without it.
- The constructors at the heads of the rows are *complete* when they are
  all those of the type, as `lang::signature_complete` states.

Then, as `lang::usefulness` states, a vector of no patterns is useful
exactly when the matrix has no rows, and otherwise, by its head:

- a constructor `c`: when the vector specialized by `c` is useful with
  respect to the matrix specialized by `c` (for a range, by one of the
  integers it matches);
- a wildcard: when the heads of the rows are complete, if the vector
  specialized by some constructor of the type is useful with respect to the
  matrix specialized by it; and otherwise, when the rest of the vector is
  useful with respect to the default matrix;
- an or-pattern: when the vector with one of its alternatives as its head
  is useful.

```fren
-- The kinds of pattern, at the head of a vector or a row.
pub enum HeadKind { Constructor, Wildcard, Or }

pub comp usefulness {
    in columns: Nat          -- the patterns of the vector
    in rows: Nat             -- the rows of the matrix
    in head: HeadKind        -- the vector's head, if it has patterns
    in complete?             -- the heads of the rows are complete for the first column's type
    in specialized?          -- for a constructor, the vector specialized by it is useful with respect to the matrix specialized by it
    in some_specialized?     -- the same holds for the vector of wildcards and some constructor of the type
    in default?              -- the rest of the vector is useful with respect to the default matrix
    in some_alternative?     -- for an or-pattern, the vector with one of its alternatives as its head is useful
    pub det out useful?

    ensure no_columns: when columns = 0, useful? iff rows = 0
    ensure constructor: when columns > 0 and head = HeadKind::Constructor, useful? iff specialized?
    ensure wildcard: when columns > 0 and head = HeadKind::Wildcard,
        useful? iff (if complete? then some_specialized? else default?)
    ensure alternatives: when columns > 0 and head = HeadKind::Or, useful? iff some_alternative?

    expect first_row: when columns = 0 and rows = 0, useful?
    expect incomplete_wildcard: when columns > 0 and head = HeadKind::Wildcard and not complete?, useful? iff default?
}
```

`lang::specialize` states how specializing by a constructor `c` changes a
row, from the kind of its head, whether the head is `c` (the same variant
or literal, or a range that contains `c`), the arity of `c` and the number
of the head's arguments:

```fren
pub comp specialize {
    in head: HeadKind        -- the row's head
    in same?                 -- the head is the constructor
    in arity: Nat            -- the arity of the constructor
    in n_args: Nat           -- the head's arguments, for a variant
    pub det out kept?        -- the row is in the specialized matrix
    pub det out added: Nat   -- the patterns that replace the head in it

    ensure wildcard: when head = HeadKind::Wildcard, kept? and added = arity
    ensure constructor: when head = HeadKind::Constructor, (kept? iff same?) and added = (if same? then n_args else 0)
    -- An or-pattern is split into rows before.
    ensure split: when head = HeadKind::Or, not kept? and added = 0

    expect dropped: when not kept?, added = 0
}
```

The constructors of an enumeration are its variants, and those of `Bool`
are `true` and `false`. No set of strings is complete, since there are
infinitely many, and no pattern but `_` and binders matches a value of a
record, set, relation, sequence or abstract type. The integers are infinitely
many too, but ranges can cover them all, as `..=-1`, `0` and `1..` do, so
the integers at the heads of a column are complete when the heads' literals
and ranges together match every integer, or for a `Nat`, every integer that
is at least 0, as `0` and `1..` do. The implementation decides this,
and specializes by integers, on intervals: it splits the integers at the
bounds of the column's literals and ranges, so that each literal and range
is a union of intervals, and specializing by any integer of an interval
gives the same matrix. `lang::signature_complete` states when the heads of a
column are complete:

Each variant of `lang::ColumnType` ends in `Type`, which
[`enum_variant_names`](../Lint/Style.md#names) would remove, since a variant
cannot be named after a built-in type, as for `lang::ValueType`.

```fren
-- The kinds of type of a column; `IntType` is `Int` or `Nat`.
set_option fren.lint.enum_variant_names "allow" in
pub enum ColumnType { EnumType, BoolType, IntType, StringType, OtherType }

pub comp signature_complete {
    in column: ColumnType
    in n_variants: Nat       -- the variants of the enumeration
    in n_named: Nat          -- those that a head names
    in has_true?             -- a head is `true`
    in has_false?            -- a head is `false`
    in covers_integers?      -- the heads' literals and ranges together match every value: every integer, or every one at least 0 for a `Nat`
    pub det out complete?

    assume counted: n_variants > 0 and n_named <= n_variants

    ensure rule: complete? iff match column {
        ColumnType::EnumType => n_named = n_variants,
        ColumnType::BoolType => has_true? and has_false?,
        ColumnType::IntType => covers_integers?,
        ColumnType::StringType | ColumnType::OtherType => false,
    }

    expect strings_never: when column = ColumnType::StringType, not complete?
    expect every_variant: when column = ColumnType::EnumType and complete?, n_named = n_variants
}
```

An or-pattern's alternative is reachable when some case of its arm that
takes it is useful: an arm's pattern stands for the or-free patterns that
choosing one alternative of each of its or-patterns gives, in order, and
each is tested for usefulness with respect to the patterns of the arms
before it that have no guard and the cases of its own arm before it. An alternative that no
useful case takes never matches (`F0318`). Since these cases are
tested one by one, and or-patterns within several values of a payload
multiply them, as `V(A | B, A | B)` stands for four, a pattern may stand
for at most 256 cases (`F0368`); split a larger one into several arms, or
match the payload in the arm's body.

When a `match` is not exhaustive, its error names the values that no arm
matches, as patterns, such as `Reply::Ok(Shape::Square(_))`, `false`, or
`1..=4` for the integers from 1 to 4. They are found by the same
specialization, following each constructor that some arm names, and listing
the constructors that none names; `_` stands for any value, such as any
string.

In a [table over a scrutinee](Expressions.md#tables-over-a-scrutinee), no
arm hides another, so each case of an arm is tested with respect to the
cases of its own arm before it alone.

## Overlap

Two patterns *overlap* when some value matches both. The arms of a [table
over a scrutinee](Expressions.md#tables-over-a-scrutinee) must not overlap
unless one has a guard, and the static rules decide it from the patterns
alone, one pair at a time, from their heads, as they decide usefulness:

- an or-pattern overlaps a pattern when one of its alternatives does;
- a wildcard, `_` or a binder, overlaps a pattern that matches some value,
  as every pattern does but one that has a range that matches no value of
  its type, such as `..=-1` within a `Nat`;
- two constructors overlap when they are the same, and the patterns of
  each value of their payloads overlap, the first's with the second's. Two
  variants are the same when they are one variant, two Booleans or two
  strings when they are equal, and two literals or ranges of integers when
  some integer matches both, one at least 0 for a `Nat`.

`lang::overlap` states this for two patterns, from their heads:

```fren
pub comp overlap {
    in first: HeadKind       -- the first pattern's head
    in second: HeadKind      -- the second's
    in same?                 -- for two constructors, they are the same
    in args_overlap?         -- for two constructors, the patterns of each value of their payloads overlap
    in first_matches?        -- the first pattern matches some value
    in second_matches?       -- the second does
    in some_alternative?     -- for an or-pattern, an alternative of one overlaps the other
    pub det out overlap?

    ensure alternatives: when first = HeadKind::Or or second = HeadKind::Or, overlap? iff some_alternative?
    ensure wildcard_first: when first = HeadKind::Wildcard and second != HeadKind::Or, overlap? iff second_matches?
    ensure wildcard_second: when first = HeadKind::Constructor and second = HeadKind::Wildcard, overlap? iff first_matches?
    ensure constructors: when first = HeadKind::Constructor and second = HeadKind::Constructor,
        overlap? iff (same? and args_overlap?)

    -- Two wildcards overlap, since every type has values.
    expect wildcards: when first = HeadKind::Wildcard and second = HeadKind::Wildcard and second_matches?, overlap?
    expect different: when first = HeadKind::Constructor and second = HeadKind::Constructor and not same?, not overlap?
}
```

`lang::pattern_overlap` states what the steps decide, over the patterns
themselves, for those of one value: `_`, a range of integers (a literal
is the range of one, and `_` of an integer the range without bounds), or
a variant whose one payload value a range matches. Two patterns overlap
exactly when some value matches both: there is then such a value, the
`witness`, and wherever any value `v` matches both, they overlap. The
integers are `Nat`s or not (`nat?`), and of a `Nat`, only those at least
0 are values, so that ranges below 0 match none, as in `..=-1`, and
`..=0` and `0..` overlap only at 0. `matches?` states which values a
pattern matches:

```fren
-- The kinds of pattern of `lang::pattern_overlap`.
pub enum PatternShape { Wildcard, Integers, Variant }

-- A range of integers: its bounds, each where it has one.
pub struct IntRange { bounded_below?, low: Int, bounded_above?, high: Int }

-- A pattern: `_`, the integers of `range`, or the variant `variant` of an
-- enumeration, whose payload's one value `payload` matches.
pub struct SimplePattern { shape: PatternShape, range: IntRange, variant: Int, payload: IntRange }

-- A value: an integer, `number`, or the variant `variant` with `number`
-- as its payload's value.
pub struct SimpleValue { variant: Int, number: Int }

fn in_range?(r: IntRange, n: Int) := (not r.bounded_below? or r.low <= n) and (not r.bounded_above? or n <= r.high)

fn matches?(p: SimplePattern, v: SimpleValue) := match p.shape {
    PatternShape::Wildcard => true,
    PatternShape::Integers => in_range?(p.range, v.number),
    PatternShape::Variant => v.variant = p.variant and in_range?(p.payload, v.number),
}

pub comp pattern_overlap {
    in first: SimplePattern
    in second: SimplePattern
    in nat?                  -- the integers are `Nat`s: the value's, or its payload's
    in v: SimpleValue              -- any value
    pub out overlap?
    pub out witness: SimpleValue   -- a value that both match, where they overlap

    -- Both are patterns of one type: of integers, or of an enumeration.
    assume typed: not (first.shape = PatternShape::Integers and second.shape = PatternShape::Variant)
        and not (first.shape = PatternShape::Variant and second.shape = PatternShape::Integers)
    assume variants: first.variant >= 0 and second.variant >= 0

    ensure common: when overlap?,
        matches?(first, witness) and matches?(second, witness) and (not nat? or witness.number >= 0)
    ensure complete: when matches?(first, v) and matches?(second, v) and (not nat? or v.number >= 0), overlap?

    expect variants_apart: when first.shape = PatternShape::Variant and second.shape = PatternShape::Variant
        and first.variant != second.variant, not overlap?
    expect below_nat: when nat? and first.shape = PatternShape::Integers and first.range.bounded_above?
        and first.range.high < 0, not overlap?
    expect wildcards: when first.shape = PatternShape::Wildcard and second.shape = PatternShape::Wildcard
        and (not nat? or v.number >= 0), overlap?
}
```

The error names a value that both patterns match, as a pattern, as a
`match` that is not exhaustive names one that no arm matches: the
constructors that both name, with such a value of each value of their
payloads, an integer that both match, or `_` where both are wildcards.

## Patterns as text

The [model of meaning](Meaning.md#layers) holds a pattern as text, in the
static part `s` of a layer: of a pattern test, `Op("is", s)`, its pattern,
and of a `match`, `Op("match", s)`, its arms' patterns, joined by `;`.
Each is written as Fren writes it, with every binder written `_` and each
variant by its path, as in `Option::Some(_); Option::None`. Nothing
produces this text yet: the front ends will, once they evaluate through
the model. Its interpretation in Lean reads only `_`, `true` and `false`,
integer literals, ranges whose bounds are literals, string literals
without escapes, variants by paths of more than one segment, and
or-patterns; no arm matches where a pattern is any other text, such as a
name of one segment, which may be a constant.
