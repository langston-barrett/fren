# Complexity

The lints of the `complexity` group find a simpler expression with the
same meaning, and `fren fix` fixes each of them but `constant_output` and
[`needless_update`](Complexity/Updates.md#needless-updates).
This chapter has the lints of `Bool` expressions, of membership, of
outputs, of records and newtypes, of literals and of quantifiers, and its subchapters the others: those of
[comparisons](Complexity/Comparisons.md), of [operators](Complexity/Operators.md),
of [methods](Complexity/Methods.md), of [matches](Complexity/Matches.md),
of [integers](Complexity/Integers.md) and of [record updates](Complexity/Updates.md).

## Simpler `Bool` expressions

`nonminimal_bool` reports a `Bool` expression that has a simpler form with
the same meaning, in any constraint, binding, constant or global
expectation:

| Written | Simpler form |
|---|---|
| `A = true`, `A != false`, `A iff true` | `A` |
| `A = false`, `A != true`, `A iff false` | `not A` |
| `not not A` | `A` |
| `not (A = B)`, and so on for every comparison | `A != B`, the complement of the comparison, simplified again if it compares with a literal |
| `if C then true else false` | `C` |
| `if C then false else true` | `not C` |
| `if C then A else false` | `C and A` |
| `if C then true else B` | `C or B` |
| `if C then false else B` | `not C and B` |
| `if C then A else true` | `not C or A` |
| `when true, D`, `unless false, D` | `D` |

A literal may be on either side of `=`, `!=` and `iff`; when both sides are
literals, the right one is taken as the literal. The rules are tried in the
order of the table, so `if C then true else false` is `C`, not `C and
true`. The rules for `if` keep the guards (see
[Expressions](../Lang/Expressions.md#sequences)): in `if C then A else B`, `A`
is guarded by `C` and `B` by `not C`, as they are in `C and A`, `C or B`,
`not C and B` and `not C or A`. So do the rules for `when` and `unless`,
since `D` is guarded by `true` in both. `when false, D` and `unless true,
D` are always `true`, but the [vacuity](../Check.md#vacuity) and
[redundancy](../Check.md#redundancy) checks report them, so they are not
rewritten. A [pattern test](../Lang/Expressions.md#pattern-tests) is not
looked inside but for its scrutinee, and keeps its parentheses where a
comparison would need them, so `ok? = if s is A(_) then true else false`
becomes `ok? = (s is A(_))`. So does a [chained
comparison](../Lang/Expressions.md#chained-comparisons): no rule rewrites
the chain itself or its comparisons, only the expressions in its operands.
`lint::literal_comparison` gives the simpler form of a comparison with a
literal:

```fren
pub mod lint

pub comp literal_comparison {
    in equal?            -- the operator is `=` or `iff`, rather than `!=`
    in literal?          -- the literal is `true`
    pub det out negated?  -- the simpler form is `not A`, rather than `A`

    ensure rule: negated? iff (equal? != literal?)

    expect equal_true: when equal? and literal?, not negated?
    expect unequal_true: when not equal? and literal?, negated?
}
```

`lint::complement` gives the complement of a
[comparison](Style.md#empty-collections), the one that holds exactly when it does
not:

```fren
pub comp complement {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}
    in op: Comparison
    pub det out result: Comparison

    ensure rule: result = match op { Eq => Ne, Ne => Eq, Lt => Ge, Ge => Lt, Gt => Le, Le => Gt }

    expect changes: result != op
}

expect complement_involutive: forall (p q: complement), when q.op = p.result, q.result = p.op
```

The message is reported at the expression, and suggests the simpler form,
in which the operands are simplified too: the suggestion for `not not (a? =
true)` is `a?`. An operand keeps the text it is written with, and it and
the simpler form itself are put in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes). So `x? and not not (a? or b?)` becomes `x? and
(a? or b?)`, and `not (x = 1)` becomes `x != 1`.

The simpler form means what the expression means. Whatever values its
paths, numbers and function applications have, if the expression has a
value, the simpler form has the same one. This is proved in Lean, over a
model of expressions that follows the [operators](../Lang/Expressions.md#operators):
the rules above decide what the simpler form is, as an expression rather
than as text, and the proof covers every expression, every rule, and the
simplification of the operands. In the model, as in a spec that
elaborates, the branches of an `if` have the same type, so that in `if C
then A else false`, `A` is a `Bool`. The proof does not cover the text:
that the simpler form, written with its parentheses, parses as the
expression the rules chose.

`lint::nonminimal_bool_keeps_meaning` states the rules as laws (see
[Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.nonminimal_bool "expect" in
pub comp nonminimal_bool_keeps_meaning {
    in a?
    in c?
    in x: Int
    in y: Int

    expect true_literals: ((a? = true) iff a?) and ((a? != false) iff a?) and ((a? iff true) iff a?)
    expect false_literals: ((a? = false) iff not a?) and ((a? != true) iff not a?) and ((a? iff false) iff not a?)
    expect literals_left: ((true = a?) iff a?) and ((true iff a?) iff a?) and ((false = a?) iff not a?)
        and ((true != a?) iff not a?) and ((false != a?) iff a?) and ((false iff a?) iff not a?)
    expect double_negation: (not not a?) iff a?
    expect negated_literal: ((not (a? = true)) iff not a?) and ((not (a? = false)) iff a?)
        and ((not (a? != true)) iff a?) and ((not (a? != false)) iff not a?)
    expect complements: ((not (x = y)) iff x != y) and ((not (x != y)) iff x = y)
        and ((not (x < y)) iff x >= y) and ((not (x <= y)) iff x > y)
        and ((not (x > y)) iff x <= y) and ((not (x >= y)) iff x < y)
    expect conditionals: ((if c? then true else false) iff c?) and ((if c? then false else true) iff not c?)
    expect conditional_operands: ((if c? then a? else false) iff (c? and a?))
        and ((if c? then true else a?) iff (c? or a?))
        and ((if c? then false else a?) iff (not c? and a?))
        and ((if c? then a? else true) iff (not c? or a?))
}
```

The lints of cardinality operators model their operands by
`lint::Operand`, of four: two operands are the same exactly when they are
[written the same](../Lint.md#written-the-same), and four are enough to
tell every case of their rules apart.

```fren
pub enum Operand { P, Q, R, S }
```

`nonminimal_bool` also fires on a [cardinality
operator](../Lang/Expressions.md#cardinality) of one argument:
`exactly_one?(A)` is `A`, and `at_most_one?(A)` is always `true`, which is
its fix. The fix of `exactly_one?(A)` keeps `A`'s text, in parentheses
where fixes need them, and evaluates it where the call did; that of
`at_most_one?(A)` evaluates nothing, so both keep the guards. These are
not in the model proved in Lean, and the refinements below check them
instead. `lint::nonminimal_cardinality` models the call by the values of
its arguments, and states what the fix is, and that it has the call's
value:

```fren
pub enum CardinalityFix { Unchanged, Argument, True }

-- Its expectation applies a cardinality operator to one argument.
set_option fren.lint.nonminimal_bool "allow" in
pub comp nonminimal_cardinality {
    use self::CardinalityFix::{Argument, True, Unchanged}
    in exactly?          -- `exactly_one?`, rather than `at_most_one?`
    in args: Seq(Bool)   -- the values of the arguments, in order
    pub det out fix: CardinalityFix

    ensure rule: fix = (if args.len != 1 then Unchanged else if exactly? then Argument else True)

    expect keeps_meaning: when fix != Unchanged,
        (if exactly? then exactly_one?(args[0]) else at_most_one?(args[0])) = (if fix = Argument then args[0] else true)
}

set_option fren.lint.nonminimal_bool "allow" in
pub comp nonminimal_cardinality_written {
    in a?
    in x: Int
    pub det out exactly? := exactly_one?(a?)
    pub det out at_most? := at_most_one?(x > 0)
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub comp nonminimal_cardinality_fixed {
    in a?
    in x: Int
    pub det out exactly? := a?
    pub det out at_most? := true
}

refine nonminimal_cardinality_sound: nonminimal_cardinality_fixed refines nonminimal_cardinality_written
refine nonminimal_cardinality_complete: nonminimal_cardinality_written refines nonminimal_cardinality_fixed
```

## Conditionals of `Bool`s

`needless_bool_assign` fires on `if C then X else not X` and on `if C
then not X else X`, where the two `X` are [written the
same](Suspicious/Expressions.md), in any constraint, binding,
definition, constant or global expectation, and is fixable. The first
holds exactly when `C` and `X` agree, which is `C iff X`, and the second
exactly when they differ, which is `C != X`, the exclusive or of two
`Bool`s, rather than `not (C iff X)`, whose two operators always need
parentheses. The fix puts `C`, `X` and itself in parentheses as for the
[comparisons](Complexity/Comparisons.md): `p? iff if a? then b? else not b?` becomes
`p? iff (a? iff b?)`. It keeps the guards (see
[Expressions](../Lang/Expressions.md#sequences)): `X` is guarded by `C` in
one branch and by `not C` in the other, so it is defined wherever the
conditional is, whichever `C` is, and `iff` and `!=` guard neither
operand, which both front ends evaluate under the guard of the operator.
`lint::needless_bool_assign` states when the lint fires, and
`lint::needless_bool_assign_meaning` checks both fixes:

```fren
pub comp needless_bool_assign {
    in else_negates?     -- the `else` branch is `not X`, for an `X` written the same as the `then` branch
    in then_negates?     -- the `then` branch is `not X`, for an `X` written the same as the `else` branch
    pub det out fires?
    pub det out unequal?  -- the fix is `C != X`, rather than `C iff X`

    ensure rule: fires? iff (else_negates? or then_negates?)
    ensure fix: unequal? iff not else_negates?
}

set_option fren.lint.needless_bool_assign "allow" in
comp needless_bool_assign_meaning {
    in c?
    in x?

    expect agree: (if c? then x? else not x?) iff (c? iff x?)
    expect differ: (if c? then not x? else x?) iff c? != x?
}
```

## Singleton membership

`singleton_membership` fires on `x in {a}`, which is `x = a`, and is
fixable. `lint::singleton_membership_keeps_meaning` states the fix as a law
(see [Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.singleton_membership "expect" in
pub comp singleton_membership_keeps_meaning {
    in x: Int
    in y: Int

    expect singleton: (x in {y}) iff x = y
}
```

## Constant outputs

`constant_output` fires on a [defined output](../Lang/Components.md#defined-outputs)
whose definition mentions no variable and no uninterpreted function (see
[Mentions](../Lang/Expressions.md#mentions)): it is the same in every behaviour,
so it is a constant. Its counterpart in the `pedantic` group,
[`definable_output`](Pedantic.md#definable-outputs), fires on an output
that is not defined but could be. `lint::output_lints` states both:

```fren
pub comp output_lints {
    in defined?              -- the output is defined
    in mentions?             -- its definition mentions a variable or an uninterpreted function, if defined
    in n_guarantees: Nat     -- guarantees that mention it, if not defined
    in equation?             -- the only one is `x = e` or `x? iff e`, with `e` not mentioning `x`
    pub det out constant?    -- `constant_output` fires
    pub det out definable?   -- `definable_output` fires

    ensure constant: constant? iff (defined? and not mentions?)
    ensure definable: definable? iff (not defined? and n_guarantees = 1 and equation?)

    expect exclusive: not (constant? and definable?)
}
```

## Copied records

`unnecessary_struct_initialization` fires on a record literal `S { x :=
r.x, y := r.y }` whose every field reads that field of one `r`, written
the same each time, where `r` is a value whose type is `S` itself: the
literal is then `r`. It does not fire where `r` is of another record with
the same fields, as `Pair { x := p.x, y := p.y }` for a `Point` `p`,
which converts one to the other, nor where `r` is an instance, as `Point
{ x := w.x, y := w.y }`, since an instance is not a value. A field without
`:=`, as `x` in `S { x, y := r.y }`, reads the variable `x`. The fix
replaces the literal with `r` as written: `r` is the receiver of a field
read, so it needs no parentheses wherever the literal could be. A record is
its fields, so the value is the same, and so are the
[guards](../Lang/Expressions.md#sequences): a field read is defined
wherever its receiver is, and `r` takes the literal's place.
`lint::unnecessary_struct_initialization` states when it fires:

```fren
pub comp unnecessary_struct_initialization {
    in n_fields: Nat     -- the fields of the literal
    in reads_own?        -- each field's value reads that field of some `r`, as `r.x` for `x`
    in same?             -- `r` is written the same in each
    in value?            -- `r` is a value, rather than an instance
    in same_type?        -- `r`'s type is the record
    pub det out fires?

    ensure rule: fires? iff (n_fields > 0 and reads_own? and same? and value? and same_type?)
}
```

The refinements below check the fix: a component that computes the
literal as written, one that computes the fix, and a
[refinement](../Lang/Refinement.md) each way, so that the solver checks
that they agree on every input. An operand of the rewrite is a variable,
standing for any expression of its type: Fren's expressions are pure, so a
rewrite that holds for every value of its operands holds for every
expression.

```fren
struct Point { x: Int, y: Int }

set_option fren.lint.unnecessary_struct_initialization "allow" in
pub comp struct_initialization_written {
    in p: Point
    pub det out v: Point := Point { x := p.x, y := p.y }
}

pub comp struct_initialization_fixed {
    in p: Point
    pub det out v: Point := p
}

refine struct_initialization_sound: struct_initialization_fixed refines struct_initialization_written
refine struct_initialization_complete: struct_initialization_written refines struct_initialization_fixed
```

## Newtypes

`redundant_newtype_roundtrip` fires on a [newtype](../Lang/Items.md#newtypes)
built from the field of a value of the same newtype, `Ms(x.0)`, which is
`x`, and on the field of a newtype just built, `Ms(n).0`, which is `n`, and
is fixable: the fix is `x` or `n`, with its text, in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes). The receiver may be in
parentheses, as in `(Ms(n)).0`. There is no fix where `n` takes its type
from the newtype, as `[]` and `{}` do ([Checking and
synthesis](../Lang/Types.md#checking-and-synthesis)): with `struct
Qs(Seq(Int))`, `Qs([]).0.len` would become `[].len`, which is an error,
so the message says why and suggests nothing. `Ms(x.0).0` is reported
once, at `Ms(x.0)`, whose fix leaves `x.0`. It does not fire where the newtypes
differ, as in `Ms(b.0)` for `b: Bytes`, which converts a `Bytes` to an
`Ms` on purpose, nor where the value is changed on the way, as in `Ms(x.0
+ 1)`. A newtype is [erased](../Lang/Expressions.md#newtypes) to its
underlying type, so the fix has the same value, and it evaluates the same
expression where the original did, so it keeps the guards. This is
Clippy's `useless_conversion`, in `complexity`, which fires on a
conversion of a value to its own type, such as `x.into()` for `x: T` where
a `T` is wanted. `lint::redundant_newtype_roundtrip` models the
expression by its shape, the newtypes it builds and reads, and what is
inside, and states whether it fires, and whether with a fix:

```fren
pub enum Newtype { Ms, Bytes }

-- The value a newtype is built from: the field of a value of a newtype,
-- `x.0`, or another expression, which has a type of its own, or takes one
-- from where it is written, as `[]` and `{}` do.
pub enum Inner { FieldOf(Newtype), Typed, Untyped }

-- `T(e)`, or `T(e).0`.
pub enum Roundtrip { Built(Newtype, Inner), Read(Newtype, Inner) }

pub enum RoundtripFix { Unchanged, Reported, Fixed }  -- `Reported` is reported without a fix

pub comp redundant_newtype_roundtrip {
    use self::Inner::{FieldOf, Typed, Untyped}
    use self::Roundtrip::{Built, Read}
    use self::RoundtripFix::{Fixed, Reported, Unchanged}
    in shape: Roundtrip
    pub det out fix: RoundtripFix

    ensure rule: fix = match shape {
        Built(t, FieldOf(u)) => if t = u then Fixed else Unchanged,
        Built(_, _) => Unchanged,
        -- `T(x.0).0` is reported once, at `T(x.0)`.
        Read(t, FieldOf(u)) => if t = u then Unchanged else Fixed,
        Read(_, Untyped) => Reported,
        Read(_, Typed) => Fixed,
    }
}
```

The refinements check both fixes:

```fren
pub struct Ms(Int)

set_option fren.lint.redundant_newtype_roundtrip "allow" in
pub comp roundtrip_written {
    in x: Ms
    in n: Int
    pub det out built: Ms := Ms(x.0)
    pub det out read: Int := Ms(n).0
    pub det out read_parenthesized: Int := (Ms(n + 1)).0 * 2
}

pub comp roundtrip_fixed {
    in x: Ms
    in n: Int
    pub det out built: Ms := x
    pub det out read: Int := n
    pub det out read_parenthesized: Int := (n + 1) * 2
}

refine roundtrip_sound: roundtrip_fixed refines roundtrip_written
refine roundtrip_complete: roundtrip_written refines roundtrip_fixed
```

The round trip is the identity on the newtype's values, which is why each
fix keeps the meaning:

```fren
set_option fren.lint.redundant_newtype_roundtrip "allow" in
comp roundtrip_keeps_meaning {
    in x: Ms
    in n: Int

    expect built: Ms(x.0) = x
    expect read: Ms(n).0 = n
}
```

## Leading zeros

`zero_prefixed_literal` fires on a decimal integer literal that starts
with `0` and has another digit, such as `010` or `00_1`, in an expression
or a pattern, but not on `0`, nor on a literal with a base, such as
`0x10`. Such a literal is decimal
(see [Lexical structure](../Lang/Lexical.md)), so `010` is 10, but in C and
the languages that follow it, a leading `0` makes a literal octal, and a
reader used to them reads 8. Like Clippy's `zero_prefixed_literal`, it is
in `complexity`, and it is fixable. The message gives the literal's value,
and the octal literal of the same digits where those are octal and their
values differ, from 8 on: `` `010` is 10; for octal write `0o10` ``, but
`` `07` is 7 ``. The fix drops the leading `0`s and the `_`s among them,
and leaves `0` where no other digit is left: `010` becomes `10`, `00_1`
becomes `1`, `01_000` becomes `1_000`, and `00` becomes `0`. A literal is
replaced by a literal, which needs no parentheses and has no guard, so the
fix keeps every guard. `lint::zero_prefixed_literal` states when it fires,
and whether `fixed` is what the fix writes, after what it drops, `zeros`.
A `slice` at a position that is not a constant, and `ends_with?` of a
string that is not one, are outside the [decidable
core](../Lang/Decidability.md#strings), so it opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub comp zero_prefixed_literal {
    in lexeme: String    -- an integer literal
    in fixed: String

    assume literal: lexeme.matches?(r"[0-9]([0-9_]*[0-9])?|0[xXbBoO][0-9a-fA-F_]*[0-9a-fA-F]")
    out zeros: String := lexeme.slice(0, lexeme.len - fixed.len)
    pub det out fires?
    pub det out is_fix?  -- the fix of `lexeme` writes `fixed`

    ensure rule: fires? iff lexeme.matches?(r"0[0-9][0-9_]*")
    ensure fix: is_fix? iff (fires? and lexeme.ends_with?(fixed) and zeros.matches?(r"[0_]*")
        and (fixed = "0" or fixed.matches?(r"[1-9][0-9_]*")))

    expect based: when lexeme = "0x10", not fires?
    expect zero: when lexeme = "0", not fires?
    expect separated: when lexeme = "00_1", is_fix? iff fixed = "1"
}
```

The [refinements](../Lang/Refinement.md) below check the fix and the
value the message gives, for each literal above: a component that
compares an input with the literal as written, one that compares it with
the fix, and a refinement each way, so that the solver checks that the
two agree for every value of the input.

```fren
set_option fren.lint.zero_prefixed_literal "allow" in
pub comp zero_prefixed_written {
    in x: Int
    pub det out ten? := x = 010
    pub det out one? := x = 00_1
    pub det out thousand? := x = 01_000
    pub det out zero? := x = 00
}

pub comp zero_prefixed_fixed {
    in x: Int
    pub det out ten? := x = 10
    pub det out one? := x = 1
    pub det out thousand? := x = 1_000
    pub det out zero? := x = 0
}

refine zero_prefixed_sound: zero_prefixed_fixed refines zero_prefixed_written
refine zero_prefixed_complete: zero_prefixed_written refines zero_prefixed_fixed
```

## Trivial quantifiers

`trivial_quantifier` fires on a [quantifier](../Lang/Quantifiers.md), or a
global expectation's leading `forall`, with a bound name whose type has
one value, as an enumeration with one variant without a payload has, or a
record whose fields each have one: its expansion has one instance for
each value of the other bound names, so the bound name could be its value
instead. The message is at the binder of the first such name. It is
fixable where every bound name's type is an enumeration with one variant
without a payload, `T::V`, and the quantifier is not a global
expectation's, whose binders over components stay: the fix writes the
body, with `T::V`, `T` as the binder writes it, in place of each mention
of a bound name, so `forall (u: Solo), u in s` becomes `Solo::Only in s`.
That is the quantifier's one instance, so the fix keeps the meaning, and
its guards, which are the quantifier's own. A path binds as tightly as
any expression, and the body binds at least as tightly as the quantifier,
so neither needs parentheses. A mention is a path of one segment that
means the bound name, and not what an inner binder of that name hides.
There is no fix where the body declares a bound name again, as in
`forall (u: Solo), (forall (u!: Solo), u in t) and u in t` or `exists
(u: Solo), let u! := u in u in t`: without the quantifier, that `u!`
would hide nothing ([Shadowing](../Lang/Components.md#shadowing)), which
is an error.
`fren fix` leaves a quantifier with a comment in it, which the fix could
lose.

Clippy's `single_element_loop`, a loop over one element, is in
`complexity`, and so `warn`, and so is this; a quantifier over a type of
no values cannot be written, since every type has one
([Meaning](../Lang/Quantifiers.md#meaning)), so Clippy's `never_loop` has
no counterpart.

`lint::trivial_quantifier` states when it fires, and when it is fixed, on
the quantifier in the [model of scopes](Unused.md#scopes): its bound
names, those whose types have one value, those whose types are an
enumeration of one variant without a payload, and its body's tree, in
which it finds the names declared again:

```fren
pub comp trivial_quantifier {
    use lint::{Local, Tree, scope}
    in names: Set(Local)           -- the bound names
    in one_value: Set(Local)       -- those whose types have one value
    in variant: Set(Local)         -- those whose types are an enumeration of one variant without a payload
    in global?                     -- a global expectation's leading `forall`
    in body: Tree
    pub det out fires?
    pub det out fixed?

    inst s: scope { t := body }

    ensure rule: fires? iff (one_value inter names) != {}
    ensure fix: fixed? iff (names != {} and names subset one_value and names subset variant and not global? and (names inter s.declared) = {})

    -- `forall (u: Solo), (forall (u!: Solo), u in t) and u in t`.
    expect inner_bang: when names = {Local::A} and one_value = names and variant = names
        and body.declares = {(body.root, Local::A)}, fires? and not fixed?
    expect fixed_fires: when fixed?, fires?
}
```

The refinements check the fixes, of a `forall` and of an `exists` of one
bound name, of two bound names, and of one mentioned twice:

```fren
pub enum Solo { Only }

set_option fren.lint.trivial_quantifier "allow" in
pub comp trivial_quantifier_written {
    in s: Set(Solo)
    in t: Set(Solo)
    pub det out every? := forall (u: Solo), u in s
    pub det out some? := exists (u: Solo), u in s and u in t
    pub det out pair? := forall (u v: Solo), u in s or v in t
}

pub comp trivial_quantifier_fixed {
    in s: Set(Solo)
    in t: Set(Solo)
    pub det out every? := Solo::Only in s
    pub det out some? := Solo::Only in s and Solo::Only in t
    pub det out pair? := Solo::Only in s or Solo::Only in t
}

refine trivial_quantifier_sound: trivial_quantifier_fixed refines trivial_quantifier_written
refine trivial_quantifier_complete: trivial_quantifier_written refines trivial_quantifier_fixed
```
