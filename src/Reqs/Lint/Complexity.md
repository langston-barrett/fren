# Complexity

The lints of the `complexity` group find a simpler expression with the
same meaning, and `fren fix` fixes each of them but `constant_output`.
This chapter has the lints of `Bool` expressions, of membership and of
outputs, and its subchapters the others: those of
[comparisons](Complexity/Comparisons.md), of [operators](Complexity/Operators.md),
of [methods](Complexity/Methods.md) and of [matches](Complexity/Matches.md).

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

    req rule: negated? iff (equal? != literal?)

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

    req rule: result = match op { Eq => Ne, Ne => Eq, Lt => Ge, Ge => Lt, Gt => Le, Le => Gt }

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
    expect double_negation: (not not a?) iff a?
    expect negated_literal: (not (a? = true)) iff not a?
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

    req rule: fires? iff (else_negates? or then_negates?)
    req fix: unequal? iff not else_negates?
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
    in n_reqs: Nat           -- requirements that mention it, if not defined
    in equation?             -- the only one is `x = e` or `x? iff e`, with `e` not mentioning `x`
    pub det out constant?    -- `constant_output` fires
    pub det out definable?   -- `definable_output` fires

    req constant: constant? iff (defined? and not mentions?)
    req definable: definable? iff (not defined? and n_reqs = 1 and equation?)

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
    in n_fields: Int     -- the fields of the literal
    in reads_own?        -- each field's value reads that field of some `r`, as `r.x` for `x`
    in same?             -- `r` is written the same in each
    in value?            -- `r` is a value, rather than an instance
    in same_type?        -- `r`'s type is the record
    pub det out fires?

    assume counts: n_fields >= 0

    req rule: fires? iff (n_fields > 0 and reads_own? and same? and value? and same_type?)
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
