# Expressions

These lints fire on expressions that are legal but probably not what the
writer meant. Two operands are compared as [written the
same](../../Lint.md#written-the-same), where the parentheses around an operand
are not part of it, so the operands of `f(x) = f(x)` are written the same,
and those of `x = (x)`, but not those of `x + 1 = 1 + x`.

## Operands written the same

`eq_op` fires on an infix operator whose two operands are written the
same, where the expression is then always the same value, or the same as
its operand: `x = x`, `x <= x`, `x >= x`, `a? iff a?` and `s subset s`
are always `true`; `x != x`, `x < x` and `x > x` are always `false`;
`x - x` is always `0` and `s minus s` always `{}`; `a? and a?`, `a? or
a?`, `s union s` and `s inter s` are the operand. The message says which.
It has no fix: the likely mistake is a typo in one operand, which no
rewrite can repair. It does not fire on `+`, `*`, `++` or `join`, where `x
+ x` and `r join r` mean something, nor on `in`, nor on the comparisons
of a [chained comparison](../../Lang/Expressions.md#chained-comparisons),
such as `x < x < y`, which it leaves to a later lint on chains.
Operands are compared in their scopes: the right operand of `and` sees the
binders of the left's pattern tests, which the left does not, so in `(v > 1
and r is Reply::Value(v!)) and (v > 1 and r is Reply::Value(v!))` the two
first `v`s differ, and it does not fire. `lint::eq_op` states this, from the
operands as [written](../Meaning.md#expressions-as-written) in their
scopes:

```fren
pub mod lint

pub enum InfixOp {
    Iff, Or, And, Eq, Ne, Lt, Le, Gt, Ge, In, Subset, Add, Sub, Concat, Union, Minus, Mul, Inter, Join,
}

pub enum EqOpValue { AlwaysTrue, AlwaysFalse, Zero, Empty, Operand }

pub proc eq_op(
    op: InfixOp,
    left: Scoped,        -- the left operand, as written in its scope
    right: Scoped,       -- the right operand
): (
    det same?,
    det fires?,
    value: EqOpValue,         -- what the expression is, where it fires
) {
    use self::EqOpValue::{AlwaysFalse, AlwaysTrue, Empty, Zero}
    use self::InfixOp::{Add, Concat, Eq, Ge, Gt, Iff, In, Join, Le, Lt, Minus, Mul, Ne, Sub, Subset}
    out same? := left = right

    ensure rule: fires? iff (same? and not op in {Add, Mul, Concat, Join, In})
    ensure values: when fires?, value = match op {
        Eq | Le | Ge | Iff | Subset => AlwaysTrue,
        Ne | Lt | Gt => AlwaysFalse,
        Sub => Zero,
        Minus => Empty,
        _ => EqOpValue::Operand,
    }

    expect needs_same: when fires?, same?
}
```

The message is right because the two operands have the same value: they
are written the same, in the same scope, and in one environment, so by
[`written_same`](../Meaning.md#expressions-as-written) their root layers
have the same head and parts' values, and so the same value, specified or
not. Here `p` and `q` are the operands' root layers:

```fren
expect eq_op_operands: forall (e: eq_op) (p q: lang::node),
    when e.fires? and p.env = q.env and p.program = q.program and p.head = written_head(e.left)
    and p.values = written_values(p.env, e.left)
    and q.head = written_head(e.right) and q.values = written_values(q.env, e.right),
    p.value = q.value
```

What the message says the expression then is, `lint::eq_op_values`
checks on Fren's own evaluation, at any value of the operand of each type
the operator applies to:

```fren
-- `nonminimal_bool` would write `not (x < x)` as `x >= x`, another case.
set_option fren.lint.eq_op "allow" in
set_option fren.lint.nonminimal_bool "allow" in
pub proc eq_op_values(op: InfixOp, x: Int, a?, s: Set<Int>) {
    use self::EqOpValue::{AlwaysFalse, AlwaysTrue, Empty, Zero}
    use self::InfixOp::{And, Eq, Ge, Gt, Iff, Inter, Le, Lt, Minus, Ne, Or, Sub, Subset, Union}

    call e := eq_op(op, Scoped { text := Operand::P, scope := {} }, Scoped { text := Operand::P, scope := {} })

    expect said: when e.fires?, match e.value {
        AlwaysTrue => (op = Eq and x = x) or (op = Le and x <= x) or (op = Ge and x >= x)
            or (op = Iff and (a? iff a?)) or (op = Subset and s subset s),
        AlwaysFalse => (op = Ne and not (x != x)) or (op = Lt and not (x < x)) or (op = Gt and not (x > x)),
        Zero => op = Sub and x - x = 0,
        Empty => op = Minus and s minus s = {},
        EqOpValue::Operand => (op = And and ((a? and a?) iff a?)) or (op = Or and ((a? or a?) iff a?))
            or (op = Union and s union s = s) or (op = Inter and s inter s = s),
    }
}
```

`eq_op` also fires on `when C, D` and `unless C, D` where `C` and `D` are
written the same. `when C, C` is always `true`, and `unless C, C` is `C`.
The body is then almost always a copy of the condition, pasted where the
consequent was meant. The body of `when` sees the binders of the
condition's pattern tests, and the condition does not, so they are
compared in their scopes, as the operands of `and` are.
`lint::eq_op_conditional` states this; that `C` and `D` have the same
value is `written_same`, as for `eq_op`:

```fren
pub proc eq_op_conditional(
    unless?,             -- `unless`, rather than `when`
    condition: Scoped,    -- the condition, as written in its scope
    body: Scoped,         -- the body
): (
    det fires?,
    value: EqOpValue,         -- what the expression is, where it fires
) {
    use self::EqOpValue::AlwaysTrue

    ensure rule: fires? iff condition = body
    ensure values: when fires?, value = if unless? then EqOpValue::Operand else AlwaysTrue
}

set_option fren.lint.eq_op "allow" in
pub proc eq_op_conditional_values(unless?, a?) {
    call e := eq_op_conditional(
        unless?,
        Scoped { text := Operand::P, scope := {} },
        Scoped { text := Operand::P, scope := {} },
    )

    -- What the message says `when a?, a?` and `unless a?, a?` are.
    expect said: when e.fires?, if unless? then e.value = EqOpValue::Operand and ((unless a?, a?) iff a?)
        else e.value = EqOpValue::AlwaysTrue and (when a?, a?)
}
```

`eq_op` also fires on an argument of a [cardinality
operator](../../Lang/Expressions.md#cardinality) written the same as an
earlier one, as in `at_most_one?(a?, b?, a?)`. Where the argument holds,
it counts twice, so neither `exactly_one?` nor `at_most_one?` holds: the
call holds only where it does not, which is seldom what a list of
conditions meant, and one of the two is probably a typo for another. The
message is reported at the later one, and says this. `true` and `false`
are left to the lints of constants. `lint::eq_op_cardinality` models an
argument as a literal or an [operand](../Meaning.md#expressions-as-written)
as written, and states when it fires at an argument, from the operands of
the arguments before it, and the refinements check what the message
says, on a call with the repeated argument written once:

```fren
-- An argument of a cardinality operator: `true` or `false`, or another
-- expression, as written.
pub enum Argument { Literal(Bool), Written(Operand) }

pub proc eq_op_cardinality(
    earlier: Set<Operand>,    -- the arguments before it that are not literals
    argument: Argument,
): (det fires?) {
    ensure rule: fires? iff match argument {
        Argument::Written(x) => x in earlier,
        Argument::Literal(_) => false,
    }
}

set_option fren.lint.eq_op "allow" in
set_option fren.evidence "enumerated" in
pub proc eq_op_cardinality_written(a?, b?): (det exactly?, det at_most?) {
    out exactly? := exactly_one?(a?, b?, a?)
    out at_most? := at_most_one?(a?, b?, a?)
}

set_option fren.evidence "enumerated" in
pub proc eq_op_cardinality_value(a?, b?): (det exactly?, det at_most?) {
    out exactly? := not a? and b?
    out at_most? := not a?
}

refine eq_op_cardinality_sound: eq_op_cardinality_value refines eq_op_cardinality_written
refine eq_op_cardinality_complete: eq_op_cardinality_written refines eq_op_cardinality_value
```

## Erasing operations

`erasing_op` fires on an operation whose value ignores an operand: `x * 0`
and `0 * x` are always `0`; `s inter {}`, `{} inter s`, `{} minus s` and
`r join {}` are always `{}`, though `{}` in `r join {}` has no type it can
take, which is an error (see
[Checking and synthesis](../../Lang/Types.md#checking-and-synthesis)); `x
in {}` and `x in []` are always `false`; and `{} subset s` is always
`true`. It mirrors
[`identity_op`](../Complexity/Operators.md#identities), and an operand is `0` or `{}` as
it is there. The message says what the value is. It has no fix: the
likely mistake is the literal, and writing the value instead would keep
the mistake and hide it. Where both operands are written the same, as in
`s = {} inter {}`, `eq_op` fires instead. It does not fire
on `s subset {}`, which says that `s` is empty. `lint::erasing_op`
states this:

```fren
pub proc erasing_op(
    op: InfixOp,
    left: IdentityOperand,
    right: IdentityOperand,
    same?,               -- the operands are written the same
): (det fires?) {
    use self::IdentityOperand::{Empty, Zero}
    use self::InfixOp::{In, Inter, Join, Minus, Mul, Subset}

    ensure rule: fires? iff (not (same? and op in {Inter, Minus, Subset}) and match op {
        Mul => left = Zero or right = Zero,
        Inter | Join => left = Empty or right = Empty,
        Minus | Subset => left = Empty,
        In => right = Empty,
        _ => false,
    })
}

expect erasing_not_eq_op: forall (e: erasing_op) (q: eq_op), when q.op = e.op and q.same? = e.same?,
    not (e.fires? and q.fires?)
```

The refinements below check the values of `in` and `subset` that the
message claims: a procedure that computes the operation as written, one
whose output is the value, and a [refinement](../../Lang/Refinement.md) each
way, so that the solver checks that they agree on every input. An operand
is a variable, standing for any expression of its type: Fren's
expressions are pure, so what holds for every value of an operand holds
for every expression.

```fren
set_option fren.lint.erasing_op "allow" in
pub proc empty_membership_written(x: Int): (det v?) {
    out v? := x in {}
}

set_option fren.lint.unused_variables "allow" in
set_option fren.lint.constant_output "allow" in
pub proc empty_membership_value(x: Int): (det v?) {
    out v? := false
}

refine empty_membership_sound: empty_membership_value refines empty_membership_written
refine empty_membership_complete: empty_membership_written refines empty_membership_value

set_option fren.lint.erasing_op "allow" in
pub proc empty_subset_written(s: Set<Int>): (det v?) {
    out v? := {} subset s
}

set_option fren.lint.unused_variables "allow" in
set_option fren.lint.constant_output "allow" in
pub proc empty_subset_value(s: Set<Int>): (det v?) {
    out v? := true
}

refine empty_subset_sound: empty_subset_value refines empty_subset_written
refine empty_subset_complete: empty_subset_written refines empty_subset_value
```

It also fires on `0 div k` and `0 mod k`, and on `-0 div k` and `-0 mod
k`, which are always `0`: `k` is a
constant that is not `0` (see [Division and
remainder](../../Lang/Expressions.md#division-and-remainder)), and `0` is a
multiple of every such `k`. `lint::erasing_division` states this, and the
[refinements](../../Lang/Refinement.md) below check the value, for a
positive divisor and a negative one:

```fren
pub proc erasing_division(
    literal?,            -- the dividend is an integer literal, possibly negated
    dividend: Int,       -- its value, if it is
): (det fires?) {
    ensure rule: fires? iff (literal? and dividend = 0)
}

set_option fren.lint.erasing_op "allow" in
set_option fren.lint.constant_output "allow" in
set_option fren.evidence "enumerated" in
pub proc erasing_division_written(): (det quotient: Int, det remainder: Int) {
    out quotient := 0 div 7
    out remainder := 0 mod -3
}

set_option fren.lint.constant_output "allow" in
set_option fren.evidence "enumerated" in
pub proc erasing_division_fixed(): (det quotient: Int, det remainder: Int) {
    out quotient := 0
    out remainder := 0
}

refine erasing_division_sound: erasing_division_fixed refines erasing_division_written
refine erasing_division_complete: erasing_division_written refines erasing_division_fixed
```

## Branches written the same

`same_branches` fires on `if c then a else b`, where `a` and `b` are
written the same: the condition decides nothing. The fix replaces the
conditional with `a`, in parentheses where
[fixes need them](../../Lint.md#parentheses-in-fixes), from the operator that the conditional is an
operand of and what follows it, as for
[`nonminimal_bool`](../Complexity.md#simpler-bool-expressions). The value is `a`'s, and
the [guards](../../Lang/Expressions.md#sequences) of what remains get no
weaker: the copy of `a` guarded by `c` and the one guarded by `not c` are
both defined exactly when `a` is defined under the guard of the
conditional, which is `a`'s guard after the fix, and removing `c` only
removes something that is evaluated. A `match` whose arms are all written
the same is left to other lints. `lint::same_branches` states when it
fires, from the branches as [written](../Meaning.md#expressions-as-written)
in their scopes. It does not fire where the condition's pattern tests bind
names, which the `then` branch sees and the `else` branch does not (see
[`lang::test_scope`](../../Lang/Expressions.md#pattern-tests)): in `if r
is Reply::Value(v!) then v else v`, the same text means the payload in one
branch and the variable `v` in the other, so the fix would change the
value. It leaves such a conditional even where the branches mention none
of those names, rather than compare what they mention:

```fren
pub proc same_branches(
    binders: Set<lang::Id>,    -- the binders of the condition's pattern tests
    then_branch: Scoped,       -- the branches, as written in their scopes
    else_branch: Scoped,
): (det fires?) {
    ensure rule: fires? iff (binders = {} and then_branch = else_branch)

    expect no_binders: when fires?, binders = {} and then_branch.scope = else_branch.scope
}
```

The fix has the conditional's value because the branches have the same
value, whichever is taken, by [`written_same`](../Meaning.md#expressions-as-written).
Here `p` and `q` are their root layers:

```fren
expect same_branches_value: forall (b: same_branches) (p q: lang::node),
    when b.fires? and p.env = q.env and p.program = q.program and p.head = written_head(b.then_branch)
    and p.values = written_values(p.env, b.then_branch) and q.head = written_head(b.else_branch)
    and q.values = written_values(q.env, b.else_branch),
    p.value = q.value
```

`same_branches` fires on a [table](../../Lang/Expressions.md#tables)
whose rows' values are all written the same, of two or more rows, or of
one row that is `_`: its conditions decide nothing either. Where the table
has a `_` row, it has that value wherever it is evaluated, and the fix
replaces it with the value, in parentheses where [fixes need
them](../../Lint.md#parentheses-in-fixes); each row's copy of the value is guarded by the table's
guard, the negations of the earlier rows' conditions and its own, and
together they cover the table's guard, so the value's guard after the fix
is no stronger. Without a `_` row, the table is unspecified where no row
holds, which the value is not, so there is no fix. The message is at the table. The refinements below
check the fix on one example:

```fren
set_option fren.lint.same_branches "allow" in
pub proc same_rows_written(n: Int): (det v: Int) {
    out v := table { n > 0 => n + 1, n < -5 => n + 1, _ => n + 1 }
}

pub proc same_rows_fixed(n: Int): (det v: Int) {
    out v := n + 1
}

refine same_rows_sound: same_rows_fixed refines same_rows_written
refine same_rows_complete: same_rows_written refines same_rows_fixed
```

`lint::same_rows` states when it fires, computing the facts from the rows, with each
row's condition by whether it holds, and checks the fix: where there is a
`_` row, the first row that holds, or `_`, has the value that every row
has:

```fren
pub struct Row { holds?, value: Body }

pub fn row_holds?(r: Row) := r.holds?

pub fn row_value(r: Row): Body := r.value

pub proc same_rows(
    rows: Seq<Row>,
    wildcard?,               -- the last row is `_`
    o: Int,
): (
    det fires?,
    det fixed?,          -- it has a fix
) {
    assume size: 1 <= rows.len <= 4

    det let n_rows: Int := rows.len
    -- the rows' values are written the same
    det let same? := (forall (s: Slot), when pos(s) < rows.len, row_value(rows[pos(s)]) = row_value(rows[0]))

    ensure rule: fires? iff (same? and (n_rows >= 2 or wildcard?))
    ensure fix: fixed? iff wildcard?

    expect keeps_meaning: forall (s: Slot), when fires? and fixed? and pos(s) < rows.len
        and (row_holds?(rows[pos(s)]) or pos(s) = rows.len - 1)
        and (forall (r: Slot), when pos(r) < pos(s), not row_holds?(rows[pos(r)])),
        body_value(row_value(rows[pos(s)]), -1, 0, -1, 0, -1, 0, o) = body_value(row_value(rows[0]), -1, 0, -1, 0, -1, 0, o)
}
```

`ifs_same_cond` fires on a test of a chain of `else if` written the same
as an earlier test of the chain, as the second `x > 0` in `if x > 0 then a
else if x > 0 then b else c`. Its branch is never taken: it is guarded by
the negation of the earlier test, so wherever the test holds, the earlier
branch is taken. It is reported at the repeated test, and the message names
the earlier one. A test in parentheses, `else (if ...)`, is still in the
chain. It has no fix: one of the tests is probably not the one meant.
`lint::ifs_same_cond` states when it fires:

```fren
set_option fren.evidence "enumerated" in
pub proc ifs_same_cond(
    earlier?,            -- an earlier test of the chain is written the same
): (det fires?) {
    ensure rule: fires? iff earlier?
}
```

## Elements written the same

`duplicate_elements` fires on a set or relation literal with an element
written the same as an earlier one, as in `{a, b, a}` or `{(a, b), (a,
b)}`, and is reported once for the literal. A set has no repeats, so the
fix, which removes each repeat with the `,` before it, keeps the meaning,
and it keeps the guards, which are the same for every element of the
literal. It does not fire on a sequence literal, where a repeat means
something. `lint::duplicate_elements` states when it fires:

```fren
pub proc duplicate_elements(
    n_repeats: Nat,      -- elements written the same as an earlier one
): (det fires?) {
    ensure rule: fires? iff n_repeats > 0
}
```
