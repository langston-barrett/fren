# Comparisons

The lints of [double comparisons](#double-comparisons) and [redundant
comparisons](#redundant-comparisons), of [searches](Methods.md#searches),
[whole slices](Methods.md#whole-slices) and [conditional
operands](Operators.md#conditional-operands), and
[`bool_equality`](../Pedantic.md#boolean-equality), look at the operators
and method calls of an expression, in any constraint, argument, binding, definition,
constant or global expectation, and are fixable. Like
[`nonminimal_bool`](../Complexity.md#simpler-bool-expressions), each fix
puts its operands, and itself, in parentheses where
[fixes need them](../../Lint.md#parentheses-in-fixes). Operands are compared
as [written the same](../../Lint.md#written-the-same). A [pattern
test](../../Lang/Expressions.md#pattern-tests) is an opaque test to these
lints, and to the other lints of operators and method calls: they look
inside it only at its scrutinee, and place it as they place a
comparison, which binds as tightly.

## Double comparisons

`double_comparison` fires on two comparisons of the same two operands,
written the same, joined by `and` or `or`, that together are one
comparison of those operands other than either of them:

| Written | Fix |
|---|---|
| `a < b or a = b` | `a <= b` |
| `a > b or a = b` | `a >= b` |
| `a < b or a > b` | `a != b` |
| `a <= b and a >= b` | `a = b` |
| `a <= b and a != b` | `a < b` |
| `a >= b and a != b` | `a > b` |
| `a subset b and b subset a` | `a = b` |

The two comparisons may come in either order, and the second may have its
operands the other way around, as in `b > a`, which is `a < b`; the fix
keeps the first's order. Orderings compare `Int`s, `String`s or values of
an [ordered enumeration](../../Lang/Items.md#enumerations), which are all
totally ordered, so whether a comparison holds depends only on whether `a`
is below, equal to or above `b`, and `lint::double_comparison_meaning`
checks that the fix holds in exactly the same cases as the two. Two sets
or relations are equal exactly when each is a subset of the other. The fix
keeps the guards: the second comparison is guarded by the first or by its
negation, but both evaluate the same operands, which the first does
unguarded, so the second is defined wherever the first is, and so is the
fix.

```fren
pub mod lint

pub enum Order { Below, Same, Above }

set_option fren.evidence "enumerated" in
pub proc comparison_holds(
    op: Comparison,
    order: Order,        -- how the left operand compares with the right
): (det holds?) {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}

    ensure rule: holds? iff match op {
        Eq => order = Order::Same,
        Ne => order != Order::Same,
        Lt => order = Order::Below,
        Le => order != Order::Above,
        Gt => order = Order::Above,
        Ge => order != Order::Below,
    }
}

pub proc double_comparison(
    conjunction?,        -- the comparisons are joined by `and`, rather than `or`
    first: Comparison,
    second: Comparison,    -- with its operands in the first's order
): (
    det fires?,
    det result: Comparison,         -- the fix, if it fires; otherwise `first`
) {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}

    ensure fires: fires? iff first != second and (if conjunction?
        then first in {Le, Ge, Ne} and second in {Le, Ge, Ne}
        else first in {Lt, Gt, Eq} and second in {Lt, Gt, Eq})
    ensure fix: result = if not fires? then first
        else if conjunction? then (if first != Ne and second != Ne then Eq else if Le in {first, second} then Lt else Gt)
        else (if first != Eq and second != Eq then Ne else if Lt in {first, second} then Le else Ge)
}

expect double_comparison_meaning: forall (d: double_comparison) (x y z: comparison_holds),
    when d.fires? and x.op = d.first and y.op = d.second and z.op = d.result
    and x.order = z.order and y.order = z.order,
    z.holds? iff (if d.conjunction? then x.holds? and y.holds? else x.holds? or y.holds?)
```

## Redundant comparisons

`redundant_comparisons` fires on two comparisons of one operand, written
the same, with integer literals, joined by `and` or `or`, where one
implies the other. Under `and`, the fix keeps the one that implies the
other, and under `or`, the one that the other implies:

| Written | Fix |
|---|---|
| `x < 3 and x < 5`, `x < 3 and x != 4`, `x = 3 and x >= 0` | `x < 3`, `x < 3`, `x = 3` |
| `x < 3 or x < 5`, `x < 3 or x != 4`, `x = 3 or x >= 0` | `x < 5`, `x != 4`, `x >= 0` |
| `x > 2 and x >= 3` | `x > 2`, which means the same as `x >= 3` |

Each comparison may have its operands the other way around, as in `5 > x`,
and the fix keeps the comparison as written; where each implies the other,
it keeps the first. Two comparisons written the same are left to
[`eq_op`](../Suspicious/Expressions.md#operands-written-the-same). Where
`double_comparison` fires, with the same literal, neither comparison implies
the other, so the two never fire together. The fix keeps the guards: the
comparison it keeps compares the same operand as the one it drops, with a
literal, so it is defined wherever the dropped one is, which is evaluated
wherever the kept one is.

Over the integers, `x OP k` with `OP` one of `=`, `>` and `>=` bounds `x`
from below, by `least(OP, k)`, and with `OP` one of `=`, `<` and `<=`
bounds it from above, by `greatest(OP, k)`. `disjoint?` says that no
integer meets two comparisons, each with `x` on the left: one bounds `x`
from below above where the other bounds it from above, or they are `x = k`
and `x != k`. `lint::disjoint` checks that this is exact. `x OP₁ a`
implies `x OP₂ b` exactly when it is disjoint from the complement of `x
OP₂ b`, `complement_of`, which is `lint::complement`'s, and
`lint::redundant_comparisons` states when the lint fires from this:

```fren
fn least(op: Comparison, k: Int): Int := if op = Gt then k + 1 else k

fn greatest(op: Comparison, k: Int): Int := if op = Lt then k - 1 else k

fn disjoint?(op1: Comparison, a: Int, op2: Comparison, b: Int) :=
    (op1 in {Eq, Gt, Ge} and op2 in {Eq, Lt, Le} and least(op1, a) > greatest(op2, b))
    or (op2 in {Eq, Gt, Ge} and op1 in {Eq, Lt, Le} and least(op2, b) > greatest(op1, a))
    or (a = b and ((op1 = Eq and op2 = Ne) or (op1 = Ne and op2 = Eq)))

fn both?(op1: Comparison, a: Int, op2: Comparison, b: Int, x: Int) := compares?(op1, x, a) and compares?(op2, x, b)

fn complement_of(op: Comparison): Comparison := match op { Eq => Ne, Ne => Eq, Lt => Ge, Ge => Lt, Gt => Le, Le => Gt }

expect complement_of_agrees: forall (c: complement), c.result = complement_of(c.op)

proc disjoint(op1: Comparison, a: Int, op2: Comparison, b: Int, x: Int) {
    expect sound: when disjoint?(op1, a, op2, b), not both?(op1, a, op2, b, x)
    -- Each comparison is the same between its literal and the next integer,
    -- so if any integer meets both, one next to `a` or `b` does.
    expect complete: when not disjoint?(op1, a, op2, b),
        both?(op1, a, op2, b, a - 1) or both?(op1, a, op2, b, a) or both?(op1, a, op2, b, a + 1)
        or both?(op1, a, op2, b, b - 1) or both?(op1, a, op2, b, b) or both?(op1, a, op2, b, b + 1)
}

pub proc redundant_comparisons(
    conjunction?,        -- the comparisons are joined by `and`, rather than `or`
    first: Comparison,    -- `x OP k`, with `x` on the left
    first_bound: Int,
    second: Comparison,
    second_bound: Int,
): (
    det fires?,
    det keep_first?,         -- the fix keeps the first comparison, rather than the second
) {
    ensure fires: fires? iff (disjoint?(first, first_bound, complement_of(second), second_bound)
        or disjoint?(second, second_bound, complement_of(first), first_bound))
    ensure fix: keep_first? iff (if conjunction?
        then disjoint?(first, first_bound, complement_of(second), second_bound)
        else disjoint?(second, second_bound, complement_of(first), first_bound))
}

proc redundant_comparisons_exact(
    conjunction?,
    first: Comparison,
    first_bound: Int,
    second: Comparison,
    second_bound: Int,
    x: Int,
) {
    call p := redundant_comparisons(conjunction?, first, first_bound, second, second_bound)

    expect exact: when p.fires?,
        (if conjunction? then both?(first, first_bound, second, second_bound, x)
        else compares?(first, x, first_bound) or compares?(second, x, second_bound))
        iff (if p.keep_first? then compares?(first, x, first_bound) else compares?(second, x, second_bound))
}

expect redundant_not_double: forall (r: redundant_comparisons) (d: double_comparison),
    when r.first_bound = r.second_bound and r.conjunction? = d.conjunction?
    and r.first = d.first and r.second = d.second,
    not (r.fires? and d.fires?)
```

## Off-by-one comparisons

`int_plus_one` fires on a non-strict comparison of integers with an
operand off by one, where its fix is the strict comparison without the
offset. Where `1` is the literal, and `1 + b` is the same as `b + 1`:

| Written | Fix |
|---|---|
| `a >= b + 1`, `a >= 1 + b`, `a - 1 >= b` | `a > b` |
| `b + 1 <= a`, `1 + b <= a`, `b <= a - 1` | `b < a` |

Where both operands are off by one, as in `a - 1 >= b + 1`, the fix drops
the `+ 1`: `a - 1 > b`. `lint::int_plus_one` states this, from the offset
of each operand of the comparison:

```fren
pub enum Offset { Zero, PlusOne, MinusOne }

use self::Offset::{MinusOne, PlusOne, Zero}

pub proc int_plus_one(
    op: Comparison,
    left: Offset,        -- `e + 1` and `1 + e` are `PlusOne`, `e - 1` is `MinusOne`, and any other operand `Zero`
    right: Offset,
): (
    det fires?,
    det result: Comparison,         -- the comparison of the fix
    det drop_left?,                 -- the fix drops the offset of the left operand, rather than the right
) {
    use self::Comparison::{Ge, Gt, Le, Lt}

    ensure rule: fires? iff ((op = Ge and (right = PlusOne or left = MinusOne))
        or (op = Le and (left = PlusOne or right = MinusOne)))
    ensure strict: result = (if op = Ge then Gt else if op = Le then Lt else op)
    ensure drop: drop_left? iff (if op = Ge then right != PlusOne else op = Le and left = PlusOne)
}
```

The fix is exact: over the integers, where the lint fires, the comparison
of the operands, `a` and `b` with their offsets, holds exactly when the
fix does:

```fren
fn offset_value(o: Offset): Int := match o { Zero => 0, PlusOne => 1, MinusOne => -1 }

proc int_plus_one_exact(
    op: Comparison,
    left: Offset,
    right: Offset,
    a: Int,              -- the left operand, without its offset
    b: Int,              -- the right operand, without its offset
) {
    call p := int_plus_one(op, left, right)

    expect exact: when p.fires?, compares?(op, a + offset_value(left), b + offset_value(right))
        iff compares?(p.result, if p.drop_left? then a else a + offset_value(left),
        if p.drop_left? then b + offset_value(right) else b)
}
```

Its fix writes its operands, and is put in parentheses itself, as the
fixes of [`double_neg` and `neg_multiply`](../Style.md#negations) are, and
keeps the guards for the same reasons.

In a [chained comparison](../../Lang/Expressions.md#chained-comparisons), it
fires on a comparison whose fix drops the offset of an operand at an end
of the chain, which is in that comparison only: `0 <= i <= n - 1` becomes
`0 <= i < n`, and `n - 1 >= i >= 0` becomes `n > i >= 0`. The fix rewrites
the chain with that comparison strict and that operand without its offset.
It does not fire where the operand is between two operators, as in `0 <=
i + 1 <= n`, whose other comparison would change. `lint::int_plus_one_in_chain`
states this, and the refinements check the fixes:

```fren
pub proc int_plus_one_in_chain(
    comparison: Nat,       -- its position in the chain, from 0
    n_comparisons: Nat,
    drop_left?,            -- `int_plus_one`'s fix of it alone drops its left operand's offset
): (det fires?) {
    assume position: comparison < n_comparisons

    ensure rule: fires? iff (if drop_left? then comparison = 0 else comparison + 1 = n_comparisons)
}

set_option fren.lint.int_plus_one "allow" in
pub proc int_plus_one_chain_written(i: Int, n: Int, m: Int): (det last?, det first?, det offset?) {
    out last? := 0 <= i <= n - 1
    out first? := n - 1 >= i >= 0
    out offset? := i + 1 <= n <= m
}

pub proc int_plus_one_chain_fixed(i: Int, n: Int, m: Int): (det last?, det first?, det offset?) {
    out last? := 0 <= i < n
    out first? := n > i >= 0
    out offset? := i < n <= m
}

refine int_plus_one_chain_sound: int_plus_one_chain_fixed refines int_plus_one_chain_written
refine int_plus_one_chain_complete: int_plus_one_chain_written refines int_plus_one_chain_fixed
```
