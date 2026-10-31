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

expect double_comparison_meaning(
    d_conjunction?,
    d_first: Comparison,
    d_second: Comparison,
    x_op: Comparison,
    x_order: Order,
    y_op: Comparison,
    y_order: Order,
    z_op: Comparison,
    z_order: Order,
) {
    call d := double_comparison(d_conjunction?, d_first, d_second)
    call x := comparison_holds(x_op, x_order)
    call y := comparison_holds(y_op, y_order)
    call z := comparison_holds(z_op, z_order)
    expect double_comparison_meaning: when d.fires? and x.op = d.first and y.op = d.second and z.op = d.result
        and x.order = z.order and y.order = z.order,
        z.holds? iff (if d.conjunction? then x.holds? and y.holds? else x.holds? or y.holds?)
}
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

fn complement_of(op: Comparison): Comparison := match op {
    Eq => Ne,
    Ne => Eq,
    Lt => Ge,
    Ge => Lt,
    Gt => Le,
    Le => Gt,
}

expect complement_of_agrees(c_op: Comparison) {
    call c := complement(c_op)
    expect complement_of_agrees: c.result = complement_of(c.op)
}

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

expect redundant_not_double(
    r_conjunction?,
    r_first: Comparison,
    r_first_bound: Int,
    r_second: Comparison,
    r_second_bound: Int,
    d_conjunction?,
    d_first: Comparison,
    d_second: Comparison,
) {
    call r := redundant_comparisons(
        r_conjunction?,
        r_first,
        r_first_bound,
        r_second,
        r_second_bound,
    )
    call d := double_comparison(d_conjunction?, d_first, d_second)
    expect redundant_not_double: when r.first_bound = r.second_bound and r.conjunction? = d.conjunction?
        and r.first = d.first and r.second = d.second,
        not (r.fires? and d.fires?)
}
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
fn offset_value(o: Offset): Int := match o {
    Zero => 0,
    PlusOne => 1,
    MinusOne => -1,
}

proc int_plus_one_exact(
    op: Comparison,
    left: Offset,
    right: Offset,
    a: Int,              -- the left operand, without its offset
    b: Int,              -- the right operand, without its offset
) {
    call p := int_plus_one(op, left, right)

    expect exact: when p.fires?, compares?(op, a + offset_value(left), b + offset_value(right))
        iff compares?(
            p.result,
            if p.drop_left? then a else a + offset_value(left),
            if p.drop_left? then b + offset_value(right) else b
        )
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

expect int_plus_one_chain_sound(i: Int, n: Int, m: Int) {
    call concrete := int_plus_one_chain_fixed(i, n, m)
    refines concrete int_plus_one_chain_written(i, n, m)
}
expect int_plus_one_chain_complete(i: Int, n: Int, m: Int) {
    call concrete := int_plus_one_chain_written(i, n, m)
    refines concrete int_plus_one_chain_fixed(i, n, m)
}
```

### Off-by-one comparisons, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
`a >= b` is `b <= a`, and `a > b` is `b < a`, as [Derived
forms](../../Lang/Semantics.md#derived-forms) states, so the rows of the
table above are of one operator, `<=`: `b + 1 <= a` and `1 + b <= a`, or
`b <= a - 1`, each of which becomes `b < a`, as [Fixes as
rewrites](../Rewrites.md) states for every such lint. Where both operands
are off by one, the fix drops the `+ 1`, as above. `offset_of` reads an
operand as `lint::int_plus_one` does, and `without_offset` drops its
offset:

```fren
-- `e` is the literal `1`.
fn one?(e: lang::Expr) := e = lang::Expr::Literal(lang::Value::Integer(1))

pub fn offset_of(e: lang::Expr): Offset := match e {
    lang::Expr::Binary(lang::BinaryOp::Add, a, b) if one?(b) or one?(a) => PlusOne,
    lang::Expr::Binary(lang::BinaryOp::Sub, _, b) if one?(b) => MinusOne,
    _ => Zero,
}

pub fn without_offset(e: lang::Expr): lang::Expr := match e {
    lang::Expr::Binary(lang::BinaryOp::Add, a, b) => if one?(b) then a else if one?(a) then b else e,
    lang::Expr::Binary(lang::BinaryOp::Sub, a, b) => if one?(b) then a else e,
    _ => e,
}

pub fn int_plus_one_fires?(e: lang::Expr) := match e {
    lang::Expr::Binary(lang::BinaryOp::Le, a, b) => offset_of(a) = PlusOne or offset_of(b) = MinusOne,
    _ => false,
}

pub fn int_plus_one_fix(e: lang::Expr): lang::Expr := match e {
    lang::Expr::Binary(lang::BinaryOp::Le, a, b) => if offset_of(a) = PlusOne
        then lang::Expr::Binary(lang::BinaryOp::Lt, without_offset(a), b)
        else if offset_of(b) = MinusOne then lang::Expr::Binary(lang::BinaryOp::Lt, a, without_offset(b))
        else e,
    _ => e,
}
```

`lint::int_plus_one` binds this to the linter: at the offsets that
`offset_of` reads, it fires on `a <= b`, and on `b >= a`, exactly where
`int_plus_one_fires?` does on their elaboration, and its fix drops the
offset that `int_plus_one_fix` drops. It fires on no other comparison,
and `int_plus_one_fires?` on no other expression. That the front ends read
the operators, and `1`, as elaboration does, is trusted, and checked by
the ui tests of the lint. In a chained comparison, the linter fires only at
an end of the chain, so not in every place that `int_plus_one_fires?`
does: the elaboration of `0 <= i + 1 <= n` has `i + 1 <= n`, on which it
fires.

```fren
expect int_plus_one_elaborated(a: lang::Expr, b: lang::Expr, e: lang::Expr) {
    use lang::BinaryOp
    use lang::Expr::Binary

    -- `a <= b`, as written, and `b >= a`.
    call le := int_plus_one(Comparison::Le, offset_of(a), offset_of(b))
    call ge := int_plus_one(Comparison::Ge, offset_of(b), offset_of(a))

    expect le_rule: le.fires? iff int_plus_one_fires?(Binary(BinaryOp::Le, a, b))
    expect ge_rule: ge.fires? iff int_plus_one_fires?(Binary(BinaryOp::Le, a, b))
    expect le_fix: when le.fires?, int_plus_one_fix(Binary(BinaryOp::Le, a, b))
        = if le.drop_left? then Binary(BinaryOp::Lt, without_offset(a), b) else Binary(BinaryOp::Lt, a, without_offset(b))
    expect ge_fix: when ge.fires?, int_plus_one_fix(Binary(BinaryOp::Le, a, b))
        = if ge.drop_left? then Binary(BinaryOp::Lt, a, without_offset(b)) else Binary(BinaryOp::Lt, without_offset(a), b)
    expect other: unless e is Binary(BinaryOp::Le, _, _), not int_plus_one_fires?(e)
}
```

Where it fires, the fix has the expression's outcome, in every
interpretation and environment: where `a` and `b` are integers, `b + 1 <=
a` holds exactly where `b < a` does, and elsewhere both are undefined. So
it [agrees](../Meaning.md#fixes-that-agree) with the expression, and is
exact. Addition and subtraction are not primitives, so this holds in
every interpretation. The solver unfolds
[`eval`](../../Lang/Semantics.md#the-evaluation-function) one step, and the
offsets are two deep, so `src/Impls/Rewrites.lean` proves it in Lean, for
every expression, interpretation and environment; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc int_plus_one_keeps_meaning(e: lang::Expr, i: lang::Interp, env: lang::Env) {
    ensure exact: when int_plus_one_fires?(e),
        lang::eval(i, env, int_plus_one_fix(e)) = lang::eval(i, env, e)
}
```

Unlike those of `overly_complex_bool_expr` and `double_neg`, this fix
fixes the lint at one place: it writes a `<`, on which the lint does not
fire (`kept`). And it starts no new firing elsewhere: the lint reads an
operand only by its offset and by whether it is `1`, and the fix keeps
both (`around`).

```fren
expect int_plus_one_once(e: lang::Expr) {
    expect kept: not int_plus_one_fires?(int_plus_one_fix(e))
    expect around: offset_of(int_plus_one_fix(e)) = offset_of(e) and (one?(int_plus_one_fix(e)) iff one?(e))
}
```
