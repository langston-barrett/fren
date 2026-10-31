# Integers

These lints of the `complexity` group find a conditional or a remainder
that a [method of `Int`](../../Lang/Expressions.md#methods), or `mod` alone,
writes more simply. Each fires only where the operands of the condition
and of the branches are [written the same](../../Lint.md#written-the-same),
and each fix keeps the meaning, which the refinements of each section
check, and the guards: every operand that the fix evaluates is evaluated
by the condition of the conditional it replaces, so is defined wherever
the conditional is. The fixes of the conditionals write their operands
without what is between them, so where the conditional has a comment,
the message has no fix, and says why.

Each looks at the type that the condition compares, as the elaborator
types it: `lint::Ordered` is `Int` or `Nat`, an [ordered
enumeration](../../Lang/Items.md#enumerations), or another type, such as
`String` or a [newtype](../../Lang/Items.md#newtypes). Only `Int` and `Nat` have
`abs`, and they and ordered enumerations alone have `min` and `max`; a
newtype of `Int` has none of them, so `a.min(b)` or `(a - b).abs` of a
newtype would be an error (`F0322`, `F0315`), and the lints leave it.
An operand's *written form* is its text without the parentheses around
it and without comments or spaces, as [written the
same](../../Lint.md#written-the-same) compares it.

```fren
pub mod lint

pub enum Ordered { Number, Enumeration, OtherType }
```

## Absolute values

`manual_abs` fires on a conditional that is the absolute value of `x`,
where `0` is the literal, `x` is not a literal, and `-x` is a negation:

| Written | Fix |
|---|---|
| `if x < 0 then -x else x`, `if x <= 0 then -x else x` | `x.abs` |
| `if x > 0 then x else -x`, `if x >= 0 then x else -x` | `x.abs` |

and so with `0` on the left, as in `if 0 > x then -x else x`. At `x = 0`
both branches are `0`, so the strict and the non-strict comparisons
agree. The condition must compare `Int`s or `Nat`s, and then the
conditional is an `Int`, as `abs` is. `x` is in parentheses as the
receiver where [`lang::operand`](../../Lang/Expressions.md#operators)
requires them, as in `(a - b).abs`, and where the grammar would not read
it as a receiver without them (`lint::print`, in [Printing
fixes](../Printing.md)). `lint::manual_abs` states when it
fires, from the comparison with `x` on its left, mirrored where `x` is
written on the right:

```fren
set_option fren.evidence "enumerated" in
pub proc manual_abs(
    compared: Ordered,    -- what the condition compares
    op: Comparison,      -- the comparison of `x` with `0`, with `x` on its left
    negated_then?,       -- the `then` branch is `-x` and the `else` branch `x`, rather than the reverse
): (det fires?) {
    use self::Comparison::{Ge, Gt, Le, Lt}

    ensure rule: fires? iff (compared = Ordered::Number and (if negated_then? then op in {Lt, Le} else op in {Gt, Ge}))
}
```

It is exact: where it fires, the conditional is `x.abs`, for every `x`:

```fren
proc manual_abs_exact(op: Comparison, negated_then?, x: Int) {
    call p := manual_abs(Ordered::Number, op, negated_then?)

    expect exact: when p.fires?,
        (if compares?(op, x, 0) then (if negated_then? then -x else x) else (if negated_then? then x else -x)) = x.abs
}
```

`manual_abs_diff` fires on a conditional that subtracts the lesser of `a`
and `b` from the greater, where `a` and `b` are not written the same:

| Written | Fix |
|---|---|
| `if a > b then a - b else b - a`, `if a >= b then a - b else b - a` | `(a - b).abs` |
| `if a < b then b - a else a - b`, `if a <= b then b - a else a - b` | `(b - a).abs` |

The condition must compare `Int`s or `Nat`s. The fix is the absolute
value of the `then` branch, so it keeps its operands in their order. It
follows Clippy's `manual_abs_diff`, in `complexity`, whose fix is
`abs_diff`, which Fren writes with `abs`. `lint::manual_abs_diff` states
when it fires, from the written forms of the condition's operands and of
each branch's minuend and subtrahend:

```fren
pub struct Difference { minuend: String, subtrahend: String }

pub proc manual_abs_diff(
    op: Comparison,      -- the comparison of `a` and `b`
    compared: Ordered,    -- what it compares
    a: String,           -- the written forms of its operands
    b: String,
    then_branch: Difference,
    else_branch: Difference,
): (det fires?) {
    use self::Comparison::{Ge, Gt, Le, Lt}

    ensure rule: fires? iff (compared = Ordered::Number and a != b
        and ((then_branch = forward and else_branch = backward and op in {Gt, Ge})
        or (then_branch = backward and else_branch = forward and op in {Lt, Le})))
        where forward := Difference {
            minuend := a,
            subtrahend := b,
        },
        backward := Difference {
            minuend := b,
            subtrahend := a,
        }
}

proc manual_abs_diff_exact(op: Comparison, then_left_first?, a: Int, b: Int) {
    call p := manual_abs_diff(
        op,
        Ordered::Number,
        "a",
        "b",
        if then_left_first? then Difference {
            minuend := "a",
            subtrahend := "b",
        }
            else Difference {
                minuend := "b",
                subtrahend := "a",
            },
        if then_left_first? then Difference {
            minuend := "b",
            subtrahend := "a",
        }
            else Difference {
                minuend := "a",
                subtrahend := "b",
            },
    )

    expect exact: when p.fires?,
        (if compares?(op, a, b) then (if then_left_first? then a - b else b - a)
        else (if then_left_first? then b - a else a - b))
        = (if then_left_first? then (a - b).abs else (b - a).abs)
}
```

The refinements below check the fixes of both lints, for each form:

```fren
set_option fren.lint.manual_abs "allow" in
set_option fren.lint.manual_abs_diff "allow" in
pub proc manual_abs_written(x: Int, y: Int): (
    det below: Int,
    det at_most: Int,
    det above: Int,
    det at_least: Int,
    det sum: Int,
    det diff_above: Int,
    det diff_below: Int,
) {
    out below := if x < 0 then -x else x
    out at_most := if 0 >= x then -x else x
    out above := if x > 0 then x else -x
    out at_least := if 0 <= x then x else -x
    out sum := if x + y < 0 then -(x + y) else x + y
    out diff_above := if x >= y then x - y else y - x
    out diff_below := if x < y then y - x else x - y
}

pub proc manual_abs_fixed(x: Int, y: Int): (
    det below: Int,
    det at_most: Int,
    det above: Int,
    det at_least: Int,
    det sum: Int,
    det diff_above: Int,
    det diff_below: Int,
) {
    out below := x.abs
    out at_most := x.abs
    out above := x.abs
    out at_least := x.abs
    out sum := (x + y).abs
    out diff_above := (x - y).abs
    out diff_below := (y - x).abs
}

expect manual_abs_sound(x: Int, y: Int) {
    call concrete := manual_abs_fixed(x, y)
    refines concrete manual_abs_written(x, y)
}
expect manual_abs_complete(x: Int, y: Int) {
    call concrete := manual_abs_written(x, y)
    refines concrete manual_abs_fixed(x, y)
}
```

### Absolute values, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
`a > b` is `b < a`, and `a >= b` is `b <= a`, as [Derived
forms](../../Lang/Semantics.md#derived-forms) states, so each condition
of these lints is a `<` or a `<=`, and its fix is a call of `abs`, as
[Fixes as rewrites](../Rewrites.md) states for every such lint.
`manual_abs` fires on `if x OP 0 then -x else x` and on `if 0 OP x then x
else -x`, where `OP` is `<` or `<=` and `x` is not an integer literal.
`manual_abs_diff` fires on `if s OP m then m - s else s - m`, where `OP`
is `<` or `<=` and `s` and `m` are not the same, and its fix is the
absolute value of the `then` branch. Operands written the same in one
scope are the same `lang::Expr`, as
[`written`](../Meaning.md#expressions-as-written) states, so `=` is the
test of being written the same. The model orders only integers, so
neither states what the condition compares.

```fren
-- `e` is the literal `0`.
fn zero?(e: lang::Expr) := e = lang::Expr::Literal(lang::Value::Integer(0))

-- `op` is `<` or `<=`, the orderings that elaboration writes.
fn ordering?(op: lang::BinaryOp) := op is lang::BinaryOp::Lt | lang::BinaryOp::Le

-- `abs` of `x`.
fn abs_of(x: lang::Expr): lang::Expr := lang::Expr::Method(
    lang::MethodName::Abs,
    x,
    lang::Expr::Nil
)

-- `if x OP 0 then -x else x`, of an `x` that is not an integer literal.
fn abs_negated_then?(c: lang::Expr, t: lang::Expr, f: lang::Expr) := match c {
    lang::Expr::Binary(op, x, z) => ordering?(op) and zero?(z) and not (x is lang::Expr::Literal(lang::Value::Integer(_)))
        and t = lang::Expr::Unary(lang::UnaryOp::Neg, x) and f = x,
    _ => false,
}

-- `if 0 OP x then x else -x`.
fn abs_negated_else?(c: lang::Expr, t: lang::Expr, f: lang::Expr) := match c {
    lang::Expr::Binary(op, z, x) => ordering?(op) and zero?(z) and not (x is lang::Expr::Literal(lang::Value::Integer(_)))
        and t = x and f = lang::Expr::Unary(lang::UnaryOp::Neg, x),
    _ => false,
}

pub fn manual_abs_fires?(e: lang::Expr) := match e {
    lang::Expr::If(c, t, f) => abs_negated_then?(c, t, f) or abs_negated_else?(c, t, f),
    _ => false,
}

pub fn manual_abs_fix(e: lang::Expr): lang::Expr := match e {
    lang::Expr::If(c, t, f) => if abs_negated_then?(c, t, f) then abs_of(f)
        else if abs_negated_else?(c, t, f) then abs_of(t)
        else e,
    _ => e,
}

-- `if s OP m then m - s else s - m`.
fn abs_diff?(c: lang::Expr, t: lang::Expr, f: lang::Expr) := match c {
    lang::Expr::Binary(op, s, m) => ordering?(op) and s != m
        and t = lang::Expr::Binary(lang::BinaryOp::Sub, m, s) and f = lang::Expr::Binary(lang::BinaryOp::Sub, s, m),
    _ => false,
}

pub fn manual_abs_diff_fires?(e: lang::Expr) := match e {
    lang::Expr::If(c, t, f) => abs_diff?(c, t, f),
    _ => false,
}

pub fn manual_abs_diff_fix(e: lang::Expr): lang::Expr := match e {
    lang::Expr::If(c, t, f) => if abs_diff?(c, t, f) then abs_of(t) else e,
    _ => e,
}
```

`lint::manual_abs` and `lint::manual_abs_diff` bind this to the linter.
For every comparison operator and every `x`, `manual_abs`, at the
comparison with `x` on its left, fires on the conditional with `x OP 0`
exactly where `manual_abs_fires?` does on its elaboration, and its fix is
`x.abs`. A condition written with `0` on the left, as in `0 > x`, is
mirrored first, to `x < 0`, whose elaboration is the same, so this is
stated with `x` on the left only. For every comparison operator and two
operands `a` and `b` not written the same, `manual_abs_diff` fires on
`if a OP b then c else d`, with `c` and `d` the two differences, exactly
where `manual_abs_diff_fires?` does on its elaboration, and its fix is the
absolute value of `c`. Where `a` and `b` are the same, neither fires.

The front ends' reading of `-`, `0` and the comparison, and the
mirroring of the condition, are trusted, and checked by the ui tests of
the lints. So is that they run these lints only at conditionals:
neither procedure has an input that says it is at one, and the functions
above fire on nothing else, by their `match`. The linter fires only where
these functions do, not in every place they do: it compares only `Int`s
and `Nat`s, which are the only values the model orders, and it leaves an
`x` written as a negated literal, such as `-5`.

```fren
-- `if x OP 0 then -x else x`, or the reverse, as elaborated.
fn abs_written(op: Comparison, negated_then?, x: lang::Expr): lang::Expr := lang::Expr::If(
    elaborated_comparison(op, x, lang::Expr::Literal(lang::Value::Integer(0))),
    if negated_then? then lang::Expr::Unary(lang::UnaryOp::Neg, x) else x,
    if negated_then? then x else lang::Expr::Unary(lang::UnaryOp::Neg, x)
)

-- `a - b`, or `b - a`.
fn difference_of(a_first?, a: lang::Expr, b: lang::Expr): lang::Expr :=
    if a_first? then lang::Expr::Binary(lang::BinaryOp::Sub, a, b) else lang::Expr::Binary(lang::BinaryOp::Sub, b, a)

-- `if a OP b then a - b else b - a`, or the reverse, as elaborated.
fn abs_diff_written(op: Comparison, then_left_first?, a: lang::Expr, b: lang::Expr): lang::Expr := lang::Expr::If(
    elaborated_comparison(op, a, b),
    difference_of(then_left_first?, a, b),
    difference_of(not then_left_first?, a, b)
)

-- The written forms of `a - b`, or of `b - a`, of the operands `a` and `b`.
fn written_difference(a_first?, a: String, b: String): Difference :=
    if a_first? then Difference {
        minuend := a,
        subtrahend := b,
    } else Difference {
        minuend := b,
        subtrahend := a,
    }

expect manual_abs_elaborated(op: Comparison, negated_then?, x: lang::Expr) {
    call p := manual_abs(Ordered::Number, op, negated_then?)

    expect rule: unless x is lang::Expr::Literal(lang::Value::Integer(_)),
        p.fires? iff manual_abs_fires?(abs_written(op, negated_then?, x))
    expect fix: when p.fires? and not (x is lang::Expr::Literal(lang::Value::Integer(_))),
        manual_abs_fix(abs_written(op, negated_then?, x)) = abs_of(x)
}

expect manual_abs_diff_elaborated(op: Comparison, then_left_first?, a: lang::Expr, b: lang::Expr) {
    call p := manual_abs_diff(
        op,
        Ordered::Number,
        "a",
        "b",
        written_difference(then_left_first?, "a", "b"),
        written_difference(not then_left_first?, "a", "b"),
    )
    call alike := manual_abs_diff(
        op,
        Ordered::Number,
        "a",
        "a",
        written_difference(then_left_first?, "a", "a"),
        written_difference(not then_left_first?, "a", "a"),
    )

    expect rule: when a != b, p.fires? iff manual_abs_diff_fires?(abs_diff_written(op, then_left_first?, a, b))
    expect fix: when a != b and p.fires?,
        manual_abs_diff_fix(abs_diff_written(op, then_left_first?, a, b)) = abs_of(difference_of(then_left_first?, a, b))
    expect same: not alike.fires? and not manual_abs_diff_fires?(abs_diff_written(op, then_left_first?, a, a))
}
```

Where they fire, the fixes have the conditional's outcome, in every
interpretation and environment: where the operands are integers, the
conditional is the absolute value of `x`, or of the difference, and
elsewhere the condition is undefined, and so are the conditional and the
call of `abs`. So each [agrees](../Meaning.md#fixes-that-agree) with the
conditional, and is exact. Negation, subtraction and `abs` are not
primitives, so this holds in every interpretation. The solver unfolds
[`eval`](../../Lang/Semantics.md#the-evaluation-function) one step, and
the operands are two deep, so `src/Impls/Rewrites.lean` proves it in Lean,
for every expression, interpretation and environment; `fren check` tests
it:

```fren
set_option fren.evidence "random" in
pub proc manual_abs_keeps_meaning(e: lang::Expr, i: lang::Interp, env: lang::Env) {
    ensure exact: when manual_abs_fires?(e), lang::eval(i, env, manual_abs_fix(e)) = lang::eval(i, env, e)
}

set_option fren.evidence "random" in
pub proc manual_abs_diff_keeps_meaning(e: lang::Expr, i: lang::Interp, env: lang::Env) {
    ensure exact: when manual_abs_diff_fires?(e), lang::eval(i, env, manual_abs_diff_fix(e)) = lang::eval(i, env, e)
}
```

Each fix writes a call of `abs`, on which the lint does not fire
(`kept`), of an operand of the conditional or of one of its operands, so
once the operands are fixed, it leaves nothing to fix. An expression
around it may start firing once it is fixed, though, since the lints
compare whole operands: in `if y.abs < 0 then -(if y < 0 then -y else y)
else y.abs`, the inner conditional does not fire, and its fix makes the
outer one fire (`around`).

```fren
-- `if y.abs < 0 then -z else y.abs`.
fn abs_around(y: lang::Expr, z: lang::Expr): lang::Expr := lang::Expr::If(
    elaborated_comparison(
        Comparison::Lt,
        abs_of(y),
        lang::Expr::Literal(lang::Value::Integer(0))
    ),
    lang::Expr::Unary(lang::UnaryOp::Neg, z),
    abs_of(y)
)

expect manual_abs_refires(y: lang::Id, e: lang::Expr) {
    expect kept: not manual_abs_fires?(manual_abs_fix(e)) and not manual_abs_diff_fires?(manual_abs_diff_fix(e))
    expect around: not manual_abs_fires?(abs_around(lang::Expr::Var(y), inner))
        and manual_abs_fires?(abs_around(lang::Expr::Var(y), manual_abs_fix(inner)))
        where inner := abs_written(Comparison::Lt, true, lang::Expr::Var(y))
}
```

## Lesser and greater

`manual_min_max` fires on `if a OP b then c else d`, where `OP` is `<`,
`<=`, `>` or `>=`, `a` and `b` are `Int`s, `Nat`s or values of one ordered
enumeration, are not written the same, and `c` and `d` are `a` and `b` in either order. Where the
comparison says that `a` is below `b`, the conditional is `a.min(b)` if
the `then` branch is `a`, and `a.max(b)` if it is `b`; where it says that
`a` is above `b`, the reverse. At `a = b` both branches are the same, so
the strict and the non-strict comparisons agree. `String`s and newtypes
have orderings too, but no `min` or `max`, so the lint looks at what the
elaborator compares.

The fix calls the method on `a`, with `b` as its argument, or on `b`, with
`a`, if `a` has an integer literal in it and `b` has none, and it does
not fire if both have one. An integer literal is a `Nat` where one is
expected (see [Natural numbers](../../Lang/Expressions.md#natural-numbers)),
and a receiver never is: so `if n < 3 then n else 3`, of a `Nat` `n`,
which is a `Nat`, is `n.min(3)`, which is a `Nat`, but `(3).max(n)` would
be an `Int`. With the receiver without a literal, the receiver has the
type it had in the condition, the argument is a `Nat` where it was and
the receiver is, and so the fix is a `Nat` wherever the conditional is,
and a `Nat` at most where the conditional was an `Int`, which widens.
Clippy has no lint of this name, since Rust's `min` and `max` came before
its lints; this follows its `manual_*` lints for operations the language
has, such as `manual_clamp`, in `complexity`. `lint::manual_min_max`
states when it fires, which method the fix calls, and on which receiver,
from the written forms:

```fren
pub enum MinMax { Min, Max }

-- An operand of the condition: its written form, and whether an integer literal is in it.
pub struct Written { text: String, literal? }

pub proc manual_min_max(
    op: Comparison,
    compared: Ordered,
    a: Written,          -- the condition's operands
    b: Written,
    then_branch: String,    -- the branches' written forms
    else_branch: String,
): (
    det fires?,
    method: MinMax,         -- the method of the fix, where it fires
    receiver_left?,         -- its receiver is `a`, and its argument `b`, rather than the reverse
) {
    use self::Comparison::{Ge, Gt, Le, Lt}
    use self::MinMax::{Max, Min}

    ensure rule: fires? iff (op in {Lt, Le, Gt, Ge} and compared != Ordered::OtherType and a.text != b.text
        and not (a.literal? and b.literal?)
        and ((then_branch = a.text and else_branch = b.text) or (then_branch = b.text and else_branch = a.text)))
    ensure which: when fires?, method = (if (op in {Lt, Le} iff then_branch = a.text) then Min else Max)
    ensure receiver: when fires?, receiver_left? iff not a.literal?
}

proc manual_min_max_exact(op: Comparison, then_left?, a: Int, b: Int) {
    call p := manual_min_max(
        op,
        Ordered::Number,
        Written {
            text := "a",
            literal? := false,
        },
        Written {
            text := "b",
            literal? := false,
        },
        if then_left? then "a" else "b",
        if then_left? then "b" else "a",
    )

    expect exact: when p.fires?,
        (if compares?(op, a, b) then (if then_left? then a else b) else (if then_left? then b else a))
        = (if p.method = MinMax::Min then a.min(b) else a.max(b))
}
```

`manual_clamp` fires on `if x OP₁ b₁ then b₁ else if x OP₂ b₂ then b₂
else x`, where the bounds `b₁` and `b₂` are integer literals, possibly
negated, `x` has no integer literal in it, one test says that `x` is below
its bound and the other that it is above, and the lower bound is at most
the upper, and the first condition compares `Int`s or `Nat`s. `x` may be
on either side of each comparison. It follows
Clippy's `manual_clamp`, in `complexity`, which fires only on constant
bounds in order too: where the lower bound is above the upper,
`x.max(lo).min(hi)` is `hi`, whatever `x` is, but the conditional is not.
The fix is `x.max(lo).min(hi)`, whose receiver is `x`, for the reasons
`manual_min_max`'s is. The inner conditional is `manual_clamp`'s, so
`manual_min_max`, which would fire on it alone, does not.
`lint::manual_clamp` states when it fires, and which test is of the lower
bound:

```fren
pub proc manual_clamp(
    compared: Ordered,        -- what the first test compares
    first_op: Comparison,     -- the first test's comparison, with `x` on its left
    second_op: Comparison,    -- the second test's
    first: Int,               -- the first test's bound
    second: Int,              -- the second test's bound
): (
    det fires?,
    det low_first?,           -- the first test is of the lower bound
) {
    use self::Comparison::{Ge, Gt, Le, Lt}

    ensure rule: fires? iff (compared = Ordered::Number
        and ((first_op in {Lt, Le} and second_op in {Gt, Ge} and first <= second)
        or (first_op in {Gt, Ge} and second_op in {Lt, Le} and second <= first)))
    ensure low: low_first? iff first_op in {Lt, Le}
}

proc manual_clamp_exact(
    first_op: Comparison,
    second_op: Comparison,
    first: Int,
    second: Int,
    x: Int,
) {
    call p := manual_clamp(Ordered::Number, first_op, second_op, first, second)

    expect exact: when p.fires?,
        (if compares?(first_op, x, first) then first else if compares?(second_op, x, second) then second else x)
        = (if p.low_first? then x.max(first).min(second) else x.max(second).min(first))
}
```

The refinements below check the fixes of both lints, for each form, with
a `Nat` among them:

```fren
set_option fren.lint.manual_min_max "allow" in
set_option fren.lint.manual_clamp "allow" in
pub proc manual_min_max_written(x: Int, y: Int, n: Nat): (
    det lesser: Int,
    det greater: Int,
    det lesser_above: Int,
    det greater_above: Int,
    det capped: Nat,
    det clamped: Int,
    det clamped_above: Int,
) {
    out lesser := if x < y then x else y
    out greater := if x <= y then y else x
    out lesser_above := if x > y then y else x
    out greater_above := if y >= x then y else x
    out capped := if n > 3 then 3 else n
    out clamped := if x < -2 then -2 else if x > 5 then 5 else x
    out clamped_above := if 5 <= x then 5 else if -2 >= x then -2 else x
}

pub proc manual_min_max_fixed(x: Int, y: Int, n: Nat): (
    det lesser: Int,
    det greater: Int,
    det lesser_above: Int,
    det greater_above: Int,
    det capped: Nat,
    det clamped: Int,
    det clamped_above: Int,
) {
    out lesser := x.min(y)
    out greater := x.max(y)
    out lesser_above := x.min(y)
    out greater_above := y.max(x)
    out capped := n.min(3)
    out clamped := x.max(-2).min(5)
    out clamped_above := x.max(-2).min(5)
}

expect manual_min_max_sound(x: Int, y: Int, n: Nat) {
    call concrete := manual_min_max_fixed(x, y, n)
    refines concrete manual_min_max_written(x, y, n)
}
expect manual_min_max_complete(x: Int, y: Int, n: Nat) {
    call concrete := manual_min_max_written(x, y, n)
    refines concrete manual_min_max_fixed(x, y, n)
}
```

## Remainders

`mod` is Euclidean (see [Division and
remainder](../../Lang/Expressions.md#division-and-remainder)): `a mod k`
is at least 0, and below `k.abs`, even where `a` or `k` is negative. A
writer used to a remainder with the sign of the dividend, as `%` has in
Rust and C, makes it non-negative with `(a mod k + k) mod k`, which is
`a mod k` already: `a mod k + k` differs from `a mod k` by `k`, and a
remainder by `k` is the same for numbers that differ by `k`.
`manual_rem_euclid` fires on `(a mod k + k) mod k`, and on `(k + a mod k)
mod k`, where the three divisors and the addend are written the same, and
its fix is `a mod k`. It follows Clippy's `manual_rem_euclid`, in
`complexity`, whose fix is `rem_euclid`, which `mod` is in Fren. The fix
is a `Nat` wherever the expression was, since `a mod k` is when `a mod k +
k` is, and may be a `Nat` where it was an `Int`, which widens: with a
constant `k` of type `Int`, `a mod k + k` is an `Int` even of a `Nat` `a`.
`lint::manual_rem_euclid` states when it fires on `(p + q) mod k`, from
the written forms of `p`, `q` and `k`, and of the divisor of each of `p`
and `q` that is a `mod`: the first of them that is a `mod` is the
remainder, and the other must be written as `k`:

```fren
-- An operand of `+`: its written form, and, if it is a `mod`, its divisor's.
pub struct Summand { text: String, remainder?, divisor: String }

pub proc manual_rem_euclid(
    p: Summand,
    q: Summand,
    k: String,           -- the outer divisor's written form
): (det fires?) {
    ensure rule: fires? iff (if p.remainder? then p.divisor = k and q.text = k
        else q.remainder? and q.divisor = k and p.text = k)
}
```

A divisor is a constant, so the refinements below check the fix for a
positive divisor, a negative one, and a `Nat` dividend:

```fren
set_option fren.lint.manual_rem_euclid "allow" in
pub proc manual_rem_euclid_written(x: Int, n: Nat): (
    det positive: Int,
    det negative: Int,
    det natural: Nat,
) {
    out positive := (x mod 7 + 7) mod 7
    out negative := (-3 + x mod -3) mod -3
    out natural := (n mod 4 + 4) mod 4
}

pub proc manual_rem_euclid_fixed(x: Int, n: Nat): (
    det positive: Int,
    det negative: Int,
    det natural: Nat,
) {
    out positive := x mod 7
    out negative := x mod -3
    out natural := n mod 4
}

expect manual_rem_euclid_sound(x: Int, n: Nat) {
    call concrete := manual_rem_euclid_fixed(x, n)
    refines concrete manual_rem_euclid_written(x, n)
}
expect manual_rem_euclid_complete(x: Int, n: Nat) {
    call concrete := manual_rem_euclid_written(x, n)
    refines concrete manual_rem_euclid_fixed(x, n)
}
```

Clippy's `manual_div_ceil` has no counterpart, since Fren has no rounding
division but `div`; nor do its `integer_division` and
`modulo_arithmetic`, which warn of a division that truncates and of a
remainder with the dividend's sign: `div` is integer division by its name,
and `mod` is never negative.
