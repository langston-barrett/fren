# Integers

These lints of the `suspicious` group find an expression of integers that
is always the same value, which is probably not what the writer meant.

```fren
pub mod lint
```

## Remainders and bounds

`modulo_one` fires on `x mod 1` and `x mod -1`, where the divisor is an
integer literal, possibly negated: every integer is a multiple of `1`, so
the remainder is always `0`, which the message says. The divisor is
probably not the one meant, as in `x mod 1 = 0` for `x mod 2 = 0`, so it
has no fix, as for [`eq_op`](Expressions.md#operands-written-the-same). A divisor that is a constant other than a
literal is left as it is. It follows Clippy's `modulo_one`, in
`correctness`, which Fren puts in `suspicious` (see
[Groups](../../Lint.md#groups)). `lint::modulo_one` states when it fires,
from the divisor:

```fren
pub proc modulo_one(divisor: Int): (det fires?) { ensure rule: fires? iff divisor is 1 | -1 }
```

`min_max` fires on `x.min(a).max(b)` where `a < b`, and on
`x.max(a).min(b)` where `a > b`, where `a` and `b` are integer literals,
possibly negated: `x.min(a)` is at most `a`, so its `max` with a greater
`b` is always `b`, and so, the other way, for `x.max(a).min(b)`. The
message says that the expression is always `b`. The bounds are probably
swapped, as in `x.min(0).max(9)` for `x.max(0).min(9)`, so it has no fix.
Bounds that are equal, as in `x.min(3).max(3)`, give `3` too, but say so,
and are left as they are, as Clippy's `min_max` leaves them; it is in
`correctness` there. `lint::min_max` states when it fires:

```fren
pub proc min_max(
    inner: MinMax,       -- the method of the inner call, `x.inner(a)`
    outer: MinMax,       -- the method of the outer call, `.outer(b)`
    a: Int,
    b: Int,
): (det fires?) {
    use self::MinMax::{Max, Min}

    ensure rule: fires? iff ((inner = Min and outer = Max and a < b) or (inner = Max and outer = Min and a > b))
}
```

The refinements below check the values that the messages of both lints
give:

```fren
set_option fren.lint.modulo_one "allow" in
set_option fren.lint.min_max "allow" in
pub proc integer_values_written(x: Int): (
    det one: Int,
    det minus_one: Int,
    det floor: Int,
    det ceiling: Int,
) {
    out one := x mod 1
    out minus_one := x mod -1
    out floor := x.min(0).max(9)
    out ceiling := x.max(4).min(-1)
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub proc integer_values_fixed(x: Int): (
    det one: Int,
    det minus_one: Int,
    det floor: Int,
    det ceiling: Int,
) {
    out one := 0
    out minus_one := 0
    out floor := 9
    out ceiling := -1
}

expect integer_values_sound(x: Int) {
    call concrete := integer_values_fixed(x)
    refines concrete integer_values_written(x)
}
expect integer_values_complete(x: Int) {
    call concrete := integer_values_written(x)
    refines concrete integer_values_fixed(x)
}
```

### Remainders by `1`, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
`-1` is `Unary(Neg, Literal(1))`, so `modulo_one` fires on `Binary(Mod,
x, b)` where `b` is `1` or that negation, and the message says that it
is `0`. As for [`eq_op`](Expressions.md#operands-written-the-same), there
is no fix, and what the lint states is that its message is right.

```fren
pub fn modulo_one_fires?<V>(e: lang::Expr<V>) := match e {
    lang::Expr::Binary(lang::BinaryOp::Mod, _, b) => one?(b) or minus_one?(b),
    _ => false,
}
```

`lint::modulo_one` binds this to the linter: for a divisor that is an
integer literal `n`, possibly negated, it fires exactly where
`modulo_one_fires?` does. That the front ends read the divisor so is
trusted, and checked by the ui tests in `test/ui/lints/integers.fren`.

```fren
expect modulo_one_elaborated(negated?, n: Nat, x: lang::Expr<lang::Id>) {
    use lang::Expr::{Binary, Literal, Unary}
    use lang::Value::Integer

    call p := modulo_one(if negated? then -n else n)

    let b: lang::Expr<lang::Id> := if negated? then Unary(lang::UnaryOp::Neg, Literal(Integer(n))) else Literal(Integer(n))

    expect fires: p.fires? iff modulo_one_fires?(Binary(lang::BinaryOp::Mod, x, b))
}
```

`mod` is a [primitive operation](../Meaning.md#primitive-operations), so
the remainder is `0` only in an interpretation that gives `mod` its usual
meaning. In one that does, the remainder by `1` or `-1` is at least `0`
and below `1`, so it is `0`, where the graph has a point for the
operands, and undefined elsewhere. `src/Impls/Rewrites.lean` proves this
in Lean, for every expression, interpretation whose primitives are
`usual?`, and environment; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc modulo_one_said_agrees(e: lang::Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure said: when usual?(i.primitives) and modulo_one_fires?(e),
        agrees?(
            lang::eval(i, env, lang::Expr::Literal(lang::Value::Integer(0))),
            lang::eval(i, env, e)
        )
}
```

## Idempotent methods

`eq_op` also fires on a call of `min` or `max` of `Int`, whose receiver
and argument are written the same: `x.min(x)` and `x.max(x)` are `x`,
which the message says. They are not infix operators, but they are
idempotent, as `and` and `union` are, and Clippy's `eq_op` fires on `x &
x` and `x | x` likewise. On a record, `r.min` reads a field, so the lint
looks at what the elaborator calls `min` or `max`. `lint::eq_op_method`
states when it fires:

```fren
pub proc eq_op_method(
    receiver: String,    -- the receiver's written form
    argument: String,    -- the argument's
): (det fires?) {
    ensure rule: fires? iff receiver = argument
}
```

The refinements below check the value that the message gives:

```fren
set_option fren.lint.eq_op "allow" in
pub proc eq_op_method_written(x: Int): (det lesser: Int, det greater: Int) {
    out lesser := x.min(x)
    out greater := (x + 1).max(x + 1)
}

pub proc eq_op_method_fixed(x: Int): (det lesser: Int, det greater: Int) {
    out lesser := x
    out greater := x + 1
}

expect eq_op_method_sound(x: Int) {
    call concrete := eq_op_method_fixed(x)
    refines concrete eq_op_method_written(x)
}
expect eq_op_method_complete(x: Int) {
    call concrete := eq_op_method_written(x)
    refines concrete eq_op_method_fixed(x)
}
```
