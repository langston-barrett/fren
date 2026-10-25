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
pub comp modulo_one {
    in divisor: Int
    pub det out fires?

    ensure rule: fires? iff (divisor = 1 or divisor = -1)
}
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
pub comp min_max {
    use self::MinMax::{Max, Min}
    in inner: MinMax     -- the method of the inner call, `x.inner(a)`
    in outer: MinMax     -- the method of the outer call, `.outer(b)`
    in a: Int
    in b: Int
    pub det out fires?

    ensure rule: fires? iff ((inner = Min and outer = Max and a < b) or (inner = Max and outer = Min and a > b))
}
```

The refinements below check the values that the messages of both lints
give:

```fren
set_option fren.lint.modulo_one "allow" in
set_option fren.lint.min_max "allow" in
pub comp integer_values_written {
    in x: Int
    pub det out one: Int := x mod 1
    pub det out minus_one: Int := x mod -1
    pub det out floor: Int := x.min(0).max(9)
    pub det out ceiling: Int := x.max(4).min(-1)
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub comp integer_values_fixed {
    in x: Int
    pub det out one: Int := 0
    pub det out minus_one: Int := 0
    pub det out floor: Int := 9
    pub det out ceiling: Int := -1
}

refine integer_values_sound: integer_values_fixed refines integer_values_written
refine integer_values_complete: integer_values_written refines integer_values_fixed
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
pub comp eq_op_method {
    in same?             -- the receiver and the argument are written the same
    pub det out fires?

    ensure rule: fires? iff same?
}
```

The refinements below check the value that the message gives:

```fren
set_option fren.lint.eq_op "allow" in
pub comp eq_op_method_written {
    in x: Int
    pub det out lesser: Int := x.min(x)
    pub det out greater: Int := (x + 1).max(x + 1)
}

pub comp eq_op_method_fixed {
    in x: Int
    pub det out lesser: Int := x
    pub det out greater: Int := x + 1
}

refine eq_op_method_sound: eq_op_method_fixed refines eq_op_method_written
refine eq_op_method_complete: eq_op_method_written refines eq_op_method_fixed
```
