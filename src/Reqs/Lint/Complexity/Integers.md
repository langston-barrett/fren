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
requires them, as in `(a - b).abs`. `lint::manual_abs` states when it
fires, from the comparison with `x` on its left, mirrored where `x` is
written on the right:

```fren
pub comp manual_abs {
    use self::Comparison::{Ge, Gt, Le, Lt}
    in compared: Ordered  -- what the condition compares
    in op: Comparison    -- the comparison of `x` with `0`, with `x` on its left
    in negated_then?     -- the `then` branch is `-x` and the `else` branch `x`, rather than the reverse
    pub det out fires?

    ensure rule: fires? iff (compared = Ordered::Number and (if negated_then? then op in {Lt, Le} else op in {Gt, Ge}))
}
```

It is exact: where it fires, the conditional is `x.abs`, for every `x`:

```fren
comp manual_abs_exact {
    in op: Comparison
    in negated_then?
    in x: Int

    inst p: manual_abs { compared := Ordered::Number, op, negated_then? }

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

pub comp manual_abs_diff {
    use self::Comparison::{Ge, Gt, Le, Lt}
    in op: Comparison    -- the comparison of `a` and `b`
    in compared: Ordered  -- what it compares
    in a: String         -- the written forms of its operands
    in b: String
    in then_branch: Difference
    in else_branch: Difference
    pub det out fires?

    ensure rule: fires? iff (compared = Ordered::Number and a != b
        and ((then_branch = forward and else_branch = backward and op in {Gt, Ge})
        or (then_branch = backward and else_branch = forward and op in {Lt, Le})))
        where forward := Difference { minuend := a, subtrahend := b },
        backward := Difference { minuend := b, subtrahend := a }
}

comp manual_abs_diff_exact {
    in op: Comparison
    in then_left_first?
    in a: Int
    in b: Int

    inst p: manual_abs_diff {
        op, compared := Ordered::Number, a := "a", b := "b",
        then_branch := if then_left_first? then Difference { minuend := "a", subtrahend := "b" }
            else Difference { minuend := "b", subtrahend := "a" },
        else_branch := if then_left_first? then Difference { minuend := "b", subtrahend := "a" }
            else Difference { minuend := "a", subtrahend := "b" },
    }

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
pub comp manual_abs_written {
    in x: Int
    in y: Int
    pub det out below: Int := if x < 0 then -x else x
    pub det out at_most: Int := if 0 >= x then -x else x
    pub det out above: Int := if x > 0 then x else -x
    pub det out at_least: Int := if 0 <= x then x else -x
    pub det out sum: Int := if x + y < 0 then -(x + y) else x + y
    pub det out diff_above: Int := if x >= y then x - y else y - x
    pub det out diff_below: Int := if x < y then y - x else x - y
}

pub comp manual_abs_fixed {
    in x: Int
    in y: Int
    pub det out below: Int := x.abs
    pub det out at_most: Int := x.abs
    pub det out above: Int := x.abs
    pub det out at_least: Int := x.abs
    pub det out sum: Int := (x + y).abs
    pub det out diff_above: Int := (x - y).abs
    pub det out diff_below: Int := (y - x).abs
}

refine manual_abs_sound: manual_abs_fixed refines manual_abs_written
refine manual_abs_complete: manual_abs_written refines manual_abs_fixed
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

pub comp manual_min_max {
    use self::Comparison::{Ge, Gt, Le, Lt}
    use self::MinMax::{Max, Min}
    in op: Comparison
    in compared: Ordered
    in a: Written        -- the condition's operands
    in b: Written
    in then_branch: String  -- the branches' written forms
    in else_branch: String
    pub det out fires?
    pub out method: MinMax  -- the method of the fix, where it fires
    pub out receiver_left?  -- its receiver is `a`, and its argument `b`, rather than the reverse

    ensure rule: fires? iff (op in {Lt, Le, Gt, Ge} and compared != Ordered::OtherType and a.text != b.text
        and not (a.literal? and b.literal?)
        and ((then_branch = a.text and else_branch = b.text) or (then_branch = b.text and else_branch = a.text)))
    ensure which: when fires?, method = (if (op in {Lt, Le} iff then_branch = a.text) then Min else Max)
    ensure receiver: when fires?, receiver_left? iff not a.literal?
}

comp manual_min_max_exact {
    in op: Comparison
    in then_left?
    in a: Int
    in b: Int

    inst p: manual_min_max {
        op, compared := Ordered::Number, a := Written { text := "a", literal? := false },
        b := Written { text := "b", literal? := false }, then_branch := if then_left? then "a" else "b",
        else_branch := if then_left? then "b" else "a",
    }

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
pub comp manual_clamp {
    use self::Comparison::{Ge, Gt, Le, Lt}
    in compared: Ordered      -- what the first test compares
    in first_op: Comparison   -- the first test's comparison, with `x` on its left
    in second_op: Comparison  -- the second test's
    in first: Int             -- the first test's bound
    in second: Int            -- the second test's bound
    pub det out fires?
    pub det out low_first?    -- the first test is of the lower bound

    ensure rule: fires? iff (compared = Ordered::Number
        and ((first_op in {Lt, Le} and second_op in {Gt, Ge} and first <= second)
        or (first_op in {Gt, Ge} and second_op in {Lt, Le} and second <= first)))
    ensure low: low_first? iff first_op in {Lt, Le}
}

comp manual_clamp_exact {
    in first_op: Comparison
    in second_op: Comparison
    in first: Int
    in second: Int
    in x: Int

    inst p: manual_clamp { compared := Ordered::Number, first_op, second_op, first, second }

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
pub comp manual_min_max_written {
    in x: Int
    in y: Int
    in n: Nat
    pub det out lesser: Int := if x < y then x else y
    pub det out greater: Int := if x <= y then y else x
    pub det out lesser_above: Int := if x > y then y else x
    pub det out greater_above: Int := if y >= x then y else x
    pub det out capped: Nat := if n > 3 then 3 else n
    pub det out clamped: Int := if x < -2 then -2 else if x > 5 then 5 else x
    pub det out clamped_above: Int := if 5 <= x then 5 else if -2 >= x then -2 else x
}

pub comp manual_min_max_fixed {
    in x: Int
    in y: Int
    in n: Nat
    pub det out lesser: Int := x.min(y)
    pub det out greater: Int := x.max(y)
    pub det out lesser_above: Int := x.min(y)
    pub det out greater_above: Int := y.max(x)
    pub det out capped: Nat := n.min(3)
    pub det out clamped: Int := x.max(-2).min(5)
    pub det out clamped_above: Int := x.max(-2).min(5)
}

refine manual_min_max_sound: manual_min_max_fixed refines manual_min_max_written
refine manual_min_max_complete: manual_min_max_written refines manual_min_max_fixed
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

pub comp manual_rem_euclid {
    in p: Summand
    in q: Summand
    in k: String         -- the outer divisor's written form
    pub det out fires?

    ensure rule: fires? iff (if p.remainder? then p.divisor = k and q.text = k
        else q.remainder? and q.divisor = k and p.text = k)
}
```

A divisor is a constant, so the refinements below check the fix for a
positive divisor, a negative one, and a `Nat` dividend:

```fren
set_option fren.lint.manual_rem_euclid "allow" in
pub comp manual_rem_euclid_written {
    in x: Int
    in n: Nat
    pub det out positive: Int := (x mod 7 + 7) mod 7
    pub det out negative: Int := (-3 + x mod -3) mod -3
    pub det out natural: Nat := (n mod 4 + 4) mod 4
}

pub comp manual_rem_euclid_fixed {
    in x: Int
    in n: Nat
    pub det out positive: Int := x mod 7
    pub det out negative: Int := x mod -3
    pub det out natural: Nat := n mod 4
}

refine manual_rem_euclid_sound: manual_rem_euclid_fixed refines manual_rem_euclid_written
refine manual_rem_euclid_complete: manual_rem_euclid_written refines manual_rem_euclid_fixed
```

Clippy's `manual_div_ceil` has no counterpart, since Fren has no rounding
division but `div`; nor do its `integer_division` and
`modulo_arithmetic`, which warn of a division that truncates and of a
remainder with the dividend's sign: `div` is integer division by its name,
and `mod` is never negative.
