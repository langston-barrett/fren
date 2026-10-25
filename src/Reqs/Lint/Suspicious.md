# Suspicious

The lints of the `suspicious` group find what is probably not what the
writer meant.

## Indexes

`index_after_use` fires on `a and b`, where `a` indexes a sequence `q` and
`b` bounds it: it mentions `q.len`, or compares `q` with `[]`. The index is
probably meant to be guarded by `b`, but `and` guards its right operand by
its left (see [Expressions](../Lang/Expressions.md#sequences)), so the
[definedness check](../Check.md#definedness) fails. The fix swaps the
operands, which does not change the meaning. The lint looks only at the
text, never at the solver:

```fren
pub mod lint

pub comp index_after_use {
    in indexes_left?     -- `a` indexes a sequence `q`
    in bounds_right?     -- `b` mentions `q.len`, or compares `q` with `[]`
    pub det out fires?

    req rule: fires? iff (indexes_left? and bounds_right?)
}
```

## Suspicious expressions

These lints fire on expressions that are legal but probably not what the
writer meant. Two operands are compared as [written the
same](../Lint.md#written-the-same), where the parentheses around an operand
are not part of it, so the operands of `f(x) = f(x)` are written the same,
and those of `x = (x)`, but not those of `x + 1 = 1 + x`.

`eq_op` fires on an infix operator whose two operands are written the
same, where the expression is then always the same value, or the same as
its operand: `x = x`, `x <= x`, `x >= x`, `a? iff a?` and `s subset s`
are always `true`; `x != x`, `x < x` and `x > x` are always `false`;
`x - x` is always `0` and `s minus s` always `{}`; `a? and a?`, `a? or
a?`, `s union s` and `s inter s` are the operand. The message says which.
It has no fix: the likely mistake is a typo in one operand, which no
rewrite can repair. It does not fire on `+`, `*`, `++` or `join`, where `x
+ x` and `r join r` mean something, nor on `in`, nor on the comparisons
of a [chained comparison](../Lang/Expressions.md#chained-comparisons),
such as `x < x < y`, which it leaves to a later lint on chains.
`lint::eq_op` states this:

```fren
pub enum InfixOp {
    Iff, Or, And, Eq, Ne, Lt, Le, Gt, Ge, In, Subset, Add, Sub, Concat, Union, Minus, Mul, Inter, Join,
}

pub enum EqOpValue { AlwaysTrue, AlwaysFalse, Zero, Empty, Operand }

pub comp eq_op {
    use self::EqOpValue::{AlwaysFalse, AlwaysTrue, Empty, Operand, Zero}
    use self::InfixOp::{Add, Concat, Eq, Ge, Gt, Iff, In, Join, Le, Lt, Minus, Mul, Ne, Sub, Subset}
    in op: InfixOp
    in same?             -- the operands are written the same
    pub det out fires?
    pub out value: EqOpValue  -- what the expression is, where it fires

    req rule: fires? iff (same? and not op in {Add, Mul, Concat, Join, In})
    req values: when fires?, value = match op {
        Eq | Le | Ge | Iff | Subset => AlwaysTrue,
        Ne | Lt | Gt => AlwaysFalse,
        Sub => Zero,
        Minus => Empty,
        _ => Operand,
    }

    expect needs_same: when fires?, same?
}
```

`same_branches` fires on `if c then a else b`, where `a` and `b` are
written the same: the condition decides nothing. The fix replaces the
conditional with `a`, in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes), from the operator that the conditional is an
operand of and what follows it, as for
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions). The value is `a`'s, and
the [guards](../Lang/Expressions.md#sequences) of what remains get no
weaker: the copy of `a` guarded by `c` and the one guarded by `not c` are
both defined exactly when `a` is defined under the guard of the
conditional, which is `a`'s guard after the fix, and removing `c` only
removes something that is evaluated. A `match` whose arms are all written
the same is left to other lints. `lint::same_branches` states when it
fires:

```fren
pub comp same_branches {
    in same?             -- the branches are written the same
    pub det out fires?

    req rule: fires? iff same?
}
```

`duplicate_elements` fires on a set or relation literal with an element
written the same as an earlier one, as in `{a, b, a}` or `{(a, b), (a,
b)}`, and is reported once for the literal. A set has no repeats, so the
fix, which removes each repeat with the `,` before it, keeps the meaning,
and it keeps the guards, which are the same for every element of the
literal. It does not fire on a sequence literal, where a repeat means
something. `lint::duplicate_elements` states when it fires:

```fren
pub comp duplicate_elements {
    in n_repeats: Int    -- elements written the same as an earlier one
    pub det out fires?

    assume counts: n_repeats >= 0

    req rule: fires? iff n_repeats > 0
}
```

`empty_argument` fires on a method applied to an empty argument, where
its value at that [edge](../Lang/Expressions.md#methods) does not depend on
the receiver as it seems to. An argument is empty if it is written `""`
or `[]`, or, as the length of `slice`, `0`. Where `s` is the receiver, a
string or a sequence, and `e` the empty argument:

| Written | Value |
|---|---|
| `s.starts_with?(e)`, `s.ends_with?(e)`, `s.contains?(e)` | `true` |
| `s.replace(e, b)` | `b ++ s` |
| `s.replace_all(e, b)` | `s` |
| `s.index_of(e, i)` | `i` if `0 <= i <= s.len`, and `-1` otherwise |
| `s.slice(i, 0)` | `""`, or `[]` |

The message says what the expression is. It has no fix: the likely
mistake is the argument, and writing the value instead would keep the
mistake and hide it. `lint::empty_argument` states when it fires, from the
method and the position of an empty argument:

```fren
pub comp empty_argument {
    use lang::Method
    use lang::Method::{Contains, EndsWith, IndexOf, Replace, ReplaceAll, Slice, StartsWith}
    in method: Method
    in index: Int        -- the position of the argument, from 0
    in empty?            -- it is written `""` or `[]`, or `0`
    pub det out fires?

    assume position: index >= 0

    req rule: fires? iff (empty? and match method {
        StartsWith | EndsWith | Contains | Replace | ReplaceAll | IndexOf => index = 0,
        Slice => index = 1,
        _ => false,
    })
}
```
