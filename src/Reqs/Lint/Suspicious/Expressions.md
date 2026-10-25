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
`lint::eq_op` states this:

```fren
pub mod lint

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

`eq_op` also fires on `when C, D` and `unless C, D` where `C` and `D` are
written the same. `when C, C` is always `true`, and `unless C, C` is `C`.
The body is then almost always a copy of the condition, pasted where the
consequent was meant. `lint::eq_op_conditional` states this:

```fren
pub comp eq_op_conditional {
    use self::EqOpValue::{AlwaysTrue, Operand}
    in unless?           -- `unless`, rather than `when`
    in same?             -- the condition and the body are written the same
    pub det out fires?
    pub out value: EqOpValue  -- what the expression is, where it fires

    req rule: fires? iff same?
    req values: when fires?, value = if unless? then Operand else AlwaysTrue
}
```

## Erasing operations

`erasing_op` fires on an operation whose value ignores an operand: `x * 0`
and `0 * x` are always `0`; `s inter {}`, `{} inter s`, `{} minus s` and
`r join {}` are always `{}`, though `{}` in `r join {}` has no type it can
take, which is an error (see
[Checking and synthesis](../../Lang/Types.md#checking-and-synthesis)); `x
in {}` is always `false`; and `{} subset s` is always `true`. It mirrors
[`identity_op`](../Complexity/Operators.md#identities), and an operand is `0` or `{}` as
it is there. The message says what the value is. It has no fix: the
likely mistake is the literal, and writing the value instead would keep
the mistake and hide it. Where both operands are written the same, as in
`s = {} inter {}`, `eq_op` fires instead. It does not fire
on `s subset {}`, which says that `s` is empty, nor on `x in []`, which
is a type error (`F0324`). `lint::erasing_op`
states this:

```fren
pub comp erasing_op {
    use self::IdentityOperand::{Empty, Zero}
    use self::InfixOp::{In, Inter, Join, Minus, Mul, Subset}
    in op: InfixOp
    in left: IdentityOperand
    in right: IdentityOperand
    in same?             -- the operands are written the same
    pub det out fires?

    req rule: fires? iff (not (same? and op in {Inter, Minus, Subset}) and match op {
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
message claims: a component that computes the operation as written, one
whose output is the value, and a [refinement](../../Lang/Refinement.md) each
way, so that the solver checks that they agree on every input. An operand
is a variable, standing for any expression of its type: Fren's
expressions are pure, so what holds for every value of an operand holds
for every expression.

```fren
set_option fren.lint.erasing_op "allow" in
pub comp empty_membership_written {
    in x: Int
    pub det out v? := x in {}
}

set_option fren.lint.unused_variables "allow" in
set_option fren.lint.constant_output "allow" in
pub comp empty_membership_value {
    in x: Int
    pub det out v? := false
}

refine empty_membership_sound: empty_membership_value refines empty_membership_written
refine empty_membership_complete: empty_membership_written refines empty_membership_value

set_option fren.lint.erasing_op "allow" in
pub comp empty_subset_written {
    in s: Set(Int)
    pub det out v? := {} subset s
}

set_option fren.lint.unused_variables "allow" in
set_option fren.lint.constant_output "allow" in
pub comp empty_subset_value {
    in s: Set(Int)
    pub det out v? := true
}

refine empty_subset_sound: empty_subset_value refines empty_subset_written
refine empty_subset_complete: empty_subset_written refines empty_subset_value
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
fires:

```fren
pub comp same_branches {
    in same?             -- the branches are written the same
    pub det out fires?

    req rule: fires? iff same?
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
pub comp ifs_same_cond {
    in earlier?          -- an earlier test of the chain is written the same
    pub det out fires?

    req rule: fires? iff earlier?
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
pub comp duplicate_elements {
    in n_repeats: Nat    -- elements written the same as an earlier one
    pub det out fires?

    req rule: fires? iff n_repeats > 0
}
```
