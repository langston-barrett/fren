# Operators

## Conditional operands

A conditional is an atom, but its `else` branch extends as far right as
possible (see [Conditionals](../../Lang/Expressions.md#conditionals)): `2 * if
c? then x else y + 1` means `2 * (if c? then x else (y + 1))`, not `(2 * if
c? then x else y) + 1`. `else_extends` fires on a conditional, not in
parentheses, that is an operand of a binary operator, and whose `else`
branch would need parentheses in its place, as an operand of that
operator, under `lang::operand`. If the `else` branch is itself a
conditional not in parentheses, its own `else` branch counts instead, and
so on. The fix puts that branch in parentheses, as it is parsed, which
keeps the meaning and the guards, and shows where it ends:

```fren
pub mod lint

use lang::{Assoc, operand}

pub comp else_extends {
    in outer: Int        -- the precedence of the operator
    in inner: Int        -- the precedence of the `else` branch's operator
    in assoc: Assoc      -- the associativity of the operator
    in right?            -- the conditional is the operator's right operand
    pub det out fires?

    inst place: operand { outer, inner, assoc, right? }

    req rule: fires? iff not place.bare?
}
```

## Identities

`identity_op` fires on an operation that leaves one operand as it is, and
its fix is that operand:

| Written | Fix |
|---|---|
| `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x` | `x` |
| `s ++ ""`, `"" ++ s`, `q ++ []`, `[] ++ q` | `s`, `q` |
| `a union {}`, `{} union a`, `a minus {}` | `a` |

It also fires on `x + -y`, whose fix is `x - y`, and on `x - -y`, whose fix
is `x + y`. The fix has the operation's value and its type: the operands
of `+`, `-`, `*`, `++`, `union` and `minus` have the same type as the
result, and `""`, `[]` and `{}` are their identities, as `0` is of `+` and
`-` and `1` of `*`; `[]` and `{}` take their type from the other operand,
which keeps it. The operand removed is a literal, or a negation whose
operand the fix evaluates where it was, so the fix keeps the guards.
`lint::identity_op` states what the fix is, from the operator and what
each operand is:

```fren
pub enum IdentityOperator { Add, Sub, Mul, Concat, Union, Minus }

-- An operand as written: `Empty` is `""`, `[]` or `{}`, and `Negation` is `-y`.
pub enum IdentityOperand { Zero, One, Empty, Negation, Other }

pub enum Rewrite { KeepLeft, KeepRight, Flip, Unchanged }

pub comp identity_op {
    use self::IdentityOperand::{Empty, Negation, One, Zero}
    use self::IdentityOperator::{Add, Concat, Minus, Mul, Sub, Union}
    use self::Rewrite::{Flip, KeepLeft, KeepRight, Unchanged}
    in op: IdentityOperator
    in left: IdentityOperand
    in right: IdentityOperand
    pub det out rewrite: Rewrite  -- `Flip` is `x - y` for `x + -y`, and `x + y` for `x - -y`

    req rule: rewrite = match op {
        Add => if right = Zero then KeepLeft else if left = Zero then KeepRight
            else if right = Negation then Flip else Unchanged,
        Sub => if right = Zero then KeepLeft else if right = Negation then Flip else Unchanged,
        Mul => if right = One then KeepLeft else if left = One then KeepRight else Unchanged,
        Concat | Union => if right = Empty then KeepLeft else if left = Empty then KeepRight else Unchanged,
        Minus => if right = Empty then KeepLeft else Unchanged,
    }

    expect flips_only_sums: when rewrite = Flip, op in {Add, Sub}
}
```

## Parentheses

`double_parens` fires on parentheses directly around parentheses, with
nothing but whitespace between them: `((e))` means what `(e)` means. It
fires once for each run of such pairs, at the outermost, and its fix keeps
only the innermost: `(((e)))` becomes `(e)`. The parentheses of an
application, a method call or a pair are its own, not around an argument
or an element, so `f((x))` and `(1, (x))` each have one pair around `x`.
Parentheses around a receiver are around it alone, so `(({1}).card)` has
one pair around `{1}` and one around `({1}).card`, not two around `{1}`.
Parentheses only group, so the fix
changes neither the meaning nor the guards. `lint::double_parens` states
when it fires:

```fren
pub comp double_parens {
    in depth: Int        -- pairs of parentheses, each directly around the next
    pub det out fires?

    assume counts: depth >= 1

    req rule: fires? iff depth >= 2
}
```
