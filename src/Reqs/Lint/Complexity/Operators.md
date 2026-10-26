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

    ensure rule: fires? iff not place.bare?
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

    ensure rule: rewrite = match op {
        Add | Sub if right = Zero => KeepLeft,
        Add if left = Zero => KeepRight,
        Add | Sub if right = Negation => Flip,
        Mul if right = One => KeepLeft,
        Mul if left = One => KeepRight,
        Concat | Union | Minus if right = Empty => KeepLeft,
        Concat | Union if left = Empty => KeepRight,
        _ => Unchanged,
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

    ensure rule: fires? iff depth >= 2
}
```

## Cardinality

`manual_at_most_one` fires on a run of adjacent conjuncts of an `and`,
each `not (a and b)`, that negate each pair of three or more operands
exactly once, and nothing else, and is fixable: `not (a? and b?) and not
(a? and c?) and not (b? and c?)` becomes `at_most_one?(a?, b?, c?)` (see
[Cardinality](../../Lang/Expressions.md#cardinality)). Where the conjunct
just before or after the run is the disjunction of the operands, each
once, as in `(a? or b? or c?) and not (a? and b?) and ...`, the run takes
it in, and the fix is `exactly_one?(a?, b?, c?)`. Operands are compared
as [written the same](../../Lint.md#written-the-same), and a pair may be
written either way round, as in `not (b? and a?)`. The run of `and` is
read as [`chainable_comparison`](../Style/Comparisons.md#chained-comparisons)
reads it, and a conjunct in parentheses is not in a run, so `p? and not
(a? and b?) and ...` fires at the conjuncts after `p?`. The message is
reported from the first conjunct it replaces to the last. The fix writes
the operands as the disjunction orders them, or else in the order they
are first written, and there is no fix where a comment is within the
conjuncts, which the call would lose; the message then suggests the call.

`n` operands take `n * (n - 1) / 2` such conjuncts, and one left out is
hard to see among the rest. With two, `not (a? and b?)` is as clear as
`at_most_one?(a?, b?)`, so the lint does not fire. The fix keeps the
meaning: at most one argument of `at_most_one?` holds exactly when no two
of them hold together, and `exactly_one?` holds where, besides, one of them
does. It keeps the guards where it fires: in the conjunction, each operand
is [guarded](../../Lang/Expressions.md#sequences) by the operands before
it, and the arguments of a cardinality operator by none, so the lint does
not fire where an operand gives a [definedness](../../Check.md#definedness)
obligation, which a guard could discharge: an index `q[i]`, a
[table](../../Lang/Expressions.md#tables), or a name of a `let` or `where`
whose definition gives one, as in `not (ok? and big?) and ... where big? :=
q[i] > 0`. Operands without one are defined wherever they are evaluated,
under any guard. Clippy has no counterpart.
`lint::manual_at_most_one` states when it fires, and which call the fix
is:

```fren
pub comp manual_at_most_one {
    in n_operands: Int   -- the operands, each counted once
    in every_pair?       -- the conjuncts negate each pair of two different operands exactly once
    in disjunction?      -- the conjunct just before or after them is the disjunction of the operands
    in obligations?      -- an operand gives a definedness obligation
    pub det out fires?
    pub det out exactly?   -- the fix is `exactly_one?`, rather than `at_most_one?`

    ensure rule: fires? iff n_operands >= 3 and every_pair? and not obligations?
    ensure fix: exactly? iff disjunction?
}
```

The refinements check both fixes, with the pairs in any order and either
way round:

```fren
set_option fren.lint.manual_at_most_one "allow" in
pub comp manual_at_most_one_written {
    in a?
    in b?
    in c?
    in d?
    pub det out three? := not (a? and b?) and not (a? and c?) and not (b? and c?)
    pub det out turned? := not (b? and a?) and not (c? and b?) and not (c? and a?)
    pub det out four? := not (a? and b?) and not (a? and c?) and not (a? and d?) and not (b? and c?)
        and not (b? and d?) and not (c? and d?)
    pub det out exactly? := (a? or b? or c?) and not (a? and b?) and not (a? and c?) and not (b? and c?)
    pub det out after? := not (a? and b?) and not (a? and c?) and not (b? and c?) and (c? or a? or b?)
}

pub comp manual_at_most_one_fixed {
    in a?
    in b?
    in c?
    in d?
    pub det out three? := at_most_one?(a?, b?, c?)
    pub det out turned? := at_most_one?(b?, a?, c?)
    pub det out four? := at_most_one?(a?, b?, c?, d?)
    pub det out exactly? := exactly_one?(a?, b?, c?)
    pub det out after? := exactly_one?(c?, a?, b?)
}

refine manual_at_most_one_sound: manual_at_most_one_fixed refines manual_at_most_one_written
refine manual_at_most_one_complete: manual_at_most_one_written refines manual_at_most_one_fixed
```

It does not fire where an operand gives an obligation, which `deny`
checks here, with an index in a `where` clause's definition and with a
table:

```fren
set_option fren.lint.manual_at_most_one "deny" in
pub comp manual_at_most_one_guarded {
    in q: Seq(Int)
    in i: Int
    in x: Int
    in z?
    pub out indexed?
    pub out tabled?

    ensure indexes: indexed? iff not (ok? and big?) and not (ok2? and big?) and not (ok? and ok2?)
        where ok? := 0 <= i < q.len, ok2? := 0 <= i < q.len and z?, big? := q[i] > 0
    ensure tables: tabled? iff not (pos? and t?) and not (pos2? and t?) and not (pos? and pos2?)
        where pos? := x > 0, pos2? := x > 0 and z?, t? := table { x > 0 => true }
}
```
