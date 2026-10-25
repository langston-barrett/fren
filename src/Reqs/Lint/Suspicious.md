# Suspicious

The lints of the `suspicious` group find what is probably not what the
writer meant. This chapter has the lints of names, of constraints and of
the spacing of negations, and its subchapters the others: those of
[expressions](Suspicious/Expressions.md), of [methods and
indexes](Suspicious/Methods.md), of [literals](Suspicious/Literals.md) and of
[comparisons](Suspicious/Comparisons.md).

## Repeated constraints

`duplicate_constraint` fires on a constraint of a component that is
written the same as an earlier one of the component, whatever their
kinds, `assume`, `req` or `expect`, and on a global expectation written
the same as an earlier one of its module in the same file. A cover goal
is not a constraint, and is not compared. Two
constraints are written the same if their expressions are (see
[Written the same](../Lint.md#written-the-same)), and two global
expectations if all they say after their names is, binders included. It is
reported at the later one's name, and the message names the first one it
repeats.

Of two `req`s that say the same, the [redundancy
check](../Check.md#redundancy) reports each as following from the other,
which invites removing both; this lint says which to remove. Two
expectations that say the same are reported by no check. Where the two are
of one kind, the fix removes the later one, with a `--` comment after it
on its last line, and for a global expectation any `set_option ... in`
before it. This keeps the meaning: a constraint
that repeats one of its kind adds nothing to the component, and an
expectation that repeats one claims nothing more. An `expect` that repeats
a `req` or an `assume` is not fixed: it tests nothing, since it follows
from what it repeats, and was probably meant to say something stronger,
which the message says. Nor is a `req` that repeats an `assume`, or the
reverse, since the two mean different things. `lint::duplicate_constraint`
states this:

```fren
pub mod lint

pub enum ConstraintKind { Assume, Req, Expect }

pub comp duplicate_constraint {
    in earlier: ConstraintKind
    in later: ConstraintKind
    in same?             -- the later is written the same as the earlier
    pub det out fires?
    pub det out fixed?   -- the fix removes the later

    req rule: fires? iff same?
    req fix: fixed? iff (same? and earlier = later)

    expect weaker_kept: when later = ConstraintKind::Expect and earlier != later, not fixed?
}
```

## Negations after operators

`suspicious_unary_op_formatting` fires on a binary operator that is a
[punctuator](../Lang/Lexical.md#punctuators), directly followed by a
negation, `-`, that whitespace follows, as in `x >=- 1`, `a =- b` and `a
*- b`: the reader may take the operator and the `-` for one operator.
`-` itself is never directly followed by a `-`, which starts a comment,
and `<` never is, since `<-` is one punctuator, an
[error](../Lang/Lexical.md#punctuators). The lint looks only at the text,
in any constraint, binding, definition, constant or global expectation,
and is fixable. The fix moves the whitespace from after the `-` to before
it, so `x >=- 1` becomes `x >= -1`, and keeps the rest as it is written;
before an operand that starts with `-`, it keeps one space after the `-`
too, as in `x >= - -1`. Only whitespace moves, so the fix changes neither
the meaning nor the guards. [`fren fmt`](../Fmt.md) writes the negation so
too. `lint::suspicious_unary_op_formatting` states when it fires:

```fren
pub comp suspicious_unary_op_formatting {
    in punctuator?       -- the operator is a punctuator other than `-`
    in adjacent?         -- the `-` directly follows it
    in spaced?           -- whitespace directly follows the `-`
    pub det out fires?

    req rule: fires? iff (punctuator? and adjacent? and spaced?)
}
```
