# Meaning

Many lints are right because of what an expression means, as the
[core](../Lang/Meaning.md) of the language states it: `x - x` is always
`0` because its two operands have the same value, and a constraint that
mentions no variable is the same in every behaviour. This chapter states
the model of an expression as written that those lints share, and how it
meets the core; each lint states its own claim over it.

```fren
pub mod lint

use lang
```

## Expressions as written

Lints compare expressions as they are [written](../Lint.md#written-the-same).
`lint::Operand` is the text of an expression, one of four: two texts are
the same exactly when they are equal, and four are enough to tell every
case of the lints' rules apart.

```fren
pub enum Operand { P, Q, R, S }
```

The same text need not mean the same expression: its names resolve in its
scope, and a pattern test's binders are in scope in some places beside it
and not others (see [`lang::test_scope`](../Lang/Expressions.md#pattern-tests)).
In `if r is Reply::Value(v!) then v else v`, the `then` branch's `v` is the
payload, and the `else` branch's the variable `v`; in `(v > 1 and r is
Reply::Value(v!)) and (v > 1 and r is Reply::Value(v!))`, the right
operand's first `v` is the left's payload. `lint::Scoped` is an expression
as written in its scope: its text, and the binders of pattern tests in
scope where it is written, each by the `Id` of its declaration, as a
`Binder` head names it (see [Layers](../Lang/Meaning.md#layers)). Names
declared outside every pattern test are the same wherever the lints
compare expressions, within one procedure or one global expectation, so
they are not part of the scope. Both front ends compare scopes as well as
texts, with `writtenSameIn`, or leave the expressions whose scopes may
differ.

```fren
pub struct Scoped { text: Operand, scope: Set<lang::Id> }
```

An expression as written is one [layer](../Lang/Meaning.md#layers) at its
root, with parts as written. `written_head(x)` is the head of that layer:
with the same text and the same binders, an expression has the same names,
of the same declarations, and so the same head. `written_values(env, x)`
is its parts' values in the environment `env`. That it is a function is
the law [`same_written`](../Lang/MeaningLaws.md) of each part, by induction
from the leaves up (see [The whole tree](../Lang/MeaningLaws.md#the-whole-tree)):
parts with the same text and binders have the same head, and the same
parts' values, in one environment, and so the same value.

```fren
pub fn written_head(Scoped): lang::Head
pub fn written_values(lang::Env, Scoped): Seq<lang::Value>
```

So, by `same_written` of the roots, two expressions written the same in
the same scope have the same value in one environment, specified or not:
`[1][5] = [1][5]` holds in every behaviour, though `[1][5]` may differ
between them. Here `p` and `q` are their root layers:

```fren
-- It quantifies over scopes, which are sets of names.
set_option fren.lint.undecidable "allow" in
expect written_same: forall (x y: Scoped) (p q: lang::node),
    when x = y and p.env = q.env and p.program = q.program and p.head = written_head(x) and p.values = written_values(p.env, x)
    and q.head = written_head(y) and q.values = written_values(q.env, y),
    p.value = q.value
```

Two texts in different scopes may have different values.
`lint::written_scopes` is the two `v`s of the conditional above: in the
`then` branch, the binder of the payload of the scrutinee `r`, and in the
`else` branch, the variable `v`, in one environment:

```fren
pub proc written_scopes(program: lang::Program, env: lang::Env) {
    call payload := lang::node(
        program,
        lang::Head::Binder("Reply::Value.0"),
        env,
        [lang::lookup(env, "r")],
        {lang::Mention::Var("r")},
        {},
    )
    call outer := lang::node(
        program,
        lang::Head::Variable("v"),
        env,
        [],
        {},
        {},
    )

    cover differ: payload.value != outer.value
}
```

## Expressions that mention nothing

What an expression mentions is a set of `lang::Mention`s, as
[`lang::mentions`](../Lang/Expressions.md#mentions) gives it. One that
mentions nothing has the same value in every environment where each of its
layers that is evaluated is specified: by [`own_mentioned`](../Lang/MeaningLaws.md), its
root reads the same in every environment, and by `frame` it then has the
same value, given the same parts' values, which by induction it has (see
[The whole tree](../Lang/MeaningLaws.md#the-whole-tree)). Where an evaluated layer is not
specified, as in `get([1], 5)` with `fn get(q: Seq<Int>, i: Int): Int :=
q[i]`, its value is the environment's to choose, so it may differ between
behaviours; the [definedness check](../Check.md#definedness) reports that
index, so in a spec that passes its checks the value is the same. Here `p`
is the root layer in one environment and `q` the same layer, with the same
parts' values, in any other:

```fren
expect mentions_nothing: forall (p q: lang::node),
    when p.mentioned = {} and p.specified? and q.program = p.program and q.head = p.head and q.values = p.values,
    q.value = p.value
```
