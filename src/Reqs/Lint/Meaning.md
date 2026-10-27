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
`lint::Operand` is an expression as written, one of four: two are written
the same exactly when they are equal, and four are enough to tell every
case of the lints' rules apart.

```fren
pub enum Operand { P, Q, R, S }
```

Within one scope, an expression as written is one [layer](../Lang/Meaning.md#layers)
at its root, with parts as written. `written_head(x)` is the head of that
layer: written the same, an expression has the same names, of the same
declarations, and so the same head. `written_values(env, x)` is its parts'
values in the environment `env`, as a list. That it is a function is the
law [`same_written`](../Lang/Meaning.md#laws) of each part, by induction
from the leaves up (see [The whole tree](../Lang/Meaning.md#the-whole-tree)):
parts written the same have the same head, and the same parts' values, in
one environment, and so the same value. The lints compare only
expressions in one scope: the operands of one operator, the branches of one
conditional, the constraints of one component.

```fren
pub fn written_head(Operand): lang::Head
pub fn written_values(lang::Env, Operand): lang::Val
```

So, by `same_written` of the roots, two expressions written the same have
the same value in one environment, specified or not: `[1][5] = [1][5]`
holds in every behaviour, though `[1][5]` may differ between them. Here
`p` and `q` are their root layers:

```fren
expect written_same: forall (x y: Operand) (p q: lang::node),
    when x = y and p.env = q.env and p.head = written_head(x) and p.values = written_values(p.env, x)
    and q.head = written_head(y) and q.values = written_values(q.env, y),
    p.value = q.value
```

## Expressions that mention nothing

What an expression mentions is a set of `lang::Mention`s, as
[`lang::mentions`](../Lang/Expressions.md#mentions) gives it. One that
mentions nothing has the same value in every environment where each of its
layers is specified: by [`own_mentioned`](../Lang/Meaning.md#laws), its
root reads the same in every environment, and by `frame` it then has the
same value, given the same parts' values, which by induction it has (see
[The whole tree](../Lang/Meaning.md#the-whole-tree)). Where a layer is not
specified, as in `get([1], 5)` with `fn get(q: Seq(Int), i: Int): Int :=
q[i]`, its value is the environment's to choose, so it may differ between
behaviours; the [definedness check](../Check.md#definedness) reports that
index, so in a spec that passes its checks the value is the same. Here `p`
is the root layer in one environment and `q` the same layer, with the same
parts' values, in any other:

```fren
expect mentions_nothing: forall (p q: lang::node),
    when p.mentioned = {} and p.specified? and q.head = p.head and q.values = p.values, q.value = p.value
```
