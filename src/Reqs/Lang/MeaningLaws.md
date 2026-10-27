# Laws of meaning

The laws of [Meaning](Meaning.md) relate behaviours of `lang::node`, one
layer of an expression. Each is about one layer, so the solver decides it.

```fren
pub mod lang
```

`frame`: a specified layer reads its environment only at its own name. Two
layers of one program with the same head and parts' values that read the
same there have the same value, whatever else their environments hold:

```fren
expect frame: forall (p q: node),
    when p.program = q.program and p.head = q.head and p.values = q.values and p.specified? and p.read = q.read,
    p.value = q.value
```

`own_mentioned`: the name a layer reads at is one that it mentions, so a
layer that mentions nothing reads the same in every environment:

```fren
expect own_mentioned: forall (p q: node),
    when p.head = q.head and p.values = q.values and p.mentioned = {}, p.read = q.read
```

`same_written`: the same head and parts' values in the same environment
give the same value, specified or not:

```fren
expect same_written: forall (p q: node),
    when p.program = q.program and p.head = q.head and p.values = q.values and p.env = q.env, p.value = q.value
```

`unevaluated`: the parts that a layer does not evaluate change neither its
value nor its definedness. Two layers with the same head and environment
whose parts agree, in their values and in whether they are defined, at
every position that the first evaluates, have the same value, and are
defined alike. This is the law behind the [definedness
check](../Check.md#definedness), which asks whether an index is in range
only under its guard. `node` states the guards of the parts at positions
up to 6, which `PartAt` names, so the law is stated of layers with at
most seven parts:

```fren
expect unevaluated: forall (p q: node),
    when p.program = q.program and p.head = q.head and p.env = q.env and p.values.len = q.values.len
    and p.values.len <= 7
    and (forall (j: PartAt), when not j in p.unevaluated, part(p.values, j) = part(q.values, j))
    and p.undefined_parts minus p.unevaluated = q.undefined_parts minus p.unevaluated,
    p.value = q.value and (p.defined? iff q.defined?)
```

`frame_mentioned`: environments that agree on what a specified layer
mentions give it the same value, so a specified layer that mentions
nothing has the same value in every environment; a defined layer is
specified, so this holds of it too. It is stated the other way round:
where two environments give a specified layer different values, they
differ at something that it mentions, a variable, or a function at the
layer's parts' values, its arguments. Its unbounded quantifiers range over
the names at which they differ, so it is outside the [decidable
core](Decidability.md#what-is-promised); the solver proves it by
instantiating them at the layer's own name:

```fren
set_option fren.lint.undecidable "allow" in
expect frame_mentioned: forall (p q: node),
    when p.program = q.program and p.head = q.head and p.values = q.values and p.specified? and p.value != q.value,
    (exists (x: Id), Mention::Var(x) in p.mentioned and lookup(p.env, x) != lookup(q.env, x))
    or (exists (f: Id), Mention::Fn(f) in p.mentioned and meaning(p.env, f, p.values) != meaning(q.env, f, p.values))
```

`field_order`: a construction's value does not depend on the order in
which its fields are written, only on what it builds and its parts' values,
which are in the order of the declaration:

```fren
-- What a construction builds, and whether a head is a construction.
pub fn built(head: Head): Id := match head {
    Head::Construction(c, _) => c,
    _ => "",
}

pub fn construction?(head: Head) := head is Head::Construction(_, _)

expect field_order: forall (p q: node),
    when construction?(p.head) and construction?(q.head) and built(p.head) = built(q.head) and p.values = q.values,
    p.value = q.value
```

## Declarations

`constant_fixed`: a constant has the same value in every environment,
where it is specified, which is why a constant may be a factor of a
product or a divisor (see [Linear
arithmetic](Expressions.md#linear-arithmetic)):

```fren
expect constant_fixed: forall (p q: node),
    when p.program = q.program and p.head = q.head and p.head is Head::Constant(_) and p.values = q.values
    and p.specified?,
    p.value = q.value
```

`substitution`: where a constant or an application of a defined function
is specified, its value is its definition's at the parts' values: the
arguments substituted for the parameters, as [Defined
functions](Items.md#defined-functions) states:

```fren
expect substitution: forall (p: node),
    when (p.head is Head::Constant(_) | Head::Defined(_)) and p.specified?,
    p.value = definition_value(p.program, declared(p.head), p.values)
```

## The whole tree

The laws hold of whole expressions by induction on the tree: what holds
of every layer, given that it holds of the layer's parts, holds of every
expression. For example, an expression that mentions nothing has the same
value in every environment, where each of its layers is specified. Its
root mentions nothing, so by `parts_kept` none of its parts does, and by
induction each part has the same value in every environment. With the
same parts' values, by `own_mentioned`, the root reads the same in every
environment, and so by `frame` it has the same value. Likewise, by
`same_written`, the same expression has the same value wherever it is
written in one behaviour. The rules that an operand of `*` mention nothing
(see [Linear arithmetic](Expressions.md#linear-arithmetic)) and that the
operands of a string operation be constants (see
[Strings](Decidability.md#strings)) rest on the first. Where a layer is
not specified, as `get([1], 5)` is with `fn get(q: Seq<Int>, i: Int): Int
:= q[i]`, its value is read from the environment, so it need not be the
same in every behaviour, though it mentions nothing.

A function in Fren is not recursive (see [Defined
functions](Items.md#defined-functions)), so the tree is not a value here:
each fact is stated of one layer, and the induction is stated in prose.
FrenCore's walks over expressions are bound to the layers by
[implementations](../Impl.md) proved in Lean for every tree, as
`lang::mentions` is. `lang::node` is proved of FrenCore's evaluation of
one layer, which its evaluator folds over a tree, and the first induction
above is proved in Lean of that evaluator, for an expression each of
whose layers is specified there: in the fragment that
[Environments](Meaning.md#environments) lists. So is `fixed_value`'s
`declared`, of every program, by the order of its declarations. No front
end evaluates through it yet, so that Fren follows the model is trusted
until they do.
