# Meaning

The rules of the other chapters rest on a few facts about what an
expression means: an expression that mentions no variable has the same
value in every behaviour, where it is specified, which is why `2 * x` is
linear; the same expression has the same value wherever it is written,
which is what a lint such as `eq_op` relies on. This chapter states that
meaning once, as a model that the other chapters
[instantiate](Instances.md) or [refine](Refinement.md), so that the rules
are stated over it rather than over facts given as inputs.

```fren
pub mod lang
```

## Values

`lang::Val` is the value of an expression, of any type: a `Bool`, an
`Int` (a `Nat` too), a `String`, a list, or a value of an enumeration,
record or newtype, by its variant, record or newtype and its payload's or
fields' values as a list, a record's in the order the record declares its
fields. A sequence is a list of its elements, and a set or relation a list
of its members, in an order the spec does not fix. A list is `Nil` or
`Cons(v, rest)`, since an enumeration may not contain itself within a
sequence (see [Sequences](Types.md#sequences)). A value of an abstract
type is not one of these: it is read from the environment, and compared
only with `=`. Names, of variables, functions, constants, variants and
operators, are `Id`s, `String`s as they are written, so that a payload can
hold them:

```fren
pub type Id := String

pub enum Val { B(Bool), I(Int), S(String), Nil, Cons(Val, Val), C(Id, Val) }
```

## Layers

An expression is a tree of *layers*. Each layer is a `lang::Head`, the
form of the expression at its root with everything in it that is not an
expression, and has the expressions below it as its *parts*: `x + f(y)` is
the layer `Op("+", "")` with parts `x` and `f(y)`, and `f(y)` is the layer
`Uninterpreted("f")` with the part `y`.

- `Literal(v)` is a literal, with its value `v`, and `Bound(v)` is a
  [quantifier's](Quantifiers.md) bound name of a listed type, with its
  value `v` in one instance of the quantifier.
- `Constant(c)` is a [constant](Items.md#constants), a variant without a
  payload, or another path of more than one segment.
- `Variable(x)` is a variable of the component or of one of its
  [instances](Instances.md#instance-variables), or a field read from one,
  as `x` or `w.x`, or the bound name of an [unbounded
  quantifier](Quantifiers.md#unbounded-quantifiers), which stands for
  every value of its type at once.
- `Definition(x)` is a [defined output](Components.md#defined-outputs) or
  a name of a [`let` or `where`](Let.md), whose one part is its
  definition.
- `Binder(b)` is a binder of a [`match` arm](Expressions.md#matches) or of
  a [pattern test](Expressions.md#pattern-tests), whose one part is its
  scrutinee. `b` is not its name but where its pattern declares it: the
  variants and fields that lead from the pattern's root to it, such as
  `Pair.1` for `y` in `Pair(_, y)`. So the `y` of `Pair(y, _)` is another
  head, and a binder never shares a head with a name of a `let`.
- `Construction(c, order)` is a
  [variant](Expressions.md#variants-with-payloads), a [record
  literal](Expressions.md#records) or a [newtype](Expressions.md#newtypes)
  `c` built from its parts. A record literal's parts are its fields'
  values in the order the record declares them, and `order` is the order
  in which they are written, which does not change the value.
- `Method(m)`, `Uninterpreted(f)` and `Defined(f)` are a
  [method](Expressions.md#methods) call, whose parts are its receiver and
  arguments, and applications of an uninterpreted and of a defined
  [function](Items.md#functions), whose parts are the arguments.
- `Op(o, s)` is any other expression, named by its operator `o`, with its
  static parts `s`: an operator, `when` and `unless`, a conditional, a
  `match` (whose parts are its scrutinee and its arms' guards and bodies,
  and whose static parts are its arms' patterns), a
  [table](Expressions.md#tables), a [pattern
  test](Expressions.md#pattern-tests) (with its pattern), a [cardinality
  operator](Expressions.md#cardinality), indexing, a field read from an
  expression that is not a name (with the field), a [record
  update](Expressions.md#record-updates) (with the fields it sets), a
  literal of a set, pair or sequence, and a `let` (whose only part is its
  body).

A [quantifier](Quantifiers.md) is not one layer: its body is evaluated at
every value of its bound names, so its value is not a function of one
value of each part. Its body's layers are, each in one instance, or with
its bound names read from the environment. A later slice of the model
states quantifiers.

```fren
pub enum Head {
    Literal(Val),
    Bound(Val),
    Constant(Id),
    Variable(Id),
    Definition(Id),
    Binder(Id),
    Construction(Id, Id),
    Method(Id),
    Uninterpreted(Id),
    Defined(Id),
    Op(Id, Id),
}
```

What an expression mentions is named apart, so that a variable and a
function of the same name are two mentions:

```fren
pub enum Mention { Var(Id), Fn(Id) }
```

## Environments

An `Env` is a behaviour together with an [interpretation](Components.md#interpretations)
of the spec's abstract types and functions: everything that the spec
does not fix, including the values of the bound names of unbounded
quantifiers. It is read in three ways: `lookup(env, x)` is the value of
the variable or bound name `x`, `meaning(env, f, args)` the value of the
uninterpreted function `f` at the arguments `args`, and
`unspecified(env, head, parts)` the value of a layer where the language
leaves it unspecified. These three are all an expression reads of its
environment.

Everything else a spec fixes: `fixed_value(head, parts)` is the value of a
layer whose meaning the spec states, at its parts' values: the value of a
constant, the body of a defined function at its arguments, a method, the
part of a scrutinee's value where a binder is declared, and an operator.
`fixed_specified?(head, parts)` says that it is specified. It is not where
the operator is an [index out of range](Expressions.md#sequences), a
`match` or table where no arm is taken, or a binder whose scrutinee does
not have its variant, and not where a constant's value or a defined
function's body is unspecified, or applies a function outside its
[preconditions](Items.md#contracts) (see
[Definedness](../Check.md#definedness)). Neither function takes an `Env`,
so neither differs between behaviours. Their values are stated by the
chapters on each construct; this chapter needs only that they are
functions.

`unspecified` is coarser than the language: it may give each head and
parts' values a value of its own, while the language gives every `match`
where no arm is taken, and every table where no row holds, of one type,
the same value, that of `[][0]` (see [Tables](Expressions.md#tables)), and
an index out of range the value of one unknown function of the sequence
and the position. What holds of every `unspecified` holds of the
language's.

```fren
pub type Env

pub fn lookup(Env, Id): Val
pub fn meaning(Env, Id, Val): Val
pub fn unspecified(Env, Head, Val): Val

pub fn fixed_value(Head, Val): Val
pub fn fixed_specified?(Head, Val)
```

## One layer

The value of a layer is `step` of its head, its environment and its
parts' values: a literal is its value, a variable is read from the
environment, a definition has its one part's value, a construction is its
variant and its parts, an application of an uninterpreted function is
read from the environment at the function and its arguments, and every
other layer has the value the spec fixes where that is specified, and the
unspecified one elsewhere. `step` is a function with a contract, rather
than a defined function, since it applies the functions above, and a
defined function applies no uninterpreted function (see [Defined
functions](Items.md#defined-functions)). Its postcondition determines it:

```fren
-- The value of a layer's only part, the first of its parts' values.
pub fn only_part(values: Val): Val := match values {
    Val::Cons(v, _) => v,
    _ => values,
}

pub fn step(head: Head, env: Env, values: Val): Val
    ensure layer: step(head, env, values) = match head {
    Head::Literal(v) => v,
    Head::Bound(v) => v,
    Head::Variable(x) => lookup(env, x),
    Head::Definition(_) => only_part(values),
    Head::Construction(c, _) => Val::C(c, values),
    Head::Uninterpreted(f) => meaning(env, f, values),
    _ => if fixed_specified?(head, values) then fixed_value(head, values) else unspecified(env, head, values),
}
```

What a layer *mentions* is the set of the variables and uninterpreted
functions whose values it may depend on, from what its parts mention
together (see [Mentions](Expressions.md#mentions)): a variable mentions
itself, an application of an uninterpreted function the function and what
its arguments mention, a literal, a bound name of a listed type and a
constant nothing, and every other layer what its parts mention, since its
meaning is fixed:

```fren
pub fn mentioned_by(head: Head, parts_mentioned: Set(Mention)): Set(Mention) := match head {
    Head::Literal(_) | Head::Bound(_) | Head::Constant(_) => {},
    Head::Variable(x) => {Mention::Var(x)},
    Head::Uninterpreted(f) => parts_mentioned union {Mention::Fn(f)},
    _ => parts_mentioned,
}
```

`lang::node` is one layer. Its inputs are its head, its environment, its
parts' values as a list, and what its parts mention, together; a literal,
a bound name, a constant and a variable have no parts, so theirs mention
nothing. Its `value` is its `step`, and `mentioned` what it mentions.
`read` is what it reads of the environment at its own name: a variable's
value, or an uninterpreted function's at the parts' values, and `Nil` for
a layer that has no name of its own to read at. `specified?` says that its
value is not the unspecified one:

```fren
pub comp node {
    use self::Head::{Bound, Constant, Construction, Definition, Literal, Uninterpreted, Variable}
    in head: Head
    in env: Env
    in values: Val                   -- its parts' values, in order, as a list
    in parts_mentioned: Set(Mention)  -- what its parts mention, together

    assume leaves: when head is Literal(_) | Bound(_) | Constant(_) | Variable(_), parts_mentioned = {}

    pub det out value: Val := step(head, env, values)
    pub det out mentioned: Set(Mention) := mentioned_by(head, parts_mentioned)
    pub det out mentions? := mentioned != {}
    pub det out read: Val := match head {
        Variable(x) => lookup(env, x),
        Uninterpreted(f) => meaning(env, f, values),
        _ => Val::Nil,
    }
    pub det out specified? := match head {
        Literal(_) | Bound(_) | Variable(_) | Definition(_) | Construction(_, _) | Uninterpreted(_) => true,
        _ => fixed_specified?(head, values),
    }

    -- What a part mentions, the whole does, and so does a layer's own name.
    expect parts_kept: parts_mentioned subset mentioned
    expect own_name: match head {
        Variable(x) => Mention::Var(x) in mentioned,
        Uninterpreted(f) => Mention::Fn(f) in mentioned,
        _ => true,
    }
    -- Only a layer whose value the spec fixes can be unspecified.
    expect fixed_only: when head is Literal(_) | Bound(_) | Variable(_) | Definition(_) | Construction(_, _)
        | Uninterpreted(_), specified?
}
```

## Laws

Four laws relate behaviours of `node`. Each is about one layer, so the
solver decides it.

`frame`: a specified layer reads its environment only at its own name. Two
layers with the same head and parts' values that read the same there have
the same value, whatever else their environments hold:

```fren
expect frame: forall (p q: node),
    when p.head = q.head and p.values = q.values and p.specified? and p.read = q.read, p.value = q.value
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
    when p.head = q.head and p.values = q.values and p.env = q.env, p.value = q.value
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
not specified, as `get([1], 5)` is with `fn get(q: Seq(Int), i: Int): Int
:= q[i]`, its value is read from the environment, so it need not be the
same in every behaviour, though it mentions nothing.

A function in Fren is not recursive (see [Defined
functions](Items.md#defined-functions)), so the tree is not a value here:
each fact is stated of one layer, and the induction is stated in prose.
FrenCore's walks over expressions are bound to the layers by
[implementations](../Impl.md) proved in Lean for every tree, as
`lang::mentions` is.
