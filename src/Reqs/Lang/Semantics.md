# Dynamic semantics

This chapter defines what an expression evaluates to. The rules of the
other chapters are stated over it: a constraint that mentions no variable
is the same in every behaviour because of the [coincidence
lemma](EvaluationRules.md#free-variables), and `a and b` may index out of range in `b`
because `b` is not evaluated where `a` is false (see
[Guards](EvaluationRules.md#guards)).

The semantics is big-step, in the style of the dynamic semantics of the
Definition of Standard ML and of chapter 3 of Pierce's *Types and
Programming Languages*. Its sections follow the Rust Reference's chapter
on expressions, and [Rules of evaluation](EvaluationRules.md) states the
rule of each form.

**Dynamic semantics**

r[semantics.eval.big-step]
One function, `lang::eval`, gives the outcome of an expression in an
interpretation and an environment. It has one rule for each form of
expression, over the outcomes of the form's immediate subexpressions, some
of them evaluated in an environment that the outcome or value of another
gives (`semantics.eval.outcomes`).

r[semantics.derived-forms]
A form of the source language that is not in the [abstract
syntax](#abstract-syntax) is a *derived form*, defined by its translation
into it (see [Derived forms](#derived-forms)).

```fren
pub mod lang
```

## Values

A value is the result of evaluating an expression that is well-defined.

**Dynamic semantics**

r[semantics.value]
`lang::Value` is the value of an expression, of any type.

r[semantics.value.bool]
`True` and `False` are the values of `Bool`.

r[semantics.value.integer]
`Integer(n)` is a value of `Int` or of `Nat`.

r[semantics.value.text]
`Text(s)` is a value of `String`.

r[semantics.value.list]
`Nil` and `Cons(v, rest)` are lists. The value of a sequence is the list
of its elements, in order. The values of a payload, and those of a
record's fields, are lists too.

r[semantics.value.constructed]
`Constructed(c, l)` is a value of an enumeration, record or newtype. `c` is
the full path of the variant, record or newtype, and `l` is the list of the
values of its payload or of its fields. A record's fields are in the order
in which the record declares them.

r[semantics.value.excluded]
Sets, relations and values of abstract types are not values of this
model (see [What the model leaves out](#what-the-model-leaves-out)).

r[semantics.value.truth]
`truth(b?)` is `True` where `b?` holds, and `False` where it does not.

> **Note:** `True` and `False` are constructors of `Value`, as those of
> `bool` are in Standard ML.

```fren
pub enum Value {
    True,
    False,
    Integer(Int),
    Text(String),
    Nil,
    Cons(Value, Value),
    Constructed(Id, Value),
}

-- The value of a `Bool`.
pub fn truth(b?): Value := if b? then Value::True else Value::False
```

## Outcomes and well-definedness

An expression's value is either fixed by the semantics, or unspecified.

**Dynamic semantics**

r[semantics.outcome]
An expression's *outcome* is `Defined(v)`, its value `v`, or `Undefined`
(`lang::Outcome`).

r[semantics.outcome.well-defined]
An expression is *well-defined* (WD) in an environment where its outcome
is defined.

r[semantics.outcome.undefined]
An expression that is not WD, such as `[][0]` or a `match` where no arm is
taken, still has a value in each behaviour. That value is unspecified, and
the checks hold for every choice of it, as they hold for every
interpretation of an uninterpreted function (see
[Definedness](../Check.md#definedness)).

r[semantics.outcome.undefined.unfixed]
The outcome `Undefined` says only that the semantics does not fix the
value. A rule that holds of every defined outcome holds of the language's
value there.

r[semantics.outcome.strict]
Evaluation is *strict*. An expression is WD only where each immediate
subexpression that it evaluates is WD.

r[semantics.outcome.lazy-forms]
The forms that do not evaluate every immediate subexpression are `And`,
`Or`, `If`, `Match` and `Let`. The definition of a `Let` is evaluated only
where its name is (see [Let expressions](EvaluationRules.md#let-expressions)).

> **Note:** TLA+ treats `[][0]` alike, as a "silly expression".

```fren
pub enum Outcome { Defined(Value), Undefined }
```

## Abstract syntax

The abstract syntax is the expression that the checker evaluates, once
the source is elaborated.

**Syntax**

r[semantics.syntax]
The abstract syntax is that of an expression after
[elaboration](Types.md#checking-and-synthesis). Every name is
[resolved](Scope.md), every type is checked, and every derived form is
translated.

r[semantics.syntax.paths]
A variant, record, newtype or function is named by its full path, as in
`Shape::Circle`.

r[semantics.syntax.names]
A variable is named by a `V`. The abstract syntax is generic in the type
`V` of the names of variables, of which nothing is known but whether two
of them are equal. `lang::Pattern<V>`, `lang::Params<V>` and
`lang::Expr<V>` take it as their type parameter.

r[semantics.syntax.names.id]
The semantics evaluates `Expr<Id>`, whose names are `Id`s, as they are
written. Another type of names, such as a [binding](Scope.md#bindings) for
each, can stand for the names once they are resolved, with the same forms.

r[semantics.syntax.names.generic]
A function that is generic in `V` knows of names only whether two are
equal, and the type's `Inhabited` default. Renaming every name of an
expression apart changes nothing that such a function computes but the
names.

r[semantics.syntax.names.recursion]
A recursion over the abstract syntax, as `eval` is, takes one type of
names, as `Id`. A generic function is [not recursive](Recursion.md).

r[semantics.syntax.lists]
No form needs a sequence of a type parameter. A form with a list of
operands has a list expression for them (see
[Expressions](#expressions)).

> **Note:** The renaming of `semantics.syntax.names.generic` is proved of
> the [lints' rules](../Lint/Rewrites.md#renaming), each by its
> definition. A generic type cannot have a sequence of a type parameter yet
> ([Type parameters](Generics.md#type-parameters)).

### Patterns

**Syntax**

r[semantics.syntax.pattern]
`lang::Pattern<V>` is a pattern of [Patterns](Patterns.md). Its forms are
`Wildcard`, a `Binder(x)`, a `Literal(v)`, the integer ranges
`AtLeast(lo)` (`lo..`), `AtMost(hi)` (`..=hi`) and `Between(lo, hi)`
(`lo..=hi`), `Variant(c, ps)`, where `ps` is a list pattern for the
payload's values, and an or-pattern `Or(a, b)`.

r[semantics.syntax.pattern.exclusive-range]
The range `lo..hi` is `Between(lo, hi - 1)`.

r[semantics.syntax.pattern.list]
A list pattern is `Nil` or `Cons(p, ps)`, as a list is. It also matches the
list of the scrutinees of a `match` with [several
scrutinees](HigherOrder.md#lambda-matches-and-multiple-scrutinees).

```fren
pub enum Pattern<V> {
    Wildcard,
    Binder(V),
    Literal(Value),
    AtLeast(Int),
    AtMost(Int),
    Between(Int, Int),
    Variant(Id, Pattern<V>),
    Nil,
    Cons(Pattern<V>, Pattern<V>),
    Or(Pattern<V>, Pattern<V>),
}
```

### Expressions

Each form of expression, an example of its source, and the section of
[Rules of evaluation](EvaluationRules.md) that gives its rule:

| Form | Source | Section |
|---|---|---|
| `Literal(v)` | `3`, `"a"`, `true` | [Literal expressions](EvaluationRules.md#literal-expressions) |
| `Var(x)` | `x` | [Path expressions](EvaluationRules.md#path-expressions) |
| `Let(x, d, b)` | `let x := d in b` | [Let expressions](EvaluationRules.md#let-expressions) |
| `Unary(op, a)` | `not a`, `-a` | [Operator expressions](EvaluationRules.md#operator-expressions) |
| `Binary(op, a, b)` | `a + b`, `a = b`, `a < b`, ... | [Operator expressions](EvaluationRules.md#operator-expressions) |
| `And(a, b)`, `Or(a, b)` | `a and b`, `a or b` | [Lazy Boolean expressions](EvaluationRules.md#lazy-boolean-expressions) |
| `If(c, t, f)` | `if c then t else f` | [If expressions](EvaluationRules.md#if-expressions) |
| `Is(s, p)` | `s is p` | [Match expressions](EvaluationRules.md#match-expressions) |
| `Match(s, p, g, b, rest)`, `NoMatch` | `match s { p if g => b, ... }` | [Match expressions](EvaluationRules.md#match-expressions) |
| `Nil`, `Cons(a, rest)` | `[a, ...]` | [List expressions](EvaluationRules.md#list-expressions) |
| `Construct(c, args)` | `C(a, b)`, `R { x := a }` | [List expressions](EvaluationRules.md#list-expressions) |
| `Project(a, c, k)` | `r.x`, `n.0` | [List expressions](EvaluationRules.md#list-expressions) |
| `Index(q, k)` | `q[k]` | [List expressions](EvaluationRules.md#list-expressions) |
| `Method(m, r, args)` | `x.abs`, `x.min(y)`, `q.len` | [Method call expressions](EvaluationRules.md#method-call-expressions) |
| `Count(c, args)` | `at_most_one?(a, b)` | [Operator expressions](EvaluationRules.md#operator-expressions) |
| `Apply(f, args, ps, body)` | `f(a)`, a constant `C` | [Call expressions](EvaluationRules.md#call-expressions) |
| `Call(f, args)` | `f(a)`, `f` uninterpreted | [Call expressions](EvaluationRules.md#call-expressions) |
| `Recur(f, args)` | `f(a)`, `f` a structural recursion | [Call expressions](EvaluationRules.md#call-expressions) |

**Syntax**

r[semantics.syntax.expr]
`lang::Expr<V>` is an expression.

r[semantics.syntax.expr.lists]
A form with a list of operands, such as the arguments of a call, has a list
expression for them, `Nil` or `Cons(e, rest)`, which evaluates to the list
of their values.

```fren
pub enum UnaryOp { Not, Neg }

pub enum BinaryOp { Eq, Lt, Le, Add, Sub, Mul, Div, Mod, Concat, In }

pub enum MethodName { Abs, Min, Max, Len }

-- The cardinality operators: `exactly_one?` and `at_most_one?`.
pub enum Cardinality { Exactly, AtMost }

-- A function's parameters, in order.
pub enum Params<V> { Nil, Cons(V, Params<V>) }

pub enum Expr<V> {
    Literal(Value),
    Var(V),
    Let(V, Expr<V>, Expr<V>),
    Unary(UnaryOp, Expr<V>),
    Binary(BinaryOp, Expr<V>, Expr<V>),
    And(Expr<V>, Expr<V>),
    Or(Expr<V>, Expr<V>),
    If(Expr<V>, Expr<V>, Expr<V>),
    Is(Expr<V>, Pattern<V>),
    Match(Expr<V>, Pattern<V>, Expr<V>, Expr<V>, Expr<V>),
    NoMatch,
    Nil,
    Cons(Expr<V>, Expr<V>),
    Construct(Id, Expr<V>),
    Project(Expr<V>, Id, Int),
    Index(Expr<V>, Expr<V>),
    Method(MethodName, Expr<V>, Expr<V>),
    Count(Cardinality, Expr<V>),
    Apply(Id, Expr<V>, Params<V>, Expr<V>),
    Call(Id, Expr<V>),
    Recur(Id, Expr<V>),
}
```

### Derived forms

A derived form is written for convenience, and means what its translation
means.

**Dynamic semantics**

r[semantics.derived]
Each derived form is the expression that its rule below gives, after its
own subexpressions are translated.

r[semantics.derived.repeated]
A translation that writes an expression twice, such as the scrutinee of a
`match`, does not change its meaning.

r[semantics.derived.not-equal]
`a != b` is `not (a = b)`.

r[semantics.derived.greater]
`a > b` is `b < a`, and `a >= b` is `b <= a`.

r[semantics.derived.iff]
`a iff b` is `a = b`.

r[semantics.derived.when]
`when c, d` is `if c then d else true`.

r[semantics.derived.unless]
`unless c, d` is `if c then true else d`.

r[semantics.derived.chain]
`a < b < c`, and every [chained comparison](Expressions.md#chained-comparisons)
alike, is `a < b and b < c`.

r[semantics.derived.let]
`let x := d, y := e in b` is `let x := d in let y := e in b`, and
`b where x := d` is `let x := d in b`.

r[semantics.derived.match]
`match s { p if g => b, arms }` is `Match(s, p, g, b, match s { arms })`.
The guard `g` of an arm without a guard is `true`.

r[semantics.derived.match.empty]
`match s {}`, after the last arm, is `NoMatch`.

r[semantics.derived.match.scrutinees]
`match a, b { p, q => e, ... }` is `match [a, b] { [p, q] => e, ... }`, its
patterns as list patterns.

r[semantics.derived.table]
`table { c => v, rows }` is `if c then v else table { rows }`.
`table { _ => v }` is `v`, and `table {}` is `NoMatch`.

r[semantics.derived.table.scrutinee]
`table s { arms }` is `match s { arms }`.

r[semantics.derived.test.and]
`s is p and e`, where `e` reads a binder of `p`, is
`And(Is(s, p), Match(s, p, true, e, NoMatch))`.

r[semantics.derived.test.if]
`if s is p then t else f`, where `t` reads a binder of `p`, is
`If(Is(s, p), Match(s, p, true, t, NoMatch), f)`.

r[semantics.derived.test.when]
`when s is p, d`, where `d` reads a binder of `p`, is
`If(Is(s, p), Match(s, p, true, d, NoMatch), true)`.

r[semantics.derived.test.chain]
In a chain of `and`s after `s is p`, as `s is p and a and e`, each later
operand that reads a binder of `p` is within
`Match(s, p, true, ·, NoMatch)`, at the places where
[`lang::test_scope`](Expressions.md#pattern-tests) has the binders in
scope. That `Match` is evaluated only where the test holds, and never
reaches `NoMatch`.

r[semantics.derived.list]
`[a, b]` is `Cons(a, Cons(b, Nil))`.

r[semantics.derived.variant]
`C`, a variant without a payload, is `Construct(C, Nil)`.

r[semantics.derived.construct]
`C(a, b)` is `Construct(C, [a, b])`, and `N(a)` is `Construct(N, [a])`.

r[semantics.derived.record]
`R { y := b, x := a }` is `Construct(R, [a, b])`, in the order in which `R`
declares `x` and `y`.

r[semantics.derived.field]
`r.x` is `Project(r, R, k)`, where `x` is `R`'s field at position `k`, and
`n.0` is `Project(n, N, 0)`.

r[semantics.derived.update]
`{ r with x := a }` is `Construct(R, ...)` of `R`'s fields: `a` for `x`,
and `Project(r, R, k)` for each other field `k`.

r[semantics.derived.apply]
`f(a, b)`, where `f` is a defined function that is not recursive, with
the parameters `x` and `y` and the body `e`, is
`Apply(f, [a, b], [x, y], e)`.

r[semantics.derived.constant]
`C`, a constant with the definition `e`, is `Apply(C, Nil, Nil, e)`.

r[semantics.derived.call]
`f(a, b)`, where `f` is uninterpreted, is `Call(f, [a, b])`.

r[semantics.derived.call.generic]
An instance of a [generic uninterpreted
function](GenericFunctions.md#uninterpreted-generic-functions) is named
with its type arguments, as `pick<Int>`. Each instance is an unknown
function of its own.

r[semantics.derived.recur]
`f(a, b)`, where `f` is a [structural recursion](Recursion.md), is
`Recur(f, [a, b])`.

r[semantics.derived.higher-order]
Let `h` be a [higher-order function](HigherOrder.md) with the function
parameter `f`, the other parameter `x` and the body `e`, and let `c` be
the closure `|y| d`. `h(c, a)` is `let #0 := z in let x := a in e'`. `e'`
is `e` with each application `f(b)` replaced by `let y := b in d'`, and
`d'` is `d` with each name `z` that it captures renamed to its capture
symbol `#0`.

r[semantics.derived.higher-order.captures]
The names that a closure captures are values, never a function parameter
`g` of an enclosing higher-order function. A closure that applies `g` is
translated within the enclosing application's unfolding, once `g` is
replaced by its closure, as `semantics.derived.function-parameter` states
for `g` itself.

r[semantics.derived.higher-order.unfolding]
The unfolding of an application of a higher-order function is a `let` of
each capture symbol at its name and of each other parameter at its
argument, around the body, as [Meaning](HigherOrder.md#meaning) states.

r[semantics.derived.higher-order.renaming]
The parameters are renamed apart from the names that the arguments
mention, as the capture symbols are. Each argument means what it means
where `h` is applied.

r[semantics.derived.lambda-match]
`match { arms }`, given to a function parameter of `n` parameters, is the
closure `|y1, ..., yn| match y1, ..., yn { arms }`, with names `y1`, ...,
`yn` that `arms` do not mention, as [Lambda
matches](HigherOrder.md#lambda-matches-and-multiple-scrutinees) states.

r[semantics.derived.function-name]
`g`, the name of a defined function, given to a function parameter of `n`
parameters, is the closure `|y1, ..., yn| g(y1, ..., yn)`, which captures
nothing. For a [generic](GenericFunctions.md) `g`, it is the closure of the
instance that the parameter's type gives.

r[semantics.derived.function-parameter]
`f`, a function parameter of the enclosing higher-order function, given to
a function parameter of an application `h(f, a)` in its body, is the
closure that `f` stands for where the enclosing function is applied.
`h(f, a)` is translated within that application's unfolding, once `f` is
replaced by its closure, whose captures are already renamed to capture
symbols. It is not translated before, as the other forms' subexpressions
are.

r[semantics.derived.count]
`exactly_one?(a, b)` is `Count(Exactly, [a, b])`, and
`at_most_one?(a, b)` is `Count(AtMost, [a, b])`.

> **Note:** A translation may write an expression twice because evaluation
> has no effects and is deterministic.

## Environments and interpretations

An expression is evaluated in an environment, which gives its variables,
and an interpretation, which gives its functions.

**Dynamic semantics**

r[semantics.env]
An *environment*, `lang::Env`, binds variables to outcomes: those of a
procedure and of its calls, the parameters of a function, the bound
names of quantifiers, the names of `let`s, and the binders of patterns.

r[semantics.env.lookup]
`lookup(env, x)` is the outcome of the innermost binding of `x`
(`lang::lookup`).

r[semantics.env.unbound]
An unbound variable is undefined. A resolved expression never reads one.

r[semantics.interp]
An *interpretation*, `lang::Interp`, gives three tables of values:
`functions`, `recursions` and `primitives`.

r[semantics.interp.functions]
`functions` gives the values of the spec's uninterpreted functions, which
differ between behaviours.

r[semantics.interp.recursions]
`recursions` gives the values of the spec's [structural
recursions](Recursion.md), which are the same in every behaviour. Each is
the least fixed point of its equations (see [Call
expressions](EvaluationRules.md#call-expressions)).

r[semantics.interp.primitives]
`primitives` gives the *primitive operations*: products and quotients of
two integers, `*`, `div` and `mod`, and concatenations of two strings,
`++`. They are the same in every behaviour.

r[semantics.interp.graph]
Each table is a `Graph`, a finite list of points `Point(f, args, r)`: `f`
at the list of arguments `args` is `r`. Where there are several points for
the same arguments, the first counts.

r[semantics.interp.finite]
Every outcome under an interpretation of the language is that under a
finite one. The rules of this chapter are stated over finite ones.

r[semantics.interp.primitives.meaning]
The language's interpretation gives each primitive its usual meaning, by
Lean's `Int.mul`, `Int.ediv`, `Int.emod` and `String.append`, at every
point that it has.

r[semantics.interp.apply]
`apply(g, f, args)` is `f`'s value at `args` in `g`, and undefined where
the graph has no point for them.

> **Note:** The three tables are kept apart because they vary differently
> between behaviours. An evaluation reads finitely many points, which is
> why a finite interpretation gives every outcome.

> **Rationale:** Fren's own decidable fragment cannot compute the
> primitive operations, so this chapter takes them as given, as the
> Definition of Standard ML takes its basic values from `APPLY` (#391).

```fren
pub enum Env { Empty, Bind(Id, Outcome, Env) }

pub enum Graph { Empty, Point(Id, Value, Value, Graph) }

pub struct Interp { functions: Graph, recursions: Graph, primitives: Graph }

pub fn lookup(env: Env, x: Id): (r: Outcome) {
    out r := match env {
        Env::Empty => Outcome::Undefined,
        Env::Bind(y, bound, rest) => if y = x then bound else lookup(rest, x),
    }

    ensure innermost: match env {
        Env::Bind(y, bound, _) => (when y = x, r = bound),
        Env::Empty => r = Outcome::Undefined,
    }
}

-- `f`'s value at `args`, and undefined where the graph has no point for them.
pub fn apply(g: Graph, f: Id, args: Value): Outcome := match g {
    Graph::Empty => Outcome::Undefined,
    Graph::Point(h, a, r, rest) => if h = f and a = args then Outcome::Defined(r) else apply(rest, f, args),
}
```

r[semantics.env.shadowing]
One binding hides another of the same name (`lang::lookup_binding`).

```fren
expect lookup_binding(env: Env, x: Id, y: Id, r: Outcome) {
    expect innermost: lookup(Env::Bind(x, r, env), x) = r
    expect others: when y != x, lookup(Env::Bind(y, r, env), x) = lookup(env, x)
}
```

## Evaluation

In summary, each form evaluates as follows, and is well-defined exactly
where what it evaluates is, and the operation applies to the values:

| Form | Evaluates | Outcome |
|---|---|---|
| `Literal(v)` | nothing | `v` |
| `Var(x)` | nothing | what the environment binds `x` to |
| `Let(x, d, b)` | `b`, and `d` where `b` reads `x` | `b`'s, with `x` bound to `d`'s outcome |
| `Unary`, `Binary`, `Count` | every operand | the operation at the operands' values |
| `And(a, b)`, `Or(a, b)` | `a`, and `b` where `a` does not decide | `false` (`true`) where `a` is, else `b`'s |
| `If(c, t, f)` | `c`, and the branch that it selects | that branch's |
| `Match(s, p, g, b, rest)` | `s`; `g` where `p` matches; `b` where `g` holds; else `rest` | the first taken arm's body's |
| `Is(s, p)` | `s` | whether `p` matches |
| `Nil`, `Cons`, `Construct` | every element | the list, or the value built |
| `Project(a, c, k)`, `Index(q, k)` | every operand | the element at `k`, where there is one |
| `Method(m, r, args)` | receiver and arguments | the method at their values |
| `Apply(f, args, ps, body)` | the arguments, then `body` | `body`'s, with only `ps` bound |
| `Call(f, args)` | the arguments | the interpretation's `functions` |
| `Recur(f, args)` | the arguments | the interpretation's `recursions` |

The functions of the next sections give each form's rule, and `lang::eval`
applies them.

**Dynamic semantics**

r[semantics.eval.laws]
[Rules of evaluation](EvaluationRules.md) states the rule of each form as
laws over the outcomes of the form's immediate subexpressions, and `eval`
meets them. They are the readable rules, and `eval` refines them, with
every case that they leave out, such as `x + true`, which elaboration
rejects, and whose outcome is undefined.

### Operations on lists

**Dynamic semantics**

r[semantics.list.nth]
`nth(list, k)` is the element of `list` at position `k`, from 0, and is
undefined out of range.

r[semantics.list.length]
`length(list)` is the number of elements of `list`.

r[semantics.list.append]
`append(a, b)` is the list of the elements of `a`, then those of `b`.

r[semantics.list.element]
`element?(v, list)` says that `v` is an element of `list`.

r[semantics.list.is-list]
`list?(v)` says that `v` is a list.

r[semantics.list.trues]
`trues(list)` is the number of elements of `list` that are `True`.

r[semantics.list.booleans]
`booleans?(list)` says that `list` is a list of `Bool`s.

```fren
-- The element at position `k`, from 0, and undefined out of range.
pub fn nth(list: Value, k: Int): (r: Outcome) {
    out r := match list {
        Value::Cons(v, rest) => if k = 0 then Outcome::Defined(v) else if k < 0 then Outcome::Undefined else nth(rest, k - 1),
        _ => Outcome::Undefined,
    }

    ensure first: match list {
        Value::Cons(v, _) => (when k = 0, r = Outcome::Defined(v)),
        _ => r = Outcome::Undefined,
    }
    ensure negative: when k < 0, r = Outcome::Undefined
}

pub fn length(list: Value): Int := match list {
    Value::Cons(_, rest) => 1 + length(rest),
    _ => 0,
}

pub fn append(a: Value, b: Value): Value := match a {
    Value::Cons(v, rest) => Value::Cons(v, append(rest, b)),
    _ => b,
}

pub fn element?(v: Value, list: Value) := match list {
    Value::Cons(w, rest) => w = v or element?(v, rest),
    _ => false,
}

pub fn list?(v: Value) := v is Value::Nil | Value::Cons(_, _)

-- How many of the elements are `true`, and whether all are `Bool`s.
pub fn trues(list: Value): Int := match list {
    Value::Cons(w, rest) => (if w = Value::True then 1 else 0) + trues(rest),
    _ => 0,
}

pub fn booleans?(list: Value) := match list {
    Value::Cons(w, rest) => w is Value::True | Value::False and booleans?(rest),
    Value::Nil => true,
    _ => false,
}
```

### Pattern matching

**Dynamic semantics**

r[semantics.match.matches]
`matches_value?(p, v)` says that `p` matches `v`.

r[semantics.match.bind]
`bind(p, v, env)` is `env` with `p`'s binders bound to the parts of `v`
that they match.

r[semantics.match.or]
An or-pattern binds nothing.

r[semantics.match.params]
`bind_params(ps, args)`, the environment of a function's body, binds its
parameters `ps` to the arguments `args`.

> **Note:** An or-pattern binds nothing because elaboration rejects one
> whose alternatives bind names (`F0333`).

```fren
pub fn matches_value?(p: Pattern<Id>, v: Value) := match p {
    Pattern::Wildcard => true,
    Pattern::Binder(_) => true,
    Pattern::Literal(w) => v = w,
    Pattern::AtLeast(lo) => v is Value::Integer(n) and n >= lo,
    Pattern::AtMost(hi) => v is Value::Integer(n) and n <= hi,
    Pattern::Between(lo, hi) => v is Value::Integer(n) and lo <= n <= hi,
    Pattern::Variant(c, ps) => match v {
        Value::Constructed(d, payload) => c = d and matches_value?(ps, payload),
        _ => false,
    },
    Pattern::Nil => v = Value::Nil,
    Pattern::Cons(first, rest) => match v {
        Value::Cons(w, more) => matches_value?(first, w) and matches_value?(rest, more),
        _ => false,
    },
    Pattern::Or(a, b) => matches_value?(a, v) or matches_value?(b, v),
}

pub fn bind(p: Pattern<Id>, v: Value, env: Env): Env := match p {
    Pattern::Binder(x) => Env::Bind(x, Outcome::Defined(v), env),
    Pattern::Variant(_, ps) => match v {
        Value::Constructed(_, payload) => bind(ps, payload, env),
        _ => env,
    },
    Pattern::Cons(first, rest) => match v {
        Value::Cons(w, more) => bind(rest, more, bind(first, w, env)),
        _ => env,
    },
    _ => env,
}

-- The environment of a function's body: its parameters bound to the arguments.
pub fn bind_params(ps: Params<Id>, args: Value): Env := match ps {
    Params::Cons(x, rest) => match args {
        Value::Cons(v, more) => Env::Bind(x, Outcome::Defined(v), bind_params(rest, more)),
        _ => Env::Empty,
    },
    Params::Nil => Env::Empty,
}
```

### Operators and methods

**Dynamic semantics**

r[semantics.operator.unary]
`unary_value(op, a)` is the outcome of the unary operator `op` at the
outcome `a`.

r[semantics.operator.primitive]
`primitive(i, f, v, w)` is the primitive operation `f` of `i` at `v` and
`w`.

r[semantics.operator.binary]
`binary_value(i, op, a, b)` is the outcome of the binary operator `op` at
the outcomes `a` and `b`.

r[semantics.operator.method]
`method_value(m, receiver, args)` is the outcome of the method `m` at the
outcomes of its receiver and its arguments.

r[semantics.operator.count]
`count_value(c, args)` is the outcome of the cardinality operator `c` at
the outcome of its arguments.

```fren
pub fn unary_value(op: UnaryOp, a: Outcome): Outcome := match op, a {
    UnaryOp::Not, Outcome::Defined(Value::True) => Outcome::Defined(Value::False),
    UnaryOp::Not, Outcome::Defined(Value::False) => Outcome::Defined(Value::True),
    UnaryOp::Neg, Outcome::Defined(Value::Integer(n)) => Outcome::Defined(Value::Integer(-n)),
    _, _ => Outcome::Undefined,
}

-- A primitive operation at two arguments.
pub fn primitive(i: Interp, f: Id, v: Value, w: Value): Outcome :=
    apply(i.primitives, f, Value::Cons(v, Value::Cons(w, Value::Nil)))

pub fn binary_value(i: Interp, op: BinaryOp, a: Outcome, b: Outcome): Outcome := match a, b {
    Outcome::Defined(v), Outcome::Defined(w) => match op, v, w {
        BinaryOp::Eq, _, _ => Outcome::Defined(truth(v = w)),
        BinaryOp::Lt, Value::Integer(m), Value::Integer(n) => Outcome::Defined(truth(m < n)),
        BinaryOp::Le, Value::Integer(m), Value::Integer(n) => Outcome::Defined(truth(m <= n)),
        BinaryOp::Add, Value::Integer(m), Value::Integer(n) => Outcome::Defined(
            Value::Integer(m + n)
        ),
        BinaryOp::Sub, Value::Integer(m), Value::Integer(n) => Outcome::Defined(
            Value::Integer(m - n)
        ),
        BinaryOp::Mul, Value::Integer(_), Value::Integer(_) => primitive(i, "*", v, w),
        BinaryOp::Div, Value::Integer(_), Value::Integer(n) => if n = 0 then Outcome::Undefined else primitive(i, "div", v, w),
        BinaryOp::Mod, Value::Integer(_), Value::Integer(n) => if n = 0 then Outcome::Undefined else primitive(i, "mod", v, w),
        BinaryOp::Concat, Value::Text(_), Value::Text(_) => primitive(i, "++", v, w),
        BinaryOp::Concat, Value::Nil | Value::Cons(_, _), Value::Nil | Value::Cons(_, _) => Outcome::Defined(append(v, w)),
        BinaryOp::In, _, Value::Nil | Value::Cons(_, _) => Outcome::Defined(truth(element?(v, w))),
        _, _, _ => Outcome::Undefined,
    },
    _, _ => Outcome::Undefined,
}

pub fn method_value(m: MethodName, receiver: Outcome, args: Outcome): Outcome := match receiver, args {
    Outcome::Defined(v), Outcome::Defined(l) => match m, v, l {
        MethodName::Abs, Value::Integer(n), Value::Nil => Outcome::Defined(Value::Integer(n.abs)),
        MethodName::Min, Value::Integer(n), Value::Cons(Value::Integer(k), Value::Nil) => Outcome::Defined(Value::Integer(n.min(k))),
        MethodName::Max, Value::Integer(n), Value::Cons(Value::Integer(k), Value::Nil) => Outcome::Defined(Value::Integer(n.max(k))),
        MethodName::Len, Value::Text(s), Value::Nil => Outcome::Defined(Value::Integer(s.len)),
        MethodName::Len, Value::Nil | Value::Cons(_, _), Value::Nil => Outcome::Defined(
            Value::Integer(length(v))
        ),
        _, _, _ => Outcome::Undefined,
    },
    _, _ => Outcome::Undefined,
}

pub fn count_value(c: Cardinality, args: Outcome): Outcome := match args {
    Outcome::Defined(l) => if booleans?(l) then Outcome::Defined(
        truth(
            match c {
                Cardinality::AtMost => trues(l) <= 1,
                Cardinality::Exactly => trues(l) = 1,
            }
        )
    ) else Outcome::Undefined,
    Outcome::Undefined => Outcome::Undefined,
}
```

### Connectives, lists and calls

**Dynamic semantics**

r[semantics.eval.outcomes]
The rule of each form is a function of the outcomes of its immediate
subexpressions, but for `Let`, `Match` and `Apply`. Those evaluate a
subexpression in an environment that another's outcome or value gives.

r[semantics.connective]
The rules of `and`, `or` and a conditional take the outcome of each
operand, and use only those that the form evaluates.

r[semantics.connective.and]
`and_value(a, b)` is `b` only where `a` is `true`. It is undefined where
`b` is only where the form evaluates `b`.

r[semantics.connective.or]
`or_value(a, b)` is `true` where `a` is `true`, `b` where `a` is `false`,
and undefined otherwise.

r[semantics.connective.if]
`if_value(c, t, f)` is `t` where `c` is `true`, `f` where `c` is `false`,
and undefined otherwise.

r[semantics.eval.match]
An arm of a `match` whose pattern matches is `if_value` of its guard, its
body and the arms after it, the guard and body in the environment with the
pattern's binders bound.

r[semantics.test]
`is_value(p, s)` says whether `p` matches the value of `s`, and is
undefined where `s` is.

r[semantics.construction.cons]
`cons_value(a, rest)` is `Cons(v, l)` where `a` is `v` and `rest` is `l`,
and undefined where either is.

r[semantics.construction.construct]
`construct_value(c, args)` is `Constructed(c, l)` where `args` is `l`, and
undefined where `args` is.

r[semantics.construction.project]
`project_value(a, c, k)` is the element at position `k` of `l` where `a`
is `Constructed(c, l)`, and undefined otherwise.

r[semantics.construction.index]
`index_value(q, k)` is the element of the list `q` at the position `k`,
and undefined out of range, where `q` is not a list, or where `k` is not
an integer.

r[semantics.call]
`call_value(g, f, args)` is `f`'s value in the graph `g` at the list of the
arguments' values, and undefined where `args` is.

> **Rationale:** Giving each rule its own function keeps `eval` small.
> Compiling it, a structural recursion with an arm for each form, took 199M
> of Lean's raw heartbeats with these rules written within it, against a
> limit of 200M, and takes 160M (#572).

```fren
-- The outcome of `a and b`, of `a or b`, and of a conditional, from those of their operands.
pub fn and_value(a: Outcome, b: Outcome): Outcome := match a {
    Outcome::Defined(Value::True) => b,
    Outcome::Defined(Value::False) => Outcome::Defined(Value::False),
    _ => Outcome::Undefined,
}

pub fn or_value(a: Outcome, b: Outcome): Outcome := match a {
    Outcome::Defined(Value::True) => Outcome::Defined(Value::True),
    Outcome::Defined(Value::False) => b,
    _ => Outcome::Undefined,
}

pub fn if_value(c: Outcome, t: Outcome, f: Outcome): Outcome := match c {
    Outcome::Defined(Value::True) => t,
    Outcome::Defined(Value::False) => f,
    _ => Outcome::Undefined,
}

pub fn is_value(p: Pattern<Id>, s: Outcome): Outcome := match s {
    Outcome::Defined(v) => Outcome::Defined(truth(matches_value?(p, v))),
    Outcome::Undefined => Outcome::Undefined,
}

pub fn cons_value(a: Outcome, rest: Outcome): Outcome := match a, rest {
    Outcome::Defined(v), Outcome::Defined(l) => Outcome::Defined(Value::Cons(v, l)),
    _, _ => Outcome::Undefined,
}

pub fn construct_value(c: Id, args: Outcome): Outcome := match args {
    Outcome::Defined(l) => Outcome::Defined(Value::Constructed(c, l)),
    Outcome::Undefined => Outcome::Undefined,
}

pub fn project_value(a: Outcome, c: Id, k: Int): Outcome := match a {
    Outcome::Defined(Value::Constructed(d, l)) => if c = d then nth(l, k) else Outcome::Undefined,
    _ => Outcome::Undefined,
}

pub fn index_value(q: Outcome, k: Outcome): Outcome := match q, k {
    Outcome::Defined(l), Outcome::Defined(Value::Integer(n)) => if list?(l) then nth(l, n) else Outcome::Undefined,
    _, _ => Outcome::Undefined,
}

pub fn call_value(g: Graph, f: Id, args: Outcome): Outcome := match args {
    Outcome::Defined(l) => apply(g, f, l),
    Outcome::Undefined => Outcome::Undefined,
}
```

### The evaluation function

`eval` is written as a [function block](Items.md#function-blocks), whose
`out` gives its body.

**Dynamic semantics**

r[semantics.eval]
`eval(i, env, e)` is the outcome of `e` in the interpretation `i` and the
environment `env`.

r[semantics.eval.structural]
`eval` is a [structural recursion](Recursion.md) on `e`. It is a function.

r[semantics.eval.determinism]
The same expression in the same interpretation and environment always has
the same outcome (*determinism*, `lang::determinism`).

> **Note:** Determinism is why two expressions written the same have the
> same value (see [Expressions as
> written](../Lint/Meaning.md#expressions-as-written)).

```fren
pub fn eval(i: Interp, env: Env, e: Expr<Id>): (r: Outcome) {
    out r := match e {
        Expr::Literal(v) => Outcome::Defined(v),
        Expr::Var(x) => lookup(env, x),
        Expr::Let(x, d, b) => eval(i, Env::Bind(x, eval(i, env, d), env), b),
        Expr::Unary(op, a) => unary_value(op, eval(i, env, a)),
        Expr::Binary(op, a, b) => binary_value(i, op, eval(i, env, a), eval(i, env, b)),
        Expr::And(a, b) => and_value(eval(i, env, a), eval(i, env, b)),
        Expr::Or(a, b) => or_value(eval(i, env, a), eval(i, env, b)),
        Expr::If(c, t, f) => if_value(eval(i, env, c), eval(i, env, t), eval(i, env, f)),
        Expr::Is(s, p) => is_value(p, eval(i, env, s)),
        Expr::Match(s, p, g, b, rest) => match eval(i, env, s) {
            Outcome::Defined(v) => if matches_value?(p, v) then if_value(
                eval(i, bind(p, v, env), g),
                eval(i, bind(p, v, env), b),
                eval(i, env, rest)
            ) else eval(i, env, rest),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::NoMatch => Outcome::Undefined,
        Expr::Nil => Outcome::Defined(Value::Nil),
        Expr::Cons(a, rest) => cons_value(eval(i, env, a), eval(i, env, rest)),
        Expr::Construct(c, args) => construct_value(c, eval(i, env, args)),
        Expr::Project(a, c, k) => project_value(eval(i, env, a), c, k),
        Expr::Index(q, k) => index_value(eval(i, env, q), eval(i, env, k)),
        Expr::Method(m, receiver, args) => method_value(
            m,
            eval(i, env, receiver),
            eval(i, env, args)
        ),
        Expr::Count(c, args) => count_value(c, eval(i, env, args)),
        Expr::Apply(_, args, ps, body) => match eval(i, env, args) {
            Outcome::Defined(l) => eval(i, bind_params(ps, l), body),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Call(f, args) => call_value(i.functions, f, eval(i, env, args)),
        Expr::Recur(f, args) => call_value(i.recursions, f, eval(i, env, args)),
    }
}
```

```fren
expect determinism(i: Interp, env: Env, e: Expr<Id>, e2: Expr<Id>) {
    expect same: when e2 = e, eval(i, env, e2) = eval(i, env, e)
}
```

## What the model leaves out

**Dynamic semantics**

r[semantics.excluded]
The model covers the expressions without quantifiers, sets, relations or
abstract types.

r[semantics.excluded.quantifiers]
[Quantifiers](Quantifiers.md) evaluate their bodies at every value of their
bound names. Their meaning is stated in their chapter.

r[semantics.excluded.abstract]
A value of an abstract type is the interpretation's, and is compared only
with `=`.

r[semantics.excluded.orders]
The orders of ordered enumerations, records and strings, and the methods
of strings but `len`, are not yet in the model.

> **Note:** No structural recursion on the expression can evaluate a
> quantifier's body at every value of its bound names. Sets and relations
> would need values compared up to the order of their members.
