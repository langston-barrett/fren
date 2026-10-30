# Dynamic semantics

This chapter defines what an expression evaluates to. The rules of the
other chapters are stated over it: a constraint that mentions no variable
is the same in every behaviour because of the [coincidence
lemma](EvaluationRules.md#free-variables), and `a and b` may index out of range in `b`
because `b` is not evaluated where `a` is false (see
[Guards](EvaluationRules.md#guards)).

The semantics is big-step, in the style of the dynamic semantics of the
Definition of Standard ML and of chapter 3 of Pierce's *Types and
Programming Languages*: one function, `lang::eval`, gives the outcome of
an expression in an interpretation and an environment, by one rule for
each form of expression, over the outcomes of its immediate
subexpressions. Its sections follow the Rust Reference's chapter on
expressions. The forms of the source language that are not in the
abstract syntax below are *derived forms*, defined by their translation
into it, as the Definition's are (see [Derived forms](#derived-forms)).

```fren
pub mod lang
```

## Values

`lang::Value` is the value of an expression, of any type:

- `True` and `False` are the `Bool`s, as the constructors of `bool` are
  in Standard ML, and `Integer(n)` and `Text(s)` an `Int` or a `Nat`, and
  a `String`;
- `Nil` and `Cons(v, rest)` are lists: a sequence is the list of its
  elements, in order, and so are the values of a payload or of a record's
  fields;
- `Constructed(c, l)` is a value of an enumeration, record or newtype:
  the variant, record or newtype `c`, by its full path, and the list `l` of
  its payload's or fields' values, a record's in the order the record
  declares its fields.

Sets, relations and values of abstract types are not values of this
model: see [What the model leaves out](#what-the-model-leaves-out).

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

An expression's *outcome* is `Defined(v)`, its value `v`, or `Undefined`.
An expression is *well-defined* (WD) in an environment where its outcome
is defined. An expression that is not WD, such as `[][0]` or a `match`
where no arm is taken, still has a value in each behaviour, as in TLA+,
where `[][0]` is a "silly expression": that value is unspecified, and the
checks hold for every choice of it, as they hold for every interpretation
of an uninterpreted function (see [Definedness](../Check.md#definedness)).
So the outcome `Undefined` says only that the semantics does not fix the
value, and a rule that holds of every defined outcome holds of the
language's value there.

Evaluation is strict: an expression is WD only where each immediate
subexpression that it evaluates is WD. The forms that do not evaluate
every immediate subexpression are `And`, `Or`, `If`, `Match` and `Let`,
whose definition is evaluated only where its name is
(see [Let expressions](EvaluationRules.md#let-expressions)).

```fren
pub enum Outcome { Defined(Value), Undefined }
```

## Abstract syntax

The abstract syntax is that of an expression after
[elaboration](Types.md#checking-and-synthesis): every name is
[resolved](Scope.md), every type is checked, and every derived form is
translated. A variable is named by its `Id`, a variant, record or newtype
by its full path, as in `Shape::Circle`.

### Patterns

`lang::Pattern` is a pattern of [Patterns](Patterns.md): `Wildcard`, a
`Binder(x)`, a `Literal(v)`, the integer ranges `AtLeast(lo)`
(`lo..`), `AtMost(hi)` (`..=hi`) and `Between(lo, hi)` (`lo..=hi`; `lo..hi`
is `Between(lo, hi - 1)`), `Variant(c, ps)`, where `ps` is a list pattern
for the payload's values, and an or-pattern `Or(a, b)`. A list pattern is
`Nil` or `Cons(p, ps)`, as a list is; it also matches the list of the
scrutinees of a `match` with [several
scrutinees](HigherOrder.md#lambda-matches-and-multiple-scrutinees).

```fren
pub enum Pattern {
    Wildcard,
    Binder(Id),
    Literal(Value),
    AtLeast(Int),
    AtMost(Int),
    Between(Int, Int),
    Variant(Id, Pattern),
    Nil,
    Cons(Pattern, Pattern),
    Or(Pattern, Pattern),
}
```

### Expressions

`lang::Expr` is an expression. A form with a list of operands, such as
the arguments of a call, has a list expression for them, `Nil` or
`Cons(e, rest)`, which evaluates to the list of their values.

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

```fren
pub enum UnaryOp { Not, Neg }

pub enum BinaryOp { Eq, Lt, Le, Add, Sub, Mul, Div, Mod, Concat, In }

pub enum MethodName { Abs, Min, Max, Len }

-- The cardinality operators: `exactly_one?` and `at_most_one?`.
pub enum Cardinality { Exactly, AtMost }

-- A function's parameters, in order.
pub enum Params { Nil, Cons(Id, Params) }

pub enum Expr {
    Literal(Value),
    Var(Id),
    Let(Id, Expr, Expr),
    Unary(UnaryOp, Expr),
    Binary(BinaryOp, Expr, Expr),
    And(Expr, Expr),
    Or(Expr, Expr),
    If(Expr, Expr, Expr),
    Is(Expr, Pattern),
    Match(Expr, Pattern, Expr, Expr, Expr),
    NoMatch,
    Nil,
    Cons(Expr, Expr),
    Construct(Id, Expr),
    Project(Expr, Id, Int),
    Index(Expr, Expr),
    Method(MethodName, Expr, Expr),
    Count(Cardinality, Expr),
    Apply(Id, Expr, Params, Expr),
    Call(Id, Expr),
    Recur(Id, Expr),
}
```

### Derived forms

Each form of the left column is the expression of the right, after its
own subexpressions are translated. A translation that writes an
expression twice, such as the scrutinee of a `match`, does not change its
meaning, since evaluation has no effects and is deterministic.

| Derived form | Translation |
|---|---|
| `a != b` | `not (a = b)` |
| `a > b`, `a >= b` | `b < a`, `b <= a` |
| `a iff b` | `a = b` |
| `when c, d` | `if c then d else true` |
| `unless c, d` | `if c then true else d` |
| `a < b < c`, and every [chained comparison](Expressions.md#chained-comparisons) | `a < b and b < c` |
| `let x := d, y := e in b`; `b where x := d` | `let x := d in let y := e in b`; `let x := d in b` |
| `match s { p if g => b, arms }` | `Match(s, p, g, b, match s { arms })`, with `g` `true` for an arm without a guard |
| `match s {}`, after the last arm | `NoMatch` |
| `match a, b { p, q => e, ... }` | `match [a, b] { [p, q] => e, ... }`, its patterns as list patterns |
| `table { c => v, rows }` | `if c then v else table { rows }`; `table { _ => v }` is `v`, and `table {}` is `NoMatch` |
| `table s { arms }` | `match s { arms }` |
| `s is p and e`, where `e` reads a binder of `p` | `And(Is(s, p), Match(s, p, true, e, NoMatch))` |
| `if s is p then t else f`, where `t` reads a binder of `p` | `If(Is(s, p), Match(s, p, true, t, NoMatch), f)` |
| `when s is p, d`, where `d` reads a binder of `p` | `If(Is(s, p), Match(s, p, true, d, NoMatch), true)` |
| a later operand of a chain of `and`s after `s is p`, as `s is p and a and e` | each operand that reads a binder of `p` within `Match(s, p, true, ·, NoMatch)`, at the places where [`lang::test_scope`](Expressions.md#pattern-tests) has the binders in scope: the `Match` is evaluated only where the test holds, so it never reaches `NoMatch` |
| `[a, b]` | `Cons(a, Cons(b, Nil))` |
| `C`, a variant without a payload | `Construct(C, Nil)` |
| `C(a, b)`; `R { y := b, x := a }`; `N(a)` | `Construct(C, [a, b])`; `Construct(R, [a, b])`, in the order that `R` declares `x` and `y`; `Construct(N, [a])` |
| `r.x`; `n.0` | `Project(r, R, k)`, where `x` is `R`'s field at position `k`; `Project(n, N, 0)` |
| `{ r with x := a }` | `Construct(R, ...)` of `R`'s fields, `a` for `x` and `Project(r, R, k)` for each other field `k` |
| `f(a, b)`, where `f` is a defined function that is not recursive, with the parameters `x` and `y` and the body `e` | `Apply(f, [a, b], [x, y], e)` |
| `C`, a constant with the definition `e` | `Apply(C, Nil, Nil, e)` |
| `f(a, b)`, where `f` is uninterpreted | `Call(f, [a, b])`; an instance of a [generic one](GenericFunctions.md#uninterpreted-generic-functions) is named with its type arguments, as `pick<Int>`, one unknown function for each instance |
| `f(a, b)`, where `f` is a [structural recursion](Recursion.md) | `Recur(f, [a, b])` |
| an application of a [higher-order function](HigherOrder.md) | its body, with each application of a function parameter replaced by the closure's body within a `let` of each of the closure's parameters, the names renamed apart, as [Meaning](HigherOrder.md#meaning) states |
| `exactly_one?(a, b)`, `at_most_one?(a, b)` | `Count(Exactly, [a, b])`, `Count(AtMost, [a, b])` |

## Environments and interpretations

An *environment*, `lang::Env`, binds variables to outcomes: those of a
procedure and of its calls, the parameters of a function, the bound
names of quantifiers, the names of `let`s, and the binders of patterns.
`lookup(env, x)` is the outcome of the innermost binding of `x`, and an
unbound variable, which a resolved expression never reads, is undefined.

An *interpretation*, `lang::Interp`, gives three tables of values, which
are kept apart because they vary differently between behaviours:

- `functions`, the values of the spec's uninterpreted functions, which
  differ between behaviours;
- `recursions`, the values of its [structural recursions](Recursion.md),
  which are the same in every behaviour: each is the least fixed point of
  its equations (see [Call expressions](EvaluationRules.md#call-expressions));
- `primitives`, the *primitive operations*, which Fren's own decidable
  fragment cannot compute and which this chapter therefore takes as given,
  as the Definition takes its basic values from `APPLY`: products and
  quotients of two integers, `*`, `div` and `mod`, and concatenations of
  two strings, `++`; they too are the same in every behaviour.

Each is a `Graph`, a finite list
of points `Point(f, args, r)`: `f` at the list of arguments `args` is `r`,
the first point for them where there are several. An evaluation reads
finitely many points, so every outcome under an interpretation of the
language is that under a finite one, and the rules below are stated over
finite ones. The language's interpretation gives each primitive its usual
meaning, by Lean's `Int.mul`, `Int.ediv`, `Int.emod` and `String.append`,
at every point that it has.

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

`lookup` finds the innermost binding, and one binding hides another of
the same name:

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

[Rules of evaluation](EvaluationRules.md) states each row as laws over the
outcomes of a form's immediate subexpressions, which `eval` meets: they are
the readable rules, and `eval` refines them, with every case that they leave out, such
as the outcome of `x + true`, which elaboration rejects: undefined. The
functions below give each form's rule; `lang::eval` applies them.

### Operations on lists

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

`matches_value?(p, v)` says that `p` matches `v`, and `bind(p, v, env)` is `env`
with `p`'s binders bound to the parts of `v` that they match. An
or-pattern binds nothing, since elaboration rejects one whose
alternatives bind names (`F0333`).

```fren
pub fn matches_value?(p: Pattern, v: Value) := match p {
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

pub fn bind(p: Pattern, v: Value, env: Env): Env := match p {
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
pub fn bind_params(ps: Params, args: Value): Env := match ps {
    Params::Cons(x, rest) => match args {
        Value::Cons(v, more) => Env::Bind(x, Outcome::Defined(v), bind_params(rest, more)),
        _ => Env::Empty,
    },
    Params::Nil => Env::Empty,
}
```

### Operators and methods

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
        BinaryOp::Add, Value::Integer(m), Value::Integer(n) => Outcome::Defined(Value::Integer(m + n)),
        BinaryOp::Sub, Value::Integer(m), Value::Integer(n) => Outcome::Defined(Value::Integer(m - n)),
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
        MethodName::Len, Value::Nil | Value::Cons(_, _), Value::Nil => Outcome::Defined(Value::Integer(length(v))),
        _, _, _ => Outcome::Undefined,
    },
    _, _ => Outcome::Undefined,
}

pub fn count_value(c: Cardinality, args: Outcome): Outcome := match args {
    Outcome::Defined(l) => if booleans?(l) then Outcome::Defined(truth(match c {
        Cardinality::AtMost => trues(l) <= 1,
        Cardinality::Exactly => trues(l) = 1,
    })) else Outcome::Undefined,
    Outcome::Undefined => Outcome::Undefined,
}
```

### The evaluation function

`eval(i, env, e)` is the outcome of `e` in the interpretation `i` and the
environment `env`. It is a [structural recursion](Recursion.md) on `e`, so
it is a function: the same expression in the same interpretation and
environment always has the same outcome (*determinism*), which is why two
expressions written the same have the same value (see [Expressions as
written](../Lint/Meaning.md#expressions-as-written)). It is written as a
[function block](Items.md#function-blocks), whose `out` gives its body.

```fren
pub fn eval(i: Interp, env: Env, e: Expr): (r: Outcome) {
    out r := match e {
        Expr::Literal(v) => Outcome::Defined(v),
        Expr::Var(x) => lookup(env, x),
        Expr::Let(x, d, b) => eval(i, Env::Bind(x, eval(i, env, d), env), b),
        Expr::Unary(op, a) => unary_value(op, eval(i, env, a)),
        Expr::Binary(op, a, b) => binary_value(i, op, eval(i, env, a), eval(i, env, b)),
        Expr::And(a, b) => match eval(i, env, a) {
            Outcome::Defined(Value::True) => eval(i, env, b),
            Outcome::Defined(Value::False) => Outcome::Defined(Value::False),
            _ => Outcome::Undefined,
        },
        Expr::Or(a, b) => match eval(i, env, a) {
            Outcome::Defined(Value::True) => Outcome::Defined(Value::True),
            Outcome::Defined(Value::False) => eval(i, env, b),
            _ => Outcome::Undefined,
        },
        Expr::If(c, t, f) => match eval(i, env, c) {
            Outcome::Defined(Value::True) => eval(i, env, t),
            Outcome::Defined(Value::False) => eval(i, env, f),
            _ => Outcome::Undefined,
        },
        Expr::Is(s, p) => match eval(i, env, s) {
            Outcome::Defined(v) => Outcome::Defined(truth(matches_value?(p, v))),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Match(s, p, g, b, rest) => match eval(i, env, s) {
            Outcome::Defined(v) => if matches_value?(p, v) then (match eval(i, bind(p, v, env), g) {
                Outcome::Defined(Value::True) => eval(i, bind(p, v, env), b),
                Outcome::Defined(Value::False) => eval(i, env, rest),
                _ => Outcome::Undefined,
            }) else eval(i, env, rest),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::NoMatch => Outcome::Undefined,
        Expr::Nil => Outcome::Defined(Value::Nil),
        Expr::Cons(a, rest) => match eval(i, env, a), eval(i, env, rest) {
            Outcome::Defined(v), Outcome::Defined(l) => Outcome::Defined(Value::Cons(v, l)),
            _, _ => Outcome::Undefined,
        },
        Expr::Construct(c, args) => match eval(i, env, args) {
            Outcome::Defined(l) => Outcome::Defined(Value::Constructed(c, l)),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Project(a, c, k) => match eval(i, env, a) {
            Outcome::Defined(Value::Constructed(d, l)) => if c = d then nth(l, k) else Outcome::Undefined,
            _ => Outcome::Undefined,
        },
        Expr::Index(q, k) => match eval(i, env, q), eval(i, env, k) {
            Outcome::Defined(l), Outcome::Defined(Value::Integer(n)) => if list?(l) then nth(l, n) else Outcome::Undefined,
            _, _ => Outcome::Undefined,
        },
        Expr::Method(m, receiver, args) => method_value(m, eval(i, env, receiver), eval(i, env, args)),
        Expr::Count(c, args) => count_value(c, eval(i, env, args)),
        Expr::Apply(_, args, ps, body) => match eval(i, env, args) {
            Outcome::Defined(l) => eval(i, bind_params(ps, l), body),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Call(f, args) => match eval(i, env, args) {
            Outcome::Defined(l) => apply(i.functions, f, l),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Recur(f, args) => match eval(i, env, args) {
            Outcome::Defined(l) => apply(i.recursions, f, l),
            Outcome::Undefined => Outcome::Undefined,
        },
    }
}
```

`determinism` states it:

```fren
expect determinism(i: Interp, env: Env, e: Expr, e2: Expr) {
    expect same: when e2 = e, eval(i, env, e2) = eval(i, env, e)
}
```

## What the model leaves out

The model covers the expressions without quantifiers, sets, relations
or abstract types. [Quantifiers](Quantifiers.md) evaluate their bodies at
every value of their bound names, which no structural recursion on the
expression can do; their meaning is stated in their chapter. Sets and
relations would need values compared up to the order of their members.
A value of an abstract type is the interpretation's, and is compared only
with `=`. The orders of ordered enumerations, records and strings, and the
methods of strings but `len`, are not yet in it either.
