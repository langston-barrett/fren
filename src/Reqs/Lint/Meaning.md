# Meaning

Many lints are right because of what an expression means, as the
[dynamic semantics](../Lang/Semantics.md) of the language states it: `x - x` is always
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
`PatternBinder` binding targets it (see [Bindings](../Lang/Scope.md#bindings)). Names
declared outside every pattern test are the same wherever the lints
compare expressions, within one procedure or one global expectation, so
they are not part of the scope. Both front ends compare scopes as well as
texts, with `writtenSameIn`, or leave the expressions whose scopes may
differ.

```fren
pub struct Scoped { text: Operand, scope: Set<lang::Id> }
```

An expression as written elaborates to one [expression of the
semantics](../Lang/Semantics.md#abstract-syntax), `written(x)`: with the
same text and the same binders, an expression has the same names, of the
same declarations, and so elaborates alike. It is the elaboration where
the expression is written. Where it reads a binder of a pattern test in
scope, that includes the `match` around it that [Derived
forms](../Lang/Semantics.md#derived-forms) writes.

```fren
pub fn written(Scoped): lang::Expr<lang::Id>
```

So, since [evaluation](../Lang/Semantics.md#the-evaluation-function) is a
function, as [`lang::determinism`](../Lang/Semantics.md#the-evaluation-function)
states, two expressions written the same in the same scope have the same
outcome in one interpretation and environment, well-defined or not:
`[1][5] = [1][5]` holds in every behaviour, though `[1][5]` is not
well-defined, and so may differ between them:

```fren
expect written_same(x: Scoped, y: Scoped, i: lang::Interp, env: lang::Env) {
    expect written_same: when x = y, lang::eval(i, env, written(x)) = lang::eval(i, env, written(y))
}
```

Two texts in different scopes may have different values.
`lint::written_scopes` is the two `v`s of the conditional above: in the
`then` branch, the binder of the payload of the scrutinee `r`, which the
`match` that the [pattern test elaborates
to](../Lang/Semantics.md#derived-forms) binds, and in the `else` branch,
the variable `v`, in an environment that binds `r` to a reply and `v` to
another value. The solver unfolds [`eval`](../Lang/Semantics.md) only one
step, and the `match` takes several, so `src/Impls/Lint.lean` proves
`payload_read` in Lean, for every interpretation and pair of values, by
evaluating the `match`; `fren check` tests it, and finds the cover goal's
witness by testing:

```fren
set_option fren.evidence "random" in
pub proc written_scopes(i: lang::Interp, payload: lang::Value, v: lang::Value) {
    use lang::{Env, Expr, Outcome, Pattern, Value, eval}

    let env: Env := Env::Bind(
        "r",
        Outcome::Defined(
            Value::Constructed("Reply::Value", Value::Cons(payload, Value::Nil))
        ),
        Env::Bind("v", Outcome::Defined(v), Env::Empty)
    )
    let in_then: Outcome := eval(
        i,
        env,
        Expr::Match(
            Expr::Var("r"),
            Pattern::Variant(
                "Reply::Value",
                Pattern::Cons(Pattern::Binder("v"), Pattern::Nil)
            ),
            Expr::Literal(Value::True),
            Expr::Var("v"),
            Expr::NoMatch
        )
    )
    let in_else: Outcome := eval(i, env, Expr::Var("v"))

    ensure payload_read: in_then = Outcome::Defined(payload)
    cover differ: in_then != in_else
}
```

## Expressions that mention nothing

What an expression mentions is a set of `lang::Mention`s, as
[`lang::mentions`](../Lang/Expressions.md#mentions) gives it, and as its
elaboration's [free variables](../Lang/EvaluationRules.md#free-variables) are.
One that mentions nothing has the same outcome in every interpretation
and environment, given the structural recursions and the primitive
operations, by the coincidence lemma; where its outcome is undefined, as
in `get([1], 5)` with `fn get(q: Seq<Int>, i: Int): Int := q[i]`, its
value is unspecified, so it may differ between behaviours; the
[definedness check](../Check.md#definedness) reports that index, so in a
spec that passes its checks the value is the
same. Here `e` is the expression's elaboration, and `i`, `p`, `j` and `q`
two interpretations and environments:

```fren
expect mentions_nothing(
    e: lang::Expr<lang::Id>,
    i: lang::Interp,
    p: lang::Env,
    j: lang::Interp,
    q: lang::Env,
) {
    assume fixed: i.recursions = j.recursions and i.primitives = j.primitives
    call c := lang::closed(i, p, j, q, e)
    expect mentions_nothing: when lang::free_vars(e) = {}, lang::eval(i, p, e) = lang::eval(j, q, e)
}
```

## Fixes that agree

A fix *agrees* with the expression it replaces where, in each
interpretation and environment, the expression is undefined or the fix
has its outcome. So where the expression as written is well-defined, the
fix is too, with the same value, and a fix may be well-defined where the
expression is not, as `false` is where `a and not a` is undefined: its
value there was unspecified (see [Outcomes and
well-definedness](../Lang/Semantics.md#outcomes-and-well-definedness)).
Each lint stated over the [syntax of the
semantics](../Lang/Semantics.md#abstract-syntax) states that its fix agrees,
with `agrees?`, at the outcomes of `lang::eval`:

```fren
pub fn agrees?(fix: lang::Outcome, original: lang::Outcome) := original = lang::Outcome::Undefined or fix = original
```

## Primitive operations

Products, quotients and remainders of integers, `*`, `div` and `mod`, and
concatenations of strings, `++`, are [primitive
operations](../Lang/Semantics.md#environments-and-interpretations): an
interpretation gives them, as a finite graph, and `eval` reads only its
points. In an arbitrary interpretation, `x * 1` and `x` need not agree.
The language's interpretation gives each primitive its usual meaning at
every point that it has. `usual?` states the part of that meaning that
the lints rest on:

- a product with `0` is `0`, and one with `1` or `-1` is the other
  operand or its negation;
- a quotient by `1` is the dividend, and one of `0` is `0`;
- a remainder by an `n` that is not `0` is at least `0` and below
  `n.abs`, and is `m` itself where the dividend `m` is in that range, and
  `m` less or more `n.abs` where `m` is within `n.abs` above or below it;
- a concatenation with `""` is the other string.

Each is a fact of linear arithmetic or of strings, which the solver
decides, as the whole product is not. Besides, a product, quotient or
remainder of two integers is an integer. A point at other arguments, or
of another name, is not constrained. Nor is a remainder by `0`, which the
language's interpretation gives as `Int.emod` does, the dividend; `eval`
never reads it, since `x mod 0`, like `x div 0`, is undefined before the
graph is read.

A lint whose fix, or whose message, rests on a primitive operation states
that it agrees in each interpretation whose primitives are `usual?`, and
not in every one. A graph with no point for the arguments leaves the
primitive undefined there, so the expression is undefined too, and the
fix agrees with it.

```fren
-- `r` is the product of `m` and `n`, where one of them is `0`, `1` or `-1`.
fn usual_product?(m: Int, n: Int, r: Int) :=
    (when n = 1, r = m) and (when m = 1, r = n) and (when n = -1, r = -m) and (when m = -1, r = -n)
    and (when m = 0 or n = 0, r = 0)

-- `r` is the remainder of `m` by `n`, where `n` is not `0`: in range, and
-- `m`'s distance to the range where that is at most `n.abs`.
fn usual_remainder?(m: Int, n: Int, r: Int) := when n != 0,
    0 <= r < n.abs
    and (when 0 <= m < n.abs, r = m)
    and (when n.abs <= m < n.abs + n.abs, r = m - n.abs)
    and (when -n.abs <= m < 0, r = m + n.abs)

-- The point `f` at `args` is `r` meets the usual meaning of `f` that the lints rest on.
fn usual_point?(f: lang::Id, args: lang::Value, r: lang::Value) := match args, r {
    lang::Value::Cons(lang::Value::Integer(m), lang::Value::Cons(lang::Value::Integer(n), lang::Value::Nil)),
    lang::Value::Integer(k) => (when f = "*", usual_product?(m, n, k))
        and (when f = "div", (when n = 1, k = m) and (when m = 0, k = 0))
        and (when f = "mod", usual_remainder?(m, n, k)),
    lang::Value::Cons(lang::Value::Integer(_), lang::Value::Cons(lang::Value::Integer(_), lang::Value::Nil)),
    _ => not (f is "*" | "div" | "mod"),
    lang::Value::Cons(lang::Value::Text(s), lang::Value::Cons(lang::Value::Text(t), lang::Value::Nil)),
    _ => (when f = "++", (when t = "", r = lang::Value::Text(s)) and (when s = "", r = lang::Value::Text(t))),
    _, _ => true,
}

-- Each point of `g` meets the usual meaning of its primitive operation that the lints rest on.
pub fn usual?(g: lang::Graph) := match g {
    lang::Graph::Empty => true,
    lang::Graph::Point(f, args, r, rest) => usual_point?(f, args, r) and usual?(rest),
}
```

`usual?` must not ask more than the language's interpretation gives, or
the claims that assume it would say nothing of that interpretation.
`lint::usual_primitives` states that every point of the language's
primitives meets it: its outputs are the language's product, quotient and
remainder of its inputs. A spec cannot compute them, since the product of
two variables is not linear, and a divisor must be a constant (see
[Division and remainder](../Lang/Expressions.md#division-and-remainder)).
So the implementation gives them, as `Int.mul`, `Int.ediv` and
`Int.emod`. The `ensure`s do not determine the outputs, so that they are
the language's primitives rests on the implementation writing them so,
which is trusted, as [Semantics](../Lang/Semantics.md) states the
language's interpretation. `src/Impls/Rewrites.lean` proves in Lean only
that those values meet `usual_point?`, for every two integers. The
concatenation is Fren's own `++`, and the solver checks
it, for every two strings. `usual_language` checks it with the
solver at the language's own value of each point whose value is linear
in its arguments: a product with `0`, `1` or `-1`; a quotient by `1`,
`-1` or `0`, or of `0`, as `Int.ediv` gives it; a remainder by `1`, `-1`
or `0`, or of a dividend within `n.abs` of the range, as `Int.emod` gives
it; and a concatenation with `""`.

```fren
-- The two integers `m` and `n`, as the list of arguments of a primitive.
fn integers(m: Int, n: Int): lang::Value :=
    lang::Value::Cons(
        lang::Value::Integer(m),
        lang::Value::Cons(lang::Value::Integer(n), lang::Value::Nil)
    )

set_option fren.lint.undecidable "allow" in
pub proc usual_primitives(m: Int, n: Int, s: String, t: String): (
    product: Int,
    quotient: Int,
    remainder: Int,
) {
    ensure times: usual_point?("*", integers(m, n), lang::Value::Integer(product))
    ensure divides: usual_point?("div", integers(m, n), lang::Value::Integer(quotient))
    ensure modulo: usual_point?("mod", integers(m, n), lang::Value::Integer(remainder))
    expect concatenates: usual_point?(
        "++",
        lang::Value::Cons(
            lang::Value::Text(s),
            lang::Value::Cons(lang::Value::Text(t), lang::Value::Nil)
        ),
        lang::Value::Text(s ++ t)
    )
}

expect usual_language(m: Int, n: Int, s: String, t: String) {
    use lang::Value::{Cons, Integer, Nil, Text}

    expect times_zero: usual_point?("*", integers(m, 0), Integer(0)) and usual_point?("*", integers(0, n), Integer(0))
    expect times_one: usual_point?("*", integers(m, 1), Integer(m)) and usual_point?("*", integers(1, n), Integer(n))
    expect times_minus_one: usual_point?("*", integers(m, -1), Integer(-m))
        and usual_point?("*", integers(-1, n), Integer(-n))
    expect by_one: usual_point?("div", integers(m, 1), Integer(m)) and usual_point?("div", integers(m, -1), Integer(-m))
    expect by_zero: usual_point?("div", integers(m, 0), Integer(0))
    expect of_zero: usual_point?("div", integers(0, n), Integer(0))
    expect mod_one: usual_point?("mod", integers(m, 1), Integer(0)) and usual_point?("mod", integers(m, -1), Integer(0))
    expect mod_zero: usual_point?("mod", integers(m, 0), Integer(m))
    expect mod_near: when n != 0,
        (when 0 <= m < n.abs, usual_point?("mod", integers(m, n), Integer(m)))
        and (when n.abs <= m < n.abs + n.abs, usual_point?("mod", integers(m, n), Integer(m - n.abs)))
        and (when -n.abs <= m < 0, usual_point?("mod", integers(m, n), Integer(m + n.abs)))
    expect empty: usual_point?("++", Cons(Text(s), Cons(Text(""), Nil)), Text(s))
        and usual_point?("++", Cons(Text(""), Cons(Text(t), Nil)), Text(t))
}
```
