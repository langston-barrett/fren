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
same declarations, and so elaborates alike.

```fren
pub fn written(Scoped): lang::Expr
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
    e: lang::Expr,
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
