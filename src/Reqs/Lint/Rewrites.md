# Fixes as rewrites

A lint whose rule and fix are stated over the [syntax of the
semantics](../Lang/Semantics.md#abstract-syntax), `lang::Expr`, is a rewrite
rule: where it fires on an expression, its fix replaces that expression.
This chapter states, for every such lint at once, what fixing it everywhere
means, and four laws: fixing everywhere leaves nothing for the lint to
fire on, it changes nothing where the lint fires nowhere, so fixing again
changes nothing, and it [agrees](Meaning.md#fixes-that-agree) with the
expression as written.

```fren
pub mod lint
```

## Each lint where it fires

Each lint is stated by two functions over `lang::Expr`, at the place where
it fires: whether it fires on an expression, and what its fix writes
there. `lint::ExprLint` names them, and `fires_at?` and `fix_at` give each
one's functions. `overly_complex_bool_expr` is the only one so far.

The generated `fix_all` below has `fix_at` inlined in each of its arms, so
its size grows with the number of arms, the number of lints and the size
of each lint's `fix_at`, and a larger `fix_at` than this one already
reached Lean's limit of heartbeats while `fix_all` was compiled. So each
lint's fix, such as [`drop_fix`](Pedantic/Booleans.md#the-rule-over-the-syntax-of-the-semantics),
evaluates each of its tests once, and `fix_at` is the fix itself, not `if
fires_at?(l, e) then … else e`, which made the term three times as large.

```fren
-- The lints stated over the syntax of the semantics.
pub enum ExprLint { OverlyComplexBoolExpr }

-- One lint so far: with more, each is an arm.
set_option fren.lint.trivial_match "allow" in
pub fn fires_at?(l: ExprLint, e: Expr) := match l {
    ExprLint::OverlyComplexBoolExpr => overly_complex_fires?(e),
}

-- Inlined in every arm of `fix_all`: each lint's arm must stay small.
set_option fren.lint.trivial_match "allow" in
pub fn fix_at(l: ExprLint, e: Expr): Expr := match l {
    ExprLint::OverlyComplexBoolExpr => overly_complex_fix(e),
}
```

The laws of the fixes below rest on three facts about each lint, which
each arm of `ExprLint` owes. Where the lint does not fire, its fix is the
expression itself (`fix_at_unfired`). Its fix agrees with the expression
(`fix_at_agrees`), as
[`overly_complex_keeps_meaning`](Pedantic/Booleans.md#the-fix-keeps-the-meaning)
states for `overly_complex_bool_expr`. And where it fires, it fires on an
`and` or an `or`, and its fix writes one of the operands or a literal, on
which the lint never fires (`fix_at_operand`), as
[`overly_complex_operand`](Pedantic/Booleans.md#the-fix-keeps-the-meaning)
states. So once the operands are fixed, the fix leaves nothing to fix.

A lint whose fix builds new nodes does not meet the last fact: the De
Morgan rewrites of
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions), which may also
grow the expression, or the fix of
[`double_comparison`](Complexity/Comparisons.md#double-comparisons). For such a lint, fixing the operands
and then the expression once is not a normal form, and fixing everywhere
would have to fix again until nothing changes, which needs a measure that
decreases other than the size of the expression.

```fren
expect fix_at_unfired(l: ExprLint, e: Expr) {
    expect unfired: unless fires_at?(l, e), fix_at(l, e) = e
}

expect fix_at_operand(l: ExprLint, e: Expr, v: lang::Value) {
    expect operand: when fires_at?(l, e), match e {
        Expr::And(a, b) => fix_at(l, e) = a or fix_at(l, e) = b or fix_at(l, e) is Expr::Literal(_),
        Expr::Or(a, b) => fix_at(l, e) = a or fix_at(l, e) = b or fix_at(l, e) is Expr::Literal(_),
        _ => false,
    }
    expect literal: not fires_at?(l, Expr::Literal(v))
}

set_option fren.evidence "random" in
pub proc fix_at_agrees(l: ExprLint, e: Expr, i: lang::Interp, env: lang::Env) {
    ensure agrees: agrees?(lang::eval(i, env, fix_at(l, e)), lang::eval(i, env, e))
}
```

## Fixing everywhere

A lint fires within an expression where it fires on the expression or
within one of its operands. As [the lints that rewrite an
expression](../Lint.md#parentheses-in-fixes) do, it looks within the body
of a `let`, but not within its definition. `fix_all` fixes it everywhere,
operands first: it fixes the operands, and then the expression that they
make. It is one way of fixing the lint everywhere. `fren fix` fixes in
passes, each of which makes the outermost of the fixes that overlap, and
whether those passes reach what `fix_all` gives is open (#490).

```fren
-- Whether `l` fires on `e` or within one of its operands.
pub fn fires_in?(l: ExprLint, e: Expr) := fires_at?(l, e) or match e {
    Expr::Let(_, _, b) => fires_in?(l, b),
    Expr::Unary(_, a) => fires_in?(l, a),
    Expr::Binary(_, a, b) => fires_in?(l, a) or fires_in?(l, b),
    Expr::And(a, b) => fires_in?(l, a) or fires_in?(l, b),
    Expr::Or(a, b) => fires_in?(l, a) or fires_in?(l, b),
    Expr::If(c, t, f) => fires_in?(l, c) or fires_in?(l, t) or fires_in?(l, f),
    Expr::Is(s, _) => fires_in?(l, s),
    Expr::Match(s, _, g, b, rest) => fires_in?(l, s) or fires_in?(l, g) or fires_in?(l, b) or fires_in?(l, rest),
    Expr::Cons(a, rest) => fires_in?(l, a) or fires_in?(l, rest),
    Expr::Construct(_, args) => fires_in?(l, args),
    Expr::Project(a, _, _) => fires_in?(l, a),
    Expr::Index(q, k) => fires_in?(l, q) or fires_in?(l, k),
    Expr::Method(_, r, args) => fires_in?(l, r) or fires_in?(l, args),
    Expr::Count(_, args) => fires_in?(l, args),
    Expr::Apply(_, args, _, body) => fires_in?(l, args) or fires_in?(l, body),
    Expr::Call(_, args) => fires_in?(l, args),
    Expr::Recur(_, args) => fires_in?(l, args),
    _ => false,
}

-- `e` with `l` fixed everywhere, operands first.
pub fn fix_all(l: ExprLint, e: Expr): Expr := match e {
    Expr::Let(x, d, b) => fix_at(l, Expr::Let(x, d, fix_all(l, b))),
    Expr::Unary(op, a) => fix_at(l, Expr::Unary(op, fix_all(l, a))),
    Expr::Binary(op, a, b) => fix_at(l, Expr::Binary(op, fix_all(l, a), fix_all(l, b))),
    Expr::And(a, b) => fix_at(l, Expr::And(fix_all(l, a), fix_all(l, b))),
    Expr::Or(a, b) => fix_at(l, Expr::Or(fix_all(l, a), fix_all(l, b))),
    Expr::If(c, t, f) => fix_at(l, Expr::If(fix_all(l, c), fix_all(l, t), fix_all(l, f))),
    Expr::Is(s, p) => fix_at(l, Expr::Is(fix_all(l, s), p)),
    Expr::Match(s, p, g, b, rest) => fix_at(l, Expr::Match(fix_all(l, s), p, fix_all(l, g), fix_all(l, b), fix_all(l, rest))),
    Expr::Cons(a, rest) => fix_at(l, Expr::Cons(fix_all(l, a), fix_all(l, rest))),
    Expr::Construct(c, args) => fix_at(l, Expr::Construct(c, fix_all(l, args))),
    Expr::Project(a, c, k) => fix_at(l, Expr::Project(fix_all(l, a), c, k)),
    Expr::Index(q, k) => fix_at(l, Expr::Index(fix_all(l, q), fix_all(l, k))),
    Expr::Method(m, r, args) => fix_at(l, Expr::Method(m, fix_all(l, r), fix_all(l, args))),
    Expr::Count(c, args) => fix_at(l, Expr::Count(c, fix_all(l, args))),
    Expr::Apply(f, args, ps, body) => fix_at(l, Expr::Apply(f, fix_all(l, args), ps, fix_all(l, body))),
    Expr::Call(f, args) => fix_at(l, Expr::Call(f, fix_all(l, args))),
    Expr::Recur(f, args) => fix_at(l, Expr::Recur(f, fix_all(l, args))),
    _ => fix_at(l, e),
}
```

## The laws of the fixes

Fixing a lint everywhere fixes it: the lint fires nowhere in what
`fix_all` gives (`fixed`). So fixing it again changes nothing
(`idempotent`), since on an expression where it fires nowhere `fix_all`
changes nothing (`unchanged`). And the result agrees with the expression as
written, in every interpretation and environment (`keeps_meaning`). These
follow from the [facts about each lint](#each-lint-where-it-fires) at the
place where it fires: `fix_at_unfired`, `fix_at_agrees` and
`fix_at_operand`. The fix at one place alone need not fix the lint, as
`overly_complex_refires` shows: these laws are of fixing everywhere. That
the passes of `fren fix` end where `fix_all` does is a property of the
passes, which these laws do not state.

The laws are about every expression, and so by induction on it, which the
solver does not do: `src/Impls/Rewrites.lean` proves them in Lean, for
every lint, expression, interpretation and environment, from those facts
and from evaluation being monotone in the operands: where each
operand of an expression agrees with another, in every environment, so does
the expression with those operands replaced. `fix_all` leaves the
definition of a `let` as written, so the environments in which it fixes
operands are the same as those in which the expression as written evaluates
them. `fren check` tests them:

```fren
set_option fren.evidence "random" in
pub proc fix_all_laws(l: ExprLint, e: Expr, i: lang::Interp, env: lang::Env) {
    ensure fixed: not fires_in?(l, fix_all(l, e))
    ensure unchanged: unless fires_in?(l, e), fix_all(l, e) = e
    ensure idempotent: fix_all(l, fix_all(l, e)) = fix_all(l, e)
    ensure keeps_meaning: agrees?(lang::eval(i, env, fix_all(l, e)), lang::eval(i, env, e))
}
```

```fren
#fren_check fix_at_unfired
#fren_check fix_at_operand
#fren_check fix_at_agrees
#fren_check fix_all_laws
```
