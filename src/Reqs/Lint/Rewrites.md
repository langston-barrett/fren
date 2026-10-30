# Fixes as rewrites

A lint whose rule and fix are stated over the [syntax of the
semantics](../Lang/Semantics.md#abstract-syntax), `lang::Expr`, is a rewrite
rule: where it fires on an expression, its fix replaces that expression.
This chapter states, for every such lint at once, what fixing it everywhere
means, and three laws: fixing everywhere leaves nothing for the lint to
fire on, so fixing again changes nothing, and it
[agrees](Meaning.md#fixes-that-agree) with the expression as written.

```fren
pub mod lint
```

## Fixes as rewrites

Each lint is stated by two functions over `lang::Expr`, at the place where
it fires: whether it fires on an expression, and what its fix writes
there, which is the expression itself where the lint does not fire on it
(`fix_at_unfired`). Each lint states that its fix agrees with the expression where it
fires: [`overly_complex_keeps_meaning`](Pedantic/Booleans.md#the-fix-keeps-the-meaning)
for `overly_complex_bool_expr`, the only one so far. `lint::ExprLint` names
them, and `fires_at?` and `fix_at` give each one's functions:

```fren
-- The lints stated over the syntax of the semantics.
pub enum ExprLint { OverlyComplexBoolExpr }

-- One lint so far: with more, each is an arm.
set_option fren.lint.trivial_match "allow" in
pub fn fires_at?(l: ExprLint, e: Expr) := match l {
    ExprLint::OverlyComplexBoolExpr => overly_complex_fires?(e),
}

set_option fren.lint.trivial_match "allow" in
pub fn fix_at(l: ExprLint, e: Expr): Expr := match l {
    ExprLint::OverlyComplexBoolExpr => overly_complex_fix(e),
}

expect fix_at_unfired(l: ExprLint, e: Expr) {
    expect unfired: unless fires_at?(l, e), fix_at(l, e) = e
}
```

A lint fires within an expression where it fires on the expression or
within one of its operands. As [the lints that rewrite an
expression](../Lint.md#parentheses-in-fixes) do, it looks within the body
of a `let`, but not within its definition. `fix_all` fixes it everywhere,
operands first: it fixes the operands, and then the expression that they
make. That is where fixing the lint over and
over ends; `fren fix` does it in passes, each of which makes the outermost
of the fixes that overlap.

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
follow from two facts about each lint at the place where it fires: its fix
agrees there, and once the operands are fixed, the fix leaves nothing to fix,
as [`overly_complex_operand`](Pedantic/Booleans.md#the-fix-keeps-the-meaning)
states for `overly_complex_bool_expr`. The fix at one place alone need not
fix the lint, as `overly_complex_refires` shows: these laws are of fixing
everywhere. That the passes of `fren fix` end where `fix_all` does is a
property of the passes, which these laws do not state.

The laws are about every expression, and so by induction on it, which the
solver does not do: `src/Impls/Rewrites.lean` proves them in Lean, for
every lint, expression, interpretation and environment, from those two
facts and from evaluation being monotone in the operands: where each
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
#fren_check fix_all_laws
```
