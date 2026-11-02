# Fixes as rewrites

A lint whose rule and fix are stated over the [syntax of the
semantics](../Lang/Semantics.md#abstract-syntax), `lang::Expr<V>`, is a rewrite
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

Each lint is stated by two functions over `lang::Expr<V>`, at the place
where it fires: whether it fires on an expression, and what its fix writes
there, both [generic](../Lang/GenericFunctions.md) in the type `V` of
names, which they only compare (see [Renaming](#renaming)).
`lint::ExprLint` names them, and `fires_at?` and `fix_at` give each one's
functions:

- [`overly_complex_bool_expr`](Pedantic/Booleans.md#the-rule-over-the-syntax-of-the-semantics);
- [`double_neg`](Style.md#negations-over-the-syntax-of-the-semantics);
- [`int_plus_one`](Complexity/Comparisons.md#off-by-one-comparisons-over-the-syntax-of-the-semantics);
- [`manual_abs` and `manual_abs_diff`](Complexity/Integers.md#absolute-values-over-the-syntax-of-the-semantics);
- [`unless_not` and `collapsible_when`](Style.md#conditionals-over-the-syntax-of-the-semantics);
- [`same_branches`](Suspicious/Expressions.md#branches-written-the-same-over-the-syntax-of-the-semantics);
- [`neg_multiply`](Style.md#products-with--1-over-the-syntax-of-the-semantics);
- [`identity_op`](Complexity/Operators.md#identities-over-the-syntax-of-the-semantics);
- [`manual_rem_euclid`](Complexity/Integers.md#remainders-over-the-syntax-of-the-semantics).

`fix_all` below applies `fix_at` in each of its arms, and `fires_in?`
applies `fires_at?`, and each lint's functions are definitions of their
own, so the cost of compiling either does not grow with the lints. It did
while the solver's copy of a structural recursion was its body with the
functions it applies unfolded, which put all of `fix_at` in each arm:
compiling `fix_all` took 83M of Lean's raw heartbeats with one lint and
126M with five, against a limit of 200M, and each lint whose test is a
conditional added about 14M. That copy is now the recursion itself
([Generated](../Generated.md#matches)), and compiling `fix_all` took 57M,
with five lints or seven. Over `Expr<V>`, whose constructions and
selectors carry the type of names, it takes 97M, and `fires_in?` 104M,
with seven.

```fren
-- The lints stated over the syntax of the semantics.
pub enum ExprLint {
    OverlyComplexBoolExpr,
    DoubleNeg,
    IntPlusOne,
    ManualAbs,
    ManualAbsDiff,
    UnlessNot,
    CollapsibleWhen,
    SameBranches,
    NegMultiply,
    IdentityOp,
    ManualRemEuclid,
}

pub fn fires_at?<V>(l: ExprLint, e: Expr<V>) := match l {
    ExprLint::OverlyComplexBoolExpr => overly_complex_fires?(e),
    ExprLint::DoubleNeg => double_neg_fires?(e),
    ExprLint::IntPlusOne => int_plus_one_fires?(e),
    ExprLint::ManualAbs => manual_abs_fires?(e),
    ExprLint::ManualAbsDiff => manual_abs_diff_fires?(e),
    ExprLint::UnlessNot => unless_not_fires?(e),
    ExprLint::CollapsibleWhen => collapsible_when_fires?(e),
    ExprLint::SameBranches => same_branches_fires?(e),
    ExprLint::NegMultiply => neg_multiply_fires?(e),
    ExprLint::IdentityOp => identity_op_fires?(e),
    ExprLint::ManualRemEuclid => manual_rem_euclid_fires?(e),
}

pub fn fix_at<V>(l: ExprLint, e: Expr<V>): Expr<V> := match l {
    ExprLint::OverlyComplexBoolExpr => overly_complex_fix(e),
    ExprLint::DoubleNeg => double_neg_fix(e),
    ExprLint::IntPlusOne => int_plus_one_fix(e),
    ExprLint::ManualAbs => manual_abs_fix(e),
    ExprLint::ManualAbsDiff => manual_abs_diff_fix(e),
    ExprLint::UnlessNot => unless_not_fix(e),
    ExprLint::CollapsibleWhen => collapsible_when_fix(e),
    ExprLint::SameBranches => same_branches_fix(e),
    ExprLint::NegMultiply => neg_multiply_fix(e),
    ExprLint::IdentityOp => identity_op_fix(e),
    ExprLint::ManualRemEuclid => manual_rem_euclid_fix(e),
}
```

The laws of the fixes below rest on three facts about each lint, which
each arm of `ExprLint` owes. Where the lint does not fire, its fix is the
expression itself (`fix_at_unfired`). Its fix agrees with the expression
(`fix_at_agrees`), as each lint's own procedure states, such as
[`overly_complex_keeps_meaning`](Pedantic/Booleans.md#the-fix-keeps-the-meaning).
And where the lint fires within no operand of an expression, it fires
nowhere within the fix (`fix_at_fixed`, stated [with
`fires_in?`](#fixing-everywhere)), so once the operands are fixed,
the fix leaves nothing to fix. The fix of `overly_complex_bool_expr`
writes an operand or a literal, and that of `double_neg` an operand's
operand, which are fixed where the operands are. That of `int_plus_one`
writes a new node, `<`, of operands that are fixed, and the lint does not
fire on a `<`. Those of `manual_abs` and `manual_abs_diff` write a call of
`abs`, on which they do not fire, of an operand or an operand's operand.
That of `unless_not` writes a conditional of an operand's operand and an
operand, whose `else` branch is `true`, on which it does not fire. Those
of `collapsible_when` write a conditional of a new `and` or `or` and of
the nested conditional's body, on which it fires only where that body is
another nested conditional, which would make the nested one fire. That
of `same_branches` writes an operand. That of `neg_multiply` writes a
negation, on which it does not fire, of an operand. That of `identity_op`
writes an operand, or an operation of an operand and an operand's operand
on which it does not fire. That of `manual_rem_euclid` writes an
operand's operand.

The fixes of `neg_multiply`, `identity_op` and `manual_rem_euclid` rest
on [primitive operations](Meaning.md#primitive-operations), `*`, `div`,
`mod` and `++` of strings, so they agree only in an interpretation that
gives them their usual meaning, as the language's does.
`uses_primitives?` names these lints, and `fits?(l, i)` says that `i` is
such an interpretation for `l`. Each law that is about meaning assumes
it. The other lints agree in every interpretation.

A lint whose fix may write something that it fires on, from operands
that are fixed, does not meet the last fact. The De Morgan rewrites of
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions) are one: `not
(a and b)` becomes `not a or not b`, which it rewrites again where `a` is
an `or`. For such a lint, fixing the operands and then the expression
once is not a normal form, and fixing everywhere would have to fix again
until nothing changes, which needs a measure that decreases other than
the size of the expression.

```fren
-- The lints whose fixes rest on the primitive operations.
pub fn uses_primitives?(l: ExprLint) := l in {
    ExprLint::NegMultiply,
    ExprLint::IdentityOp,
    ExprLint::ManualRemEuclid,
}

-- `i` gives the primitive operations that `l`'s fix rests on their usual meaning.
pub fn fits?(l: ExprLint, i: lang::Interp) := not uses_primitives?(l) or usual?(i.primitives)

expect fix_at_unfired(l: ExprLint, e: Expr<lang::Id>) {
    expect unfired: unless fires_at?(l, e), fix_at(l, e) = e
}

set_option fren.evidence "random" in
pub proc fix_at_agrees(l: ExprLint, e: Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure agrees: when fits?(l, i), agrees?(lang::eval(i, env, fix_at(l, e)), lang::eval(i, env, e))
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
pub fn fires_in?(l: ExprLint, e: Expr<lang::Id>) := fires_at?(l, e) or match e {
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

-- `l` fires within no operand of `e`, as `fires_in?` looks within them.
pub fn operands_fixed?(l: ExprLint, e: Expr<lang::Id>) := match e {
    Expr::Let(_, _, b) => not fires_in?(l, b),
    Expr::Unary(_, a) => not fires_in?(l, a),
    Expr::Binary(_, a, b) => not fires_in?(l, a) and not fires_in?(l, b),
    Expr::And(a, b) => not fires_in?(l, a) and not fires_in?(l, b),
    Expr::Or(a, b) => not fires_in?(l, a) and not fires_in?(l, b),
    Expr::If(c, t, f) => not fires_in?(l, c) and not fires_in?(l, t) and not fires_in?(l, f),
    Expr::Is(s, _) => not fires_in?(l, s),
    Expr::Match(s, _, g, b, rest) => not fires_in?(l, s) and not fires_in?(l, g) and not fires_in?(l, b)
        and not fires_in?(l, rest),
    Expr::Cons(a, rest) => not fires_in?(l, a) and not fires_in?(l, rest),
    Expr::Construct(_, args) => not fires_in?(l, args),
    Expr::Project(a, _, _) => not fires_in?(l, a),
    Expr::Index(q, k) => not fires_in?(l, q) and not fires_in?(l, k),
    Expr::Method(_, r, args) => not fires_in?(l, r) and not fires_in?(l, args),
    Expr::Count(_, args) => not fires_in?(l, args),
    Expr::Apply(_, args, _, body) => not fires_in?(l, args) and not fires_in?(l, body),
    Expr::Call(_, args) => not fires_in?(l, args),
    Expr::Recur(_, args) => not fires_in?(l, args),
    _ => true,
}

set_option fren.evidence "random" in
pub proc fix_at_fixed(l: ExprLint, e: Expr<lang::Id>) {
    ensure fixed: when operands_fixed?(l, e), not fires_in?(l, fix_at(l, e))
}

-- `e` with `l` fixed everywhere, operands first.
pub fn fix_all(l: ExprLint, e: Expr<lang::Id>): Expr<lang::Id> := match e {
    Expr::Let(x, d, b) => fix_at(l, Expr::Let(x, d, fix_all(l, b))),
    Expr::Unary(op, a) => fix_at(l, Expr::Unary(op, fix_all(l, a))),
    Expr::Binary(op, a, b) => fix_at(l, Expr::Binary(op, fix_all(l, a), fix_all(l, b))),
    Expr::And(a, b) => fix_at(l, Expr::And(fix_all(l, a), fix_all(l, b))),
    Expr::Or(a, b) => fix_at(l, Expr::Or(fix_all(l, a), fix_all(l, b))),
    Expr::If(c, t, f) => fix_at(l, Expr::If(fix_all(l, c), fix_all(l, t), fix_all(l, f))),
    Expr::Is(s, p) => fix_at(l, Expr::Is(fix_all(l, s), p)),
    Expr::Match(s, p, g, b, rest) => fix_at(
        l,
        Expr::Match(
            fix_all(l, s),
            p,
            fix_all(l, g),
            fix_all(l, b),
            fix_all(l, rest)
        )
    ),
    Expr::Cons(a, rest) => fix_at(l, Expr::Cons(fix_all(l, a), fix_all(l, rest))),
    Expr::Construct(c, args) => fix_at(l, Expr::Construct(c, fix_all(l, args))),
    Expr::Project(a, c, k) => fix_at(l, Expr::Project(fix_all(l, a), c, k)),
    Expr::Index(q, k) => fix_at(l, Expr::Index(fix_all(l, q), fix_all(l, k))),
    Expr::Method(m, r, args) => fix_at(l, Expr::Method(m, fix_all(l, r), fix_all(l, args))),
    Expr::Count(c, args) => fix_at(l, Expr::Count(c, fix_all(l, args))),
    Expr::Apply(f, args, ps, body) => fix_at(
        l,
        Expr::Apply(f, fix_all(l, args), ps, fix_all(l, body))
    ),
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
written, in every interpretation that `fits?` the lint and every
environment (`keeps_meaning`). These
follow from the [facts about each lint](#each-lint-where-it-fires) at the
place where it fires: `fix_at_unfired`, `fix_at_agrees` and
`fix_at_fixed`. The fix at one place alone need not fix the lint, as
`overly_complex_refires`, `double_neg_refires`, `manual_abs_refires`,
`collapsible_when_refires`, `same_branches_refires`,
`neg_multiply_refires`, `identity_op_refires` and
`manual_rem_euclid_refires` show: these laws are of fixing everywhere. For `int_plus_one` and `unless_not` it does, as
`int_plus_one_once` and `unless_not_once` show. That the passes of `fren
fix` end where `fix_all` does is a property of the passes, which these
laws do not state.

The laws are about every expression, and so by induction on it, which the
solver does not do: `src/Impls/Rewrites.lean` proves them in Lean, for
every lint, expression, interpretation that `fits?` it and environment,
from those facts and from evaluation being monotone in the operands:
where each operand of an expression agrees with another, in every
environment, so does the expression with those operands replaced.
`fix_all` leaves the definition of a `let` as written, so the
environments in which it fixes operands are the same as those in which
the expression as written evaluates them. `fren check` tests them:

```fren
set_option fren.evidence "random" in
pub proc fix_all_laws(l: ExprLint, e: Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure fixed: not fires_in?(l, fix_all(l, e))
    ensure unchanged: unless fires_in?(l, e), fix_all(l, e) = e
    ensure idempotent: fix_all(l, fix_all(l, e)) = fix_all(l, e)
    ensure keeps_meaning: when fits?(l, i), agrees?(lang::eval(i, env, fix_all(l, e)), lang::eval(i, env, e))
}
```

## Renaming

A lint's rule and fix are stated over `Expr<V>`, for a type `V` of names
of which nothing is known but whether two of them are equal, and that it
has a value, its `Inhabited` default: `fires_at?` and `fix_at` are
[generic](../Lang/GenericFunctions.md) in `V`. So renaming every name of
an expression apart, free and bound alike, so that names that differed
still differ, changes neither whether a lint fires on it nor, but for the
renaming, what its fix writes: what a lint computes does not depend on how
the names are spelled. `fires_in?` and `fix_all` look within the operands
of an expression and fix them, and so, being recursive, are [not
generic](../Lang/Recursion.md); they are stated at `Expr<lang::Id>`, and
only apply `fires_at?` and `fix_at`, so this holds of them too. It is
proved for every lint, each by its definition, not by the genericity
alone: Lean does not know that a function generic in `V` uses only
equality, and a new lint needs its own lemma.

This is not the law of [#494](https://github.com/langston-barrett/fren/issues/494)
that renaming *bound* names consistently, to an alpha-variant, changes
nothing. That one does not hold: renaming one bound name alone can change
which names are equal, as `bound_renaming` shows, where `b` is the
negation of `a` only once `y` is renamed `x`, and only then does
`overly_complex_bool_expr` fire. Stating that law needs names compared by
binding, as an `Expr<Binding>` would.

`swap_names(a, b, e)` is `e` with the names `a` and `b` swapped, at every
variable, binder, `let` and parameter. A renaming of the names of an
expression apart is a sequence of such swaps, since it renames only the
finitely many names of the expression and there are names to spare, so
`renamed_apart` states it for one swap. `src/Impls/Renaming.lean` proves
it in Lean, for every renaming apart, at the place where each lint fires
for every type of names, and everywhere by induction on the expression;
`fren check` tests it:

```fren
-- `x`, with the names `a` and `b` swapped.
pub fn swapped(a: lang::Id, b: lang::Id, x: lang::Id): lang::Id := if x = a then b else if x = b then a else x

pub fn swap_pattern(
    a: lang::Id,
    b: lang::Id,
    p: lang::Pattern<lang::Id>
): lang::Pattern<lang::Id> := match p {
    lang::Pattern::Binder(x) => lang::Pattern::Binder(swapped(a, b, x)),
    lang::Pattern::Variant(c, ps) => lang::Pattern::Variant(c, swap_pattern(a, b, ps)),
    lang::Pattern::Cons(first, rest) => lang::Pattern::Cons(
        swap_pattern(a, b, first),
        swap_pattern(a, b, rest)
    ),
    lang::Pattern::Or(p1, p2) => lang::Pattern::Or(swap_pattern(a, b, p1), swap_pattern(a, b, p2)),
    _ => p,
}

pub fn swap_params(a: lang::Id, b: lang::Id, ps: lang::Params<lang::Id>): lang::Params<lang::Id> := match ps {
    lang::Params::Cons(x, rest) => lang::Params::Cons(swapped(a, b, x), swap_params(a, b, rest)),
    lang::Params::Nil => lang::Params::Nil,
}

-- `e`, with the names `a` and `b` swapped.
pub fn swap_names(a: lang::Id, b: lang::Id, e: Expr<lang::Id>): Expr<lang::Id> := match e {
    Expr::Var(x) => Expr::Var(swapped(a, b, x)),
    Expr::Let(x, d, body) => Expr::Let(
        swapped(a, b, x),
        swap_names(a, b, d),
        swap_names(a, b, body)
    ),
    Expr::Unary(op, x) => Expr::Unary(op, swap_names(a, b, x)),
    Expr::Binary(op, x, y) => Expr::Binary(op, swap_names(a, b, x), swap_names(a, b, y)),
    Expr::And(x, y) => Expr::And(swap_names(a, b, x), swap_names(a, b, y)),
    Expr::Or(x, y) => Expr::Or(swap_names(a, b, x), swap_names(a, b, y)),
    Expr::If(c, t, f) => Expr::If(
        swap_names(a, b, c),
        swap_names(a, b, t),
        swap_names(a, b, f)
    ),
    Expr::Is(s, p) => Expr::Is(swap_names(a, b, s), swap_pattern(a, b, p)),
    Expr::Match(s, p, g, body, rest) => Expr::Match(
        swap_names(a, b, s),
        swap_pattern(a, b, p),
        swap_names(a, b, g),
        swap_names(a, b, body),
        swap_names(a, b, rest)
    ),
    Expr::Cons(x, rest) => Expr::Cons(swap_names(a, b, x), swap_names(a, b, rest)),
    Expr::Construct(c, args) => Expr::Construct(c, swap_names(a, b, args)),
    Expr::Project(x, c, k) => Expr::Project(swap_names(a, b, x), c, k),
    Expr::Index(q, k) => Expr::Index(swap_names(a, b, q), swap_names(a, b, k)),
    Expr::Method(m, r, args) => Expr::Method(m, swap_names(a, b, r), swap_names(a, b, args)),
    Expr::Count(c, args) => Expr::Count(c, swap_names(a, b, args)),
    Expr::Apply(f, args, ps, body) => Expr::Apply(
        f,
        swap_names(a, b, args),
        swap_params(a, b, ps),
        swap_names(a, b, body)
    ),
    Expr::Call(f, args) => Expr::Call(f, swap_names(a, b, args)),
    Expr::Recur(f, args) => Expr::Recur(f, swap_names(a, b, args)),
    _ => e,
}

set_option fren.evidence "random" in
pub proc renamed_apart(l: ExprLint, e: Expr<lang::Id>, a: lang::Id, b: lang::Id) {
    ensure fires_at: fires_at?(l, swap_names(a, b, e)) = fires_at?(l, e)
    ensure fix_at: fix_at(l, swap_names(a, b, e)) = swap_names(a, b, fix_at(l, e))
    ensure fires_in: fires_in?(l, swap_names(a, b, e)) = fires_in?(l, e)
    ensure fix_all: fix_all(l, swap_names(a, b, e)) = swap_names(a, b, fix_all(l, e))
}

-- `x` and `y` bound alike, but apart: an alpha-variant of `a` is
-- `Let(y, true, Var(y))`, and renaming it back makes the lint fire.
expect bound_renaming(x: lang::Id, y: lang::Id) {
    expect apart: when x != y, not overly_complex_fires?(
        Expr::Or(
            Expr::Let(x, Expr::Literal(lang::Value::True), Expr::Var(x)),
            Expr::Unary(
                lang::UnaryOp::Not,
                Expr::Let(y, Expr::Literal(lang::Value::True), Expr::Var(y))
            )
        )
    )
    expect renamed: overly_complex_fires?(
        Expr::Or(
            Expr::Let(x, Expr::Literal(lang::Value::True), Expr::Var(x)),
            Expr::Unary(
                lang::UnaryOp::Not,
                Expr::Let(x, Expr::Literal(lang::Value::True), Expr::Var(x))
            )
        )
    )
}
```

```fren
#fren_check fix_at_unfired
#fren_check fix_at_fixed
#fren_check fix_at_agrees
#fren_check fix_all_laws
#fren_check renamed_apart
#fren_check bound_renaming
```
