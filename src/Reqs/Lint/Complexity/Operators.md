# Operators

## Conditional operands

A conditional is an atom, but its `else` branch extends as far right as
possible (see [Conditionals](../../Lang/Expressions.md#conditionals)): `2 * if
c? then x else y + 1` means `2 * (if c? then x else (y + 1))`, not `(2 * if
c? then x else y) + 1`. `else_extends` fires on a conditional, not in
parentheses, that is an operand of a binary operator, and whose `else`
branch would need parentheses in its place, as an operand of that
operator, under `lang::operand`. If the `else` branch is itself a
conditional not in parentheses, its own `else` branch counts instead, and
so on. The fix puts that branch in parentheses, as it is parsed, which
keeps the meaning and the guards, and shows where it ends:

```fren
pub mod lint

use lang::{Assoc, operand}

pub proc else_extends(
    outer: Int,          -- the precedence of the operator
    inner: Int,          -- the precedence of the `else` branch's operator
    assoc: Assoc,        -- the associativity of the operator
    right?,              -- the conditional is the operator's right operand
): (det fires?) {
    call place := operand(outer, inner, assoc, right?)

    ensure rule: fires? iff not place.bare?
}
```

## Identities

`identity_op` fires on an operation that leaves one operand as it is, and
its fix is that operand:

| Written | Fix |
|---|---|
| `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x`, `x div 1` | `x` |
| `s ++ ""`, `"" ++ s`, `q ++ []`, `[] ++ q` | `s`, `q` |
| `a union {}`, `{} union a`, `a minus {}` | `a` |

It also fires on `x + -y`, whose fix is `x - y`, and on `x - -y`, whose fix
is `x + y`. The fix has the operation's value and its type: the operands
of `+`, `-`, `*`, `++`, `union` and `minus` have the same type as the
result, and `""`, `[]` and `{}` are their identities, as `0` is of `+` and
`-` and `1` of `*` and `div`; `x div 1` is a `Nat` exactly where `x` is,
since `1` is positive; `[]` and `{}` take their type from the other operand,
which keeps it. The operand removed is a literal, or a negation whose
operand the fix evaluates where it was, so the fix keeps the guards.
`lint::identity_op` states what the fix is, from the operator and what
each operand is:

```fren
pub enum IdentityOperator { Add, Sub, Mul, Concat, Union, Minus, Div }

-- An operand as written: `Empty` is `""`, `[]` or `{}`, and `Negation` is `-y`.
pub enum IdentityOperand { Zero, One, Empty, Negation, Other }

pub enum Rewrite { KeepLeft, KeepRight, Flip, Unchanged }

pub proc identity_op(op: IdentityOperator, left: IdentityOperand, right: IdentityOperand): (
    det rewrite: Rewrite,         -- `Flip` is `x - y` for `x + -y`, and `x + y` for `x - -y`
) {
    use self::IdentityOperand::{Empty, Negation, One, Zero}
    use self::IdentityOperator::{Add, Concat, Div, Minus, Mul, Sub, Union}
    use self::Rewrite::{Flip, KeepLeft, KeepRight, Unchanged}

    ensure rule: rewrite = match op {
        Add | Sub if right = Zero => KeepLeft,
        Add if left = Zero => KeepRight,
        Add | Sub if right = Negation => Flip,
        Mul if right = One => KeepLeft,
        Mul if left = One => KeepRight,
        Div if right = One => KeepLeft,
        Concat | Union | Minus if right = Empty => KeepLeft,
        Concat | Union if left = Empty => KeepRight,
        _ => Unchanged,
    }

    expect flips_only_sums: when rewrite = Flip, op in {Add, Sub}
}
```

## Parentheses

`double_parens` fires on parentheses directly around parentheses, with
nothing but whitespace between them: `((e))` means what `(e)` means. It
fires once for each run of such pairs, at the outermost, and its fix keeps
only the innermost: `(((e)))` becomes `(e)`. The parentheses of an
application, a method call or a pair are its own, not around an argument
or an element, so `f((x))` and `(1, (x))` each have one pair around `x`.
Parentheses around a receiver are around it alone, so `(({1}).card)` has
one pair around `{1}` and one around `({1}).card`, not two around `{1}`.
Parentheses only group, so the fix
changes neither the meaning nor the guards. `lint::double_parens` states
when it fires:

```fren
pub proc double_parens(
    depth: Int,          -- pairs of parentheses, each directly around the next
): (det fires?) {
    assume counts: depth >= 1

    ensure rule: fires? iff depth >= 2
}
```

## Cardinality

`manual_at_most_one` fires on a run of adjacent conjuncts of an `and`,
each `not (a and b)` of two different operands, that negate each pair of
three or more operands, and is fixable: `not (a? and b?) and not
(a? and c?) and not (b? and c?)` becomes `at_most_one?(a?, b?, c?)` (see
[Cardinality](../../Lang/Expressions.md#cardinality)). Where the conjunct
just before or after the run is the disjunction of exactly those
operands, as in `(a? or b? or c?) and not (a? and b?) and ...`, the run takes
it in, and the fix is `exactly_one?(a?, b?, c?)`. Operands are compared
as [written the same](../../Lint.md#written-the-same), and a pair may be
written either way round, as in `not (b? and a?)`, or more than once,
which the conjunction means the same with. The run of `and` is
read as [`chainable_comparison`](../Style/Comparisons.md#chained-comparisons)
reads it, and a conjunct in parentheses is not in a run, so `p? and not
(a? and b?) and ...` fires at the conjuncts after `p?`. The message is
reported from the first conjunct it replaces to the last. The fix writes
each operand once, as the disjunction orders them, or else in the order
they are first written, and there is no fix where a comment is within the
conjuncts, which the call would lose; the message then suggests the call.

`n` operands take `n * (n - 1) / 2` such conjuncts, and one left out is
hard to see among the rest. With two, `not (a? and b?)` is as clear as
`at_most_one?(a?, b?)`, so the lint does not fire. The fix keeps the
meaning: at most one argument of `at_most_one?` holds exactly when no two
of them hold together, and `exactly_one?` holds where, besides, one of them
does. It keeps the guards where it fires: in the conjunction, each operand
is [guarded](../../Lang/Expressions.md#sequences) by the operands before
it, and the arguments of a cardinality operator by none, so the lint does
not fire where an operand gives a [definedness](../../Check.md#definedness)
obligation, which a guard could discharge: an index `q[i]`, a
[table](../../Lang/Expressions.md#tables), or a name of a `let` or `where`
whose definition gives one, as in `not (ok? and big?) and ... where big? :=
q[i] > 0`. Operands without one are defined wherever they are evaluated,
under any guard. Clippy has no counterpart.
`lint::manual_at_most_one` models the run as the set of conjuncts `not
(a and b)` it reads, each with its two operands and whether the `and` gives a
definedness obligation, and the operands of the disjunction just before or
after it, if there is one. Operands are the four of
[`lint::Operand`](../Meaning.md#expressions-as-written), enough to
tell every case of the rule apart. The procedure states when
the lint fires, which call the fix is, and that the fix holds exactly where
the conjuncts do, for every set of operands that hold:

```fren
-- `not (first and second)`, where `obligation?` says that the `and` gives a
-- definedness obligation.
pub struct PairNegation { first: Operand, second: Operand, obligation? }

-- Some conjunct is `not (x and y)`.
fn pair_negated?(pairs: Set<PairNegation>, x: Operand, y: Operand) :=
    PairNegation { first := x, second := y, obligation? := true } in pairs
    or PairNegation { first := x, second := y, obligation? := false } in pairs

-- `x` is an operand of some conjunct.
fn named?(pairs: Set<PairNegation>, x: Operand) := exists (y: Operand), pair_negated?(pairs, x, y) or pair_negated?(pairs, y, x)

pub proc manual_at_most_one(
    pairs: Set<PairNegation>,     -- the run of conjuncts `not (a and b)`
    disjunction: Set<Operand>,    -- the operands of the disjunction beside them; `{}` if there is none
): (
    det fires?,
    det exactly?,                 -- the fix is `exactly_one?`, rather than `at_most_one?`
) {
    ensure rule: fires? iff ((exists (x y z: Operand), x != y and x != z and y != z
        and named?(pairs, x) and named?(pairs, y) and named?(pairs, z))
        and (forall (x: Operand), not pair_negated?(pairs, x, x))
        and (forall (x y: Operand), when x != y and named?(pairs, x) and named?(pairs, y),
        pair_negated?(pairs, x, y) or pair_negated?(pairs, y, x))
        and not (exists (x y: Operand), PairNegation { first := x, second := y, obligation? := true } in pairs))
    ensure fix: exactly? iff (disjunction != {} and (forall (x: Operand), x in disjunction iff named?(pairs, x)))
}
```

The fix keeps the meaning: `holds` is the set of operands that hold, and
where the lint fires, the conjuncts hold exactly where at most one named
operand does, and with the disjunction, exactly where one does:

```fren
proc manual_at_most_one_meaning(
    pairs: Set<PairNegation>,
    disjunction: Set<Operand>,
    holds: Set<Operand>,
) {
    call m := manual_at_most_one(pairs, disjunction)

    expect at_most: when m.fires?,
        (forall (x y: Operand), when pair_negated?(pairs, x, y), not (x in holds and y in holds))
        iff (forall (x y: Operand), when x != y and named?(pairs, x) and named?(pairs, y), not (x in holds and y in holds))
    expect exactly: when m.fires? and m.exactly?,
        ((exists (x: Operand), x in disjunction and x in holds)
        and (forall (x y: Operand), when pair_negated?(pairs, x, y), not (x in holds and y in holds)))
        iff (exists (x: Operand), named?(pairs, x) and x in holds
        and (forall (y: Operand), when y != x and named?(pairs, y), not y in holds))
}
```

`lint::manual_at_most_one` names the operands by the four of
`lint::Operand`, which is enough to tell the cases of the rule apart and
keeps the procedure in the decidable core, so that `decide` checks its
implementation over every list of conjuncts. `lint::manual_at_most_one_any`
states the same rule precisely, over any number of operands, each a
string, as written, since the lint compares operands as written, with
[unbounded quantifiers](../../Lang/Quantifiers.md#unbounded-quantifiers)
over them. It is outside the decidable core, and its implementation is
proved in Lean of the lint's code, for every run of conjuncts: each
`forall` of the rule is a `∀` of the theorem. The two are the pattern for a
lint's spec: the precise one proved of the code, and the bounded one a
`decide` check of it.

```fren
-- `not (first and second)`, where `obligation?` says that the `and` gives a
-- definedness obligation, with its operands as written.
pub struct WrittenNegation { first: String, second: String, obligation? }

-- Some conjunct is `not (x and y)`.
fn written_negated?(pairs: Set<WrittenNegation>, x: String, y: String) :=
    exists (o?: Bool), WrittenNegation { first := x, second := y, obligation? := o? } in pairs

-- `x` is an operand of some conjunct.
set_option fren.lint.undecidable "allow" in
fn written_named?(pairs: Set<WrittenNegation>, x: String) :=
    exists (p: WrittenNegation), p in pairs and (p.first = x or p.second = x)

set_option fren.lint.undecidable "allow" in
pub proc manual_at_most_one_any(
    pairs: Set<WrittenNegation>,      -- the run of conjuncts `not (a and b)`
    disjunction: Set<String>,         -- the operands of the disjunction beside them; `{}` if there is none
): (
    det fires?,
    det exactly?,                     -- the fix is `exactly_one?`, rather than `at_most_one?`
) {
    ensure rule: fires? iff ((exists (x y z: String), x != y and x != z and y != z
        and written_named?(pairs, x) and written_named?(pairs, y) and written_named?(pairs, z))
        and (forall (p: WrittenNegation), when p in pairs, p.first != p.second)
        and (forall (x y: String), when x != y and written_named?(pairs, x) and written_named?(pairs, y),
        written_negated?(pairs, x, y) or written_negated?(pairs, y, x))
        and not (exists (p: WrittenNegation), p in pairs and p.obligation?))
    ensure fix: exactly? iff (disjunction != {} and (forall (x: String), x in disjunction iff written_named?(pairs, x)))
}
```

The refinements check both fixes, with the pairs in any order and either
way round:

```fren
set_option fren.lint.manual_at_most_one "allow" in
set_option fren.evidence "enumerated" in
pub proc manual_at_most_one_written(a?, b?, c?, d?): (
    det three?,
    det turned?,
    det four?,
    det exactly?,
    det after?,
) {
    out three? := not (a? and b?) and not (a? and c?) and not (b? and c?)
    out turned? := not (b? and a?) and not (c? and b?) and not (c? and a?)
    out four? := not (a? and b?) and not (a? and c?) and not (a? and d?) and not (b? and c?)
        and not (b? and d?) and not (c? and d?)
    out exactly? := (a? or b? or c?) and not (a? and b?) and not (a? and c?) and not (b? and c?)
    out after? := not (a? and b?) and not (a? and c?) and not (b? and c?) and (c? or a? or b?)
}

set_option fren.evidence "enumerated" in
pub proc manual_at_most_one_fixed(a?, b?, c?, d?): (
    det three?,
    det turned?,
    det four?,
    det exactly?,
    det after?,
) {
    out three? := at_most_one?(a?, b?, c?)
    out turned? := at_most_one?(b?, a?, c?)
    out four? := at_most_one?(a?, b?, c?, d?)
    out exactly? := exactly_one?(a?, b?, c?)
    out after? := exactly_one?(c?, a?, b?)
}

expect manual_at_most_one_sound(a?, b?, c?, d?) {
    call concrete := manual_at_most_one_fixed(a?, b?, c?, d?)
    refines concrete manual_at_most_one_written(a?, b?, c?, d?)
}
expect manual_at_most_one_complete(a?, b?, c?, d?) {
    call concrete := manual_at_most_one_written(a?, b?, c?, d?)
    refines concrete manual_at_most_one_fixed(a?, b?, c?, d?)
}
```

It does not fire where an operand gives an obligation, which `deny`
checks here, with an index in a `where` clause's definition and with a
table:

```fren
set_option fren.lint.manual_at_most_one "deny" in
pub proc manual_at_most_one_guarded(q: Seq<Int>, i: Int, x: Int, z?): (indexed?, tabled?) {
    ensure indexes: indexed? iff not (ok? and big?) and not (ok2? and big?) and not (ok? and ok2?)
        where ok? := 0 <= i < q.len, ok2? := 0 <= i < q.len and z?, big? := q[i] > 0
    ensure tables: tabled? iff not (pos? and t?) and not (pos2? and t?) and not (pos? and pos2?)
        where pos? := x > 0, pos2? := x > 0 and z?, t? := table { x > 0 => true }
}
```

The `obligation?` of a conjunct is what makes the fix keep definedness. In
the conjunct `not (a and b)`, the `and` is an
[`And`](../../Lang/EvaluationRules.md#lazy-boolean-expressions), whose right
operand is evaluated only where its left is true; in the fix, the operands
are the arguments of a [`Count`](../../Lang/EvaluationRules.md#operator-expressions),
which evaluates both. An `and` without an obligation is one whose operands
are well-defined in every environment, so the two are well-defined alike,
whatever the operands' values: the guard that the fix drops was not
needed. `lint::manual_at_most_one_defined` states this over
[evaluation](../../Lang/Semantics.md); with an obligation, the `and` can be
well-defined where the call is not, which is why the lint does not fire
there.

`lint::manual_at_most_one` and `lint::manual_at_most_one_any` are tied to
this only by the assumption `no_obligation`: their `obligation?` is a
field of each conjunct, an input that the lint computes from the
conjunct's syntax, and their implementations read it as one, so it cannot
be defined from evaluation. That the lint's syntactic test gives
`obligation?` wherever an operand may not be well-defined, as
`no_obligation` assumes, is tested, by `lint::manual_at_most_one_guarded`
above and the ui tests, not proved. Its own evidence is testing, which
evaluates both expressions, since the solver unfolds
[`eval`](../../Lang/Semantics.md#the-evaluation-function) one step, and the
call's argument list is two deep:

```fren
set_option fren.evidence "random" in
pub proc manual_at_most_one_defined(
    i: Interp,
    env: Env,
    a: Expr,                         -- the operands
    b: Expr,
    obligation?,                     -- the `and` gives a definedness obligation
) {
    use lang::{Cardinality, Env, Expr, Interp, Outcome, Value, eval}

    -- The operands are `Bool`s where they are well-defined.
    assume booleans: eval(i, env, a) is Outcome::Undefined | Outcome::Defined(Value::True | Value::False)
        and eval(i, env, b) is Outcome::Undefined | Outcome::Defined(Value::True | Value::False)
    assume no_obligation: unless obligation?, eval(i, env, a) is Outcome::Defined(_) and eval(i, env, b) is Outcome::Defined(_)

    let conjunct: Outcome := eval(i, env, Expr::And(a, b))
    let counted: Outcome := eval(i, env, Expr::Count(Cardinality::AtMost, Expr::Cons(a, Expr::Cons(b, Expr::Nil))))

    expect kept: unless obligation?, conjunct is Outcome::Defined(_) and counted is Outcome::Defined(_)
    -- With an obligation, the `and`'s guard can be what makes it well-defined.
    cover guard_needed: obligation? and conjunct is Outcome::Defined(_) and counted = Outcome::Undefined
}
```
