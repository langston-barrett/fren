# Boolean operands

This lint of the `pedantic` group looks at the operands of `and` and `or`.
It is stated over the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
`lang::Expr`, and its fix is checked with the semantics' own
[evaluation](../../Lang/Semantics.md#the-evaluation-function), as
[Fixes as rewrites](../Rewrites.md) states for every such lint.

```fren
pub mod lint

use lang::Expr
```

## Operands that can be dropped

`overly_complex_bool_expr`, `allow` by default, fires on an `and` or an
`or` with an operand that can be dropped, its operands compared as
[written the same](../../Lint.md#written-the-same), in either order:

| Rule | Written | Fix |
|---|---|---|
| absorption | `a or (a and b)`, `a or (b and a)`, `(a and b) or a`, `(b and a) or a` | `a` |
| absorption | `a and (a or b)`, `a and (b or a)`, `(a or b) and a`, `(b or a) and a` | `a` |
| contradiction | `a and not a`, `not a and a` | `false` |
| excluded middle | `a or not a`, `not a or a` | `true` |

The fix is in parentheses where [fixes need
them](../../Lint.md#parentheses-in-fixes). Where the expression is an
operand in parentheses of its own, the fix replaces them too, so that
`((a? or b?) and a?) or c?` becomes `a? or c?`, not `(a?) or c?`. The
lint looks at the operands of the operator alone: in `a or (a and b and
c)`, the right operand is `(a and b) and c`, whose operands are not `a`.
Its Clippy counterpart is in `correctness`.

[`eq_op`](../Suspicious/Expressions.md#operands-written-the-same) reports an
operator whose operands are written the same, and this lint one whose
operands are not, so no expression is reported by both. It does not fire
where the negation `not a` has a simpler form that
[`nonminimal_bool`](../Complexity.md#simpler-bool-expressions) reports, as in `x
= 1 and not x = 1`: its fix, `x = 1 and x != 1`, is
[`contradictory_comparisons`](../Suspicious/Comparisons.md) when the values
are integers.

### The rule, over the syntax of the semantics

In the semantics, an expression is its
[elaboration](../../Lang/Semantics.md#abstract-syntax), and two operands
written the same in one scope are the same `lang::Expr`, as
[`written`](../Meaning.md#expressions-as-written) states. So the table above
is, over `lang::Expr`: an `and` fires where one operand is an `or` with the
other as an operand of its own, or where one operand is `not` the other,
and an `or` likewise, with `and` for `or`. The fix keeps the operand that
the absorption leaves, or writes `false` for an `and` and `true` for an
`or`.

```fren
-- `k` is `p or q`, in an `and` (`conj?`), or `p and q`, in an `or`,
-- where `p` or `q` is `o`.
pub fn absorbs_operand?<V>(conj?, k: Expr<V>, o: Expr<V>) := match k {
    Expr::Or(p, q) => conj? and (p = o or q = o),
    Expr::And(p, q) => not conj? and (p = o or q = o),
    _ => false,
}

-- `k` is `not o`.
pub fn negates_operand?<V>(k: Expr<V>, o: Expr<V>) := k = Expr::Unary(lang::UnaryOp::Not, o)

-- An operand of the `and` (`conj?`) or the `or` of `a` and `b` can be dropped.
pub fn drops?<V>(conj?, a: Expr<V>, b: Expr<V>) := absorbs_operand?(conj?, b, a) or absorbs_operand?(conj?, a, b)
    or negates_operand?(a, b) or negates_operand?(b, a)

-- What the fix of `e`, the `and` (`conj?`) or the `or` of `a` and `b`,
-- writes: the operand that the absorption leaves, or the `Bool` that `e`
-- always is; and `e` where no operand can be dropped.
pub fn drop_fix<V>(conj?, a: Expr<V>, b: Expr<V>, e: Expr<V>): Expr<V> := if absorbs_operand?(conj?, b, a) then a
    else if absorbs_operand?(conj?, a, b) then b
    else if negates_operand?(a, b) or negates_operand?(b, a) then Expr::Literal(lang::truth(not conj?))
    else e

pub fn overly_complex_fires?<V>(e: Expr<V>) := match e {
    Expr::And(a, b) => drops?(true, a, b),
    Expr::Or(a, b) => drops?(false, a, b),
    _ => false,
}

pub fn overly_complex_fix<V>(e: Expr<V>): Expr<V> := match e {
    Expr::And(a, b) => drop_fix(true, a, b, e),
    Expr::Or(a, b) => drop_fix(false, a, b, e),
    _ => e,
}
```

Each row of the table is an instance, for every two operands `a` and `b`,
which the solver checks. Where `b` is `a`, `a or ((a and b) and b)` is an
absorption, so `nested` assumes they differ:

```fren
expect overly_complex_rows(a: Expr<lang::Id>, b: Expr<lang::Id>) {
    use lang::UnaryOp::Not

    assume differ: a != b

    expect or_first: overly_complex_fix(Expr::Or(a, Expr::And(a, b))) = a
    expect or_first_swapped: overly_complex_fix(Expr::Or(a, Expr::And(b, a))) = a
    expect or_last: overly_complex_fix(Expr::Or(Expr::And(a, b), a)) = a
    expect or_last_swapped: overly_complex_fix(Expr::Or(Expr::And(b, a), a)) = a
    expect and_first: overly_complex_fix(Expr::And(a, Expr::Or(a, b))) = a
    expect and_first_swapped: overly_complex_fix(Expr::And(a, Expr::Or(b, a))) = a
    expect and_last: overly_complex_fix(Expr::And(Expr::Or(a, b), a)) = a
    expect and_last_swapped: overly_complex_fix(Expr::And(Expr::Or(b, a), a)) = a
    expect contradiction: overly_complex_fix(Expr::And(a, Expr::Unary(Not, a))) = Expr::Literal(lang::Value::False)
        and overly_complex_fix(Expr::And(Expr::Unary(Not, a), a)) = Expr::Literal(lang::Value::False)
    expect excluded_middle: overly_complex_fix(Expr::Or(a, Expr::Unary(Not, a))) = Expr::Literal(lang::Value::True)
        and overly_complex_fix(Expr::Or(Expr::Unary(Not, a), a)) = Expr::Literal(lang::Value::True)
    -- The lint looks at the operands of the operator alone.
    expect nested: not overly_complex_fires?(Expr::Or(a, Expr::And(Expr::And(a, b), b)))
}
```

`lint::overly_complex_bool_expr` binds this to the linter, with the rule
for the message. The linter also leaves the negations that
`nonminimal_bool` rewrites, which the elaborated expression does not show,
since elaboration does not tell `a iff b` from `a = b`. So whether
`nonminimal_bool` rewrites the operand that is a negation is an input,
`negation_rewritten?`, and where it holds, the lint fires by absorption
alone.

The linter's rule is one function, `Core.overlyComplexRule`, generic over
one layer of an expression, a test of whether two operands are the same,
and a test of whether `nonminimal_bool` rewrites a negation. What is
proved and what is trusted:

- Proved: `src/Impls/Rewrites.lean` instantiates it at `lang::Expr`, with
  `=` for being the same and, for whether `nonminimal_bool` rewrites a
  negation, `negation_rewritten?` at an operand that is the negation of an
  operand of `e`, and `false` at any other, and proves that it meets this
  procedure, for every expression. So it checks that the linter asks
  about the operand that is the negation, whichever side it is on.
- Trusted, and checked by the ui tests of the lint: both front ends run it
  at their own expressions as written (`BNode.boolLayer`), with
  [written the same](../../Lint.md#written-the-same) for being the same
  (`writtenSame`) and `nonminimal_bool`'s own rule for the negation
  (`rewritten`), and these read `and`, `or` and `not` as elaboration does.
  Operands written the same are the same `lang::Expr` by `written`, where
  they have no binding pattern test, and the front ends drop every report
  on an expression with one.

So the linter fires only where this procedure does, though not in every
such place: operands whose texts differ but elaborate alike, such as `a iff
b` and `a = b`, or `(a)` and `a`, are the same `lang::Expr`, but not
written the same.

What the fix keeps is `kept_by(e)`: the left operand, the right one or a
`Bool`, by the first test of `drop_fix` that holds, in the order in which
the linter's rule tries them. Saying only that `kept_fix` writes the fix
would leave it open where two of them write the same: in `false and
(false or q)`, `Kept::Left` and `Kept::Constant` both write `false`, and
`kept_by` says `Kept::Left`, as the linter does. That the fix keeps it is
`fix_written`. Stating which one it keeps also makes the procedure's
realizability a query that the solver decides: with `kept`
free, cvc5 1.3 gives up on the `exists` over it, as it does on any such
`exists` over a parametric datatype with a field of its parameter, as
`Expr<lang::Id>` is.

```fren
pub enum BoolRule { Absorption, Contradiction, ExcludedMiddle }

-- What the fix writes: the left operand, the right one, or a `Bool`.
pub enum Kept { Left, Right, Constant }

-- The rule by which the lint fires on `e`, for the message.
pub fn bool_rule<V>(e: Expr<V>): BoolRule := match e {
    Expr::And(a, b) => if absorbs_operand?(true, b, a) or absorbs_operand?(true, a, b) then BoolRule::Absorption
        else BoolRule::Contradiction,
    Expr::Or(a, b) => if absorbs_operand?(false, b, a) or absorbs_operand?(false, a, b) then BoolRule::Absorption
        else BoolRule::ExcludedMiddle,
    _ => BoolRule::Absorption,
}

-- What the fix of an `and`, if `conj?`, or an `or` keeps, by the first test
-- of `drop_fix` that holds.
fn drop_kept<V>(conj?, a: Expr<V>, b: Expr<V>): Kept := if absorbs_operand?(conj?, b, a) then Kept::Left
    else if absorbs_operand?(conj?, a, b) then Kept::Right
    else Kept::Constant

-- What the fix of `e` writes, by `k`.
pub fn kept_fix<V>(e: Expr<V>, k: Kept): Expr<V> := match e, k {
    Expr::And(a, _), Kept::Left => a,
    Expr::And(_, b), Kept::Right => b,
    Expr::And(_, _), Kept::Constant => Expr::Literal(lang::Value::False),
    Expr::Or(a, _), Kept::Left => a,
    Expr::Or(_, b), Kept::Right => b,
    Expr::Or(_, _), Kept::Constant => Expr::Literal(lang::Value::True),
    _, _ => e,
}

-- What the fix of `e` keeps, by the first test of `drop_fix` that holds.
pub fn kept_by<V>(e: Expr<V>): Kept := match e {
    Expr::And(a, b) => drop_kept(true, a, b),
    Expr::Or(a, b) => drop_kept(false, a, b),
    _ => Kept::Constant,
}

pub proc overly_complex_bool_expr(
    e: Expr<lang::Id>,
    negation_rewritten?,  -- `nonminimal_bool` rewrites the operand of `e` that is the negation of the other
): (det fires?, kept: Kept, kind: BoolRule) {
    ensure rule: fires? iff overly_complex_fires?(e)
        and not (negation_rewritten? and bool_rule(e) != BoolRule::Absorption)
    ensure fix: when fires?, kept = kept_by(e)
    ensure kind_rule: when fires?, kind = bool_rule(e)

    expect fix_written: when fires?, kept_fix(e, kept) = overly_complex_fix(e)
}
```

### The fix keeps the meaning

Where the lint fires, the fix [agrees](../Meaning.md#fixes-that-agree) with
the expression in every interpretation and environment: where the
expression is well-defined, the fix is, and has its value. Undefined
operands are why it is not equal: `a and not a` is undefined where `a`
is, and its fix, `false`, never is. The fix keeps the guards: it drops
operands that the expression as written evaluates, which removes
evaluations and adds none. The solver unfolds
[`eval`](../../Lang/Semantics.md#the-evaluation-function) one step, and the
absorptions are two deep, so `src/Impls/Rewrites.lean` proves `keeps_meaning`
in Lean, by evaluating the operands, for every expression, interpretation
and environment; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc overly_complex_keeps_meaning(e: Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure keeps_meaning: when overly_complex_fires?(e),
        agrees?(
            lang::eval(i, env, overly_complex_fix(e)),
            lang::eval(i, env, e)
        )
}
```

The fix writes an operand of the expression, or a literal, on which the
lint never fires. So once the operands are fixed, the fix of the
expression leaves nothing to fix, which is what makes [fixing
everywhere](../Rewrites.md#fixing-everywhere) end with the lint fixed. That
is not so of the fix alone: the operand it keeps may itself fire, as in
`(c or (c and d)) or ((c or (c and d)) and b)`, whose fix is `c or (c and
d)`; and an expression around it may fire once it is fixed, where it did not
before, as in `c or ((c or (c and d)) and b)`, which becomes `c or (c and
b)`:

```fren
expect overly_complex_operand(e: Expr<lang::Id>) {
    expect operand: when overly_complex_fires?(e), match e {
        Expr::And(a, b) => overly_complex_fix(e) = a or overly_complex_fix(e) = b
            or overly_complex_fix(e) = Expr::Literal(lang::Value::False),
        Expr::Or(a, b) => overly_complex_fix(e) = a or overly_complex_fix(e) = b
            or overly_complex_fix(e) = Expr::Literal(lang::Value::True),
        _ => false,
    }
    expect literal: when e is Expr::Literal(_), not overly_complex_fires?(e)
}

-- `(c or (c and d)) or ((c or (c and d)) and b)`, and `c or ((c or (c and
-- d)) and b)`, for three names.
expect overly_complex_refires(b: lang::Id, c: lang::Id, d: lang::Id) {
    use lang::Expr::{And, Or, Var}

    assume distinct: b != c

    expect kept: overly_complex_fires?(
        overly_complex_fix(
            Or(
                Or(Var(c), And(Var(c), Var(d))),
                And(Or(Var(c), And(Var(c), Var(d))), Var(b))
            )
        )
    )
    expect around: not overly_complex_fires?(
        Or(Var(c), And(Or(Var(c), And(Var(c), Var(d))), Var(b)))
    )
        and overly_complex_fires?(
            Or(
                Var(c),
                And(overly_complex_fix(Or(Var(c), And(Var(c), Var(d)))), Var(b))
            )
        )
}
```

The refinements below check the rows of the table on `Bool` operands that
are well-defined, by enumeration. Each operand stands for any
well-defined expression of its type, as for the [other rewrites of this
group](../Pedantic.md). They are instances of
`overly_complex_keeps_meaning`, which `fren check` only tests, so they give
the `fren` command a decided check of each row.

```fren
set_option fren.lint.overly_complex_bool_expr "allow" in
set_option fren.evidence "enumerated" in
pub proc absorption_written(a?, b?): (
    det or_first?,
    det or_first_swapped?,
    det or_last?,
    det or_last_swapped?,
    det and_first?,
    det and_first_swapped?,
    det and_last?,
    det and_last_swapped?,
) {
    out or_first? := a? or (a? and b?)
    out or_first_swapped? := a? or (b? and a?)
    out or_last? := (a? and b?) or a?
    out or_last_swapped? := (b? and a?) or a?
    out and_first? := a? and (a? or b?)
    out and_first_swapped? := a? and (b? or a?)
    out and_last? := (a? or b?) and a?
    out and_last_swapped? := (b? or a?) and a?
}

set_option fren.lint.unused_variables "allow" in
set_option fren.evidence "enumerated" in
pub proc absorption_fixed(a?, b?): (
    det or_first?,
    det or_first_swapped?,
    det or_last?,
    det or_last_swapped?,
    det and_first?,
    det and_first_swapped?,
    det and_last?,
    det and_last_swapped?,
) {
    out or_first? := a?
    out or_first_swapped? := a?
    out or_last? := a?
    out or_last_swapped? := a?
    out and_first? := a?
    out and_first_swapped? := a?
    out and_last? := a?
    out and_last_swapped? := a?
}

expect absorption_sound(a?, b?) {
    call concrete := absorption_fixed(a?, b?)
    refines concrete absorption_written(a?, b?)
}
expect absorption_complete(a?, b?) {
    call concrete := absorption_written(a?, b?)
    refines concrete absorption_fixed(a?, b?)
}

set_option fren.lint.overly_complex_bool_expr "allow" in
set_option fren.evidence "enumerated" in
pub proc contradiction_written(a?): (det first?, det last?) {
    out first? := a? and not a?
    out last? := not a? and a?
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
set_option fren.evidence "enumerated" in
pub proc contradiction_fixed(a?): (det first?, det last?) {
    out first? := false
    out last? := false
}

expect contradiction_sound(a?) {
    call concrete := contradiction_fixed(a?)
    refines concrete contradiction_written(a?)
}
expect contradiction_complete(a?) {
    call concrete := contradiction_written(a?)
    refines concrete contradiction_fixed(a?)
}

set_option fren.lint.overly_complex_bool_expr "allow" in
set_option fren.evidence "enumerated" in
pub proc excluded_middle_written(a?): (det first?, det last?) {
    out first? := a? or not a?
    out last? := not a? or a?
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
set_option fren.evidence "enumerated" in
pub proc excluded_middle_fixed(a?): (det first?, det last?) {
    out first? := true
    out last? := true
}

expect excluded_middle_sound(a?) {
    call concrete := excluded_middle_fixed(a?)
    refines concrete excluded_middle_written(a?)
}
expect excluded_middle_complete(a?) {
    call concrete := excluded_middle_written(a?)
    refines concrete excluded_middle_fixed(a?)
}
```
