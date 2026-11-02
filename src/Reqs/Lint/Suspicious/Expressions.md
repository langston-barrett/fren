# Expressions

These lints fire on expressions that are legal but probably not what the
writer meant. Two operands are compared as [written the
same](../../Lint.md#written-the-same), where the parentheses around an operand
are not part of it, so the operands of `f(x) = f(x)` are written the same,
and those of `x = (x)`, but not those of `x + 1 = 1 + x`.

## Operands written the same

`eq_op` fires on an infix operator whose two operands are written the
same, where the expression is then always the same value, or the same as
its operand: `x = x`, `x <= x`, `x >= x`, `a? iff a?` and `s subset s`
are always `true`; `x != x`, `x < x` and `x > x` are always `false`;
`x - x` is always `0` and `s minus s` always `{}`; `a? and a?`, `a? or
a?`, `s union s` and `s inter s` are the operand. The message says which.
It has no fix: the likely mistake is a typo in one operand, which no
rewrite can repair. It does not fire on `+`, `*`, `++` or `join`, where `x
+ x` and `r join r` mean something, nor on `in`, nor on the comparisons
of a [chained comparison](../../Lang/Expressions.md#chained-comparisons),
such as `x < x < y`, which it leaves to a later lint on chains.
Operands are compared in their scopes: the right operand of `and` sees the
binders of the left's pattern tests, which the left does not, so in `(v > 1
and r is Reply::Value(v!)) and (v > 1 and r is Reply::Value(v!))` the two
first `v`s differ, and it does not fire. `lint::eq_op` states this, from the
operands as [written](../Meaning.md#expressions-as-written) in their
scopes:

```fren
pub mod lint

pub enum InfixOp {
    Iff, Or, And, Eq, Ne, Lt, Le, Gt, Ge, In, Subset, Add, Sub, Concat, Union, Minus, Mul, Inter, Join,
}

pub enum EqOpValue { AlwaysTrue, AlwaysFalse, Zero, Empty, Operand }

pub proc eq_op(
    op: InfixOp,
    left: Scoped,        -- the left operand, as written in its scope
    right: Scoped,       -- the right operand
): (
    det same?,
    det fires?,
    value: EqOpValue,         -- what the expression is, where it fires
) {
    use self::EqOpValue::{AlwaysFalse, AlwaysTrue, Empty, Zero}
    use self::InfixOp::{Add, Concat, Eq, Ge, Gt, Iff, In, Join, Le, Lt, Minus, Mul, Ne, Sub, Subset}
    out same? := left = right

    ensure rule: fires? iff (same? and not op in {Add, Mul, Concat, Join, In})
    ensure values: when fires?, value = match op {
        Eq | Le | Ge | Iff | Subset => AlwaysTrue,
        Ne | Lt | Gt => AlwaysFalse,
        Sub => Zero,
        Minus => Empty,
        _ => EqOpValue::Operand,
    }

    expect needs_same: when fires?, same?
}
```

The message is right because the two operands have the same value: they
are written the same, in the same scope, and in one environment, so by
[`written_same`](../Meaning.md#expressions-as-written) they elaborate
alike, and so have the same outcome, well-defined or not:

```fren
expect eq_op_operands(
    e_op: InfixOp,
    e_left: Scoped,
    e_right: Scoped,
    i: lang::Interp,
    env: lang::Env,
) {
    call e := eq_op(e_op, e_left, e_right)
    expect eq_op_operands: when e.fires?, lang::eval(i, env, written(e.left)) = lang::eval(i, env, written(e.right))
}
```

What the message says the expression then is, `lint::eq_op_values`
checks on Fren's own evaluation, at any value of the operand of each type
the operator applies to:

```fren
-- `nonminimal_bool` would write `not (x < x)` as `x >= x`, another case.
set_option fren.lint.eq_op "allow" in
set_option fren.lint.nonminimal_bool "allow" in
pub proc eq_op_values(op: InfixOp, x: Int, a?, s: Set<Int>) {
    use self::EqOpValue::{AlwaysFalse, AlwaysTrue, Empty, Zero}
    use self::InfixOp::{And, Eq, Ge, Gt, Iff, Inter, Le, Lt, Minus, Ne, Or, Sub, Subset, Union}

    call e := eq_op(
        op,
        Scoped {
            text := Operand::P,
            scope := {},
        },
        Scoped {
            text := Operand::P,
            scope := {},
        },
    )

    expect said: when e.fires?, match e.value {
        AlwaysTrue => (op = Eq and x = x) or (op = Le and x <= x) or (op = Ge and x >= x)
            or (op = Iff and (a? iff a?)) or (op = Subset and s subset s),
        AlwaysFalse => (op = Ne and not (x != x)) or (op = Lt and not (x < x)) or (op = Gt and not (x > x)),
        Zero => op = Sub and x - x = 0,
        Empty => op = Minus and s minus s = {},
        EqOpValue::Operand => (op = And and ((a? and a?) iff a?)) or (op = Or and ((a? or a?) iff a?))
            or (op = Union and s union s = s) or (op = Inter and s inter s = s),
    }
}
```

`eq_op` also fires on `when C, D` and `unless C, D` where `C` and `D` are
written the same. `when C, C` is always `true`, and `unless C, C` is `C`.
The body is then almost always a copy of the condition, pasted where the
consequent was meant. The body of `when` sees the binders of the
condition's pattern tests, and the condition does not, so they are
compared in their scopes, as the operands of `and` are.
`lint::eq_op_conditional` states this; that `C` and `D` have the same
value is `written_same`, as for `eq_op`:

```fren
pub proc eq_op_conditional(
    unless?,             -- `unless`, rather than `when`
    condition: Scoped,    -- the condition, as written in its scope
    body: Scoped,         -- the body
): (
    det fires?,
    value: EqOpValue,         -- what the expression is, where it fires
) {
    use self::EqOpValue::AlwaysTrue

    ensure rule: fires? iff condition = body
    ensure values: when fires?, value = if unless? then EqOpValue::Operand else AlwaysTrue
}

set_option fren.lint.eq_op "allow" in
pub proc eq_op_conditional_values(unless?, a?) {
    call e := eq_op_conditional(
        unless?,
        Scoped {
            text := Operand::P,
            scope := {},
        },
        Scoped {
            text := Operand::P,
            scope := {},
        },
    )

    -- What the message says `when a?, a?` and `unless a?, a?` are.
    expect said: when e.fires?, if unless? then e.value = EqOpValue::Operand and ((unless a?, a?) iff a?)
        else e.value = EqOpValue::AlwaysTrue and (when a?, a?)
}
```

`eq_op` also fires on an argument of a [cardinality
operator](../../Lang/Expressions.md#cardinality) written the same as an
earlier one, as in `at_most_one?(a?, b?, a?)`. Where the argument holds,
it counts twice, so neither `exactly_one?` nor `at_most_one?` holds: the
call holds only where it does not, which is seldom what a list of
conditions meant, and one of the two is probably a typo for another. The
message is reported at the later one, and says this. `true` and `false`
are left to the lints of constants. `lint::eq_op_cardinality` models an
argument as a literal or an [operand](../Meaning.md#expressions-as-written)
as written, and states when it fires at an argument, from the operands of
the arguments before it, and the refinements check what the message
says, on a call with the repeated argument written once:

```fren
-- An argument of a cardinality operator: `true` or `false`, or another
-- expression, as written.
pub enum Argument { Literal(Bool), Written(Operand) }

pub proc eq_op_cardinality(
    earlier: Set<Operand>,    -- the arguments before it that are not literals
    argument: Argument,
): (det fires?) {
    ensure rule: fires? iff match argument {
        Argument::Written(x) => x in earlier,
        Argument::Literal(_) => false,
    }
}

set_option fren.lint.eq_op "allow" in
set_option fren.evidence "enumerated" in
pub proc eq_op_cardinality_written(a?, b?): (det exactly?, det at_most?) {
    out exactly? := exactly_one?(a?, b?, a?)
    out at_most? := at_most_one?(a?, b?, a?)
}

set_option fren.evidence "enumerated" in
pub proc eq_op_cardinality_value(a?, b?): (det exactly?, det at_most?) {
    out exactly? := not a? and b?
    out at_most? := not a?
}

expect eq_op_cardinality_sound(a?, b?) {
    call concrete := eq_op_cardinality_value(a?, b?)
    refines concrete eq_op_cardinality_written(a?, b?)
}
expect eq_op_cardinality_complete(a?, b?) {
    call concrete := eq_op_cardinality_written(a?, b?)
    refines concrete eq_op_cardinality_value(a?, b?)
}
```

### Operands written the same, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
two operands written the same in the same scope are one expression: a
pattern test's binders are not names in scope beside it, but a `match`
around each operand that reads them, as [Derived
forms](../../Lang/Semantics.md#derived-forms) states. So the operands of
`(v > 1 and r is Reply::Value(v!)) and (v > 1 and r is Reply::Value(v!))`
differ: the right `v > 1` is in a `match`. Operands written the same in
the same scope have equal elaborations, which `eq_op_fires?` tests. The
converse need not hold: an operand written in two scopes that differ only
by a binder it does not read elaborates alike, and the linter does not
fire on it. So the scope is still an input of the linter's rule.
Elaboration writes `!=` as the negation of `=`, `>` and `>=` as `<` and
`<=` with the operands swapped, and `iff` as `=`. So `eq_op_fires?` fires
on `a = a`, `a < a`, `a <= a`, `a - a`, `not (a = a)`, `a and a` and
`a or a`, and on `when c, c` and `unless c, c`, which are `if c then c
else true` and `if c then true else c`. `eq_op_said` is what the message
says the expression is. `lint::infix_of` is an operator as elaborated.
`in` and the operators of sets and relations are not in the model, and
`modelled?` leaves them out:

```fren
-- `a OP b` as elaborated, for an `OP` in the model; `NoMatch` for the rest.
pub fn infix_of<V>(op: InfixOp, a: lang::Expr<V>, b: lang::Expr<V>): lang::Expr<V> := match op {
    InfixOp::Iff | InfixOp::Eq => lang::Expr::Binary(lang::BinaryOp::Eq, a, b),
    InfixOp::Ne => lang::Expr::Unary(
        lang::UnaryOp::Not,
        lang::Expr::Binary(lang::BinaryOp::Eq, a, b)
    ),
    InfixOp::Lt => lang::Expr::Binary(lang::BinaryOp::Lt, a, b),
    InfixOp::Le => lang::Expr::Binary(lang::BinaryOp::Le, a, b),
    InfixOp::Gt => lang::Expr::Binary(lang::BinaryOp::Lt, b, a),
    InfixOp::Ge => lang::Expr::Binary(lang::BinaryOp::Le, b, a),
    InfixOp::And => lang::Expr::And(a, b),
    InfixOp::Or => lang::Expr::Or(a, b),
    InfixOp::Add => lang::Expr::Binary(lang::BinaryOp::Add, a, b),
    InfixOp::Sub => lang::Expr::Binary(lang::BinaryOp::Sub, a, b),
    InfixOp::Mul => lang::Expr::Binary(lang::BinaryOp::Mul, a, b),
    InfixOp::Concat => lang::Expr::Binary(lang::BinaryOp::Concat, a, b),
    _ => lang::Expr::NoMatch,
}

-- `op` is an operator of the model.
pub fn modelled?(op: InfixOp) :=
    not op in {
        InfixOp::In,
        InfixOp::Subset,
        InfixOp::Union,
        InfixOp::Minus,
        InfixOp::Inter,
        InfixOp::Join,
    }

pub fn eq_op_fires?<V>(e: lang::Expr<V>) := match e {
    lang::Expr::Binary(op, a, b) =>
        a = b and op in {
            lang::BinaryOp::Eq,
            lang::BinaryOp::Lt,
            lang::BinaryOp::Le,
            lang::BinaryOp::Sub,
        },
    lang::Expr::Unary(lang::UnaryOp::Not, lang::Expr::Binary(lang::BinaryOp::Eq, a, b)) => a = b,
    lang::Expr::And(a, b) => a = b,
    lang::Expr::Or(a, b) => a = b,
    lang::Expr::If(c, t, f) => (t = c and true?(f)) or (true?(t) and f = c),
    _ => false,
}

-- What `e` is, where `eq_op` fires on it.
pub fn eq_op_said<V>(e: lang::Expr<V>): lang::Expr<V> := match e {
    lang::Expr::Binary(lang::BinaryOp::Lt, _, _) => lang::Expr::Literal(lang::Value::False),
    lang::Expr::Binary(lang::BinaryOp::Sub, _, _) => lang::Expr::Literal(lang::Value::Integer(0)),
    lang::Expr::Binary(_, _, _) => lang::Expr::Literal(lang::Value::True),
    lang::Expr::Unary(_, _) => lang::Expr::Literal(lang::Value::False),
    lang::Expr::And(a, _) => a,
    lang::Expr::Or(a, _) => a,
    lang::Expr::If(c, t, _) => if true?(t) then c else lang::Expr::Literal(lang::Value::True),
    _ => e,
}

-- What a `lint::EqOpValue` says the expression is, of its left operand
-- `a`; `NoMatch` for `{}`, which is not in the model.
pub fn value_of<V>(v: EqOpValue, a: lang::Expr<V>): lang::Expr<V> := match v {
    EqOpValue::AlwaysTrue => lang::Expr::Literal(lang::Value::True),
    EqOpValue::AlwaysFalse => lang::Expr::Literal(lang::Value::False),
    EqOpValue::Zero => lang::Expr::Literal(lang::Value::Integer(0)),
    EqOpValue::Empty => lang::Expr::NoMatch,
    EqOpValue::Operand => a,
}
```

`lint::eq_op` and `lint::eq_op_conditional` bind this to the linter.
Where `eq_op` fires on an operator of the model, `eq_op_fires?` fires on
its elaboration, and says what the message says. On `+`, `*` and `++`,
neither fires. Where `eq_op` fires on `when C, D` or `unless C, D`,
`eq_op_fires?` fires on its elaboration, and says what the message says.
`written(x)` is `x`'s elaboration where it is written, with the `match`
around it, as [Expressions as
written](../Meaning.md#expressions-as-written) states. The front ends'
reading of the operator and the keyword is trusted, and checked by the
ui tests in `test/ui/lints/suspicious.fren` and
`test/ui/lints/mistakes.fren`. The linter fires only where
`eq_op_fires?` does, not everywhere it does. On `a != a`, the linter
fires once, and `eq_op_fires?` fires on both the negation and the `=`
within it. It also fires on `if c then c else true`, which the linter
sees as an `if`.

```fren
expect eq_op_elaborated(op: InfixOp, left: Scoped, right: Scoped) {
    call p := eq_op(op, left, right)

    expect fires: when p.fires? and modelled?(op),
        eq_op_fires?(infix_of(op, written(left), written(right)))
        and eq_op_said(infix_of(op, written(left), written(right))) = value_of(p.value, written(left))
    expect others: when op in {InfixOp::Add, InfixOp::Mul, InfixOp::Concat},
        not p.fires? and not eq_op_fires?(infix_of(op, written(left), written(right)))
}

expect eq_op_conditional_elaborated(unless?, condition: Scoped, body: Scoped) {
    call p := eq_op_conditional(unless?, condition, body)

    expect fires: when p.fires?,
        eq_op_fires?(conditional_of(unless?, written(condition), written(body)))
        and eq_op_said(conditional_of(unless?, written(condition), written(body)))
        = value_of(p.value, written(condition))
}
```

`eq_op` has no fix, so it does not join the [rewrites](../Rewrites.md).
What it states is that its message is right. Where it fires, what the
message says the expression is [agrees](../Meaning.md#fixes-that-agree)
with the expression, in every interpretation and environment. Where the
operand is well-defined, the expression has the value that the message
says. `x = x` is `true` wherever `x` is well-defined, and `when c, c`
wherever `c` is a `Bool`. `x < x` and `x - x` are `false` and `0`
wherever `x` is an integer. `a and a`, `a or a` and `unless c, c` have the
operand's outcome wherever it is a `Bool`. Elsewhere the expression is
undefined. `not (a = a)` is two layers deep, and the solver unfolds
[`eval`](../../Lang/Semantics.md#the-evaluation-function) only one step,
so `src/Impls/Rewrites.lean` proves this in Lean, for every expression,
interpretation and environment; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc eq_op_said_agrees(e: lang::Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure said: when eq_op_fires?(e), agrees?(lang::eval(i, env, eq_op_said(e)), lang::eval(i, env, e))
}
```

`eq_op` on the arguments of a cardinality operator stays on its model
for now. Finding an argument written the same as an earlier one looks
along the list of arguments, which needs a recursion, and a generic
function cannot be one. So does `eq_op` on `x.min(x)` and `x.max(x)`
([Idempotent methods](Integers.md#idempotent-methods)), whose model
compares texts without their scopes; it moves with the other lints of
`min` and `max`.

## Erasing operations

`erasing_op` fires on an operation whose value ignores an operand: `x * 0`
and `0 * x` are always `0`; `s inter {}`, `{} inter s`, `{} minus s` and
`r join {}` are always `{}`, though `{}` in `r join {}` has no type it can
take, which is an error (see
[Checking and synthesis](../../Lang/Types.md#checking-and-synthesis)); `x
in {}` and `x in []` are always `false`; and `{} subset s` is always
`true`. It mirrors
[`identity_op`](../Complexity/Operators.md#identities), and an operand is `0` or `{}` as
it is there. The message says what the value is. It has no fix: the
likely mistake is the literal, and writing the value instead would keep
the mistake and hide it. Where both operands are written the same, as in
`s = {} inter {}`, `eq_op` fires instead. It does not fire
on `s subset {}`, which says that `s` is empty. `lint::erasing_op`
states this:

```fren
pub proc erasing_op(
    op: InfixOp,
    left: IdentityOperand,
    right: IdentityOperand,
    same?,               -- the operands are written the same
): (det fires?) {
    use self::IdentityOperand::{Empty, Zero}
    use self::InfixOp::{In, Inter, Join, Minus, Mul, Subset}

    ensure rule: fires? iff (not (same? and op in {Inter, Minus, Subset}) and match op {
        Mul => left = Zero or right = Zero,
        Inter | Join => left = Empty or right = Empty,
        Minus | Subset => left = Empty,
        In => right = Empty,
        _ => false,
    })
}

expect erasing_not_eq_op(
    e_op: InfixOp,
    e_left: IdentityOperand,
    e_right: IdentityOperand,
    e_same?,
    q_op: InfixOp,
    q_left: Scoped,
    q_right: Scoped,
) {
    call e := erasing_op(e_op, e_left, e_right, e_same?)
    call q := eq_op(q_op, q_left, q_right)
    expect erasing_not_eq_op: when q.op = e.op and q.same? = e.same?,
        not (e.fires? and q.fires?)
}
```

The refinements below check the values of `in` and `subset` that the
message claims: a procedure that computes the operation as written, one
whose output is the value, and a [refinement](../../Lang/Refinement.md) each
way, so that the solver checks that they agree on every input. An operand
is a variable, standing for any expression of its type: Fren's
expressions are pure, so what holds for every value of an operand holds
for every expression.

```fren
set_option fren.lint.erasing_op "allow" in
pub proc empty_membership_written(x: Int): (det v?) { out v? := x in {} }

set_option fren.lint.unused_variables "allow" in
set_option fren.lint.constant_output "allow" in
pub proc empty_membership_value(x: Int): (det v?) { out v? := false }

expect empty_membership_sound(x: Int) {
    call concrete := empty_membership_value(x)
    refines concrete empty_membership_written(x)
}
expect empty_membership_complete(x: Int) {
    call concrete := empty_membership_written(x)
    refines concrete empty_membership_value(x)
}

set_option fren.lint.erasing_op "allow" in
pub proc empty_subset_written(s: Set<Int>): (det v?) { out v? := {} subset s }

set_option fren.lint.unused_variables "allow" in
set_option fren.lint.constant_output "allow" in
pub proc empty_subset_value(s: Set<Int>): (det v?) { out v? := true }

expect empty_subset_sound(s: Set<Int>) {
    call concrete := empty_subset_value(s)
    refines concrete empty_subset_written(s)
}
expect empty_subset_complete(s: Set<Int>) {
    call concrete := empty_subset_written(s)
    refines concrete empty_subset_value(s)
}
```

It also fires on `0 div k` and `0 mod k`, and on `-0 div k` and `-0 mod
k`, which are always `0`: `k` is a
constant that is not `0` (see [Division and
remainder](../../Lang/Expressions.md#division-and-remainder)), and `0` is a
multiple of every such `k`. `lint::erasing_division` states this, and the
[refinements](../../Lang/Refinement.md) below check the value, for a
positive divisor and a negative one:

```fren
pub proc erasing_division(
    literal?,            -- the dividend is an integer literal, possibly negated
    dividend: Int,       -- its value, if it is
): (det fires?) {
    ensure rule: fires? iff (literal? and dividend = 0)
}

set_option fren.lint.erasing_op "allow" in
set_option fren.lint.constant_output "allow" in
set_option fren.evidence "enumerated" in
pub proc erasing_division_written(): (det quotient: Int, det remainder: Int) {
    out quotient := 0 div 7
    out remainder := 0 mod -3
}

set_option fren.lint.constant_output "allow" in
set_option fren.evidence "enumerated" in
pub proc erasing_division_fixed(): (det quotient: Int, det remainder: Int) {
    out quotient := 0
    out remainder := 0
}

expect erasing_division_sound() {
    call concrete := erasing_division_fixed()
    refines concrete erasing_division_written()
}
expect erasing_division_complete() {
    call concrete := erasing_division_written()
    refines concrete erasing_division_fixed()
}
```

### Erasing operations, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
`0` is a literal, `-0` is `Unary(Neg, Literal(0))`, and `[]` is `Nil`.
`erasing_op_fires?` fires on `x * 0`, `0 * x`, `x in []`, and on `0 div
k`, `0 mod k`, `-0 div k` and `-0 mod k`. Sets and relations are not in
the model, so it leaves the operations of `{}`. `erasing_op_said` is the
value that the message says the expression has. As for
[`eq_op`](#operands-written-the-same-over-the-syntax-of-the-semantics),
there is no fix, so the lint does not join the [rewrites](../Rewrites.md),
and what it states is that its message is right.

```fren
-- `e` is `0`, possibly negated.
fn zero_dividend?<V>(e: lang::Expr<V>) :=
    zero?(e) or e = lang::Expr::Unary(
        lang::UnaryOp::Neg,
        lang::Expr::Literal(lang::Value::Integer(0))
    )

pub fn erasing_op_fires?<V>(e: lang::Expr<V>) := match e {
    lang::Expr::Binary(lang::BinaryOp::Mul, a, b) => zero?(a) or zero?(b),
    lang::Expr::Binary(lang::BinaryOp::Div, a, _) => zero_dividend?(a),
    lang::Expr::Binary(lang::BinaryOp::Mod, a, _) => zero_dividend?(a),
    lang::Expr::Binary(lang::BinaryOp::In, _, b) => b = lang::Expr::Nil,
    _ => false,
}

-- What `e` is, where `erasing_op` fires on it.
pub fn erasing_op_said<V>(e: lang::Expr<V>): lang::Expr<V> := match e {
    lang::Expr::Binary(lang::BinaryOp::In, _, _) => lang::Expr::Literal(lang::Value::False),
    _ => lang::Expr::Literal(lang::Value::Integer(0)),
}
```

`lint::erasing_op` and `lint::erasing_division` bind this to the linter.
`operand_of` reads an operand as [`identity_op`'s
binding](../Complexity/Operators.md#identities-over-the-syntax-of-the-semantics)
does. On a product, and on a membership in `[]`, `erasing_op` fires
exactly where `erasing_op_fires?` does. On a quotient or a remainder,
`erasing_division` fires exactly where `erasing_op_fires?` does, whether
the dividend is an integer literal, possibly negated, or not. That the
front ends read the operands so, and the value that the message gives
for each operator, are trusted, and checked by the ui tests in
`test/ui/lints/operators.fren` and `test/ui/lints/integers.fren`.

```fren
expect erasing_op_elaborated(
    op: InfixOp,
    left: IdentityOperand,
    right: IdentityOperand,
    same?,
    left_list?,
    right_list?,
    x: lang::Expr<lang::Id>,
    y: lang::Expr<lang::Id>,
    z: lang::Expr<lang::Id>,
    w: lang::Expr<lang::Id>,
) {
    use lang::BinaryOp::{In, Mul}
    use lang::Expr::Binary

    assume plain: plain_operand?(x) and plain_operand?(z)

    call p := erasing_op(op, left, right, same?)

    let a: lang::Expr<lang::Id> := operand_of(left, left_list?, x, y)
    let b: lang::Expr<lang::Id> := operand_of(right, right_list?, z, w)

    expect product: when op = InfixOp::Mul, p.fires? iff erasing_op_fires?(Binary(Mul, a, b))
    expect membership: when op = InfixOp::In and right_list?, p.fires? iff erasing_op_fires?(Binary(In, a, b))
}

expect erasing_division_elaborated(
    literal?,
    negated?,
    n: Nat,
    x: lang::Expr<lang::Id>,
    k: lang::Expr<lang::Id>,
) {
    use lang::BinaryOp::{Div, Mod}
    use lang::Expr::{Binary, Literal, Unary}
    use lang::Value::Integer

    assume plain: not (x is Literal(Integer(_)) | Unary(lang::UnaryOp::Neg, Literal(Integer(_))))

    call p := erasing_division(literal?, if negated? then -n else n)

    let a: lang::Expr<lang::Id> := if not literal? then x
        else if negated? then Unary(lang::UnaryOp::Neg, Literal(Integer(n)))
        else Literal(Integer(n))

    expect fires: (p.fires? iff erasing_op_fires?(Binary(Div, a, k))) and (p.fires? iff erasing_op_fires?(Binary(Mod, a, k)))
}
```

Where it fires, what the message says agrees with the expression. `x in
[]` is `false` wherever `x` is well-defined, in every interpretation.
`*`, `div` and `mod` are [primitive
operations](../Meaning.md#primitive-operations), so the rest hold in each
interpretation that gives them their usual meaning: a product with `0` is
`0`, and so are a quotient and a remainder of `0`, where the divisor is
not `0`, and where the graph has a point for the operands; elsewhere the
expression is undefined. `src/Impls/Rewrites.lean` proves this in Lean,
for every expression, interpretation whose primitives are `usual?`, and
environment; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc erasing_op_said_agrees(e: lang::Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure said: when usual?(i.primitives) and erasing_op_fires?(e),
        agrees?(
            lang::eval(i, env, erasing_op_said(e)),
            lang::eval(i, env, e)
        )
}
```

## Branches written the same

`same_branches` fires on `if c then a else b`, where `a` and `b` are
written the same: the condition decides nothing. The fix replaces the
conditional with `a`, in parentheses where
[fixes need them](../../Lint.md#parentheses-in-fixes), from the operator that the conditional is an
operand of and what follows it, as for
[`nonminimal_bool`](../Complexity.md#simpler-bool-expressions). The value is `a`'s, and
the [guards](../../Lang/Expressions.md#sequences) of what remains get no
weaker: the copy of `a` guarded by `c` and the one guarded by `not c` are
both defined exactly when `a` is defined under the guard of the
conditional, which is `a`'s guard after the fix, and removing `c` only
removes something that is evaluated. A `match` whose arms are all written
the same is left to other lints. `lint::same_branches` states when it
fires, from the branches as [written](../Meaning.md#expressions-as-written)
in their scopes. It does not fire where the condition's pattern tests bind
names, which the `then` branch sees and the `else` branch does not (see
[`lang::test_scope`](../../Lang/Expressions.md#pattern-tests)): in `if r
is Reply::Value(v!) then v else v`, the same text means the payload in one
branch and the variable `v` in the other, so the fix would change the
value. It leaves such a conditional even where the branches mention none
of those names, rather than compare what they mention:

```fren
pub proc same_branches(
    binders: Set<lang::Id>,    -- the binders of the condition's pattern tests
    then_branch: Scoped,       -- the branches, as written in their scopes
    else_branch: Scoped,
): (det fires?) {
    ensure rule: fires? iff (binders = {} and then_branch = else_branch)

    expect no_binders: when fires?, binders = {} and then_branch.scope = else_branch.scope
}
```

The fix has the conditional's value because the branches have the same
value, whichever is taken, by [`written_same`](../Meaning.md#expressions-as-written):

```fren
expect same_branches_value(
    b_binders: Set<lang::Id>,
    b_then_branch: Scoped,
    b_else_branch: Scoped,
    i: lang::Interp,
    env: lang::Env,
) {
    call b := same_branches(b_binders, b_then_branch, b_else_branch)
    expect same_branches_value: when b.fires?,
        lang::eval(i, env, written(b.then_branch)) = lang::eval(i, env, written(b.else_branch))
}
```

`same_branches` fires on a [table](../../Lang/Expressions.md#tables)
whose rows' values are all written the same, of two or more rows, or of
one row that is `_`: its conditions decide nothing either. Where the table
has a `_` row, it has that value wherever it is evaluated, and the fix
replaces it with the value, in parentheses where [fixes need
them](../../Lint.md#parentheses-in-fixes); each row's copy of the value is guarded by the table's
guard, the negations of the earlier rows' conditions and its own, and
together they cover the table's guard, so the value's guard after the fix
is no stronger. Without a `_` row, the table is unspecified where no row
holds, which the value is not, so there is no fix. The message is at the table. The refinements below
check the fix on one example:

```fren
set_option fren.lint.same_branches "allow" in
pub proc same_rows_written(n: Int): (det v: Int) {
    out v := table {
        n > 0 => n + 1,
        n < -5 => n + 1,
        _ => n + 1,
    }
}

pub proc same_rows_fixed(n: Int): (det v: Int) { out v := n + 1 }

expect same_rows_sound(n: Int) {
    call concrete := same_rows_fixed(n)
    refines concrete same_rows_written(n)
}
expect same_rows_complete(n: Int) {
    call concrete := same_rows_written(n)
    refines concrete same_rows_fixed(n)
}
```

`lint::same_rows` states when it fires, computing the facts from the rows, with each
row's condition by whether it holds, and checks the fix: where there is a
`_` row, the first row that holds, or `_`, has the value that every row
has:

```fren
pub struct Row { holds?, value: Body }

pub fn row_holds?(r: Row) := r.holds?

pub fn row_value(r: Row): Body := r.value

pub proc same_rows(
    rows: Seq<Row>,
    wildcard?,               -- the last row is `_`
    o: Int,
): (
    det fires?,
    det fixed?,          -- it has a fix
) {
    assume size: 1 <= rows.len <= 4

    det let n_rows: Int := rows.len
    -- the rows' values are written the same
    det let same? := (forall (s: Slot), when pos(s) < rows.len, row_value(rows[pos(s)]) = row_value(rows[0]))

    ensure rule: fires? iff (same? and (n_rows >= 2 or wildcard?))
    ensure fix: fixed? iff wildcard?

    expect keeps_meaning: forall (s: Slot), when fires? and fixed? and pos(s) < rows.len
        and (row_holds?(rows[pos(s)]) or pos(s) = rows.len - 1)
        and (forall (r: Slot), when pos(r) < pos(s), not row_holds?(rows[pos(r)])),
        body_value(row_value(rows[pos(s)]), -1, 0, -1, 0, -1, 0, o) = body_value(row_value(rows[0]), -1, 0, -1, 0, -1, 0, o)
}
```

`ifs_same_cond` fires on a test of a chain of `else if` written the same
as an earlier test of the chain, as the second `x > 0` in `if x > 0 then a
else if x > 0 then b else c`. Its branch is never taken: it is guarded by
the negation of the earlier test, so wherever the test holds, the earlier
branch is taken. It is reported at the repeated test, and the message names
the earlier one. A test in parentheses, `else (if ...)`, is still in the
chain. The parentheses around a whole test are not part of it, so in `if b
> 0 then a else if (b > 0) then c else d` the second test repeats the
first. It has no fix: one of the tests is probably not the one meant.
`lint::ifs_same_cond` states when it fires, over the chain's tests, in
order, each as [written](../../Lint.md#written-the-same): `lint::repeated?`
says that the test at a position is written the same as an earlier one,
and `lint::first_same` gives the first such, which the message names; the
claim `lint::duplicate_elements_members` of [Elements written the
same](Literals.md#elements-written-the-same) uses it too. Their
quantifiers are over positions of any number of tests, so they are outside
the decidable core; their own checks are tested, and their implementations
are proved in Lean of the lint's code, for every chain:

```fren
-- The text at position `i` is written the same as an earlier one.
set_option fren.lint.undecidable "allow" in
pub fn repeated?(forms: Seq<String>, i: Int) :=
    0 <= i < forms.len and (exists (j: Int), 0 <= j < i and forms[j] = forms[i])

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc first_same(
    forms: Seq<String>,      -- texts, in order, each as written
    k: Int,                  -- a position
): (
    det earlier: Int,        -- the first earlier position written the same, or -1
) {
    ensure first: when repeated?(forms, k), 0 <= earlier < k and forms[earlier] = forms[k]
        and (forall (j: Int), when 0 <= j < earlier, forms[j] != forms[k])
    ensure none: unless repeated?(forms, k), earlier = -1
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc ifs_same_cond(
    tests: Seq<String>,      -- the tests of the chain of `else if`, in order, each as written
    k: Int,                  -- the position of a test
): (
    det fires?,
    det earlier: Int,        -- the position of the first earlier test written the same, or -1
) {
    call first := first_same(tests, k)

    ensure rule: fires? iff repeated?(tests, k)
    ensure named: earlier = first.earlier
}
```

Its branch is never taken. Every test of the chain is written in one
scope, and evaluated in one environment: the test at `k` is in the `else`
branch of each earlier one, which sees none of its binders, by
[`lang::test_scope`](../../Lang/Expressions.md#pattern-tests), and the
claim checks this for a pattern test of any earlier test. So tests written
the same are the same [`Scoped`](../Meaning.md#expressions-as-written)
expression, and have the same outcome, by
[`written_same`](../Meaning.md#expressions-as-written). The branch of the
test at `k` is taken where that test is `true` and each earlier one `false`.
`lint::ifs_same_cond_never_taken` states this over the tests as written in
their scope, and their outcomes by Fren's own evaluation; the solver
checks it, for any number of tests:

```fren
set_option fren.lint.undecidable "allow" in
pub proc ifs_same_cond_never_taken(
    forms: Seq<String>,           -- the tests, each as written
    tests: Seq<Scoped>,           -- the tests, as written in their scope
    scope: Set<lang::Id>,         -- the chain's scope
    i: lang::Interp,
    env: lang::Env,
    k: Int,
    operands: Nat,                -- an earlier test's chain of `and` that holds a pattern test: its operands
    test_at: Nat,                 -- the test's position among them, from 0
) {
    use lang::{Outcome, Site, TestContext, Value, eval}

    assume within: test_at < operands
    assume texts: tests.len = forms.len and (forall (a b: Int), when 0 <= a < forms.len
        and 0 <= b < forms.len and forms[a] = forms[b], tests[a].text = tests[b].text)
    assume one_scope: forall (a: Int), when 0 <= a < tests.len, tests[a].scope = scope

    call c := ifs_same_cond(forms, k)
    call earlier_test := lang::test_scope(
        TestContext::IfCondition,
        operands,
        test_at,
        Site::ElseBranch,
    )

    -- A later test, in the `else` branch, sees none of an earlier test's binders: one scope.
    expect unseen: not earlier_test.visible?

    -- The branch of the test at `k` is taken where that test is `true`, and each earlier one `false`.
    expect never_taken: when c.fires?, not (eval(i, env, written(tests[k])) = Outcome::Defined(Value::True)
        and (forall (j: Int), when 0 <= j < k, eval(i, env, written(tests[j])) = Outcome::Defined(Value::False)))
}
```

Which branch is taken is what evaluating the chain gives: `if p then a
else if q then b else d` is `If(p, a, If(q, b, d))`, by the [abstract
syntax](../../Lang/Semantics.md#expressions), and [If
expressions](../../Lang/EvaluationRules.md#if-expressions) selects the
branch. `lint::ifs_same_cond_taken` evaluates such a chain, with tests
that are variables: its outcome is that of `if p? then a else if q? then
b else d`, so it takes the branch of `q` exactly where `p` is `false` and
`q` `true`, as `lint::ifs_same_cond_never_taken` reads it, and where the
two tests have the same value, the chain has the outcome that it has
without the second test. Its evidence is testing, which evaluates it,
since the solver unfolds [`eval`](../../Lang/Semantics.md) only one step:

```fren
set_option fren.evidence "random" in
pub proc ifs_same_cond_taken(
    i: lang::Interp,
    p?,
    q?,
    a: lang::Value,
    b: lang::Value,
    d: lang::Value,
) {
    use lang::{Env, Expr, Outcome, eval, truth}

    let env: Env := Env::Bind(
        "p",
        Outcome::Defined(truth(p?)),
        Env::Bind("q", Outcome::Defined(truth(q?)), Env::Empty)
    )
    let chain: Outcome := eval(
        i,
        env,
        Expr::If(
            Expr::Var("p"),
            Expr::Literal(a),
            Expr::If(Expr::Var("q"), Expr::Literal(b), Expr::Literal(d))
        )
    )
    let without: Outcome := eval(
        i,
        env,
        Expr::If(Expr::Var("p"), Expr::Literal(a), Expr::Literal(d))
    )

    -- The branch of `q` is taken where `q` is `true` and `p` `false`.
    expect taken: chain = (if p? then Outcome::Defined(a) else if q? then Outcome::Defined(b) else Outcome::Defined(d))
    expect never_taken: when (p? iff q?), chain = without
    cover second: not p? and q? and chain = Outcome::Defined(b)
}
```

### Branches written the same, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
`same_branches` fires on `If(c, a, a)`, and its fix is `a`. That is a
rewrite, as [Fixes as rewrites](../Rewrites.md) states for every such
lint. A branch that reads a binder of the condition's pattern tests is
elaborated within a `match` ([Derived
forms](../../Lang/Semantics.md#derived-forms)). So in `if r is
Reply::Value(v!) then v else v` the branches differ, and
`same_branches_fires?` does not fire:

```fren
pub fn same_branches_fires?<V>(e: lang::Expr<V>) := match e {
    lang::Expr::If(_, t, f) => t = f,
    _ => false,
}

pub fn same_branches_fix<V>(e: lang::Expr<V>): lang::Expr<V> := match e {
    lang::Expr::If(_, t, f) => if t = f then t else e,
    _ => e,
}
```

`lint::same_branches` binds this to the linter. For every condition `c`
and branches as written, where `same_branches` fires on `if c then t else
f`, `same_branches_fires?` fires on its elaboration, and the fix is
`written(t)`. The linter leaves a conditional whose condition binds names
even where the branches read none of them. There the function fires, so
the linter fires only where the function does, and not everywhere it
does. A table is a nest of conditionals ([Derived
forms](../../Lang/Semantics.md#derived-forms)). With a `_` row, `table {
c => v, d => v, _ => v }` is `If(c, v, If(d, v, v))`. Fixing the inner
conditional, as [fixing everywhere](../Rewrites.md#fixing-everywhere)
does first, makes the outer one `If(c, v, v)`, whose fix is `v`, the fix
the linter writes (`rows`). Without a `_` row, the last conditional's
`else` branch is `NoMatch`, so where `v` is not `NoMatch`,
`same_branches_fires?` fires on none of the conditionals (`no_wildcard`).
The linter fires there, without a fix, and `lint::same_rows` states that.
These two facts, `same_branches_tables`, are about the functions alone:
`lint::same_rows` models a row's value as a `Body`, not as an
expression, so that its fix is the value `rows` reaches is stated in
this prose, and not as a check. The front ends' reading of the branches
and the rows, and the text of the fix, are trusted, and checked by the ui
tests in `test/ui/lints/suspicious.fren` and
`test/ui/lints/patterns_tables.fren`.

```fren
expect same_branches_elaborated(
    binders: Set<lang::Id>,
    t: Scoped,
    f: Scoped,
    c: lang::Expr<lang::Id>,
) {
    use lang::Expr::If

    call p := same_branches(binders, t, f)

    expect fires: when p.fires?, same_branches_fires?(If(c, written(t), written(f)))
        and same_branches_fix(If(c, written(t), written(f))) = written(t)
}

expect same_branches_tables(
    c: lang::Expr<lang::Id>,
    d: lang::Expr<lang::Id>,
    v: lang::Expr<lang::Id>,
) {
    use lang::Expr::If

    expect rows: same_branches_fix(If(c, v, same_branches_fix(If(d, v, v)))) = v
    expect no_wildcard: unless v = lang::Expr::NoMatch,
        not same_branches_fires?(If(c, v, If(d, v, lang::Expr::NoMatch)))
        and not same_branches_fires?(If(d, v, lang::Expr::NoMatch))
}
```

Where it fires, the fix [agrees](../Meaning.md#fixes-that-agree) with the
conditional, in every interpretation and environment. Where the
condition is `true` or `false`, the conditional has the branch's outcome,
and that is the fix's. Elsewhere the conditional is undefined. The fix
may be well-defined there, so it agrees, but need not have the same
outcome. `src/Impls/Rewrites.lean` proves this in Lean, for every
expression, interpretation and environment, as it proves the other
rewrites; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc same_branches_keeps_meaning(e: lang::Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure agrees: when same_branches_fires?(e),
        agrees?(
            lang::eval(i, env, same_branches_fix(e)),
            lang::eval(i, env, e)
        )
}
```

The fix writes a branch. Once the operands are fixed, the branch does not
fire, so the fix leaves nothing to fix. The fix alone need not. For every
`c`, `d` and `v`, the fix of `if c then (if d then v else v) else (if d
then v else v)` is `if d then v else v`, which fires again (`kept`). And
an expression around it may start firing once it is fixed. `if c then v
else (if d then v else v)` does not fire, but the fix of its `else`
branch makes it `if c then v else v`, which does (`around`). This is the
table above.

```fren
expect same_branches_refires(
    c: lang::Expr<lang::Id>,
    d: lang::Expr<lang::Id>,
    v: lang::Expr<lang::Id>,
) {
    use lang::Expr::If

    expect kept: same_branches_fires?(same_branches_fix(If(c, If(d, v, v), If(d, v, v))))
    expect around: not same_branches_fires?(If(c, v, If(d, v, v)))
        and same_branches_fires?(If(c, v, same_branches_fix(If(d, v, v))))
}
```
