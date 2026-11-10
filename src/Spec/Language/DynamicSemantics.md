# Dynamic semantics

The dynamic semantics evaluates an expression. An evaluation that ends
has an outcome, a value or an error; an evaluation need not end, since
typing does not exclude recursion. The semantics is operational, and it is
defined for every well-typed program, whether or not the program is
[verified](StaticSemantics.md#r-statics.program.verified). It fixes one
order of evaluation. An operation outside its domain gives an error state,
and never an arbitrary value. The
[denotational semantics](DenotationalSemantics.md) is defined for verified
Core only; the adequacy theorem states that there evaluation ends, reaches
no error and gives the denotation.

The evaluation rules and the theorems are open: each is listed below under
its identifier with what it will state. What this chapter states in Fren is
[an evaluator of call-free derivation tables](#the-table-evaluator), which
has no error outcome and gives no value to `*`, `div` or `%`.

## Overview

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `P ⊢ ⟨e, ρ⟩ ⇓ r` | in the program P, e evaluates at ρ to the outcome r | open |
| `P ⊢ ⟨e, ρ⟩ ⇑` | in the program P, the evaluation of e at ρ does not end | open |
| `P ⊢ f(v₁, …, vₙ) ⇓ r` | the call of f at the argument values has outcome r | open |
| `op(v) ⇓ r`, `op(v₁, v₂) ⇓ r` | the operator op has outcome r at the operand values | open; `unary_value` and `binary_value` where they give a value |
| `eval(t, i, ρ) = v` | row i of the call-free table t has the value v at ρ | `eval` |

```text
  r ::= v                              a value
      | error(k)                       an error of kind k

  k ::= …                              the kinds of error; open

  ρ ::= ·  |  ρ, v                     assignments, by de Bruijn level
```

The values v are those of the
[denotational semantics](DenotationalSemantics.md#values). P is a
well-typed program, e is well typed in a context Γ of P, and ρ gives each
level of Γ a value of its type.

## Scope

r[dynamics.scope]
The dynamic semantics is defined for every well-typed program. It reads
no contract proof, no hypothesis and no solver's answer: an evaluation
depends only on the program, the expression and the assignment. A program
that is well typed and not verified has evaluations; some of them may end
in an error, and some may not end. This rule is open, with the judgments
it describes.

## Outcomes and errors

r[dynamics.outcome]
An evaluation that ends, ends in exactly one *outcome*: a value, or an
error with its kind. An error is not a value: no local is bound to one,
and no operator or call takes one as an operand. This rule is open.

r[dynamics.divergence]
An evaluation need not end. Typing does not exclude recursion
([Core typing](Types.md#r-types.judgment.separate)), so a well-typed
function may call itself without bound. Such an evaluation *diverges*,
`P ⊢ ⟨e, ρ⟩ ⇑`. Divergence is not an outcome and not an error: `⇓` relates
a diverging evaluation to no outcome at all. This rule is open. How
divergence is stated is decided with the evaluation rules: as a judgment
of its own beside `⇓`, or as an unending run of a step relation from which
`⇓` is derived. Either way it must tell divergence apart from an
expression that no rule applies to, which
[type safety](#r-dynamics.theorem.type-safety) excludes.

r[dynamics.error.kinds]
A division or remainder whose divisor evaluates to zero has the outcome
error. This rule is open. It will list every kind of error; whether a call
that fails its callee's precondition, or an assertion that evaluates to
false, is an error, and of which kind, is decided with it.

r[dynamics.error.propagation]
When evaluating a child that an expression needs ends in an error, the
expression ends in that error, and no later child is evaluated. When
evaluating such a child diverges, the expression diverges. This rule is
open.

## Evaluation

r[dynamics.order]
Evaluation has one fixed order. The arguments of a call, and the operands
of every operator other than `and` and `or`, are evaluated left to right,
each exactly once, before the call or operator itself. `and` and `or`
evaluate their first operand exactly once, and first. A let evaluates its
value, then its body. A conditional evaluates its condition, then only the
selected branch; a match evaluates its scrutinee, then only the selected
arm. This rule is open. Whether `and` and `or` evaluate their second
operand when the first decides the result is decided with it; nothing in
this chapter depends on that choice. Either way
[definedness](StaticSemantics.md#r-statics.definedness.declarative) does not
follow the order: it requires both operands to be defined.

r[dynamics.evaluation.rules]
`P ⊢ ⟨e, ρ⟩ ⇓ r` is defined by rules for each Core form: one for the form's
value and one for each child whose error it propagates. An expression
whose evaluation [diverges](#r-dynamics.divergence) has no derivation of
`⇓`. A literal, a local
and a constructor evaluate to the values that
[the interpretation](DenotationalSemantics.md#r-expressions.meaning.context)
gives them. These rules are open.

r[dynamics.operators.total]
Every operator has an outcome at every pair of operand values of its
operand types: applying an operator to values never diverges. `*`, `div`
and `%` evaluate to the product and to the Euclidean quotient and
remainder that the
[equations of their meaning](DenotationalSemantics.md#r-expressions.meaning.operators)
state, and `div` and `%` to an error at a zero divisor. This rule is
open: `binary_value` computes no result for these three operators, and
`binary_meaning?` does not determine one.

r[dynamics.call]
A call evaluates its arguments, then the callee's body at the assignment
that lists the argument values, without the caller's locals. Its outcome
is the body's, and it diverges when the body does. The rule reads no
contract and bounds no recursion: a call is evaluated whether or not its
callee's recursion is
[well founded](StaticSemantics.md#r-statics.call-order.well-founded). This
rule is open.

## The table evaluator

The rules of this section are stated in Fren. They evaluate the rows of a
call-free [derivation table](Types.md#derivations), and give no value
where the open rules above will give an error or the value of a product, a
quotient, a remainder or a call. A table has no calls and its rows are
finite, so this evaluator always ends.

r[expressions.meaning.values] spec::dynamics::{unary_value, integer_value, boolean_value, binary_value}
`unary_value` and `binary_value` compute an operator's result from its
operands' values. They give none for operands of the wrong sorts. They
give none for `*`, `div` and `%` either: the relation `binary_meaning?`
only [approximates](DenotationalSemantics.md#r-denotation.operators.arithmetic)
the results of those three, and no function here computes them.

```fren
pub mod spec
pub mod spec::dynamics

use spec::denotation::{Value, binary_meaning?, unary_meaning?}

use spec::names::{CoreF, Ctx, Form, ItemId, Ty, four, length, lookup, one}

use spec::surface::{BinaryOp, Snoc, UnaryOp}

use spec::types::{Arm, Row}

use spec::surface::Snoc::{Empty, Extend}

pub fn unary_value(op: UnaryOp, operand: Value): Option<Value> := match op, operand {
    UnaryOp::Neg, Value::Integer(n) => Some(Value::Integer(-n)),
    UnaryOp::Not, Value::Boolean(b?) => Some(Value::Boolean(not b?)),
    _, _ => None,
}

pub fn integer_value(op: BinaryOp, a: Int, b: Int): Option<Value> := match op {
    BinaryOp::Add => Some(Value::Integer(a + b)),
    BinaryOp::Sub => Some(Value::Integer(a - b)),
    BinaryOp::Lt => Some(Value::Boolean(a < b)),
    BinaryOp::Le => Some(Value::Boolean(a <= b)),
    BinaryOp::Gt => Some(Value::Boolean(a > b)),
    BinaryOp::Ge => Some(Value::Boolean(a >= b)),
    BinaryOp::Eq => Some(Value::Boolean(a = b)),
    BinaryOp::Ne => Some(Value::Boolean(a != b)),
    _ => None,
}

pub fn boolean_value(op: BinaryOp, p?, q?): Option<Value> := match op {
    BinaryOp::And => Some(Value::Boolean(p? and q?)),
    BinaryOp::Or => Some(Value::Boolean(p? or q?)),
    BinaryOp::Iff | BinaryOp::Eq => Some(Value::Boolean(p? iff q?)),
    BinaryOp::Ne => Some(Value::Boolean(not (p? iff q?))),
    _ => None,
}

pub fn binary_value(op: BinaryOp, left: Value, right: Value): Option<Value> := match left, right {
    Value::Integer(a), Value::Integer(b) => integer_value(op, a, b),
    Value::Boolean(p?), Value::Boolean(q?) => boolean_value(op, p?, q?),
    Value::Nominal(_, _), Value::Nominal(_, _) => match op {
        BinaryOp::Eq => Some(Value::Boolean(left = right)),
        BinaryOp::Ne => Some(Value::Boolean(left != right)),
        _ => None,
    },
    _, _ => None,
}
```

r[expressions.meaning.values-agree] spec::dynamics::values_agree::{unary, binary}
A computed result is a result that the operator's meaning admits.

```fren
set_option fren.evidence "random" in
pub proc values_agree(unop: UnaryOp, op: BinaryOp, left: Value, right: Value, result: Value): (
    holds?,
) {
    ensure output: holds?
    ensure unary: when unary_value(unop, left) = Some(result), unary_meaning?(unop, left, result)
    ensure binary: when binary_value(op, left, right) = Some(result),
        binary_meaning?(op, left, right, result)
}
```

r[expressions.meaning.evaluation] spec::dynamics::{value_at, arm_value, layer_value, initial, values, eval}
The *evaluator* computes the value of every row of a
[derivation table](Types.md#derivations) in one local assignment ρ.
`values` works row by row, oldest first, and reads each child's value from
the rows before it. A literal, a local and a constructor have the values
that [the interpretation](DenotationalSemantics.md#r-expressions.meaning.context)
gives them. An
operator row has the result of `unary_value` or `binary_value` at its
operands' values. A conditional has the value of the branch that its
condition selects, and a match the value of the arm for its scrutinee's
constructor. A let row is evaluated in two steps: its value v in ρ, then
its body in the assignment that keeps the levels of the let's own context
and appends v. `eval(t, r, ρ)` is the value of row r.

A row has no value when a child that it needs has none, when a local is
not in ρ, when an operator has no result, or when it is a call. So a
row that depends on a product, a quotient or a remainder has none. The
evaluator is strict where verification is: an operator needs both
operands' values, and a let needs its value's, whether or not the result
depends on them. A conditional needs only the selected branch, and a match
only the selected arm. The evaluator covers the call-free Core; evaluating
a call needs the callee's body, and is not yet specified.

```fren
pub fn value_at(prior: Snoc<Option<Value>>, pos: Int): Option<Value> := match lookup(prior, pos) {
    Some(value) => value,
    None => None,
}

pub fn arm_value(prior: Snoc<Option<Value>>, arms: Snoc<Arm>, constructor: ItemId): Option<Value> :=
    match arms {
        Empty => None,
        Extend(earlier, arm) =>
            if arm.constructor = constructor then value_at(prior, arm.body)
            else arm_value(prior, earlier, constructor),
    }

pub fn layer_value(prior: Snoc<Option<Value>>, env: Snoc<Value>, row: Row): Option<Value> :=
    match row.form {
        CoreF::BooleanLiteral(value?) => Some(Value::Boolean(value?)),
        CoreF::IntegerLiteral(value) => Some(Value::Integer(value)),
        CoreF::Local(level) => lookup(env, level),
        CoreF::Constructor(item) => match row.ty {
            Ty::Nominal(owner) => Some(Value::Nominal(owner, item)),
            _ => None,
        },
        CoreF::Unary(op, operand) => match value_at(prior, operand) {
            Some(value) => unary_value(op, value),
            None => None,
        },
        CoreF::Binary(op, left, right) => match value_at(prior, left), value_at(prior, right) {
            Some(l), Some(r) => binary_value(op, l, r),
            _, _ => None,
        },
        CoreF::If(condition, yes, no) => match value_at(prior, condition) {
            Some(Value::Boolean(holds?)) =>
                if holds? then value_at(prior, yes) else value_at(prior, no),
            _ => None,
        },
        CoreF::Match(scrutinee, arms) => match value_at(prior, scrutinee) {
            Some(Value::Nominal(_, constructor)) => arm_value(prior, arms, constructor),
            _ => None,
        },
        _ => None,
    }

pub fn initial<T>(xs: Snoc<T>, count: Int): Snoc<T> := match xs {
    Empty => Empty,
    Extend(earlier, _) => if length(earlier) < count then xs else initial(earlier, count),
}

pub fn values(rows: Snoc<Row>, env: Snoc<Value>): Snoc<Option<Value>> := match rows {
    Empty => Empty,
    Extend(earlier, row) => Extend(
        values(earlier, env),
        match row.form {
            CoreF::Let(_, value, body) => match value_at(values(earlier, env), value) {
                Some(bound) => value_at(
                    values(earlier, Extend(initial(env, length(row.ctx)), bound)),
                    body
                ),
                None => None,
            },
            _ => layer_value(values(earlier, env), env, row),
        }
    ),
}

pub fn eval(rows: Snoc<Row>, pos: Int, env: Snoc<Value>): Option<Value> :=
    value_at(values(rows, env), pos)
```

r[expressions.examples.evaluation] spec::dynamics::{typed, LET_ROWS, evaluation_examples::{bound, unbound, uncomputed}}
`let d := 2 in 10 - d` has this table; row 4 is the let.

| Row | Layer | Context |
| --- | --- | --- |
| 0 | `2` | `·` |
| 1 | `10` | `·, Int` |
| 2 | `#0` | `·, Int` |
| 3 | `row 1 - row 2` | `·, Int` |
| 4 | `let d := row 0 in row 3` | `·` |

In the empty assignment the let has the value 8. Its body's row 3 has
none there, since the local is not in the assignment. A quotient has no
computed value, even of 10 and 2.

```fren
pub fn typed(form: Form, ctx: Ctx, ty: Ty): Row := Row { form, ctx, ty }

pub const LET_ROWS: Snoc<Row> := Extend(
    four(
        typed(CoreF::IntegerLiteral(2), Empty, Ty::Integer),
        typed(CoreF::IntegerLiteral(10), one(Ty::Integer), Ty::Integer),
        typed(CoreF::Local(0), one(Ty::Integer), Ty::Integer),
        typed(
            CoreF::Binary(BinaryOp::Sub, 1, 2),
            one(Ty::Integer),
            Ty::Integer
        )
    ),
    typed(CoreF::Let(None, 0, 3), Empty, Ty::Integer)
)

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc evaluation_examples(): (holds?) {
    ensure output: holds?
    ensure bound: eval(LET_ROWS, 4, Empty) = Some(Value::Integer(8))
    ensure unbound: eval(LET_ROWS, 3, Empty) = None
    ensure uncomputed: binary_value(BinaryOp::Div, Value::Integer(10), Value::Integer(2)) = None
}
```

## Properties

The properties of this section are open: none is stated in Fren or proved.

r[dynamics.theorem.determinism]
An expression has at most one outcome at an assignment, and an expression
that has an outcome there does not diverge there.

r[dynamics.theorem.type-safety]
In a well-typed program, a well-typed expression of type τ, at an
assignment of its context, either evaluates to a valid value of type τ,
or evaluates to one of the listed errors, or diverges. It is in no other
state: no rule is missing for a well-typed expression. In a step
presentation this is progress and preservation. The theorem does not say
that evaluation ends.

r[dynamics.theorem.termination]
Evaluation ends where recursion is well founded. In a well-typed program
whose [call order is well founded](StaticSemantics.md#r-statics.call-order.well-founded),
every well-typed expression has an outcome at every assignment of its
context that meets the conditions under which the static semantics
establishes the decrease of each recursive call. Without that condition
the theorem is false: a well-typed function whose body is a call of itself
at its own parameters diverges. The exact condition is open with the
static rule it cites.

r[dynamics.theorem.adequacy]
In a verified program, an expression that is defined under hypotheses
which the assignment ρ makes true does not diverge and evaluates to a
value and not to an error, and that value is its denotation:
`P ⊢ ⟨e, ρ⟩ ⇓ ⟦e⟧ρ`. A verified function called at an argument tuple that
meets its precondition evaluates to its denotation there.

r[dynamics.theorem.table-agreement]
Where the [table evaluator](#the-table-evaluator) gives a row a value, the
evaluation judgment gives the row's expression that value.

r[dynamics.theorem.implementation]
An implementation that evaluates in another order, or that omits a check
which verification has discharged, agrees with this chapter on verified
programs. The [evaluator chapter](../Compiler/Evaluator.md) states the
agreement of the compiler's evaluator; it is open here.
