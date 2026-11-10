# Dynamic semantics

The dynamic semantics evaluates an expression. It is operational and
small-step: a one-step relation rewrites a configuration, and an
evaluation is a run of steps. It is defined for every well-typed
program, whether or not the program is
[verified](StaticSemantics.md#r-statics.program.verified) and whether or
not it has a [static error](StaticSemantics.md#r-statics.scope). A run has one
of three results: it ends in a value, it ends in an error state, or it
diverges. Evaluation contexts fix one order of evaluation. An operation
outside its domain steps to an error state, and never to an arbitrary
value. The [denotational semantics](DenotationalSemantics.md) gives a
meaning only to a function that
[has a denotation](DenotationalSemantics.md#r-denotation.domain): its
declaration and the declaration of every function that it depends on are
verified, and their assumptions are true.
[Adequacy](#r-dynamics.theorem.adequacy) states that an expression over
such functions, evaluated where its hypotheses are true, ends in a
value, which is the denotation.

A rule whose `r[...]` line names no Fren definition is stated in prose
only. What this chapter states in Fren is
[an evaluator of derivation tables](#the-table-evaluator).

## Overview

| Judgment | Meaning | Rule | Fren |
| --- | --- | --- | --- |
| `P ⊢ m → m′` | in the program P, the configuration m takes one step to m′ | [steps](#r-dynamics.step) | — |
| `P ⊢ m → error(k)` | m takes one step to the error state of kind k | [steps](#r-dynamics.step) | — |
| `P ⊢ m →* s` | a finite run leads from m to the state s | [runs](#r-dynamics.run) | — |
| `P ⊢ m ⇑` | m diverges: it has an infinite run | [divergence](#r-dynamics.divergence) | — |
| `P ⊢ m : τ` | the configuration m has the type τ | [configuration typing](#r-dynamics.configuration.typing) | — |
| `op(v) = r`, `op(v₁, v₂) = r` | the operator op has the outcome r at the operand values | [operators](#r-dynamics.operators.total) | `unary_value` and `operator_outcome`, where they give an outcome |
| `P ⊢ ⟨e, ρ⟩ ⇓ r` | derived: e evaluates at ρ to the outcome r | [big-step evaluation](#r-dynamics.evaluation.rules) | — |
| `outcome(C, t, i, ρ) = r` | row i of the table t has the outcome r at ρ, with the call record C | [the table evaluator](#r-expressions.meaning.evaluation) | `outcome` |
| `eval(t, i, ρ) = v` | that outcome is the value v, with the empty call record | [the table evaluator](#r-expressions.meaning.evaluation) | `eval` |
| `justified?(P, C)` | each call of the record C has the outcome that its callee's body has in P | [call records](#r-dynamics.table.calls) | `justified?` |

```text
  m ::= v                              configurations: a value
      | op m  |  m₁ op m₂              an operator
      | if m₀ then m₁ else m₂          a conditional
      | match m₀ { c₁ ⇒ m₁ … cₙ ⇒ mₙ }  a match
      | let m in (e, ρ)                a let; its body e waits at ρ
      | f(m₁, …, mₙ)                   a call

  s ::= m  |  error(k)                 states
  r ::= v  |  error(k)                 outcomes

  k ::= zero-divisor                   division or remainder by zero
      | no-arm                         a match without an arm for its value

  ρ ::= ·  |  ρ, v                     assignments, by de Bruijn level

  E ::= []                             evaluation contexts
      | op E
      | E op m  |  v op E              op is neither `and` nor `or`
      | E and m  |  E or m
      | if E then m₁ else m₂
      | match E { c₁ ⇒ m₁ … cₙ ⇒ mₙ }
      | let E in (e, ρ)
      | f(v₁, …, vᵢ₋₁, E, mᵢ₊₁, …, mₙ)
```

The values v are those of the
[denotational semantics](DenotationalSemantics.md#values). P is a
well-typed program.

## Scope

r[dynamics.scope]
The dynamic semantics is defined for every well-typed program, and for
the well-typed expressions over it. A program in which a match has two
arms for one constructor is
[in error statically](StaticSemantics.md#r-statics.match.distinct) and is
still well typed, so this chapter evaluates it:
[selection](#r-dynamics.match.selection) takes the first of the arms. The
dynamic semantics reads no contract,
no hypothesis, no result of the termination check and no solver's answer:
a run depends only on the program, the expression and the assignment. It
evaluates the bodies of functions and never their conditions, unless a
condition is itself the expression being evaluated.

## Configurations

r[dynamics.configuration]
A *configuration* m is an expression in the course of its evaluation. It
has the forms of Core, with two differences. It has no local: every local
has been replaced by its value. The body of a let stays a Core expression
e, paired with the assignment ρ at which the let was loaded; it becomes a
configuration when the let's value is known. The body cannot be loaded
with the let: loading replaces every local by its value, and the body's
newest local has none until the let's value is known. So the pair is a
closure, and a let is the one place where the replacement of locals is
delayed. A *state* is a configuration
or an error state `error(k)`. An error state is not a configuration: no
context holds one, and no operator or call takes one as an operand.
[Loading](#r-dynamics.configuration.loading) keeps the arms of a match in
the order in which they are written, and so does every step.

r[dynamics.configuration.loading]
*Loading* gives the configuration `⟨e, ρ⟩` of an expression e, well typed
in a context Γ, at an assignment ρ of Γ. It is
defined by recursion on e
and evaluates nothing. A literal and a constructor load to their
[leaf values](DenotationalSemantics.md#r-denotation.leaf), and the local
of level i loads to the value that ρ gives level i. `⟨let e₁ in e₂, ρ⟩`
is `let ⟨e₁, ρ⟩ in (e₂, ρ)`. Every other form loads its children at ρ:
`⟨e₁ op e₂, ρ⟩` is `⟨e₁, ρ⟩ op ⟨e₂, ρ⟩`, and likewise for a unary
operator, a conditional, the scrutinee and the arms of a match, and the
arguments of a call. The *initial configuration* of e at ρ is `⟨e, ρ⟩`.

r[dynamics.configuration.typing]
`P ⊢ m : τ` types a configuration. A value has the type τ when it is a
[valid value](DenotationalSemantics.md#values) of τ. An operator, a
conditional, a match and a call are typed from the types of their
children by the [Core rule](Types.md#typing-rules) of their form.
`let m in (e, ρ)` has the type τ when m has a type σ, ρ gives each level
of a context Γ a value of its type, and e has the type τ in Γ extended
with σ.

## Steps

r[dynamics.context]
An *evaluation context* E is a configuration with one hole `[]`, of the
forms that the [overview](#overview) lists; `E[m]` is E with m in its
hole. The contexts fix the [order of evaluation](#r-dynamics.order): the
hole is where the next step is taken. There is no context for the second
operand of `and` or `or`, for a branch of a conditional, for an arm of a
match or for the body of a let.

r[dynamics.step]
The *step relation* has two forms, `P ⊢ m → m′` and `P ⊢ m → error(k)`.
It is the least relation closed under the
[reductions](#r-dynamics.step.reductions) and two context rules: a step
of m to m′ is a step of `E[m]` to `E[m′]`, and a step of m to `error(k)`
is a step of `E[m]` to `error(k)`. A value takes no step, and neither
does an error state.

```text
  P ⊢ m → m′                       P ⊢ m → error(k)
  ───────────────────              ─────────────────────
  P ⊢ E[m] → E[m′]                 P ⊢ E[m] → error(k)
```

r[dynamics.step.reductions]
A *reduction* is a step of a configuration that is not a value and whose
evaluated children are values. The reductions are these, and no others.

```text
  op v → v′                            when op(v) = v′
  v₁ op v₂ → r                         when op(v₁, v₂) = r;
                                       op is neither `and` nor `or`
  false and m → false                  true and m → m
  true or m → true                     false or m → m
  if true then m₁ else m₂ → m₁         if false then m₁ else m₂ → m₂
  match c { c₁ ⇒ m₁ … cₙ ⇒ mₙ } → mᵢ    when selection gives arm i
  match c { c₁ ⇒ m₁ … cₙ ⇒ mₙ } → error(no-arm)
                                       when selection gives no arm
  let v in (e, ρ) → ⟨e, (ρ, v)⟩
  f(v₁, …, vₙ) → ⟨e, (·, v₁, …, vₙ)⟩    when f has the body e in P
```

The outcome of an operator is that of
[its rule](#r-dynamics.operators.total), and the arm of a match is the
one that [selection](#r-dynamics.match.selection) gives.

r[dynamics.run]
A *run* from m is a sequence of states that starts at m, each state but
the first being a step from the one before it. `P ⊢ m →* s` holds when a
finite run from m ends at s; a run of no steps gives `m →* m`. A run
*ends* when its last state is a value or an error state. A configuration
is *stuck* when it is not a value and takes no step.

## Outcomes, errors and divergence

r[dynamics.outcome]
An *outcome* is a value or an error state. An expression e *has the
outcome* r at ρ when `P ⊢ ⟨e, ρ⟩ →* r`. An evaluation has one of three
*results*: it ends in a value, it ends in an error, or it
[diverges](#r-dynamics.divergence).

r[dynamics.error.kinds]
There are two kinds of error. A division or remainder whose divisor is
zero steps to `error(zero-divisor)`. A match whose scrutinee is a
constructor that none of its arms has steps to `error(no-arm)`. Nothing
else is an error. In particular a call at arguments that fail its
callee's precondition is not one: the call steps to the callee's body as
[any call does](#r-dynamics.call).

r[dynamics.error.propagation]
An error state ends the run. When a configuration in an evaluation
context steps to an error state, the whole configuration steps to that
error state, by the second [context rule](#r-dynamics.step); nothing
that the context holds is evaluated afterwards.

r[dynamics.divergence]
Divergence, `P ⊢ m ⇑`, is a judgment of its own. It is not the absence
of an outcome: m *diverges* when there is an infinite run from m, that
is, an infinite sequence m₀, m₁, m₂, … of configurations with m₀ = m and
`P ⊢ mᵢ → mᵢ₊₁` for every i. An expression e diverges at ρ when its
initial configuration `⟨e, ρ⟩` does. Divergence is not an outcome and not
an error.

## Order of evaluation

r[dynamics.order]
Evaluation has one fixed order, which the
[evaluation contexts](#r-dynamics.context) give. The arguments of a call,
and the operands of every operator other than `and` and `or`, are
evaluated left to right, each exactly once, before the call or operator
itself. `and` and `or` short-circuit: each evaluates its first operand,
and evaluates its second only when the first does not decide the result,
which is when the first operand of `and` is true and when that of `or` is
false. A let evaluates its value, used or not, then its body. A
conditional evaluates its condition, then only the selected branch; a
match evaluates its scrutinee, then only the selected arm.
[Definedness](StaticSemantics.md#r-statics.definedness.declarative) does
not follow the order: it requires both operands of `and` and of `or` to
be defined, under the same hypotheses.

r[dynamics.match.selection]
A match selects, for a scrutinee value that is the constructor c, the
first arm written whose constructor is c. So selection gives exactly one
arm or none, in every well-typed match. Where the arms of the match are
[distinct](StaticSemantics.md#r-statics.match.distinct), at most one arm
has that constructor, and it is the arm selected. Where several arms
have it, the match is a static error; it is still well typed, and
selection takes the first of them and never an arm written after it.
This is the arm that [`select`](Patterns.md#r-patterns.matching.select)
gives. When no arm has the constructor, the match selects no arm and
steps to `error(no-arm)`.

r[dynamics.operators.total]
`op(v) = r` and `op(v₁, v₂) = r` give an operator's outcome at operand
values of its operand types. `div` and `%` have the outcome
`error(zero-divisor)` at a zero divisor. At every other operand values an
operator's outcome is the value that
[its meaning](DenotationalSemantics.md#r-expressions.meaning.operators)
gives: for `*`, `div` and `%`, the product and the Euclidean quotient and
remainder of
[integer arithmetic](DenotationalSemantics.md#r-denotation.operators.arithmetic).
The reductions take the outcomes of `and` and `or` from their first
operand alone where it decides them, and from this rule nowhere.

r[dynamics.call]
A call whose arguments are values steps to the callee's body, loaded at
the assignment that lists the argument values, without the caller's
locals. The step reads no contract and bounds no recursion: it is taken
whether or not the arguments meet the callee's precondition, and whether
or not the callee's declaration
[passes the termination check](StaticSemantics.md#r-statics.termination).

## Big-step evaluation

r[dynamics.evaluation.rules]
`P ⊢ ⟨e, ρ⟩ ⇓ r` is a derived judgment for the evaluations that end. It
is not the definition of evaluation, which is the
[step relation](#r-dynamics.step);
[a property](#r-dynamics.theorem.big-step) relates the two. It is defined
inductively, by rules for each Core form: one for the form's value, one
for each [error of the form's own](#r-dynamics.error.kinds), and one for
each evaluated child that has an error, whose error the form then has. A
literal, a local and a constructor evaluate to their
[leaf values](DenotationalSemantics.md#r-denotation.leaf). An operator
evaluates its operands in [order](#r-dynamics.order) and has the
[outcome of the operator](#r-dynamics.operators.total) at their values;
`and` whose first operand is false is false, and `or` whose first
operand is true is true, and otherwise each has the outcome of its second
operand. A let has the outcome of its body at the assignment with the
value of its value appended. A conditional has the outcome of the branch
that its condition's value selects, and a match that of the arm that
[selection](#r-dynamics.match.selection) gives. A call has the outcome of
its callee's body at the assignment that lists its arguments' values.

## The table evaluator

r[expressions.meaning.values] spec::dynamics::{unary_value, integer_value, boolean_value, binary_value}
`unary_value` and `binary_value` compute an operator's result from its
operands' values. They give none for operands of the wrong sorts. They
give none for `*`, `div` and `%` either: the relation `binary_meaning?`
only [approximates](DenotationalSemantics.md#r-denotation.operators.arithmetic)
the results of those three, and no function here computes them. Fren1,
in which this chapter is written, has no product of two variables and no
quotient or remainder by a variable, and a function defined in it cannot
apply an uninterpreted one, so none can be written.

```fren
pub mod spec
pub mod spec::dynamics

use spec::denotation::{Value, binary_meaning?, unary_meaning?}

use spec::names::{CoreF, Ctx, Form, ItemId, Ty, four, length, lookup, one}

use spec::surface::{BinaryOp, Snoc, UnaryOp}

use spec::types::{Arm, Decl, Row}

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

r[dynamics.table.outcome] spec::dynamics::{ErrorKind, Outcome, valued, outcome_at, zero_divisor?, operator_outcome, binary_outcome}
The evaluator gives a row an [outcome](#r-dynamics.outcome), a value or
an error of one of the [two kinds](#r-dynamics.error.kinds), or it gives
the row none. `operator_outcome` is the
[outcome of a binary operator](#r-dynamics.operators.total) at two
values: `error(zero-divisor)` for `div` and `%` at two integers of which
the second is zero, and otherwise the value that `binary_value` gives,
where it gives one. `binary_outcome` is the outcome of an operator row
from the value of its first operand and the outcome of its second, in
the [order of evaluation](#r-dynamics.order). `and` at false is false and
`or` at true is true, whatever the second operand's row has, an error or
no outcome included; `and` at true and `or` at false have the outcome of
the second operand. Every other operator has the second operand's error
where it has one, and otherwise the operator's outcome at the two
values.

```fren
pub enum ErrorKind { ZeroDivisor, NoArm }

pub enum Outcome { Value(Value), Error(ErrorKind) }

pub fn valued(value: Option<Value>): Option<Outcome> := match value {
    Some(found) => Some(Outcome::Value(found)),
    None => None,
}

pub fn outcome_at(prior: Snoc<Option<Outcome>>, pos: Int): Option<Outcome> :=
    match lookup(prior, pos) {
        Some(outcome) => outcome,
        None => None,
    }

pub fn zero_divisor?(op: BinaryOp, left: Value, right: Value) := match op, left, right {
    BinaryOp::Div | BinaryOp::Rem, Value::Integer(_), Value::Integer(divisor) => divisor = 0,
    _, _, _ => false,
}

pub fn operator_outcome(op: BinaryOp, left: Value, right: Value): Option<Outcome> :=
    if zero_divisor?(op, left, right) then Some(Outcome::Error(ErrorKind::ZeroDivisor))
    else valued(binary_value(op, left, right))

pub fn binary_outcome(op: BinaryOp, left: Value, second: Option<Outcome>): Option<Outcome> :=
    match op {
        BinaryOp::And => match left {
            Value::Boolean(holds?) => if holds? then second else Some(Outcome::Value(left)),
            _ => None,
        },
        BinaryOp::Or => match left {
            Value::Boolean(holds?) => if holds? then Some(Outcome::Value(left)) else second,
            _ => None,
        },
        _ => match second {
            Some(Outcome::Value(right)) => operator_outcome(op, left, right),
            Some(Outcome::Error(kind)) => Some(Outcome::Error(kind)),
            None => None,
        },
    }
```

r[dynamics.table.calls] spec::dynamics::{Call, called, Operands, operands, body_of, justified?}
The evaluator does not run a callee's body where it meets a call. It
reads the call's outcome from a *call record* C, a sequence of calls,
each a callee, a tuple of argument values and an outcome. `called` gives
the outcome that C lists for a callee at an argument tuple, and none
where C lists no such call. `operands` evaluates the arguments of a call
left to right: it gives their values, or the error of the first argument
that has one, and none where an argument before that error has no
outcome.

A call record is *justified* in a program when each of its calls names a
function that has a body in the program, and the call's outcome is the
one that the evaluator gives the last row of that body, at the
assignment that lists the call's arguments and with the calls listed
before it as the call record. `body_of` takes the last declaration of
the callee's name, which is the step relation's lookup in a
[well-typed program](Types.md#r-types.program.typing), since that
declares each function once. So a justified record is a finite
derivation of its calls' outcomes, oldest first, and it plays the part
of fuel: each call that the evaluation of a body reaches must be listed
earlier. By [table agreement](#r-dynamics.theorem.table-agreement),
which is open, a call of a well-typed program at valid argument values
that [diverges](#r-dynamics.divergence) is listed in no justified
record, so the evaluator gives it no outcome, whatever justified record
it is given. The record rests on no result of the
[termination check](StaticSemantics.md#r-statics.termination).

```fren
pub struct Call { callee: ItemId, arguments: Snoc<Value>, outcome: Outcome }

pub fn called(record: Snoc<Call>, callee: ItemId, arguments: Snoc<Value>): Option<Outcome> :=
    match record {
        Empty => None,
        Extend(earlier, call) =>
            if call.callee = callee and call.arguments = arguments then Some(call.outcome)
            else called(earlier, callee, arguments),
    }

pub enum Operands { Values(Snoc<Value>), Error(ErrorKind) }

pub fn operands(prior: Snoc<Option<Outcome>>, args: Snoc<Int>): Option<Operands> := match args {
    Empty => Some(Operands::Values(Empty)),
    Extend(earlier, arg) => match operands(prior, earlier) {
        Some(Operands::Values(found)) => match outcome_at(prior, arg) {
            Some(Outcome::Value(value)) => Some(Operands::Values(Extend(found, value))),
            Some(Outcome::Error(kind)) => Some(Operands::Error(kind)),
            None => None,
        },
        Some(Operands::Error(kind)) => Some(Operands::Error(kind)),
        None => None,
    },
}

pub fn body_of(decls: Snoc<Decl>, item: ItemId): Option<Snoc<Row>> := match decls {
    Empty => None,
    Extend(earlier, decl) => match decl {
        Decl::Function(name, rows) => if name = item then Some(rows) else body_of(earlier, item),
        Decl::Condition(_, _) => body_of(earlier, item),
    },
}
```

r[expressions.meaning.evaluation] spec::dynamics::{first_arm, arm_outcome, layer_outcome, initial, outcomes, outcome, eval, justified?}
The *evaluator* computes the outcome of every row of a
[derivation table](Types.md#derivations) in one local assignment ρ and
with one [call record](#r-dynamics.table.calls) C. `outcomes` works row by
row, oldest first, and reads each child's outcome from the rows before
it. A literal, a local and a constructor have their
[leaf values](DenotationalSemantics.md#r-denotation.leaf). A unary
operator row has the result of `unary_value` at its operand's value, and
a binary operator row the outcome that
[`binary_outcome`](#r-dynamics.table.outcome) gives. A conditional has
the outcome of the branch that its condition selects. A match has the
outcome of the arm that `first_arm` takes for its scrutinee's
constructor, which is the first arm written for it, as
[selection](#r-dynamics.match.selection) gives; where no arm is written
for it, the match has the outcome `error(no-arm)`. A call has the
outcome that C lists for its callee at its arguments' values. A let row
is evaluated in two steps: its value v in ρ, then its body in the
assignment that keeps the levels of the let's own context and appends v.
`outcome(C, t, r, ρ)` is the outcome of row r, and `eval(t, r, ρ)` is the
value of row r with the empty call record, where that outcome is a
value.

A row has the error of the child that the
[order of evaluation](#r-dynamics.order) evaluates first among its
children with an error, where every child evaluated before that one has
a value: an operand, a condition, a scrutinee, an argument or a let's
value. The outcome of a branch, of an arm and of a let's body is the
row's own, an error included.

Where no error passes to it in this way, a row has no outcome when a
child that it needs has none, when a local is not in ρ, when an operator
has no result at its operands' values, or when it is a call whose
arguments have values and which C does not list at them. So a row that
needs the value of a product, of a quotient or of a remainder whose
operands have values, the divisor not zero, or of a call that C does
not list at its arguments' values, has none. A conditional needs only its condition
and the selected branch, a match only its scrutinee and the selected
arm, and `and` and `or` need their second operand only where the first
does not decide them. A let needs its value's outcome, whether or not
its body reads it.

```fren
pub fn first_arm(arms: Snoc<Arm>, constructor: ItemId): Option<Arm> := match arms {
    Empty => None,
    Extend(earlier, arm) => match first_arm(earlier, constructor) {
        Some(found) => Some(found),
        None => if arm.constructor = constructor then Some(arm) else None,
    },
}

pub fn arm_outcome(
    prior: Snoc<Option<Outcome>>,
    arms: Snoc<Arm>,
    constructor: ItemId
): Option<Outcome> := match first_arm(arms, constructor) {
    Some(found) => outcome_at(prior, found.body),
    None => Some(Outcome::Error(ErrorKind::NoArm)),
}

pub fn layer_outcome(
    record: Snoc<Call>,
    prior: Snoc<Option<Outcome>>,
    env: Snoc<Value>,
    row: Row
): Option<Outcome> := match row.form {
    CoreF::BooleanLiteral(value?) => Some(Outcome::Value(Value::Boolean(value?))),
    CoreF::IntegerLiteral(value) => Some(Outcome::Value(Value::Integer(value))),
    CoreF::Local(level) => valued(lookup(env, level)),
    CoreF::Constructor(item) => match row.ty {
        Ty::Nominal(owner) => Some(Outcome::Value(Value::Nominal(owner, item))),
        _ => None,
    },
    CoreF::Unary(op, operand) => match outcome_at(prior, operand) {
        Some(Outcome::Value(value)) => valued(unary_value(op, value)),
        Some(Outcome::Error(kind)) => Some(Outcome::Error(kind)),
        None => None,
    },
    CoreF::Binary(op, left, right) => match outcome_at(prior, left) {
        Some(Outcome::Value(value)) => binary_outcome(op, value, outcome_at(prior, right)),
        Some(Outcome::Error(kind)) => Some(Outcome::Error(kind)),
        None => None,
    },
    CoreF::If(condition, yes, no) => match outcome_at(prior, condition) {
        Some(Outcome::Value(Value::Boolean(holds?))) =>
            if holds? then outcome_at(prior, yes) else outcome_at(prior, no),
        Some(Outcome::Error(kind)) => Some(Outcome::Error(kind)),
        _ => None,
    },
    CoreF::Match(scrutinee, arms) => match outcome_at(prior, scrutinee) {
        Some(Outcome::Value(Value::Nominal(_, constructor))) =>
            arm_outcome(prior, arms, constructor),
        Some(Outcome::Error(kind)) => Some(Outcome::Error(kind)),
        _ => None,
    },
    CoreF::Call(callee, args) => match operands(prior, args) {
        Some(Operands::Values(arguments)) => called(record, callee, arguments),
        Some(Operands::Error(kind)) => Some(Outcome::Error(kind)),
        None => None,
    },
    CoreF::Let(_, _, _) => None,
}

pub fn initial<T>(xs: Snoc<T>, count: Int): Snoc<T> := match xs {
    Empty => Empty,
    Extend(earlier, _) => if length(earlier) < count then xs else initial(earlier, count),
}

pub fn outcomes(record: Snoc<Call>, rows: Snoc<Row>, env: Snoc<Value>): Snoc<Option<Outcome>> :=
    match rows {
        Empty => Empty,
        Extend(earlier, row) => Extend(
            outcomes(record, earlier, env),
            match row.form {
                CoreF::Let(_, value, body) =>
                    match outcome_at(outcomes(record, earlier, env), value) {
                        Some(Outcome::Value(bound)) => outcome_at(
                            outcomes(
                                record,
                                earlier,
                                Extend(initial(env, length(row.ctx)), bound)
                            ),
                            body
                        ),
                        Some(Outcome::Error(kind)) => Some(Outcome::Error(kind)),
                        None => None,
                    },
                _ => layer_outcome(record, outcomes(record, earlier, env), env, row),
            }
        ),
    }

pub fn outcome(record: Snoc<Call>, rows: Snoc<Row>, pos: Int, env: Snoc<Value>): Option<Outcome> :=
    outcome_at(outcomes(record, rows, env), pos)

pub fn eval(rows: Snoc<Row>, pos: Int, env: Snoc<Value>): Option<Value> :=
    match outcome(Empty, rows, pos, env) {
        Some(Outcome::Value(value)) => Some(value),
        _ => None,
    }

pub fn justified?(decls: Snoc<Decl>, record: Snoc<Call>) := match record {
    Empty => true,
    Extend(earlier, call) =>
        justified?(decls, earlier)
        and match body_of(decls, call.callee) {
            Some(rows) =>
                outcome(earlier, rows, length(rows) - 1, call.arguments) = Some(call.outcome),
            None => false,
        },
}
```

r[dynamics.table.differences]
The table evaluator is not the step relation. It agrees with it on
[errors](#r-dynamics.error.kinds), on the
[order of evaluation](#r-dynamics.order), `and` and `or` included, and on
the [arm of a match](#r-dynamics.match.selection). Three differences
remain.

- It computes a row's outcome in one pass over the rows before it, and
  has no configurations, steps or runs. A function of a derivation table
  cannot have them: the [derived judgment](#r-dynamics.evaluation.rules)
  is its counterpart, and
  [table agreement](#r-dynamics.theorem.table-agreement) relates it to
  the runs.
- It gives no outcome to a product whose operands have values, or to a
  quotient or a remainder whose operands have values and whose divisor
  is not zero, where the step relation reduces each to a value.
  [Fren1 cannot compute them](#r-expressions.meaning.values). The error
  at a zero divisor is computed, and so is the error of an operand,
  which passes to the product, quotient or remainder that reads it.
- It does not find a call's outcome: it reads the outcome from a
  [call record](#r-dynamics.table.calls), and gives the call none where
  its arguments have values and the record does not list it at them; an
  argument's error passes to the call whatever the record lists. The step relation reduces every call to
  its callee's body. A function of Fren1 recurses only on a part of one
  of its parameters, and a callee's body is no part of the caller's
  table, so the evaluator cannot enter it; the justified record is the
  finite derivation that stands for the run. The evaluator is total, so
  it cannot diverge. By
  [table agreement](#r-dynamics.theorem.table-agreement), which is open,
  a call that diverges in a well-typed program has no outcome at any
  justified record.

Where it gives an outcome at a justified record,
[the step relation gives the same one](#r-dynamics.theorem.table-agreement).
The compiler's evaluator is a third function, and the
[evaluator chapter](../Compiler/Evaluator.md#differences-from-the-step-relation)
lists the ways in which it differs from the step relation; the two lists
are of different evaluators and are kept apart.

r[expressions.examples.evaluation] spec::dynamics::{typed, LET_ROWS, QUOTIENT_ROWS, DOUBLE, DOUBLE_ROWS, CALL_ROWS, ERROR_ROWS, doubled, DOUBLED, evaluation_examples::{bound, unbound, uncomputed, zero_divisor, decided, propagated, uncalled, product_propagated, call_propagated, quotient_propagated, remainder_propagated, called, justified, unjustified}}
`let d := 2 in 10 - d` has this table; row 4 is the let.

| Row | Layer | Context |
| --- | --- | --- |
| 0 | `2` | `·` |
| 1 | `10` | `·, Int` |
| 2 | `#0` | `·, Int` |
| 3 | `row 1 - row 2` | `·, Int` |
| 4 | `let d := row 0 in row 3` | `·` |

In the empty assignment the let has the value 8. Its body's row 3 has
no outcome there, since the local is not in the assignment. The
quotient of the values 10 and 2 has no computed value, as at every
nonzero divisor.

`false and 1 div 0 = 1` has the table below, with the outcome of each
row in the empty assignment. The quotient's row 2 has the error
`error(zero-divisor)`, and so has the comparison's row 3, whose first
operand has it. The row 5 of `and` is false: its first operand decides
it.

| Row | Layer | Outcome |
| --- | --- | --- |
| 0 | `1` | 1 |
| 1 | `0` | 0 |
| 2 | `row 0 div row 1` | `error(zero-divisor)` |
| 3 | `row 2 = row 0` | `error(zero-divisor)` |
| 4 | `false` | false |
| 5 | `row 4 and row 3` | false |

Let `double` be the function of one integer parameter n whose body is
`n + n`; its table `DOUBLE_ROWS` has the two rows `#0` and
`row 0 + row 0`. The call `double(2)` has the table `CALL_ROWS`, whose
rows are `2` and `double(row 0)`. With the empty call record the call
has no outcome. The record `DOUBLED` lists `double` at 2 with the
outcome 4; with it the call has the value 4. `DOUBLED` is justified in
the program that declares `double`, and the record that lists the
outcome 5 is not.

An operand's error passes to a product, to a quotient and a remainder
at a nonzero divisor, and to a call that the record does not list. The
table `ERROR_ROWS` has the rows `1`, `0`, `row 0 div row 1`,
`row 2 * row 0`, `double(row 2)`, `row 2 div row 0` and
`row 2 % row 0`. With the empty call record the product's row 3, the
call's row 4, the quotient's row 5 and the remainder's row 6 all have
`error(zero-divisor)`, the outcome of row 2.

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

pub const QUOTIENT_ROWS: Snoc<Row> := Extend(
    Extend(
        four(
            typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
            typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer),
            typed(CoreF::Binary(BinaryOp::Div, 0, 1), Empty, Ty::Integer),
            typed(CoreF::Binary(BinaryOp::Eq, 2, 0), Empty, Ty::Boolean)
        ),
        typed(CoreF::BooleanLiteral(false), Empty, Ty::Boolean)
    ),
    typed(CoreF::Binary(BinaryOp::And, 4, 3), Empty, Ty::Boolean)
)

pub const DOUBLE: ItemId := ["M", "double"]

pub const DOUBLE_ROWS: Snoc<Row> := Extend(
    one(typed(CoreF::Local(0), one(Ty::Integer), Ty::Integer)),
    typed(
        CoreF::Binary(BinaryOp::Add, 0, 0),
        one(Ty::Integer),
        Ty::Integer
    )
)

pub const CALL_ROWS: Snoc<Row> := Extend(
    one(typed(CoreF::IntegerLiteral(2), Empty, Ty::Integer)),
    typed(CoreF::Call(DOUBLE, one(0)), Empty, Ty::Integer)
)

pub const ERROR_ROWS: Snoc<Row> := Extend(
    Extend(
        Extend(
            four(
                typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
                typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer),
                typed(CoreF::Binary(BinaryOp::Div, 0, 1), Empty, Ty::Integer),
                typed(CoreF::Binary(BinaryOp::Mul, 2, 0), Empty, Ty::Integer)
            ),
            typed(CoreF::Call(DOUBLE, one(2)), Empty, Ty::Integer)
        ),
        typed(CoreF::Binary(BinaryOp::Div, 2, 0), Empty, Ty::Integer)
    ),
    typed(CoreF::Binary(BinaryOp::Rem, 2, 0), Empty, Ty::Integer)
)

pub fn doubled(result: Int): Snoc<Call> := one(
    Call {
        callee := DOUBLE,
        arguments := one(Value::Integer(2)),
        outcome := Outcome::Value(Value::Integer(result)),
    }
)

pub const DOUBLED: Snoc<Call> := doubled(4)

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc evaluation_examples(): (holds?) {
    ensure output: holds?
    ensure bound: eval(LET_ROWS, 4, Empty) = Some(Value::Integer(8))
    ensure unbound: outcome(Empty, LET_ROWS, 3, Empty) = None
    ensure uncomputed: operator_outcome(BinaryOp::Div, Value::Integer(10), Value::Integer(2)) = None
    ensure zero_divisor: outcome(Empty, QUOTIENT_ROWS, 2, Empty)
        = Some(Outcome::Error(ErrorKind::ZeroDivisor))
    ensure propagated: outcome(Empty, QUOTIENT_ROWS, 3, Empty)
        = Some(Outcome::Error(ErrorKind::ZeroDivisor))
    ensure decided: eval(QUOTIENT_ROWS, 5, Empty) = Some(Value::Boolean(false))
    ensure uncalled: outcome(Empty, CALL_ROWS, 1, Empty) = None
    ensure product_propagated: outcome(Empty, ERROR_ROWS, 3, Empty)
        = Some(Outcome::Error(ErrorKind::ZeroDivisor))
    ensure call_propagated: outcome(Empty, ERROR_ROWS, 4, Empty)
        = Some(Outcome::Error(ErrorKind::ZeroDivisor))
    ensure quotient_propagated: outcome(Empty, ERROR_ROWS, 5, Empty)
        = Some(Outcome::Error(ErrorKind::ZeroDivisor))
    ensure remainder_propagated: outcome(Empty, ERROR_ROWS, 6, Empty)
        = Some(Outcome::Error(ErrorKind::ZeroDivisor))
    ensure called: outcome(DOUBLED, CALL_ROWS, 1, Empty) = Some(Outcome::Value(Value::Integer(4)))
    ensure justified: justified?(one(Decl::Function(DOUBLE, DOUBLE_ROWS)), DOUBLED)
    ensure unjustified: not justified?(one(Decl::Function(DOUBLE, DOUBLE_ROWS)), doubled(5))
}
```

## Properties

The properties of this section are open: none is stated in Fren or proved.

r[dynamics.theorem.determinism]
A configuration takes at most one step. A configuration that is not a
value decomposes in exactly one way into an evaluation context E and a
configuration m that is not a value and whose evaluated children are all
values, and m has at most one [reduction](#r-dynamics.step.reductions).
For a match this is because
[selection](#r-dynamics.match.selection) gives the first arm written for
the scrutinee's constructor, which is one arm or none, whether or not the
arms are distinct. Every derivation of a step of `E[m]` ends in that reduction: the
context rules, applied through E or through the contexts that compose to
E, derive the same step. So a run from a configuration is unique, and an
evaluation has exactly one of the three results, or it reaches a stuck
configuration.

r[dynamics.theorem.progress]
In a well-typed program, a configuration that has a
type is a value or takes a step, to a configuration or to an error state
of one of the
[two kinds](#r-dynamics.error.kinds). It is not stuck.

r[dynamics.theorem.preservation]
In a well-typed program, a step keeps the type: if
`P ⊢ m : τ` and `P ⊢ m → m′`, then `P ⊢ m′ : τ`. The initial
configuration of an expression of type τ, at an
assignment of its context, has the type τ.

r[dynamics.theorem.type-safety]
Type safety is [progress](#r-dynamics.theorem.progress) and
[preservation](#r-dynamics.theorem.preservation) together. In a
well-typed program, a well-typed expression of type τ, at an assignment
of its context, ends in a valid
value of type τ, or ends in an error of
one of the two kinds, or [diverges](#r-dynamics.divergence). It never
reaches a stuck configuration. The theorem does not say that evaluation
ends, and it needs neither definedness nor termination. None of the
three needs distinct arms: every arm of a well-typed match has the
match's type, whichever arm selection takes. No theorem of this chapter
asks for them.

r[dynamics.theorem.big-step]
The derived judgment agrees with the runs that end:
`P ⊢ ⟨e, ρ⟩ ⇓ r` holds exactly when `P ⊢ ⟨e, ρ⟩ →* r`, for a value or
an error state r.

r[dynamics.theorem.adequacy]
Let e be an expression that is defined under hypotheses Φ,
[in its declaration or as an expression written in none](StaticSemantics.md#r-statics.entailment),
and let every
function that e or Φ mentions
[have a denotation](DenotationalSemantics.md#r-denotation.domain). At an
assignment ρ that makes each hypothesis of Φ true, e ends in a value, and
that value is its denotation: `P ⊢ ⟨e, ρ⟩ →* ⟦e⟧ρ`, and so
`P ⊢ ⟨e, ρ⟩ ⇓ ⟦e⟧ρ`. It does not end in an error and it does not
diverge. A function that has a denotation, called at an argument tuple
that meets its precondition, ends in its denotation there. The theorem
asks nothing of a declaration that e and Φ do not depend on: such a
declaration may be unverified, and its assumptions may be false.

r[dynamics.theorem.total-correctness]
A function that
[has a denotation](DenotationalSemantics.md#r-denotation.domain) is
totally correct. Let v̄ be a tuple of values of its parameters' types at
which its precondition is true. Then the call of f at v̄ ends in a value
u, and the postcondition is true at v̄ and u. The call does not end in an
error and it does not diverge. This is
[adequacy](#r-dynamics.theorem.adequacy) with
[the contract theorem](DenotationalSemantics.md#r-denotation.theorem.contract).
The precondition and the postcondition have truth values there: they
are conditions of f's declaration that the
[call relation](StaticSemantics.md#r-statics.call-order.relation) reads,
so f depends on the functions that they mention and on every function
that those reach, and each of them has a denotation too. The theorem is not
stated of a function whose declaration is verified while a declaration
that it depends on is not.

r[dynamics.theorem.termination]
The call of a function that
[has a denotation](DenotationalSemantics.md#r-denotation.domain), at an
argument tuple that meets its precondition, ends: this is the part
of [adequacy](#r-dynamics.theorem.adequacy) that excludes divergence, and
it has adequacy's conditions. Of these it uses only that the function
passes the termination check hereditarily, by the
[soundness of the check](StaticSemantics.md#r-statics.property.termination). The termination check of the function's
own declaration does not give it. A function whose body is a call of a
function that has opted out of the check, and that does not reach it, is
in no recursive group and, where its own declaration has not opted out,
[passes the check](StaticSemantics.md#r-statics.termination), and its
call diverges where the callee's does. Nor does
[passing the check hereditarily](StaticSemantics.md#r-statics.termination) alone
give a value: the call may end in an error where a declaration is not
defined or an assumption is false. Without the check the theorem fails.
A well-typed function whose body is a call of itself at its own
parameters is
[defined and meets its contract](StaticSemantics.md#r-statics.examples.recursion),
and it diverges at every argument.

r[dynamics.theorem.partial-correctness]
A function need not pass the termination check to be partially
correct. Let f be a function of a well-typed program,
and let the declaration of f and of every function that f depends on be
[defined](StaticSemantics.md#r-statics.declaration.defined) and
[meet its contract](StaticSemantics.md#r-statics.contract.meets), with
[true assumptions](DenotationalSemantics.md#r-denotation.truth). Let v̄
be a tuple of values of f's parameters' types at which the precondition
of f is true. Then the call of f at v̄ reaches no error state, and if it
ends in a value u, the postcondition of f is true at v̄ and u. The call
may diverge, and the theorem says nothing more of one that does. The
conditions have truth values where the theorem reads them. The
declarations of f and of the functions that f depends on are defined, so
[each function that one of their contracts or assumptions mentions passes the termination check hereditarily](StaticSemantics.md#r-statics.condition.terminating).
By the theorem's own conditions such a function and every function that
it reaches are also defined and meet their contracts, with true
assumptions, so
[each has a denotation](StaticSemantics.md#r-statics.property.conditions).
The theorem needs all of these conditions and not the termination check
of the mentioned functions alone.

r[dynamics.theorem.table-agreement]
Let P be a [well-typed](Types.md#r-types.program.typing) program, let C
be a call record that is [justified](#r-dynamics.table.calls) in P, let
the table t be a derivation of `Γ ⊢ e : τ` in P, and let ρ be an
assignment of Γ: a sequence of valid values of the types of Γ. Where
the [table evaluator](#the-table-evaluator) gives the table's last row
an outcome r at ρ with the record C, a value or an error, the
expression e has that outcome: `P ⊢ ⟨e, ρ⟩ →* r`. The same holds of
each earlier row i, with the expression eᵢ, the context Γᵢ and the type
τᵢ that the row derives, at every assignment of Γᵢ. So where the
evaluator gives a value, e does not diverge and does not end in an
error, and where it gives an error, e ends in the error of that kind.
The converse does not hold: the evaluator gives no outcome to a
[product, or to a quotient or a remainder at a nonzero divisor](#r-dynamics.table.differences),
whose operands have values, or to a call whose arguments have values
and which C does not list at them.

The premises are needed. Loading is defined only for a well-typed
expression at an assignment of its context, and the evaluator also
gives outcomes to rows of a table that is no derivation. A record that
is not justified may list any outcome for a call. The empty record is
justified in every program, and with it the theorem is about
[`eval`](#r-expressions.meaning.evaluation), which is what
[verification](PropertiesAndChecks.md#r-verification.validity.uncomputed)
reads. The theorem does not ask for
[distinct arms](StaticSemantics.md#r-statics.match.distinct): the
evaluator and the step relation both take the first arm written for
the scrutinee's constructor. It asks for no result of the
[termination check](StaticSemantics.md#r-statics.termination) either:
by induction on a justified record, each call that it lists at valid
values of its callee's parameter types has a finite run to the listed
outcome, since the evaluation of the callee's body reads only calls
listed earlier. The induction is over those entries only: `justified?`
does not ask that an entry's arguments be of the callee's parameter
types or of their number, loading is not defined for an entry where
they are not, and a table that is a derivation, at an assignment of its
context, reads only entries where they are.

The theorem is open. Its parts that are proved in Lean are local: the
[operator results](#r-expressions.meaning.values) are those of the
operator rules, and the evaluator's
[selection](Patterns.md#r-patterns.matching.dynamics) is the step
relation's.

r[dynamics.theorem.implementation]
An implementation may evaluate in another order, leave an unused let's
value unevaluated, evaluate in one pass and not by steps, omit a
check which verification has discharged, or give no value: it may
decline a program and may stop at a bound of its own. Where it gives a
value, that value agrees with this chapter under the premises of
[adequacy](#r-dynamics.theorem.adequacy), with the typing premises of
[table agreement](#r-dynamics.theorem.table-agreement). Let P be a
well-typed program, let e be an expression with `Γ ⊢ e : τ` in P that
is defined under hypotheses Φ, let every function that e or Φ mentions
have a denotation, and let ρ be an assignment of Γ that makes each
hypothesis of Φ true. Then every value in which the implementation, run
on e at ρ, ends is the value v with `P ⊢ ⟨e, ρ⟩ →* v`, which is `⟦e⟧ρ`.
The property does not say that the implementation ends in a value.
Outside these premises it says nothing: there an implementation may give
a value where this chapter gives an error or a divergence, since a
skipped operand or an omitted check may be the one that errs. The
property is open. For the compiler's evaluator, the
[evaluator chapter](../Compiler/Evaluator.md#differences-from-the-step-relation)
lists how it differs from the step relation. Under these premises its
one-pass walk, its lazy let and its single undefined outcome change no
value that it gives. Its fourth difference is why the property is
conditional: that evaluator gives a value only for a program that it
admits, which has no recursion, and only within its depth bound, and
these premises ensure neither.
