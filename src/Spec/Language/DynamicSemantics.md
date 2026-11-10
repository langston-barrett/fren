# Dynamic semantics

The dynamic semantics evaluates an expression. It is operational and
small-step: a one-step relation rewrites a configuration, and an
evaluation is a run of steps. It is defined for every well-typed program,
whether or not the program is
[verified](StaticSemantics.md#r-statics.program.verified). A run has one
of three results: it ends in a value, it ends in an error state, or it
diverges. Evaluation contexts fix one order of evaluation. An operation
outside its domain steps to an error state, and never to an arbitrary
value. The [denotational semantics](DenotationalSemantics.md) is defined
for verified Core only; [adequacy](#r-dynamics.theorem.adequacy) states
that there a run ends in a value, which is the denotation.

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
| `op(v) = r`, `op(v₁, v₂) = r` | the operator op has the outcome r at the operand values | [operators](#r-dynamics.operators.total) | `unary_value` and `binary_value`, where they give a value |
| `P ⊢ ⟨e, ρ⟩ ⇓ r` | derived: e evaluates at ρ to the outcome r | [big-step evaluation](#r-dynamics.evaluation.rules) | — |
| `eval(t, i, ρ) = v` | row i of the table t has the value v at ρ | [the table evaluator](#r-expressions.meaning.evaluation) | `eval` |

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
The dynamic semantics is defined for every well-typed program. It reads
no contract, no hypothesis, no result of the termination check and no
solver's answer: a run depends only on the program, the expression and
the assignment. It evaluates the bodies of functions and never their
conditions, unless a condition is itself the expression being evaluated.

## Configurations

r[dynamics.configuration]
A *configuration* m is an expression in the course of its evaluation. It
has the forms of Core, with two differences. It has no local: every local
has been replaced by its value. The body of a let stays a Core expression
e, paired with the assignment ρ at which the let was loaded; it becomes a
configuration when the let's value is known. A *state* is a configuration
or an error state `error(k)`. An error state is not a configuration: no
context holds one, and no operator or call takes one as an operand.

r[dynamics.configuration.loading]
*Loading* gives the configuration `⟨e, ρ⟩` of an expression e, well typed
in a context Γ, at an assignment ρ of Γ. It is defined by recursion on e
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
A *reduction* is a step of a configuration whose evaluated children are
values. The reductions are these, and no others.

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
A match selects, for a scrutinee value that is the constructor c, the arm
whose constructor is c. When several arms have that constructor, it
selects the one written last. When none has it, the match selects no arm
and steps to `error(no-arm)`.

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
or not the callee
[terminates](StaticSemantics.md#r-statics.termination).

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

r[dynamics.truth]
A Boolean expression φ *evaluates to true* at ρ when
`P ⊢ ⟨φ, ρ⟩ →* true`, and to false likewise. The *assumptions of P hold
in evaluation* when, for every function declaration of P and every tuple
of values of its parameters' types at which each of its preconditions
evaluates to true, each of its assumptions evaluates to true.

## The table evaluator

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
the rows before it. A literal, a local and a constructor have their
[leaf values](DenotationalSemantics.md#r-denotation.leaf). An
operator row has the result of `unary_value` or `binary_value` at its
operands' values. A conditional has the value of the branch that its
condition selects, and a match the value of the arm that
[selection](#r-dynamics.match.selection) gives for its scrutinee's
constructor. A let row is evaluated in two steps: its value v in ρ, then
its body in the assignment that keeps the levels of the let's own context
and appends v. `eval(t, r, ρ)` is the value of row r.

A row has no value when a child that it needs has none, when a local is
not in ρ, when an operator has no result, when a match has no arm for
its scrutinee's constructor, or when it is a call. So a row that depends
on a product, a quotient, a remainder or a call has none, and the
evaluator has no error outcome. An operator row needs both operands'
values, `and` and `or` included, and a let needs its value's, whether or
not the result depends on them. A conditional needs only the selected
branch, and a match only the selected arm.

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

r[dynamics.table.differences]
The table evaluator is not the step relation, and it differs from it in
five ways. It computes a row's value in one pass over the rows before
it, and has no configurations, steps or runs. It has no error state: a
row that the step relation takes to an error has no value. It gives no
value to a call, a product, a quotient or a remainder, where the step
relation reduces each. It needs the second operand of `and` and of `or`
even where the first decides the result, so a row has no value when that
operand has none, where the step relation never evaluates it. It cannot
diverge.
[Where it gives a value](#r-dynamics.theorem.table-agreement), the step
relation gives the same one.

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
A configuration takes at most one step. A configuration that is not a
value decomposes in exactly one way into an evaluation context E and a
configuration m whose evaluated children are all values, and m has at
most one [reduction](#r-dynamics.step.reductions). Every derivation of a
step of `E[m]` ends in that reduction: the context rules, applied through
E or through the contexts that compose to E, derive the same step. So a run from a
configuration is unique, and an evaluation has exactly one of the three
results, or it reaches a stuck configuration.

r[dynamics.theorem.progress]
In a well-typed program, a configuration that has a type is a value or
takes a step, to a configuration or to an error state of one of the
[two kinds](#r-dynamics.error.kinds). It is not stuck.

r[dynamics.theorem.preservation]
In a well-typed program, a step keeps the type: if `P ⊢ m : τ` and
`P ⊢ m → m′`, then `P ⊢ m′ : τ`. The initial configuration of an
expression of type τ, at an assignment of its context, has the type τ.

r[dynamics.theorem.type-safety]
Type safety is [progress](#r-dynamics.theorem.progress) and
[preservation](#r-dynamics.theorem.preservation) together. In a
well-typed program, a well-typed expression of type τ, at an assignment
of its context, ends in a valid value of type τ, or ends in an error of
one of the two kinds, or [diverges](#r-dynamics.divergence). It never
reaches a stuck configuration. The theorem does not say that evaluation
ends, and it needs neither definedness nor termination.

r[dynamics.theorem.big-step]
The derived judgment agrees with the runs that end:
`P ⊢ ⟨e, ρ⟩ ⇓ r` holds exactly when `P ⊢ ⟨e, ρ⟩ →* r`, for a value or
an error state r.

r[dynamics.theorem.adequacy]
In a verified program whose
[assumptions hold](DenotationalSemantics.md#r-denotation.truth), an
expression that is defined under hypotheses which the assignment ρ makes
true ends in a value, and that value is its denotation:
`P ⊢ ⟨e, ρ⟩ →* ⟦e⟧ρ`, and so `P ⊢ ⟨e, ρ⟩ ⇓ ⟦e⟧ρ`. It does not end in an
error and it does not diverge. A function of such a program, called at
an argument tuple that meets its precondition, ends in its denotation
there.

r[dynamics.theorem.termination]
Evaluation ends where the termination check has passed: this is the part
of [adequacy](#r-dynamics.theorem.adequacy) that excludes divergence, and
it has adequacy's conditions. Without the check it fails. A well-typed
function whose body is a call of itself at its own parameters is
[defined and meets its contract](StaticSemantics.md#r-statics.examples.recursion),
and it diverges at every argument.

r[dynamics.theorem.partial-correctness]
A program that is well typed, is
[defined](StaticSemantics.md#r-statics.program.defined) and
[meets its contracts](StaticSemantics.md#r-statics.contract.meets) is
partially correct, whether or not it passes the termination check. Let
its [assumptions hold in evaluation](#r-dynamics.truth), and let f be one
of its functions and v̄ a tuple at which each precondition of f evaluates
to true. If the call of f at v̄ ends in a value u, then u meets the
postcondition: the postcondition does not evaluate to false at v̄ and u.
The theorem says nothing of a call that diverges. It does not say that
the call reaches no error state, and that is not claimed of a program
that has not passed the termination check: a condition may mention a
function that diverges, and then a precondition that has no value can be
entailed at a call whose callee's body divides by zero.

r[dynamics.theorem.table-agreement]
Where the [table evaluator](#the-table-evaluator) gives a row a value v
at ρ, the row's expression e has that outcome: `P ⊢ ⟨e, ρ⟩ →* v`.

r[dynamics.theorem.implementation]
An implementation that evaluates in another order, that leaves an unused
let's value unevaluated, that evaluates in one pass and not by steps, or
that omits a check which verification has discharged, agrees with this
chapter on verified programs whose assumptions hold, at the assignments
of [adequacy](#r-dynamics.theorem.adequacy). The
[evaluator chapter](../Compiler/Evaluator.md) states how the compiler's
evaluator differs from this chapter elsewhere.
