# Denotational semantics

The denotational semantics gives each function whose declaration is
[verified](StaticSemantics.md#r-statics.program.verified), with the
declarations that it depends on, and each defined expression over such
functions, a value, as a set-theoretic function of the values of its free
locals. It gives a meaning to verified Core only. A verified declaration
has passed the termination check, so no denotation has to account for an
evaluation that does not end; a function that is defined and meets its
contract without that check has no denotation. The chapter proceeds
[stratum by stratum](StaticSemantics.md#r-statics.stratification). A
denotation is total on its domain: it has no undefined result, no error
value and no case for a zero divisor, and it has no order of evaluation.
The [dynamic semantics](DynamicSemantics.md) evaluates every well-typed
program with distinct arms, and
[adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy) states where
the two agree.

A rule whose `r[...]` line names no Fren definition is stated in prose
only.

## Overview

| Judgment | Meaning | Rule | Fren |
| --- | --- | --- | --- |
| `Σ ⊢ v ∈ ⟦τ⟧` | v is a value of type τ | [values of a type](#r-denotation.type) | `value_type`, `value_valid?` |
| `Σ ⊢ ρ ∈ ⟦Γ⟧` | ρ assigns a value of its type to each level of Γ | [assignments](#r-denotation.assignment) | — |
| `⟦op⟧(v) = w`, `⟦op⟧(v₁, v₂) = w` | the operator op has the result w | [operators](#r-expressions.meaning.operators), [arithmetic](#r-denotation.operators.arithmetic) | `unary_meaning?`, `binary_meaning?` |
| `I` | an interpretation gives each function a function on values | [interpretation](#r-expressions.meaning.context) | — |
| `⟦e⟧ᴵρ = v` | e has the value v at ρ under the interpretation I | [expressions](#r-denotation.expression) | — |
| `⟦e⟧ρ = v` | e denotes v at ρ | [expressions](#r-denotation.expression), [domain](#r-denotation.domain) | — |
| `⟦f⟧(v₁, …, vₙ) = v` | the function f maps the argument tuple to v | [functions](#r-denotation.function) | — |
| `ρ ⊨ φ` | the Boolean expression φ is true at ρ | [truth](#r-denotation.truth) | — |
| `⊨ A` | the assumption A is true | [truth](#r-denotation.truth) | — |
| `⊨ ψ` | the expectation ψ is true | [truth](#r-denotation.truth) | — |

```text
  v ::= true | false                   Booleans
      | n                              mathematical integers
      | c                              a constructor of a nominal enum

  ρ ::= ·  |  ρ, v                     assignments, by de Bruijn level
```

The denotation of a program is the family of its functions' denotations.
The judgments carry it implicitly, as they carry Σ.

## Values

r[expressions.value.type] spec::denotation::{Value, value_type, value_valid?}
A value is a Boolean, an integer, or a nominal value that names an actual
constructor of its canonical enum owner; `value_type` gives its type.

```fren
pub mod spec
pub mod spec::denotation

use spec::names::{ItemId, ItemKind, Symb, Ty, entry}

use spec::surface::{BinaryOp, UnaryOp}

pub enum Value { Boolean(Bool), Integer(Int), Nominal(ItemId, ItemId) }

pub fn value_type(value: Value): Ty := match value {
    Value::Boolean(_) => Ty::Boolean,
    Value::Integer(_) => Ty::Integer,
    Value::Nominal(owner, _) => Ty::Nominal(owner),
}

pub fn value_valid?(symb: Symb, value: Value) := match value {
    Value::Nominal(owner, item) => entry(symb, item) = Option::Some(ItemKind::Constructor(owner)),
    _ => true,
}
```

r[denotation.type]
The values of type τ, `Σ ⊢ v ∈ ⟦τ⟧`, are the valid values whose
`value_type` is τ: the two Booleans for `Bool`, every integer for `Int`,
and the constructors of the enum a for `Nominal(a)`.

r[denotation.assignment]
An assignment ρ of a context Γ, `Σ ⊢ ρ ∈ ⟦Γ⟧`, lists one value for each
level of Γ, oldest first, each a value of that level's type.
[Definedness and verification](PropertiesAndChecks.md#r-verification.validity.assignment)
states the same condition in Fren for the context of a table's row.

r[denotation.leaf]
Three forms have a value that depends on no other expression, in every
well-typed program. A Boolean or integer literal has the value that it
carries. A constructor c of the enum a has the nominal value of c with
owner a. A local has, at an assignment ρ, the value that ρ lists at the
local's level. Both this chapter and the
[dynamic semantics](DynamicSemantics.md#r-dynamics.configuration.loading) give
these forms these values.

## Operators

r[expressions.meaning.operators] spec::denotation::{unary_meaning?, integer_meaning?, boolean_meaning?, binary_meaning?}
Within their domains, arithmetic operators have their mathematical meanings.
Division and remainder are Euclidean: the remainder is nonnegative and
strictly less than the absolute divisor, and `n = (n div d) * d + n % d`.
Comparisons use integer order; Boolean operators use their truth tables;
equality compares values of one type, including canonical nominal identity.
Unary minus negates an integer and `not` complements a Boolean.
`unary_meaning?` and `binary_meaning?` fix the result of every operator
except `*`, `div` and `%`; of those three they fix the result's sort and,
at a nonzero divisor, the remainder's range.

```fren
pub fn unary_meaning?(op: UnaryOp, operand: Value, result: Value) := match op, operand {
    UnaryOp::Neg, Value::Integer(n) => result = Value::Integer(-n),
    UnaryOp::Not, Value::Boolean(b?) => result = Value::Boolean(not b?),
    _, _ => false,
}

pub fn integer_meaning?(op: BinaryOp, a: Int, b: Int, result: Value) := match op {
    BinaryOp::Add => result = Value::Integer(a + b),
    BinaryOp::Sub => result = Value::Integer(a - b),
    BinaryOp::Mul | BinaryOp::Div => result is Value::Integer(_),
    BinaryOp::Rem => match result {
        Value::Integer(r) => b = 0 or 0 <= r < b.abs,
        _ => false,
    },
    BinaryOp::Lt => result = Value::Boolean(a < b),
    BinaryOp::Le => result = Value::Boolean(a <= b),
    BinaryOp::Gt => result = Value::Boolean(a > b),
    BinaryOp::Ge => result = Value::Boolean(a >= b),
    BinaryOp::Eq => result = Value::Boolean(a = b),
    BinaryOp::Ne => result = Value::Boolean(a != b),
    _ => false,
}

pub fn boolean_meaning?(op: BinaryOp, p?, q?, result: Value) := match op {
    BinaryOp::And => result = Value::Boolean(p? and q?),
    BinaryOp::Or => result = Value::Boolean(p? or q?),
    BinaryOp::Iff | BinaryOp::Eq => result = Value::Boolean(p? iff q?),
    BinaryOp::Ne => result = Value::Boolean(not (p? iff q?)),
    _ => false,
}

pub fn binary_meaning?(op: BinaryOp, left: Value, right: Value, result: Value) :=
    match left, right {
        Value::Integer(a), Value::Integer(b) => integer_meaning?(op, a, b, result),
        Value::Boolean(p?), Value::Boolean(q?) => boolean_meaning?(op, p?, q?, result),
        Value::Nominal(_, _), Value::Nominal(_, _) => match op {
            BinaryOp::Eq => result = Value::Boolean(left = right),
            BinaryOp::Ne => result = Value::Boolean(left != right),
            _ => false,
        },
        _, _ => false,
    }
```

r[denotation.operators.arithmetic]
`*` denotes the product at every pair of integers. `div` and `%` denote
the Euclidean quotient and remainder, which the equation
`n = (n div d) * d + n % d` and the remainder's range determine, at every
pair of integers whose divisor is not zero. They denote nothing at a zero
divisor.

## Expressions

r[expressions.meaning.context]
An interpretation assigns meanings to canonical items: to each function, a
function from value tuples of its parameters' types to values of its
result's type, which need not have a value at every tuple. A local
assignment lists values by level, oldest first, in the exact typing
context. Literals, locals and constructors have their
[leaf values](#r-denotation.leaf). A named call applies its callee's
meaning to its positional arguments, and its callee's body is read in the
parameter context, without inheriting the caller's locals. A let
interprets its value in the incoming context and its body with that value
appended as the newest level. An if denotes its selected branch; a match
denotes, in the incoming context, the body of the arm whose constructor
is its scrutinee's constructor. The arms of a match are
[distinct](StaticSemantics.md#r-statics.match.distinct), so there is at
most one such arm.

r[denotation.expression]
`⟦e⟧ᴵρ`, the value of e at ρ under an interpretation I, is given by one
equation for each Core form, by recursion on e. The equations state
[the paragraph above](#r-expressions.meaning.context): an operator's value
is its [meaning](#r-expressions.meaning.operators) at its operands'
values, and a call's value is the value that I gives the callee at the
arguments' values. `⟦e⟧ᴵρ` has a value only where every part that its
equation reads has one. The equation of a conditional reads the condition
and the selected branch, and that of a match the scrutinee and the
selected arm. The equation of `and` reads its second operand only where
the first is true, and that of `or` only where the first is false. Every
other equation reads all the children of its form. A division or
remainder has no value at a zero divisor, a match has none without an arm
for its scrutinee's constructor, and a call has none where I gives the
callee no value. The *denotation* `⟦e⟧ρ` is `⟦e⟧ᴵρ` for the
interpretation that gives each function its
[denotation](#r-denotation.function).

## Domain

r[denotation.domain]
A function f *has a denotation* when the declaration of f and the
declaration of every function that f
[depends on](StaticSemantics.md#r-statics.call-order.relation) are
[verified](StaticSemantics.md#r-statics.program.verified), and the
assumptions of those declarations are [true](#r-denotation.truth). The
definition is by recursion on the
[strata](StaticSemantics.md#r-statics.stratification): the truth of an
assumption reads the denotations of functions of earlier strata only.
`⟦f⟧(v̄)` exists exactly when f has a denotation and v̄ meets f's
precondition. `⟦e⟧ρ` is asked for exactly when e is
[defined](StaticSemantics.md#r-statics.definedness.rules) under some
hypotheses Φ, every function that e or Φ mentions has a denotation, ρ is
an assignment of e's context, and ρ makes every hypothesis of Φ true.
The equations then need a callee's denotation only at the argument
tuples of the calls that they [read](#r-denotation.expression) at ρ, and
a callee need have a denotation at no other tuple: a call in a branch
that is not selected is not read. A declaration that f does not depend
on takes no denotation away from f: it may be unverified, and its
assumptions may be false. This chapter gives no meaning to an ill-typed
expression, to an expression that is not defined, to a function that has
no denotation, or to a defined expression at an assignment that fails
its hypotheses.

## Functions and programs

r[denotation.function]
A function f denotes the function that maps each argument tuple v̄ of its
[domain](#r-denotation.domain) to the denotation of f's body at that
tuple. It has no value at any other tuple. The equation is a definition by
recursion on
[call order](StaticSemantics.md#r-statics.call-order.instances), with the
decreasing parameters under which f's group
[terminates](StaticSemantics.md#r-statics.termination).

r[denotation.program]
The denotation of a program gives each of its functions that
[has a denotation](#r-denotation.domain) its denotation,
[stratum by stratum](StaticSemantics.md#r-statics.stratification). In a
verified program whose assumptions are all true, every function has one.

## Truth

r[denotation.truth]
Under an interpretation I, a Boolean expression φ is *true* at ρ when
`⟦φ⟧ᴵρ` is the value true and *false* at ρ when it is the value false;
where `⟦φ⟧ᴵρ` has no value, φ is neither. φ is true at ρ, `ρ ⊨ φ`, when
`⟦φ⟧ρ` is the value true. A tuple v̄ *meets* the precondition of f when
the precondition is true at v̄. An assumption A of a function f is
*true*, `⊨ A`, when it is true at every argument tuple that meets f's
precondition. This is asked only where every function that A or the
precondition mentions [has a denotation](#r-denotation.domain); those
functions are of
[strata before f's](StaticSemantics.md#r-statics.condition.group), and
they [terminate hereditarily](StaticSemantics.md#r-statics.condition.terminating).
An assumption is a hypothesis
[only within its own declaration](StaticSemantics.md#r-statics.condition.scope),
and it is asked to be true only by a theorem about a function that
depends on its declaration's function, or about that function itself. No
theorem of these chapters asks that all the assumptions of a program be
true. The assumptions of an expectation declaration are hypotheses of its
expectations and are not asked to be true. An expectation ψ of a
declaration d is true, `⊨ ψ`, when ψ is true at every assignment of d's
parameters that makes true the
[hypotheses of d](StaticSemantics.md#r-statics.condition.scope); this is
asked only where every function that ψ or those hypotheses mention has a
denotation. The truth of an expectation is a fact about the program
and depends on no solver, and it is no part of being verified. The
verdict that a check reports for an expectation belongs to the
[tooling part](../Tooling/index.md).

## Properties

The properties of this section are open: none is stated in Fren or proved.

r[expressions.value.denotation]
A well-typed expression of type τ that is defined under hypotheses Φ,
where every function that it or Φ mentions
[has a denotation](#r-denotation.domain), has a denotation at every
assignment of its context that makes Φ true, and the denotation is a valid
value of type τ. No division or remainder that the denotation reads has a
zero divisor there, and every match that it reads has an arm for its
scrutinee's constructor.

r[denotation.theorem.unique]
The denotation is a function: where `⟦e⟧ρ` exists, the equations determine
exactly one value. In particular it does not depend on the hypotheses
under which e is defined.

r[denotation.theorem.well-defined]
The domain is not defined in terms of itself. Whether a declaration is
verified reads no denotation, and whether its assumptions are true reads
the denotations of earlier strata only, since
[no assumption or precondition mentions a function of its own group](StaticSemantics.md#r-statics.condition.group).
A verified group
[terminates](StaticSemantics.md#r-statics.termination), so at an
argument tuple of its domain the body reads the group's denotations only
at preceding call instances; call order is
[well founded](StaticSemantics.md#r-statics.property.call-order), so the
equations of the group have exactly one solution on the tuples of the
group's domains. Without the termination check the equations of a group
may have no solution or several, which is why this chapter gives such a
group no denotation.

r[denotation.theorem.extension]
The denotation of a function does not change when declarations of later
strata are added to the program.

r[denotation.theorem.coincidence]
`⟦e⟧ρ` depends only on the values that ρ gives to e's free local slots and
on the denotations of the functions that e
[mentions](StaticSemantics.md#r-expressions.mentions.closure).

r[denotation.theorem.contract]
Every function that [has a denotation](#r-denotation.domain) has a value
at every argument tuple that meets its precondition, and its
postcondition is true of that tuple and that value. The postcondition
has a truth value there, since the functions that it mentions are of
earlier strata and have denotations. The
proof is by induction on call order, over call instances. At `(f, v̄)`,
the denotations of the earlier strata, together with those of f's
recursive group restricted to the instances that precede `(f, v̄)`, form
an interpretation that is
[admissible](StaticSemantics.md#r-statics.entailment.admissible) for f's
declaration, which is what the entailments of that declaration range
over; termination gives the body's calls into the group their values
under it.

r[denotation.theorem.models]
A model that a solver gives for a verified program's conditions agrees
with the denotation. The [SMT chapter](../Compiler/Smt.md) states this of
its encoding, including the values that the encoding gives a division by
zero, to which this chapter gives none.

## Examples

r[denotation.examples.levels]
With `Γ = ·, Bool, Int`, local 0 denotes the Boolean, and local 1 the
integer. In `let x := y + 1 in x + y`, with the incoming context `·, Int`
for `y`, the value uses level 0 for `y`; the body uses level 0 for `y` and
level 1 for `x`. These are the contexts that the
[typing rule of a let](Types.md#r-types.expression.let) requires.
