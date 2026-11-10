# Denotational semantics

The denotational semantics gives each verified function, and each defined
expression over verified functions, a value, as a set-theoretic function
of the values of its free locals. It is defined only for verified Core,
[stratum by stratum](StaticSemantics.md#r-statics.stratification): a
function has a denotation once it and the functions it reaches are
verified. It therefore has no undefined result and no error value, its
intended meaning has no case for a zero divisor, and it has no order of
evaluation. The
[dynamic semantics](DynamicSemantics.md) is defined for every well-typed
program, and agrees with this chapter on the verified ones.

This chapter defines values and the meanings of the operators. The
equations of the denotation and its theorems are open: each is listed below
under its identifier with what it will state.

## Overview

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `Σ ⊢ v ∈ ⟦τ⟧` | v is a value of type τ | `value_type`, `value_valid?` |
| `Σ ⊢ ρ ∈ ⟦Γ⟧` | ρ assigns a value of its type to each level of Γ | open |
| `⟦op⟧(v) = w`, `⟦op⟧(v₁, v₂) = w` | the operator op has result w | `unary_meaning?`, `binary_meaning?`; for `*`, `div` and `%` the relation is looser than the judgment |
| `⟦e⟧ρ = v` | the defined expression e over verified functions denotes v at ρ | open |
| `⟦f⟧(v₁, …, vₙ) = v` | the verified function f maps the argument tuple to v | open |
| `ρ ⊨ φ` | the Boolean expression φ is true at ρ | open |
| `⊨ φ` | the expectation φ is true | open |

```text
  v ::= true | false                   Booleans
      | n                              mathematical integers
      | c                              a constructor of a nominal enum

  ρ ::= ·  |  ρ, v                     assignments, by de Bruijn level

  ⟦e⟧ρ      is defined when  Σ; Γ; Φ ⊢ e def,  Σ ⊢ ρ ∈ ⟦Γ⟧  and  ρ ⊨ Φ,
            and every function that e reaches is verified
  ⟦f⟧(v̄)    is defined when  Σ ⊢ f verified  and  v̄ ⊨ P,  f's precondition
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
level of Γ, oldest first, each a value of that level's type. This rule is
open: [Definedness and verification](PropertiesAndChecks.md#r-verification.validity.assignment)
states it for the context of a table's row.

## Domain

r[denotation.domain]
`⟦e⟧ρ` is defined exactly when e is
[defined](StaticSemantics.md#definedness) under some hypotheses Φ, every
function that e calls, and every function those reach, is verified, ρ is
an assignment of e's context, and ρ makes every hypothesis of Φ true.
`⟦f⟧(v̄)` is defined exactly when f is verified and v̄ meets f's
precondition; a verified declaration has verified callees, so every
function that f reaches is verified too. The domain does not wait for the
whole program: the functions of a
[stratum](StaticSemantics.md#r-statics.stratification) have denotations as
soon as that stratum is verified, and the judgments of later declarations
read them. The judgments of a declaration read no denotation of its own
recursive group, so the domain is not defined in terms of itself. Nothing
else has a denotation: this chapter gives no meaning to an ill-typed
expression, to an expression that is not defined, to a function that is
not verified, or to a defined expression at an assignment that fails its
hypotheses. This rule is open.

## Operators

r[expressions.meaning.operators] spec::denotation::{unary_meaning?, integer_meaning?, boolean_meaning?, binary_meaning?}
Within their domains, arithmetic operators have their mathematical meanings.
Division and remainder are Euclidean: the remainder is nonnegative and
strictly less than the absolute divisor, and `n = (n div d) * d + n % d`.
Comparisons use integer order; Boolean operators use their truth tables;
equality compares values of one type, including canonical nominal identity.
Unary minus negates an integer and `not` complements a Boolean.
`binary_meaning?` and `unary_meaning?` state the result of every other
operator exactly. For `*`, `div` and `%` they state only the result's
sort, and the remainder's range at a nonzero divisor; the equations above
give the values, and [the rule below](#r-denotation.operators.arithmetic)
says what the relation leaves out.

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
The denotation of `*`, `div` and `%` is a function on the verified domain:
`*` denotes the product at every pair of integers, and `div` and `%` denote
the Euclidean quotient and remainder at every pair whose divisor is not
zero. A zero divisor is outside the domain, and no defined expression
reaches one. This rule is open, and `binary_meaning?` does not state it.
The relation is a looser approximation: it accepts every integer as the
result of `*` and of `div`, at a zero divisor too; it accepts every integer
as the remainder by zero; and at a nonzero divisor it bounds the
remainder's range without fixing its value. The rule will replace those
three cases by the product and the equation `n = (n div d) * d + n % d`,
and will relate no result to a zero divisor.

## Expressions

r[expressions.meaning.context]
An interpretation assigns meanings to canonical items. A local assignment
lists values by level, oldest first, in the exact typing context. Literals
denote the values they carry; a local denotes the value at its level; a
constructor denotes its nominal value. A named call substitutes its
positional arguments into its function body's parameter context, without
inheriting the caller's locals. A let interprets its value in the incoming
context and its body with that value appended as the newest level. An if
denotes its selected branch; a match denotes the body for its constructor, in the incoming context.

r[denotation.expression]
`⟦e⟧ρ` is defined by one equation for each Core form, by recursion on e.
The equations state [the paragraph above](#r-expressions.meaning.context):
an operator's value is its [meaning](#r-expressions.meaning.operators) at
its operands' denotations, and a call's value is its callee's
[denotation](#r-denotation.function) at its arguments' denotations. These
equations are open.

r[expressions.value.denotation]
A well-typed expression of type τ, in a verified program and under values
of its context's types, whose partial operations are within their domains,
denotes a value of type τ. This is open. With
[adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy) it gives
[type safety](Types.md#r-types.safety) on verified programs.

## Functions and programs

r[denotation.function]
A verified function f denotes the function that maps each argument tuple
v̄ meeting f's precondition to the denotation of f's body at that tuple. It
is not defined at any other tuple. The equation is a definition by
recursion on
[call order](StaticSemantics.md#r-statics.call-order.well-founded): the
body at v̄ reads the denotations of the functions of earlier strata, and
those of f's own recursive group only at call instances that precede
`(f, v̄)`. For a function that is not recursive only the first kind
occurs. Call order is well founded, so the equations of a recursive group
have exactly one solution on the tuples that meet the preconditions. This
rule is open.

r[denotation.program]
The denotation of a verified program gives each of its functions its
denotation, [stratum by stratum](StaticSemantics.md#r-statics.stratification).
The denotation of a function does not change when later declarations are
added or verified. This rule is open.

## Truth

r[denotation.truth]
A Boolean expression φ is true at ρ, `ρ ⊨ φ`, when `⟦φ⟧ρ` is the value
true. An expectation is true, `⊨ φ`, when φ is true at every assignment of
its context that makes the program's assumptions true. The truth of an
expectation is a fact about the program and depends on no solver; the
verdict that a check reports for it belongs to the
[tooling part](../Tooling/index.md). This rule is open.

## Properties

The properties of this section are open: none is stated in Fren or proved.

r[denotation.theorem.unique]
The denotation is a function: where `⟦e⟧ρ` is defined, the equations
determine exactly one value. In particular it does not depend on the
hypotheses under which e is defined.

r[denotation.theorem.coincidence]
`⟦e⟧ρ` depends only on the values that ρ gives to e's free local slots and
on the denotations of the functions that e
[mentions](StaticSemantics.md#r-expressions.mentions.closure).

r[denotation.theorem.contract]
Every verified function has a denotation at every argument tuple that
meets its precondition, and its postcondition is true of that tuple and
the denotation's value there. The proof is by induction on call order,
over call instances: at `(f, v̄)` the postconditions of the preceding
instances of f's recursive group hold by the induction hypothesis, which
is what the verification of f's declaration
[assumed of them](StaticSemantics.md#r-statics.stratification).

r[denotation.theorem.models]
A model that a solver gives for a verified program's conditions agrees
with the denotation. The [SMT chapter](../Compiler/Smt.md) states this of
its encoding, including the values that the encoding gives a division by
zero, which this chapter does not define.

## Examples

With `Γ = ·, Boolean, Integer`, local 0 denotes the Boolean, and local 1 the
integer. In `let x := y + 1 in x + y`, with incoming context `·, y: Integer`,
the value uses level 0 for `y`; the body uses level 0 for `y` and level 1
for `x`. These are the same contexts required by `rule?`.
