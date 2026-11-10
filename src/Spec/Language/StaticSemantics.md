# Static semantics

The static semantics of the Core is three judgments: typing, definedness
and contracts. A program that satisfies all three is *verified*.
[Resolution](NamesAndScope.md) produces the Core and its symbol environment,
and [Core typing](Types.md) defines the typing judgment. This chapter
defines which items an expression mentions and when a partial operation is
within its domain, and gives the forms of the definedness and contract
judgments. The [denotational semantics](DenotationalSemantics.md) gives a
meaning to verified programs only. The
[dynamic semantics](DynamicSemantics.md) evaluates every well-typed
program, verified or not.

The rules of definedness and of contracts are open: each is listed below
under its identifier with what it will state.
[Definedness and verification](PropertiesAndChecks.md) holds the present
statement of definedness, as obligations over derivation tables
([below](#material-that-other-chapters-hold)).

## Overview

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `Σ; Γ ⊢ e : τ` | e has type τ in Γ | [Core typing](Types.md)'s `derivation?` |
| `e ∋ a` | e mentions the item a | `direct_item?` for one layer; the closure is open |
| `Σ ⊢ f ≺ g` | f precedes g in call order | open |
| `Σ; Γ; Φ ⊨ φ` | every assignment of Γ that satisfies the hypotheses Φ satisfies φ | open |
| `Σ; Γ; Φ ⊢ e def` | under Φ, every partial operation and call written in e is within its domain | open; `integer_domain?` for one operator |
| `Σ ⊢ {P} f {Q}` | f has precondition P and postcondition Q | open |
| `Σ ⊢ d verified` | the declaration d is defined and meets its contract | open |
| `⊢ (Σ, ds) verified` | the program is verified | open |

```text
  Γ ::= ·  |  Γ, τ                     contexts, by de Bruijn level
  Φ ::= ·  |  Φ, φ                     hypotheses, outermost first
  P, Q, φ                              Core expressions of type Bool

  f : (x₁: τ₁, …, xₙ: τₙ) → τ          a signature of Σ
  P is typed in  ·, τ₁, …, τₙ          over the whole argument tuple
  Q is typed in  ·, τ₁, …, τₙ, τ       over the argument tuple and the result
```

Each name stands for a de Bruijn level: `x₁` is level 0, and in Q the
result is level n. A contract relates a function's arguments to its
result. It is not part of any type: a parameter's type, and the result's,
are the `Ty` of the signature whatever the contract says.

## Scope

r[statics.scope]
The static semantics is stated over the Core that
[resolution](NamesAndScope.md) produces: literals, locals, constructors,
named calls, unary and binary operators, lets, conditionals and constructor
matches, with the declarations of a program. It is declarative: a judgment
depends on the written form of an expression and never on an order of
evaluation. Whether an expectation is true is not a static judgment; the
[denotational semantics](DenotationalSemantics.md#r-denotation.truth) defines
it. What a solver's answer establishes, the evidence for a judgment and the
diagnostics that report a failure belong to the
[tooling part](../Tooling/index.md).

## Typing

r[statics.typing]
The typing judgment `Σ; Γ ⊢ e : τ` and its liftings to declarations and
programs are those of [Core typing](Types.md). Every other judgment of this
chapter is stated of well-typed expressions only.

## Mentioned items and call order

r[expressions.mentions.direct] spec::statics::{arm_mentions?, direct_item?}
An occurrence directly mentions its constructor, callee or match-pattern
items. A local mentions its resolved context slot, rather than an item with
the same written spelling.

```fren
pub mod spec
pub mod spec::statics

use spec::names::{ArmF, CoreF, ItemId}

use spec::surface::{BinaryOp, Snoc}

pub fn arm_mentions?<E>(arms: Snoc<ArmF<E>>, item: ItemId) := match arms {
    Snoc::Empty => false,
    Snoc::Extend(earlier, arm) => arm.constructor = item or arm_mentions?(earlier, item),
}

pub fn direct_item?<E>(form: CoreF<E>, item: ItemId) := match form {
    CoreF::Constructor(target) => item = target,
    CoreF::Call(target, _) => item = target,
    CoreF::Match(_, arms) => arm_mentions?(arms, item),
    _ => false,
}
```

r[expressions.mentions.closure]
An expression's mentioned items are the union of its direct items and those
of every written child. Its free local slots are collected through every
child, removing the let's own level when leaving a let body; other levels
are unchanged. A let's value has no additional binder. Match patterns add none.
Names in an unselected branch or unused definition still count. This
structural closure uses the same children and binding depths as typing;
it is independent of a particular evaluation trace.

r[statics.call-order.relation]
A function g *precedes* a function f in call order, `Σ ⊢ g ≺ f`, when f's
body or contract mentions g, or mentions a function that g precedes. This
rule is open: the relation is not yet stated in Fren, and the closure of
[mentioned items](#r-expressions.mentions.closure) that it needs is prose.

r[statics.call-order.well-founded]
In a verified program no function precedes itself, so call order is a
well-founded order on the program's functions. The judgments of this
chapter and the denotation of a function are defined by induction on it.
This rule is open. It admits no recursion; the rule for structural
recursion, which lets a function precede itself at structurally smaller
arguments, is open too.

## Definedness

Typing does not make an expression defined: `n div d` is well typed
whatever the value of `d`. An expression is *defined* under hypotheses when
every partial operation written in it is within its domain and every call
written in it meets its callee's precondition.

r[expressions.domain.integer] spec::statics::integer_domain?
Division and remainder require a nonzero divisor. Typing alone does not
establish this condition.

```fren
pub fn integer_domain?(op: BinaryOp, right: Int) :=
    not op in {BinaryOp::Div, BinaryOp::Rem} or right != 0
```

r[statics.definedness.hypotheses]
The hypotheses Φ of a judgment are Boolean Core expressions typed in its
context Γ. A conditional adds its condition to the hypotheses of its first
branch and the condition's negation to those of its second. A match adds,
to each arm, that the scrutinee is the arm's constructor. A let adds, to
its body, that the new local equals the let's value. This rule is open.

r[statics.definedness.rules]
`Σ; Γ; Φ ⊢ e def` is defined by one rule for each Core form. Every written
child of e is defined under the hypotheses that e's form gives it: both
operands of every operator, `and` and `or` included, under the incoming
hypotheses; every argument of a call; the value of a let, used or not; and
every branch and arm. A division or remainder adds the premise
`Σ; Γ; Φ ⊨ d != 0` for its divisor d, and a call adds the
[premise of its callee's precondition](#r-statics.contract.call). These
rules are open.

r[statics.definedness.declarative]
Definedness is independent of evaluation. An operation needs its premise
at the place where it is written, whether or not an evaluation would reach
it, and no hypothesis comes from the order in which operands are written.
This rule is open.

## Contracts

r[statics.contract.form]
A function's *contract* `Σ ⊢ {P} f {Q}` is a precondition P and a
postcondition Q. P is a Boolean expression over the whole argument tuple,
and Q one over the argument tuple and the result. A function that states
neither has `true` for both. This rule is open, as is the surface syntax
that states a contract.

r[statics.contract.well-formed]
A contract is well formed when P has type `Bool` in the context of the
parameters and is defined under no hypotheses, and Q has type `Bool` in
that context extended by the result's type and is defined under P. This
rule is open.

r[statics.contract.call]
A call `f(a₁, …, aₙ)` is defined when each argument is defined and the
hypotheses entail f's precondition at the arguments. The postcondition of
f, at the arguments and the call's value, is available as a hypothesis
wherever the call's value is. This rule is open. Whether a caller may also
use the callee's body is decided with it.

r[statics.contract.body]
A function declaration is verified, `Σ ⊢ d verified`, when its contract is
well formed, its body is defined under its precondition, and its
precondition entails its postcondition at the parameters and the body's
value. This rule is open.

r[statics.contract.facts]
A program's assumptions are hypotheses of each of its judgments, taken
without proof. An assertion written in an expression is a premise where it
is written and a hypothesis afterwards. An expectation is neither: it adds
no premise and no hypothesis to the static semantics, and a verified
program may state a false one. This rule is open.

## Entailment

r[statics.entailment]
`Σ; Γ; Φ ⊨ φ` holds when every assignment of values of Γ's types that
makes every hypothesis of Φ true makes φ true. The truth of a hypothesis
and of φ at an assignment is the
[denotation](DenotationalSemantics.md#r-denotation.truth) of each. This
rule is open.

r[statics.stratification]
Entailment reads denotations, and a denotation exists only for a verified
expression, so the judgments are defined together, by induction on call
order and, within one declaration, on the expression. A hypothesis or a
goal is interpreted only after its own definedness is established, under
the hypotheses that precede it, and a callee's denotation only after the
callee is verified. This rule is open.

## Programs

r[statics.program.verified]
A program is verified, `⊢ (Σ, ds) verified`, when it is
[well typed](Types.md#r-types.program.typing), its call order is well founded,
and each of its declarations is verified. This rule is open.

## Properties

The properties of this section are open: none is stated in Fren or proved.

r[statics.property.regularity]
Every expression of a definedness, contract or entailment judgment is well
typed in the judgment's context, and every hypothesis, precondition and
postcondition has type `Bool`.

r[statics.property.hypotheses]
Definedness and entailment survive an added hypothesis and an extension of
the context by newer levels.

r[statics.property.generation]
The premises of the form `Σ; Γ; Φ ⊨ φ` that a derivation of definedness
needs are a computable function of the expression, and they are the only
premises that are not decidable.

r[statics.property.soundness]
The static semantics is sound for the other two semantics. A verified
function has a denotation on every argument tuple that meets its
precondition, and that denotation meets its postcondition
([the contract theorem](DenotationalSemantics.md#r-denotation.theorem.contract)).
Evaluating a verified program reaches no error state and gives the
denotation ([adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy)).

## Material that other chapters hold

[Definedness and verification](PropertiesAndChecks.md) states definedness
over the derivation tables of Core typing: the condition of each layer,
the obligations collected from it with their hypotheses, satisfaction at an
assignment, validity, and defined and verified programs. Its goals cover
the divisor of a division or remainder, a callee's `require` and an
asserted fact. It states no postcondition. The open rules of this chapter
restate that material as the judgments above, and add contracts.

## Examples

`Ty::Nominal(["M", "Light"])` and `Ty::Nominal(["M", "Signal"])` are
different types even if both enums declare `Red`. A comparison between
their constructors fails typing, before its truth or definedness is checked.
The checked derivations and arithmetic examples follow their shared
definitions in the [typing chapter](Types.md#examples).
