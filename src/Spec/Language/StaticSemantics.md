# Static semantics

Static semantics comprises resolution, typing, definedness, contracts and
termination. [Resolution](NamesAndScope.md) produces the Core and its
symbol environment, and [Core typing](Types.md) defines the typing
judgment. This chapter defines which items an expression mentions, the
call order of a program, when a partial operation is within its domain,
and the judgments of definedness and of contracts. It names the judgment
of termination, which a chapter of its own will define. A program that
satisfies all of them is *verified*. The
[denotational semantics](DenotationalSemantics.md) gives a meaning to
verified programs only. The [dynamic semantics](DynamicSemantics.md)
evaluates every well-typed program, verified or not.

A rule whose `r[...]` line names no Fren definition is stated in prose
only. [Definedness and verification](PropertiesAndChecks.md) states
definedness as obligations over derivation tables; a
[property below](#r-statics.property.tables) relates the two statements.

## Overview

| Judgment | Meaning | Rule | Fren |
| --- | --- | --- | --- |
| `Σ; Γ ⊢ e : τ` | e has type τ in Γ | [typing](#r-statics.typing) | [Core typing](Types.md)'s `derivation?` |
| `e ∋ a` | e mentions the item a | [mentioned items](#r-expressions.mentions.closure) | `direct_item?`, for one layer |
| `Σ ⊢ f → g` | the function f calls the function g | [calls](#r-statics.call-order.relation) | — |
| `Σ; Γ; Φ ⊨ φ` | the hypotheses Φ entail φ | [entailment](#r-statics.entailment) | — |
| `Σ; Γ; Φ ⊢ e def` | under Φ, e is defined | [definedness](#r-statics.definedness.rules) | `integer_domain?`, for one operator |
| `Σ ⊢ {P} f {Q} ok` | the contract of f, with precondition P and postcondition Q, is well formed | [contracts](#r-statics.contract.well-formed) | — |
| `Σ ⊢ d defined` | the declaration d is defined | [defined declarations](#r-statics.declaration.defined) | — |
| `Σ ⊢ d meets {P} {Q}` | the function declaration d meets its contract | [meeting a contract](#r-statics.contract.meets) | — |
| `Σ ⊢ (g, w̄) ≺ (f, v̄)` | the call of g at the arguments w̄ precedes the call of f at v̄ | [call instances](#r-statics.call-order.instances) | — |
| `Σ ⊢ d terminates` | the declaration d passes the termination check | [termination](#r-statics.termination) | — |
| `⊢ (Σ, ds) defined` | the program is defined | [defined programs](#r-statics.program.defined) | — |
| `⊢ (Σ, ds) verified` | the program is verified | [verified programs](#r-statics.program.verified) | — |

```text
  Γ, Δ ::= ·  |  Γ, τ                  contexts, by de Bruijn level
  Φ    ::= ·  |  Φ, φ                  hypotheses
  P, Q, A, φ, ψ                        Core expressions of type Bool

  f : (x₁: τ₁, …, xₙ: τₙ) → τ          a signature of Σ
  Δ = ·, τ₁, …, τₙ                     the context of f's parameters
  P is typed in  Δ                     over the whole argument tuple
  Q is typed in  Δ, τ                  over the argument tuple and the result
```

Each name stands for a de Bruijn level: `x₁` is level 0, and in Q the
result is level n.

## Scope

r[statics.scope]
The static semantics is stated over the Core that
[resolution](NamesAndScope.md) produces: literals, locals, constructors,
named calls, unary and binary operators, lets, conditionals and constructor
matches, with the declarations of a program. It is declarative: a judgment
depends on the written form of an expression and never on an order of
evaluation. What a solver's answer establishes, the evidence for a judgment
and the diagnostics that report a failure belong to the
[tooling part](../Tooling/index.md).

r[statics.declaration]
A program's declarations are function declarations and expectation
declarations. A function declaration has a signature, a body and
conditions. An expectation declaration has a parameter context and
conditions, and no body. A *condition* is a Boolean expression in the
context Δ of its declaration's parameters, with one of the four keywords
`require`, `assert`, `assume` and `expect`. It belongs to exactly one
declaration. A `require` condition is a *precondition*, an `assume`
condition an *assumption*, an `assert` condition an *asserted fact* and an
`expect` condition an *expectation*. The Core's
[declarations](Types.md#declarations-and-programs) hold each condition
apart, without its keyword; this chapter reads the keyword and the owning
declaration as the
[members of a declaration](PropertiesAndChecks.md#r-verification.member.table)
record them.

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
A function f *calls* a function g, `Σ ⊢ f → g`, when f's body or one of
the conditions of f's declaration [mentions](#r-expressions.mentions.closure)
g. f *reaches* g when a chain of one or more calls leads from f to g. Two
functions are in one *recursive group* when each reaches the other. A
function that reaches itself is *recursive*, and its group may hold it
alone. A function that does not reach itself is in no group.

## Definedness

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
its body, that the new local equals the let's value. No other form adds a
hypothesis: in particular the second operand of `and` and of `or` has the
hypotheses of the first.

r[statics.definedness.rules]
An expression is *defined* under hypotheses, `Σ; Γ; Φ ⊢ e def`, when every
partial operation written in it is within its domain, every call written
in it meets its callee's precondition, and every match written in it
covers its scrutinee's constructors. The judgment has one rule for each
Core form. Every written child of e is defined under the
[hypotheses that e's form gives it](#r-statics.definedness.hypotheses):
both operands of every operator, every argument of a call, the value of a
let, used or not, and every branch and arm. A division or remainder has
the further premise `Σ; Γ; Φ ⊨ d != 0` for its divisor d. A call has the
[premises of its callee's contract](#r-statics.contract.call). A match has
the premise of [coverage](#r-statics.definedness.coverage).

r[statics.definedness.coverage]
A match *covers* its scrutinee when every constructor of the scrutinee's
enum is the constructor of at least one of its arms. Coverage reads the
written arms and the scrutinee's type, and no hypothesis: an arm is
required for a constructor even where the hypotheses exclude it.

r[statics.definedness.declarative]
Definedness is independent of evaluation. An operation needs its premise
at the place where it is written, whether or not an evaluation would reach
it, and no hypothesis comes from the order in which operands are written.

## Contracts

r[statics.contract.form]
A function's *contract* is a precondition P and a postcondition Q. P is
the conjunction of the `require` conditions of the function's declaration,
a Boolean expression over the whole argument tuple, and `true` when there
are none. Q is a Boolean expression over the argument tuple and the
result, and `true` when the declaration states none. A contract relates a
function's arguments to its result and is not part of any type: a
parameter's type, and the result's, are the `Ty` of the signature whatever
the contract says.

r[statics.contract.well-formed]
A contract is well formed, `Σ ⊢ {P} f {Q} ok`, when P has type `Bool` in
the context of the parameters and is defined under no hypotheses, Q has
type `Bool` in that context extended by the result's type and is defined
under P, and neither mentions a function of f's own recursive group.

```text
  Σ; Δ ⊢ P : Bool        Σ; Δ; · ⊢ P def
  Σ; Δ, τ ⊢ Q : Bool     Σ; Δ, τ; P ⊢ Q def
  P and Q mention no function of f's recursive group
  ──────────────────────────────────────────────────
  Σ ⊢ {P} f {Q} ok
```

r[statics.contract.call]
A call `f(a₁, …, aₙ)` is defined under Φ when each argument is defined
under Φ and Φ entails `P[a₁, …, aₙ]`, f's precondition with the arguments
bound to its parameters by Core lets. The rule is the same for a call
into the caller's own recursive group, and it has no premise about
[termination](#r-statics.termination). A call adds no hypothesis. What a
judgment knows of a call's value is fixed by the
[interpretations that entailment ranges over](#r-statics.entailment.admissible):
for a callee of an earlier stratum, that the value is the value of the
callee's body and meets the callee's postcondition; for a callee of the
caller's own group, that it meets the postcondition, and nothing else.

r[statics.condition.scope]
The hypotheses of a declaration's conditions and body are conditions of
that same declaration, selected by keyword and never by position, as the
[scope of a keyword](PropertiesAndChecks.md#r-verification.keyword.scope)
states. The *hypotheses of a declaration* d, Φ_d, are its preconditions
and its assumptions. A precondition and an assumption have no hypotheses.
The body, the postcondition's entailment and each asserted fact have Φ_d.
An expectation has Φ_d and the asserted facts. No condition of another
declaration is a hypothesis, and an expectation is a hypothesis of
nothing.

r[statics.declaration.defined]
A function declaration is defined, `Σ ⊢ d defined`, when its contract is
well formed, each assumption is defined under no hypotheses, its body is
defined under Φ_d, each asserted fact is defined under Φ_d and entailed
by it, and each expectation is defined under Φ_d and the asserted facts.
An expectation declaration is defined by the same rule without the
contract and the body: its Φ_d is its assumptions. In both cases no
condition of d mentions a function of d's own recursive group. The rule
asks for the definedness of an expectation and never for its truth, and
it has no premise about the postcondition or about termination.

```text
  Σ ⊢ {P} f {Q} ok       Φ = P, A₁, …, Aₖ
  Σ; Δ; · ⊢ A def                         for each assumption A
  Σ; Δ; Φ ⊢ e def
  Σ; Δ; Φ ⊢ φ def        Σ; Δ; Φ ⊨ φ      for each asserted fact φ
  Σ; Δ; Φ, φ₁, …, φₘ ⊢ ψ def              for each expectation ψ
  ──────────────────────────────────────────────────────────────
  Σ ⊢ function f with body e defined
```

r[statics.contract.meets]
A defined function declaration d with body e *meets its contract*,
`Σ ⊢ d meets {P} {Q}`, when Φ_d entails the postcondition at the body's
value, `Σ; Δ; Φ_d ⊨ Q[e]`. `Q[e]` is the Core let whose value is e and
whose body is Q, so that the result's level in Q has the value of e. An
expectation declaration has no contract to meet.

## Entailment

r[statics.entailment]
`Σ; Γ; Φ ⊨ φ` is a judgment of one declaration d, about Boolean
expressions typed in Γ. It is semantic: it is stated over values and
interpretations, and names no solver and no method of proof. How far a
solver unfolds a callee's body to establish it belongs to the
[tooling part](../Tooling/index.md). The entailment holds when, for every
assignment ρ of Γ and every interpretation I that is
[admissible for d](#r-statics.entailment.admissible): if every hypothesis
of Φ is true at ρ under I, then φ is not false at ρ under I. Truth at an
assignment under an interpretation is that of the
[denotational semantics](DenotationalSemantics.md#r-denotation.truth); an
expression that has no value there is neither true nor false.

r[statics.entailment.admissible]
An [interpretation](DenotationalSemantics.md#r-expressions.meaning.context)
gives each function values at some argument tuples, and need not give one
at every tuple. It is *admissible for a declaration* d when it meets two
conditions. The first is on bodies: for every function g of a
[stratum](#r-statics.stratification) before d's, and every tuple w̄ at
which I gives g a value, g's body has that same value at w̄ under I. The
second is on contracts: for every function g of a stratum before d's or
of d's own recursive group, and every tuple w̄ at which I gives g a value
u, if g's precondition is true at w̄ under I, then g's postcondition is
not false at w̄ and u under I. Admissibility asks nothing about the
tuples at which I gives no value, and nothing about termination.

r[statics.stratification]
The judgments are defined in *strata*, and not all at once. Each recursive
group is a stratum, each function in no group is a stratum, and each
expectation declaration is a stratum. The strata are taken in an order in
which each comes after every function that it mentions outside itself.
An interpretation admissible for a declaration is constrained by the
bodies of earlier strata and by the contracts of earlier strata and of
the declaration's own group, and by nothing of a later stratum.

## Termination

r[statics.termination]
`Σ ⊢ d terminates` is the judgment of the *termination check*. It is a
judgment of the static semantics in its own right: typing, definedness
and the meeting of contracts have no premise about it, and each is stated
of declarations that fail it. The Termination chapter, which follows this
one among the chapters of static semantics and is not yet written,
defines the judgment. Until it does, the judgment is the placeholder
below: a declaration terminates when it is in no recursive group, or when
its recursion is [structural](#r-statics.call-order.structural).

r[statics.termination.optional]
The termination check need not be applied to a program. A program to
which it is not applied may be well typed, be defined and meet its
contracts; it is not [verified](#r-statics.program.verified), and it has
no denotation. This chapter does not state how a program selects whether
the check applies.

r[statics.call-order.instances]
A *call instance* is a pair `(f, v̄)` of a function and a tuple of values of
its parameters' types. A value u is a *proper subterm* of a value v when v
is a constructor applied to arguments and u is one of those arguments or a
proper subterm of one. *Call order*, `Σ ⊢ (g, w̄) ≺ (f, v̄)`, is a relation
on call instances. It is relative to a choice of one parameter of each
recursive function, its *decreasing parameter*. `(g, w̄) ≺ (f, v̄)` holds
in two cases: when f reaches g and g does not reach f; and when f and g
are in one recursive group and the value that w̄ gives g's decreasing
parameter is a proper subterm of the value that v̄ gives f's.

r[statics.call-order.structural]
A call `g(a₁, …, aₙ)` written in the body of f, with g in f's recursive
group, is *decreasing* under the hypotheses Φ when the following holds at
every assignment ρ and under every interpretation I
[admissible for f's declaration](#r-statics.entailment.admissible): if
every hypothesis of Φ is true at ρ under I, and the argument for g's
decreasing parameter has a value there, then that value is a proper
subterm of the value that ρ gives f's decreasing parameter. The recursion
of a group is *structural* when one choice of decreasing parameters makes
every such call in the bodies of the group decreasing under the
hypotheses at the place where it is written.

## Programs

r[statics.program.defined]
A program is defined, `⊢ (Σ, ds) defined`, when it is
[well typed](Types.md#r-types.program.typing) and each of its
declarations is [defined](#r-statics.declaration.defined).

r[statics.program.verified]
A declaration is *verified* when it is defined, meets its contract if it
is a function declaration, and
[terminates](#r-statics.termination). A stratum is verified when each of
its declarations is. A program is verified, `⊢ (Σ, ds) verified`, when it
is well typed and each of its declarations is verified: it is typed, it
is defined, it meets its contracts and it passes the termination check.
The truth of an expectation is no part of it:
[a verified program may state a false expectation](DenotationalSemantics.md#r-denotation.truth).

## Properties

The properties of this section are open: none is stated in Fren or proved.

r[statics.property.regularity]
Every expression of a definedness, contract or entailment judgment is well
typed in the judgment's context, and every hypothesis, precondition,
postcondition and condition has type `Bool`.

r[statics.property.hypotheses]
Definedness and entailment survive an added hypothesis and an extension of
the context by newer levels.

r[statics.property.generation]
The premises of the form `Σ; Γ; Φ ⊨ φ` that a derivation of definedness
needs are a computable function of the expression, and they are the only
premises of definedness that are not decidable.

r[statics.property.independence]
Definedness and the meeting of contracts do not depend on termination. No
rule of either has a premise about call order, and the interpretations
that entailment ranges over are constrained at the tuples where they give
a value and nowhere else. The interpretation that gives no function a
value is admissible for every declaration. So whether a program is
defined and meets its contracts is the same with the termination check
applied and without it.

r[statics.property.call-order]
Call order is well founded for every choice of decreasing parameters: no
call instance has an unending chain of predecessors. The recursive groups
of a finite program are ordered by reaching, and a value has finitely many
proper subterms.

r[statics.property.subterms]
A Boolean, an integer and a constructor of a payload-free enum have no
proper subterm. In a program whose values are of those types only, a
call inside a recursive group is decreasing only under hypotheses that no
assignment makes true together with a value for the argument, so that the
placeholder condition admits no recursion that an evaluation can reach.

r[statics.property.stratified]
The strata of a finite program can be ordered as
[stratification](#r-statics.stratification) requires. No judgment of a
declaration reads a denotation: entailment ranges over interpretations.
The denotations of a verified program are defined afterwards, stratum by
stratum, and each
[reads the earlier strata only](DenotationalSemantics.md#r-denotation.theorem.well-defined).

r[statics.property.entailment]
In a [verified](#r-statics.program.verified) stratum that comes after
verified strata only, with the
[assumptions of those strata holding](DenotationalSemantics.md#r-denotation.truth),
entailment implies truth under the denotations. If `Σ; Γ; Φ ⊨ φ` holds in
a declaration of the stratum and φ is defined under Φ, then every
assignment at which each hypothesis of Φ denotes true is one at which φ
denotes true.

r[statics.property.soundness]
The static semantics is sound for the other two semantics. In a verified
program whose assumptions hold, every function has a denotation on every
argument tuple that meets its precondition, and that denotation meets its
postcondition
([the contract theorem](DenotationalSemantics.md#r-denotation.theorem.contract)).
Evaluation agrees with the denotation as
[adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy) states: only
at an assignment that makes true the hypotheses under which the evaluated
expression is defined. A program that is defined and meets its contracts
without passing the termination check has no denotation; the dynamic
semantics states its
[partial correctness](DynamicSemantics.md#r-dynamics.theorem.partial-correctness).

r[statics.property.tables]
[Definedness and verification](PropertiesAndChecks.md) states definedness
over the derivation tables of Core typing: the condition of each layer,
the obligations collected from it with their hypotheses, satisfaction at
an assignment, validity, and defined programs. Its goals are the divisor
of a division or remainder, a callee's `require` and an asserted fact; it
states no postcondition and admits no recursion. For a program without
recursion whose postconditions are all `true`, one direction holds: when
its tables are
[defined](PropertiesAndChecks.md#r-verification.program.defined) there,
the program is defined by this chapter. Such a program meets its
contracts and terminates, so it is then verified. The converse fails.
The tables give
[no value](PropertiesAndChecks.md#r-verification.validity.uncomputed) to
a call, a product, a quotient or a remainder, so a goal that depends on
one does not hold there, where entailment reads the callee's body. With
`g()` of body `1` and `f()` of body `1 div g()`, this chapter's
entailment admits the divisor, and the divisor's obligation is not valid
over the tables.

## Examples

r[statics.examples.nominal]
`Nominal(M::Light)` and `Nominal(M::Signal)` are different types even if
both enums declare `Red`. A comparison between their constructors fails
typing, before its truth or definedness is considered. The checked
derivations and arithmetic examples follow their shared definitions in the
[typing chapter](Types.md#examples).

r[statics.examples.recursion]
A function `f(x: Int)` with no conditions whose body is `f(x)` is well
typed and defined, and it meets its contract, whose postcondition is
`true`. Its group is f alone. It does not terminate: the call is
decreasing only if the value of `x` is a proper subterm of itself, and no
value is. So the program is not verified and f has no denotation. Its
evaluation [diverges](DynamicSemantics.md#r-dynamics.divergence) at every
argument.
