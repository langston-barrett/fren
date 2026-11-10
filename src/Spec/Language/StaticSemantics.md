# Static semantics

Static semantics comprises resolution, typing, definedness, contracts and
termination. [Resolution](NamesAndScope.md) produces the Core and its
symbol environment, and [Core typing](Types.md) defines the typing
judgment. This chapter defines which items an expression mentions, the
call order of a program, when the arms of a match are distinct, when a
partial operation is within its domain, and the judgments of definedness
and of contracts. It names the judgment of the termination check, which
a sub-chapter of Static semantics will define. A program that satisfies
all of them is *verified*: it is typed, it is defined, it meets its
contracts and it passes the termination check. The [denotational semantics](DenotationalSemantics.md) gives
a meaning to a function only when its declaration and the declaration of
every function that it depends on are verified and their assumptions are
true. The
[dynamic semantics](DynamicSemantics.md) evaluates every well-typed
program with distinct arms, verified or not.

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
| `e distinct` | no match written in e has two arms for one constructor | [distinct arms](#r-statics.match.distinct) | `arms_distinct?`, for one match |
| `Σ; Γ; Φ ⊨ φ` | the hypotheses Φ entail φ | [entailment](#r-statics.entailment) | — |
| `Σ; Γ; Φ ⊢ e def` | under Φ, e is defined | [definedness](#r-statics.definedness.rules) | `integer_domain?`, for one operator |
| `Σ ⊢ {P} f {Q} ok` | the contract of f, with precondition P and postcondition Q, is well formed | [contracts](#r-statics.contract.well-formed) | — |
| `Σ ⊢ d defined` | the declaration d is defined | [defined declarations](#r-statics.declaration.defined) | — |
| `Σ ⊢ d meets {P} {Q}` | the function declaration d meets its contract | [meeting a contract](#r-statics.contract.meets) | — |
| `Σ ⊢ (g, w̄) ≺ (f, v̄)` | the call of g at the arguments w̄ precedes the call of f at v̄ | [call instances](#r-statics.call-order.instances) | — |
| `Σ ⊢ d passes` | the declaration d passes the termination check | [termination](#r-statics.termination) | — |
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
[tooling part](../Tooling/index.md). A *static error* is a failure of a
condition that this chapter states of the written program and that no
hypothesis can discharge. A program with a static error has no judgment
of this chapter other than typing, and no evaluation.

r[statics.declaration]
A program's declarations are function declarations and expectation
declarations. A function declaration has a signature, a body and
conditions. An expectation declaration has a parameter context and
conditions, and no body. A *condition* is a Boolean expression in the
context Δ of its declaration's parameters, with one of the four keywords
`require`, `assert`, `assume` and `expect`. It belongs to exactly one
declaration. A `require` condition is a *precondition*, an `assume`
condition an *assumption*, an `assert` condition an *asserted fact* and an
`expect` condition an *expectation*. A function declaration also has one
*postcondition*, a Boolean expression in Δ extended by the result's
type. It has no keyword, and it is `true` when the declaration states
none. The postcondition counts among the conditions of its declaration:
the [call relation](#r-statics.call-order.relation) and what a
declaration depends on read it as they read a precondition. The Core's
declarations have no field for a postcondition yet, so every
postcondition of a program that the Core can state is `true`. Each
declaration also carries a mark that says whether it has
[opted out](#r-statics.termination.optional) of the termination check;
the Core's declarations have no field for the mark either. The Core's
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
A function f *calls* a function g, `Σ ⊢ f → g`, when f's body or a
condition of f's declaration other than an expectation
[mentions](#r-expressions.mentions.closure) g. An expectation makes no
call: it is a hypothesis of nothing, and
[its truth](DenotationalSemantics.md#r-denotation.truth) is read through
the denotations, after every judgment of this chapter. f *reaches* g when a chain of one or more calls leads from f to g. Two
functions are in one *recursive group* when each reaches the other. A
function that reaches itself is *recursive*, and its group may hold it
alone. A function that does not reach itself is in no group. A
declaration d *depends on* a function g when d's body or one of d's
conditions other than an expectation mentions g, or mentions a function
that reaches g. So the declaration of a function f depends on exactly
the functions that f reaches, and f is said to depend on them too. An
expectation depends on the functions that it mentions and on those that
they reach; its declaration does not depend on them for that.

## Distinct arms

r[statics.match.distinct] spec::statics::arms_distinct?
The arms of a match are *distinct* when no two of them have the same
constructor. An expression *has distinct arms*, `e distinct`, when the
arms of every match written in it are distinct, and a program does when
every body and every condition of its declarations does. A match with two
arms for one constructor is a static error. Typing does not establish the
condition: a well-typed match stays well typed when an arm is
[repeated](Types.md#r-types.judgment.coverage-separate). Every judgment
that this chapter defines after this rule is stated of expressions with
distinct arms only, and the
[dynamic semantics](DynamicSemantics.md#r-dynamics.scope) evaluates no
other expression. So a match has at most one arm for a constructor, and
no rule of the three semantics chooses among several. The compiler
rejects a match that repeats a constructor in its
[coverage validation](../Compiler/Thir.md#r-thir.validation.coverage).

```fren
pub fn arms_distinct?<E>(arms: Snoc<ArmF<E>>) := match arms {
    Snoc::Empty => true,
    Snoc::Extend(earlier, arm) =>
        not arm_mentions?(earlier, arm.constructor) and arms_distinct?(earlier),
}
```

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
enum is the constructor of one of its arms. The arms are
[distinct](#r-statics.match.distinct), so each constructor then has
exactly one arm. Coverage reads the written arms and the scrutinee's
type, and no hypothesis: an arm is required for a constructor even where
the hypotheses exclude it.

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
under P, neither mentions a
[function of f's own recursive group](#r-statics.condition.group), and
every function that either mentions
[passes the termination check hereditarily](#r-statics.condition.terminating).

```text
  Σ; Δ ⊢ P : Bool        Σ; Δ; · ⊢ P def
  Σ; Δ, τ ⊢ Q : Bool     Σ; Δ, τ; P ⊢ Q def
  P and Q mention no function of f's recursive group
  every function that P or Q mentions passes the check hereditarily
  ─────────────────────────────────────────────────────────────────
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
for a callee outside the caller's group, that the value is the value of the
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
nothing. In particular an assumption is a hypothesis only within its own
declaration: a caller of f does not have f's assumptions among its
hypotheses. What a caller knows of f is f's contract, and the theorems
that rely on that contract ask that f's assumptions be
[true](DenotationalSemantics.md#r-denotation.truth).

r[statics.condition.group]
No precondition, postcondition, assumption or asserted fact of a
declaration mentions a function of the declaration's own recursive
group. Each of the four is included because another judgment relies on
it. A precondition and an assumption are
[hypotheses](#r-statics.condition.scope) of the body and of the other
conditions. The postcondition is what a caller knows of the function's
value, and what the body knows of a call into its own group. An asserted
fact is a hypothesis of the declaration's expectations. A function's
body may call the function's group, and these conditions may not. Since
a function [calls](#r-statics.call-order.relation) what these conditions
mention, the rule also excludes a cycle that passes through one of them:
when a precondition of f mentions g and g's body mentions f, the two are
in one group, and the precondition mentions a function of it. So no
function that such a condition of d mentions reaches d's function. An
expectation is not restricted and makes no call: it is a hypothesis of
nothing. Where an expectation of f mentions g and g's body calls f,
neither function is in a recursive group for that. The restriction is
provisional, and a later revision of this chapter may admit some of
these mentions under rules of their own.

r[statics.condition.terminating]
Every function that a precondition, the postcondition or an assumption
of a declaration mentions
[passes the termination check hereditarily](#r-statics.termination): its
declaration passes the check, and so does the declaration of every
function that it reaches, so that none of them opts out. The rule is
about the declarations that the
condition depends on, which are outside the declaration's group, and not
about the check of the declaration that states the condition. A declaration
that [opts out](#r-statics.termination.optional) of the termination
check has not passed it, so no precondition, postcondition or assumption
mentions its function or a function that reaches it. An asserted fact
and an expectation are not so restricted. The rule asks for more than
the check of the mentioned function alone: a function g whose body is
`h(0)`, where h does not reach g, is in no recursive group and passes
the check even when h has opted out, and its evaluation diverges where
that of `h(0)` does. The rule is a premise about the termination check
and about nothing else. It does not by itself give a condition a truth
value: the functions that the condition depends on must also be defined,
meet their contracts and have true assumptions, as
[the property of conditions](#r-statics.property.conditions) states.

r[statics.declaration.defined]
A function declaration is defined, `Σ ⊢ d defined`, when its contract is
well formed, each assumption is defined under no hypotheses, its body is
defined under Φ_d, each asserted fact is defined under Φ_d and entailed
by it, and each expectation is defined under Φ_d and the asserted facts.
An expectation declaration is defined by the same rule without the
contract and the body: its Φ_d is its assumptions. In both cases
[no condition of d other than an expectation mentions a function of d's own recursive group](#r-statics.condition.group),
and every function that an assumption of d mentions
[passes the termination check hereditarily](#r-statics.condition.terminating). The rule
asks for the definedness of an expectation and never for its truth. It
has no premise about the postcondition's truth, and none about whether d
itself or d's recursive group passes the termination check.

```text
  Σ ⊢ {P} f {Q} ok       Φ = P, A₁, …, Aₖ
  Σ; Δ; · ⊢ A def                         for each assumption A
  every function that A mentions passes the check hereditarily
  Σ; Δ; Φ ⊢ e def
  Σ; Δ; Φ ⊢ φ def        Σ; Δ; Φ ⊨ φ      for each asserted fact φ
  Σ; Δ; Φ, φ₁, …, φₘ ⊢ ψ def              for each expectation ψ
  no A and no φ mentions a function of f's recursive group
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
expressions typed in Γ. The notation leaves d out: it is the declaration
in whose body or condition the expression is written, and
[definedness](#r-statics.definedness.rules) is of that declaration in
the same way. An expression that is written in no declaration, as where
another chapter speaks of an expression defined under Φ, is judged as
the body of a declaration that is in no recursive group and has the
hypotheses Φ: it depends on the functions that it or Φ mentions and on
those that they reach. It is semantic: it is stated over values and
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
conditions. The first is on bodies: for every function g that d
[depends on](#r-statics.call-order.relation) and that is not of d's own
recursive group, and every tuple w̄ at
which I gives g a value, g's body has that same value at w̄ under I. The
second is on contracts: for every function g that d depends on, those of
d's own recursive group included, and every tuple w̄ at which I gives g a value
u, if g's precondition is true at w̄ under I, then g's postcondition is
not false at w̄ and u under I. Both conditions read the call order and
no order chosen among the [strata](#r-statics.stratification). Where an
expectation of d is judged, a function that the expectation depends on
is constrained as well: by both conditions when it does not reach d's
function, and by the second alone when it does. Admissibility asks
nothing about the tuples at which I gives no value, nothing about a
function that is not named here, and nothing about the termination
check.

r[statics.stratification]
The judgments are defined in *strata*, and not all at once. Each recursive
group is a stratum, each function in no group is a stratum, and each
expectation declaration is a stratum. The strata are taken in an order in
which each comes after every function that it depends on outside itself.
Several orders may do, and no judgment depends on the choice.
An interpretation admissible for a declaration is constrained by the
bodies of the functions that the declaration depends on outside its
group and by the contracts of those functions and of the declaration's
own group, which are of earlier strata or of its own. A function that
only an expectation mentions may be of a later stratum.

## Termination

r[statics.termination]
`Σ ⊢ d passes` is the judgment of the *termination check*: the
declaration d *passes the termination check*. It is a
judgment of the static semantics in its own right. Typing has no premise
about it. Definedness and the meeting of contracts have no premise about
whether the declaration that they judge, or its recursive
group, passes the check, and each is stated of declarations that fail it.
Definedness does have a premise about the check of other
declarations: every function that a contract or an assumption mentions
[passes the check hereditarily](#r-statics.condition.terminating).
Termination, a sub-chapter of Static semantics that is not yet written,
defines the judgment. Until it does, the judgment is the placeholder
below: a declaration passes the check when it has not
[opted out](#r-statics.termination.optional) of it and either it
is in no recursive group or its recursion is
[structural](#r-statics.call-order.structural). The judgment is of one
declaration and reads no other declaration's check: a declaration that
is in no recursive group passes it whether or not the functions that it
calls do. So passing the check does not state that the declaration's
function terminates, and this chapter does not call a declaration
terminating. A function *passes the termination check hereditarily* when
its declaration passes the check and so does the declaration
of every function that it [reaches](#r-statics.call-order.relation):
each of them passes, and none has opted out. Neither notion
alone states that an evaluation ends. A function's evaluation is stated
to end only where the function
[has a denotation](DenotationalSemantics.md#r-denotation.domain): it
passes the check hereditarily, and its declaration and the declaration of
every function that it reaches are defined, meet their contracts and
have true assumptions.

r[statics.termination.optional]
The termination check need not be applied to every declaration. A
declaration may *opt out* of it. Each declaration
[carries a mark](#r-statics.declaration) that says whether it has; the
Termination sub-chapter will define how a declaration is written so, and
this chapter states only what follows. A
declaration that opts out has not passed the check: `Σ ⊢ d passes`
does not hold of it, whether or not it is recursive. Such a declaration
may be well typed, be defined and meet its contract. It is not
[verified](#r-statics.program.verified), neither its function nor a
function that reaches its function has a denotation, and
[no precondition, postcondition or assumption mentions its function or a function that reaches it](#r-statics.condition.terminating).
Let d be a declaration that has opted out and g its function. Another
declaration whose body calls g, and whose function g does not reach, may
still be verified, since the termination check of that other declaration
does not read the check of d.

r[statics.call-order.instances]
A *call instance* is a pair `(f, v̄)` of a function and a tuple of values of
its parameters' types. A value u is a *proper subterm* of a value v when v
is a constructor applied to arguments and u is one of those arguments or a
proper subterm of one. *Call order*, `Σ ⊢ (g, w̄) ≺ (f, v̄)`, is a relation
on call instances. It is relative to a choice of one parameter of each
recursive function, its *decreasing parameter*. A recursive function
with no parameters has no decreasing parameter, and the second case
below holds of no call instance of it. `(g, w̄) ≺ (f, v̄)` holds
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
subterm of the value that ρ gives f's decreasing parameter. Where f or g
has no parameters, and so no decreasing parameter, the call is
decreasing only when no such ρ and I make every hypothesis of Φ true.
So a group that holds a function with no parameters has structural
recursion only if every call of the group that is written in that
function's body, or that calls it, stands under hypotheses that are true
nowhere. The recursion
of a group is *structural* when one choice of decreasing parameters makes
every such call in the bodies of the group decreasing under the
hypotheses at the place where it is written.

## Programs

r[statics.program.defined]
A program is defined, `⊢ (Σ, ds) defined`, when it is
[well typed](Types.md#r-types.program.typing), it has
[distinct arms](#r-statics.match.distinct) and each of its declarations
is [defined](#r-statics.declaration.defined).

r[statics.program.verified]
A declaration is *verified* when it is well typed, it has
[distinct arms](#r-statics.match.distinct), it is
[defined](#r-statics.declaration.defined), it
[meets its contract](#r-statics.contract.meets) if it
is a function declaration, and it
[passes the termination check](#r-statics.termination). A stratum is verified when each of
its declarations is. A program is verified, `⊢ (Σ, ds) verified`, when it
is [well typed](Types.md#r-types.program.typing), it has distinct arms
and each of its declarations is verified: it is typed, it
is defined, it meets its contracts and it passes the termination check.
The truth of an expectation is no part of it:
[a verified program may state a false expectation](DenotationalSemantics.md#r-denotation.truth).
Being verified is a property of one declaration. It does not state that
the function's evaluation ends: the body of a verified declaration may
call a function whose declaration is not verified, such as one that has
opted out of the termination check and diverges. The theorems about
evaluation are stated of a function that
[has a denotation](DenotationalSemantics.md#r-denotation.domain), whose
declaration is verified together with the declaration of every function
that it depends on. In a verified program every declaration is verified,
so there the two differ only by the truth of the assumptions.

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
The premises of the form `Σ; Γ; Φ ⊨ φ` that a derivation of
`Σ; Γ; Φ ⊢ e def` needs are a computable function of the expression, and
they are the only premises of that judgment that are not decidable. The
definedness of a declaration has one more premise that is not decidable:
that the functions which its contract and its assumptions mention
[pass the termination check hereditarily](#r-statics.condition.terminating).
The placeholder for that check asks that calls be
[decreasing](#r-statics.call-order.structural) at every assignment and
under every admissible interpretation.

r[statics.property.independence]
Whether a declaration is defined and meets its contract does not depend
on its own termination or on that of its recursive group. No rule of
either asks that a call be decreasing or that the declaration pass the
termination check, and the interpretations that
entailment ranges over are constrained at the tuples where they give a
value and nowhere else. The interpretation that gives no function a value
is admissible for every declaration. Definedness has two premises that
read the call order, and both are about conditions:
[no condition other than an expectation mentions a function of its declaration's own recursive group](#r-statics.condition.group),
and the
[functions that a contract or an assumption mentions](#r-statics.condition.terminating),
which are outside the declaration's group, pass the termination check
hereditarily. The second is its one premise about that check. So a declaration is defined and meets its
contract when it opts out of the termination check exactly when it does
otherwise; opting out can change those judgments only for the
declarations whose contract or assumptions depend on it.

r[statics.property.conditions]
The conditions of a contract and the assumptions are total where the
functions that they depend on are verified and have true assumptions.
Let d be a
[defined](#r-statics.declaration.defined) declaration, and let the
declaration of every function that its preconditions, its postcondition
and its assumptions mention, and of every function that such a function
reaches, be defined, meet its contract and have
[true assumptions](DenotationalSemantics.md#r-denotation.truth). Since d
is defined, each function that those conditions mention
[passes the termination check hereditarily](#r-statics.condition.terminating), so each of
the declarations just named passes the termination check too and is
verified, and each function that the conditions mention
[has a denotation](DenotationalSemantics.md#r-denotation.domain). Then
each precondition and each assumption of d has a truth value at every
assignment of d's parameters, and the postcondition has one at every
assignment of the parameters and the result at which the precondition is
true. This holds whether or not d itself passes the termination check.
The premise about the check alone does not give it: a function that
passes the check hereditarily and whose body is `1 div 0` has no value anywhere, and a condition that
calls it has no truth value.

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
Entailment implies truth under the denotations. Let d be a
[verified](#r-statics.program.verified) declaration, and let every
function that d depends on
[have a denotation](DenotationalSemantics.md#r-denotation.domain). If
`Σ; Γ; Φ ⊨ φ` holds in d and φ is defined under Φ, then every assignment
at which each hypothesis of Φ denotes true is one at which φ denotes
true. The property asks nothing of a declaration that d does not depend
on, and nothing of d's own assumptions beyond what Φ holds, unless d is
recursive and so depends on its own function.

r[statics.property.soundness]
The static semantics is sound for the other two semantics. A function
that [has a denotation](DenotationalSemantics.md#r-denotation.domain)
has a value on every argument tuple that meets its precondition, and
that value meets its postcondition
([the contract theorem](DenotationalSemantics.md#r-denotation.theorem.contract)).
Its evaluation there ends in that value: the function is
[totally correct](DynamicSemantics.md#r-dynamics.theorem.total-correctness).
Evaluation agrees with the denotation as
[adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy) states: only
at an assignment that makes true the hypotheses under which the evaluated
expression is defined. None of this is stated of a declaration that is
verified while a declaration that it depends on is not: its function has
no denotation. A function that is defined and meets its contract
without passing the termination check has no denotation either; where
the declarations that it depends on are defined and meet their contracts
too, with true assumptions, the dynamic semantics states its
[partial correctness](DynamicSemantics.md#r-dynamics.theorem.partial-correctness).

r[statics.property.tables]
[Definedness and verification](PropertiesAndChecks.md) states definedness
over the derivation tables of Core typing: the condition of each layer,
the obligations collected from it with their hypotheses, satisfaction at
an assignment, validity, and defined programs. Its goals are the divisor
of a division or remainder, a callee's `require` and an asserted fact; it
states no postcondition and admits no recursion through bodies. Its
[condition on recursion](Types.md#r-types.program.nonrecursive) reads the
calls in bodies only, where the [call order](#r-statics.call-order.relation)
of this chapter also reads the functions that a condition other than an
expectation mentions, so
that condition does not make the call order acyclic. Where `f()` has the
body `0` and the asserted fact `g() = 0`, and `g()` has the body `f()`, no
body calls itself through others, and f and g are one recursive group of
this chapter: the asserted fact
[mentions a function of its own group](#r-statics.condition.group), so
the declaration of f is not defined here, and the group does not pass
the termination check. So the correspondence has three conditions on the
program: no function reaches itself in this chapter's call order, bodies
and conditions other than expectations together; its postconditions are all `true`; and no
declaration opts out of the termination check. For such a program one
direction holds: when its tables
are [defined](PropertiesAndChecks.md#r-verification.program.defined)
there, the program is defined by this chapter. The tables ask that a
goal hold at every assignment that
[refutes no hypothesis](PropertiesAndChecks.md#r-verification.assignment.fact),
and entailment asks that it be not false at every assignment that makes
the hypotheses true. A true hypothesis is not refuted, so the tables
ask it at every assignment that entailment reads, and a goal that holds
is not false. Each declaration of such
a program meets its contract and, being in no recursive group and not
opted out, passes the termination check, so each is then verified. The
converse fails.
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
`true`. Its group is f alone. Its declaration does not pass the
termination check: the call is
decreasing only if the value of `x` is a proper subterm of itself, and no
value is. So the program is not verified and f has no denotation. Its
evaluation [diverges](DynamicSemantics.md#r-dynamics.divergence) at every
argument.

r[statics.examples.conditions]
Let `g(x: Int): Bool` have the body `if g(x) then false else true`, and
let `f(x: Int): Int` have the precondition `g(x)` and the body
`1 div 0`. g is recursive and its recursion is not structural, so the
declaration of g does not pass the termination check. The precondition of f mentions g, so the declaration of f
is [not defined](#r-statics.condition.terminating). Entailment alone
would not reject it. No admissible interpretation gives g a value, since
no Boolean is its own negation. So the body of f would be defined, its
hypothesis `g(x)` being true nowhere, and a call `f(0)` would be defined
too, its goal `g(0)` being false nowhere, though the evaluation of
`f(0)` ends in `error(zero-divisor)`. The example also shows what
[entailment](#r-statics.entailment) means for a goal that calls a
function: the goal is entailed when it is false under no admissible
interpretation, the one that gives no function a value and every total
one alike. A goal with no value under the first must still be not false
under each of the others, and here there are no others for g.

r[statics.examples.repeated-arm]
With an enum of the constructors `A` and `B`, the match
`match e { A => 1, A => 2, B => 3 }` is well typed and has an arm for
each constructor. Its arms are not
[distinct](#r-statics.match.distinct), so a program that writes it is in
error: it is not defined, and it has no evaluation.
