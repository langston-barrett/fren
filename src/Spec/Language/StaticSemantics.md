# Static semantics

Static semantics comprises resolution, typing, definedness, contracts and
termination. [Resolution](NamesAndScope.md) produces the Core and its
symbol environment, and [Core typing](Types.md) defines the typing
judgment. This chapter defines which items an expression mentions, the
call order of a program, when the arms of a match are distinct, when a
partial operation is within its domain, and the judgments of definedness
and of contracts. [Termination](#termination), a sub-chapter of Static
semantics, defines the termination check. A program that satisfies
all of them is *verified*: it is typed, it is defined, it meets its
contracts and it passes the termination check. The [denotational semantics](DenotationalSemantics.md) gives
a meaning to a function only when its declaration and the declaration of
every function that it depends on are verified and their assumptions are
true. The
[dynamic semantics](DynamicSemantics.md) evaluates every well-typed
program, verified or not.

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
| `size(S, e) = s` | in the size context S, e has the size s | [sizes](#r-statics.termination.size) | `form_size`, for one layer; `local_size` and `parameter_sizes`, for a size context |
| `Σ ⊢ d passes` | the declaration d passes the termination check | [termination](#r-statics.termination) | `passes_alone?` and `group_passes?`, of functions given with their [written calls](#r-statics.termination.written) and grouped by the call order |
| `⊢ (Σ, ds) defined` | the program is defined | [defined programs](#r-statics.program.defined) | — |
| `⊢ (Σ, ds) verified` | the program is verified | [verified programs](#r-statics.program.verified) | — |

```text
  Γ, Δ ::= ·  |  Γ, τ                  contexts, by de Bruijn level
  Φ    ::= ·  |  Φ, φ                  hypotheses
  P, Q, A, φ, ψ                        Core expressions of type Bool
  s    ::= same | smaller | unknown    sizes
  S    ::= ·  |  S, s                  size contexts, by de Bruijn level

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
[tooling part](../Tooling/index.md). A *static error* is a failure of
[distinct arms](#r-statics.match.distinct): a match with two arms for
one constructor. This chapter states no other static error. A program
with a static error has no judgment of this chapter other than typing.
A condition that is a premise of one judgment is not a static error
when it fails, also where it reads the written program alone and no
hypothesis can discharge it: the judgment then does not hold, and every
other judgment of this chapter is still made of the program. So a
declaration that does not
[pass the termination check](#r-statics.termination) is not verified,
and a declaration with a condition that
[mentions its own recursive group](#r-statics.condition.group) against
that rule, or
[a function that does not pass the check hereditarily](#r-statics.condition.terminating)
against that one, is not defined; none of the three is a static error, and such a
declaration may still be well typed, be defined where the failed premise
is not one of definedness, and meet its contract. It may still be well typed, and the
[dynamic semantics](DynamicSemantics.md#r-dynamics.scope) evaluates
every well-typed program.

r[statics.declaration]
A program's declarations are function declarations and expectation
declarations. A function declaration has a signature, a body, conditions
and a termination mark. An expectation declaration has a parameter
context and conditions, and neither a body nor a mark. A *condition* is a Boolean expression in the
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
postcondition of a program that the Core can state is `true`. The
*termination mark* of a function declaration is `checked` or
`unchecked`. It belongs to that one declaration, and
[what it covers](#r-statics.termination.optional) is the declaration's
function or, where the function is recursive, its recursive group. The
Core's declarations have no field for the mark either, and the
[source grammar](Syntax.md) has no form that writes it, so every
declaration that a source program can state is marked `checked`. The Core's
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

use spec::names::{ArmF, CoreF, Ctx, Form, ItemId, length, lookup}

use spec::surface::{BinaryOp, Snoc}

use spec::types::{Arm, Row}

use spec::surface::Snoc::{Empty, Extend}

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
they reach; its declaration does not depend on them for that. An
expectation is outside the static semantics. It is typed, and its arms
are [distinct](#r-statics.match.distinct), as those of every written
expression are. Beyond that no judgment of this chapter is of an
expectation: definedness, entailment, admissibility and the termination
check have no premise about one.

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
distinct arms only, and so are the denotations. So a match has at most
one arm for a constructor there, and no rule of this chapter or of the
denotational semantics chooses among several. The
[dynamic semantics](DynamicSemantics.md#r-dynamics.match.selection) is
defined for every well-typed expression, with distinct arms or not: for a
constructor with several arms it selects the first one written. The compiler
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
An expectation has Φ_d and the asserted facts where a
[check](PropertiesAndChecks.md#r-verification.keyword.scope) reads it.
[Its truth](DenotationalSemantics.md#r-denotation.truth) is read under
Φ_d, and no judgment of this chapter is made of it. No
condition of another
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
fact is [entailed](#r-statics.declaration.defined) by the declaration's
hypotheses, and a check of the declaration's expectations takes it as a
hypothesis. A function's
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
`h(0)`, where h does not reach g, is in no recursive group and, where
its own declaration has not opted out, passes
the check even when h has opted out, and its evaluation diverges where
that of `h(0)` does. The rule is a premise about the termination check
and about nothing else. It does not by itself give a condition a truth
value: the functions that the condition depends on must also be defined,
meet their contracts and have true assumptions, as
[the property of conditions](#r-statics.property.conditions) states.

r[statics.declaration.defined]
A function declaration is defined, `Σ ⊢ d defined`, when its contract is
well formed, each assumption is defined under no hypotheses, its body is
defined under Φ_d, and each asserted fact is defined under Φ_d and
entailed by it.
An expectation declaration is defined by the same rule without the
contract and the body: its Φ_d is its assumptions. In both cases
[no condition of d other than an expectation mentions a function of d's own recursive group](#r-statics.condition.group),
and every function that an assumption of d mentions
[passes the termination check hereditarily](#r-statics.condition.terminating). The rule
has no premise about an expectation, neither about its truth nor about
its definedness: an expectation is outside the static semantics. Whether
an expectation has a value and whether it is true are read
[through the denotations](DenotationalSemantics.md#r-denotation.truth),
and a tool
[reports them as verdicts](PropertiesAndChecks.md#r-verification.program.verified).
So a declaration is defined or not whatever expectations it states. The
rule has no premise about the postcondition's truth either, and none
about whether d
itself or d's recursive group passes the termination check.

```text
  Σ ⊢ {P} f {Q} ok       Φ = P, A₁, …, Aₖ
  Σ; Δ; · ⊢ A def                         for each assumption A
  every function that A mentions passes the check hereditarily
  Σ; Δ; Φ ⊢ e def
  Σ; Δ; Φ ⊢ φ def        Σ; Δ; Φ ⊨ φ      for each asserted fact φ
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
in whose body, or in whose condition other than an expectation, the
expression is written, and
[definedness](#r-statics.definedness.rules) is of that declaration in
the same way. Neither judgment is made of an expectation or of a part of
one. An expression that is written in no declaration, as where
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
no order chosen among the [strata](#r-statics.stratification). A
function that only an expectation of d mentions is not constrained: no
expectation is judged. Admissibility asks
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
own group, which are of earlier strata or of its own.

## Termination

Termination is a sub-chapter of Static semantics. It defines the
termination check: the mark by which a declaration opts out of it, the
order on call instances that it establishes, and the criterion,
structural recursion on one parameter of each function, read from the
written body alone.

r[statics.termination]
`Σ ⊢ d passes` is the judgment of the *termination check*: the
declaration d *passes the termination check*. It is a judgment of the
static semantics in its own right, with three rules. An expectation
declaration passes. A function declaration passes when it has not
[opted out](#r-statics.termination.optional) and its function is in no
[recursive group](#r-statics.call-order.relation). A function
declaration passes when it has not opted out and its function's
recursive group is
[structurally recursive](#r-statics.termination.structural). A function
*passes the termination check hereditarily* when its declaration passes
the check and so does the declaration of every function that it
[reaches](#r-statics.call-order.relation).

```text
  d is an expectation declaration
  ───────────────────────────────
  Σ ⊢ d passes

  d declares f     d has not opted out     f is in no recursive group
  ───────────────────────────────────────────────────────────────────
  Σ ⊢ d passes

  d declares f     d has not opted out
  the recursive group of f is structurally recursive
  ──────────────────────────────────────────────────
  Σ ⊢ d passes
```

r[statics.termination.optional]
A function declaration carries a
[termination mark](#r-statics.declaration), `checked` or `unchecked`.
The mark sits on one function declaration. It covers that function and,
where the function is recursive, the whole of its recursive group: a
declaration has *opted out* of the termination check when it is marked
`unchecked`, or when the declaration of a function of its recursive
group is. The mark covers the group because the check of a group is one
check, of all the group's bodies under one choice of decreasing
parameters, and it cannot be made of some functions of a group without
the others. An expectation declaration has no mark and does not opt
out. A declaration that has opted out does not pass the check: no rule
of [`Σ ⊢ d passes`](#r-statics.termination) concludes it, whether or
not the function is recursive and whether or not its group is
structurally recursive. Opting out changes no other judgment of the
declaration: the declaration may be well typed, be
defined and meet its contract, as
[independence](#r-statics.property.independence) states. It is not
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
recursive function that has a parameter, its *decreasing parameter*. A
recursive function with no parameters has no decreasing parameter, and
the second case below holds of no pair of call instances of which one
is an instance of it. `(g, w̄) ≺ (f, v̄)` holds in two cases: when f reaches g and g does
not reach f; and when f and g are in one recursive group, each has a
decreasing parameter, and the value that w̄ gives g's decreasing
parameter is a proper subterm of the value that v̄ gives f's.

r[statics.termination.size] spec::statics::{Size, local_of, local_size, form_size, parameter_sizes}
The check reads the body of a function f that has a decreasing
parameter, and gives each local of the body a *size* relative to that
parameter: `same`, `smaller` or `unknown`. A *size context* S of a
context Γ gives each level of Γ a size. The size of an expression in S
is the size that S gives its level when the expression is a local, and
`unknown` for every other form: an operator, a call, a let, a
conditional and a match have the size `unknown` whatever their parts
are. Each expression written in the body of f has a size context, by
these rules. The body has the size context of f's parameters: `same` at
the decreasing parameter and `unknown` at every other parameter. The
body of a let has the size context of the let, extended by the size of
the let's value at the new level. Every other written child has the size
context of its parent: the operands of an operator, the arguments of a
call, the value of a let, the condition and the branches of a
conditional, and the scrutinee and the arms of a match. An arm
[binds no local](NamesAndScope.md#r-names.core.syntax), so it extends no
size context. `form_size` states the size of one layer, and
`local_size` that of a level, or of an expression that is no local.
`parameter_sizes` gives the size context of a function's parameters for
a decreasing parameter.

```text
  s ::= same | smaller | unknown       sizes
  S ::= ·  |  S, s                     size contexts, by de Bruijn level

  size(S, x) = S(x)                    x a local
  size(S, e) = unknown                 e of any other form

  S_f = ·, s₁, …, sₙ                   sᵢ = same when xᵢ is f's decreasing
                                       parameter, and unknown otherwise

  let e₁ in e₂ has S                   e₁ has S;  e₂ has S, size(S, e₁)
```

```fren
pub enum Size { Same, Smaller, Unknown }

pub fn local_of<E>(form: CoreF<E>): Option<Int> := match form {
    CoreF::Local(level) => Some(level),
    _ => None,
}

pub fn local_size(sizes: Snoc<Size>, level: Option<Int>): Size := match level {
    Some(index) => match lookup(sizes, index) {
        Some(size) => size,
        None => Size::Unknown,
    },
    None => Size::Unknown,
}

pub fn form_size<E>(sizes: Snoc<Size>, form: CoreF<E>): Size := local_size(sizes, local_of(form))

pub fn parameter_sizes(parameters: Ctx, decreasing: Int): Snoc<Size> := match parameters {
    Empty => Empty,
    Extend(earlier, _) => Extend(
        parameter_sizes(earlier, decreasing),
        if length(earlier) = decreasing then Size::Same else Size::Unknown
    ),
}
```

r[statics.termination.fields]
The size `smaller` is for a local that an arm of a match binds to an
argument of its scrutinee's constructor. This rule is the criterion's
one source of `smaller`, and it is stated ahead of the forms that it
reads: where a constructor takes arguments and an arm binds a local to
each, an arm of a match whose scrutinee has the size `same` or `smaller`
gives each of those locals the size `smaller`, and an arm of any other
match gives each the size `unknown`. The Core has
[no constructor with arguments](NamesAndScope.md#r-names.core.syntax)
and no arm that binds a local, so the rule has no instance in it.

r[statics.termination.guarded] spec::statics::{guarded?, argument_guarded?}
Let f and g be functions of one recursive group, each with a decreasing
parameter. A call `g(a₁, …, aₙ)` written in the body of f is *guarded*
when the argument for g's decreasing parameter has the size `smaller` in
the size context of the call. A guarded call's argument at that position
is therefore a local. The condition reads the written argument and its
size context only: no hypothesis, no assignment and no interpretation.
`guarded?` states it of the argument's layer, and `argument_guarded?` of
a call's arguments, each given by its level where it is a local, and
the level of the callee's decreasing parameter.

```text
  g's decreasing parameter is its i-th     size(S, aᵢ) = smaller
  ───────────────────────────────────────────────────────────────
  g(a₁, …, aₙ), written in the body of f with the size context S, is guarded
```

```fren
pub fn guarded?<E>(sizes: Snoc<Size>, argument: CoreF<E>) :=
    form_size(sizes, argument) = Size::Smaller

pub fn argument_guarded?(sizes: Snoc<Size>, arguments: Snoc<Option<Int>>, parameter: Int) :=
    match lookup(arguments, parameter) {
        Some(argument) => local_size(sizes, argument) = Size::Smaller,
        None => false,
    }
```
r[statics.termination.written] spec::statics::{Calls, local_at, calls_at, argument_locals, argument_calls, arm_calls, layer_calls, table_calls, written_calls}
The check reads of a body only its *written calls*: each call written
in it, with its callee and, for each argument, the level of the argument
where the argument is a local; and each let that encloses a call or
not, with the level of its value where the value is a local. `Leaf` has
no call. `Both(C, D)` has the calls of C and of D in one size context.
`Call(g, ās)` is one call of g, where `ās` lists for each argument its
level, or nothing where the argument is not a local. `Let(a, C)` has the
calls C of a let's body, where `a` is the level of the let's value, or
nothing. An operator has the calls of its operands, a call those of its
arguments and itself, a let those of its value and, under `Let`, those
of its body, a conditional those of its condition and branches, and a
match those of its scrutinee and arms. A literal, a local and a
constructor have none. `written_calls` gives the written calls of the
expression that a table derives, row by row as
[typing reads the table](Types.md#r-types.table.rows).

```fren
pub enum Calls { Leaf, Both(Calls, Calls), Call(ItemId, Snoc<Option<Int>>), Let(Option<Int>, Calls) }

pub fn local_at(rows: Snoc<Row>, position: Int): Option<Int> := match lookup(rows, position) {
    Some(row) => local_of(row.form),
    None => None,
}

pub fn calls_at(prior: Snoc<Calls>, position: Int): Calls := match lookup(prior, position) {
    Some(calls) => calls,
    None => Calls::Leaf,
}

pub fn argument_locals(rows: Snoc<Row>, arguments: Snoc<Int>): Snoc<Option<Int>> :=
    match arguments {
        Empty => Empty,
        Extend(earlier, argument) =>
            Extend(argument_locals(rows, earlier), local_at(rows, argument)),
    }

pub fn argument_calls(prior: Snoc<Calls>, arguments: Snoc<Int>): Calls := match arguments {
    Empty => Calls::Leaf,
    Extend(earlier, argument) =>
        Calls::Both(argument_calls(prior, earlier), calls_at(prior, argument)),
}

pub fn arm_calls(prior: Snoc<Calls>, arms: Snoc<Arm>): Calls := match arms {
    Empty => Calls::Leaf,
    Extend(earlier, arm) => Calls::Both(arm_calls(prior, earlier), calls_at(prior, arm.body)),
}

pub fn layer_calls(rows: Snoc<Row>, prior: Snoc<Calls>, form: Form): Calls := match form {
    CoreF::Unary(_, operand) => calls_at(prior, operand),
    CoreF::Binary(_, left, right) => Calls::Both(calls_at(prior, left), calls_at(prior, right)),
    CoreF::Call(callee, arguments) => Calls::Both(
        argument_calls(prior, arguments),
        Calls::Call(callee, argument_locals(rows, arguments))
    ),
    CoreF::Let(_, value, body) => Calls::Both(
        calls_at(prior, value),
        Calls::Let(local_at(rows, value), calls_at(prior, body))
    ),
    CoreF::If(condition, yes, no) => Calls::Both(
        calls_at(prior, condition),
        Calls::Both(calls_at(prior, yes), calls_at(prior, no))
    ),
    CoreF::Match(scrutinee, arms) =>
        Calls::Both(calls_at(prior, scrutinee), arm_calls(prior, arms)),
    _ => Calls::Leaf,
}

pub fn table_calls(rows: Snoc<Row>): Snoc<Calls> := match rows {
    Empty => Empty,
    Extend(earlier, row) =>
        Extend(table_calls(earlier), layer_calls(earlier, table_calls(earlier), row.form)),
}

pub fn written_calls(rows: Snoc<Row>): Calls := match table_calls(rows) {
    Empty => Calls::Leaf,
    Extend(_, calls) => calls,
}
```

r[statics.termination.group] spec::statics::{Mark, Function, Chosen, chosen, calls_guarded?, body_guarded?, choice_guarded?, extended_choices, parameter_choices, choices, some_guarded?}
The check reads of a function its identity, its parameters, its
[termination mark](#r-statics.declaration) and the written calls of its
body. A *choice* of decreasing parameters lists functions, each with the
level of one parameter. The calls of a body are *guarded under a choice*
when every call written in it whose callee the choice lists is
[guarded](#r-statics.termination.guarded) in its
[size context](#r-statics.termination.size): the size context of the
body is that of the function's parameters under the choice, and the
calls under a `Let` have it extended by the size of the let's value. A
call whose callee the choice does not list is of no function of the
group, and the condition does not read it. A function is guarded under a
choice when the choice lists it and its body is guarded under the
choice, and a group is when each of its functions is. `choices`
lists the choices of a group, each of which lists every function of the
group once with one of its own parameters, and `some_guarded?` decides
whether one of the listed choices guards the group.

```fren
pub enum Mark { Checked, Unchecked }

pub struct Function { item: ItemId, parameters: Ctx, mark: Mark, body: Calls }

pub struct Chosen { function: ItemId, parameter: Int }

pub fn chosen(choice: Snoc<Chosen>, item: ItemId): Option<Int> := match choice {
    Empty => None,
    Extend(earlier, entry) =>
        if entry.function = item then Some(entry.parameter) else chosen(earlier, item),
}

pub fn calls_guarded?(choice: Snoc<Chosen>, sizes: Snoc<Size>, calls: Calls) := match calls {
    Calls::Leaf => true,
    Calls::Both(left, right) =>
        calls_guarded?(choice, sizes, left) and calls_guarded?(choice, sizes, right),
    Calls::Call(callee, arguments) => match chosen(choice, callee) {
        Some(parameter) => argument_guarded?(sizes, arguments, parameter),
        None => true,
    },
    Calls::Let(value, body) =>
        calls_guarded?(choice, Extend(sizes, local_size(sizes, value)), body),
}

pub fn body_guarded?(choice: Snoc<Chosen>, function: Function) :=
    match chosen(choice, function.item) {
        Some(parameter) => calls_guarded?(
            choice,
            parameter_sizes(function.parameters, parameter),
            function.body
        ),
        None => false,
    }

pub fn choice_guarded?(choice: Snoc<Chosen>, group: Snoc<Function>) := match group {
    Empty => true,
    Extend(earlier, function) =>
        body_guarded?(choice, function) and choice_guarded?(choice, earlier),
}

pub fn extended_choices(onto: Snoc<Snoc<Chosen>>, choices: Snoc<Snoc<Chosen>>, entry: Chosen): Snoc<Snoc<Chosen>> :=
    match choices {
        Empty => onto,
        Extend(earlier, choice) =>
            Extend(extended_choices(onto, earlier, entry), Extend(choice, entry)),
    }

pub fn parameter_choices(choices: Snoc<Snoc<Chosen>>, item: ItemId, candidates: Ctx): Snoc<Snoc<Chosen>> :=
    match candidates {
        Empty => Empty,
        Extend(fewer, _) => extended_choices(
            parameter_choices(choices, item, fewer),
            choices,
            Chosen { function := item, parameter := length(fewer) }
        ),
    }

pub fn choices(group: Snoc<Function>): Snoc<Snoc<Chosen>> := match group {
    Empty => Extend(Empty, Empty),
    Extend(earlier, function) =>
        parameter_choices(choices(earlier), function.item, function.parameters),
}

pub fn some_guarded?(candidates: Snoc<Snoc<Chosen>>, group: Snoc<Function>) := match candidates {
    Empty => false,
    Extend(earlier, choice) => choice_guarded?(choice, group) or some_guarded?(earlier, group),
}
```

r[statics.termination.structural] spec::statics::structural?
A recursive group is *structurally recursive* when one choice of a
decreasing parameter for each of its functions makes
[guarded](#r-statics.termination.guarded) every call of a function of
the group that is written in the body of a function of the group. The
choice gives every function of the group one of its own parameters. A
group that holds a function with no parameters has no such choice, and
it is not structurally recursive. The condition is on every such call
that is written, in a branch that no evaluation selects as in any
other. It reads bodies and no condition: a call
[evaluates the callee's body](DynamicSemantics.md#r-dynamics.call) and
never a condition. A call of the group that is written in a condition
other than an expectation is excluded by
[a rule of its own](#r-statics.condition.group), which is a premise of
definedness and not of this check.
`structural?` decides it of the functions of one recursive group.

```fren
pub fn structural?(group: Snoc<Function>) := some_guarded?(choices(group), group)
```

r[statics.termination.decision] spec::statics::{opted_out?, passes_alone?, group_passes?}
The [judgment](#r-statics.termination) is decided of the functions that
pass or fail together: a function that is in no recursive group, alone,
or the functions of one recursive group. Each is read as
[the check reads it](#r-statics.termination.group). `opted_out?` decides
whether [the mark](#r-statics.termination.optional) of one of them opts
them out. `passes_alone?` decides the judgment of a function that is in
no recursive group, and `group_passes?` of the functions of one
recursive group. Which functions are in one recursive group is the
[call order](#r-statics.call-order.relation)'s to say.

```fren
pub fn opted_out?(covered: Snoc<Function>) := match covered {
    Empty => false,
    Extend(earlier, function) => function.mark = Mark::Unchecked or opted_out?(earlier),
}

pub fn passes_alone?(function: Function) := not opted_out?(Extend(Empty, function))

pub fn group_passes?(group: Snoc<Function>) := not opted_out?(group) and structural?(group)
```

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
Neither the truth of an expectation nor its definedness is part of it:
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
definedness of a declaration adds no other: its premise that the
functions which its contract and its assumptions mention
[pass the termination check hereditarily](#r-statics.condition.terminating)
is [decidable](#r-statics.property.decidable), and so is its premise
about [recursive groups](#r-statics.condition.group).

r[statics.property.independence]
Whether a declaration is defined and meets its contract does not depend
on its own termination or on that of its recursive group. No rule of
either asks that a call be guarded or that the declaration pass the
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

r[statics.property.check-local]
The termination check is of one declaration and of its recursive group,
and reads no other declaration's check. A function declaration that has
not opted out and whose function is in no recursive group passes it
whether or not the functions that it calls do.
So passing the check does not state that the declaration's function
terminates, and this chapter does not call a declaration terminating.
Typing has no premise about the check. Definedness and the meeting of
contracts have no premise about whether the declaration that they judge,
or its recursive group, passes the check, and each is stated of
declarations that fail it. Definedness does have a premise about the
check of other declarations: every function that a contract or an
assumption mentions
[passes the check hereditarily](#r-statics.condition.terminating).

r[statics.property.sizes]
Sizes are sound for the values of one evaluation of one body. Let
`(f, v̄)` be a call instance of a function f with a decreasing parameter,
and let v be the value that v̄ gives the decreasing parameter. The
property is of the evaluation of f's body at the assignment v̄ by the
[evaluation rules](DynamicSemantics.md#r-dynamics.evaluation.rules), as
far as the expressions written in that body: it follows the rules from
the body into operands, the value and the body of a let, conditions and
branches, scrutinees and arms, and the arguments of calls, and it does
not follow a call into its callee's body. A callee's body is evaluated
at the assignment that lists the arguments' values, which is another
call instance with a decreasing argument of its own, also where the
callee is f: where the body of `f(n: Int)` is `f(n - 1)`, the instance
`(f, 3)` evaluates `n - 1` at the assignment 3, and the evaluation of
the body at 2 belongs to the instance `(f, 2)`. Within the evaluation of
the instance `(f, v̄)`, every expression written in the body is
evaluated only at assignments that give each level of size `same` the
value v and each level of size `smaller` a proper subterm of v. The
assignment v̄ does so for the size context of the parameters. A let
keeps it: its body is evaluated with the value of the let's value at
the new level, and where the let's value is a local, that is the value
of the local's level.
[Arms that bind arguments](#r-statics.termination.fields) keep it too:
an argument of a constructor value is a proper subterm of that value,
and a proper subterm of a proper subterm of v is one of v. Every other
form evaluates its children at its own assignment. So where a
[guarded](#r-statics.termination.guarded) call of g written in the body
of f is reached in that evaluation with the argument values w̄, the
value that w̄ gives g's decreasing parameter is a proper subterm of v,
and [`(g, w̄) ≺ (f, v̄)`](#r-statics.call-order.instances) holds by the
second case of call order.

r[statics.property.termination]
The termination check is sound for the dynamic semantics. Let P be a
well-typed program and f a function of it that
[passes the termination check hereditarily](#r-statics.termination).
Then the call of f at every tuple of values of its parameters' types
ends, in a value or in an error state: it does not
[diverge](DynamicSemantics.md#r-dynamics.divergence). The property asks
nothing of definedness, of contracts or of assumptions, which the
dynamic semantics does not read; without them the call may end in an
error. The argument is an induction on
[call order](#r-statics.call-order.instances), which is
[well founded](#r-statics.property.call-order), over the call instances
of f and of the functions that f reaches, with the decreasing parameters
under which each of their groups is structurally recursive. At an
instance `(f, v̄)`, let v be the value that v̄ gives f's decreasing
parameter, where f has one. An inner induction on the expressions
written in f's body shows that each has an
[outcome](DynamicSemantics.md#r-dynamics.evaluation.rules) at every
assignment that gives each level of size `same` the value v and each
level of size `smaller` a proper subterm of v, which are the
assignments that the [soundness of sizes](#r-statics.property.sizes)
states for this one instance. The induction is on the expressions of
this body only, and it enters no callee's body: a callee's body is that
of another instance, which the outer induction covers. An operator has an outcome at all
operand values, a match selects an arm or has the outcome
`error(no-arm)`, and each other form has the outcome of the children
that it evaluates. A call written in the body, reached with the argument
values w̄, is of a callee g that f reaches. Where g does not reach f,
`(g, w̄) ≺ (f, v̄)` by the first case of call order. Where g reaches f,
the two are in one group, the group is structurally recursive, the call
is guarded, and `(g, w̄) ≺ (f, v̄)` by the soundness of sizes for the
instance `(f, v̄)`. In both cases g's body has an outcome at w̄ by the
outer induction, at the instance `(g, w̄)` with its own decreasing
argument, and so has the call. So
`P ⊢ ⟨e, v̄⟩ ⇓ r` holds of f's body e for some outcome r, the run
[ends in r](DynamicSemantics.md#r-dynamics.theorem.big-step), and it is
the [only run](DynamicSemantics.md#r-dynamics.theorem.determinism).
This is what
[total correctness](DynamicSemantics.md#r-dynamics.theorem.total-correctness)
takes from the check. A function that
[has a denotation](DenotationalSemantics.md#r-denotation.domain) is
verified together with every function that it reaches, so it passes the
check hereditarily and its calls end;
[partial correctness](DynamicSemantics.md#r-dynamics.theorem.partial-correctness)
states that a call at a tuple that meets the precondition reaches no
error state and ends only in a value that meets the postcondition.

r[statics.property.decidable]
Whether a declaration passes the termination check is decidable, and so
is whether a function passes it hereditarily. The marks and the
recursive groups of a finite program are computed from its written
declarations. A group has finitely many choices of decreasing
parameters, one for each tuple of parameter positions of its functions.
For one choice, the size context of each written expression and whether
each call is guarded are computed from the bodies. The check has no
premise of entailment and quantifies over no assignment and no
interpretation.

r[statics.property.conservative]
Passing the termination check
[hereditarily](#r-statics.termination) is
[sufficient](#r-statics.property.termination) for the calls of a
function to end, and it is not necessary. Passing the check is not
sufficient by itself: the declaration of a function in no recursive
group passes it where it has not opted out, and the function
[may call a function that diverges](#r-statics.property.check-local).
The check rejects every recursive group in which, under every choice of
decreasing parameters, some call of the group that is written in a body
of the group has, at the callee's decreasing parameter, an argument that
is not a local of size `smaller`, whether or not an evaluation reaches that call and whether or
not the argument's value decreases. A declaration whose function's
calls all end may so be stated, marked `checked`, and not pass the
check, as [a call that no evaluation reaches](#r-statics.examples.unreachable-call)
shows. Such a declaration is not verified, and
[opting out](#r-statics.termination.optional) does not make it so: a
declaration that has opted out does not pass the check either.

r[statics.property.call-order]
Call order is well founded for every choice of decreasing parameters: no
call instance has an unending chain of predecessors. The recursive groups
of a finite program are ordered by reaching, and a value has finitely many
proper subterms.

r[statics.property.subterms]
In the present Core, a recursive group whose bodies call a function of
the group does not pass the termination check. A Boolean, an integer and
a constructor of a payload-free enum have no proper subterm, and
correspondingly no rule that has an instance in the Core gives a local
the size `smaller`: the parameters have the sizes `same` and `unknown`,
a let copies the size of a local, and
[the rule that gives `smaller`](#r-statics.termination.fields) reads
forms that the Core lacks. So no call is guarded, and a recursive group
is structurally recursive exactly when each of its functions has a
parameter and no body of the group calls a function of the group. Such
a group is recursive through conditions only: some condition of one of
its declarations, other than an expectation, mentions a function of the
group, and that declaration is
[not defined](#r-statics.condition.group). So in a program of the
present Core no recursive group has all its declarations verified, and
no recursive function has a denotation.

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
true. Here φ and the hypotheses of Φ are written in d's body or in
conditions of d other than expectations, as
[entailment](#r-statics.entailment) is stated of no other expression. So
every function that φ or Φ mentions is one that d depends on, and has a
denotation. The property says nothing of an expectation: a function that
only an expectation of d mentions may have no denotation while d is
verified, and
[the truth of an expectation](DenotationalSemantics.md#r-denotation.truth)
is asked only where the functions that it mentions have denotations. The
property asks nothing of a declaration that d does not depend
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
the termination check. The two conditions on recursion compare as
follows. In the present Core the termination check admits no recursion
through bodies:
[no recursive group whose bodies call it passes](#r-statics.property.subterms),
so a program all of whose declarations pass the check meets that
condition. The check admits structural recursion, which that condition
excludes, only once the Core has constructors with arguments. That
condition does not include the check: the program just given has no
recursion through bodies and its group, which is recursive through a
condition and holds functions without parameters, does not pass; nor
does a declaration marked `unchecked`. So the correspondence has three conditions on the
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
`true`. Its group is f alone, and its decreasing parameter can only be
`x`. Its declaration does not pass the termination check: the argument
`x` of the call has the size `same`, so the call is not
[guarded](#r-statics.termination.guarded). So the program is not
verified and f has no denotation. Its
evaluation [diverges](DynamicSemantics.md#r-dynamics.divergence) at every
argument.

r[statics.examples.unreachable-call]
A function `f(x: Int)` whose body is `if false then f(x) else 0` does
not pass the termination check, though its call ends in 0 at every
argument. The call `f(x)` is written in the body and its argument has
the size `same`. The check
[reads every written call](#r-statics.termination.structural), and not
only those that an evaluation reaches. The same holds of a body
`let y := x in f(y)`: the let gives `y` the size of `x`, which is
`same`, and the call is not guarded.

r[statics.examples.no-parameter]
A function `f()` whose body is `f()` is recursive and has no parameter,
so its group has no choice of decreasing parameters and is not
[structurally recursive](#r-statics.termination.structural). The same
holds of `f()` with the body `if false then f() else 0`, and of a group
of `f()` with the body `g(0)` and `g(x: Int)` with the body `f()`: one
function without a parameter is enough.

r[statics.examples.unchecked]
Let `f(n: Int): Int` have the precondition `n >= 0` and the body
`if n = 0 then 0 else f(n - 1)`. The argument `n - 1` is an operator
and has the size `unknown`, so the declaration does not pass the
termination check, though every call of f that meets the precondition
ends: the check
[is not necessary](#r-statics.property.conservative) for that. With the
mark `unchecked` the declaration
[opts out](#r-statics.termination.optional). Marked or not, it is
defined and meets its contract: the call in the body is defined, since
the hypotheses `n >= 0` and `not (n = 0)` entail `n - 1 >= 0`. It is not
verified and f has no denotation. Since it does not pass the check, no
precondition, postcondition or assumption of a defined declaration
[mentions f](#r-statics.condition.terminating). A function `h()` with the
body `f(3)`, marked `checked`, is in no recursive group and its
declaration is verified;
h has no denotation, since it depends on f. With true assumptions f and
h are
[partially correct](DynamicSemantics.md#r-dynamics.theorem.partial-correctness).

r[statics.examples.group-mark]
Let `p(x: Int)` have the body `q(x)` and `q(x: Int)` the body `p(x)`,
and let the declaration of p be marked `unchecked` and that of q
`checked`. p and q are one recursive group, so
[both declarations have opted out](#r-statics.termination.optional), and
neither passes the termination check. A function `r(x: Int)` with the
body `p(x)` is in no group and has not opted out: its declaration passes
the check, and r does not pass it hereditarily.

r[statics.examples.conditions]
Let `g(x: Int): Bool` have the body `if g(x) then false else true`, and
let `f(x: Int): Int` have the precondition `g(x)` and the body
`1 div 0`. g is recursive and its group is not
[structurally recursive](#r-statics.termination.structural), so the
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
error, and it is not defined. It is still well typed, so the dynamic
semantics evaluates it:
[selection](DynamicSemantics.md#r-dynamics.match.selection) takes the
first arm written for a constructor, and where e ends in `A` the match
ends in 1.
