# Evaluation

Evaluation gives a concrete meaning to an expression for a particular choice
of its inputs. This chapter specifies the source domain of
[typed syntax](Thir.md). It does not decide whether a property holds for
all inputs. It defines the concrete value-debugging strategy.
The [dynamic semantics](../Language/DynamicSemantics.md) is the language's
evaluation. This evaluator agrees with it on verified programs whose
assumptions hold, as its
[implementation property](../Language/DynamicSemantics.md#r-dynamics.theorem.implementation)
states, and differs from it elsewhere in four ways. It is a recursive
walk that computes an outcome in one pass, where the dynamic semantics
is a step relation on configurations. It leaves a let's
definition unread where the body does not read it, where the dynamic
semantics evaluates every let's value. It has one undefined outcome,
where the dynamic semantics has two kinds of error. It evaluates only
the admitted nonrecursive programs, so it always ends, where an
evaluation of the dynamic semantics may
[diverge](../Language/DynamicSemantics.md#r-dynamics.divergence). The
[static semantics](../Language/StaticSemantics.md) separately defines
declarative source verification.

## Inputs and outcomes

**Proof obligations**

r[evaluator.input.boundary]
The input module is an actual successful `checkWalking` or
`checkWalkingSource` result, or a typed value with evidence of actual
successful typing and coverage and non-recursion validation. An arbitrary edited `Typed` record
is not such evidence. The expression is a value-typed retained body or
occurrence in that module, evaluated in its corresponding lexical context. A callable designator supplies
the resolved signature and body for a call; it is not itself a value or an
undefined evaluation. Parameter slots contain concrete values of their recorded
types; let slots contain outcomes. Arguments match the callee's signature in
order. Enum values carry canonical enum and constructor identities.

r[evaluator.outcome.defined]
Evaluation of a value-typed expression returns either a value of its type or
an explicit undefined outcome. It never substitutes a default value for an undefined
operation or treats undefined as false. Given the same admitted input and
local values, the outcome is deterministic.

Coverage and non-recursion are separate from typing. The validators visit
all written bodies; their successful boundary supplies the intended finite
call graph and exhaustive constructor matches. Their universal correspondence
to those declarative properties remains an obligation of the static stage.
Evaluation must not infer those properties from a `Typed` record alone.

## Expression meaning

**Proof obligations**

r[evaluator.expression.walk]
A literal evaluates to its value, a constructor to its nominal value, and a
local to the outcome at its resolved nearest-first index. Parentheses preserve
outcome. A let binds the outcome of its definition in the incoming environment
and evaluates its body with that outcome prepended. An undefined definition
makes the let undefined only where the body reads that slot. Nested definitions
retain the incoming lexical bindings, even when later bindings shadow them.
This is the current value strategy: it does not discard the written
definition's verification obligations. Logical lowering retains those even
when the slot is unused.
An if evaluates its condition and then only the selected branch. A match evaluates
its scrutinee and then only the arm with the same canonical constructor;
patterns add no local slots. Undefined in a demanded subexpression propagates.

r[evaluator.expression.call]
A call evaluates its arguments in written order in the caller's environment,
then evaluates the resolved function body with positional parameter values
in the corresponding nearest-first context. An undefined argument or body
yields undefined. Calls do not inherit caller locals. Under the admitted
nonrecursive call graph, calls cannot recurse indefinitely.

r[evaluator.expression.operator]
Unary minus and `not` have their usual integer and Boolean meanings. Binary
arithmetic uses mathematical integers; comparisons compare their left operand
to their right, Boolean operators have their truth-table meanings, and equality
compares values of the same type, including canonical enum identities.
In the current raw value strategy,
`and` demands its right operand only when its left is true; `or` demands its
right operand only when its left is false. An undefined left operand propagates.
All other binary operators evaluate both operands, left first: in particular
`iff`, equality and inequality remain strict. Division and remainder use
Euclidean quotient and remainder for a nonzero right operand: the remainder is nonnegative and less
than the divisor's absolute value, and `left = quotient * right + remainder`.
A zero divisor yields undefined. This definedness rule does not assert that
the current static checker rejects zero or enforces Fren's solver restrictions.
Source verification independently retains both ordinary Boolean operands'
obligations in the incoming context. Only explicit conditional/guard scopes
supply conditional verification contexts; unused values do not erase checks.
The dynamic semantics fixes
[one order of evaluation](../Language/DynamicSemantics.md#r-dynamics.order):
written order, with `and` and `or` short-circuiting, given by its
evaluation contexts. This evaluator visits subexpressions in that order
except at a let. Which diagnostic is reported first is an
implementation policy.

For a check member, evaluation produces its Boolean value under supplied
parameter values. Assumptions restrict which parameter assignments are relevant
to an expectation; they are not values to be silently discarded. An undefined
assumption or expectation is an undefined evaluation, not a pass or failure.
There is no solver verdict, counterexample delivery, or whole-compiler result
at this boundary.

## Primitive arithmetic

These independent contracts fix operand order and distinguish addition from
subtraction. They constrain mathematical results; they are not an executable
model of the value evaluator.

**Dynamic semantics**

r[evaluator.primitive.arithmetic] spec::evaluator::arithmetic::{add, sub, addition_example, subtraction_example}
Addition and subtraction use the named left and right operands.

```fren
pub mod spec
pub mod spec::evaluator

pub proc arithmetic(left: Int, right: Int): (sum: Int, difference: Int) {
    ensure add: sum = left + right
    ensure sub: difference = left - right
    expect addition_example: when left = 70 and right = 30, sum = 100
    expect subtraction_example: when left = 70 and right = 30, difference = 40
}

#fren_check
```

## Primitive demand

This small contract specifies the actual choice to visit a Boolean right
operand, independently of its truth table. The wrapper binds it to
`FrenEval.shortCircuit`, which the walker calls before visiting that operand.
It does not encode syntax, environments or a second interpreter. This is
only a concrete visitation-strategy contract: ordinary `and`/`or` still
contribute both source operands' verification obligations.

**Dynamic semantics**

r[evaluator.primitive.demand] spec::evaluator::right_demand
Only `and` with false and `or` with true skip their right operands.

```fren
pub mod spec::evaluator

pub enum BooleanOp { And, Or, Iff, Equal, NotEqual }

pub proc right_demand(op: BooleanOp, left?): (needed?) {
    ensure meaning: needed? iff match op {
        BooleanOp::And => left?,
        BooleanOp::Or => not left?,
        BooleanOp::Iff => true,
        BooleanOp::Equal => true,
        BooleanOp::NotEqual => true,
    }
    expect skips_and: when op = BooleanOp::And and not left?, not needed?
    expect skips_or: when op = BooleanOp::Or and left?, not needed?
}

#fren_check
```

For the example with `Light { Red, Amber, Green }`, `next(Amber)`
evaluates to `Red`, and `wait(Red, 70)` evaluates to `100`. At `l = Amber`,
`next(l) != Light::Red` evaluates to false. These are concrete evaluations,
not claims that a solver has found or delivered a counterexample.

## Supported values and verification

This contract covers Bool, Int, payload-free nominal enums, locals, let,
if, constructor matches, nonrecursive named calls and the operators in the
typing table. It makes no claim about recursive calls, payload
patterns, first-class functions, other types, effects or unsupported syntax.
Only selected branches and demanded Boolean right operands are visited;
let-definition outcomes are stored without propagating failures at binding.
Static checking still visits all written expressions. The actual source grammar
and static boundary determine which programs can reach this contract. A full
verification-aware debugger must also check applicable executable obligations
or report unresolved predicates. The current raw `FrenEval` result alone
performs no such discharge; LIR now retains this information separately.
Conditions proved by verification may be erased for value evaluation.

The evaluator reads the walking program, not the output of
[desugaring](Desugaring.md). Each transformation must establish its own value
correspondence under the required well-definedness premises, independently
of completeness of its retained source verification information.

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).

## Arm selection

A match evaluates the arm that its scrutinee's constructor selects, which is
the arm that [`select`](../Language/Patterns.md#r-patterns.matching.select)
names. The evaluator's walk selects it with `FrenHirToThir.selectArm`, the
function that confirmation also calls, and the Thir wrapper proves that
function equal to `select`.

r[evaluator.selection.arm] spec::evaluator::evaluator_pick::agrees
The arm that the evaluator selects for a constructor is the arm `select`
names for it.

```fren
use spec::names::{ArmF, ItemId}
use spec::surface::Snoc
use spec::types::Typing
use spec::patterns::select

pub fn evaluator_pick(arms: Snoc<ArmF<Typing>>, constructor: ItemId): (arm: Option<ArmF<Typing>>) {
    ensure agrees: arm = select(arms, constructor)
}
```
