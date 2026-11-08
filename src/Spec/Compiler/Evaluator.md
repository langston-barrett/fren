# Walking evaluation

Evaluation gives a concrete meaning to an expression for a particular choice
of its inputs. This chapter specifies the walking subset of
[typed syntax](Thir.md), before a desugared THIR exists. It does not decide
whether a property holds for all inputs.

## Inputs and outcomes

**Proof obligations**

r[evaluator.input.boundary]
The input module is an actual successful `checkWalking` or
`checkWalkingSource` result, or a typed value with evidence of actual
successful typing and walking validation. An arbitrary edited `Typed` record
is not such evidence. The expression is a retained body or occurrence in
that module, evaluated in its corresponding lexical context. Each local slot
has a concrete value of its recorded type; arguments match the callee's
signature in order. Enum values carry canonical enum and constructor identities.

r[evaluator.outcome.defined]
Evaluation returns either a value of the expression's type or an explicit
undefined outcome. It never substitutes a default value for an undefined
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
local to the value at its resolved nearest-first index. Parentheses preserve
outcome. A let evaluates its value in the incoming environment and its body
with that value prepended; undefined in either yields undefined. An if
evaluates its condition and then only the selected branch. A match evaluates
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
compares values of the same type, including canonical enum identities. Both
operands are demanded. Division and remainder use Euclidean quotient and
remainder for a nonzero right operand: the remainder is nonnegative and less
than the divisor's absolute value, and `left = quotient * right + remainder`.
A zero divisor yields undefined. This definedness rule does not assert that
the current static checker rejects zero or enforces Fren's solver restrictions.

For a check member, evaluation produces its Boolean value under supplied
parameter values. Assumptions restrict which parameter assignments are relevant
to an expectation; they are not values to be silently discarded. An undefined
assumption or expectation is an undefined evaluation, not a pass or failure.
There is no solver verdict, counterexample delivery, or whole-compiler result
at this boundary.

## Primitive arithmetic

These independent contracts fix operand order and distinguish addition from
subtraction. They constrain mathematical results; they are not an executable
model of the walking evaluator.

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
```

For the walking example with `Light { Red, Amber, Green }`, `next(Amber)`
evaluates to `Red`, and `wait(Red, 70)` evaluates to `100`. At `l = Amber`,
`next(l) != Light::Red` evaluates to false. These are concrete evaluations,
not claims that a solver has found or delivered a counterexample.

## Scope and evidence

This contract covers Bool, Int, payload-free nominal enums, locals, let,
if, constructor matches, nonrecursive named calls and the operators in the
walking typing table. It makes no claim about recursive calls, payload
patterns, first-class functions, other types, effects or unsupported syntax.
Only demanded branches are evaluated, although static checking visits all
written branches. The actual walking grammar and static boundary determine
which programs can reach this contract.

A future evaluator over desugared THIR must relate its values, undefinedness
and assumptions to these source-level outcomes through the actual desugaring
pass. Neither that representation, pass, evaluator nor their correspondence
is established by this chapter.

- [x] Check the small arithmetic contract independently with Fren.
- [ ] Implement the walking evaluator on actual admitted typed syntax and bind
  its primitive decisions and outcome laws to actual code.
- [ ] Establish traversal, typing, determinism and definedness correspondence;
  exercise actual code on accepted and rejected inputs with premise counts.
- [ ] Establish the future desugared THIR correspondence when that producer
  and evaluator exist.
