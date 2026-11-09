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
This follows the Language's [let rules](../../Reqs/Lang/EvaluationRules.md#let-expressions).
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
As in the Language's [lazy Boolean rules](../../Reqs/Lang/EvaluationRules.md#lazy-boolean-expressions),
`and` demands its right operand only when its left is true; `or` demands its
right operand only when its left is false. An undefined left operand propagates.
All other binary operators demand both operands, left first: in particular
`iff`, equality and inequality remain strict. Division and remainder use
Euclidean quotient and remainder for a nonzero right operand: the remainder is nonnegative and less
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

#fren_check
```

## Primitive demand

This small contract specifies the actual choice to visit a Boolean right
operand, independently of its truth table. The wrapper binds it to
`FrenEval.shortCircuit`, which the walker calls before visiting that operand.
It does not encode syntax, environments or a second interpreter.

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

For the walking example with `Light { Red, Amber, Green }`, `next(Amber)`
evaluates to `Red`, and `wait(Red, 70)` evaluates to `100`. At `l = Amber`,
`next(l) != Light::Red` evaluates to false. These are concrete evaluations,
not claims that a solver has found or delivered a counterexample.

## Scope and evidence

This contract covers Bool, Int, payload-free nominal enums, locals, let,
if, constructor matches, nonrecursive named calls and the operators in the
walking typing table. It makes no claim about recursive calls, payload
patterns, first-class functions, other types, effects or unsupported syntax.
Only selected branches and demanded Boolean right operands are visited;
let-definition outcomes are stored without propagating failures at binding.
Static checking still visits all written expressions. The actual walking grammar
and static boundary determine which programs can reach this contract.

A future evaluator over desugared THIR must relate its values, undefinedness
and assumptions to these source-level outcomes through the actual desugaring
pass. Neither that representation, pass, evaluator nor their correspondence
is established by this chapter.

- [x] Check the small arithmetic and demand contracts independently with Fren.
- [x] Implement the walking evaluator on actual admitted typed syntax in
  `FrenEval`, with actual-code arithmetic and outcome boundary laws in Lean.
- [x] Exercise actual code with direct Plausible and concrete controls on
  accepted, rejected, undefined and invalid inputs, with premise counts.
- [ ] Prove universal traversal soundness, result completeness and definedness
  correspondence; the output type check and finite controls do not prove these.
- [ ] Establish the future desugared THIR correspondence when that producer
  and evaluator exist.

## Implemented walking boundary

`FrenEval.Program` stores the actual `Typed` value and proof that
`checkWalking input = .ok typed`. `fromResolved` runs that producer;
`fromSource` runs the real parser and resolver before it. `fromTyped` requires
proof of actual typing before running walking validation. An edited record
or a supplied Boolean cannot create this evidence. `Program.retains`,
`Program.static` and `fromResolved_success` bind this boundary to the actual
producer and its retained document, coverage and non-recursion results.

`evaluate` selects a retained body by canonical owner and optional member
label. Its positional concrete arguments must match the body's parameters;
they are reversed into the existing nearest-first context. Enum inputs must
name an actual declared constructor of their recorded canonical owner.
The interpreter walks the existing syntax and resolved references, using
typed callable occurrences to enter a named body with only its arguments.
There is no second syntax tree, executable Fren pass model or solver call.
The result retains the original body and complete check member, including
whether it is an assumption or expectation, its label and its source spans.
Clients must keep assumptions when interpreting check assignments.

An outcome is a concrete `Value`, semantic `Failure.undefined` (zero divisor),
`Failure.exhausted`, or an invalid/unsupported diagnostic. Missing requests
are invalid; bad arguments are invalid outcomes associated with the retained
body. These failures carry source spans and details; undefinedness also
retains its operator. They are never converted to false or a solver verdict.

The total implementation uses the static walker's depth approach: each
visited expression, including entry into a callee body, consumes one unit.
Siblings receive the same remaining depth; the bound does not count total
steps. Let definitions are computed once in the incoming environment at the
let's remaining depth and stored as complete outcomes, without a thunk or
closure machine. Reading a slot consumes the name's unit and returns that
stored outcome; it does not reevaluate the definition at the use site's depth.
An unused slot's undefined, exhausted, invalid or unsupported outcome does
not escape. A read returns that exact outcome and its original diagnostic.
Thus an unused definition may still cost work. A definition exhausted at
binding depth remains exhausted at every read; slot reads do not retry it.
Skipped `and`/`or` right expressions consume no depth or evaluation work.
`defaultDepth` multiplies the largest body token count plus one by the function
count plus one. Callers may supply another depth, including
zero. Exhaustion is explicitly separate from semantic undefinedness. No
theorem currently proves that this default suffices for every admitted
program, or bounds total execution time, memory or integer magnitude.

`binary_add`, `binary_sub`, `binary_mul`, `binary_div`, `binary_mod`,
`div_zero`, `mod_zero` and `euclidean` prove the actual primitive arithmetic
decisions. The independent Fren contract above remains checked separately;
changing its addition to subtraction must fail. Native controls also mutate
operators in actual admitted source and require the changed concrete results.
`evaluate_selected` proves retained body selection, `evaluate_type` proves
that a returned value matches the retained body's type and constructor
inventory, and `evaluate_deterministic` proves uniqueness at fixed depth.
The type theorem follows from an explicit output check, not a universal
preservation proof of the recursive interpreter.

`walk_and_false` and `walk_or_true` prove the Language's deciding-left facts
about the actual recursive walker for every right expression. `walk_let`
proves its outcome-binding equation at explicit depth, and `walk_local`
proves exact retrieval of any stored outcome. `walk_strict_failure` preserves
complete demanded right failures; `shortCircuit_strict` excludes every other
operator from skipping. The wrapper also checks admitted source against
independent lazy-let and Boolean outcomes. These laws and regressions close
the reported strict-demand mistake; they do not prove universal correspondence
to the Language evaluator or completeness at `defaultDepth`.

Direct Plausible generates source programs and concrete values, then runs
the real producer and evaluator. Every source sample requires defined,
undefined, invalid, exhausted and rejected cases; no failed premise is
discarded. The separate fixed census reports each class explicitly. These
tests include S1's three concrete results above, unused/used/guarded lets,
lexical shadowing, skipped/demanded `and`/`or` operands, strict `iff`, equality,
inequality and calls, both check-member roles, depth controls, nominal input
rejection and operator mutation sensitivity. The 24-source evaluator census
requires 216 defined and 120 undefined outcomes, 96 invalid arguments, 24
exhaustions, 120 rejected sources, 24 rejected edited producers and 24 operator
mutants, with no discarded premises. These remain finite evidence.

- [ ] Restate recursive evaluation and its correspondence laws in Fren once
  Fren2 can express recursive syntax and judgments, without copying the IR.
