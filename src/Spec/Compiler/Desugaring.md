# Walking desugaring

Desugaring normally replaces convenient source forms with a smaller language
for later passes. The current [walking typed input](Thir.md) already contains
only core forms: there is nothing to expand. Its desugaring stage is therefore
an identity, but it is still a stage with a contract. The eventual MIR builder
can consume its result without each later stage having to rediscover which
source forms were accepted.

## Boundary and identity

**Proof obligations**

r[desugaring.walking.input]
The input is an actual successful `FrenHirToThir.checkWalking` or
`checkWalkingSource` result, with evidence of that producer and its walking
validation, as required by [evaluation](Evaluator.md). An arbitrary edited
`Typed` record is not evidence of admission. Typing alone does not establish
coverage or non-recursion.

r[desugaring.walking.identity]
For every such input the stage succeeds and returns the same typed program.
It retains the entire resolved document, token tape and source spans, canonical
item and constructor identities, resolved local indices and contexts, types,
written order, and every declaration and check member. In particular it retains
assumption and expectation kinds, labels, bodies and their order. Equality here
is equality of the actual retained data, not equality of rendered names or a
copy of selected fields. The stage is deterministic.

r[desugaring.walking.boundary]
The stage does not silently drop or reinterpret unsupported constructs. The
walking grammar and admission currently accept Bool and Int, payload-free
nominal enums, nonrecursive named functions, checks, literals, names,
parentheses, unary and binary operators, calls, `if`, `let`, and matches on
constructors. A future entry point that accepts a wider input must either
implement the applicable desugaring rules or explicitly reject unsupported
forms; it must not pass them through as though they were desugared. Expansion
of `ensure`, `where`, `unless`, unnamed match parameters, lambda matches and
tables, including table-specific disjointness, is unimplemented by this slice.

## Preservation

**Proof obligations**

r[desugaring.walking.static]
The result retains the input's actual typing and walking validation evidence.
For the same admitted source, type and static-check outcomes are unchanged;
a rejected source is not turned into a successful desugared program. This
stage does not create a solver verdict or establish that expressions are
always defined.

r[desugaring.walking.evaluation]
For each retained value body or check member and the same valid concrete
arguments and depth, evaluation before and after the stage has the same
outcome, including its value or its undefined, exhausted, invalid or unsupported
failure and associated data. Assumptions remain assumptions restricting the
assignments relevant to expectations; undefined is never changed to false or
a pass. The identity stage has an actual-interpreter correspondence theorem;
future transformations and their consumers must establish their own correspondence.

The current evaluator's depth bound is operational: exhaustion is distinct from
semantic undefinedness such as division by zero. Identity must preserve both;
it does not prove that the default depth always suffices. Static validation
visits written branches even when evaluation selects only one. Raw evaluator
correspondence is distinct from declarative source verification. The identity
also retains every written operand and unused let definition, hence the data
needed for their obligations and explicit conditional scopes. A later pass
must preserve that information independently of a concrete execution trace;
ordinary `and`/`or` do not introduce verification guards.

## Example

The walking example's `next` and `wait` already use core matches and arithmetic.
The following smaller instance can cross this stage unchanged: the `Red` arm
still refers to the same constructor, `base + 30` still has the same operands,
and `bounded` remains an assumption for `at_most`.

```fren
pub mod desugar_example

pub enum Light { Red, Green }

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => base + 30,
    Light::Green => base,
}

expect waits(l: Light, base: Int) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}

#fren_check
```

This fence is checked by Fren1 as a concrete example; it is not an executable
model, execution or proof of the Fren2 pass. The eventual MIR path must
still build a theory, carry the assumption into the goal and preserve its
meaning; this chapter does not specify or implement that path.

## Evidence still needed

`FrenThirDesugar.Program` carries the actual successful `checkWalking`
result as evidence. `desugar` returns that program unchanged. The Lean
`identity`, `static`, `admitted`, `rejected` and `deterministic` theorems
state properties of this stage. The test-only `FrenThirDesugarTests.evaluation`
theorem equates actual `FrenEval.evaluate` calls at the same operational depth.
Finite property tests exercise actual admitted, rejected and partial inputs;
the checked Fren1 example does not prove these properties.

- [x] Implement the identity on admitted walking typed data, with producer
  evidence and failure at the actual admission boundary.
- [x] Establish identity-specific admission, static and evaluator correspondence
  and test actual producer inputs, including failure and partial outcomes.
- [ ] Establish universal traversal and checker soundness beyond these identity
  laws and finite tests.
- [ ] Specify and implement each future sugared form before admitting it, and
  establish its typing and meaning preservation, including table disjointness.
- [ ] Build the MIR path and establish assumption-to-goal preservation.
- [ ] Restate recursive correspondence in Fren when it can express the actual
  recursive syntax and judgments, without copying the IR or pass into Fren.
