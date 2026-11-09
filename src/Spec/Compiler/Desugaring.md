# Desugaring

Desugaring normally replaces convenient source forms with a smaller language
for later passes. The [typed input](Thir.md) contains
only core forms: there is nothing to expand. Its desugaring stage is therefore
an identity. The MIR builder consumes its result with the admitted source
forms and their static validation retained.

## Boundary and identity

**Proof obligations**

r[desugaring.walking.input]
The input is an actual successful `FrenHirToThir.checkWalking` or
`checkWalkingSource` result, with evidence of that producer and its coverage and non-recursion
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
source grammar and admission accept Bool and Int, payload-free
nominal enums, nonrecursive named functions, checks, literals, names,
parentheses, unary and binary operators, calls, `if`, `let`, and matches on
constructors. An entry point accepting a wider input must either
implement the applicable desugaring rules or explicitly reject unsupported
forms; it must not pass them through as though they were desugared. The admitted source forms exclude `ensure`, `where`, `unless`, unnamed
match parameters, lambda matches and tables.

## Preservation

**Proof obligations**

r[desugaring.walking.static]
The result retains the input's actual typing and coverage and non-recursion validation evidence.
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
transformations and their consumers must establish their own correspondence.

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

The example's `next` and `wait` already use core matches and arithmetic.
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

The MIR path must build a theory, carry the assumption into the goal and
preserve its meaning, as specified by the [MIR rules](Mir.md).

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
