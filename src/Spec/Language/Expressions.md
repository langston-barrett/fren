# Expressions

This chapter covers expressions and their meanings.

## Pure values and source verification

The walking pure fragment has declarative source verification. Partial
operations require proof of their domain conditions in the exact context
of their written occurrence. Verification statically traverses written
expressions independently of a particular evaluation trace. Ordinary unary
and binary operands, including both sides of `and`/`or`, contribute their
obligations in the incoming context. Unused values and let definitions do
not discard definedness or assertion obligations.

Explicit `if`, constructor-match and guard scopes provide conditional
contexts. For example, the nonzero-divisor check in
`if d != 0 then n div d else 0` belongs under `d != 0`;
in `false and (1 div 0 = 0)` it remains in the incoming context.
Every named definition retains its own verification information even when
there is no call to it. Pure value semantics require no fixed evaluation
order; deterministic diagnostic traversal is an implementation policy.

Assumptions and assertions remain scoped IR verification information until
LIR -> OIR condition generation. Preserve their lexical binders, substitutions,
branch guards, owners and source origins. An unproved goal cannot justify
itself, and local hypotheses cannot become unconditional global facts.
Subset introduction/coercion predicates use the same framework: prove the
introduced value's predicate, and use an already-established parameter
predicate only as a scoped body assumption. The current walking grammar
has no assert/assume expressions or subset syntax; this policy does not
admit or implement those future forms.

The [raw walking evaluator](../Compiler/Evaluator.md) uses a lazy strategy
for concrete values. Its skipped operands and unused slots do not specify
which proof obligations exist. Verification-aware debugging must check
applicable executable obligations where possible and report unresolved
predicates honestly. Proved conditions may be erased for value evaluation;
one concrete successful execution is not a universal proof.
