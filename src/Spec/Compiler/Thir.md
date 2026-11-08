# THIR and walking type checking

The typed high-level intermediate representation (THIR) adds value types to
resolved expressions. This chapter contracts the next production
`FrenHirToThir` slice using the real `FrenAst` and `FrenModule.Resolved` APIs.
It implements neither that pass nor a complete THIR schema. The
[Language types](../Language/Types.md) chapter supplies the typing rules.

## Input admission

The current HIR is `FrenModule.Resolved`: a retained `document`, collected
`scope` and ordered `references`. Each reference records its `written`
occurrence, `role`, `target` and exact nearest-first token `context`.
Targets are `.boolType`, `.intType`, `.item id` or `.local index`.
`referenceAt` searches by the anchor's tape slice; it does not validate that
the table is complete, unique or coherent with an edited document.

**Proof obligations**

r[thir.input.admission]
An admitted input is the actual successful output of `FrenAstToHir.resolve`
on its retained document, or carries independently established evidence of
the same syntax, collection and occurrence coherence.

r[thir.input.coherence]
Coherence relates the complete parsed file, collected item kinds and
canonical identities, every required occurrence's role and target, and its
exact lexical context to that input's actual declarations and syntax.

An API caller can construct or edit every field of `Resolved`. Merely having
that Lean type, an in-range index, or a supplied `valid?` Boolean establishes
neither obligation. The wrapper names the concrete successful-producer
relation `Admitted`; it is a proposition, not a validation implementation.
For the next public checker, reusing the existing resolver to compare with
the supplied resolved value is an acceptable executable admission check.
Alternatively a trusted producer boundary can carry evidence. Missing,
duplicate or stale references, wrong local slots or contexts, changed item
kinds, invented constructor ownership and changed AST/source data must
prevent success. No second lexical/path lookup implementation is required.

## Required result information

The checker may retain syntax plus typed occurrence data or use typed nodes.
This inventory fixes what consumers can obtain, not a storage layout.

| Component | Retained or established information |
| --- | --- |
| Source | Original document, file identity, half-open UTF-8 byte spans and written tokens, including parentheses and separate equal-spelling occurrences. |
| Items | Canonical module, enum, constructor, function and expectation `ItemId`s; source order and constructor ownership. |
| Signatures | Resolved parameter types in written order, result type, parameter binder occurrences and implicit versus explicit annotations. |
| Locals | The exact resolver-selected index with its aligned typed context, including each let's inferred slot type. |
| Expressions | Original literals, operators, ordered children and a value type for each value expression. |
| Calls | Resolved function identity, checked positional arguments and declared result type; the callee designator has a signature, not a first-class value type. |
| Matches | Scrutinee enum identity, resolved arm constructor identities, ordered bodies and inferred common result type. |
| Checks | Ordered member labels and assume/expect kinds, parameter context and Bool-typed bodies. |

**Proof obligations**

r[thir.result.typing]
Every successful typed result satisfies all Language walking typing rules
in the signatures and contexts derived from its admitted input.

r[thir.result.preservation]
Erasing type information recovers the admitted syntax and resolved targets,
with their order and source occurrences unchanged.

r[thir.result.failure]
A static failure returns nonempty diagnostic data and no successful typed
module; unsupported forms or missing types are never silently erased.

The checker first derives signatures and constructor owners from the actual
collected declarations and annotation references. It interprets enum types
as canonical identities and keeps builtins disjoint. It then walks bodies,
using existing `FrenBase.Binding.lookup`/`HasType` for local types at the
resolver-selected indices. Parameters extend the context in written order,
so the last parameter is index zero. A let checks its value before extending
that context; match patterns extend it by zero slots. No name lookup is
repeated to replace a selected target with a different callable or value.

Typing decides exact call arity, callee callability, item value eligibility,
annotation and suffix consistency, argument/result compatibility, all
operand types, Bool conditions and pattern ownership. It rejects empty
matches without an inferred result. It checks every declaration and member,
including unused functions and unreachable written branches. For fixed
admitted input it returns deterministic typed data or diagnostics; no solver
choice or guessed type is involved. Diagnostic recovery and multi-error
aggregation are not required by this slice.

## Type correctness and walking validation

**Proof obligations**

r[thir.validation.coverage]
The separate `WalkingCoverage` obligation requires every enum constructor
exactly once in each match, rejecting repeated and missing constructors.

r[thir.validation.nonrecursive]
The separate `WalkingNonrecursive` obligation requires the function call
graph to have no self cycle or mutually recursive strongly connected component.

r[thir.validation.boundary]
Whole walking static acceptance requires admitted input, successful typing,
`WalkingCoverage` and `WalkingNonrecursive`; typing alone establishes only
the first two.

The next typing slice must decide arity, callability and constructor owner
compatibility itself. It need not implement the two named validators, but
must expose their outstanding status and retain the information they need.
A nonempty partial match with compatible bodies and a recursive call can
be type correct while still failing walking validation. No downstream
consumer may assume those checks passed merely because THIR exists.
Neither validation nor typing proves evaluation termination in general,
operator definedness, solver success, evidence quality, or the correctness
of later desugaring and lowering. No evaluator simulation law is claimed
before the actual typed representation and evaluator exist.

## Focused examples and evidence

This checked program exercises constructor values, positional calls, a
nearest-first let context, if branches, match results and Bool conditions.
It runs with today's checker, not the future Fren2 typechecker.

```fren
pub mod typing

pub enum Light { Red, Green }

pub fn choose(b?, x: Int): Int := let y := x + 1 in if b? then y else x

pub fn delay(l: Light, base: Int): Int := match l {
    Light::Red => choose(true, base),
    Light::Green => base,
}

expect arithmetic(l: Light, base: Int) {
    assume bounded: base <= 100
    expect nondecreasing: delay(l, base) >= base
}
```

The Language chapter's exact `l + 1` example must produce `F0304`, expected
`Int`, found `bad::Light`, at line 5 column 28, byte span `[71, 72)`. Its
wrapper checks that the actual parser/resolver admit that source and retain
the offending local occurrence and nominal annotation. The current-checker
example checks the established diagnostic text; it is not Fren2 diagnostic
execution. A wrong call arity, local callee, cross-enum comparison, wrong
branch type, non-Bool condition or wrong-owner pattern is likewise a typing
failure, even when resolution succeeds. No diagnostic code beyond the
pinned case is assigned by this slice.

The S1 `wrong` expectation remains a well-typed goal for later lowering and
solver checking. The S1 unknown `y` remains a resolver failure. Accepting
syntax and names for the enum arithmetic example must not turn it into a
successful typed result or an empty set of goals.

- [ ] Implement the actual walking checker and its admission check, then
  state `result.typing`, `result.preservation` and deterministic success/failure
  laws over that concrete function. Add real primitive `impl` bindings only
  when their deciding functions exist, with proofs rather than sampling.
- [ ] Add actual-checker tests for each expression/operator, annotation,
  suffix, local/let/sibling context, forward call, arity and callability case;
  both enum identities and constructor ownership; every branch and member;
  and source/target retention. Pin the full `F0304` code/text/span above.
- [ ] Test API-created/edited resolved inputs with deleted/duplicate entries,
  changed role, target, context, scope and source. A supplied Boolean cannot
  exempt any control from admission.
- [ ] Use direct Plausible on the real checker with valid, ill-typed and
  partial inputs. Report counts for admission, signature collection, lookup
  hit/miss and typing success/failure; test wrong-slot, builtin/enum
  conflation and dropped-branch controls. Finite primitive consequences and
  sampled tests do not prove the recursive pass.
- [ ] Implement and test `WalkingCoverage` and `WalkingNonrecursive` before
  claiming whole walking static acceptance. Preserve the distinction from
  evaluation, solver verdicts and evidence checks.
- [ ] Restate the recursive typing/preservation relation in Fren once Fren2
  supports recursive expression datatypes and recursive judgments over
  their children and binder contexts. State it in Lean over the real pass
  meanwhile; it does not require a copied executable Fren IR.

These existing Spec wrappers remain compatibility documentation checked by
Fren1. They introduce no Fren2 runtime/test module and are outside the
runtime module/header and physical-size guard's inventory.
