# THIR and walking type checking

The typed high-level intermediate representation (THIR) adds value types to
resolved expressions. This chapter contracts the production
`FrenHirToThir` slice using the real `FrenAst` and `FrenModule.Resolved` APIs.
The actual pass now retains resolved syntax plus typed occurrence data; this
chapter does not freeze a complete THIR schema. The
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
relation `Admitted`. The actual `admit` boundary reuses the resolver, its
proved document-retention law and decidable equality on the complete scope
and reference table to establish this proposition.
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

The type-only `check` and `checkSource` decide arity, callability and
constructor owner compatibility. They retain the information the two
validators consume; they do not run those validators.
A nonempty partial match with compatible bodies and a recursive call can
be type correct while still failing walking validation. No downstream
consumer may assume those checks passed merely because THIR exists.
Neither validation nor typing proves evaluation termination in general,
operator definedness, solver success, evidence quality, or the correctness
of later desugaring and lowering. No evaluator simulation law is claimed
before the actual typed representation and evaluator exist.

## Actual static boundary

`validateCoverage` visits the actual typed postorder occurrences in every
function and check member, including assumptions and unreachable written
branches. It identifies the scrutinee occurrence by its complete token
sequence, reads its nominal enum type, and takes the constructor inventory
from the admitted declaration scope, filtered by canonical owner. It checks
pattern reference identities in written order, recording every repeated
case and every absent constructor independently of the arm count. The
walking AST supports only constructor paths as patterns. It has no wildcard
or pattern binder; unresolved `_` and wrong-owner patterns fail before static
validation rather than silently discharging coverage.

`callEdges` reads actual call nodes and the callable signatures of their
callee occurrences. The source grammar currently admits adjacent named
calls only. Names in other positions and local values create no edge. `validateNonrecursive` searches
from every declared function, even unused ones. Each breadth-first search
enqueues each canonical function once, with a bound from the actual
signature count, and detects a path back to its root. Declaration order,
body postorder and written child order decide failure order; hash iteration
and display names never decide identity. Calls inside check members do not
create function edges because checks cannot be called.

The raw validation helpers require genuine `check r = .ok t` output. An
arbitrary caller-edited `Typed` record does not establish that precondition.
`checkWalking` runs admission and actual typing on its resolved input before
both validators; `checkWalkingSource` runs the actual source pipeline first.
`checkWalkingTyped` instead requires proof of actual successful producer
output. Successful results preserve the complete typed value, syntax and
references. `StaticFailure.typing` retains existing diagnostics, including
`F0201` and `F0304`. Validation failures are structured data without invented
catalogue codes: coverage includes the owner, missing and repeated IDs; a
cycle includes a closed canonical function path. Missing cases point at the
match keyword, repetitions at the first repeated pattern, and cycles at the
closing call's callee. Metadata failures also carry the actual source span.
Rendering these new failures is future work.

The actual Lean laws `validateWalking_iff`, `walking_success`,
`walking_failure_iff`, `walking_retains` and `walking_deterministic` establish
the executable success/failure boundary, admission, preservation and
uniqueness. They do not prove a universal correspondence between traversal
and the declarative coverage or graph obligations. Direct Plausible and
native tests exercise actual generated programs with successful, partial,
repeated, ill-typed, cyclic and edited-provider variants, requiring explicit
nonzero premise counts and no discards. Finite tests are evidence rather
than recursive universal soundness proofs.

## Focused examples and evidence

This checked program exercises constructor values, positional calls, a
nearest-first let context, if branches, match results and Bool conditions.
The fence runs through Fren1's documentation wrapper; native walking tests
exercise the actual Fren2 checker separately.

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

- [x] Implement actual walking typing and admission in `FrenHirToThir`, with
  genuine admission, erasure, lookup, primitive and determinism proofs.
  The wrapper's `Admitted` is the actual pass's relation.
- [x] Test every expression/operator, annotation/suffix, local/let/sibling
  context, forward call, arity, callability, enum identity, constructor owner,
  branch and member, with independent S1 type/target/span expectations and
  the exact `F0304` code/text/span above.
- [x] Reject edited resolved inputs with deleted/duplicate entries and changed
  role, target, context, scope, constructor owner, source, tape or AST.
- [x] Run direct Plausible on the actual recursive checker with required
  success, typing failure and partial-table admission failure per sample.
  Native census counts admission, signatures, lookup hit/miss and typing
  success/failure without discarded premises.
- [ ] Prove the declarative `HasValue` relation for every successful actual
  traversal (`TypingSound`). The finite native and Plausible cases do not
  establish universal soundness or complete traversal correctness.
- [x] Implement and test `WalkingCoverage` and `WalkingNonrecursive` over
  actual typed syntax, and provide the admitted whole walking static entry.
  S1 retains all four Bool members, including the false `never_red` goal.
- [ ] Prove universal declarative coverage/call-graph correspondence for the
  actual validators; finite tests and executable boundary laws do not prove it.
- [ ] Restate recursive coverage traversal and call-graph laws in Fren once
  recursive syntax and graph reachability can be expressed there.
- [ ] Restate the recursive typing/preservation relation in Fren once Fren2
  supports recursive expression datatypes and recursive judgments over
  their children and binder contexts. State it in Lean over the real pass
  meanwhile; it does not require a copied executable Fren IR.

These existing Spec wrappers remain compatibility documentation checked by
Fren1. They introduce no Fren2 runtime/test module and are outside the
runtime module/header and physical-size guard's inventory.
