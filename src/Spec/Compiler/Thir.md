# THIR and type checking

The typed high-level intermediate representation (THIR) adds value types to
resolved expressions. This chapter specifies
`FrenHirToThir` using the `FrenAst` and `FrenModule.Resolved` APIs.
The pass retains resolved syntax plus typed occurrence data. The
[Language types](../Language/Types.md) chapter supplies the typing rules.

## Shared judgments and pass interface

`Produces input out` means that the actual type checker returned `out`.
`BodyTyping` uses the recursive `FrenHirToThir.HasValue` judgment over the
retained AST, whose clauses are literals, selected locals and constructors,
operators, exact-arity named calls, lets, conditionals and constructor matches.
It is the recursive closure of the [Language local rules](../Language/Types.md#finite-expression-derivations),
with resolver-selected targets and binder tokens retained. The finite Fren
derivation verifies a candidate proof; the production checker infers one.
No equality between those two presentations is assumed as an input.

`ChildContext` states the context of each immediate written child.
`AtContext` is its reflexive structural closure. In particular, a let value
uses the parent context and only its body receives the value's type. A match
arm receives no extra binder. All branches, arguments and unused definitions
are traversed. `OccurrenceTyping` requires a sound entry for each actual
descendant and requires every output entry to have the source context and
meaning. Callable names and their retained parentheses use `HasCallable`.
`OccurrenceInventory` requires the exact structural inventory in postorder:
callee before arguments; condition before then and else branches; let value
before body; scrutinee before arm bodies. Arguments and arms retain written
order. Each visit contributes one entry after its children, including the
root. Pattern paths, binder tokens and punctuation contribute no separate
entry. Neither surplus entries nor a permutation of distinct visits is allowed.

Inventory is local to each `TypedBody`, whose owner and optional member are
constrained by `BodyInventory`. The relation counts structural visits, rather
than distinct expression/context pairs: if an arbitrary AST repeats an equal
subtree, both visits remain. In parsed source, tokens retain file, byte span
and tape position. The lookup API compares the complete expression token
sequence within one body; it does not compare just the first token, rendered
text, context or another body's expressions. No global uniqueness of equal
expression/context pairs is assumed.

`DeclaresBody` derives each body's declared result and nearest-first parameter
context from actual source declarations and resolved signatures. `BodyInventory`
requires exactly one retained entry for every source body, including unused
functions and every check member; it also excludes invented entries.
These declarations are compiled in the [chapter wrapper](Thir.lean), over
actual production types.

**Proof obligations**

r[thir.contract.typing]
Every successful production satisfies `TypePassContract`, including recursive
body and occurrence typing, exact ordered occurrence inventory, signatures
and body inventory, admission and exact retained resolved input.

r[thir.contract.coverage]
On actual successful type-only output, coverage validation holds exactly
when every constructor of the scrutinee owner occurs once in each match.

r[thir.contract.nonrecursion]
On actual successful type-only output, non-recursion validation holds exactly
when the selected function-call graph has no nonempty cycle.

The definitions of `ChildContext`, `AtContext`, `OccurrenceTyping`,
`OccurrenceInventory`, `DeclaresBody`, `BodyInventory`, `TypePassContract`,
`CoverageContract` and `NonrecursionContract` are Lean declarations over
actual production types. They are in the [chapter wrapper](Thir.lean),
between `-- reference begin` and `-- reference end`.

`MatchCoverage` and `Nonrecursive` are semantic relations over actual
source descendants, collected constructors and selected calls. They do not
define correctness as the validator returning true. Their correspondence
contracts are separate from `TypePassContract`; a type-correct partial match
or recursive call does not acquire static acceptance from its typing derivation.
The `body_contract_iff` theorem equates the body component with the existing
`FrenHirToThir.TypingSound` obligation. It does not prove that obligation.
The wrapper proves admission/retention, uniqueness, failure exclusion and the
exact factorization of the public static boundary using actual-code theorems.
`TypePassContract`, including the general occurrence inventory and context
correspondence, remains unproved. The wrapper proves the exact table relation
and actual inference law for integer addition with literal operands, for all
inputs, tokens and contexts. Its raw-output mutation controls check a proved
necessary projection of that relation. These laws and controls do not prove
the universal contract. `CoverageContract` and `NonrecursionContract` also
remain unproved; the correspondence obligations are retained in
[development coverage](../../../docs/fren2-specification-coverage.md).

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
At the public checking boundary, reusing the existing resolver to compare with
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
Every successful typed result satisfies all Language typing rules
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
choice or guessed type is involved. The legacy checker described above
stops at the first error in the module.

## The typed module

The separated type checker, `FrenHirToThir.Pass.typeModule`, takes the
[HIR module](Hir.md) as its whole input and applies the same typing rules.
Its successful result is the THIR module: the same items in declaration
order, each function body and check member an expression whose every node
carries its type and keeps its origin. Parentheses are still nodes. The THIR
module is the whole input of [desugaring](Desugaring.md), which reads nothing
else.

**Proof obligations**

r[thir.module.items]
Each item is typed on its own, against the signatures and constructor owners
of the whole module. Within one item the checker stops at the first error, in
the order parameters, then the body or the members as written. An error in one
item neither hides nor changes the result of another.

r[thir.module.errors]
The result is the THIR module exactly when no item fails. Otherwise it is a
nonempty list holding the first error of each failing item, in declaration
order, and no typed module. Each error names its item, the origin of the
offending node and the reason.

Coverage and non-recursion are not part of this result; the walking
validators below decide them for the legacy checker's output.

## Type correctness, coverage and non-recursion

**Proof obligations**

r[thir.validation.coverage]
The separate `WalkingCoverage` obligation requires every enum constructor
exactly once in each match, rejecting repeated and missing constructors.

r[thir.validation.nonrecursive]
The separate `WalkingNonrecursive` obligation requires the function call
graph to have no self cycle or mutually recursive strongly connected component.

r[thir.validation.boundary]
Whole static acceptance requires admitted input, successful typing,
`WalkingCoverage` and `WalkingNonrecursive`; typing alone establishes only
the first two.

The type-only `check` and `checkSource` decide arity, callability and
constructor owner compatibility. They retain the information the two
validators consume; they do not run those validators.
A nonempty partial match with compatible bodies and a recursive call can
be type correct while still failing coverage and non-recursion validation. No downstream
consumer may assume those checks passed merely because THIR exists.
Neither validation nor typing proves evaluation termination in general,
operator definedness, solver success, evidence quality, or the correctness
of later desugaring and lowering. Value correspondence requires a separate simulation law.

## Coverage and cycle diagnostics

`validateCoverage` visits the actual typed postorder occurrences in every
function and check member, including assumptions and unreachable written
branches. It identifies the scrutinee occurrence by its complete token
sequence, reads its nominal enum type, and takes the constructor inventory
from the admitted declaration scope, filtered by canonical owner. It checks
pattern reference identities in written order, recording every repeated
case and every absent constructor independently of the arm count. The
AST supports only constructor paths as patterns. It has no wildcard
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
These validation failures are structured data; they have no new catalogue codes.

## Examples

This checked program exercises constructor values, positional calls, a
nearest-first let context, if branches, match results and Bool conditions.
Its checked fence exercises the documented source forms.

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
pinned case is assigned by this source domain.

## Correspondence with Core typing

The [Core typing](../Language/Types.md) chapter numbers locals by de Bruijn
level, oldest first; production contexts number them nearest first. The
rules below relate the two and the production operator decisions to the
Core's operator tables.

r[thir.core.levels]
For `0 ≤ i < |Γ|`, the Core entry at level i of Γ is the production entry at
nearest-first index `|Γ| - 1 - i`. The wrapper proves this as `Spec.Compiler.Thir.lookup_nearest`.

r[thir.core.unary]
The production unary operator decision accepts an operand type and returns a
result type exactly when the Core's `unary_type?` relates them, for every
operator and canonical identity. The wrapper proves this as `Spec.Compiler.Thir.core_unary`.

r[thir.core.binary]
The production binary operator decision accepts operand types and returns a
result type exactly when the Core's `binary_type?` relates them, for every
operator and canonical identity. The wrapper proves this as `Spec.Compiler.Thir.core_binary`.

r[thir.core.derivation]
For an admitted resolved expression in the Core domain, a successful
production typing traversal yields exactly a Core derivation of its reported
type in its resolved context, and every such derivation is accepted by that
traversal. The correspondence retains every written occurrence and relates
nearest-first indices to levels as `thir.core.levels` states. This is open.

The following contracts express the production operator decisions with a
finite tag and a separate nominal equality atom.

r[thir.primitive.compatibility] spec::thir::compatible::{meaning, builtin, nominal, distinct, disjoint}
Compatibility compares tags and, only for nominal types, identity atoms.

```fren
pub mod spec
pub mod spec::thir

pub enum ValueKind { Boolean, Integer, Nominal }

-- The production unary and binary operators.
pub enum UnaryTag { Neg, Not }
pub enum BinaryTag { Add, Sub, Mul, Div, Rem, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Iff }

pub proc compatible(left: ValueKind, right: ValueKind, left_id: Int, right_id: Int): (same?) {
    ensure meaning: same? iff left = right and (left != ValueKind::Nominal or left_id = right_id)

    expect builtin: when left = right and left != ValueKind::Nominal, same?
    expect nominal: when left = ValueKind::Nominal and right = left and left_id = right_id, same?
    expect distinct: when left = ValueKind::Nominal and right = left and left_id != right_id, not same?
    expect disjoint: when left != right, not same?
}
```

r[thir.primitive.unary] spec::thir::unary::{meaning, result_type, negate_bool, not_int}
A unary operator accepts exactly its table operand and preserves its tag.

```fren
pub proc unary(op: UnaryTag, operand: ValueKind): (accepted?, result: ValueKind) {
    ensure meaning: accepted? iff (op = UnaryTag::Neg and operand = ValueKind::Integer) or (op = UnaryTag::Not and operand = ValueKind::Boolean)
    ensure result_type: when accepted?, result = operand

    expect negate_bool: when op = UnaryTag::Neg and operand = ValueKind::Boolean, not accepted?
    expect not_int: when op = UnaryTag::Not and operand = ValueKind::Integer, not accepted?
}
```

r[thir.primitive.binary] spec::thir::binary::{meaning, result_type, enum_add, mixed_equality, distinct_enums, same_enum}
A binary operator accepts exactly its table operands and returns its table
tag, including nominal identity comparison for equality.

```fren
pub fn integer_tag?(op: BinaryTag) :=
    op in {
        BinaryTag::Add,
        BinaryTag::Sub,
        BinaryTag::Mul,
        BinaryTag::Div,
        BinaryTag::Rem,
        BinaryTag::Lt,
        BinaryTag::Le,
        BinaryTag::Gt,
        BinaryTag::Ge,
    }

pub fn boolean_tag?(op: BinaryTag) := op in {BinaryTag::And, BinaryTag::Or, BinaryTag::Iff}

pub proc binary(op: BinaryTag, left: ValueKind, right: ValueKind, left_id: Int, right_id: Int): (
    accepted?,
    result: ValueKind,
) {
    ensure meaning: accepted? iff (
        if integer_tag?(op) then left = ValueKind::Integer and right = ValueKind::Integer
        else if boolean_tag?(op) then left = ValueKind::Boolean and right = ValueKind::Boolean
        else left = right and (left != ValueKind::Nominal or left_id = right_id)
        )
    ensure result_type: when accepted?, result = (
        if op in {
            BinaryTag::Add,
            BinaryTag::Sub,
            BinaryTag::Mul,
            BinaryTag::Div,
            BinaryTag::Rem,
        }
        then ValueKind::Integer
        else ValueKind::Boolean
        )

    expect enum_add: when op = BinaryTag::Add and left = ValueKind::Nominal, not accepted?
    expect mixed_equality: when op = BinaryTag::Eq and left != right, not accepted?
    expect distinct_enums: when op = BinaryTag::Ne and left = ValueKind::Nominal and right = left and left_id != right_id, not accepted?
    expect same_enum: when op = BinaryTag::Eq and left = ValueKind::Nominal and right = left and left_id = right_id, accepted? and result = ValueKind::Boolean
}
```
