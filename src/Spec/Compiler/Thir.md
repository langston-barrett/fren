# THIR and type checking

The typed high-level intermediate representation (THIR) adds value types to
resolved expressions. This chapter specifies
`FrenHirToThir` using the `FrenAst` and `FrenModule.Resolved` APIs.
The pass retains resolved syntax plus typed occurrence data. The
[Language types](../Language/Types.md) chapter supplies the typing rules of
the Core, which is the desugared THIR. [Algorithmic typing](#algorithmic-typing)
states the checker's own rules over HIR and relates them to the Core's.

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
Each item is typed alone. Typing an item alone reads that item and, of the
rest of the module, only the functions' signatures and the owner of each
constructor. It reads no other item's body, members or origins. Typing an
item alone gives the typed item or one error. If the item's parameters have
an error, that error is the item's error, whatever its body or members are.

r[thir.module.errors]
The result is a THIR module exactly when every item, typed alone, gives a
typed item. That module has the input's identity and, at each position, the
typed item of the input item at that position. Otherwise the result is a
nonempty list of errors and no typed module. The list holds, in declaration
order, the error that each failing item gives when it is typed alone, and
nothing else. An error in one item therefore neither hides nor changes the
error of another.

The chapter wrapper states both rules without the production module
function. `Alone` types one item against the module's signatures and
constructor owners, and `ModuleResult` is the relation of
`thir.module.errors` between a module and a result. The wrapper proves that
the production checker's result satisfies the relation
(`typed_module_sound`) and that any result that satisfies it is the
production checker's (`typed_module_unique`). It proves that the error of
each item that fails alone is in the list (`item_error_reported`), and that
each listed error is the error of some item typed alone
(`reported_error_alone`). It proves that two modules with the same signatures
and constructor owners give an item the same result
(`alone_reads_signatures`), and that a parameter error is the item's error
(`function_params_first`, `check_params_first`). A property test over
generated modules breaks two or more items at once and requires exactly the
error of each broken item, in declaration order. Two parts are covered only
by tests: that within a check the members are typed in written order and the
first failing member gives the error, and that each error names the origin
of the offending node.

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

The Core is the desugared THIR: THIR keeps every written parenthesis and
the Core has none. The [Core typing](../Language/Types.md) chapter numbers
locals by de Bruijn level, oldest first; production contexts number them
nearest first. The rules below relate the two and the production operator
decisions to the Core's operator tables.

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
For an admitted resolved expression, a successful production typing
traversal yields a derivation of its reported type in its resolved context
for the desugared expression, and every such derivation is accepted by that
traversal. The correspondence retains every written occurrence and relates
nearest-first indices to levels as `thir.core.levels` states. It has two
halves, and neither is proved for expressions.
[Algorithmic typing](#algorithmic-typing) proves a part of the first, for
supplied derivation tables only: a HIR table that the bidirectional rules
accept desugars to a Core table that the declarative rules accept
(`thir.algorithmic.preservation`), and a HIR table whose desugaring the
declarative rules accept is itself accepted, provided each of its
parenthesis rows has the context and type of its body's row
(`thir.algorithmic.reflection`). That every Core derivation of a desugared
expression arises from such a HIR table is open
(`thir.algorithmic.expression-complete`). The second half, that the
production traversal is that judgment, is open, as
`thir.algorithmic.production` states.

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

## Algorithmic typing

The Core's typing rules are declarative: `Σ; Γ ⊢ e : τ` says which types an
expression has, and gives no order in which to find them. This section
states the checker's rules as a *bidirectional* judgment over HIR, the
checker's input. *Synthesis* `Σ; Γ ⊢ e ⇒ τ` computes τ from Σ, Γ and e.
*Checking* `Σ; Γ ⊢ e ⇐ τ` takes τ as an input as well. Each premise of a
rule is in one of the two modes, so a rule says where each expected type
comes from. The language has no subtyping and every form synthesizes, so the
two modes accept the same expressions; they differ in which premise a
mismatch is reported against.

The Core is the desugared THIR. A HIR expression is typed to a THIR
expression, which keeps every written parenthesis, and
[desugaring](Desugaring.md) removes the parentheses. The declarative rules
type the result of both steps. The rules below are sound and complete for
them one layer at a time. For a supplied table of typed rows, they are
related to the declarative rules in both directions, the converse under a
hypothesis on the table's parenthesis rows. Nothing below is proved for an
expression given as a tree; the rules that would do so are stated as open.

```text
                    valid HIR table, root Γ, τ
   HIR rows T  ───────────────────────────▶  typed HIR table T
     │                                            │
     │ erase parentheses                          │ desugar
     ▼                                            ▼
   Core rows |T|  ────────────────────────▶  typed Core table |T|
                    valid Core table, root Γ, τ
```

Here `|T|` is the desugaring of the table T, which has a row for each row of
T with the same context and type. The square is stated for supplied tables,
whose rows already carry their contexts and types. Downwards, desugaring
preserves typing: when T is a valid HIR table, `|T|` is a valid Core table
with the same root (`thir.algorithmic.preservation`). Upwards, when `|T|` is
a valid Core table and each parenthesis row of T has the context and type of
its body's row, T is a valid HIR table (`thir.algorithmic.reflection`); the
hypothesis is needed, as that rule's example shows. The statement for
expressions, that e synthesizes τ in Γ exactly when its desugaring `|e|` has
type τ in Γ in the Core, is not proved: it needs
`thir.algorithmic.tree-lift` and `thir.algorithmic.expression-complete`,
which are open.

r[thir.algorithmic.layer] spec::algorithmic::HirF
A *HIR layer* is a Core layer or a parenthesis around one child. As in a
Core layer, a child position holds the child's typing: the context it was
typed in and the type it synthesized. In HIR a constructor is an item in
value position, a call is an application whose callee is an item, and a let
whose binder has the `?` suffix is a let annotated `Bool`. An application
whose callee is a local has no layer and no type.

```fren
pub mod spec::algorithmic

use spec::names::{ArmF, CoreF, Ctx, Form, ItemKind, Symb, Ty, ctx_ok?, entry, lookup, symb_ok?}
use spec::surface::{BinaryOp, Snoc, UnaryOp}
use spec::surface::Snoc::{Empty, Extend}
use spec::thir

use spec::types::{
    Row,
    Typing,
    annotate,
    argument_types?,
    arm_bodies?,
    arm_patterns?,
    boolean_binary?,
    comparison?,
    derivation?,
    extends?,
    in_context?,
    integer_binary?,
    provided,
    rows_valid?,
    rule?,
    typing_at,
}

pub enum HirF<E> { Core(CoreF<E>), Paren(E) }
```

r[thir.algorithmic.modes] spec::algorithmic::{synthesized?, checked?}
A premise `Σ; Γ ⊢ c ⇒ σ` on a child c holds when c was typed in Γ; σ is then
the type c synthesized. A premise `Σ; Γ ⊢ c ⇐ σ` holds when c was typed in Γ
and synthesized σ.

```fren
pub fn synthesized?(child: Typing, ctx: Ctx) := child.ctx = ctx
pub fn checked?(child: Typing, ctx: Ctx, expected: Ty) := child.ctx = ctx and child.ty = expected
```

r[thir.algorithmic.operators] spec::algorithmic::{unary_operand, binary_operand, binary_output}
A unary operator fixes the type of its operand, which is also its result's.
An arithmetic or comparison operator expects `Int` operands and a Boolean
operator `Bool` operands; equality and inequality expect the type that the
left operand synthesized. Arithmetic returns an `Int` and every other binary
operator a `Bool`.

```fren
pub fn unary_operand(op: UnaryOp): Ty := match op {
    UnaryOp::Neg => Ty::Integer,
    UnaryOp::Not => Ty::Boolean,
}

pub fn binary_operand(op: BinaryOp, left: Ty): Ty :=
    if integer_binary?(op) or comparison?(op) then Ty::Integer
    else if boolean_binary?(op) then Ty::Boolean
    else left

pub fn binary_output(op: BinaryOp): Ty := if integer_binary?(op) then Ty::Integer else Ty::Boolean
```

r[thir.algorithmic.synthesis] spec::algorithmic::{first_body, value_typed?, synth_core, synth_layer}
Synthesis of one layer, its children's typings given:

```text
  ───────────────   ───────────────   Γ(x) = τ        Σ(c) = constructor of a
  Σ; Γ ⊢ b ⇒ Bool   Σ; Γ ⊢ n ⇒ Int    ─────────────   ────────────────────────
                                      Σ; Γ ⊢ x ⇒ τ    Σ; Γ ⊢ c ⇒ Nominal(a)

  Σ; Γ ⊢ e ⇐ unary_operand(⊖)         Σ; Γ ⊢ l ⇒ σ   υ = binary_operand(⊕, σ)
  ──────────────────────────────      Σ; Γ ⊢ l ⇐ υ   Σ; Γ ⊢ r ⇐ υ
  Σ; Γ ⊢ ⊖ e ⇒ unary_operand(⊖)       ─────────────────────────────────────────
                                      Σ; Γ ⊢ l ⊕ r ⇒ binary_output(⊕)

  Σ(f) = function with parameters σ₀, …, σₙ₋₁ and result τ
  Σ; Γ ⊢ aₖ ⇐ σₖ   (each k < n)
  ────────────────────────────────────────────────────────
  Σ; Γ ⊢ f(a₀, …, aₙ₋₁) ⇒ τ

  Σ; Γ ⊢ e₁ ⇒ σ   Σ; Γ, x : σ ⊢ e₂ ⇒ τ     Σ; Γ ⊢ e₁ ⇐ σ   Σ; Γ, x : σ ⊢ e₂ ⇒ τ
  ─────────────────────────────────────    ─────────────────────────────────────
  Σ; Γ ⊢ let x := e₁ in e₂ ⇒ τ             Σ; Γ ⊢ let x : σ := e₁ in e₂ ⇒ τ

  Σ; Γ ⊢ c ⇐ Bool   Σ; Γ ⊢ e₁ ⇒ τ   Σ; Γ ⊢ e₂ ⇐ τ      Σ; Γ ⊢ e ⇒ τ
  ─────────────────────────────────────────────────    ───────────────
  Σ; Γ ⊢ if c then e₁ else e₂ ⇒ τ                      Σ; Γ ⊢ (e) ⇒ τ

  Σ; Γ ⊢ s ⇒ Nominal(a)   Σ(cₖ) = constructor of a   (each arm k)
  Σ; Γ ⊢ e₀ ⇒ τ   Σ; Γ ⊢ eₖ ⇐ τ   (each later arm k)
  ─────────────────────────────────────────────────────────────
  Σ; Γ ⊢ match s { c₀ ⇒ e₀ | … | cₘ ⇒ eₘ } ⇒ τ
```

A local, a constructor and a call read their types from Γ and Σ. A call
checks each argument against its parameter's type, and there are as many
arguments as parameters. A let synthesizes its value, or checks it against
the annotation, and synthesizes its body in the extended context. A
conditional synthesizes its first branch and checks the second against it.
A match has at least one arm; the body of the first written arm synthesizes
and each later body is checked against that type. A parenthesis synthesizes
what its body does. `synth_layer` returns the synthesized type, or `None`
when a premise fails.

```fren
pub fn first_body(arms: Snoc<ArmF<Typing>>): Option<Typing> := match arms {
    Empty => None,
    Extend(earlier, arm) => match first_body(earlier) {
        Some(first) => Some(first),
        None => Some(arm.body),
    },
}

pub fn value_typed?(annotation: Option<Ty>, value: Typing, ctx: Ctx) := match annotation {
    Some(written) => checked?(value, ctx, written),
    None => synthesized?(value, ctx),
}

pub fn synth_core(symb: Symb, ctx: Ctx, form: CoreF<Typing>): Option<Ty> := match form {
    CoreF::BooleanLiteral(_) => Some(Ty::Boolean),
    CoreF::IntegerLiteral(_) => Some(Ty::Integer),
    CoreF::Local(level) => lookup(ctx, level),
    CoreF::Constructor(item) => match entry(symb, item) {
        Some(ItemKind::Constructor(owner)) => Some(Ty::Nominal(owner)),
        _ => None,
    },
    CoreF::Unary(op, operand) => provided(
        checked?(operand, ctx, unary_operand(op)),
        Some(unary_operand(op))
    ),
    CoreF::Binary(op, left, right) => provided(
        synthesized?(left, ctx)
            and checked?(left, ctx, binary_operand(op, left.ty))
            and checked?(right, ctx, binary_operand(op, left.ty)),
        Some(binary_output(op))
    ),
    CoreF::Call(item, args) => match entry(symb, item) {
        Some(ItemKind::Function(sig)) => provided(
            in_context?(args, ctx) and argument_types?(args, sig.params),
            Some(sig.result)
        ),
        _ => None,
    },
    CoreF::Let(annotation, value, body) => provided(
        value_typed?(annotation, value, ctx) and synthesized?(body, Extend(ctx, value.ty)),
        Some(body.ty)
    ),
    CoreF::If(condition, then_branch, else_branch) => provided(
        checked?(condition, ctx, Ty::Boolean)
            and synthesized?(then_branch, ctx)
            and checked?(else_branch, ctx, then_branch.ty),
        Some(then_branch.ty)
    ),
    CoreF::Match(scrutinee, arms) => match scrutinee.ty, first_body(arms) {
        Ty::Nominal(owner), Some(first) => provided(
            synthesized?(scrutinee, ctx)
                and arm_patterns?(symb, arms, owner)
                and arm_bodies?(arms, ctx, first.ty),
            Some(first.ty)
        ),
        _, _ => None,
    },
}

pub fn synth_layer(symb: Symb, ctx: Ctx, form: HirF<Typing>): Option<Ty> := match form {
    HirF::Core(core) => synth_core(symb, ctx, core),
    HirF::Paren(body) => provided(synthesized?(body, ctx), Some(body.ty)),
}
```

r[thir.algorithmic.checking] spec::algorithmic::{check_layer?, modes::switch, modes::unique}
A layer checks against τ when it synthesizes τ. This is the only checking
rule, so a layer checks against at most one type.

```text
  Σ; Γ ⊢ e ⇒ τ
  ─────────────
  Σ; Γ ⊢ e ⇐ τ
```

```fren
pub fn check_layer?(symb: Symb, ctx: Ctx, form: HirF<Typing>, expected: Ty) :=
    synth_layer(symb, ctx, form) = Some(expected)

expect modes(symb: Symb, ctx: Ctx, form: HirF<Typing>, a: Ty, b: Ty) {
    expect switch: check_layer?(symb, ctx, form, a) iff synth_layer(symb, ctx, form) = Some(a)
    expect unique: when check_layer?(symb, ctx, form, a) and check_layer?(symb, ctx, form, b), a = b
}
```

r[thir.algorithmic.sound] spec::algorithmic::layer_sound::sound
Synthesis is sound for the Core, one layer at a time: when a Core layer
synthesizes τ, `Σ; Γ ⊢ l ▷ τ` holds.

```fren
expect layer_sound(symb: Symb, ctx: Ctx, form: CoreF<Typing>, ty: Ty) {
    expect sound: when synth_layer(symb, ctx, HirF::Core(form)) = Some(ty), rule?(symb, ctx, form, ty)
}
```

r[thir.algorithmic.first-arm] spec::algorithmic::{first_typed?, first_arm::typed}
When a match has an arm and every arm body is typed in Γ at τ, its first
written body is typed in Γ at τ.

```fren
pub fn first_typed?(arms: Snoc<ArmF<Typing>>, ctx: Ctx, ty: Ty) :=
    arms = Empty or not arm_bodies?(arms, ctx, ty) or first_body(arms) = Some(Typing { ctx, ty })

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc first_arm(arms: Snoc<ArmF<Typing>>, ctx: Ctx, ty: Ty): (holds?) {
    ensure output: holds?
    ensure typed: first_typed?(arms, ctx, ty)
}
```

r[thir.algorithmic.complete] spec::algorithmic::layer_complete::complete
Synthesis is complete for the Core, one layer at a time: when
`Σ; Γ ⊢ l ▷ τ` holds, the layer l synthesizes τ. The solver uses
`thir.algorithmic.first-arm` for a match, as the assumption below.

```fren
expect layer_complete(symb: Symb, ctx: Ctx, form: CoreF<Typing>, ty: Ty) {
    assume first_arm: match form {
        CoreF::Match(_, arms) => first_typed?(arms, ctx, ty),
        _ => true,
    }
    expect complete: when rule?(symb, ctx, form, ty), synth_layer(symb, ctx, HirF::Core(form)) = Some(ty)
}
```

r[thir.algorithmic.parens] spec::algorithmic::paren_layer::transparent
A parenthesis has no Core layer: it desugars to its body. It synthesizes τ
in Γ exactly when its body was typed in Γ at τ, so the typing of the
parenthesis is the typing of what it desugars to.

```fren
expect paren_layer(symb: Symb, ctx: Ctx, body: Typing, ty: Ty) {
    expect transparent: synth_layer(symb, ctx, HirF::Paren(body)) = Some(ty) iff body = Typing { ctx, ty }
}
```

r[thir.algorithmic.table] spec::algorithmic::{HirRow, core_row, desugar_rows, hir_annotate, hir_rows_valid?}
A *HIR table* is a snoc sequence of rows, each a HIR layer whose children
are levels of earlier rows, a context and a type. Its *desugaring* is the
Core table with a row for each of its rows, at the same level and with the
same context and type. The row of a Core layer keeps its layer. The row of a
parenthesis takes the layer of its body's desugared row, so it unfolds to
what the body's row unfolds to, and a parenthesis whose body names no
earlier row has no desugaring. A child's typing is read at its level, which
is the same in a table and its desugaring. A HIR table is valid in Σ when
every row's context is well formed and every row's layer, with each child
replaced by its typing, checks against the row's type in the row's context.

```fren
pub struct HirRow { form: HirF<Int>, ctx: Ctx, ty: Ty }

-- The Core row at the level of a HIR row: a layer with that row's context and type.
pub fn core_row(form: Form, row: HirRow): Row := Row { form, ctx := row.ctx, ty := row.ty }

pub fn desugar_rows(rows: Snoc<HirRow>): Option<Snoc<Row>> := match rows {
    Empty => Some(Empty),
    Extend(earlier, row) => match desugar_rows(earlier) {
        Some(core) => match row.form {
            HirF::Core(form) => Some(Extend(core, core_row(form, row))),
            HirF::Paren(body) => match lookup(core, body) {
                Some(desugared) => Some(Extend(core, core_row(desugared.form, row))),
                None => None,
            },
        },
        None => None,
    },
}

pub fn hir_annotate(core: Snoc<Row>, form: HirF<Int>): Option<HirF<Typing>> := match form {
    HirF::Core(layer) => match annotate(core, layer) {
        Some(typed) => Some(HirF::Core(typed)),
        None => None,
    },
    HirF::Paren(body) => match typing_at(core, body) {
        Some(typed) => Some(HirF::Paren(typed)),
        None => None,
    },
}

pub fn hir_rows_valid?(symb: Symb, rows: Snoc<HirRow>) := match rows {
    Empty => true,
    Extend(earlier, row) =>
        hir_rows_valid?(symb, earlier)
        and ctx_ok?(symb, row.ctx)
        and match desugar_rows(earlier) {
            Some(core) => match hir_annotate(core, row.form) {
                Some(form) => check_layer?(symb, row.ctx, form, row.ty),
                None => false,
            },
            None => false,
        },
}
```

r[thir.algorithmic.judgment] spec::algorithmic::{hir_rows_extend?, synthesis?}
`Σ; Γ ⊢ e ⇒ τ` holds when Σ and Γ are well formed and some valid HIR table,
every row of which has a context that extends Γ, has a newest row with
context Γ and type τ that unfolds to e. `Σ; Γ ⊢ e ⇐ τ` holds when
`Σ; Γ ⊢ e ⇒ τ` does. `synthesis?` checks that a supplied table is valid in
this way with such a root. It takes every row's context and type as inputs
and does not check that the root unfolds to e: this chapter defines no
unfolding of a HIR table, and the rules below are about tables for that
reason (`thir.algorithmic.tree-lift`).

```fren
pub fn hir_rows_extend?(rows: Snoc<HirRow>, base: Ctx) := match rows {
    Empty => true,
    Extend(earlier, row) => extends?(row.ctx, base) and hir_rows_extend?(earlier, base),
}

pub fn synthesis?(symb: Symb, rows: Snoc<HirRow>, ctx: Ctx, ty: Ty) :=
    symb_ok?(symb)
    and ctx_ok?(symb, ctx)
    and hir_rows_valid?(symb, rows)
    and hir_rows_extend?(rows, ctx)
    and match rows {
        Empty => false,
        Extend(_, root) => root.ctx = ctx and root.ty = ty,
    }
```

r[thir.algorithmic.preservation] spec::algorithmic::{desugared_valid?, desugared_derivation?, desugaring_preserves::typed}
Desugaring preserves the typing of a table: when `synthesis?` accepts a HIR
table with root context Γ and root type τ, the Core's `derivation?` accepts
its desugaring with the same Γ and τ. This lifts `thir.algorithmic.sound`
and `thir.algorithmic.parens` from one layer to a supplied table, by
induction on its rows. That the desugared table's root unfolds to the
desugaring of the expression that the HIR table types is part of the open
`thir.algorithmic.tree-lift`.

```fren
pub fn desugared_valid?(symb: Symb, rows: Snoc<HirRow>) := match desugar_rows(rows) {
    Some(core) => rows_valid?(symb, core),
    None => false,
}

pub fn desugared_derivation?(symb: Symb, rows: Snoc<HirRow>, ctx: Ctx, ty: Ty) :=
    match desugar_rows(rows) {
        Some(core) => derivation?(symb, core, ctx, ty),
        None => false,
    }

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc desugaring_preserves(symb: Symb, rows: Snoc<HirRow>, ctx: Ctx, ty: Ty): (holds?) {
    ensure output: holds?
    ensure typed: when synthesis?(symb, rows, ctx, ty), desugared_derivation?(symb, rows, ctx, ty)
}
```

r[thir.algorithmic.reflection] spec::algorithmic::{parens_faithful?, desugaring_reflects::typed, UNFAITHFUL, unfaithful_paren::{desugaring_valid, table_invalid, excluded}}
Desugaring reflects typing: a HIR table is valid when its desugaring is a
valid Core table and each parenthesis row has the context and type of its
body's row. With `thir.algorithmic.preservation` this relates a supplied HIR
table to its desugaring in both directions, the converse only under that
hypothesis on the parenthesis rows. This lifts `thir.algorithmic.complete`
and `thir.algorithmic.parens`.

The hypothesis is needed, because desugaring gives a parenthesis row the
layer of its body's row and forgets that row's context and type. In the
table `UNFAITHFUL`, row 0 is the literal `true` in the context `·, Bool` and
row 1 is a parenthesis around row 0 in the empty context. Its desugaring has
the literal in both rows and is a valid Core table, but the parenthesis row
is not valid, since its body was typed in another context. The procedure
`unfaithful_paren` states this for the empty Σ, and the wrapper proves it by
evaluation.

```fren
pub fn parens_faithful?(rows: Snoc<HirRow>) := match rows {
    Empty => true,
    Extend(earlier, row) =>
        parens_faithful?(earlier)
        and match row.form, desugar_rows(earlier) {
            HirF::Paren(body), Some(core) =>
                typing_at(core, body) = Some(Typing { ctx := row.ctx, ty := row.ty }),
            _, _ => true,
        },
}

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc desugaring_reflects(symb: Symb, rows: Snoc<HirRow>): (holds?) {
    ensure output: holds?
    ensure typed: when parens_faithful?(rows) and desugared_valid?(symb, rows), hir_rows_valid?(symb, rows)
}

pub const UNFAITHFUL: Snoc<HirRow> := Extend(
    Extend(
        Empty,
        HirRow {
            form := HirF::Core(CoreF::BooleanLiteral(true)),
            ctx := Extend(Empty, Ty::Boolean),
            ty := Ty::Boolean,
        }
    ),
    HirRow {
        form := HirF::Paren(0),
        ctx := Empty,
        ty := Ty::Boolean,
    }
)

set_option fren.lint.assertions_on_constants "allow" in
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc unfaithful_paren(): (holds?) {
    ensure output: holds?
    ensure desugaring_valid: desugared_valid?(Empty, UNFAITHFUL)
    ensure table_invalid: not hir_rows_valid?(Empty, UNFAITHFUL)
    ensure excluded: not parens_faithful?(UNFAITHFUL)
}
```

r[thir.algorithmic.unique] spec::algorithmic::{hir_same_shape?, synthesis_unique::equal}
Synthesis is deterministic for a table: two valid HIR tables with the same
layers and contexts, row by row, are equal, and so have the same types row
by row. This lifts the `unique` expectation of `thir.algorithmic.checking`.

```fren
pub fn hir_same_shape?(left: Snoc<HirRow>, right: Snoc<HirRow>) := match left, right {
    Empty, Empty => true,
    Extend(left_earlier, l), Extend(right_earlier, r) =>
        l.form = r.form and l.ctx = r.ctx and hir_same_shape?(left_earlier, right_earlier),
    _, _ => false,
}

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc synthesis_unique(symb: Symb, left: Snoc<HirRow>, right: Snoc<HirRow>): (holds?) {
    ensure output: holds?
    ensure equal: when hir_rows_valid?(symb, left) and hir_rows_valid?(symb, right) and hir_same_shape?(left, right),
        left = right
}
```

r[thir.algorithmic.decidable]
Verifying a supplied table is decidable and deterministic. Each of
`synth_layer`, `check_layer?`, `hir_rows_valid?` and `synthesis?` is a total
function, so evaluating it decides the premise it states: no rule guesses a
type. A layer has at most one synthesized type because `synth_layer` is a
function, and two valid tables with the same layers and contexts have the
same types by `thir.algorithmic.unique`. `synthesis?` takes every row's
context and type as inputs, so this decides whether a given table is a
derivation. It does not decide whether an expression has a typing, which
needs a procedure that builds the table; that is
`thir.algorithmic.inference`, which is open. Whether a tree, as opposed to a
table, has a unique type is the Core chapter's
`types.derivation.unique-expression` question and is not settled here.

### Open: expressions

The rules above relate supplied tables. The three rules below state what
would carry them to expressions given as trees. None is proved, and no Fren
definition states them yet.

r[thir.algorithmic.tree-lift]
A HIR expression e has a HIR table in a context Γ that is built bottom-up:
its rows are e's subexpressions in postorder, each in the context that the
rule of its parent prescribes, and each row's type is what `synth_layer`
synthesizes from its children's rows. `Σ; Γ ⊢ e ⇒ τ` holds exactly when
this table exists and its root has type τ, and the desugaring of this table
unfolds to the desugaring `|e|` of the expression
(`desugaring.pass.parens`). This is open: the chapter defines no
construction of a table from a tree and no unfolding of a HIR table.

r[thir.algorithmic.expression-complete]
Synthesis is complete for expressions: when `Σ; Γ ⊢ |e| : τ` holds in the
Core for the desugaring of a HIR expression e, `Σ; Γ ⊢ e ⇒ τ` holds. This
is open. `thir.algorithmic.reflection` gives it only for a supplied HIR
table whose parenthesis rows have the contexts and types of their bodies'
rows; it remains to show that every Core table for `|e|` is the desugaring
of such a HIR table for e, which needs `thir.algorithmic.tree-lift` and the
Core chapter's `types.derivation.unique-expression`.

r[thir.algorithmic.inference]
An expression's typing is decidable: an algorithm, given Σ, Γ and a HIR
expression e, finds the τ with `Σ; Γ ⊢ e ⇒ τ` or reports that there is
none, by inference that builds e's table as `thir.algorithmic.tree-lift`
describes. This is open, as is the Core's `types.judgment.decidability`.

### The production checker

r[thir.algorithmic.primitive] spec::algorithmic::{unary_tag, binary_tag, value_kind, primitive_unary::{accepts, result}, primitive_binary::{accepts, result}}
The operator modes are the production operator decisions. The primitive
contracts `thir.primitive.unary` and `thir.primitive.binary`, which the
production `FrenExpr.unary` and `FrenExpr.binary` implement, accept an
operand exactly when it has the type `thir.algorithmic.operators` expects,
and return the kind of the type it gives. Two nominal types have equal
identity atoms exactly when they are equal. The wrapper also proves, as
`Spec.Compiler.Thir.algorithmic_unary_operand`,
`Spec.Compiler.Thir.algorithmic_binary_operand` and
`Spec.Compiler.Thir.algorithmic_binary_output`, that the three mode tables
are the functions `FrenExpr.unaryOperand`, `FrenExpr.binaryOperand` and
`FrenExpr.binaryResult` from which `FrenHirToThir.Pass.step` takes each
expected type.

```fren
pub fn unary_tag(op: UnaryOp): thir::UnaryTag := match op {
    UnaryOp::Neg => thir::UnaryTag::Neg,
    UnaryOp::Not => thir::UnaryTag::Not,
}

pub fn binary_tag(op: BinaryOp): thir::BinaryTag := match op {
    BinaryOp::Add => thir::BinaryTag::Add,
    BinaryOp::Sub => thir::BinaryTag::Sub,
    BinaryOp::Mul => thir::BinaryTag::Mul,
    BinaryOp::Div => thir::BinaryTag::Div,
    BinaryOp::Rem => thir::BinaryTag::Rem,
    BinaryOp::Eq => thir::BinaryTag::Eq,
    BinaryOp::Ne => thir::BinaryTag::Ne,
    BinaryOp::Lt => thir::BinaryTag::Lt,
    BinaryOp::Le => thir::BinaryTag::Le,
    BinaryOp::Gt => thir::BinaryTag::Gt,
    BinaryOp::Ge => thir::BinaryTag::Ge,
    BinaryOp::And => thir::BinaryTag::And,
    BinaryOp::Or => thir::BinaryTag::Or,
    BinaryOp::Iff => thir::BinaryTag::Iff,
}

pub fn value_kind(ty: Ty): thir::ValueKind := match ty {
    Ty::Boolean => thir::ValueKind::Boolean,
    Ty::Integer => thir::ValueKind::Integer,
    Ty::Nominal(_) => thir::ValueKind::Nominal,
}

expect primitive_unary(op: UnaryOp, operand: Ty) {
    call decision := thir::unary(unary_tag(op), value_kind(operand))
    expect accepts: decision.accepted? iff operand = unary_operand(op)
    expect result: when decision.accepted?, decision.result = value_kind(unary_operand(op))
}

expect primitive_binary(op: BinaryOp, left: Ty, right: Ty, left_id: Int, right_id: Int) {
    assume identity: when value_kind(left) = thir::ValueKind::Nominal and value_kind(right) = thir::ValueKind::Nominal,
        (left_id = right_id) iff (left = right)
    call decision := thir::binary(
        binary_tag(op),
        value_kind(left),
        value_kind(right),
        left_id,
        right_id,
    )
    expect accepts: decision.accepted? iff (left = binary_operand(op, left) and right = binary_operand(op, left))
    expect result: when decision.accepted?, decision.result = value_kind(binary_output(op))
}
```

r[thir.algorithmic.production]
`FrenHirToThir.Pass.step` is the production form of `synth_layer`: it runs a
layer's children in written order, takes each expected type from the modes
above, and annotates the layer with the type it synthesized. Erasing the
types of its output gives back its input, as `thir.result.preservation` requires; the
generated cases of the checker's tests check this on every accepted case.
Three differences of representation separate `step` from `synth_layer`:
production contexts are nearest first (`thir.core.levels`), production
items are canonical identities rather than paths, and a production `let`
carries a `?` suffix where the Core carries an annotation. No theorem yet
states that `step` accepts a layer exactly when `synth_layer` does, for
calls, matches, constructors, locals and `let` in particular, nor that the
production traversal of a tree yields a valid HIR table
(`thir.algorithmic.tree-lift`). Both are open.
