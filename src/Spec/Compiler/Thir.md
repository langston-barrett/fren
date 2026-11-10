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
nearest-first indices to levels as `thir.core.levels` states. This is open.
[Algorithmic typing](#algorithmic-typing) states the traversal's rules and
what is proved of them.

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
expression has, and gives no order in which to find them or to report a
failure. This section states the checker's rules as a *bidirectional*
judgment over HIR, the checker's input. *Synthesis* `Σ; Γ ⊢ e ⇒ τ` computes
τ from Σ, Γ and e. *Checking* `Σ; Γ ⊢ e ⇐ τ` takes τ as an input as well.
The language has no subtyping and every form synthesizes, so the two modes
accept the same expressions. They differ in what a failure reports: a
checking premise that fails *blames* its own expression, with the expected
type and the type found.

The Core is the desugared THIR. A HIR expression is typed to a THIR
expression, which keeps every written parenthesis, and
[desugaring](Desugaring.md) removes the parentheses. The declarative rules
type the result of both steps.

| Judgment | Subject | Rule |
| --- | --- | --- |
| `c ⇒ σ`, `c ⇐ σ` as a premise | a child of a layer, already typed | `thir.algorithmic.modes` |
| `Σ; Γ ⊢ l ⇒ τ`, or a blamed premise | one layer, its children's typings given | `thir.algorithmic.synthesis` |
| valid table | a table of typed rows | `thir.algorithmic.table` |
| `Σ; Γ ⊢ e ⇒ τ` | a HIR expression | `thir.algorithmic.judgment` |
| `Σ; Γ ⊢ e ⇐ τ` | the body of a declaration | `thir.algorithmic.declaration` |

### Layers

r[thir.algorithmic.layer] spec::algorithmic::HirF
A *HIR layer* is a Core layer or a parenthesis around one child. As in a
Core layer, a child position holds the child's typing: the context it was
typed in and the type it synthesized.

```fren
pub mod spec::algorithmic

use spec::names::{
    ArmF,
    CoreF,
    Ctx,
    Form,
    ItemId,
    ItemKind,
    LIGHT,
    LIGHT_GREEN,
    LIGHT_RED,
    Sig,
    Symb,
    Ty,
    ctx_ok?,
    entry,
    length,
    lookup,
    one,
    symb_ok?,
    two,
}

use spec::surface::{BinaryOp, Snoc, UnaryOp}
use spec::surface::Snoc::{Empty, Extend}
use spec::thir

use spec::types::{
    F,
    Pair,
    Row,
    SIGNAL,
    SIGNAL_RED,
    SYMB,
    Typing,
    alike?,
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

r[thir.algorithmic.embedding] spec::algorithmic::{Callee, NodeF, embed}
A *HIR node* is one node of the checker's input. It differs from a HIR
layer in three forms. An item in value position is a constructor layer. An
application whose callee is an item is a call layer; an application whose
callee is a local has no layer. A let carries only whether its binder has
the `?` suffix: with the suffix it is the let annotated `Bool`, and without
it the let with no annotation. No HIR node is a let annotated with another
type. Every other node is the layer of the same form with the same children.

```fren
pub enum Callee { Item(ItemId), Local(Int) }

pub enum NodeF<E> {
    BooleanLiteral(Bool),
    IntegerLiteral(Int),
    Local(Int),
    Item(ItemId),
    Apply(Callee, Snoc<E>),
    Unary(UnaryOp, E),
    Binary(BinaryOp, E, E),
    If(E, E, E),
    Let(Bool, E, E),
    Match(E, Snoc<ArmF<E>>),
    Paren(E),
}

pub fn embed<E>(node: NodeF<E>): Option<HirF<E>> := match node {
    NodeF::BooleanLiteral(value?) => Some(HirF::Core(CoreF::BooleanLiteral(value?))),
    NodeF::IntegerLiteral(value) => Some(HirF::Core(CoreF::IntegerLiteral(value))),
    NodeF::Local(level) => Some(HirF::Core(CoreF::Local(level))),
    NodeF::Item(item) => Some(HirF::Core(CoreF::Constructor(item))),
    NodeF::Apply(Callee::Item(item), args) => Some(HirF::Core(CoreF::Call(item, args))),
    NodeF::Apply(Callee::Local(_), _) => None,
    NodeF::Unary(op, operand) => Some(HirF::Core(CoreF::Unary(op, operand))),
    NodeF::Binary(op, left, right) => Some(HirF::Core(CoreF::Binary(op, left, right))),
    NodeF::If(condition, then_branch, else_branch) =>
        Some(HirF::Core(CoreF::If(condition, then_branch, else_branch))),
    NodeF::Let(suffix?, value, body) => Some(
        HirF::Core(
            CoreF::Let(if suffix? then Some(Ty::Boolean) else None, value, body)
        )
    ),
    NodeF::Match(scrutinee, arms) => Some(HirF::Core(CoreF::Match(scrutinee, arms))),
    NodeF::Paren(body) => Some(HirF::Paren(body)),
}
```

### Outcomes and modes

r[thir.algorithmic.outcome] spec::algorithmic::{Premise, Fault, Outcome, outcome_type}
Judging a layer has one *outcome*: the type it synthesizes, or the first
premise that fails, in the order in which its rule lists them, with the
fault found there. A premise is named by its place in the layer: the layer
as a whole, a child, the binder of a let, or the pattern or body of the arm
at a written index, counted from zero. A diagnostic for a blamed premise
points at the expression, binder or pattern in that place.

```fren
pub enum Premise {
    Whole,
    Operand,
    Left,
    Right,
    Argument(Int),
    Binder,
    Condition,
    ElseBranch,
    Scrutinee,
    Pattern(Int),
    Body(Int),
}

pub enum Fault {
    -- The expected type, then the type found.
    Mismatch(Ty, Ty),
    Unbound,
    NotValue,
    NotCallable,
    -- The number of parameters, then the number of arguments.
    Arity(Int, Int),
    NotEnumeration(Ty),
    NoArms,
    NotConstructor,
}

pub enum Outcome { Typed(Ty), Blamed(Premise, Fault) }

pub fn outcome_type(outcome: Outcome): Option<Ty> := match outcome {
    Outcome::Typed(ty) => Some(ty),
    Outcome::Blamed(_, _) => None,
}
```

r[thir.algorithmic.modes] spec::algorithmic::expect_type
A premise on a child of a layer is in one of two modes. A synthesis premise
`c ⇒ σ` reads σ, the type the child synthesized, and cannot fail. A checking
premise `c ⇐ σ` takes σ from the rule and holds when the child synthesized
σ; otherwise the layer's outcome blames the premise with a mismatch of the
expected σ and the type found. `expect_type` states one checking premise,
followed by the outcome of the premises after it.

```fren
pub fn expect_type(premise: Premise, expected: Ty, found: Ty, rest: Outcome): Outcome :=
    if found = expected then rest else Outcome::Blamed(premise, Fault::Mismatch(expected, found))
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

### The rule of each form

Each rule below gives the outcome of one form from its children's types.
Its premises are listed, and fail, in the order written. That each child
was typed in the context its rule prescribes is stated once for all forms,
by `thir.algorithmic.synthesis`.

r[thir.algorithmic.literal]
A Boolean literal synthesizes `Bool` and an integer literal `Int`. Neither
has a premise.

```text
  ────────────────        ───────────────
  Σ; Γ ⊢ b ⇒ Bool         Σ; Γ ⊢ n ⇒ Int
```

r[thir.algorithmic.local] spec::algorithmic::judge_local
A local synthesizes the type at its level in Γ. A level that Γ does not
have is unbound, and blames the local.

```text
  Γ(x) = τ
  ─────────────
  Σ; Γ ⊢ x ⇒ τ
```

```fren
pub fn judge_local(ctx: Ctx, level: Int): Outcome := match lookup(ctx, level) {
    Some(ty) => Outcome::Typed(ty),
    None => Outcome::Blamed(Premise::Whole, Fault::Unbound),
}
```

r[thir.algorithmic.constructor] spec::algorithmic::judge_constructor
An item in value position synthesizes the nominal type of its enumeration
when Σ binds it to a constructor. Any other item is not a value, and blames
the item.

```text
  Σ(c) = constructor of a
  ────────────────────────
  Σ; Γ ⊢ c ⇒ Nominal(a)
```

```fren
pub fn judge_constructor(symb: Symb, item: ItemId): Outcome := match entry(symb, item) {
    Some(ItemKind::Constructor(owner)) => Outcome::Typed(Ty::Nominal(owner)),
    _ => Outcome::Blamed(Premise::Whole, Fault::NotValue),
}
```

r[thir.algorithmic.unary] spec::algorithmic::judge_unary
A unary operation checks its operand against the operator's operand type
and synthesizes that type.

```text
  Σ; Γ ⊢ e ⇐ unary_operand(⊖)
  ──────────────────────────────
  Σ; Γ ⊢ ⊖ e ⇒ unary_operand(⊖)
```

```fren
pub fn judge_unary(op: UnaryOp, operand: Typing): Outcome := expect_type(
    Premise::Operand,
    unary_operand(op),
    operand.ty,
    Outcome::Typed(unary_operand(op))
)
```

r[thir.algorithmic.binary] spec::algorithmic::judge_binary
A binary operation synthesizes its left operand, checks the left and then
the right operand against the operand type that the operator takes from the
left operand's type, and synthesizes the operator's result type. For
equality and inequality the left check cannot fail, so a mismatch blames the
right operand.

```text
  Σ; Γ ⊢ l ⇒ σ
  υ = binary_operand(⊕, σ)
  Σ; Γ ⊢ l ⇐ υ
  Σ; Γ ⊢ r ⇐ υ
  ────────────────────────────────
  Σ; Γ ⊢ l ⊕ r ⇒ binary_output(⊕)
```

```fren
pub fn judge_binary(op: BinaryOp, left: Typing, right: Typing): Outcome := expect_type(
    Premise::Left,
    binary_operand(op, left.ty),
    left.ty,
    expect_type(
        Premise::Right,
        binary_operand(op, left.ty),
        right.ty,
        Outcome::Typed(binary_output(op))
    )
)
```

r[thir.algorithmic.call] spec::algorithmic::{judge_arguments, judge_call}
A call reads its callee's signature from Σ. An item that Σ does not bind to
a function is not callable, and a call with another number of arguments
than the signature has parameters has the wrong arity; both blame the call,
and the arity is decided before any argument is checked. The arguments are
then checked against their parameters' types in written order, and the call
synthesizes the signature's result type.

```text
  Σ(f) = function with parameters σ₀, …, σₙ₋₁ and result τ
  Σ; Γ ⊢ aₖ ⇐ σₖ   (each k < n, in order)
  ────────────────────────────────────────────────────────
  Σ; Γ ⊢ f(a₀, …, aₙ₋₁) ⇒ τ
```

```fren
-- The arguments before the newest are judged first; `rest` is what follows them all.
pub fn judge_arguments(args: Snoc<Typing>, params: Ctx, rest: Outcome): Outcome :=
    match args, params {
        Extend(earlier, arg), Extend(earlier_params, param) => judge_arguments(
            earlier,
            earlier_params,
            expect_type(Premise::Argument(length(earlier)), param, arg.ty, rest)
        ),
        _, _ => rest,
    }

pub fn judge_call(symb: Symb, item: ItemId, args: Snoc<Typing>): Outcome :=
    match entry(symb, item) {
        Some(ItemKind::Function(sig)) =>
            if length(args) != length(sig.params)
            then Outcome::Blamed(
                Premise::Whole,
                Fault::Arity(length(sig.params), length(args))
            )
            else judge_arguments(args, sig.params, Outcome::Typed(sig.result)),
        _ => Outcome::Blamed(Premise::Whole, Fault::NotCallable),
    }
```

r[thir.algorithmic.let] spec::algorithmic::judge_let
A let synthesizes its value, or checks it against the annotation when it
has one, and synthesizes its body in Γ extended by the value's type. A
mismatch with the annotation blames the binder, where the annotation is
written.

```text
  Σ; Γ ⊢ e₁ ⇒ σ                     Σ; Γ ⊢ e₁ ⇐ σ
  Σ; Γ, x : σ ⊢ e₂ ⇒ τ              Σ; Γ, x : σ ⊢ e₂ ⇒ τ
  ─────────────────────────────     ─────────────────────────────────
  Σ; Γ ⊢ let x := e₁ in e₂ ⇒ τ      Σ; Γ ⊢ let x : σ := e₁ in e₂ ⇒ τ
```

```fren
pub fn judge_let(annotation: Option<Ty>, value: Typing, body: Typing): Outcome := match annotation {
    Some(written) => expect_type(Premise::Binder, written, value.ty, Outcome::Typed(body.ty)),
    None => Outcome::Typed(body.ty),
}
```

r[thir.algorithmic.if] spec::algorithmic::judge_if
A conditional checks its condition against `Bool`, synthesizes its first
branch and checks its second branch against the first's type, which it
synthesizes.

```text
  Σ; Γ ⊢ c ⇐ Bool
  Σ; Γ ⊢ e₁ ⇒ τ
  Σ; Γ ⊢ e₂ ⇐ τ
  ────────────────────────────────
  Σ; Γ ⊢ if c then e₁ else e₂ ⇒ τ
```

```fren
pub fn judge_if(condition: Typing, then_branch: Typing, else_branch: Typing): Outcome :=
    expect_type(
        Premise::Condition,
        Ty::Boolean,
        condition.ty,
        expect_type(
            Premise::ElseBranch,
            then_branch.ty,
            else_branch.ty,
            Outcome::Typed(then_branch.ty)
        )
    )
```

r[thir.algorithmic.match] spec::algorithmic::{first_body, judge_arm, judge_arms, judge_match}
A match synthesizes its scrutinee, whose type must be nominal; another type
blames the scrutinee. A match with no arm blames the match. The arms are
then judged in written order. The pattern of an arm must be an item that Σ
binds to a constructor, and is checked against the scrutinee's type, so a
constructor of another enumeration is a mismatch; both blame the pattern.
The body of the first arm synthesizes the match's type, and the body of each
later arm is checked against it.

```text
  Σ; Γ ⊢ s ⇒ Nominal(a)
  Σ(cₖ) = constructor of a   (each arm k, before its body)
  Σ; Γ ⊢ e₀ ⇒ τ
  Σ; Γ ⊢ eₖ ⇐ τ   (each later arm k)
  ───────────────────────────────────────────────
  Σ; Γ ⊢ match s { c₀ ⇒ e₀ | … | cₘ ⇒ eₘ } ⇒ τ
```

```fren
pub fn first_body(arms: Snoc<ArmF<Typing>>): Option<Typing> := match arms {
    Empty => None,
    Extend(earlier, arm) => match first_body(earlier) {
        Some(first) => Some(first),
        None => Some(arm.body),
    },
}

-- One arm at a written index, `common` being the first body's type.
pub fn judge_arm(
    symb: Symb,
    owner: ItemId,
    common: Ty,
    index: Int,
    arm: ArmF<Typing>,
    rest: Outcome
): Outcome := match entry(symb, arm.constructor) {
    Some(ItemKind::Constructor(found)) => expect_type(
        Premise::Pattern(index),
        Ty::Nominal(owner),
        Ty::Nominal(found),
        expect_type(Premise::Body(index), common, arm.body.ty, rest)
    ),
    _ => Outcome::Blamed(Premise::Pattern(index), Fault::NotConstructor),
}

-- The arms before the newest are judged first; `rest` is what follows them all.
pub fn judge_arms(
    symb: Symb,
    owner: ItemId,
    common: Ty,
    arms: Snoc<ArmF<Typing>>,
    rest: Outcome
): Outcome := match arms {
    Empty => rest,
    Extend(earlier, arm) => judge_arms(
        symb,
        owner,
        common,
        earlier,
        judge_arm(symb, owner, common, length(earlier), arm, rest)
    ),
}

pub fn judge_match(symb: Symb, scrutinee: Typing, arms: Snoc<ArmF<Typing>>): Outcome :=
    match scrutinee.ty {
        Ty::Nominal(owner) => match first_body(arms) {
            Some(first) => judge_arms(symb, owner, first.ty, arms, Outcome::Typed(first.ty)),
            None => Outcome::Blamed(Premise::Whole, Fault::NoArms),
        },
        found => Outcome::Blamed(Premise::Scrutinee, Fault::NotEnumeration(found)),
    }
```

r[thir.algorithmic.paren]
A parenthesis synthesizes the type that its body synthesizes. It has no
checking premise.

```text
  Σ; Γ ⊢ e ⇒ τ
  ───────────────
  Σ; Γ ⊢ (e) ⇒ τ
```

r[thir.algorithmic.synthesis] spec::algorithmic::{judge_core, judge_layer, arms_in_context?, placed_core?, placed?, synth_core, synth_layer}
The outcome of a layer is the outcome of the rule of its form. A layer is
*placed* in Γ when each child was typed in the context that its rule
prescribes: the body of a let in Γ extended by the value's type, and every
other child in Γ. `Σ; Γ ⊢ l ⇒ τ` holds for a layer l, its children's typings
given, when l is placed in Γ and its outcome is the type τ. A layer
therefore synthesizes at most one type.

```fren
pub fn judge_core(symb: Symb, ctx: Ctx, form: CoreF<Typing>): Outcome := match form {
    CoreF::BooleanLiteral(_) => Outcome::Typed(Ty::Boolean),
    CoreF::IntegerLiteral(_) => Outcome::Typed(Ty::Integer),
    CoreF::Local(level) => judge_local(ctx, level),
    CoreF::Constructor(item) => judge_constructor(symb, item),
    CoreF::Unary(op, operand) => judge_unary(op, operand),
    CoreF::Binary(op, left, right) => judge_binary(op, left, right),
    CoreF::Call(item, args) => judge_call(symb, item, args),
    CoreF::Let(annotation, value, body) => judge_let(annotation, value, body),
    CoreF::If(condition, then_branch, else_branch) => judge_if(condition, then_branch, else_branch),
    CoreF::Match(scrutinee, arms) => judge_match(symb, scrutinee, arms),
}

pub fn judge_layer(symb: Symb, ctx: Ctx, form: HirF<Typing>): Outcome := match form {
    HirF::Core(core) => judge_core(symb, ctx, core),
    HirF::Paren(body) => Outcome::Typed(body.ty),
}

pub fn arms_in_context?(arms: Snoc<ArmF<Typing>>, ctx: Ctx) := match arms {
    Empty => true,
    Extend(earlier, arm) => arm.body.ctx = ctx and arms_in_context?(earlier, ctx),
}

pub fn placed_core?(ctx: Ctx, form: CoreF<Typing>) := match form {
    CoreF::Unary(_, operand) => operand.ctx = ctx,
    CoreF::Binary(_, left, right) => left.ctx = ctx and right.ctx = ctx,
    CoreF::Call(_, args) => in_context?(args, ctx),
    CoreF::Let(_, value, body) => value.ctx = ctx and body.ctx = Extend(ctx, value.ty),
    CoreF::If(condition, then_branch, else_branch) =>
        condition.ctx = ctx and then_branch.ctx = ctx and else_branch.ctx = ctx,
    CoreF::Match(scrutinee, arms) => scrutinee.ctx = ctx and arms_in_context?(arms, ctx),
    _ => true,
}

pub fn placed?(ctx: Ctx, form: HirF<Typing>) := match form {
    HirF::Core(core) => placed_core?(ctx, core),
    HirF::Paren(body) => body.ctx = ctx,
}

pub fn synth_core(symb: Symb, ctx: Ctx, form: CoreF<Typing>): Option<Ty> := provided(
    placed_core?(ctx, form),
    outcome_type(judge_core(symb, ctx, form))
)

pub fn synth_layer(symb: Symb, ctx: Ctx, form: HirF<Typing>): Option<Ty> := provided(
    placed?(ctx, form),
    outcome_type(judge_layer(symb, ctx, form))
)
```

r[thir.algorithmic.local-callee] spec::algorithmic::judge_node
A HIR node has the outcome of its layer. An application whose callee is a
local has no layer: it is not callable, and blames the application, whatever
its arguments are. For example `x(1)`, with x a local of any type, is
rejected in this way.

```fren
pub fn judge_node(symb: Symb, ctx: Ctx, node: NodeF<Typing>): Outcome := match embed(node) {
    Some(form) => judge_layer(symb, ctx, form),
    None => Outcome::Blamed(Premise::Whole, Fault::NotCallable),
}
```

r[thir.algorithmic.declaration] spec::algorithmic::judge_body
`Σ; Γ ⊢ e ⇐ τ` holds when `Σ; Γ ⊢ e ⇒ τ` does. This is the only checking
rule for an expression, and the body of a declaration is the only expression
whose expected type comes from outside it. The body of a function is checked
against the function's declared result type, in the context of its
parameters in written order, and each member of a check is checked against
`Bool` in the context of the check's parameters. A body that synthesizes
another type blames the body as a whole, with a mismatch of the declared
type and the type found.

```text
  Σ; Γ ⊢ e ⇒ τ
  ─────────────
  Σ; Γ ⊢ e ⇐ τ
```

```fren
pub fn judge_body(expected: Ty, found: Ty): Outcome :=
    expect_type(Premise::Whole, expected, found, Outcome::Typed(expected))
```

r[thir.algorithmic.outcomes] spec::algorithmic::{closed, RED_ARM, FOREIGN_ARM, judged_examples::{literal, unbound, not_value, operand, left, right, equality, arity, argument, not_callable, local_callee, binder, condition, else_branch, scrutinee, no_arms, foreign_pattern, pattern, later_body, paren, body}}
The examples below give one outcome for each fault of each rule, in the
empty context, with every child typed there. They use the Core chapter's
example environment: an enumeration `M::Light` with constructors `Red` and
`Green`, an enumeration `M::Signal` with constructor `Red`, and a function
`M::f` from `Int` to `Int`.

| Expression | Outcome |
| --- | --- |
| `true` | `Bool` |
| `#0` | the local is unbound |
| `M::f` in value position | the item is not a value |
| `-true` | the operand: expected `Int`, found `Bool` |
| `true + 1` | the left operand: expected `Int`, found `Bool` |
| `1 + false` | the right operand: expected `Int`, found `Bool` |
| `1 = false` | the right operand: expected `Int`, found `Bool` |
| `M::f()` | the call: one parameter, no argument |
| `M::f(true)` | argument 0: expected `Int`, found `Bool` |
| `M::Light(1)` | the call: the item is not callable |
| `x(1)`, x a local | the application: not callable |
| `let b? := 1 in b?` | the binder: expected `Bool`, found `Int` |
| `if 1 then 2 else 3` | the condition: expected `Bool`, found `Int` |
| `if true then 1 else false` | the second branch: expected `Int`, found `Bool` |
| `match 1 { M::Light::Red ⇒ 1 }` | the scrutinee: `Int` is not an enumeration |
| a match on `M::Light::Red` with no arm | the match: no arm |
| `match M::Light::Red { M::Signal::Red ⇒ 1 }` | pattern 0: expected `Nominal(M::Light)`, found `Nominal(M::Signal)` |
| `match M::Light::Red { M::f ⇒ 1 }` | pattern 0: not a constructor |
| `match M::Light::Red { M::Light::Red ⇒ 1 \| M::Light::Green ⇒ true }` | body 1: expected `Int`, found `Bool` |
| `(1)` | `Int` |
| a body of type `Int` declared `Bool` | the body: expected `Bool`, found `Int` |

```fren
-- A child typed in the empty context.
pub fn closed(ty: Ty): Typing := Typing { ctx := Empty, ty }

pub const RED_ARM: ArmF<Typing> := ArmF {
    constructor := LIGHT_RED,
    body := closed(Ty::Integer),
}

pub const FOREIGN_ARM: ArmF<Typing> := ArmF {
    constructor := SIGNAL_RED,
    body := closed(Ty::Integer),
}

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc judged_examples(): (holds?) {
    ensure output: holds?
    ensure literal: judge_node(SYMB, Empty, NodeF::BooleanLiteral(true)) = Outcome::Typed(Ty::Boolean)
    ensure unbound: judge_node(SYMB, Empty, NodeF::Local(0)) = Outcome::Blamed(Premise::Whole, Fault::Unbound)
    ensure not_value: judge_node(SYMB, Empty, NodeF::Item(F)) = Outcome::Blamed(Premise::Whole, Fault::NotValue)
    ensure operand: judge_node(SYMB, Empty, NodeF::Unary(UnaryOp::Neg, closed(Ty::Boolean)))
        = Outcome::Blamed(Premise::Operand, Fault::Mismatch(Ty::Integer, Ty::Boolean))
    ensure left: judge_node(
        SYMB,
        Empty,
        NodeF::Binary(BinaryOp::Add, closed(Ty::Boolean), closed(Ty::Integer))
    )
        = Outcome::Blamed(Premise::Left, Fault::Mismatch(Ty::Integer, Ty::Boolean))
    ensure right: judge_node(
        SYMB,
        Empty,
        NodeF::Binary(BinaryOp::Add, closed(Ty::Integer), closed(Ty::Boolean))
    )
        = Outcome::Blamed(Premise::Right, Fault::Mismatch(Ty::Integer, Ty::Boolean))
    ensure equality: judge_node(
        SYMB,
        Empty,
        NodeF::Binary(BinaryOp::Eq, closed(Ty::Integer), closed(Ty::Boolean))
    )
        = Outcome::Blamed(Premise::Right, Fault::Mismatch(Ty::Integer, Ty::Boolean))
    ensure arity: judge_node(SYMB, Empty, NodeF::Apply(Callee::Item(F), Empty))
        = Outcome::Blamed(Premise::Whole, Fault::Arity(1, 0))
    ensure argument: judge_node(
        SYMB,
        Empty,
        NodeF::Apply(Callee::Item(F), one(closed(Ty::Boolean)))
    )
        = Outcome::Blamed(
            Premise::Argument(0),
            Fault::Mismatch(Ty::Integer, Ty::Boolean)
        )
    ensure not_callable: judge_node(
        SYMB,
        Empty,
        NodeF::Apply(Callee::Item(LIGHT), one(closed(Ty::Integer)))
    )
        = Outcome::Blamed(Premise::Whole, Fault::NotCallable)
    ensure local_callee: judge_node(
        SYMB,
        one(Ty::Integer),
        NodeF::Apply(Callee::Local(0), one(closed(Ty::Integer)))
    )
        = Outcome::Blamed(Premise::Whole, Fault::NotCallable)
    ensure binder: judge_node(
        SYMB,
        Empty,
        NodeF::Let(
            true,
            closed(Ty::Integer),
            Typing {
                ctx := one(Ty::Integer),
                ty := Ty::Integer,
            }
        )
    )
        = Outcome::Blamed(Premise::Binder, Fault::Mismatch(Ty::Boolean, Ty::Integer))
    ensure condition: judge_node(
        SYMB,
        Empty,
        NodeF::If(
            closed(Ty::Integer),
            closed(Ty::Integer),
            closed(Ty::Integer)
        )
    )
        = Outcome::Blamed(
            Premise::Condition,
            Fault::Mismatch(Ty::Boolean, Ty::Integer)
        )
    ensure else_branch: judge_node(
        SYMB,
        Empty,
        NodeF::If(
            closed(Ty::Boolean),
            closed(Ty::Integer),
            closed(Ty::Boolean)
        )
    )
        = Outcome::Blamed(
            Premise::ElseBranch,
            Fault::Mismatch(Ty::Integer, Ty::Boolean)
        )
    ensure scrutinee: judge_node(SYMB, Empty, NodeF::Match(closed(Ty::Integer), one(RED_ARM)))
        = Outcome::Blamed(Premise::Scrutinee, Fault::NotEnumeration(Ty::Integer))
    ensure no_arms: judge_node(SYMB, Empty, NodeF::Match(closed(Ty::Nominal(LIGHT)), Empty))
        = Outcome::Blamed(Premise::Whole, Fault::NoArms)
    ensure foreign_pattern: judge_node(
        SYMB,
        Empty,
        NodeF::Match(closed(Ty::Nominal(LIGHT)), one(FOREIGN_ARM))
    )
        = Outcome::Blamed(
            Premise::Pattern(0),
            Fault::Mismatch(Ty::Nominal(LIGHT), Ty::Nominal(SIGNAL))
        )
    ensure pattern: judge_node(
        SYMB,
        Empty,
        NodeF::Match(
            closed(Ty::Nominal(LIGHT)),
            one(
                ArmF {
                    constructor := F,
                    body := closed(Ty::Integer),
                }
            )
        )
    )
        = Outcome::Blamed(Premise::Pattern(0), Fault::NotConstructor)
    ensure later_body: judge_node(
        SYMB,
        Empty,
        NodeF::Match(
            closed(Ty::Nominal(LIGHT)),
            two(
                RED_ARM,
                ArmF {
                    constructor := LIGHT_GREEN,
                    body := closed(Ty::Boolean),
                }
            )
        )
    )
        = Outcome::Blamed(Premise::Body(1), Fault::Mismatch(Ty::Integer, Ty::Boolean))
    ensure paren: judge_node(SYMB, Empty, NodeF::Paren(closed(Ty::Integer))) = Outcome::Typed(Ty::Integer)
    ensure body: judge_body(Ty::Boolean, Ty::Integer)
        = Outcome::Blamed(Premise::Whole, Fault::Mismatch(Ty::Boolean, Ty::Integer))
}
```

### Agreement with the Core, one layer at a time

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

r[thir.algorithmic.sequences] spec::algorithmic::{arguments_judged::{accepted, rejected}, arms_judged::{accepted, rejected}}
Judging a sequence of arguments passes on to what follows exactly when the
Core's premise on the sequence holds: when each argument has its
parameter's type, the outcome is that of what follows, and when the
sequences have one length and some argument has another type, the outcome
is a blame. Likewise for arms whose bodies were typed in Γ: when each
pattern is a constructor of the scrutinee's enumeration and each body has
the common type, the outcome is that of what follows, and otherwise it is a
blame.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc arguments_judged(args: Snoc<Typing>, params: Ctx, rest: Outcome): (holds?) {
    ensure output: holds?
    ensure accepted: when argument_types?(args, params),
        length(args) = length(params) and judge_arguments(args, params, rest) = rest
    ensure rejected: when length(args) = length(params) and not argument_types?(args, params),
        outcome_type(judge_arguments(args, params, rest)) = None
}

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc arms_judged(
    symb: Symb,
    owner: ItemId,
    common: Ty,
    arms: Snoc<ArmF<Typing>>,
    ctx: Ctx,
    rest: Outcome,
): (holds?) {
    ensure output: holds?
    ensure accepted: when arm_patterns?(symb, arms, owner) and arm_bodies?(arms, ctx, common),
        arms_in_context?(arms, ctx) and judge_arms(symb, owner, common, arms, rest) = rest
    ensure rejected: when arms_in_context?(arms, ctx) and not (arm_patterns?(symb, arms, owner) and arm_bodies?(arms, ctx, common)),
        outcome_type(judge_arms(symb, owner, common, arms, rest)) = None
}
```

r[thir.algorithmic.agreement] spec::algorithmic::{layer_agrees::{sound, complete}, call_agrees::{function, other}, match_agrees::exact}
Synthesis agrees with the Core, one layer at a time: a Core layer l
synthesizes τ in Γ exactly when `Σ; Γ ⊢ l ▷ τ` holds. The solver proves
this for every form but a call and a match, and for a call from
`thir.algorithmic.sequences`; the two cases of a call are exhaustive. For a
match the wrapper proves it, from `thir.algorithmic.sequences` and
`thir.algorithmic.first-arm`.

```fren
expect layer_agrees(symb: Symb, ctx: Ctx, form: CoreF<Typing>, ty: Ty) {
    assume other_form: not (form is CoreF::Call(_, _)) and not (form is CoreF::Match(_, _))
    expect sound: when synth_layer(symb, ctx, HirF::Core(form)) = Some(ty), rule?(symb, ctx, form, ty)
    expect complete: when rule?(symb, ctx, form, ty), synth_layer(symb, ctx, HirF::Core(form)) = Some(ty)
}

expect call_agrees(
    symb: Symb,
    ctx: Ctx,
    item: ItemId,
    args: Snoc<Typing>,
    params: Ctx,
    result: Ty,
    ty: Ty,
) {
    call judged := arguments_judged(args, params, Outcome::Typed(result))
    expect function: when entry(symb, item) = Some(ItemKind::Function(Sig { params, result })),
        synth_layer(symb, ctx, HirF::Core(CoreF::Call(item, args))) = Some(ty)
        iff rule?(symb, ctx, CoreF::Call(item, args), ty)
    expect other: when not (entry(symb, item) is Some(ItemKind::Function(_))),
        synth_layer(symb, ctx, HirF::Core(CoreF::Call(item, args))) = None
        and not rule?(symb, ctx, CoreF::Call(item, args), ty)
}

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc match_agrees(symb: Symb, ctx: Ctx, scrutinee: Typing, arms: Snoc<ArmF<Typing>>, ty: Ty): (
    holds?,
) {
    ensure output: holds?
    ensure exact: synth_layer(symb, ctx, HirF::Core(CoreF::Match(scrutinee, arms))) = Some(ty)
        iff rule?(symb, ctx, CoreF::Match(scrutinee, arms), ty)
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

### Tables and expressions

A table of typed rows stands for an expression and its typing, as in the
Core. Desugaring maps a HIR table to a Core table row by row, and the rules
below relate what the two judgments accept.

```text
  HIR table  ───── desugar_rows, row by row ─────▶  Core table
      │                                                 │
  synthesis?                                       derivation?
      ▼                                                 ▼
  Σ; Γ ⊢ e ⇒ τ  ──────── the same Γ and τ ────────  Σ; Γ ⊢ |e| : τ
```

r[thir.algorithmic.table] spec::algorithmic::{HirRow, core_row, desugar_rows, hir_annotate, hir_rows_valid?}
A *HIR table* is a snoc sequence of rows, each a HIR layer whose children
are levels of earlier rows, a context and a type. Its *desugaring* is the
Core table with a row for each of its rows, at the same level and with the
same context and type. The row of a Core layer keeps its layer. The row of a
parenthesis takes the layer of its body's desugared row, and a parenthesis
whose body names no earlier row has no desugaring. A child's typing is read
at its level, which is the same in a table and its desugaring. A HIR table
is valid in Σ when every row's context is well formed and every row's
layer, with each child replaced by its typing, synthesizes the row's type
in the row's context.

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
                Some(form) => synth_layer(symb, row.ctx, form) = Some(row.ty),
                None => false,
            },
            None => false,
        },
}
```

r[thir.algorithmic.rows] spec::algorithmic::desugaring_keeps_rows::same
Desugaring keeps the number of rows. The desugaring of a table with a
parenthesis row therefore has more rows than the smallest Core table for
the same expression. A Core table for the desugaring of an expression that
has a parenthesis therefore need not be the desugaring of a HIR table for
that expression (`thir.algorithmic.example`).

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc desugaring_keeps_rows(rows: Snoc<HirRow>): (holds?) {
    ensure output: holds?
    ensure same: match desugar_rows(rows) {
        Some(core) => length(core) = length(rows),
        None => true,
    }
}
```

r[thir.algorithmic.unfolding]
A row of a HIR table *unfolds* to a HIR expression. The row of a Core layer
unfolds as a row of a Core table does (`types.derivation.unfolding`): to the
expression whose root form is the row's layer, with each child level
replaced by the expression that the row at that level unfolds to. The row
of a parenthesis whose body is the level i unfolds to `(e)`, where e is the
expression that the row at level i unfolds to. A valid table's children name
only earlier rows, so unfolding ends.

r[thir.algorithmic.desugared-unfolding]
Desugaring a table desugars what it unfolds to: when a row of a valid HIR
table unfolds to e, the row at the same level of the table's desugaring
unfolds to `|e|`, the expression e with every parenthesis replaced by its
body (`desugaring.pass.parens`). Fren cannot state unfolding to a tree, so
no procedure states this law. It is open.

r[thir.algorithmic.judgment] spec::algorithmic::{hir_rows_extend?, synthesis?}
`Σ; Γ ⊢ e ⇒ τ` holds when Σ and Γ are well formed and some valid HIR table,
every row of which has a context that extends Γ, has a newest row, its
*root*, with context Γ and type τ that unfolds to e. `synthesis?` checks
that a table is valid in this way with such a root.

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
Desugaring preserves typing: when `synthesis?` accepts a HIR table with root
context Γ and root type τ, the Core's `derivation?` accepts its desugaring
with the same Γ and τ. This lifts `thir.algorithmic.agreement` and
`thir.algorithmic.parens` from one layer to a table, by induction on its
rows.

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

r[thir.algorithmic.reflection] spec::algorithmic::{parens_faithful?, desugaring_reflects::exact}
A HIR table is valid exactly when its desugaring is a valid Core table and
each of its parenthesis rows has the context and type of its body's row.
The second condition is what desugaring forgets: it gives a parenthesis row
the layer of its body's row, and not that row's context and type.

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
    ensure exact: hir_rows_valid?(symb, rows) iff (desugared_valid?(symb, rows) and parens_faithful?(rows))
}
```

r[thir.algorithmic.unfaithful] spec::algorithmic::{UNFAITHFUL, unfaithful_paren::{desugaring_valid, table_invalid, excluded}}
The table `UNFAITHFUL` shows that the second condition of
`thir.algorithmic.reflection` is needed. Its desugaring is a valid Core
table in the empty Σ, and it is not a valid HIR table: the body of its
parenthesis was typed in another context than the parenthesis.

| Row | Layer | Context | Type | Desugared layer |
| --- | --- | --- | --- | --- |
| 0 | `true` | `·, Bool` | `Bool` | `true` |
| 1 | `(#0)` | `·` | `Bool` | `true` |

```fren
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
by row.

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

r[thir.algorithmic.expression-sound] spec::algorithmic::{desugars_alike?, expression_sound::agrees}
Synthesis is sound for an expression, against any Core table for its
desugaring. A HIR table *desugars alike* a Core table when the root of its
desugaring and the root of the Core table unfold alike
(`types.derivation.alike`), whatever the two tables' sharing of rows and
numbers of rows. When `synthesis?` accepts a HIR table with Γ and τ,
`derivation?` accepts a Core table with Γ and υ, and the HIR table desugars
alike the Core table, τ = υ.

```fren
pub fn desugars_alike?(hir: Snoc<HirRow>, core: Snoc<Row>, pairs: Snoc<Pair>) :=
    match desugar_rows(hir) {
        Some(desugared) => alike?(
            desugared,
            length(desugared) - 1,
            core,
            length(core) - 1,
            pairs
        ),
        None => false,
    }

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc expression_sound(
    symb: Symb,
    ctx: Ctx,
    hir: Snoc<HirRow>,
    core: Snoc<Row>,
    pairs: Snoc<Pair>,
    a: Ty,
    b: Ty,
): (holds?) {
    ensure output: holds?
    ensure agrees: when synthesis?(symb, hir, ctx, a) and derivation?(symb, core, ctx, b) and desugars_alike?(hir, core, pairs),
        a = b
}
```

r[thir.algorithmic.expression-unique] spec::algorithmic::{desugarings_alike?, expression_unique::unique}
Synthesis is deterministic for an expression, up to parentheses: when
`synthesis?` accepts two HIR tables in Γ, with types τ and υ, and the roots
of their desugarings unfold alike, τ = υ.

```fren
pub fn desugarings_alike?(left: Snoc<HirRow>, right: Snoc<HirRow>, pairs: Snoc<Pair>) :=
    match desugar_rows(right) {
        Some(core) => desugars_alike?(left, core, pairs),
        None => false,
    }

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc expression_unique(
    symb: Symb,
    ctx: Ctx,
    left: Snoc<HirRow>,
    right: Snoc<HirRow>,
    pairs: Snoc<Pair>,
    a: Ty,
    b: Ty,
): (holds?) {
    ensure output: holds?
    ensure unique: when synthesis?(symb, left, ctx, a) and synthesis?(symb, right, ctx, b) and desugarings_alike?(left, right, pairs),
        a = b
}
```

r[thir.algorithmic.example] spec::algorithmic::{PAREN_TRUE, PAREN_TRUE_DESUGARED, TRUE_CORE, paren_true::{accepted, desugared, preserved, smaller, alike}}
`Σ; · ⊢ (true) ⇒ Bool`, for the empty Σ. The HIR table `PAREN_TRUE` has a
row for the literal and a row for the parenthesis, whose root unfolds to
`(true)`. Its desugaring `PAREN_TRUE_DESUGARED` has the same two rows with
the literal's layer in both, and its root unfolds to `true`. The Core table
`TRUE_CORE` for `true` has one row. It is not the desugaring of a HIR
table for `(true)`, and `PAREN_TRUE` desugars alike it, with both rows of
the desugaring paired with its one row.

| Row | HIR layer | Desugared layer | Context | Type |
| --- | --- | --- | --- | --- |
| 0 | `true` | `true` | `·` | `Bool` |
| 1 | `(#0)` | `true` | `·` | `Bool` |

```fren
pub const PAREN_TRUE: Snoc<HirRow> := two(
    HirRow {
        form := HirF::Core(CoreF::BooleanLiteral(true)),
        ctx := Empty,
        ty := Ty::Boolean,
    },
    HirRow {
        form := HirF::Paren(0),
        ctx := Empty,
        ty := Ty::Boolean,
    }
)

pub const TRUE_CORE: Snoc<Row> := one(
    Row {
        form := CoreF::BooleanLiteral(true),
        ctx := Empty,
        ty := Ty::Boolean,
    }
)

pub const PAREN_TRUE_DESUGARED: Snoc<Row> := Extend(
    TRUE_CORE,
    Row {
        form := CoreF::BooleanLiteral(true),
        ctx := Empty,
        ty := Ty::Boolean,
    }
)

set_option fren.lint.assertions_on_constants "allow" in
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc paren_true(): (holds?) {
    ensure output: holds?
    ensure accepted: synthesis?(Empty, PAREN_TRUE, Empty, Ty::Boolean)
    ensure desugared: desugar_rows(PAREN_TRUE) = Some(PAREN_TRUE_DESUGARED)
    ensure preserved: derivation?(Empty, PAREN_TRUE_DESUGARED, Empty, Ty::Boolean)
    ensure smaller: derivation?(Empty, TRUE_CORE, Empty, Ty::Boolean)
    ensure alike: desugars_alike?(
        PAREN_TRUE,
        TRUE_CORE,
        two(
            Pair { left := 1, right := 0 },
            Pair { left := 0, right := 0 }
        )
    )
}
```

### Open: expressions as trees

The rules above are about tables, and relate two tables for one expression
by a supplied pairing. The two rules below state what remains for
expressions given as trees.

r[thir.algorithmic.tree-lift]
The judgment agrees with the inductive reading of the rules: when Σ and Γ
are well formed, `Σ; Γ ⊢ e ⇒ τ` holds exactly when a finite tree of
instances of the rules of this section concludes it, with one subtree for
each written child of each form, in the context that the rule gives that
child. The well-formedness conditions are part of the reading and do not
follow from a tree, as in `types.judgment.adequacy`: the rule of a Boolean
literal has an instance under any Σ and Γ. Then a HIR expression synthesizes
at most one type in a context, and a traversal that judges each layer after
its children, in the contexts that the rules prescribe, finds a τ with
`Σ; Γ ⊢ e ⇒ τ` or the first blamed premise.

This is open. It rests on four lemmas:

1. Regularity: every row of a table that `synthesis?` accepts has a well
   formed context and a type that Σ declares. For the desugared table this
   is the Core's `types.judgment.regularity`, by
   `thir.algorithmic.preservation`, and a HIR row has the context and type
   of its desugared row.
2. Two HIR tables whose roots unfold to the same expression desugar alike.
   With `thir.algorithmic.expression-unique` this gives the uniqueness of
   the synthesized type. It is not proved.
3. A valid table's root unfolds to exactly one expression, and a tree of
   rule instances concludes its row. The Lean development proves both for
   any layer functor, as `Spec.Tables.Unfolds.unique` and
   `Spec.Tables.Valid.derives`. They are not yet instantiated at HIR layers.
4. Every tree of rule instances has a table. The Lean development proves
   this for any layer functor as `Spec.Tables.Derives.table`, under
   conditions on the rule that the HIR rules are not yet shown to meet.

r[thir.algorithmic.expression-complete]
Synthesis is complete for expressions: when Σ and Γ are well formed and
`Σ; Γ ⊢ |e| : τ` holds in the Core for the desugaring of a HIR expression e,
`Σ; Γ ⊢ e ⇒ τ` holds. This is open. `thir.algorithmic.reflection` does not
give it, since a Core table for `|e|` need not be the desugaring of a HIR
table for e (`thir.algorithmic.example`). The route is by induction on e.
The Core's adequacy theorem
`Spec.Language.Types.judgment_adequate` gives a tree of Core rule instances
for `|e|`, whatever the shape of the given table.
`thir.algorithmic.agreement` turns each of its nodes into an instance of the
synthesis rule of the same form, and `thir.algorithmic.parens` adds an
instance for each parenthesis of e, with the typing of its body. The
result is a tree of synthesis rule instances for e, and
`thir.algorithmic.tree-lift` gives its table.

### The production checker

r[thir.algorithmic.primitive] spec::algorithmic::{unary_tag, binary_tag, value_kind, primitive_unary::{accepts, result}, primitive_binary::{accepts, result}}
The operator types of `thir.algorithmic.operators` are the production
operator decisions. The primitive contracts `thir.primitive.unary` and
`thir.primitive.binary`, which the production `FrenExpr.unary` and
`FrenExpr.binary` implement, accept an operand exactly when it has the
expected type, and return the kind of the result type. Two nominal types
have equal identity atoms exactly when they are equal. The wrapper also
proves, as `Spec.Compiler.Thir.algorithmic_unary_operand`,
`Spec.Compiler.Thir.algorithmic_binary_operand` and
`Spec.Compiler.Thir.algorithmic_binary_output`, that the three functions
are `FrenExpr.unaryOperand`, `FrenExpr.binaryOperand` and
`FrenExpr.binaryResult`, from which `FrenHirToThir.Pass.step` takes each
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

r[thir.algorithmic.step]
`FrenHirToThir.Pass.step` is the production form of the rules of five
forms: a unary operation, a binary operation, a conditional, a let and a
parenthesis. Given that each child of a node was typed, with the type that
the rule's typing of that child has, `step` returns the outcome of the
node's rule: the same type, or a mismatch with the same expected and found
types at the origin of the blamed premise. The operand, the left and right
operands, the condition and the second branch are blamed at the origin of
that child, and the binder of a let at the binder's origin. A production
binder has the annotation `Bool` when it carries the `?` suffix and none
otherwise. Likewise
`FrenHirToThir.Pass.typeBody` checks a typed body against a declared type
as `judge_body` does, and blames the body's origin. The wrapper proves
these as `Spec.Compiler.Thir.step_unary`, `step_binary`, `step_if`,
`step_let`, `step_paren` and `body_checked`. They relate a production type
to a type of this chapter by any injective naming of the nominal types.

r[thir.algorithmic.production]
The rest of the correspondence between `FrenHirToThir.Pass` and the rules
of this section is open. No theorem yet states any of the following.

1. `step` on a local, an item in value position, an application and a
   match returns the outcome of `judge_node`. These need the production
   context, which is nearest first (`thir.core.levels`), and the production
   item environment, whose items are canonical identities and not paths,
   related to Γ and Σ. In the production checker an application whose
   callee is a local is not callable; the arity of a call is decided before
   any argument is typed; and each arm's pattern and body are checked
   before the next arm's.
2. When a child of a node fails, every child before it was typed and every
   check that `step` makes before it types that child passes, `step` fails
   with that child's failure. The production traversal types the children
   of a node in written order and makes each check as soon as the child it
   concerns is typed, and it stops at the first child or check that fails.
   So the failure of a child is reported before a mismatch of a later one,
   and a mismatch of an earlier child before the failure of a later one: in
   `true + e`, `step` blames the left operand and does not type e. The
   rules of this section give the outcome of a layer whose children are all
   typed.
3. The successful production traversal of an expression yields a valid
   HIR table whose root unfolds to it (`thir.algorithmic.tree-lift`), in
   the context that `FrenHirToThir.Pass.typeItem` gives a declaration's
   body.

Erasing the types of the traversal's output gives back its input, as
`thir.result.preservation` requires; the generated cases of the checker's
tests check this on every accepted case.
