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
actual production types; the source audit checks this displayed block against it.

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

```lean
/-- Immediate written children and their exact lexical type contexts. -/
inductive ChildContext (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr → FrenModule.TypeContext → FrenAst.Expr → Prop where
  | paren : ChildContext r sigs ctx (.paren o e c) ctx e
  | unary : ChildContext r sigs ctx (.unary tok op e) ctx e
  | binaryLeft : ChildContext r sigs ctx (.binary a tok op b) ctx a
  | binaryRight : ChildContext r sigs ctx (.binary a tok op b) ctx b
  | callee : ChildContext r sigs ctx (.call f o args commas c) ctx f
  | argument : e ∈ args.toList → ChildContext r sigs ctx (.call f o args commas c) ctx e
  | condition : ChildContext r sigs ctx (.ifE i b t yes e no) ctx b
  | thenBranch : ChildContext r sigs ctx (.ifE i b t yes e no) ctx yes
  | elseBranch : ChildContext r sigs ctx (.ifE i b t yes e no) ctx no
  | letValue : ChildContext r sigs ctx (.letE l name assign value i body) ctx value
  | letBody : FrenHirToThir.HasValue r sigs ctx value vt →
      ChildContext r sigs ctx (.letE l name assign value i body) ((name, vt) :: ctx) body
  | scrutinee : ChildContext r sigs ctx (.matchE m scrutinee o arms c) ctx scrutinee
  | armBody : arm ∈ arms.toList →
      ChildContext r sigs ctx (.matchE m scrutinee o arms c) ctx arm.2.2.1

/-- Reflexive structural closure, with context changes carried at every step. -/
inductive AtContext (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr → FrenModule.TypeContext → FrenAst.Expr → Prop where
  | root : AtContext r sigs ctx e ctx e
  | child : AtContext r sigs rootCtx root ctx parent →
      ChildContext r sigs ctx parent childCtx childExpr →
      AtContext r sigs rootCtx root childCtx childExpr

/-- The actual successful type-only producer, rather than a supplied verdict. -/
def Produces (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  FrenHirToThir.check input = .ok out

/-- The recursive body judgment is over the retained production AST. -/
def BodyTyping (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList,
    FrenHirToThir.HasValue input out.signatures body.context body.expression body.type

/-- Callable meaning propagates through retained callee parentheses. -/
inductive HasCallable (input : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr → FrenModule.Signature → Prop where
  | name : FrenHirToThir.Selects input ctx path .expression (.item sig.id) →
      FrenHirToThir.signatureAt sigs sig.id = some sig →
      HasCallable input sigs ctx (.name path) sig
  | paren : HasCallable input sigs ctx e sig →
      HasCallable input sigs ctx (.paren o e c) sig

def OccurrenceMeaning (input : FrenModule.Resolved) (sigs : Array FrenModule.Signature)
    (occurrence : FrenModule.TypedOccurrence) : Prop :=
  match occurrence.type with
  | .value ty => FrenHirToThir.HasValue input sigs occurrence.context occurrence.expression ty
  | .callable sig => HasCallable input sigs occurrence.context occurrence.expression sig

/-- Ordered immediate children. Pattern paths and binder tokens are not expressions. -/
inductive WrittenChildren (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr →
      List (FrenModule.TypeContext × FrenAst.Expr) → Prop where
  | bool : WrittenChildren r sigs ctx (.bool t b) []
  | integer : WrittenChildren r sigs ctx (.integer t n) []
  | name : WrittenChildren r sigs ctx (.name p) []
  | paren : WrittenChildren r sigs ctx (.paren o e c) [(ctx, e)]
  | unary : WrittenChildren r sigs ctx (.unary t op e) [(ctx, e)]
  | binary : WrittenChildren r sigs ctx (.binary a t op b) [(ctx, a), (ctx, b)]
  | call : WrittenChildren r sigs ctx (.call f o args commas c)
      ((ctx, f) :: args.toList.map (ctx, ·))
  | ifE : WrittenChildren r sigs ctx (.ifE i b t yes e no)
      [(ctx, b), (ctx, yes), (ctx, no)]
  | letE : FrenHirToThir.HasValue r sigs ctx value vt →
      WrittenChildren r sigs ctx (.letE l name assign value i body)
        [(ctx, value), ((name, vt) :: ctx, body)]
  | matchE : WrittenChildren r sigs ctx (.matchE m scrutinee o arms c)
      ((ctx, scrutinee) :: arms.toList.map (fun arm => (ctx, arm.2.2.1)))

mutual
  /-- One entry per structural visit, after all ordered child entries. No key deduplication. -/
  inductive OccurrenceOrder (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
      FrenModule.TypeContext → FrenAst.Expr → List FrenModule.TypedOccurrence → Prop where
    | node : WrittenChildren r sigs ctx expr children →
        OccurrenceForest r sigs children nodes →
        OccurrenceOrder r sigs ctx expr (nodes ++ [⟨expr, ctx, ty⟩])

  /-- Child subtrees concatenate in written order, retaining their multiplicities. -/
  inductive OccurrenceForest (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
      List (FrenModule.TypeContext × FrenAst.Expr) → List FrenModule.TypedOccurrence → Prop where
    | nil : OccurrenceForest r sigs [] []
    | cons : OccurrenceOrder r sigs ctx expr first →
        OccurrenceForest r sigs rest remaining →
        OccurrenceForest r sigs ((ctx, expr) :: rest) (first ++ remaining)
end

/-- Exact per-body source inventory, including multiplicity and postorder. -/
def OccurrenceInventory (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList,
    OccurrenceOrder input out.signatures body.context body.expression body.occurrences.toList

/-- Both source-to-output coverage and soundness of every output entry. -/
def OccurrenceTyping (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  (∀ body ∈ out.bodies.toList, ∀ ctx expr,
    AtContext input out.signatures body.context body.expression ctx expr →
    ∃ occurrence ∈ body.occurrences.toList,
      occurrence.expression = expr ∧ occurrence.context = ctx ∧
      OccurrenceMeaning input out.signatures occurrence) ∧
  (∀ body ∈ out.bodies.toList, ∀ occurrence ∈ body.occurrences.toList,
    AtContext input out.signatures body.context body.expression
      occurrence.context occurrence.expression ∧
    OccurrenceMeaning input out.signatures occurrence)

/-- Source declarations determine body owner, result type and parameter context. -/
inductive DeclaresBody (input : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenBase.ItemId → Option FrenAst.Member → FrenAst.Expr →
      FrenModule.TypeContext → FrenExpr.Ty → Prop where
  | function : input.document.root = .declarations decls →
      FrenAst.Decl.function vis keyword name params colon result assign expr ∈ decls.toList →
      FrenHirToThir.signatureAt sigs (input.scope.id.named name.text) = some sig →
      DeclaresBody input sigs sig.id none expr
        (FrenHirToThir.parameterContext sig.parameters) sig.result
  | member : input.document.root = .declarations decls →
      FrenAst.Decl.expectation keyword name params openTok members closeTok ∈ decls.toList →
      member ∈ members.toList → FrenHirToThir.parameters input params = .ok typedParams →
      DeclaresBody input sigs (input.scope.id.named name.text) (some member) member.body
        (FrenHirToThir.parameterContext typedParams) .bool

def BodyEntry (body : FrenModule.TypedBody) (owner : FrenBase.ItemId)
    (member : Option FrenAst.Member) (expr : FrenAst.Expr)
    (ctx : FrenModule.TypeContext) (ty : FrenExpr.Ty) : Prop :=
  body.owner = owner ∧ body.member = member ∧ body.expression = expr ∧
    body.context = ctx ∧ body.type = ty

/-- Every source body occurs once, including unused functions and every member. -/
def BodyInventory (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  (∀ body ∈ out.bodies.toList,
    DeclaresBody input out.signatures body.owner body.member body.expression body.context body.type) ∧
  (∀ owner member expr ctx ty, DeclaresBody input out.signatures owner member expr ctx ty →
    ∃ i : Fin out.bodies.size, BodyEntry out.bodies[i] owner member expr ctx ty ∧
      ∀ j : Fin out.bodies.size, BodyEntry out.bodies[j] owner member expr ctx ty → j = i)

def TypePassContract : Prop := ∀ input out, Produces input out →
  FrenHirToThir.Admitted input ∧ out.resolved = input ∧
    FrenHirToThir.signatures input = .ok out.signatures ∧
    BodyInventory input out ∧ BodyTyping input out ∧
    OccurrenceInventory input out ∧ OccurrenceTyping input out

/-- Coverage quantifies over actual AST descendants, not just a supplied table. -/
def MatchCoverage (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList, ∀ ctx m scrutinee o arms c,
    AtContext input out.signatures body.context body.expression ctx
      (.matchE m scrutinee o arms c) →
    ∃ owner, FrenHirToThir.HasValue input out.signatures ctx scrutinee (.enum owner) ∧
      (∀ item ∈ input.scope.items.toList,
        item.kind = .constructor → item.id.parent = some owner →
        ∃ j : Fin arms.size,
          FrenHirToThir.Selects input ctx arms[j].1 .pattern (.item item.id) ∧
          ∀ k : Fin arms.size,
            FrenHirToThir.Selects input ctx arms[k].1 .pattern (.item item.id) → k = j) ∧
      (∀ arm ∈ arms.toList, ∃ item ∈ input.scope.items.toList,
        item.kind = .constructor ∧ item.id.parent = some owner ∧
        FrenHirToThir.Selects input ctx arm.1 .pattern (.item item.id))

def Calls (input : FrenModule.Resolved) (out : FrenModule.Typed)
    (caller callee : FrenBase.ItemId) : Prop :=
  ∃ body ∈ out.bodies.toList, body.owner = caller ∧ body.member = none ∧
    ∃ ctx path o args commas c,
      AtContext input out.signatures body.context body.expression ctx
        (.call (.name path) o args commas c) ∧
      FrenHirToThir.Selects input ctx path .expression (.item callee)

inductive CallPath (edge : FrenBase.ItemId → FrenBase.ItemId → Prop) :
    FrenBase.ItemId → FrenBase.ItemId → Prop where
  | one : edge a b → CallPath edge a b
  | more : edge a b → CallPath edge b c → CallPath edge a c

def Nonrecursive (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ item, ¬ CallPath (Calls input out) item item

/-- These are correspondence obligations, not aliases for validator success. -/
def CoverageContract : Prop := ∀ input out, Produces input out →
  (FrenHirToThir.WalkingCoverage out ↔ MatchCoverage input out)

def NonrecursionContract : Prop := ∀ input out, Produces input out →
  (FrenHirToThir.WalkingNonrecursive out ↔ Nonrecursive input out)
```

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
choice or guessed type is involved. Diagnostic recovery and multi-error
aggregation are not required by this source domain.

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
