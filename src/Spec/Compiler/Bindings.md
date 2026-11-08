# Binders and substitution

A binder gives a local variable a meaning within a term. In `|x| |y| x`,
the use of `x` crosses the binder for `y`: its de Bruijn index is 1.
Index 0 always denotes the nearest binder. This chapter specifies the
shared binding operations for expressions, quantifiers, sentences and
obligations. It builds on [compiler identity](Overview.md#identity-and-origin)
and [base definitions](BaseDefinitions.md).

The reference implementation used here is the successful raw-index
[expression prototype](../../../scratch/expr/Prototype.lean). Its `Expr p`
is a small Lean test representation, not the production IR datatype.
The equations below constrain the future shared library without fixing
production constructors. `V i`, `All b`, `Let v b`, and `Array xs` abbreviate
prototype variable, quantifier, let and array nodes. They are mathematical
notation, not additional Fren syntax.

## Contexts and scope

A *context* lists available local slots, nearest first. For context
`[y, x]`, `V 0` denotes `y` and `V 1` denotes `x`. Names in these lists
explain examples; the semantic references are the positions.

**Legality rules**

r[bindings.representation.raw]
Local occurrences carry natural-number de Bruijn indices with an explicit
scope predicate, independently of typing.

r[bindings.scope.context]
`Scoped n t` means that every occurrence at local binder depth `d` has index
strictly below `n + d`, where `n` is the root context length.

r[bindings.scope.children]
Each child is checked at the parent context extended by the binders in
scope at that child, including every element of an array.

r[bindings.scope.boundary]
A boundary promising a well-scoped term requires scope evidence or a
successful scope check in its supplied context.

**Dynamic semantics**

r[bindings.identity.context]
A raw index is interpreted relative to its supplied context; equal context
lengths alone do not identify slots in different contexts.

r[bindings.identity.metadata]
Written names, origins and debug spans do not decide semantic binding or
alpha-equivalence.

The prototype's exact child contexts are:

| Node | Child contexts at root length `n` |
| --- | --- |
| Literal or variable | No children; variable `i` requires `i < n` |
| `Let v b` | `v` at `n`; `b` at `n + 1` |
| `All b` | `b` at `n + 1` |
| `Array xs` | Every child at `n`, in array order |
| Phase-gated sugar | Its body at `n`; its gate introduces no binder |

In Fren, `let x = y; x` binds `x` in its body, not in `y`. Accordingly,
`Let (V 0) (V 0)` is scoped in context `[y]`, but fails in the empty
context: the value cannot use its own binder. `All (V 0)` is closed;
`All (V 1)` needs one outer slot. `V 2` is invalid in a context of length
2, while `Array #[]` is scoped in every context.

An open term has free occurrences relative to the root. It can still be
well scoped in a nonempty context. A dangling occurrence exceeds that
context. Raw operations below also accept dangling occurrences; that
computational totality does not make the result valid. Scope says nothing
about types, definedness, or whether evaluation succeeds. Future error or
hole forms must expose their child binding depths; their traversal and
scope policy remain part of their IR chapter. They acquire no evaluation
or typing guarantee from this chapter.

> **Rationale:** The prototype keeps arrays and raw indices after two
> particular intrinsic scope-indexed array encodings were rejected by
> Lean's kernel. Those failures do not establish that all intrinsic
> encodings are impossible. The accepted implementation uses extrinsic
> `Scoped` and an equivalent executable `scopeCheck`.

## Renaming and shifting

Renaming changes references to outer slots while preserving each binder's
own occurrences. Write `rename ρ t` for simultaneous renaming by a total
map `ρ : Nat → Nat`.

**Dynamic semantics**

r[bindings.operations.total]
Binding operations terminate on finite raw terms without fuel or exceptions,
including dangling indices; scope guarantees require their stated premises.

r[bindings.rename.lift]
Renaming uses `ρ` at a variable and lifts it across each binder by
`upRen ρ 0 = 0` and `upRen ρ (i + 1) = ρ i + 1`.

r[bindings.rename.structure]
Renaming preserves nonbinding fields and maps all children at their binding
depths, preserving array length and order.

r[bindings.shift.cutoff]
For natural `a` and `c`, `shift a c t` is `rename (S a c) t`, where
`S a c i = if i < c then i else i + a`.

A shift inserts `a` slots at position `c`: nearer slots remain in place,
older slots move outwards. When `c ≤ n`, it takes a term scoped at `n`
to one scoped at `n + a`. Under one binder its cutoff becomes `c + 1`.
A child under `k` binders uses `upRen` iterated `k` times. Array siblings
start at the same parent depth; traversal does not accumulate binders from
one sibling to the next. An arbitrary signed downward shift is not supplied: context removal uses
substitution, with explicit replacement of the removed slot.

```text
shift 2 0 (All (Array #[V 0, V 1])) = All (Array #[V 0, V 3])
shift 2 1 (All (Array #[V 0, V 1])) = All (Array #[V 0, V 1])
```

The first `V 0` is locally bound. Shifting it would turn the closed
`All (V 0)` into the dangling `All (V 1)` when the amount is 1. Failing
to increment cutoff under `All` makes precisely this mistake. The second
example protects root slot 0 as well: cutoff is part of the operation,
not a tuning parameter.

## Substitution and capture avoidance

Simultaneous substitution replaces each outer slot by a term. A total
environment `σ : Nat → Expr p` includes images for dangling indices too.
Only the images of in-scope indices need scope evidence for preservation.
A child under `k` binders uses `upSub` iterated `k` times. Each IR must
expose all semantic children, including binding-bearing type annotations,
and their binder increments to the shared traversal.

**Dynamic semantics**

r[bindings.substitution.lift]
Substitution uses `σ i` at a variable and lifts across a binder by
`upSub σ 0 = V 0` and `upSub σ (i + 1) = rename Nat.succ (σ i)`.

r[bindings.substitution.structure]
Substitution maps every child at its binding depth and preserves nonbinding
fields, phase gates, array length and array order.

r[bindings.substitution.top]
`substTop s t` removes root slot 0 using the environment
`0 ↦ s` and `i + 1 ↦ V i`.

r[bindings.substitution.at]
For natural `j`, `substAt j s t` removes root slot `j` using the environment
`i ↦ if i < j then V i else if i = j then s else V (i - 1)`.

`substAt` is notation for a call to simultaneous substitution, not an
existing prototype API. With `j ≤ n`, body scoped at `n + 1` and
replacement scoped at `n`, its result is scoped at `n`. The replacement
is already expressed in the destination context after deletion. Subtraction
occurs only in the `i > j` case; no valid index is truncated at zero.

For the Fren pattern `let x = y; |z| x`, substitute the open replacement
`V 0` in context `[y]` into body `All (V 1)` in context `[x, y]`:

```text
substTop (V 0) (All (V 1)) = All (V 1)
substTop (V 0) (All (Array #[V 0, V 1, V 2]))
  = All (Array #[V 0, V 1, V 1])
```

The replacement becomes `V 1` under `z`, preserving its reference to `y`.
An unlifted substitution would yield `All (V 0)`, capturing `y` as `z`.
Both results can pass a scope check; capture avoidance needs more than
scope preservation. In the array example, the last entry originally
refers to `y`, whose root slot is decremented when `x` is removed.
On raw malformed input `substTop (literal 8) (V 99) = V 98`; this equation
does not establish well-formedness.

## Opening and closing

Opening instantiates an exposed binder body; closing abstracts a selected
outer slot as the newest slot. Both use indices, with no separate named
free-variable constructor. These are semantic definitions for future APIs;
the prototype currently supplies only `substTop`, `subst` and `rename`.

**Dynamic semantics**

r[bindings.opening.definition]
`open s b` is `substTop s b`, with `b` scoped in the destination context
extended by one newest slot and `s` scoped in the destination context.

r[bindings.closing.definition]
For slot `j` in context `Γ`, `close j t` is `rename Cj t`, where
`Cj i = if i = j then 0 else i + 1`, in context `[new] ++ Γ`.

Closing leaves the old slot `j` available in the context but unused in
the result at root index `j + 1`. It does not delete or permute `Γ`.
A caller wanting a smaller context must supply an explicit reindexing.
For `Γ = [a, b]`, closing slot 1 in `Array #[V 0, V 1]` gives body
`Array #[V 1, V 0]` under `[new, a, b]`. Opening it with `V 1` in `Γ`
recovers the original array.

**Proof obligations**

r[bindings.open-close.laws]
For `j < n` and `Scoped n t`, opening `close j t` with `V j` recovers
`t`; for `Scoped (n + 1) b`, closing `open (V j) b` recovers `b` only
when root free index `j + 1` is absent from `b`.

The second direction needs freshness relative to the older copy of the
slot. For `Γ = [a, b]`, body `Array #[V 0, V 2]` opens with `V 1` to
`Array #[V 1, V 1]`; closing slot 1 gives `Array #[V 0, V 0]`, losing the
distinction. A general replacement also has no closing inverse:
`open (literal 7) (V 0)` is a literal, from which closing cannot reconstruct
the occurrence. Production API argument order and checked return types
remain unsettled; these equations must survive those choices.

## Free indices and alpha-equivalence

A free index is a reference to the context outside the term, not a name.
Removing the binders traversed on the path normalizes it to a root slot.

**Dynamic semantics**

r[bindings.free-indices.definition]
`FV t` is the finite set containing `i - d` for each occurrence `V i` at
local depth `d` with `d ≤ i`.

r[bindings.free-indices.children]
Free-index collection unions every child's indices, dropping indices below
that child's binder increment and subtracting the increment from the rest.

r[bindings.alpha.definition]
Syntactic de Bruijn alpha-equivalence is equality of binding structure and
semantic fields, ignoring written names, origins and debug spans, with
ordered arrays compared element by element in corresponding contexts.

For the prototype, `FV (V i) = {i}`, `FV (literal v) = ∅`,
`FV (All b) = {i | i + 1 ∈ FV b}`, and
`FV (Let v b) = FV v ∪ {i | i + 1 ∈ FV b}`.
An array uses the union over all members; the empty array contributes `∅`.
Thus `FV (All (Array #[V 0, V 2])) = {1}` even when no context is supplied.
It is scoped in a context of length 2 and dangling in one of length 1.

The source lambdas `|x| x` and `|y| y` are alpha-equivalent although their
pretty names differ. The same raw `V 0` under `[a]` and `[b]` does not
assert that `a` and `b` denote the same external object. Comparing open
terms from different contexts requires an explicit correspondence or
renaming first. Alpha-equivalence is syntactic: it does not equate `1 + 1`
with `2`, nor discharge type or definedness obligations. The future equality
implementation must exclude metadata; the prototype has no such metadata.

**Proof obligations**

r[bindings.alpha.laws]
Alpha-equivalence is reflexive, symmetric and transitive in corresponding
contexts, and is preserved by equal renamings and pointwise
alpha-equivalent substitution environments.

For the substitution law the source terms are scoped at `n` and the
images of each source slot below `n` are scoped in the same destination
context. For renaming, both terms use the same source context and the
same map into a common destination context. These are requirements for
the future metadata-independent equality API, not existing Lean theorems.

## Whole-term laws and evidence

The equations use one fixed prototype phase `p` and its actual operations.
`V`, `upRen`, `upSub`, `rename`, `shift`, `subst`, `substTop`, `Scoped` and
`scopeCheck` refer to `ExprPrototype`. Symbols for free indices, closing,
alpha-equivalence and `substAt` denote the definitions above, with no claim
of existing production declarations.

**Proof obligations**

r[bindings.laws.scope]
Renaming preserves scope when `∀ i < n, ρ i < m`; substitution preserves
scope when `∀ i < n, Scoped m (σ i)`; both start with `Scoped n t`.

r[bindings.laws.checker]
`scopeCheck n t = true` holds exactly when `Scoped n t`.

r[bindings.laws.composition]
Renaming and substitution satisfy the identity and composition equations
below with the indicated context maps.

r[bindings.laws.shift-substitution]
Shifting after slot deletion satisfies the reindexed equation below for
`Scoped (n + 1) t`, `Scoped n s`, `j ≤ n` and `c ≤ n`.

r[bindings.laws.free-indices]
`Scoped n t` holds exactly when every member of `FV t` is below `n`;
`FV (subst σ t) = ⋃ i ∈ FV t, FV (σ i)`.

The composition equations are requirements on the actual shared operations,
not executable Fren models. Here `ρ : n → m` abbreviates a total natural
map bounded on indices below `n`, and `σ : n ⇒ m` abbreviates a total
term map whose first `n` images are scoped at `m`:

```text
rename id t = t                         subst V t = t
rename η (rename ρ t) = rename (η ∘ ρ) t
  t : n, ρ : n → m, η : m → k
subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t
  t : n, σ : n ⇒ m, τ : m ⇒ k
rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t
  t : n, σ : n ⇒ m, ρ : m → k
subst σ (rename ρ t) = subst (fun i => σ (ρ i)) t
  t : n, ρ : n → m, σ : m ⇒ k
```

At binders these equations compare lifted maps: e.g. the composed
substitution uses `upSub τ` on `upSub σ` images, not the original maps.
The scope hypotheses give the intended source and destination contexts;
the total raw definitions also permit testing the equations on dangling
inputs. Renaming need not be injective for these laws; a renaming used
as a context embedding must be injective on the slots it embeds.

For upward shift amount `a`, destination cutoff `c`, and deleted slot `j`,
let `j' = if j < c then j else j + a` and
`c' = if c ≤ j then c else c + 1`. Then:

```text
shift a c (substAt j s t)
  = substAt j' (shift a c s) (shift a c' t)
```

The left result has scope `n + a`. The shifted body on the right has
scope `n + 1 + a`; its removed slot is `j'`. For top substitution with
`c = 0`, both source and replacement shift at zero, but the removed index
becomes `a`. Keeping index 0 is wrong: with `t = V 0`, `s = literal 7`,
`a = 1`, the left side is `literal 7` and that wrong right side is `V 0`.
For `j = 0, c = 1`, the source cutoff is 2, not 1. With `t = V 1`,
shifting it at 1 before deleting slot 0 moves a protected slot incorrectly.
These cases distinguish reindexing from a naive always-equal formula.

The existing universal proofs are `rename_scoped`, `subst_scoped`,
`scoped_mono`, `substTop_closed_scoped`, and `scopeCheck_iff` in the prototype.
In particular, `Scoped 0 s → Scoped (n + 1) b → Scoped n (substTop s b)`
is already proved for every depth and every array member. Open replacements
are covered by the stronger `subst_scoped`; the additional chapter test
proves that specialization directly. These proofs use real induction on
scope evidence, not a solver abstraction or a test classified as a proof.

[Chapter checks](../../../scratch/expr/BindingsLaws.lean) add direct Plausible
checks of actual prototype composition and shift/substitution operations on
bounded raw terms, and concrete capture/cutoff controls. They include open
and dangling terms and nonzero cutoffs. They do not implement a production
binder library. The prototype has no type checker or hole constructor;
raw malformed terms exercise scope failure, not all future partial IR forms.
The original [prototype tests](../../../scratch/expr/Tests.lean) also cover
both phases, let-value/body distinctions, arrays and deliberately bad lifts.

The evidence boundary is explicit:

| Obligation | Evidence now | Remaining work |
| --- | --- | --- |
| Scope preservation and checker equivalence | Universal Lean prototype proofs | Bind to the eventual shared library |
| Identity, composition, shift/substitution | Bounded executable tests on prototype operations | Universal composition/commutation proofs |
| Free indices, alpha-equivalence, opening/closing inverses | Definitions and laws in this chapter | Actual APIs, formalization and tests |
| Generic fold induction/fusion | Prototype has a total fold | Prove the reusable theorem once and instantiate it |
| Production pass simulations | Overview's requirements | Relate values, assumptions and obligations for each pass |

- [ ] Formalize the composition and commutation equations in Lean over the
  shared implementation, using real induction where the fold theorem
  does not suffice.
- [ ] Prove free-index, alpha and open/close laws over their actual APIs.
- [ ] Instantiate the planned generic fold theorem for simple traversal
  laws; it is not an existing proof delivered by the prototype.
- [ ] Bind the future shared code with `impl` where applicable, without
  using `impl … by plausible` as proof evidence.
- [ ] Test actual future IR forms with direct Plausible, including invalid,
  ill-typed and partial inputs; report accepted/rejected premise counts.
- [ ] Restate recursive laws in Fren after crossover when it supports
  recursive functions over array children and the required environments.
  No Fren 1 recursive feature is a prerequisite for this chapter.

## Independent primitive contracts

These small contracts check index arithmetic and cases independently of
recursive code. Their `Nat` inputs and explicit context bounds fix their
domains; they neither encode an IR nor establish the whole-term laws above. True and false scope premises occur in the examples.

**Dynamic semantics**

r[bindings.primitive.scope] spec::bindings::scope_case::{membership, zero_invalid, last_valid, boundary_invalid}
For a nonnegative index in a context of nonnegative length `n`, validity
is strict inequality: no index is valid at zero, `n - 1` is valid when
`n > 0`, and `n` is invalid.

```fren
pub mod spec
pub mod spec::bindings

pub proc scope_case(i: Nat, n: Nat): (valid?) {
    ensure membership: valid? iff i < n

    expect zero_invalid: when n = 0, not valid?
    expect last_valid: when n > 0 and i = n - 1, valid?
    expect boundary_invalid: when i = n, not valid?
    expect open_valid: when i = 0 and n = 1, valid?
}
```

r[bindings.primitive.shift] spec::bindings::shift_case::{below, above, enlarged}
Upward index shifting leaves indices below cutoff alone and adds the amount
at or above cutoff, preserving the enlarged context bound.

```fren
pub proc shift_case(i: Nat, n: Nat, c: Nat, a: Nat): (r: Int) {
    require index: i < n
    require cutoff: c <= n
    ensure below: when i < c, r = i
    ensure above: when i >= c, r = i + a
    expect enlarged: 0 <= r < n + a

    expect zero_cutoff: when c = 0, r = i + a
    expect end_cutoff: when c = n, r = i
}
```

r[bindings.primitive.lift] spec::bindings::lift_case::{newest, older, bound}
A lifted renaming fixes the newest index at zero and increments each older
image, bounded in a context extended by one slot.

```fren
pub proc lift_case(i: Nat, image: Nat, m: Nat): (r: Int) {
    require image_bound: image < m
    ensure newest: when i = 0, r = 0
    ensure older: when i > 0, r = image + 1
    expect bound: 0 <= r < m + 1

    expect avoid_newest: when i > 0, r > 0
}
```

r[bindings.primitive.delete] spec::bindings::delete_case::{nearer, removed, older, bound}
Deleting an in-scope slot classifies its own occurrence as replaced, keeps
nearer indices, and decrements older indices into the remaining context.

```fren
pub proc delete_case(i: Nat, j: Nat, n: Nat): (replaced?, r: Int) {
    require index: i < n + 1
    require target: j <= n
    ensure nearer: when i < j, (not replaced? and r = i)
    ensure removed: replaced? iff i = j
    ensure older: when i > j, (not replaced? and r = i - 1)
    expect bound: when not replaced?, (0 <= r < n)

    expect only_slot: when n = 0, replaced?
    expect older_nonnegative: when i > j, i > 0
}
```

The replacement case places no bound on the unused output `r`. The
recursive substitution contract instead requires the replacement term to
be scoped in the destination context. The chapter's negative validation
asserts that the exact context boundary is valid in a separate fixture;
normal checking must reject it. That control tests the primitive checker,
not a universal recursive theorem.
