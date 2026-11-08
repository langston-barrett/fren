# Expression representation feasibility (#997)

This isolated prototype starts at local integration
`e408c13b92543ab6f66f4237827861becc030ca4` (tree
`fd91857eb6db7b4a3ea4a36627261b581e233abc`). It tests the representation in
the approved IR design and R0. It neither adopts the later split-study
recommendations nor freezes a production schema. No planned IR library,
shared test driver, Lake declaration, or compiler specification changes.

## Result and decision

Use the authorized fallback on Lean 4.32: plain de Bruijn indices with an
explicit scope relation. Keep a phase parameter, an ordinary recursive
position parameter in the layer, and arrays. Two intrinsic candidates fail
in the kernel; the fallback compiles with total recursion and actual scope
proofs. This establishes feasibility for these constructors. It does not
rule out every possible intrinsic representation, or measure full compiler
performance.

`Prototype.lean` has this exact contract:

| Form in `Layer p R` | Fields | Scope of children in context n |
|---|---|---|
| `lit` | `value : Nat` | no children |
| `var` | `index : Nat` | requires index < n |
| `letE` | `value body : R` | value at n; body at n + 1 |
| `all` | `body : R` | body at n + 1 |
| `array` | `children : Array R` | every child at n |
| `sugar` | `gate : HasSugar p`, `body : R` | body at n |

`Phase` has `high` and `low`. `HasSugar p` is the decidable proposition
`p = high`; its definition is exposed for imported proof clients.
`Expr p` has one constructor, `roll : Layer p (Expr p) → Expr p`.
`Scoped n e` is an inductive relation; `scopeCheck n e` is proved equivalent
to it. The raw type intentionally permits bad indices, which tests exercise.
A future checked library boundary must require scope evidence or run the
check. The prototype does not add that production boundary.

`mapChildrenM` visits immediate children in field order, then array order,
and reports binder increments to the callback. It preserves the phase gate
and non-child fields; it is not a whole-term traversal. Its pure specialization
is `mapChildren`. The generic `fold` accepts `Layer p A → A` but spells out
constructor recursion, including `Array.map`, under `termination_by sizeOf`.
Lean exposes the array membership decrease through `attach` in the compiled
well-founded definition. Recursing through a callback to `mapChildren` fails
termination inference, as recorded in `attempts/OpaqueTraversal.lean`.
These two constructor dispatches must stay aligned when adding forms.

Renaming and substitution are actual folds into environment-dependent
functions. `upRen` fixes index zero and increments older images. `upSub`
fixes index zero and shifts every older replacement before crossing a
binder. `substTop` replaces index zero and decrements older free indices;
its replacement is scoped in the remaining context. `shift amount cutoff`
is an upward shift by a natural amount, leaving indices below the cutoff
alone and lifting the cutoff through binders. It handles all raw terms
without truncation, fuel, exceptions, or a scope precondition. Context
removal is provided by substitution; arbitrary signed downward shifts are
outside this experiment.

## Kernel evidence and tests

The proof chain in `Prototype.lean` is `rename_scoped`, `subst_scoped`,
`scoped_mono`, then `substTop_closed_scoped`. The latter says:

```text
Scoped 0 value → Scoped (n + 1) body → Scoped n (substTop value body)
```

The simultaneous substitution theorem is stronger: every in-scope source
index may map to any term scoped in the destination context. Both proofs
cover every array member and any binder depth. `scopeCheck_iff` connects the
executable check with the same relation. These are proofs, not sampled
properties. `Audit.lean` prints axiom dependencies, the array fold equation,
and the accepted `WellFounded.Nat.fix` implementation. Dependencies are only
Lean's `propext` and `Quot.sound` (traversal needs only `propext`); there are
no new axioms or admissions, `sorryAx`, unsafe definitions, or partial
substitution. Ordinary Lean import trust is used, not a full recheck of Std.

`Tests.lean` runs as an executable Lean `main`. It checks concrete open and
closed substitutions through nested let/quantifier/array boundaries,
nonzero shift cutoffs, context deletion, malformed indices, folds, traversal
order, failure propagation and short circuiting. Deliberately unlifted
substitution and shifting bound variables must disagree with the correct
expected terms; scope alone would miss some capture bugs. The corpus has
36 high-phase and 29 low-phase terms, including nested arrays and the gated
form, with context sizes 0–5. Identity, composition and reconstruction laws
are tested on that finite corpus; they are not claimed as universal proofs.
`attempts/ForbiddenGate.lean` must fail at type checking. Codecs roundtrip
all six layer forms at high phase and all five allowed low forms through
text; malformed arity, array element type and low-phase sugar are rejected.

Reproduce from the repository root with the pinned, already-built assets:

```sh
scripts/heavy --offline python3 scratch/expr/check.py --out /tmp/expr-997-check
```

The output directory must be new. Every Lean invocation uses
`lake --no-cache env`; only the two scratch imports produce `.olean`/`.ir`
files in `.lake/build/lib/lean/scratch/expr`. There is no package build or
new Lake library in this runner. `Tests.lean` has a `meta import` so imported
runtime definitions can execute in the interpreter. The negative fixtures
must exit 1 with their expected diagnostic; a missing import cannot pass.

## Failed candidates and cost

The exact negative sources are kept in `attempts/`; the captured original
kernel/termination diagnostics are in `failures.txt`. `IndexedLayer.lean`
tries a scope-indexed recursive position in a layer. `IndexedDirect.lean`
puts scope on the whole inductive family. Both kernels reject arrays with
“nested inductive datatypes parameters cannot contain local variables”.
`OpaqueTraversal.lean` is rejected because the generic callback gives no
proof that its child is smaller. The fallback keeps arrays and uses an
explicit constructor match with a size measure; no failing encoding is
admitted into the prototype module.

Measured on this worktree with already warm dependencies and source/page
caches, including Lake environment setup, excluding outer Heavy/fd admission:

| Check | Executed seconds | Outcome |
|---|---:|---|
| indexed layer | 0.652 | kernel rejection |
| indexed whole family | 0.545 | kernel rejection |
| recursive generic traversal | 0.814 | termination rejection |
| fallback core, including proofs | 1.166 | accepted |
| fallback core repeated | 1.197 | accepted |
| one-layer codec | 0.648 | accepted |
| proof audit | 0.655 | accepted |
| interpreted tests, including elaboration | 0.879 | passed |

The first captured timing round (`validation/results.json` in the author
artifacts) ran for 8.312 seconds with 0.036 seconds of Heavy
admission wait. `wait4` child high-water RSS was 789–791 MiB across these
commands, including Lake; this is not simultaneous process-tree memory.
Heavy sampled 1291 MiB peak for the whole validation process group. The
environment-function fold allocates intermediate arrays of child functions, and lifted substitution renames replacement images under each
binder. Deep binders or large replacements may therefore cost much more
than this toy; runtime allocation and asymptotic behavior need later work.
No cold toolchain/dependency build, isolated Lean-only timing, or native
runtime benchmark was measured. The first untimed successful fold preceded proof
development; the measured rows above are final warm elaborations, not cold
builds or a Lake no-op. Negative admission time is not usable compile time
for an alternative encoding.

Proof effort: four scope-preservation/monotonicity lemmas and the checker
equivalence, 134 lines including scope checking. The successful
route is induction on scope evidence, with environment lifting at binders
and member-wise reasoning for arrays. Intermediate proof scripts needed
explicit fold equation simplification and the member-based array `all`
lemma; these were elaboration mistakes, not further kernel obstructions.
The measured core includes all proofs; proof-only CPU and human effort
were not measured separately.

## Remaining deriving and generator contracts

`Codec.lean` uses existing `Fren.ToSexp`/`Fren.FromSexp` classes for a
handwritten generic layer codec, plus a full-tree encoder using the fold.
It does not implement #979 or #982, or a full-tree parser. The layer wire
forms are `(lit n)`, `(var i)`, `(let value body)`, `(all body)`,
`(array (child ...))`, and `(sugar body)`; phase is supplied externally.
The production version envelope remains a #979 integration requirement.

For #979 the derived handler must:

- Support parameterized layers, recursive fixpoints and array recursion,
  with a total parser whose structural decrease remains visible to Lean.
- Dispatch tags with exact arities, retain child order, and prefix decoding
  errors by field/array index using the base codec's paths and positions.
- Omit proof fields, reconstruct decidable gates after checking the phase,
  and reject forbidden forms. Generic arbitrary proof-field decoding cannot
  just synthesize proofs or accept a Boolean in place of the gate.
- Take phase as a caller-supplied index or check it in an external envelope;
  it cannot infer the intended phase from an omitted proof field.
- Keep parsing raw indices separate from recursive scope validation.
  A raw roundtrip alone establishes no scoping or typing property.
- Support Lean `module` visibility: exported gate contracts or exposed
  definitions, and runtime code accessible to interpreting clients. Standard
  derived `Repr` and `BEq` already work for this layer/fixpoint combination.

For #982 the derived generator must:

- Use a size/depth budget with terminating base cases and bounded array
  lengths; generate both empty arrays and several nested children.
- Select constructors allowed by the phase, constructing a real gate proof.
- Generate well-scoped terms with an explicit context size: variable indices
  below n, let values at n, and let/quantifier bodies at n + 1. At n = 0,
  exclude variables; reserve separate malformed-index controls.
- Offer open replacements scoped in the destination context and closed
  replacements, covering capture and context deletion as well as literals.
- Preserve phase and scope during shrinking. Use the real scope definition
  for premise statistics, and avoid vacuous property tests from rejected
  inputs. Typing is an additional extrinsic invariant outside this toy.

No Plausible integration is added here: the required recursive preservation
property is proved universally, and the other executable laws use an
explicit finite corpus. That corpus is not a substitute for #982.

## Restatement checklist for later specification chapters

- [ ] Restate recursive `Scoped` and the `scopeCheck` equivalence in Fren once
  Fren2 supports recursive datatypes with sequence children and recursive
  predicates over every sequence element.
- [ ] Restate lifted renaming/substitution and scope preservation once Fren2
  supports recursive functions through sequence children and the necessary
  environment representation. Preserve the let-value/body distinction.
- [ ] Restate recursive fold reconstruction and shift/composition laws once
  the same recursive-function features exist; currently these laws have
  finite executable checks, while scope preservation has a Lean proof.
- [ ] State one-layer traversal/algebra laws with today's ordinary type
  parameters and phase well-formedness predicates when writing the relevant
  chapter. Generic fold induction/fusion remains later work after #997.

No recursive compiler chapter is declared complete. No frontend, UI,
mutation, full-suite or legacy native investigation is part of validation.
