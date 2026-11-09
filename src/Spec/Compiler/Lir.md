# Walking logical lowering (LIR)

Logical lowering turns a retained program into first-order terms suitable
for asking logical questions. It must preserve both a term's value and
where that value is defined. Keeping only Boolean formulas would lose the
difference between a false expectation and an undefined one.

This chapter specifies the walking boundary after the actual
[MIR producer](Mir.md). [FrenLir](../../FrenLir/Walking.lean) now provides
first-order values and scoped verification information, and
[FrenFlatToLir](../../FrenFlatToLir/Walking.lean) lowers the admitted walking
fragment directly. No mono, closure or flat pass is claimed. `FrenLirEval`
remains a stub; there is no production logical evaluator or solver backend.
The checked primitive facts below remain independent contract tests.

## Input and retained program

**Proof obligations**

r[lir.walking.input]
The walking input is a `FrenMir.Theory` returned successfully by
`FrenThirToMir.produce p`, with that success and `p.accepted` as evidence.
An arbitrary edited theory or typed record is insufficient. Unsupported
inputs remain explicit failures, never silently erased expressions.

The admitted source has Bool, mathematical Int, nominal payload-free enums,
nonrecursive named expression-bodied functions and global expectations.
Bodies have the existing literals, resolved names, parentheses, unary and
binary operators, calls, lets, conditionals and exhaustive constructor
matches. The [desugaring boundary](Desugaring.md) is currently an identity.
There are no type parameters, function-valued parameters or closures here;
this slice neither implements nor pretends to run the full instance,
closure-specialization and match-compilation pipeline of the
[compiler overview](Overview.md). A walking implementation may lower these
already first-order MIR bodies directly, with an explicit boundary.

r[lir.walking.retention]
The resulting program retains ordered nominal enum declarations, function
signatures and definitions, and every owned check request, with a traceable
correspondence to their actual source identities and typed lexical contexts.

MIR retains the full `Typed` source, including the document, file identity,
token tape, spans and typed occurrences. Lowering must keep this data or
explicit maps back to it. Canonical `ItemId`s identify enums, constructors,
functions and block owners; spelling or structural equality cannot replace
them. Each enum domain contains exactly its declared constructors, distinct
from those of every other enum. Bool has its two values; Int has all
integers, with no machine overflow or restriction to nonnegative values.
Arithmetic and precedence retain their existing meanings. The pure fragment's
[declarative verification policy](../Language/Expressions.md) governs source
obligations independently of the concrete evaluator's execution strategy.

The walking logical vocabulary needs typed local variables, literals and
nominal constructor constants, first-order symbol applications, primitives,
conditionals (`ite`), constructor tests and scoped local lets. Exhaustive
matches can become constructor tests and conditionals, provided the selected
arm's value and conditional verification context are preserved. Partial-operation
obligations remain scoped until condition generation; no solver
assertion is emitted merely because an operation was encountered.

Parameters retain written order and nearest-first local slots. A let value
uses the incoming context; its body prepends its binder. Shadowing keeps
these slots distinct. Constructor patterns add no slots in this fragment.
Calls retain their canonical targets and ordered arguments, entering the
callee's parameter context without the caller's locals. A typed local is
meaningful only in its own recorded context, even if another slot has the
same type or display name.

r[lir.walking.requests]
Definitions remain definitions. Each block retains its assumption-satisfiability
request first, then one validity request per written expectation, in written
order, with all and only that block's assumptions and parameter context.

These are the requests actually produced by `FrenMir.Block.requests`.
Assumptions written after an expectation apply to it too. No unproved goal,
including a sibling goal, becomes a hypothesis. Definitions give calls their
meaning; they are neither extra goals nor arbitrary unchecked axioms.
Separate blocks never acquire each other's assumptions.

Once the required definedness checks have been discharged, let `A(i)` be
the conjunction of a block's assumptions under a well-typed parameter
assignment `i`, and `G(i)` one goal. Sat asks whether some `i` satisfies
`A(i)`. Validity asks whether every `i` satisfying `A(i)` satisfies `G(i)`;
its counterexample condition is `A(i) and not G(i)`. Empty assumptions mean
true, including in a block with no members. Contradictory assumptions can
make validity vacuous while Sat fails. Undefined assumptions cannot be
silently treated as false to make either question pass. These meanings
specialize the existing [global checks](../../Reqs/Check.md#global-expectations).

## Values and declarative verification

**Proof obligations**

r[lir.walking.demand]
Lowering statically traverses all written expressions and retains every
applicable source obligation with its lexical context, owner and origin.
Ordinary Boolean values and verification information remain separate. An
unproved goal is never a hypothesis for itself or a sibling goal.

Write `V(e)` for a symbolic value and `WD(e)` for declarative source
well-definedness. `FrenLir.Lowered` retains a value and a scoped
`Verification` tree; `defined` derives a formula summary from that tree.
The tree keeps individual checks, conjunctions, explicit branch guards and
scoped let binders until LIR -> OIR. This summary does not generate or
prove OIR conditions. Outside its domain a partial operation has an
unspecified symbolic value, which cannot discharge its obligation.

- Every ordinary unary or binary operand contributes its obligations in
  the incoming context. In particular `and`, `or`, `iff`, equality and
  inequality all retain both operands' obligations, regardless of their
  Boolean values. There is no source proof policy of short-circuiting.
- Division and remainder also require a nonzero divisor in that context.
- A call retains all positional argument obligations and the named
  definition's domain application. The callee uses its own parameter
  context. Every definition retains its verification tree even if unused;
  a call graph or concrete execution trace cannot erase it.
- A let retains its definition's obligations in the incoming context,
  whether or not the body reads the binder. Its body is verified in the
  extended lexical context, with exact value/domain substitution.
- An explicit conditional retains its condition's obligations and both
  written branches, under the condition and its negation respectively.
  A match likewise retains each written arm under its constructor context.
  Only these explicit scopes guard obligations in the walking grammar.

Thus ordinary `a and b` and `a or b` both have
`WD(a) and WD(b)`. A conditional has `WD(c)` together with
`V(c) implies WD(then)` and `not V(c) implies WD(else)`.
A let has `WD(value)` together with its scoped body's obligations;
unused binding does not remove `WD(value)`. An unguarded conjunction of
both conditional branches' obligations is wrong, as is guarding an ordinary
Boolean right operand by the left value.

The current walking grammar has no local assert/assume expressions or
subset syntax. For the existing check blocks, assumptions, goals, parameter
contexts and their independent verification roots remain explicit IR data.
Future assertion and subset introduction/coercion predicates use the same
scoped mechanism: preserve the obligation and applicable assumptions until
condition generation, without unconditional global hoisting. A parameter's
established subset predicate may become a scoped body assumption; the
introduced value's predicate must first be proved. These forms are not
implemented or silently admitted by this slice.

The raw [walking evaluator](Evaluator.md) uses a lazy value strategy.
Its outcome on one input does not determine which verification obligations
exist. In particular, a concrete value from an unused partial let or a
skipped Boolean operand does not establish source well-definedness.
Operational exhaustion remains a failure, never false, Sat or validity.
A verification-aware debugger must check applicable executable conditions
where possible and report unresolved predicates honestly. Proved conditions
may then be erased for value evaluation; one execution is not their proof.

Here `bad` abbreviates `1 div 0` only for this table:

| Source | Declarative obligation | Raw lazy value outcome |
|---|---|---|
| `let x := bad in 0` | nonzero-divisor check in incoming context | 0 |
| `let x := bad in if d != 0 then x else 0` | same incoming check, even at `d = 0` | 0 at `d = 0` |
| `false and (bad = 0)`; `true or (bad = 0)` | right-side check in incoming context | false; true |
| `false iff (bad = 0)`; `bad = bad` | same incoming check | undefined |
| `if false then bad else 0` | retained check under false guard | 0 |
| `if d != 0 then n div d else 0` | retained check under `d != 0` | 0 at `d = 0` |
| `ignore(bad)`, with `ignore(x: Int): Int := 0` | argument check retained | undefined |

The [native controls](../../FrenFlatToLirTests/Verification.lean) inspect
actual retained checks without evaluating guards, including checks beneath
constant-false branches, unused definitions and lexical lets. Independent
formula probes distinguish incoming from conditional contexts and kill the
old lazy-demand formulas as mutants. Value comparisons use only cases
with independently expected true verification domains. They do not prove
universal source-obligation completeness or solver correspondence.

## Sharing and attribution

**Proof obligations**

r[lir.walking.sharing]
A shared-term table contains only lexically closed, well-typed terms.
A `ref k` has its entry's sort, and entries refer only to earlier entries.
Terms with free local slots are shared only by scoped local lets, with
capture avoided and the original typed contexts respected.

Closed means no free lexical slots; a term may still mention declared
symbols. Sharing `x + 1` from one function or let context in a global table
would lose its binding. Closed sharing must not hoist a partial operation's
obligation out of its explicit guard. Acyclic references permit finite
expansion; expansion and local-let substitution must preserve values and
verification contexts, not just textual equality. Sharing is optional in the first walking
implementation; emitting no table is preferable to an unsound one.

r[lir.walking.attribution]
Lowering and sharing are deterministic in declaration and child order.
Origins and maps retain each source diagnostic occurrence, its canonical
owner and branch or binder context, even when values share a term.

Origins do not decide equality or hashing. Equal terms with different labels
still represent distinct checks. Table numbering and printed symbol naming
must not depend on hash-map iteration or erase nominal identities. The
concrete schema, versioned dump format and well-formed generator remain to
be delivered with the actual representation.

## Retained example

This small program lies in the walking source fragment. The goal appears
before its assumption deliberately.

```fren
pub mod lir_walk

pub enum Light { Red, Green }

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => base + 30,
    Light::Green => base,
}

expect waits(l: Light, base: Int) {
    expect limit: wait(l, base) <= 130
    assume bounded: base <= 100
}

#fren_check
```

Logical lowering must retain the enum, the definition of `wait`, then the
owned Sat and `limit` requests. Both requests carry `bounded`; neither
carries `limit` as an assumption. At entry, `base` is local slot zero and
`l` slot one. The Red branch adds mathematical 30 to that same `base`.
The fence is checked by Fren1, not an execution of logical lowering.
Removing `bounded` admits `l = Light::Red, base = 101`, which falsifies
`limit`; turning `limit` into a hypothesis would hide that mistake.

## Checked primitive facts

The following independent facts catch reversed counterexample polarity,
wrong branch guards and wrong value domains. They use today's Fren1 checker;
there is no Fren IR, executable pass model or production `impl` binding here.
The procedure and `when` syntax do not extend walking admission.

**Dynamic semantics**

r[lir.primitive.polarity] lir_example::primitive_facts::polarity
Failure of implication requires a true assumption and a false goal.

r[lir.primitive.guards] lir_example::primitive_facts::{then_guard, else_guard}
A nonzero-divisor condition is required only on its selected branch.

r[lir.primitive.strict] lir_example::primitive_facts::strict
Requiring both operand domains fails if either is absent, independently of
any simplifying identity of the values.

r[lir.primitive.integers] lir_example::primitive_facts::integers
Every integer has a smaller and a larger integer.

r[lir.primitive.enum] lir_example::primitive_facts::enum_domain
The example enum has exactly its two distinct constructors.

```fren
pub mod lir_example

pub enum Light { Red, Green }

pub proc primitive_facts(
    assumption?,
    goal?,
    selected?,
    left_wd?,
    right_wd?,
    d: Int,
    n: Int,
    l: Light,
) {
    expect polarity: (not (when assumption?, goal?)) iff (assumption? and not goal?)
    expect then_guard: (when selected?, d != 0) iff (not selected? or d != 0)
    expect else_guard: (when not selected?, d != 0) iff (selected? or d != 0)
    expect strict: (not (left_wd? and right_wd?)) iff (not left_wd? or not right_wd?)
    expect integers: n - 1 < n < n + 1
    expect enum_domain: (l = Light::Red) iff (l != Light::Green)
}

#fren_check
```

Changing `not goal?` to `goal?` in `polarity` is a deliberate negative
control: `assumption? = true, goal? = false` refutes it. Removing the
`not` before `selected?` in `then_guard` is refuted at `selected? = false,
d = 0`. These are primitive counterexamples, not Fren2 solver models.

## Actual-producer evidence and remaining laws

[Producer laws](../../FrenFlatToLir/Walking.lean) prove actual admission,
retention of the complete MIR and typed source, determinism, rejection
propagation and success of the output scope/retention checker. The latter
includes Boolean declaration/request retention certificates; it is not a
proof of their equality from unproved lawful-equality instances.
[Combinator laws](../../FrenLir/Walking.lean) prove the actual branch, let,
ordinary-operator and call domain equations, including both Boolean operands
and unused definitions. The retained `Verification` tree is the source of
the formula summary; no independently supplied definedness bit is accepted.
[Direct Plausible
properties](../../FrenFlatToLirTests/Properties.lean) exercise the actual
producer on mandatory admitted, rejected and partial classes, with explicit
premise counts and independent arithmetic/request expectations. Native
controls retain nominal identities, owned request roots and lexical origins,
and kill source, domain and retention mutants.

The universal laws below remain obligations, beyond those checked facts.

For every `p : FrenThirDesugar.Program` and `t : FrenMir.Theory` with
`FrenThirToMir.produce p = .ok t`, the logical-lowering producer must
succeed on this walking domain and return a well-formed program satisfying
the retention, requests, verification and sharing rules above.
For every retained value body or occurrence, in its recorded lexical
context, relate source and logical environments slot by slot at their
actual Bool, Int or canonical enum types. Under corresponding definition
interpretations and environments, declarative source obligations and LIR
verification information must correspond in both directions. Where those
obligations hold, values must correspond at the recorded result type. Raw
interpreter comparisons additionally require sufficient operational depth;
their undefinedness is not the source verification judgment. Lets require
exact scoped value/domain bindings, not just lists of unscoped values.

After the applicable definedness obligations are accounted for, assumption
satisfiability and each owned validity question must agree in both
directions over the same parameter domains. This includes empty blocks,
contradictory assumptions, assumptions after goals, nominal enums, unused
definitions and the declarative regressions above. These are laws about the
actual eventual producer and evaluators, not universal simulation theorems
proved by the six primitive facts.

- [x] Implement the walking representation and producer, with actual-code
  structural laws, direct Plausible over admitted, rejected and partial inputs,
  reported premise counts and independent native verification/context controls.
- [ ] Establish whole-term value, definedness and request preservation,
  beyond the actual static-scope audits and negative controls already tested.
- [ ] Restate these laws in Fren when recursive typed syntax, scoped
  outcome environments and recursive evaluation judgments can be expressed
  against the real code. No general quantifier or recursive-unfolding model
  is needed to deliver this nonrecursive walking slice.

The next OIR step must generate conditions from the retained scoped
verification information, separating each goal from its active assumptions
and branch guards. It must follow the existing
[definedness hypotheses](../../Reqs/Check.md#definedness),
including other assumptions when checking an assumption, rather than let
an undefined predicate disappear as false. Solver translation, Sat/validity
polarity, limits, unknown results and source-model confirmation then need
their own actual-path evidence. This chapter does not deliver OIR condition
generation, recursive unfolding, general quantifier expansion, an SMT
backend or a completed S1 solver result.
