# Walking logical lowering (LIR)

Logical lowering turns a retained program into first-order terms suitable
for asking logical questions. It must preserve both a term's value and
where that value is defined. Keeping only Boolean formulas would lose the
difference between a false expectation and an undefined one.

This chapter specifies the next walking boundary after the actual
[MIR producer](Mir.md). There is no LIR producer, logical evaluator or solver
backend yet: `FrenLir`, `FrenFlatToLir` and `FrenLirEval` are stubs. The
contract below concerns their eventual real code. The checked primitive
facts at the end are independent tests of the contract's ingredients.

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
Arithmetic, precedence and branch selection come from the existing
[Language rules](../../Reqs/Lang/Expressions.md#operators) and
[evaluation rules](../../Reqs/Lang/EvaluationRules.md), not a new LIR language
semantics.

The walking logical vocabulary needs typed local variables, literals and
nominal constructor constants, first-order symbol applications, primitives,
conditionals (`ite`), constructor tests and scoped local lets. Exhaustive
matches can become constructor tests and conditionals, provided the selected
arm's value and demand are preserved. Partial-operation obligations remain
attached to their demand structure until condition generation; no solver
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

## Values travel with demand

**Proof obligations**

r[lir.walking.demand]
Lowering preserves the source demand structure until it has an explicit
encoding that guards every partial-operation obligation correctly. It
preserves assumption and goal demand roots separately from Boolean values.

For reasoning, write `V(e)` for the symbolic value and `WD(e)` for semantic
definedness. This notation is not a second interpreter or a delivered pair
datatype. Outside its domain a partial operation has an unspecified but
fixed symbolic value; its required definedness check still exists. That
symbolic value does not discharge definedness, and an interpreter's undefined
outcome is not Boolean false.
In particular, simplifying `e = e` to true must not discard the demand for
`e` when equality is strict.

The [walking evaluator](Evaluator.md) already distinguishes undefined,
exhausted, invalid and unsupported outcomes. Its operational depth is not
a logical domain restriction. A later comparison of evaluators must account
for sufficient depth explicitly; exhaustion cannot become undefined, false,
a Sat failure or evidence of validity.

The following demand rules are inherited from the Language and the actual
`FrenEval.walk`, rather than replacements for them:

- Ordinary unary and binary operations demand their operands, left to right.
  Division and remainder also require a nonzero divisor. `iff` and Boolean
  equality and inequality are strict, even where their values agree with a
  formula that could short-circuit.
- Calls demand every positional argument, even if the function body does
  not read its parameter. The body then uses those values in the callee's
  context. Inlining must preserve this argument demand.
- A let binds an outcome. Its definition's partiality matters only where
  the bound slot is read; binding alone imposes no unguarded `WD` obligation.
- `a and b` demands `a`, and demands `b` only where `a` is true.
  `a or b` demands `a`, and demands `b` only where `a` is false.
- A conditional demands its condition and only the selected branch. A match
  demands its scrutinee and only the arm selected by its canonical constructor.

Thus, for defined Boolean `c`, branch obligations are guarded by `c` for
then and `not c` for else. More generally a conditional requires `WD(c)`
as well as `(V(c) implies WD(then))` and
`(not V(c) implies WD(else))`. An unguarded conjunction of both branches'
definedness is wrong. A bare branch value does not justify using its guard
without establishing the condition's definedness. A shared or inlined let
must retain the guards at its uses, rather than demand its definition at
the binding site.

These concrete regressions constrain the eventual producer and consumer;
`bad` abbreviates `1 div 0` in this table, not a new source construct.

| Source expression or call | Required concrete outcome |
|---|---|
| `let x := bad in 0` | defined, 0 |
| `let x := bad in if d != 0 then x else 0`, at `d = 0` | defined, 0 |
| the preceding let at `d = 1` | undefined |
| `false and (bad = 0)`; `true or (bad = 0)` | defined, false; defined, true |
| `true and (bad = 0)`; `false or (bad = 0)` | undefined |
| `false iff (bad = 0)`; `(bad = bad)` | undefined |
| `if d != 0 then n div d else 0`, at `d = 0` | defined, 0 |
| `match l { Light::Red => bad, Light::Green => 0 }`, at Green | defined, 0 |
| `ignore(bad)`, where `ignore(x: Int): Int := 0` | undefined |

The match row uses exactly the two-constructor enum below. Static admission
still visits unselected written branches. These examples must also be tested
inside retained assumption and expectation bodies, with unused and repeated
let reads, nested shadowing and calls. They are future actual-path regression
targets here, not claimed executions of LIR.

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
obligation out of its demand guard. Acyclic references permit finite
expansion; expansion and local-let substitution must preserve values and
demand, not just textual equality. Sharing is optional in the first walking
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

## Actual-producer laws still to establish

For every `p : FrenThirDesugar.Program` and `t : FrenMir.Theory` with
`FrenThirToMir.produce p = .ok t`, the eventual real logical-lowering
producer must succeed on this walking domain and return a well-formed
program satisfying the retention, requests, demand and sharing rules above.
For every retained value body or occurrence, in its recorded lexical
context, relate source and logical environments slot by slot at their
actual Bool, Int or canonical enum types. Under corresponding definition
interpretations and environments, definedness must agree in both
directions; where defined, values must correspond at the recorded result
type. Lets require outcome-aware environments, not just lists of values.

After the applicable definedness obligations are accounted for, assumption
satisfiability and each owned validity question must agree in both
directions over the same parameter domains. This includes empty blocks,
contradictory assumptions, assumptions after goals, nominal enums, unused
definitions and the demand regressions above. These are laws about the
actual eventual producer and evaluators, not universal simulation theorems
proved by the six primitive facts.

- [ ] Implement the real representation and producer, then state and test
  these laws directly in Lean, with Plausible over admitted, rejected and
  partial inputs and reported premise counts; prove structural laws where cheap.
- [ ] Establish whole-term value, definedness and request preservation;
  test actual guards and negative controls without a copied compiler model.
- [ ] Restate these laws in Fren when recursive typed syntax, scoped
  outcome environments and recursive evaluation judgments can be expressed
  against the real code. No general quantifier or recursive-unfolding model
  is needed to deliver this nonrecursive walking slice.

The next OIR step must generate conditions from the retained demand,
separating a goal from its active assumptions and branch guards. It must
follow the existing [definedness hypotheses](../../Reqs/Check.md#definedness),
including other assumptions when checking an assumption, rather than let
an undefined predicate disappear as false. Solver translation, Sat/validity
polarity, limits, unknown results and source-model confirmation then need
their own actual-path evidence. This chapter does not deliver OIR condition
generation, recursive unfolding, general quantifier expansion, an SMT
backend or a completed S1 solver result.
