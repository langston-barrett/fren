# Walking obligations (OIR)

Obligation generation turns retained verification information into logical
questions. A question records what must hold, under which assumptions and
branch guards, for which parameters, and at which source occurrence. Keeping
only a Boolean goal would lose the difference between an undefined assumption,
contradictory assumptions, an undefined goal and a false goal.

This chapter specifies the next boundary after [logical lowering](Lir.md).
The actual `FrenLir.Program` and its scoped verification trees exist;
`FrenOir` and `FrenLirToOir` are still empty module stubs. No OIR producer,
solver backend or completed S1 solver result is delivered here. The small
checked facts below constrain logical primitives independently of that future
implementation.

## Input and questions

**Proof obligations**

r[oir.walking.input]
The input is an actual successful `FrenFlatToLir.produce p` result, together
with that success and the accepted walking source witness. An arbitrary
edited `Program`, or a successful scope audit alone, is insufficient.

The admitted fragment has Bool, mathematical Int, nominal payload-free enums,
nonrecursive named functions, lexical lets, explicit conditionals and exhaustive
constructor matches, and global expectation blocks. The retained MIR and typed
source establish identities and contexts. This boundary adds no syntax,
recursive unfolding, procedure relations, general quantifiers, subset types,
closures or full mono/fo/flat pipeline. The quantifiers in the mathematical
contract below describe questions over parameters, not new source constructs.

r[oir.walking.requests]
Generate separate assumption-definedness, assumption-satisfiability,
goal-definedness and goal-validity questions from the actual retained bodies
and verification trees. Definitions retain their own verification questions,
even when unused. No required question may disappear because another passes.

`FrenMir.Block.requests` supplies one Sat request first, even for an empty
block, then a validity request for each written expectation. Its assumptions
are all and only that block's assumptions, including those written after a
goal. The corresponding LIR `CheckRequest` carries `source`, `assumptions`,
`question` and static `demand` roots. These roots are bodies to inspect, not
already proved facts or an execution trace. Generate assumption checks once
or share their results explicitly across requests of the same owner; preserve
every goal's identity and dependencies. Separate blocks never supply premises
to one another.

For a well-typed parameter assignment `i`, write `A_j(i)` for assumption
values, `A(i)` for their conjunction, and `E(i)` for one goal value. These
formulas use the retained definitions with their actual meanings. Once the
applicable definedness checks are established:

| Question | Mathematical condition | Solver search formula |
|---|---|---|
| Assumptions can hold | `exists i, A(i)` | `A(i)` |
| Goal follows | `forall i, A(i) implies E(i)` | `A(i) and not E(i)` |

Free parameters in a solver search range existentially over their complete
typed domains. Bool has two values, Int all integers, and each enum exactly
its own canonical constructors. The empty conjunction is true. The empty
parameter tuple has one assignment. These domains are inhabited in this
walking fragment, so an empty block's Sat question succeeds mathematically.
Contradictory assumptions make validity vacuous and Sat fail; a vacuous
validity result cannot establish a successful block.

## Definedness and hypotheses

**Proof obligations**

r[oir.walking.definedness]
Generate each domain condition from the retained `Verification` tree in its
lexical and conditional context, independently of the truth of its owner's
goal. Undefined assumptions cannot be treated as false to filter assignments,
make Sat fail, or make validity pass.

Let `H` be the admissible hypotheses for an occurrence, `B` its explicit
branch guard and `C` its required domain condition. Its proof question is
`forall i, (H(i) and B(i)) implies C(i)`; its counterexample search is
`H(i) and B(i) and not C(i)`, with any local binders still scoped. The
condition and its context come from actual terms, never a supplied
"already defined" flag. Solver failure to prove `C` does not create
mathematical undefinedness. Values of partial operations outside their
domains are unspecified and cannot discharge these conditions.

The existing [definedness hypotheses](../../Reqs/Check.md#definedness)
permit the other assumptions when checking an assumption; its own value is
excluded. A global expectation's goal uses its block assumptions, never
itself or sibling goals. A walking function body has no written
preconditions, hence no block hypotheses: its written domain obligations
must be checked over its own parameters, even when the function is unused.
Definitions supply value and domain equations for their actual bodies, not
arbitrary axioms asserting that the bodies are always defined. A call also
retains argument checks and the callee-domain application.

r[oir.walking.dependencies]
A hypothesis used for a definedness or validity result must have justified
definedness in the relevant context. Neither an unproved goal nor an
unjustified domain assumption may establish itself through a dependency
cycle. Results record these dependencies and retain unresolved ones.

There is a concrete unresolved semantic choice at this boundary. The legacy
other-assumptions rule does not specify how to establish the definedness of
those *other* assumptions without circularity. For example, two assumptions
`1 div d = 0` and `1 div d != 0` must not jointly discharge both divisor
checks merely because their Boolean conjunction is contradictory. Likewise
neither may use its own truth to prove `d != 0`. By contrast, the independent,
total assumption `d != 0` can justify a sibling division's domain check.

Before admitting general mutually partial assumptions, the producer needs a
precise, sound rule for this dependency problem, compatible with contextual
definedness. Possible approaches require a justified dependency ordering or
a separately proved simultaneous rule; this chapter chooses neither. It does
not silently replace the legacy rule with unconditional definedness of every
assumption over all parameters. A consumer lacking that rule must retain the
questions and report the affected result unresolved/unsupported, with the
reason, rather than claim a verified block. Tests of total assumptions cannot
close this gap. This is a pending part of OIR semantics, not a new source
feature or separate crossover gate.

## Static traversal, guards and bindings

**Proof obligations**

r[oir.walking.traversal]
Visit both sides of every ordinary operator and every written definition.
Only explicit branch scopes add conditional contexts. Do not use a raw
left-to-right short-circuit trace to select static obligations.

For the actual `FrenLir.Verification` constructors:

| Tree | Condition generation |
|---|---|
| `empty` | no domain question |
| `check C` | require `C` under the current context |
| `both a b` | visit both in the same incoming context |
| `branch c a b` | visit `a` under `B and c`, `b` under `B and not c` |
| `letE binder ty value domain body` | keep the exact scoped value/domain binding while visiting `body` |
| `at origin body` | retain that occurrence's origin while visiting `body` |

The surrounding tree retains the condition's own obligations before its
branch. A guard's use requires its own definedness; treating an undefined
condition as false is unsound. Constructor matches retain nominal tests and
the corresponding arm guards. Keep even constant-false guarded occurrences
for attribution; proving their guarded questions trivial does not erase the
written checks. `Lowered.defined` is a formula summary of this tree, not an
independent proof and not a replacement for per-occurrence attribution.

Ordinary `a and b`, `a or b`, `iff` and equality retain both operand
domains in the incoming context. A let retains its definition's checks there
even when the body ignores it; its body's checks stay under the binder.
Thus `false and (1 div 0 = 0)`, `true or (1 div 0 = 0)` and
`let x := 1 div 0 in 0` retain an unguarded nonzero-divisor obligation.
`if false then 1 div 0 else 0` retains that obligation under false;
`if d != 0 then n div d else 0` retains it under `d != 0`.
The raw [evaluator](Evaluator.md) may return a value for skipped operands or
unused lets; that execution does not discharge any of these source checks.

r[oir.walking.scope]
Retain ordered typed parameters, nearest-first local slots, canonical symbol
identities, explicit guards, owner and source occurrence through extraction,
sharing and substitution. No open condition becomes an unconditional global
fact, and equal conditions at different occurrences remain attributable.

A let value is interpreted in the incoming context; its body prepends the
binder. Shadowed names remain distinct slots. Substitution must transport
both value and domain components without capture. Calls enter the callee's
ordered parameter context without caller locals. In particular, the check
for `let x := 1 div d in if d != 0 then x else 0` belongs at the let
definition, outside the conditional. Moving it under the use's guard changes
the source policy. Closed term sharing may share formulas, but must preserve
the distinct diagnostic occurrences, guards and dependency edges. Emit
questions deterministically in declaration and child order, not hash order.

Scoped assume/assert expressions and subset conditions are future consumers
of this interface, as specified in [Expressions](../Language/Expressions.md).
They retain local assumptions and asserted predicates until extraction;
assertions require proof, and subset introduction/coercion requires proving
the predicate for the introduced value. An already-established parameter
predicate may be a scoped body hypothesis. None of these forms is admitted
by the current walking grammar or implemented by this chapter.

## Answers and source confirmation

**Proof obligations**

r[oir.walking.answers]
Interpret Sat and validity answers with their distinct polarities. Preserve
unknown, unsupported, invalid-input and resource-exhaustion results and their
reasons. None is false, a proof, or permission to drop a required question.

For the assumption search `A`, Sat supplies a candidate witness and Unsat
establishes contradictory assumptions. For `A and not E`, Sat supplies a
candidate counterexample and Unsat establishes validity, subject to the
definedness and dependency checks above. Domain counterexamples use the same
negated-condition polarity. Unknown establishes neither side. Report each
required result separately, including consistency and vacuity, and cap any
aggregate success by unresolved dependencies, following
[Checks](../../Reqs/Check.md#global-expectations) and
[Evidence](../../Reqs/Evidence.md). A bounded search finding no witness does
not establish Unsat. Bounded satisfiability or finite tests do not establish
general consistency of a theory or universal validity. A confirmed witness
from bounded search can establish this particular existential Sat question;
it says nothing about the other questions.

r[oir.walking.confirmation]
Before reporting a solver model as a source witness or counterexample,
confirm the relevant assumptions, guards, domains and failing goal against
the retained source meanings and complete parameter assignment.

For a validity counterexample, all block assumptions must be true and
defined, the goal defined and false. For a domain failure, confirm its
admissible context and guard and the failed domain condition instead; an
undefined goal is not a false goal. For a Sat witness, confirm the assumptions
and their domains. Retain owner, member label, source span and nominal values
in each report. Raw evaluation alone is insufficient when it skips static
checks. Unsupported or exhausted confirmation leaves a candidate unconfirmed,
with its reason; it cannot become a source failure or pass. Finite model
confirmation validates that assignment, not a universal preservation theorem.

## Checked primitive facts

These independent Fren1 facts specify truth-table and quantifier primitives.
They do not copy an IR, implement extraction, take a precomputed pass decision
as input, or bind a nonexistent producer with `impl`. The procedure and
quantifier syntax below do not extend walking admission.

**Dynamic semantics**

r[oir.primitive.polarity] oir_primitives::facts::polarity
A failed implication requires a true hypothesis and false goal.

r[oir.primitive.guards] oir_primitives::facts::{then_guard, else_guard}
The positive and negative branch guards give different conditional domains.

r[oir.primitive.operands] oir_primitives::facts::both_domains
Requiring both ordinary operand domains is independent of operand values.

r[oir.primitive.vacuity] oir_primitives::facts::vacuity
Contradictory hypotheses imply a goal without supplying a witness.

r[oir.primitive.quantifiers] oir_primitives::facts::witness_not_universal
Existence of a satisfying Boolean assignment does not imply all satisfy it.

```fren
pub mod oir_primitives

pub proc facts(assumption?, goal?, selected?, left_domain?, right_domain?, d: Int) {
    expect polarity: (not (when assumption?, goal?)) iff (assumption? and not goal?)
    expect then_guard: (when selected?, d != 0) iff (not selected? or d != 0)
    expect else_guard: (when not selected?, d != 0) iff (selected? or d != 0)
    expect both_domains: (not (left_domain? and right_domain?)) iff (not left_domain? or not right_domain?)
    expect vacuity: not (assumption? and not assumption?) or goal?
    expect witness_not_universal: (exists (b?: Bool), b? = goal?) and not (forall (b?: Bool), b? = goal?)
}

#fren_check
```

Changing `not goal?` to `goal?` on the right of `polarity` is deliberately
false at `assumption? = true, goal? = false`. Replacing `not selected?`
with `selected?` on the right of `then_guard` is false at
`selected? = false, d = 0`. These controls must actually fail the checker;
their counterexamples are primitive Fren1 results, not Fren2 solver models.

## Remaining actual-pass laws

All eight `oir.walking.*` rules above are pending actual-producer obligations.
The primitive facts prove none of the following whole-pass statements:

- [ ] For every actual successful admitted LIR production, extraction either
  produces well-formed contextual questions for every retained verification
  occurrence and MIR request, or reports the exact unsupported boundary.
  Establish the partial-assumption dependency rule before claiming success
  for that class of inputs.
- [ ] Prove both directions of correspondence between those questions and
  declarative source obligations, under related typed environments and actual
  definition interpretations. Preserve let substitution, explicit guards,
  unused bodies, ordinary operands, owners and every diagnostic occurrence.
- [ ] Prove that after independently established applicable domains, each
  owned Sat and validity request agrees in both directions with the formulas
  above over the complete parameter domains. Never infer validity from its
  own goal or consistency from bounded search.
- [ ] Test the actual producer directly, with premise counts for admitted,
  partial, contradictory and unsupported classes. Delete a check, use the
  wrong owner or slot, guard an ordinary operand, move a let check, insert a
  goal as a premise and flip counterexample polarity as negative controls.
- [ ] Bind solver translation and later source-model confirmation to the
  actual code, retaining unknown and exhaustion. Restate recursive scoped
  laws in Fren when it can express them against that code. No copied Fren
  pass model or plausible-only `impl` substitutes for these laws.

The existing MIR request laws and LIR constructor equations establish useful
retention and local structure. They are not OIR extraction proofs. This
chapter leaves general pipeline soundness and the actual producer to later
units while making their required boundary explicit.
