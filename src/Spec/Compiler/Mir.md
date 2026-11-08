# Walking MIR and theory construction

The mid-level intermediate representation (MIR) separates what a module
**defines** from what it asks Fren to **check**. A function contributes its
signature and body. A global expectation contributes assumptions and goals
over its parameters. MIR carries these meanings toward logical lowering
(LIR), obligation generation (OIR) and SMT solving, as described in the
[compiler overview](Overview.md).

This chapter specifies the next producer, `FrenThirToMir`, for the current
[walking desugaring](Desugaring.md) boundary. `FrenMir` and `FrenThirToMir`
are currently empty module stubs. The rules below are requirements for their
future real code, not properties already proved of a producer. They fix
observable information and meaning without freezing a final IR datatype,
printed format or generator.

## Admitted input and retained identity

**Proof obligations**

r[mir.walking.admission]
The input carries evidence of actual successful walking admission and
identity desugaring, including successful typing, coverage and non-recursion.

`FrenThirDesugar.Program` contains `input`, `typed` and
`accepted : checkWalking input = .ok typed`; `desugar` is the identity on
that program. `fromSource` parses and resolves before this checked boundary.
A caller-edited `Typed` record, successful type-only `check`, or supplied
validity Boolean is insufficient. Admission failures remain failures before
MIR construction. The admitted fragment has Bool, Int, nominal payload-free
enums, nonrecursive expression-bodied named functions, global expectations,
and their existing literals, names, parentheses, operators, calls, `if`,
`let` and exhaustive constructor matches.

**Proof obligations**

r[mir.walking.retention]
Successful construction retains the complete admitted source and its
identities, declaration order and distinct diagnostic occurrences.

The source includes the document, file identity, token tape and UTF-8 byte
spans. Canonical module, enum, constructor, function and expectation
`ItemId`s remain traceable through construction; constructor ownership and
resolved call targets remain unchanged. Rendered names do not replace those
identities. Definitions and requests follow declaration order, with members
and children in written order, independently of lookup-table iteration.
Structural sharing does not merge separate diagnostic occurrences. Origins
remain diagnostic data, not semantic identity.

## Declarations and check requests

A *theory* packages a module's declarations and statements about them.
This walking theory needs enum declarations, function signatures and bodies,
and global expectation checks. A *check request* identifies a question to
be answered later; it is not a verdict or a solver query already executed.

**Proof obligations**

r[mir.walking.definitions]
Every admitted enum and function contributes its canonical declaration;
each function's signature and defining body remain separate from check goals.

Retain enum constructors in declaration order and distinguish two nominal
enums even if their constructors have the same spelling. A function keeps
its ordered parameter types and declared result type, together with its
actual defining expression and resolved dependencies. Calls refer to that
function, with arguments in positional order. A definition supplies meaning
to calls; it is neither an unchecked arbitrary axiom nor a global expectation
to be proved. Unused declarations and unselected written branches are not
erased at this boundary. Matches remain matches here; compiling them belongs
to the later match-lowering stage.

**Proof obligations**

r[mir.walking.contexts]
Each definition, member and derived obligation retains its exact source
parameter and lexical binder context, or an explicit correspondence to it.

`Typed.signatures` holds function signatures. `Typed.bodies` contains
function bodies with `member = none`, and each check member with its full
`FrenAst.Member` in `member = some ...`. That member includes kind, label,
body and source tokens. Bodies retain `context` and typed postorder
`occurrences`; each occurrence has its own context. A global expectation
with no members still exists in the retained document: traversing bodies
alone cannot recover every check owner and its parameters.

Parameters are written left to right and stored nearest first for locals:
in `wait(l, base)`, `base` is index zero and `l` index one. A let value uses
the incoming context; its body prepends the new binder, even if another
binder has the same spelling. Constructor patterns introduce no slots.
A call enters its callee's parameter context with the checked positional
arguments, without inheriting the caller's local slots. Equal types or
spellings do not justify substituting another context.

**Proof obligations**

r[mir.walking.members]
Every global expectation retains its ordered assume/expect members, their
labels, canonical owner, Bool bodies and parameter context.

r[mir.walking.assumptions]
Assumptions restrict the parameter assignments relevant to every expectation
of their owning block; they do not become proved goals or global axioms.

r[mir.walking.goals]
Each expectation member creates its own validity request under its owning
block's assumptions and the applicable function definitions, without taking
itself or another unproved expectation as a hypothesis.

For parameter assignment `i`, let `A(i)` be the conjunction of the block's
assumptions and `E(i)` one expectation, with named function calls interpreted
by their definitions. On defined evaluations, validity means that every
assignment satisfying `A(i)` satisfies `E(i)`. A counterexample must satisfy
`A(i)` and falsify `E(i)` in the same context. All assumptions of the block
apply, including those written after an expectation. Preserving member order
does not turn this into a sequential prefix of assumptions. Assumptions from
another block and facts from an incompatible branch do not enter the request.
These are the current [global expectation semantics](../../Reqs/Lang/Global.md#meaning)
and [checking rules](../../Reqs/Check.md#global-expectations), specialized to
this fragment without procedure calls, outputs or guarantees.

**Proof obligations**

r[mir.walking.satisfiability]
Each block global expectation also requests that its assumptions can hold;
an unsatisfiable assumption set fails this check independently of validity.

This is the current realizability check with no outputs. Even a block with
no written assumptions asks it: its conjunction is true, over the declared
parameter domains. Contradictory assumptions may entail every expectation
vacuously while this separate check fails. This fragment has no written
`when` triggers, so it does not add a trigger-vacuity request to every member.
Future trigger syntax must follow the distinct
[vacuity rule](../../Reqs/Check.md#vacuity). Solver limits and unknown results
remain inconclusive, never successful evidence.

## Definedness and correspondence

**Proof obligations**

r[mir.walking.partiality]
Construction preserves partial operations, their operands, demand contexts
and source occurrences, with the information needed for their definedness
obligations; it never substitutes false, a default value or an unexplained
axiom for an undefined operation.

For example, division and remainder require a nonzero divisor. In
`if d != 0 then n div d else 0`, the condition selects the branch in which
that operation is demanded. A future logical encoding must account for
partiality as well as the result; retaining only an equation about a result
is insufficient. An undefined assumption cannot silently exclude assignments
as though it were a false Boolean, and an undefined expectation is not a
proved or refuted expectation.

**Proof obligations**

r[mir.walking.values]
The future actual producer preserves defined source and MIR values in both
directions at corresponding types, canonical identities and environments,
together with the conditions under which those values are defined.

r[mir.walking.check-correspondence]
The future actual producer preserves the source assumptions and obligations
and their contexts in both directions, including assumption satisfiability,
expectation validity and required definedness checks.

These are obligations about the eventual real producer and consumers.
They require more than a value-only commuting square. Dropping `bounded`
from the example below changes validity even if every function still returns
the same value. Assuming `at_most` rather than checking it makes a false
claim pass. Using the wrong local slot changes both function values and
the meaning of assumptions.

There is a current partiality mismatch to resolve before claiming a general
outcome simulation. The accepted [walking evaluator](Evaluator.md) eagerly
evaluates let values and both operands of `and` and `or`. The design's
demand-based assert insertion and the current Language
[evaluation rules](../../Reqs/Lang/EvaluationRules.md#let-expressions) make
let definitions and the right operands of `and` and `or` lazy. `iff`, Boolean
equality/inequality and ordinary call arguments remain strict. For example,
`let x := 1 div 0 in 0` does not demand `x` in its body, but the actual
walking interpreter reports undefined. This chapter retains the deciding
syntax and contexts and records the mismatch; it does not claim these
outcomes are equal or choose a new language rule. The total examples below
are unaffected. Full partial-outcome correspondence remains pending this
reconciliation.

The actual interpreter also distinguishes semantic undefinedness,
operational depth exhaustion, invalid requests/arguments and unsupported
operations, with associated spans and details. These distinctions must
remain visible in any evaluator correspondence used to validate construction;
exhaustion is not a logical falsehood or an unsatisfiable assumption set.
A later solver may encode unspecified values as required by the Language
semantics, but that is separate from concrete interpreter outcomes and must
retain the required definedness obligations and their guards.

## Walking example and independent facts

`Light` has three nominal values. `next` cycles through them; `wait` adds
an offset to `base`. The bounded assumption belongs to `waits`, and no
expectation is available as a hypothesis for another expectation.

```fren
pub mod mir_example

pub enum Light { Red, Amber, Green }

pub fn next(l: Light): Light := match l {
    Light::Red => Light::Green,
    Light::Green => Light::Amber,
    Light::Amber => Light::Red,
}

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => base + 30,
    Light::Amber => base + 5,
    Light::Green => base,
}

expect cycles(l: Light) { expect back: next(next(next(l))) = l }

expect waits(l: Light, base: Int) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}
```

The following three small facts independently fix arithmetic offset,
Boolean implication and the Amber row used in the example. Fren1 checks
these facts and the preceding true examples. They neither model MIR nor
prove a future pass, evaluator or solver correct. The procedure and `when`
syntax below belong to Fren1's contract language; they do not extend the
admitted walking grammar.

**Dynamic semantics**

r[mir.primitive.offset] mir_example::primitive_facts::offset
Adding thirty and subtracting the original integer gives thirty.

r[mir.primitive.implication] mir_example::primitive_facts::implication
Boolean implication holds exactly when its premise is false or its
conclusion is true.

r[mir.primitive.amber] mir_example::primitive_facts::amber
The example's next light after Amber is Red.

```fren
pub proc primitive_facts(base: Int, l: Light, premise?, conclusion?) {
    expect offset: base + 30 - base = 30
    expect implication: (when premise?, conclusion?) iff (not premise? or conclusion?)
    expect amber: when l = Light::Amber, next(l) = Light::Red
}

#fren_check
```

The original S1 adds this deliberately false block, shown as text so that
the book's checked examples remain successful:

```text
expect wrong(l: Light) {
    expect never_red: next(l) != Light::Red
}
```

For S1's three blocks alone, the intended future Fren2 solver output is
exactly **5 passed, 1 failed**: `back` and `at_most` pass, each of the three
blocks' assumption-satisfiability checks passes, and `never_red` fails with
`l = Light::Amber`. This is an acceptance target for the future complete
pipeline, not solver evidence currently computed by Fren2. In particular,
a concrete interpreter returning false at Amber is not delivery of a solver
counterexample. Removing `bounded` is a separate negative control:
`l = Light::Red, base = 101` makes `at_most` false. The chapter's positive
Fren fences do not contain either deliberate failure.

## Pending implementation evidence

The three primitive facts have Fren1 checks. There is no MIR producer,
production `impl` binding, MIR evaluation or general simulation theorem yet.
The eleven `mir.walking.*` rules are pending contracts, not eleven proofs.

- [ ] Implement the actual admitted walking producer and its retained theory
  information, with explicit failure data and deterministic declaration order.
- [ ] Bind the actual code to admission, retention, definitions, contexts and
  member contracts, using Lean proofs where cheap.
- [ ] Establish actual value, assumption and obligation correspondence,
  including satisfiability and definedness, and reconcile the partiality
  mismatch before claiming general outcome preservation.
- [ ] Test the real code directly with Plausible, reporting premise counts
  for admitted, rejected and partial inputs. Include mutations that drop an
  assumption or obligation, flip a role and use the wrong context.
- [ ] Connect downstream requests to real LIR/OIR/SMT and confirm source
  counterexamples, including S1's Amber result. A Fren1 negative control
  demonstrates sensitivity of the example, not sensitivity of future code.

Interfaces, views, morphisms, recursive groups, subset erasure, procedure
relations, generic and closure elimination, a full MIR schema and Lean
emission remain future scope. This slice does not implement OIR or claim
that current requests have already been solved.
