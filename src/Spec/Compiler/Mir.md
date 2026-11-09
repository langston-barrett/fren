# MIR and theory construction

The mid-level intermediate representation (MIR) separates what a module
**defines** from what it asks Fren to **check**. A function contributes its
signature and body. A global expectation contributes assumptions and goals
over its parameters. MIR carries these meanings toward logical lowering
(LIR), obligation generation (OIR) and SMT solving, as described in the
[compiler overview](Overview.md).

This chapter specifies the [desugaring](Desugaring.md)-to-MIR boundary.
It retains typed expressions and separates definitions from explicit check
requests. The rules fix observable information and meaning independently
of a particular storage layout.

## Admitted input and retained identity

**Proof obligations**

r[mir.walking.admission]
The input carries evidence of actual successful source admission and
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
This theory needs enum declarations, function signatures and bodies,
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
Construction preserves partial operations, their operands, verification contexts
and source occurrences, with the information needed for their definedness
obligations; it never substitutes false, a default value or an unexplained
axiom for an undefined operation.

For example, division and remainder require a nonzero divisor. In
`if d != 0 then n div d else 0`, that obligation has the explicit branch
context `d != 0`. Ordinary `and`/`or` retain both operands' obligations in
the incoming context. An unused let definition retains its own obligations.
The required contexts come from written syntax, not a concrete execution
trace. An undefined assumption cannot silently exclude assignments as a
false Boolean, and an undefined expectation is not a verified goal.

**Proof obligations**

r[mir.walking.values]
The producer preserves defined source and MIR values in both
directions at corresponding types, canonical identities and environments,
together with the conditions under which those values are defined.

r[mir.walking.check-correspondence]
The producer preserves the source assumptions and obligations
and their contexts in both directions, including assumption satisfiability,
expectation validity and required definedness checks.

These obligations relate the actual producer and consumers.
They require more than a value-only commuting square. Dropping `bounded`
from the example below changes validity even if every function still returns
the same value. Assuming `at_most` rather than checking it makes a false
claim pass. Using the wrong local slot changes both function values and
the meaning of assumptions.

The raw [value evaluator](Evaluator.md) implements a lazy value strategy:
an unused `let x := 1 div 0 in 0` returns 0, and deciding-left Boolean
operands may skip their right side. Those concrete outcomes do not establish
source well-definedness. Declarative verification traverses all written
expressions, retaining both ordinary Boolean operands' checks and unused
definitions' checks. Only explicit if/match/guard scopes make them conditional.
[LIR](Lir.md) retains the actual scoped verification trees and value/domain
symbols; it does not yet generate or solve OIR conditions.

The interpreter's undefined, exhausted, invalid and unsupported failures
remain distinct. Exhaustion cannot become logical falsehood, an unsatisfiable
assumption set or evidence of validity. Value correspondence under established
well-definedness and static obligation completeness are separate obligations.

## Example and arithmetic laws

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
prove a pass, evaluator or solver correct. The procedure and `when`
syntax below belong to Fren1's contract language; they do not extend the
admitted source grammar.

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

A deliberately false expectation, such as `next(l) != Light::Red`, remains
a typed validity request. It fails mathematically at `l = Light::Amber`.
Removing `bounded` makes `at_most` false at `l = Light::Red, base = 101`.
These counterexamples describe the formulas' meanings, not solver evidence.
