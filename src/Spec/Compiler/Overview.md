# Compiler overview

The compiler turns Fren source into checks and Lean declarations. Its
intermediate representations (IRs) separate name resolution, type checking,
logical lowering and the construction of solver obligations. This chapter
sets the contracts shared by their chapters; those chapters define the
individual representations and passes.

## Pipeline

Both the command-line and hosted front ends accept Fren source. A hosted
`fren { … }` command supplies its body to the same parser as a source file.

**Dynamic semantics**

r[compiler.pipeline.parser]
Both front ends use one parser and share the pipeline after parsing.

r[compiler.pipeline.stages]
The compiler processes an item through the following stages in order, except
that Lean emission takes MIR as its input.

| Stage | Produced by | Representation |
| --- | --- | --- |
| AST | Parsing | Lossless source tree, including tokens and trivia. |
| HIR | Name resolution | Surface forms with paths and names resolved to items or binders. |
| THIR | Type checking | Surface forms with types, overloads, fields and views resolved. |
| Desugared THIR | Desugaring | Typed expressions with surface sugar replaced by its meaning. |
| MIR | Logical elaboration | Theories, signatures, definitions, sentences and check requests, with obligations and assumptions explicit. |
| `mono` | Instance collection and monomorphization | Uses specialized to their generic instances. |
| `fo` | Closure lowering | First-order uses, by specialization or defunctionalization. |
| `flat` | Match compilation | Matches replaced by tests, selections and conditionals. |
| LIR | Logical lowering and sharing | First-order logical terms and shared closed terms. |
| OIR | Obligation generation | Goals with their active hypotheses, methods and contexts. |
| SMT-LIB | Solver emission | Solver declarations and queries for those obligations. |
| Lean | Lean emission from MIR | Lean declarations and propositions corresponding to MIR. |

r[compiler.pipeline.order]
Monomorphization precedes closure lowering, which precedes match compilation.

This table is the intended order. The implementation does not yet follow it
between desugaring and MIR: [MIR construction](Mir.md) does not read desugared
THIR. It reads the [walking program](Walking.md), the legacy type checker's
result over the written syntax, and the desugaring pass's output has no
consumer yet.

A theory packages declarations and sentences about them. For example, an
interface contributes abstract operations and laws; a view supplies an
interpretation of them and obligations for its laws. A check request asks
for a verdict on a particular sentence or obligation. OIR makes its
hypotheses explicit: the goal in the `then` branch of `if b` may assume `b`,
while the goal in the other branch may assume `not b`.

## Phase-specific forms

An IR phase determines which forms may occur. The table describes availability,
not a concrete datatype layout. “Through” includes both endpoints; later
chapters specify each form and its well-formedness.

**Legality rules**

r[compiler.forms.phases]
Each representation admits only the forms available at its phase.

| Form | Availability |
| --- | --- |
| Source tokens, comments and whitespace | AST |
| Unresolved paths and names | AST |
| Resolved surface sugar, including `where` and `table` | HIR through THIR |
| Inferred type annotations and resolved overloads and views | THIR onward, in the form appropriate to each phase |
| Desugared expressions | Desugared THIR through `flat` |
| Written type syntax, including subset-type arguments | HIR through desugared THIR; subset types erased in MIR with assumptions and obligations |
| Generic uses | HIR through MIR; instances replace them in `mono` |
| Closures and function-typed parameters | HIR through `mono`; lowered in `fo` |
| Pattern matches | HIR through `fo`; compiled in `flat` |
| First-order logical terms and sharing | LIR and OIR |
| Goals and their active hypotheses | OIR |

The rows that name desugared THIR describe the intended pipeline. Until MIR
construction reads desugared THIR, the expressions MIR is built from are the
[walking program](Walking.md)'s written expressions, which still contain
parentheses.

A declared subset type may remain as signature metadata after erasure. For
example, a value entering a positive-integer subset carries an obligation to
satisfy its invariant; a bound variable of that subset may assume it.
Erasing the type alone would lose both facts.

## Identity and origin

A local binder is identified by its distance from a use, not by its spelling.
In `|x| |y| x`, the use of `x` refers past the `y` binder. Renaming either
binder does not change that reference.

**Dynamic semantics**

r[compiler.identity.binders]
Local binding uses de Bruijn indices, with the index interpreted in its
binding context.

r[compiler.identity.items]
An item is identified by its path, including its enclosing module and item.

r[compiler.identity.instances]
An instance is identified by its item and complete canonical substitution,
including type arguments, view arguments and closure identity where applicable.

r[compiler.identity.origins]
Origins record source spans and derivation steps for diagnostics and debugging.

r[compiler.identity.origin-independence]
Origins do not decide equality, hashing, or compiler behavior.

r[compiler.identity.occurrences]
Distinct diagnostic occurrences remain distinct even when their expressions
are structurally equal.

For example, two applications of a generic function at the same type but with
different view implementations are different instances. Two identical
assertions at different source locations are different diagnostic
occurrences. Moving a term to another item remaps its origins; a semantic
choice needed by a later pass is represented independently of those origins.

## Work and correctness

An item is a unit such as a function or theory. A recursion group is a
strongly connected component of the item dependency graph: each member can
reach every other member through dependencies.

**Dynamic semantics**

r[compiler.work.item]
Each itemwise pass takes an item and lookup access to the items it depends on.

r[compiler.work.groups]
Recursion groups are computed from item dependencies and retained for passes
that need them.

r[compiler.work.instances]
Instance collection is a whole-program step that computes the required
instances and closures.

r[compiler.work.errors]
An item proceeds to lowering only when it and its dependencies have no errors.

r[compiler.work.order]
Observable output follows declaration order, including when lookup uses a
hash table.

r[compiler.correctness.simulation]
Each pass preserves the meaning of its input through a simulation relation
between input and output values, obligations and assumptions.

For `if d != 0 then n / d else 0`, preserving only the returned value is
insufficient: the division's definedness obligation is needed under the
branch condition. A transformation must preserve the relevant assumptions
as well as that obligation. An error in an unrelated item does not prevent
this item from being checked. Recursion groups and instance collection do
not require source declarations to be written in dependency order.

## Diagnostics and evidence

A diagnostic describes a problem independently of its rendering. Evidence
records how a particular check was established or attempted.

**Dynamic semantics**

r[compiler.diagnostic.data]
A diagnostic contains a code, a primary span, labelled spans, notes and
suggestions with their applicability.

r[compiler.diagnostic.rendering]
Text and structured output render the same diagnostic data.

r[compiler.diagnostic.error-node]
An error node carries evidence that its diagnostic was emitted.

r[compiler.evidence.data]
A check result records its method and the evidence produced by that method,
including a model, core, test seed and count, or Lean theorem when available.

r[compiler.evidence.dependencies]
The evidence for a result accounts for the evidence of the assumptions on
which it rests.

r[compiler.evidence.limits]
Solver limits, inconclusive results and caching follow Fren's checking rules;
a limit or an inconclusive result is not a proof.

For example, a tested hypothesis cannot turn a conclusion that rests on it
into a proved conclusion. A counterexample is checked against the active
hypotheses as well as the negated goal. A suggested edit has an applicability
level, allowing a client to distinguish a machine-applicable edit from one
that needs human judgment.

## Specifying the compiler

The detailed compiler chapters state laws about the actual implementation.
They do not define a second executable compiler in Fren.

**Proof obligations**

r[compiler.specification.laws]
A pass law is stated in Lean over the real code or in Fren over uninterpreted
functions bound to the real code by `impl`.

r[compiler.specification.testing]
Property tests exercise the real code with Plausible, including invalid and
partial inputs where applicable, and report how many inputs satisfy each
premise.

r[compiler.specification.proof]
Laws are proved in Lean where a proof is cheap; a pass expressed as a fold
uses the generic Lean fold theorem where it applies.

r[compiler.specification.primitives]
Independent small Fren contracts state primitive facts on which the laws rely.

r[compiler.specification.evidence]
The stated evidence distinguishes testing, proof and assumptions and does
not classify a Plausible test as a proof through `impl`.

A commuting-square test evaluates an expression before and after a pass and
compares the results. If both evaluations use an evaluator that implements
`a + b` as `a - b`, the results can agree while both are wrong. An independent
arithmetic fact such as `2 + 1 = 3` detects that particular mistake. The
contract below checks an independent increase property that also catches this
error. The evaluator must separately satisfy its primitive contract.
The contract does not bind or verify a production pass or evaluator.

**Proof obligations**

r[compiler.specification.addition] spec::compiler_overview::addition::increases
Adding one to an integer increases it.

```fren
pub mod spec
pub mod spec::compiler_overview

pub proc addition(x: Int) { expect increases: x + 1 > x }
```
