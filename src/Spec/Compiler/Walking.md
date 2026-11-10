# The walking program

[MIR construction](Mir.md) and the passes after it do not yet read the
[desugared module](Desugaring.md). They take the walking program: a resolved
input, the legacy checker's typed result for that input, and evidence that the
legacy checker with both walking validators accepted it. This chapter states
that boundary and the source obligations MIR construction reads from it.

The walking program is not an output of the desugaring pass, and nothing in
this chapter depends on that pass. The chapter is temporary. When the later
passes read the desugared module it is deleted, as the
[removal plan](../../../docs/fren2-walking-removal.md) describes.

## Admission

Admission takes a resolved input and gives a walking program or a static
failure. The chapter wrapper names the two outcomes: `Produces r q` says that
admitting the resolved input `r` gives the program `q`, and `Rejects r d` says
that the legacy checker with its validators fails on `r` with the failure `d`.

**Proof obligations**

r[walking.program.input]
A walking program must carry actual producer evidence. A caller-supplied typed
value, occurrence table or validation Boolean does not establish admission.
For resolved input `r`, a successful result with typed data `t` exists exactly
when the legacy type checker produces `t` and both the coverage and the
non-recursion validator accept it. This is `admission_domain` in the chapter
wrapper.

r[walking.program.boundary]
Admitting a resolved input gives the program `q` exactly when `q` retains
that input and the typed result of `q` is the one the legacy checker with both
validators gives for it. Admission fails exactly when that checker fails, and
with the same failure. Each resolved input therefore has one outcome, a
program or a failure and never both. Type errors, coverage errors and
recursive-call errors remain distinct failures. Admitting source text parses
and resolves it first. A parse error becomes a typing diagnostic at the
parser's span whose detail is the word `expected` followed by what the parser
expected. A resolver diagnostic becomes a typing failure unchanged. Otherwise
the outcome is that of the resolved input, so no rejected input becomes a
walking program, and the typed result or failure of source admission is that
of the legacy source checker. The grammar excludes ensure, where, unless,
unnamed match parameters, lambda matches and tables; this relation supplies no
rule admitting any of them. The wrapper proves these as `resolved_success`,
`resolved_failure`, `produced_unique`, `failure_excludes_success` and
`source_projection`.

## Scoped obligations

`Guard` records an if condition and polarity, or a match scrutinee and written
constructor pattern, together with the context in which that subject is read.
The pattern's target comes from the retained resolved input. A guard is a
scoped hypothesis, not evidence that the condition holds or is defined.
`ScopedChild` and `ScopedAt` define the structural traversal of source
obligations. Their context projection is the shared
[THIR](Thir.md#shared-judgments-and-pass-interface) `ChildContext` and
`AtContext`; `scoped_child_context` and `scoped_at_context` prove this
direction.

**Proof obligations**

r[walking.program.static]
A walking program retains actual type-production, coverage and non-recursion
validation evidence (`output_static`). Every written child participates in
obligation traversal, a parenthesised body included. Ordinary Boolean
operands add no guard. An unused let definition uses the incoming context;
only its body extends that context. An if condition and match scrutinee use
the incoming guards; each branch or arm adds only its explicit guard.
Existing guards keep their original lexical contexts across later binders.
All named definitions and check members remain roots.

r[walking.program.obligations]
`DomainSite` identifies each written division/remainder obligation by its full
body, lexical context, ordered guard path, operands, operator token and kind.
The required integer domain is nonzero divisor, as defined by
[expression domains](../Language/Expressions.md#operator-domains).
`Members` gives the ordered assumption and expectation arrays for each
canonical owner, including full member data. All of a block's assumptions
remain available to its expectations, regardless of written position; no
assumption becomes a goal or a global unconditional fact. Recording an
obligation does not prove its domain or its hypotheses. These definitions do
not settle dependencies among mutually partial assumptions or assign solver
verdicts. An interpreter may skip an ordinary Boolean operand or ignore an
unused let's failure; its demand trace does not remove the site's static
obligation.

These definitions are compiled in the [chapter wrapper](Walking.lean) over
production types, without an alternative executable compiler.

## Examples

In a block that states `expect goal: f(d) = 0` and then
`assume later: d = 0`, `later` is an assumption of the block and `goal` is its
expectation, although the assumption is written second.

For a partial expression, `if d != 0 then 1 div d else 0` has a division site
under the positive condition guard. `false and (1 div 0 = 0)` has an unguarded
division site, as does the value in `let x := 1 div 0 in 3`. The walking
program has all three sites even if a particular execution returns a value.
These cases separate interpretation from obligations.

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
