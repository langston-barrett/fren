# Desugaring

Desugaring maps the typed module to the desugared typed module. Its source
domain is the [Language core](../Language/Types.md): Bool, Int, payload-free
nominal enums, nonrecursive named functions, checks, literals, names,
parentheses, operators, calls, if, let and constructor matches. In this
domain the only surface form is the written parenthesis, so the pass removes
parentheses and changes nothing else.

## The pass

The input is the [THIR module](Thir.md#the-typed-module), the output of the
separated type checker: one module of items, each function and check member
carrying a typed expression. The output is the same module shape over
desugared THIR expressions. Both use the shared expression representation
described in the [HIR chapter](Hir.md), in which a local is its index, an
item is its canonical identity, and each node carries an origin and, from
THIR onward, a type. The desugared THIR phase has no parenthesis node.

**Proof obligations**

r[desugaring.pass.input]
The pass reads the THIR module and nothing else. It does not read source
text, the syntax tree or the resolver's tables, and it runs no parser,
resolver or type checker. It is total: every THIR module has a desugared
module, and the pass reports no error of its own. Its result depends only on
its argument.

r[desugaring.pass.parens]
A parenthesised expression desugars to the desugaring of its body. The result
therefore carries the origin and type of the desugared body, not of the
written body: `((x))` desugars to what `x` desugars to, with `x`'s origin, and
the origins and types of both parentheses are removed. Every other node is
rebuilt with the same origin, the same type and its desugared children in the
same order. Literal values, local indices, constructor and callee identities,
operators, let binders and the constructor pattern of each match arm are
unchanged. These two clauses determine the pass: each expression has exactly
one result that satisfies them. The output phase admits no parenthesis node,
so none remains at any depth.

r[desugaring.pass.module]
The module keeps its identity. Items are desugared one for one in declaration
order, and each item's output depends on that item alone. An enum is
unchanged. A function keeps its identity, origin, parameters and result
type; a check keeps its identity, origin, parameters and its members in
order, each with its kind, label and origin. No item, member, operand or
unused definition is deleted. Each item keeps its origin table whole,
including the entries of removed parentheses, so an origin that survives
denotes the same source position before and after.

The chapter wrapper states these rules as relations that do not mention the
production pass. `Erases` relates a THIR expression to a desugared one by the
two clauses of `desugaring.pass.parens`, one case for each node form.
`ErasesMember`, `ErasesItem` and `ErasesModule` state every clause of
`desugaring.pass.module`: the module's identity, the item count and order,
that an item keeps its kind, an enum whole, a function's and a check's
identity, origin, parameters and result type, the member count and order,
each member's kind, label and origin, and the origin table. The wrapper
proves, for every input, that the production pass's output is related to its
input (`desugar_sound`, `item_sound`, `module_sound`) and that anything
related to an input is the production pass's output (`desugar_unique`,
`item_unique`, `module_unique`). It also proves that no output node is a
parenthesis (`output_has_no_paren`) and the nested case above. Two parts of
the rules are not theorems. In `desugaring.pass.input`, totality and
dependence on the argument alone hold because the pass is a total Lean
function of the module; that it runs no other pass and reads no other
representation is checked by the `layering` test over its imports. That no
operand or unused definition is deleted follows from the relations, which
keep every child and every item, but is not stated as a theorem of its own.

Property tests over generated well-typed modules, with parentheses added at
every depth, check the pass against oracles of their own over a bounded
sample. The output's printed form is the input's with only its parentheses
removed. Typing the parenthesis-free erasure of the input gives the output,
so desugaring commutes with typing. Added parentheses do not change the
output's bodies. The node count falls by one for each parenthesis, and
scoping is unchanged. Only the tests cover the last four; no theorem states
that desugaring preserves typing, scoping or evaluation.

Parentheses are concrete syntax. The [Language](../Language/Types.md)
states its typing and evaluation rules over the Core, which has no
parenthesis form, so a parenthesised expression has the type, value and
definedness of its body. Removing parentheses therefore preserves each of
these, and removes no division or remainder site, branch or member.

A later form of surface sugar must be defined by its Language semantics. Its
desugaring must relate the complete input and output, preserve typing in the
exact contexts, and establish value and obligation correspondence. A table
expansion must retain table kind and disjointness obligations when translated
to a match. The rules above give no correspondence for such a form.

## The walking program

[MIR construction](Mir.md) and the passes after it do not yet consume the
desugared module. They take the walking program, `FrenWalking.Program`: a
resolved input, the legacy checker's typed result, and evidence that the
checker with both walking validators accepted that input. This section states
that boundary and the source obligations MIR construction reads from it. The
walking program is not an output of the desugaring pass.

`Produces r q` is the graph of the admission entry point `fromResolved`;
`Rejects r d` states its rejected resolved input and static failure.

**Proof obligations**

r[desugaring.walking.input]
A walking program must carry actual producer evidence. A caller-supplied typed
value, occurrence table or validation Boolean does not establish admission.
For resolved input `r`, a successful result with typed data `t` exists exactly
when the legacy type checker produces `t` and both the coverage and the
non-recursion validator accept it. This is `admission_domain` in the chapter
wrapper.

r[desugaring.walking.boundary]
`fromResolved r = .ok q` holds exactly when `q.input = r` and
`checkWalking r = .ok q.typed`. Its error result is exactly `Rejects r d`,
with the same failure payload. Type errors, coverage errors and recursive-call
errors remain distinct. `fromSource` first parses and resolves; it maps a
parse error to the typing diagnostic with detail `expected ` followed by the
parser's expected text and the same span, maps a resolver diagnostic to a
typing failure unchanged, then uses `fromResolved`. No rejected input becomes
a walking program. `source_projection` proves equality of its typed/error
projection with `checkWalkingSource`. The grammar excludes ensure, where,
unless, unnamed match parameters, lambda matches and tables; this relation
supplies no rule admitting any of them.

`Guard` records an if condition and polarity, or a match scrutinee and written
constructor pattern, together with the context in which that subject is read.
The pattern's target comes from the retained resolved input. A guard is a
scoped hypothesis, not evidence that the condition holds or is defined.
`ScopedChild` and `ScopedAt` define the structural traversal of source
obligations. Their context projection is the shared
[THIR](Thir.md#shared-judgments-and-pass-interface) `ChildContext` and
`AtContext`; `scoped_child_context` and `scoped_at_context` prove this
direction.

r[desugaring.walking.static]
A walking program retains actual type-production, coverage and non-recursion
validation evidence (`output_static`). Every written child participates in
obligation traversal. Ordinary Boolean operands add no guard. An unused let
definition uses the incoming context; only its body extends that context. An
if condition and match scrutinee use the incoming guards; each branch or arm
adds only its explicit guard. Existing guards keep their original lexical
contexts across later binders. All named definitions and check members remain
roots.

r[desugaring.contract.obligations]
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

These definitions are compiled in the [chapter wrapper](Desugaring.lean) over
production types, without an alternative executable compiler.

## Example

This program has no parentheses, so the desugaring pass rebuilds each body
unchanged, origins included. Had the first arm been written `(base) + 30`,
its desugaring would be the same addition with the same operand origins. In
the walking program,
`bounded` is an assumption in `waits` and `at_most` is its expectation. Both
match arms are written bodies, independently of which arm a particular
execution selects.

```fren
pub mod desugar_example

pub enum Light { Red, Green }

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => base + 30,
    Light::Green => base,
}

expect waits(l: Light, base: Int) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}

#fren_check
```

For a partial expression, `if d != 0 then 1 div d else 0` has a division site
under the positive condition guard. `false and (1 div 0 = 0)` has an unguarded
division site, as does the value in `let x := 1 div 0 in 3`. The walking
program has all three sites even if a particular execution returns a value,
and removing the parentheses of the second leaves its site in place. These
cases separate interpretation from obligations.

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
