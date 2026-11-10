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
function whose only argument is the THIR module and whose result is the
desugared module. That it reads nothing else follows from that type: a pure
function has no other input. That it runs no other pass is checked by the
`layering` test, which fails if the parser, the resolver, the type checker or
any other pass is reachable from the pass's imports. The test checks no more
than that: the shared module library the pass imports also defines the syntax
tree's and the legacy checker's tables, which the pass can name but is never
given. That no
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
definedness of its body. This is the argument for why removing parentheses
should preserve each of these and remove no division or remainder site,
branch or member. It is an argument, not a proven result. The wrapper proves
none of these preservations. The tests above check typing and scoping over a
bounded sample, and nothing yet checks value or definedness.

A later form of surface sugar must be defined by its Language semantics. Its
desugaring must relate the complete input and output, preserve typing in the
exact contexts, and establish value and obligation correspondence. A table
expansion must retain table kind and disjointness obligations when translated
to a match. The rules above give no correspondence for such a form.

## Example

The first arm's left operand is written in parentheses. Desugaring gives the
addition whose left operand is the local `base`, with the origin and type of
that inner occurrence; the parenthesis node, its origin and its type are
gone, and the origin table still holds the entry of the parenthesis. Every
other node of both items is rebuilt unchanged, origins included.

```fren
pub mod desugar_example

pub enum Light { Red, Green }

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => (base) + 30,
    Light::Green => base,
}

expect waits(l: Light, base: Int) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}

#fren_check
```

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
