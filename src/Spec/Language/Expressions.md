# Expressions

An expression denotes a value in an interpretation of its declarations and
an assignment to its free locals. [Types and expression typing](Types.md)
defines the shared `Ty`, `Value`, `Symbols`, `Context` and expression forms.
This chapter specifies how their meanings and source obligations compose.
The domain is Booleans, integers, payload-free nominal enums, locals, named
calls, unary and binary operators, lets, conditionals and constructor matches.

## Values, interpretation and mentioned names

**Dynamic semantics**

r[expressions.value.type] spec::types::{value_type, value_valid?}
Every expression denotes a value of its type. A nominal value names an
actual constructor of its canonical enum owner.

r[expressions.meaning.context]
An interpretation assigns meanings to canonical items. A local assignment
lists values by level, oldest first, in the exact typing context. Literals
denote the values they carry; a local denotes the value at its level; a
constructor denotes its nominal value. A named call substitutes its
positional arguments into its function body's parameter context, without
inheriting the caller's locals. A let interprets its value in the incoming
context and its body with that value appended as the newest level. An if denotes its selected
branch; a match denotes the body for its constructor, in the incoming context.

r[expressions.meaning.operators] spec::types::{linear_meaning?, meaning_examples}
Within their domains, arithmetic operators have their mathematical meanings.
Division and remainder are Euclidean: the remainder is nonnegative and
strictly less than the absolute divisor, and `n = (n div d) * d + n mod d`.
Comparisons use integer order; Boolean operators use their truth tables;
equality compares values of one type, including canonical nominal identity.
Unary minus negates an integer and `not` complements a Boolean.

r[expressions.mentions.direct] spec::types::direct_item?
An occurrence directly mentions its constructor, callee or match-pattern
items. A local mentions its resolved context slot, rather than an item with
the same written spelling.

r[expressions.mentions.closure]
An expression's mentioned items are the union of its direct items and those
of every written child. Its free local slots are collected through every
child, removing the let's own level when leaving a let body; other levels
are unchanged. A let's value has no additional binder. Match patterns add none.
Names in an unselected branch or unused definition still count. This
structural closure uses the same children and binding depths as typing;
it is independent of a particular evaluation trace.

## Definedness and source verification

A domain condition states when a partial operation has its specified meaning.
Expressions outside that domain still denote a fixed value of their type;
that value is unspecified by the operation's equation. A source obligation
requires proof of the domain at the operation's written occurrence.

**Legality rules**

r[expressions.domain.integer] spec::types::integer_domain?
Division and remainder require a nonzero divisor. Typing alone does not
establish this condition.

r[expressions.domain.traversal]
Verification traverses every written expression. Ordinary unary and binary
operands, including both sides of `and` and `or`, retain their obligations
in the incoming context. Unused let values and uncalled named definitions
retain their obligations too. An interpreter's short-circuit trace cannot
decide which obligations exist.

r[expressions.domain.guards]
An if's condition is checked in the incoming context; its branches add the
condition and its negation respectively. A constructor match checks its
scrutinee in the incoming context and each arm under its constructor guard.
These explicit scopes determine conditional obligations. Thus the division
in `if d != 0 then n div d else 0` has hypothesis `d != 0`, whereas the
division in `false and (1 div 0 = 0)` retains its unconditional obligation.

r[expressions.domain.evidence]
An unknown result or resource limit is neither proof nor undefinedness.
No unproved goal can justify itself. A local hypothesis cannot become an
unconditional global fact. Verification of a domain and evaluation of a
value are distinct judgments.

The [OIR rules](../Compiler/Oir.md#static-traversal-guards-and-bindings)
retain lexical binders, substitutions, branch guards, owners and source
origins. Their assert/assume and subset interfaces describe scoped
verification information. The source grammar defined here contains no
assert/assume expressions or subset syntax; global assumption members are
specified by the check-request rules. No rule here settles dependency
semantics for unresolved mutually partial assumptions.

## Examples

With `Γ = ·, Boolean, Integer`, local 0 denotes the Boolean, and local 1 the
integer. In `let x := y + 1 in x + y`, with incoming context `·, y: Integer`,
the value uses level 0 for `y`; the body uses level 0 for `y` and level 1
for `x`. These are the same contexts required by `rule?`.

`Ty::Nominal(["M", "Light"])` and `Ty::Nominal(["M", "Signal"])` are
different types even if both enums declare `Red`. A comparison between
their constructors fails typing, before its truth or definedness is checked.
The checked derivations and arithmetic examples follow their shared
definitions in the [typing chapter](Types.md#worked-derivations).

On well-defined pure expressions an implementation may evaluate arguments
left to right and short-circuit Boolean operations. Verification-aware debug
execution checks applicable executable obligations and reports unresolved
predicates. Proved conditions may be erased for value evaluation; one
successful concrete execution does not prove a universally quantified goal.
Implementation correspondence and mathematical proof coverage are recorded
in the [development coverage document](../../../docs/fren2-specification-coverage.md).
