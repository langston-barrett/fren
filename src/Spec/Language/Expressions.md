# Expressions

A well-typed expression whose partial operations are within their domains
denotes a value in an interpretation of its declarations and an assignment
to its free locals. [Core typing](Types.md)
defines the shared `Ty`, `Symb`, `Ctx` and expression forms.
This chapter specifies how their meanings and source obligations compose.
The domain is Booleans, integers, payload-free nominal enums, locals, named
calls, unary and binary operators, lets, conditionals and constructor matches.

## Values, interpretation and mentioned names

r[expressions.value.denotation]
A well-typed expression of type τ, in a verified program and under values
of its context's types, whose partial operations are within their domains,
denotes a value of type τ. The [typing chapter](Types.md) states this as
type safety; it is open.

r[expressions.value.type] spec::expressions::{Value, value_type, value_valid?}
A value is a Boolean, an integer, or a nominal value that names an actual
constructor of its canonical enum owner; `value_type` gives its type.

```fren
pub mod spec
pub mod spec::expressions

use spec::surface::{BinaryOp, UnaryOp}
use spec::types::{ArmF, ExprF, ItemId, ItemKind, Snoc, Symb, Ty, entry}

pub enum Value { Boolean(Bool), Integer(Int), Nominal(ItemId, ItemId) }

pub fn value_type(value: Value): Ty := match value {
    Value::Boolean(_) => Ty::Boolean,
    Value::Integer(_) => Ty::Integer,
    Value::Nominal(owner, _) => Ty::Nominal(owner),
}

pub fn value_valid?(symb: Symb, value: Value) := match value {
    Value::Nominal(owner, item) => entry(symb, item) = Option::Some(ItemKind::Constructor(owner)),
    _ => true,
}
```

r[expressions.meaning.context]
An interpretation assigns meanings to canonical items. A local assignment
lists values by level, oldest first, in the exact typing context. Literals
denote the values they carry; a local denotes the value at its level; a
constructor denotes its nominal value. A named call substitutes its
positional arguments into its function body's parameter context, without
inheriting the caller's locals. A let interprets its value in the incoming
context and its body with that value appended as the newest level. An if denotes its selected
branch; a match denotes the body for its constructor, in the incoming context.

r[expressions.meaning.operators] spec::expressions::{unary_meaning?, integer_meaning?, boolean_meaning?, binary_meaning?}
Within their domains, arithmetic operators have their mathematical meanings.
Division and remainder are Euclidean: the remainder is nonnegative and
strictly less than the absolute divisor, and `n = (n div d) * d + n % d`.
Comparisons use integer order; Boolean operators use their truth tables;
equality compares values of one type, including canonical nominal identity.
Unary minus negates an integer and `not` complements a Boolean. `binary_meaning?` and
`unary_meaning?` state every operator's result; for `*`, `div` and `%` they
state the result's sort and the remainder's range, and the equations above
give the values.

```fren
pub fn unary_meaning?(op: UnaryOp, operand: Value, result: Value) := match op, operand {
    UnaryOp::Neg, Value::Integer(n) => result = Value::Integer(-n),
    UnaryOp::Not, Value::Boolean(b?) => result = Value::Boolean(not b?),
    _, _ => false,
}

pub fn integer_meaning?(op: BinaryOp, a: Int, b: Int, result: Value) := match op {
    BinaryOp::Add => result = Value::Integer(a + b),
    BinaryOp::Sub => result = Value::Integer(a - b),
    BinaryOp::Mul | BinaryOp::Div => result is Value::Integer(_),
    BinaryOp::Mod => match result {
        Value::Integer(r) => b = 0 or 0 <= r < b.abs,
        _ => false,
    },
    BinaryOp::Lt => result = Value::Boolean(a < b),
    BinaryOp::Le => result = Value::Boolean(a <= b),
    BinaryOp::Gt => result = Value::Boolean(a > b),
    BinaryOp::Ge => result = Value::Boolean(a >= b),
    BinaryOp::Eq => result = Value::Boolean(a = b),
    BinaryOp::Ne => result = Value::Boolean(a != b),
    _ => false,
}

pub fn boolean_meaning?(op: BinaryOp, p?, q?, result: Value) := match op {
    BinaryOp::And => result = Value::Boolean(p? and q?),
    BinaryOp::Or => result = Value::Boolean(p? or q?),
    BinaryOp::Iff | BinaryOp::Eq => result = Value::Boolean(p? iff q?),
    BinaryOp::Ne => result = Value::Boolean(not (p? iff q?)),
    _ => false,
}

pub fn binary_meaning?(op: BinaryOp, left: Value, right: Value, result: Value) :=
    match left, right {
        Value::Integer(a), Value::Integer(b) => integer_meaning?(op, a, b, result),
        Value::Boolean(p?), Value::Boolean(q?) => boolean_meaning?(op, p?, q?, result),
        Value::Nominal(_, _), Value::Nominal(_, _) => match op {
            BinaryOp::Eq => result = Value::Boolean(left = right),
            BinaryOp::Ne => result = Value::Boolean(left != right),
            _ => false,
        },
        _, _ => false,
    }
```

r[expressions.mentions.direct] spec::expressions::{arm_mentions?, direct_item?}
An occurrence directly mentions its constructor, callee or match-pattern
items. A local mentions its resolved context slot, rather than an item with
the same written spelling.

```fren
pub fn arm_mentions?<E>(arms: Snoc<ArmF<E>>, item: ItemId) := match arms {
    Snoc::Empty => false,
    Snoc::Extend(earlier, arm) => arm.constructor = item or arm_mentions?(earlier, item),
}

pub fn direct_item?<E>(form: ExprF<E>, item: ItemId) := match form {
    ExprF::Constructor(target) => item = target,
    ExprF::Call(target, _) => item = target,
    ExprF::Match(_, arms) => arm_mentions?(arms, item),
    _ => false,
}
```

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
This chapter assigns no value to an operation outside its domain. A source
obligation requires proof of the domain at the operation's written
occurrence.

r[expressions.domain.integer] spec::expressions::integer_domain?
Division and remainder require a nonzero divisor. Typing alone does not
establish this condition.

```fren
pub fn integer_domain?(op: BinaryOp, right: Int) :=
    not op in {BinaryOp::Div, BinaryOp::Mod} or right != 0
```

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
definitions in the [typing chapter](Types.md#examples).

On well-defined pure expressions an implementation may evaluate arguments
left to right and short-circuit Boolean operations. Verification-aware debug
execution checks applicable executable obligations and reports unresolved
predicates. Proved conditions may be erased for value evaluation; one
successful concrete execution does not prove a universally quantified goal.
Implementation correspondence and mathematical proof coverage are recorded
in the [development coverage document](../../../docs/fren2-specification-coverage.md).
