# Expressions

A well-typed expression whose partial operations are within their domains
denotes a value in an interpretation of its declarations and an assignment
to its free locals. [Core typing](Types.md)
defines the shared `Ty`, `Symb`, `Ctx` and expression forms.
This chapter specifies how their meanings compose and when a partial
operation is within its domain;
[Definedness and verification](PropertiesAndChecks.md) specifies the
obligations.
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

use spec::types::{
    Arm,
    ArmF,
    Ctx,
    ExprF,
    Form,
    ItemId,
    ItemKind,
    Row,
    Snoc,
    Symb,
    Ty,
    entry,
    four,
    length,
    lookup,
    one,
}

use spec::types::Snoc::{Empty, Extend}

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
    BinaryOp::Rem => match result {
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

## Evaluation

r[expressions.meaning.values] spec::expressions::{unary_value, integer_value, boolean_value, binary_value}
`unary_value` and `binary_value` compute an operator's result from its
operands' values. They give none for operands of the wrong sorts. They
give none for `*`, `div` and `%` either: the values of those three are
specified only by the relation `binary_meaning?`, which no function here
computes.

```fren
pub fn unary_value(op: UnaryOp, operand: Value): Option<Value> := match op, operand {
    UnaryOp::Neg, Value::Integer(n) => Some(Value::Integer(-n)),
    UnaryOp::Not, Value::Boolean(b?) => Some(Value::Boolean(not b?)),
    _, _ => None,
}

pub fn integer_value(op: BinaryOp, a: Int, b: Int): Option<Value> := match op {
    BinaryOp::Add => Some(Value::Integer(a + b)),
    BinaryOp::Sub => Some(Value::Integer(a - b)),
    BinaryOp::Lt => Some(Value::Boolean(a < b)),
    BinaryOp::Le => Some(Value::Boolean(a <= b)),
    BinaryOp::Gt => Some(Value::Boolean(a > b)),
    BinaryOp::Ge => Some(Value::Boolean(a >= b)),
    BinaryOp::Eq => Some(Value::Boolean(a = b)),
    BinaryOp::Ne => Some(Value::Boolean(a != b)),
    _ => None,
}

pub fn boolean_value(op: BinaryOp, p?, q?): Option<Value> := match op {
    BinaryOp::And => Some(Value::Boolean(p? and q?)),
    BinaryOp::Or => Some(Value::Boolean(p? or q?)),
    BinaryOp::Iff | BinaryOp::Eq => Some(Value::Boolean(p? iff q?)),
    BinaryOp::Ne => Some(Value::Boolean(not (p? iff q?))),
    _ => None,
}

pub fn binary_value(op: BinaryOp, left: Value, right: Value): Option<Value> := match left, right {
    Value::Integer(a), Value::Integer(b) => integer_value(op, a, b),
    Value::Boolean(p?), Value::Boolean(q?) => boolean_value(op, p?, q?),
    Value::Nominal(_, _), Value::Nominal(_, _) => match op {
        BinaryOp::Eq => Some(Value::Boolean(left = right)),
        BinaryOp::Ne => Some(Value::Boolean(left != right)),
        _ => None,
    },
    _, _ => None,
}
```

r[expressions.meaning.values-agree] spec::expressions::values_agree::{unary, binary}
A computed result is a result that the operator's meaning admits.

```fren
set_option fren.evidence "random" in
pub proc values_agree(unop: UnaryOp, op: BinaryOp, left: Value, right: Value, result: Value): (
    holds?,
) {
    ensure output: holds?
    ensure unary: when unary_value(unop, left) = Some(result), unary_meaning?(unop, left, result)
    ensure binary: when binary_value(op, left, right) = Some(result),
        binary_meaning?(op, left, right, result)
}
```

r[expressions.meaning.evaluation] spec::expressions::{value_at, arm_value, layer_value, initial, values, eval}
The *evaluator* computes the value of every row of a
[derivation table](Types.md#derivations) in one local assignment ρ.
`values` works row by row, oldest first, and reads each child's value from
the rows before it. A literal, a local and a constructor have the values
that [the interpretation](#r-expressions.meaning.context) gives them. An
operator row has the result of `unary_value` or `binary_value` at its
operands' values. A conditional has the value of the branch that its
condition selects, and a match the value of the arm for its scrutinee's
constructor. A let row is evaluated in two steps: its value v in ρ, then
its body in the assignment that keeps the levels of the let's own context
and appends v. `eval(t, r, ρ)` is the value of row r.

A row has no value when a child that it needs has none, when a local is
not in ρ, when an operator has no result, or when it is a call. So a
row that depends on a product, a quotient or a remainder has none. The
evaluator is strict where verification is: an operator needs both
operands' values, and a let needs its value's, whether or not the result
depends on them. A conditional needs only the selected branch, and a match
only the selected arm. The evaluator covers the call-free Core; evaluating
a call needs the callee's body, and is not yet specified.

```fren
pub fn value_at(prior: Snoc<Option<Value>>, pos: Int): Option<Value> := match lookup(prior, pos) {
    Some(value) => value,
    None => None,
}

pub fn arm_value(prior: Snoc<Option<Value>>, arms: Snoc<Arm>, constructor: ItemId): Option<Value> :=
    match arms {
        Empty => None,
        Extend(earlier, arm) =>
            if arm.constructor = constructor then value_at(prior, arm.body)
            else arm_value(prior, earlier, constructor),
    }

pub fn layer_value(prior: Snoc<Option<Value>>, env: Snoc<Value>, row: Row): Option<Value> :=
    match row.form {
        ExprF::BooleanLiteral(value?) => Some(Value::Boolean(value?)),
        ExprF::IntegerLiteral(value) => Some(Value::Integer(value)),
        ExprF::Local(level) => lookup(env, level),
        ExprF::Constructor(item) => match row.ty {
            Ty::Nominal(owner) => Some(Value::Nominal(owner, item)),
            _ => None,
        },
        ExprF::Unary(op, operand) => match value_at(prior, operand) {
            Some(value) => unary_value(op, value),
            None => None,
        },
        ExprF::Binary(op, left, right) => match value_at(prior, left), value_at(prior, right) {
            Some(l), Some(r) => binary_value(op, l, r),
            _, _ => None,
        },
        ExprF::If(condition, yes, no) => match value_at(prior, condition) {
            Some(Value::Boolean(holds?)) =>
                if holds? then value_at(prior, yes) else value_at(prior, no),
            _ => None,
        },
        ExprF::Match(scrutinee, arms) => match value_at(prior, scrutinee) {
            Some(Value::Nominal(_, constructor)) => arm_value(prior, arms, constructor),
            _ => None,
        },
        _ => None,
    }

pub fn initial<T>(xs: Snoc<T>, count: Int): Snoc<T> := match xs {
    Empty => Empty,
    Extend(earlier, _) => if length(earlier) < count then xs else initial(earlier, count),
}

pub fn values(rows: Snoc<Row>, env: Snoc<Value>): Snoc<Option<Value>> := match rows {
    Empty => Empty,
    Extend(earlier, row) => Extend(
        values(earlier, env),
        match row.form {
            ExprF::Let(_, value, body) => match value_at(values(earlier, env), value) {
                Some(bound) => value_at(
                    values(earlier, Extend(initial(env, length(row.ctx)), bound)),
                    body
                ),
                None => None,
            },
            _ => layer_value(values(earlier, env), env, row),
        }
    ),
}

pub fn eval(rows: Snoc<Row>, pos: Int, env: Snoc<Value>): Option<Value> :=
    value_at(values(rows, env), pos)
```

r[expressions.examples.evaluation] spec::expressions::{typed, LET_ROWS, evaluation_examples::{bound, unbound, uncomputed}}
`let d := 2 in 10 - d` has this table; row 4 is the let.

| Row | Layer | Context |
| --- | --- | --- |
| 0 | `2` | `·` |
| 1 | `10` | `·, Int` |
| 2 | `#0` | `·, Int` |
| 3 | `row 1 - row 2` | `·, Int` |
| 4 | `let d := row 0 in row 3` | `·` |

In the empty assignment the let has the value 8. Its body's row 3 has
none there, since the local is not in the assignment. A quotient has no
computed value, even of 10 and 2.

```fren
pub fn typed(form: Form, ctx: Ctx, ty: Ty): Row := Row { form, ctx, ty }

pub const LET_ROWS: Snoc<Row> := Extend(
    four(
        typed(ExprF::IntegerLiteral(2), Empty, Ty::Integer),
        typed(ExprF::IntegerLiteral(10), one(Ty::Integer), Ty::Integer),
        typed(ExprF::Local(0), one(Ty::Integer), Ty::Integer),
        typed(
            ExprF::Binary(BinaryOp::Sub, 1, 2),
            one(Ty::Integer),
            Ty::Integer
        )
    ),
    typed(ExprF::Let(None, 0, 3), Empty, Ty::Integer)
)

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc evaluation_examples(): (holds?) {
    ensure output: holds?
    ensure bound: eval(LET_ROWS, 4, Empty) = Some(Value::Integer(8))
    ensure unbound: eval(LET_ROWS, 3, Empty) = None
    ensure uncomputed: binary_value(BinaryOp::Div, Value::Integer(10), Value::Integer(2)) = None
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

## Operator domains

A domain condition states when a partial operation has its specified meaning.
This chapter assigns no value to an operation outside its domain.

r[expressions.domain.integer] spec::expressions::integer_domain?
Division and remainder require a nonzero divisor. Typing alone does not
establish this condition.

```fren
pub fn integer_domain?(op: BinaryOp, right: Int) :=
    not op in {BinaryOp::Div, BinaryOp::Rem} or right != 0
```

[Definedness and verification](PropertiesAndChecks.md) defines the obligation
that each written occurrence of a partial operation gives rise to, the
hypotheses that conditionals, matches and lets supply, and what a solver's
answer establishes.

The [OIR chapter](../Compiler/Oir.md#static-traversal-guards-and-bindings)
relates the compiler's conditions to those obligations.

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
