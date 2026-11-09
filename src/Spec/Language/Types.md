# Types and expression typing

A type describes which values an expression can produce. This chapter defines
Booleans, mathematical integers and nominal payload-free enumeration types.
Named functions have ordered parameter types and a result type; they are not
first-class values. The [source grammar](../Compiler/AstAndParsing.md#source-forms)
and [name resolution](NamesAndScope.md) determine the expressions to which
these rules apply. Typing does not prove a check true or an operation defined.

## Shared semantic definitions

An `ItemId` is the canonical sequence of enclosing module and item names,
including the enumeration name for a constructor. It is obtained by resolution,
not by splitting a display string. Identity uses the entire sequence. Local
indices instead refer to the exact nearest-first context at an occurrence,
as specified by [binding](../Compiler/Bindings.md#contexts-and-scope).

**Legality rules**

r[types.walking.identity] spec::types::type_identity
Value types have disjoint Boolean, integer and nominal constructors.

r[types.walking.compatibility] spec::types::type_identity
Compatibility is equality of these types, including the complete nominal identity.

```fren
pub mod spec
pub mod spec::types

pub type ItemId := Seq<String>
pub enum Ty { Boolean, Integer, Nominal(ItemId) }
pub type Context := Seq<Ty>
pub struct Signature { item: ItemId, parameters: Seq<Ty>, result: Ty }
pub struct Constructor { item: ItemId, owner: ItemId }
pub struct Symbols { functions: Seq<Signature>, constructors: Seq<Constructor> }

pub fn compatible_type?(left: Ty, right: Ty) := left = right

pub proc type_identity(a: ItemId, b: ItemId) {
    expect disjoint: Ty::Boolean != Ty::Integer and not Ty::Nominal(a) is Ty::Boolean | Ty::Integer
    expect nominal: compatible_type?(Ty::Nominal(a), Ty::Nominal(b)) iff a = b
    expect reflexive: compatible_type?(Ty::Nominal(a), Ty::Nominal(a))
}
```

`Symbols` contains resolved function signatures and constructor ownership.
Its entries come from the collected declarations before bodies are checked.
The same canonical item has only one signature or constructor entry, and an
item cannot have both kinds. These are finite, decidable table conditions.
An enumeration declaration, module, expectation or bare function is not a
value. Equal variant spellings in different enumerations do not identify them.

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.lint.collapsible_when "allow" in
pub fn symbols_valid?(s: Symbols) :=
    (forall (i: Int), when 0 <= i < s.functions.len,
        forall (j: Int), when 0 <= j < s.functions.len, when i < j, s.functions[i].item != s.functions[j].item)
    and (forall (i: Int), when 0 <= i < s.constructors.len,
        forall (j: Int), when 0 <= j < s.constructors.len, when i < j, s.constructors[i].item != s.constructors[j].item)
    and (forall (i: Int), when 0 <= i < s.functions.len,
        forall (j: Int), when 0 <= j < s.constructors.len, s.functions[i].item != s.constructors[j].item)
```

r[types.walking.annotations] spec::types::annotation_type?
Every parameter and function result annotation denotes its resolved value
type; an omitted parameter annotation supplies `Bool` only for a `?` name.

r[types.walking.suffix] spec::types::binder?
A parameter or let binder whose name ends in `?` has type `Bool`, including
when a parameter has an explicit annotation.

```fren
pub enum Annotation { Boolean, Integer, Nominal(ItemId), Omitted }

pub fn annotation_type?(annotation: Annotation, question?, ty: Ty) := match annotation {
    Annotation::Boolean => ty = Ty::Boolean,
    Annotation::Integer => ty = Ty::Integer,
    Annotation::Nominal(item) => ty = Ty::Nominal(item),
    Annotation::Omitted => question? and ty = Ty::Boolean,
}

pub fn binder?(question?, ty: Ty) := not question? or ty = Ty::Boolean
```

There are no coercions or integer subtypes in this domain. A written
`b?: Int` resolves but fails typing; the suffix does not overwrite an
annotation. Parameter contexts reverse written parameter order, so the last
parameter is at index zero. Every parameter must satisfy `binder?`.

r[types.context.parameters] spec::types::parameter_context?
Parameter types occupy the body context in reverse written order, with every
question-suffixed parameter checked against Boolean.

```fren
pub struct Parameter { ty: Ty, question? }

set_option fren.lint.undecidable "allow" in
pub fn parameter_context?(parameters: Seq<Parameter>, context: Context) :=
    parameters.len = context.len
    and (forall (i: Int), when 0 <= i < parameters.len,
        context[parameters.len - 1 - i] = parameters[i].ty
        and binder?(parameters[i].question?, parameters[i].ty))
```

## Operators

The following contracts retain the actual-code bindings for compatibility
and operator decisions. `ValueKind` is an adapter classification, not a second
language type representation: the nominal identity is carried by `Ty` above.
The integer identity atoms in these bindings instantiate the production
primitive's generic identity parameter; they are never hashes or rendered names.

r[types.primitive.compatibility] spec::types::compatible::{meaning, builtin, nominal, distinct, disjoint}
Compatibility compares tags and, only for nominal types, identity atoms.

```fren
pub enum ValueKind { Boolean, Integer, Nominal }
pub enum Unary { Negate, Not }
pub enum Binary { Add, Sub, Mul, Div, Mod, Lt, Le, Gt, Ge, And, Or, Iff, Eq, Ne }

pub proc compatible(left: ValueKind, right: ValueKind, left_id: Int, right_id: Int): (same?) {
    ensure meaning: same? iff left = right and (left != ValueKind::Nominal or left_id = right_id)

    expect builtin: when left = right and left != ValueKind::Nominal, same?
    expect nominal: when left = ValueKind::Nominal and right = left and left_id = right_id, same?
    expect distinct: when left = ValueKind::Nominal and right = left and left_id != right_id, not same?
    expect disjoint: when left != right, not same?
}
```

r[types.primitive.unary] spec::types::unary::{meaning, result_type, negate_bool, not_int}
A unary operator accepts exactly its table operand and preserves its tag.

```fren
pub proc unary(op: Unary, operand: ValueKind): (accepted?, result: ValueKind) {
    ensure meaning: accepted? iff (op = Unary::Negate and operand = ValueKind::Integer) or (op = Unary::Not and operand = ValueKind::Boolean)
    ensure result_type: when accepted?, result = operand

    expect negate_bool: when op = Unary::Negate and operand = ValueKind::Boolean, not accepted?
    expect not_int: when op = Unary::Not and operand = ValueKind::Integer, not accepted?
}
```

r[types.primitive.binary] spec::types::binary::{meaning, result_type, enum_add, mixed_equality, distinct_enums, same_enum}
A binary operator accepts exactly its table operands and returns its table
tag, including nominal identity comparison for equality.

```fren
pub proc binary(op: Binary, left: ValueKind, right: ValueKind, left_id: Int, right_id: Int): (
    accepted?,
    result: ValueKind,
) {
    ensure meaning: accepted? iff match op {
        Binary::Add => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Sub => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Mul => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Div => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Mod => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Lt => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Le => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Gt => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Ge => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::And => left = ValueKind::Boolean and right = ValueKind::Boolean,
        Binary::Or => left = ValueKind::Boolean and right = ValueKind::Boolean,
        Binary::Iff => left = ValueKind::Boolean and right = ValueKind::Boolean,
        Binary::Eq => left = right and (left != ValueKind::Nominal or left_id = right_id),
        Binary::Ne => left = right and (left != ValueKind::Nominal or left_id = right_id),
    }
    ensure result_type: when accepted?, result = match op {
        Binary::Add => ValueKind::Integer,
        Binary::Sub => ValueKind::Integer,
        Binary::Mul => ValueKind::Integer,
        Binary::Div => ValueKind::Integer,
        Binary::Mod => ValueKind::Integer,
        Binary::Lt => ValueKind::Boolean,
        Binary::Le => ValueKind::Boolean,
        Binary::Gt => ValueKind::Boolean,
        Binary::Ge => ValueKind::Boolean,
        Binary::And => ValueKind::Boolean,
        Binary::Or => ValueKind::Boolean,
        Binary::Iff => ValueKind::Boolean,
        Binary::Eq => ValueKind::Boolean,
        Binary::Ne => ValueKind::Boolean,
    }

    expect enum_add: when op = Binary::Add and left = ValueKind::Nominal, not accepted?
    expect mixed_equality: when op = Binary::Eq and left != right, not accepted?
    expect distinct_enums: when op = Binary::Ne and left = ValueKind::Nominal and right = left and left_id != right_id, not accepted?
    expect same_enum: when op = Binary::Eq and left = ValueKind::Nominal and right = left and left_id = right_id, accepted? and result = ValueKind::Boolean
}
```


## Shared values and operator meaning

A nominal value records its enum owner and constructor identity. `value_type`
computes its type; `value_valid?` additionally checks actual constructor
ownership in the resolved symbols. Static typing and value validity remain
separate from an integer operation's domain.

```fren
pub enum Value { Boolean(Bool), Integer(Int), Nominal(ItemId, ItemId) }

pub fn value_type(value: Value): Ty := match value {
    Value::Boolean(_) => Ty::Boolean,
    Value::Integer(_) => Ty::Integer,
    Value::Nominal(owner, _) => Ty::Nominal(owner),
}

set_option fren.lint.undecidable "allow" in
pub fn value_valid?(s: Symbols, value: Value) := match value {
    Value::Nominal(owner, item) => (exists (k: Int), 0 <= k < s.constructors.len
        and s.constructors[k].item = item and s.constructors[k].owner = owner),
    _ => true,
}

pub fn integer_domain?(op: Binary, right: Int) := not op in {Binary::Div, Binary::Mod} or right != 0

pub fn linear_meaning?(op: Binary, left: Int, right: Int, result: Int) :=
    integer_domain?(op, right) and match op {
        Binary::Add => result = left + right,
        Binary::Sub => result = left - right,
        _ => false,
    }

set_option fren.lint.assertions_on_constants "allow" in
pub proc meaning_examples(n: Int) {
    expect addition: linear_meaning?(Binary::Add, n, 1, n + 1)
    expect order: not linear_meaning?(Binary::Sub, 7, 2, -5)
    expect quotient: -9 div (-2) = 5
    expect remainder: -9 mod (-2) = 1
    expect zero_domain: not integer_domain?(Binary::Div, 0) and not integer_domain?(Binary::Mod, 0)
}
```

`linear_meaning?` defines addition and subtraction; it rejects other operators.
The examples additionally check signed division and remainder with a fixed
nonzero divisor. The general multiplication and Euclidean equations are
mathematical rules in the expression chapter, not claims that the current
linear-arithmetic solver decides them for variable operands.
An arithmetic equation constrains a result only within its operation's
domain. Outside it, the expression still denotes a value of its type, fixed
by the interpretation, but no arithmetic equation here constrains that value.
Successful proof establishes the domain; a timeout establishes neither its
truth nor its negation. Operational failure reports are specified separately
by the [evaluator](../Compiler/Evaluator.md).

## Finite expression derivations

Write `Σ; Γ ⊢ e : T` when `e` has type `T` in symbols `Σ` and local context
`Γ`. A finite expression is represented by its written occurrences in
postorder: each child index is strictly smaller than its parent's. A row
contains the occurrence and a *candidate* context and type. These candidates
are a derivation witness, not trusted typing facts: `derivation?` checks the
local rule at **every** row, using the child's actual row and requiring its
exact context and type. The final row is the root. All written children,
including unused let values and unreachable branches, must appear.
This representation describes a judgment, not a production compiler IR.

```fren
pub struct Arm { constructor: ItemId, body: Int }

pub enum Form {
    BooleanLiteral,
    IntegerLiteral,
    Local(Int),
    ConstructorValue(ItemId),
    UnaryExpression(Unary, Int),
    BinaryExpression(Binary, Int, Int),
    Call(ItemId, Seq<Int>),
    Let(Bool, Int, Int),
    Conditional(Int, Int, Int),
    Match(Int, Seq<Arm>),
    Parenthesized(Int),
}

pub struct Row { form: Form, context: Context, ty: Ty }

set_option fren.lint.undecidable "allow" in
pub fn direct_item?(form: Form, item: ItemId) := match form {
    Form::ConstructorValue(target) => item = target,
    Form::Call(target, _) => item = target,
    Form::Match(_, arms) => (exists (j: Int), 0 <= j < arms.len and item = arms[j].constructor),
    _ => false,
}

pub fn edge?(rows: Seq<Row>, parent: Int, child: Int, context: Context, ty: Ty) :=
    0 <= child < parent < rows.len and rows[child].context = context and compatible_type?(rows[child].ty, ty)

pub fn integer_binary?(op: Binary) :=
    op in {
        Binary::Add,
        Binary::Sub,
        Binary::Mul,
        Binary::Div,
        Binary::Mod,
    }

pub fn comparison?(op: Binary) := op in {Binary::Lt, Binary::Le, Binary::Gt, Binary::Ge}
pub fn boolean_binary?(op: Binary) := op in {Binary::And, Binary::Or, Binary::Iff}
```

r[types.operator.unary] spec::types::unary_type?
Unary minus takes and returns `Int`; `not` takes and returns `Bool`.

r[types.operator.binary] spec::types::binary_type?
Arithmetic takes integers and returns an integer; integer comparisons return
a Boolean. Boolean operators take and return Booleans. Equality and
inequality take two values of one type and return a Boolean.

```fren
pub fn unary_type?(op: Unary, operand: Ty, result: Ty) := match op {
    Unary::Negate => operand = Ty::Integer and result = Ty::Integer,
    Unary::Not => operand = Ty::Boolean and result = Ty::Boolean,
}

pub fn binary_type?(op: Binary, left: Ty, right: Ty, result: Ty) :=
    if integer_binary?(op) then left = Ty::Integer and right = Ty::Integer and result = Ty::Integer
    else if comparison?(op) then left = Ty::Integer and right = Ty::Integer and result = Ty::Boolean
    else if boolean_binary?(op) then left = Ty::Boolean and right = Ty::Boolean and result = Ty::Boolean
    else compatible_type?(left, right) and result = Ty::Boolean
```

The literal forms retain their type-relevant shape only; their Boolean or
integer value is irrelevant to typing. `Let` records whether its binder has
the `?` suffix. A match pattern has a resolved constructor identity and no
binder. Parentheses preserve type. The relation below has no permissive
fallback for non-value items or non-function callees.

**Legality rules**

r[types.expression.local] spec::types::local_rule?
A local has the exact context entry at its resolved index; missing lookup fails.

r[types.expression.values] spec::types::local_rule?
Literals have their built-in type; constructors have their canonical owner's type.

r[types.expression.items] spec::types::local_rule?
Only constructor items are values; only function items are callable.

r[types.expression.call] spec::types::local_rule?
A call checks the exact arity and every positional argument against its signature.

r[types.expression.let] spec::types::local_rule?
The value uses the incoming context, and only the body receives its type as a new slot.

r[types.expression.if] spec::types::local_rule?
The condition is Boolean and both branches have the result type.

r[types.expression.match] spec::types::local_rule?
The scrutinee is nominal; every pattern has that owner and every body has the result type.

r[types.expression.parentheses] spec::types::local_rule?
Parentheses preserve context and type.

```fren
set_option fren.lint.undecidable "allow" in
pub fn local_rule?(s: Symbols, rows: Seq<Row>, i: Int) := 0 <= i < rows.len and
    (let r := rows[i] in match r.form {
        Form::BooleanLiteral => r.ty = Ty::Boolean,
        Form::IntegerLiteral => r.ty = Ty::Integer,
        Form::Local(slot) => 0 <= slot < r.context.len and r.ty = r.context[slot],
        Form::ConstructorValue(item) => (exists (k: Int), 0 <= k < s.constructors.len
            and s.constructors[k].item = item and r.ty = Ty::Nominal(s.constructors[k].owner)),
        Form::UnaryExpression(op, child) => 0 <= child < i
            and edge?(rows, i, child, r.context, rows[child].ty)
            and unary_type?(op, rows[child].ty, r.ty),
        Form::BinaryExpression(op, left, right) => 0 <= left < i and 0 <= right < i
            and edge?(rows, i, left, r.context, rows[left].ty)
            and edge?(rows, i, right, r.context, rows[right].ty)
            and binary_type?(op, rows[left].ty, rows[right].ty, r.ty),
        Form::Call(item, args) => (exists (k: Int), 0 <= k < s.functions.len
            and s.functions[k].item = item and args.len = s.functions[k].parameters.len
            and r.ty = s.functions[k].result
            and (forall (j: Int), when 0 <= j < args.len,
            edge?(rows, i, args[j], r.context, s.functions[k].parameters[j]))),
        Form::Let(question?, value, body) => 0 <= value < i
            and edge?(rows, i, value, r.context, rows[value].ty)
            and binder?(question?, rows[value].ty)
            and edge?(rows, i, body, [rows[value].ty] ++ r.context, r.ty),
        Form::Conditional(condition, yes, no) => edge?(rows, i, condition, r.context, Ty::Boolean)
            and edge?(rows, i, yes, r.context, r.ty) and edge?(rows, i, no, r.context, r.ty),
        Form::Match(scrutinee, arms) => 0 <= scrutinee < i and arms != []
            and edge?(rows, i, scrutinee, r.context, rows[scrutinee].ty)
            and (forall (j: Int), when 0 <= j < arms.len,
            edge?(rows, i, arms[j].body, r.context, r.ty)
            and (exists (k: Int), 0 <= k < s.constructors.len
            and s.constructors[k].item = arms[j].constructor
            and rows[scrutinee].ty = Ty::Nominal(s.constructors[k].owner))),
        Form::Parenthesized(child) => edge?(rows, i, child, r.context, r.ty),
    })
```

r[types.declaration.result] spec::types::derivation?
A function body has a derivation at its declared result type.

r[types.declaration.conditions] spec::types::derivation?
Each assume/expect body has a derivation at `Ty::Boolean`.

```fren
set_option fren.lint.undecidable "allow" in
pub fn derivation?(s: Symbols, rows: Seq<Row>, context: Context, ty: Ty) :=
    symbols_valid?(s) and rows != []
    and rows[rows.len - 1].context = context and rows[rows.len - 1].ty = ty
    and (forall (i: Int), when 0 <= i < rows.len, local_rule?(s, rows, i))
```

This is a full-domain decidable *derivation check* for arbitrary finite
sequences, not a test bounded to a particular number of nodes or enum types.
Every indexed access has an explicit finite bound. The `undecidable` lint
opt-outs mark the current solver's treatment of sequence operations and
integer quantifiers, not mathematical undecidability: their guards restrict
all quantified indices to the supplied finite sequences. They do not claim
that SMT can prove every universally quantified theorem about this judgment. A malformed index, empty
match, wrong context or wrong candidate type fails the relation. No solver
verdict or caller-supplied `accepted?` determines a row's validity.
By induction on the row index, each child of an accepted row has a derivation
in its required context. Conversely, a finite tree derivation can be listed
in postorder with these rows. Sharing is permitted only when both contexts
and types agree; a source adapter must retain every distinct written
occurrence for diagnostics. Extra rows are checked too and cannot hide an
ill-typed term. The judgment of a source expression is the existence of such
a derivation of its complete occurrence tree, with root context `Γ` and type
`T`. This existential presentation is not itself a claim that unbounded
SMT search for a witness terminates. Type inference on a fixed resolved
finite tree is a bottom-up decision: leaf types come from literals, `Γ` and
`Σ`; each operator, call, let or branch either determines its type or fails.
The production traversal's universal correspondence is recorded separately
in the [coverage document](../../../docs/fren2-specification-coverage.md).

Match coverage and absence of recursive function cycles are separate static
obligations. This relation admits repeated or missing constructors in a
nonempty match whose bodies have one type. It checks every arm, regardless
of reachability. Function bodies must have their declared result type;
assume/expect bodies must be Boolean in their parameter context.

## Worked derivations

Examples use the shared definitions, including negative derivations. A
nearest-first context `[Boolean, Integer]` gives local 0 type Boolean,
never Integer. A let value does not have access to its new slot.

```fren
pub const EMPTY_SYMBOLS: Symbols := Symbols { functions := [], constructors := [] }

pub fn literal(ty: Ty): Row := Row {
    form := Form::IntegerLiteral,
    context := [],
    ty,
}

set_option fren.lint.assertions_on_constants "allow" in
pub proc derivation_examples() {
    expect integer: derivation?(EMPTY_SYMBOLS, [literal(Ty::Integer)], [], Ty::Integer)
    expect wrong_literal: not derivation?(EMPTY_SYMBOLS, [literal(Ty::Boolean)], [], Ty::Boolean)
    expect absent_local: not derivation?(
        EMPTY_SYMBOLS,
        [
            Row {
                form := Form::Local(0),
                context := [],
                ty := Ty::Integer,
            },
        ],
        [],
        Ty::Integer
    )
    expect nearest: derivation?(
        EMPTY_SYMBOLS,
        [
            Row {
                form := Form::Local(0),
                context := [Ty::Boolean, Ty::Integer],
                ty := Ty::Boolean,
            },
        ],
        [Ty::Boolean, Ty::Integer],
        Ty::Boolean
    )
    expect wrong_nearest: not derivation?(
        EMPTY_SYMBOLS,
        [
            Row {
                form := Form::Local(0),
                context := [Ty::Boolean, Ty::Integer],
                ty := Ty::Integer,
            },
        ],
        [Ty::Boolean, Ty::Integer],
        Ty::Integer
    )
    expect missing_child: not derivation?(
        EMPTY_SYMBOLS,
        [
            Row {
                form := Form::Parenthesized(0),
                context := [],
                ty := Ty::Integer,
            },
        ],
        [],
        Ty::Integer
    )
    expect nominal: not binary_type?(
        Binary::Eq,
        Ty::Nominal(["M", "Light"]),
        Ty::Nominal(["M", "Signal"]),
        Ty::Boolean
    )
    expect domain_separate: binary_type?(Binary::Div, Ty::Integer, Ty::Integer, Ty::Integer)
}
```

The following examples exercise every expression form. Each case checks a
complete derivation, including every written row. The partial and repeated-arm
examples deliberately pass typing: coverage is separate. Wrong contexts,
argument counts, owners and branch types deliberately fail.
The type and expression Lean wrappers check every example constant against these Fren
definitions, using exact finite quantifier decisions. These concrete checks
do not prove production traversal soundness; the core definitions remain
unbounded in sequence length and nominal identity.

```fren
pub fn node(form: Form, context: Context, ty: Ty): Row := Row { form, context, ty }

pub const EXAMPLE_SYMBOLS: Symbols := Symbols {
    functions := [
        Signature {
            item := ["M", "f"],
            parameters := [Ty::Integer],
            result := Ty::Integer,
        },
    ],
    constructors := [
        Constructor {
            item := ["M", "Light", "Red"],
            owner := ["M", "Light"],
        },
        Constructor {
            item := ["M", "Light", "Green"],
            owner := ["M", "Light"],
        },
        Constructor {
            item := ["M", "Signal", "Red"],
            owner := ["M", "Signal"],
        },
    ],
}

pub const CALL_SYMBOLS: Symbols := { EXAMPLE_SYMBOLS with constructors := [] }

pub const MATCH_SYMBOLS: Symbols := Symbols {
    functions := [],
    constructors := [
        Constructor {
            item := ["M", "Light", "Red"],
            owner := ["M", "Light"],
        },
        Constructor {
            item := ["M", "Light", "Green"],
            owner := ["M", "Light"],
        },
    ],
}

pub const UNARY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::UnaryExpression(Unary::Negate, 0), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const UNARY_REJECT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::BooleanLiteral, [], Ty::Boolean),
            node(Form::UnaryExpression(Unary::Negate, 0), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const BINARY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::BinaryExpression(Binary::Add, 0, 1), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const BINARY_REJECT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::BooleanLiteral, [], Ty::Boolean),
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::BinaryExpression(Binary::Add, 0, 1), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const BOOLEAN_RIGHT_CHECKED_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::BooleanLiteral, [], Ty::Boolean),
            node(Form::Local(0), [], Ty::Boolean),
            node(Form::BinaryExpression(Binary::And, 0, 1), [], Ty::Boolean),
        ],
        [],
        Ty::Boolean
    )

pub const LET_BODY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::Local(0), [Ty::Integer], Ty::Integer),
        node(Form::Let(false, 0, 1), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const SUFFIX_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::Local(0), [Ty::Integer], Ty::Integer),
            node(Form::Let(true, 0, 1), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const LET_VALUE_SCOPE_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::Local(0), [], Ty::Integer),
            node(Form::Local(0), [Ty::Integer], Ty::Integer),
            node(Form::Let(false, 0, 1), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CONDITIONAL_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(Form::BooleanLiteral, [], Ty::Boolean),
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::Conditional(0, 1, 2), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const BOTH_BRANCHES_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::BooleanLiteral, [], Ty::Boolean),
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::BooleanLiteral, [], Ty::Boolean),
            node(Form::Conditional(0, 1, 2), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CONDITION_TYPE_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::Conditional(0, 1, 2), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const MATCH_ARMS_EXAMPLE: Bool := derivation?(
    MATCH_SYMBOLS,
    [
        node(
            Form::ConstructorValue(["M", "Light", "Red"]),
            [],
            Ty::Nominal(["M", "Light"])
        ),
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(
            Form::Match(
                0,
                [
                    Arm {
                        constructor := ["M", "Light", "Red"],
                        body := 1,
                    },
                    Arm {
                        constructor := ["M", "Light", "Green"],
                        body := 2,
                    },
                ]
            ),
            [],
            Ty::Integer
        ),
    ],
    [],
    Ty::Integer
)

pub const MATCH_OWNER_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        [
            node(
                Form::ConstructorValue(["M", "Light", "Red"]),
                [],
                Ty::Nominal(["M", "Light"])
            ),
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(
                Form::Match(
                    0,
                    [
                        Arm {
                            constructor := ["M", "Signal", "Red"],
                            body := 1,
                        },
                    ]
                ),
                [],
                Ty::Integer
            ),
        ],
        [],
        Ty::Integer
    )

pub const MATCH_EMPTY_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        [
            node(
                Form::ConstructorValue(["M", "Light", "Red"]),
                [],
                Ty::Nominal(["M", "Light"])
            ),
            node(Form::Match(0, []), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const MATCH_ALL_BODIES_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        [
            node(
                Form::ConstructorValue(["M", "Light", "Red"]),
                [],
                Ty::Nominal(["M", "Light"])
            ),
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::BooleanLiteral, [], Ty::Boolean),
            node(
                Form::Match(
                    0,
                    [
                        Arm {
                            constructor := ["M", "Light", "Red"],
                            body := 1,
                        },
                        Arm {
                            constructor := ["M", "Light", "Green"],
                            body := 2,
                        },
                    ]
                ),
                [],
                Ty::Integer
            ),
        ],
        [],
        Ty::Integer
    )

pub const COVERAGE_SEPARATE_EXAMPLE: Bool := derivation?(
    MATCH_SYMBOLS,
    [
        node(
            Form::ConstructorValue(["M", "Light", "Red"]),
            [],
            Ty::Nominal(["M", "Light"])
        ),
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(
            Form::Match(
                0,
                [
                    Arm {
                        constructor := ["M", "Light", "Red"],
                        body := 1,
                    },
                ]
            ),
            [],
            Ty::Integer
        ),
    ],
    [],
    Ty::Integer
)

pub const DUPLICATES_SEPARATE_EXAMPLE: Bool := derivation?(
    MATCH_SYMBOLS,
    [
        node(
            Form::ConstructorValue(["M", "Light", "Red"]),
            [],
            Ty::Nominal(["M", "Light"])
        ),
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(
            Form::Match(
                0,
                [
                    Arm {
                        constructor := ["M", "Light", "Red"],
                        body := 1,
                    },
                    Arm {
                        constructor := ["M", "Light", "Red"],
                        body := 1,
                    },
                ]
            ),
            [],
            Ty::Integer
        ),
    ],
    [],
    Ty::Integer
)

pub const CALL_EXAMPLE: Bool := derivation?(
    CALL_SYMBOLS,
    [
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::Call(["M", "f"], [0]), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const CALL_ARITY_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        [
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::Call(["M", "f"], [0, 0]), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CALL_ARGUMENT_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        [
            node(Form::BooleanLiteral, [], Ty::Boolean),
            node(Form::Call(["M", "f"], [0]), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CONSTRUCTOR_NOT_CALLABLE_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        [
            node(Form::IntegerLiteral, [], Ty::Integer),
            node(Form::Call(["M", "Light", "Red"], [0]), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const FUNCTION_NOT_VALUE_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        [node(Form::ConstructorValue(["M", "f"]), [], Ty::Integer)],
        [],
        Ty::Integer
    )

pub const CONSTRUCTOR_TYPE_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        [
            node(
                Form::ConstructorValue(["M", "Light", "Red"]),
                [],
                Ty::Integer
            ),
        ],
        [],
        Ty::Integer
    )

pub const PARENTHESES_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(Form::IntegerLiteral, [], Ty::Integer),
        node(Form::Parenthesized(0), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const CONTEXT_ALIGNMENT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(Form::Local(0), [Ty::Integer], Ty::Integer),
            node(Form::Parenthesized(0), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const PARAMETER_ORDER_EXAMPLE: Bool := parameter_context?(
    [
        Parameter { ty := Ty::Integer, question? := false },
        Parameter { ty := Ty::Boolean, question? := true },
    ],
    [Ty::Boolean, Ty::Integer]
)

pub const PARAMETER_SUFFIX_EXAMPLE: Bool :=
    not parameter_context?(
        [Parameter { ty := Ty::Integer, question? := true }],
        [Ty::Integer]
    )

pub const IMPLICIT_BOOLEAN_EXAMPLE: Bool := annotation_type?(Annotation::Omitted, true, Ty::Boolean)

pub const MISSING_ANNOTATION_EXAMPLE: Bool :=
    not annotation_type?(Annotation::Omitted, false, Ty::Boolean)

pub const EXPLICIT_NOT_OVERWRITTEN_EXAMPLE: Bool :=
    annotation_type?(Annotation::Integer, true, Ty::Integer) and not binder?(true, Ty::Integer)

pub const VALUE_OWNER_EXAMPLE: Bool := value_valid?(
    MATCH_SYMBOLS,
    Value::Nominal(["M", "Light"], ["M", "Light", "Red"])
)

pub const WRONG_VALUE_OWNER_EXAMPLE: Bool :=
    not value_valid?(
        EXAMPLE_SYMBOLS,
        Value::Nominal(["M", "Signal"], ["M", "Light", "Red"])
    )

pub const DIRECT_CALLEE_EXAMPLE: Bool := direct_item?(Form::Call(["M", "f"], []), ["M", "f"])
```

Typing does not decide integer division's domain or a Boolean goal's truth.
The following isolated source example pins the diagnostic at its original
line 5 column 28, byte span `[71, 72)`. Canonical type display uses `::`.

```fren example
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := l + 1  --~ error: type mismatch: expected `Int`, found `bad::Light`
```
