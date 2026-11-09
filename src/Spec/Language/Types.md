# Core typing

The Core is the typed high-level intermediate representation (THIR). Source
constructs are defined by translation into Core forms. Static semantics comprises resolution, typing,
and verification, including definedness. This chapter defines typing;
[resolution](NamesAndScope.md) supplies identities, and
[expression obligations](Expressions.md) supply verification hypotheses to
be discharged by SMT. Dynamic semantics applies only to well-typed, verified
programs. Typing alone establishes neither definedness nor logical truth.

## Semantic objects

r[types.walking.identity] spec::types::type_identity
An *item identity* is the canonical sequence of enclosing module and item
names supplied by resolution. Constructor identities include their enumeration
name. Value types are Boolean, mathematical integer, and nominal enumeration
types; their constructors are disjoint.
<!-- status: definition -->

r[types.walking.compatibility] spec::types::type_identity
Two value types are *compatible* exactly when they are equal, including every
component of a nominal identity.
<!-- status: smt -->

```fren
pub mod spec
pub mod spec::types

pub type ItemId := Seq<String>
pub enum Ty { Boolean, Integer, Nominal(ItemId) }
pub type Context := Seq<Ty>
pub struct Signature { item: ItemId, parameters: Seq<Ty>, result: Ty }
pub struct Constructor { item: ItemId, owner: ItemId }
pub struct Symbols { functions: Seq<Signature>, constructors: Seq<Constructor> }
pub enum Unary { Negate, Not }
pub enum Binary { Add, Sub, Mul, Div, Mod, Lt, Le, Gt, Ge, And, Or, Iff, Eq, Ne }
pub enum ValueKind { Boolean, Integer, Nominal }

pub fn compatible_type?(left: Ty, right: Ty) := left = right

pub proc type_identity(a: ItemId, b: ItemId) {
    expect disjoint: Ty::Boolean != Ty::Integer and not Ty::Nominal(a) is Ty::Boolean | Ty::Integer
    expect nominal: compatible_type?(Ty::Nominal(a), Ty::Nominal(b)) iff a = b
    expect reflexive: compatible_type?(Ty::Nominal(a), Ty::Nominal(a))
}
```

r[types.context.slots]
A *context* Γ is a finite sequence of value types, newest binder first.
Γ[i] is defined for 0 ≤ i < |Γ|. Extending Γ by τ produces `[τ] ++ Γ`.
Local indices refer to this exact context, as specified by
[binding](../Compiler/Bindings.md#contexts-and-scope).
<!-- status: definition -->

r[types.symbols.valid] spec::types::symbols_valid?
A *symbol environment* Σ contains function signatures and constructor
ownership. Each item has at most one entry and belongs to at most one of
these tables. Signatures contain parameter types in written order and a
result type. All signatures are available when bodies are typed.
<!-- status: definition -->

```fren
-- Finite sequence quantifiers lie outside the current solver's decidability lint.
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
A parameter or result annotation denotes its resolved value type. An omitted
parameter annotation denotes Boolean only when its name ends in `?`.
<!-- status: definition -->

r[types.walking.suffix] spec::types::binder?
A parameter or let binder whose name ends in `?` has type Boolean, including
when a parameter has an explicit annotation.
<!-- status: definition -->

```fren
pub enum Annotation { Boolean, Integer, Nominal(ItemId), Omitted }

pub fn annotation_type?(annotation: Annotation, question?, ty: Ty) := match annotation {
    Annotation::Boolean => ty = Ty::Boolean,
    Annotation::Integer => ty = Ty::Integer,
    Annotation::Nominal(item) => ty = Ty::Nominal(item),
    Annotation::Omitted => question? and ty = Ty::Boolean,
}

pub fn binder?(question?, ty: Ty) := not question? or ty = Ty::Boolean
pub struct Parameter { ty: Ty, question? }
```

There are no coercions or integer subtypes. A written `b?: Int` fails typing;
the suffix does not overwrite its annotation.

r[types.context.parameters] spec::types::parameter_context?
A declaration's body context reverses written parameter order. Every
parameter satisfies its binder condition.
<!-- status: definition -->

```fren
-- The bounded parameter/context sequence quantifier needs the solver lint opt-out.
set_option fren.lint.undecidable "allow" in
pub fn parameter_context?(parameters: Seq<Parameter>, context: Context) :=
    parameters.len = context.len
    and (forall (i: Int), when 0 <= i < parameters.len,
        context[parameters.len - 1 - i] = parameters[i].ty
        and binder?(parameters[i].question?, parameters[i].ty))
```

<a id="finite-expression-derivations"></a>

## Core forms and judgments

r[types.expression.syntax] spec::types::ExprF
An expression has one of the forms of `ExprF<E>`, where E is the position
occupied by a child expression. An arm has a resolved constructor pattern
and a body, with no binder. Literal payloads do not affect typing. Parentheses
are a type-preserving derived form retained in this presentation.
<!-- status: definition -->

```fren
pub struct ArmF<E> { constructor: ItemId, body: E }

pub enum ExprF<E> {
    BooleanLiteral,
    IntegerLiteral,
    Local(Int),
    ConstructorValue(ItemId),
    UnaryExpression(Unary, E),
    BinaryExpression(Binary, E, E),
    Call(ItemId, Seq<E>),
    Let(Bool, E, E),
    Conditional(E, E, E),
    Match(E, Seq<ArmF<E>>),
    Parenthesized(E),
}

pub struct Judgment { context: Context, ty: Ty }
```

r[types.judgment.typing] spec::types::layer_rule?
The judgment `Σ; Γ ⊢ e : τ` holds when e has a finite derivation tree with
root context Γ and type τ. Each node satisfies `layer_rule?` for its form
and the judgments derived by all its children. A child annotation contains
its own context and type; it is justified by that child's subtree.
<!-- status: definition -->

r[types.judgment.layer] spec::types::rule?
The one-layer judgment takes a form and child annotations and checks exactly
the matching rule below. `annotation` associates each child position with
its judgment. Instantiating E with `Judgment` and annotation with identity
places those annotations directly in the form. The symbol environment is
valid and shared by every node of a derivation. Lookup requires a matching
entry and checks the premise at every matching entry; validity makes that
entry unique.
<!-- status: definition -->

All written children require derivations, including unused let values,
both conditional branches and every match body. Verification is a further
static judgment, not a premise that may excuse a missing typing derivation.

## Typing rules

r[types.expression.values] spec::types::rule?
The literal and constructor rules are the only rules for value leaves.
<!-- status: definition -->

r[types.expression.items] spec::types::rule?
Only constructor items are values; only function items are callable.
Enumeration declarations, modules, assumptions, expectations and bare
functions are not value forms.
<!-- status: definition -->

r[types.operator.unary] spec::types::unary_type?
Unary minus takes and returns integers; `not` takes and returns Booleans.
<!-- status: lean Spec.Language.Types.core_unary -->

r[types.operator.binary] spec::types::binary_type?
Arithmetic takes integers and returns an integer; integer comparisons return
a Boolean. Boolean operators take and return Booleans. Equality and
inequality take two compatible operands and return a Boolean.
<!-- status: lean Spec.Language.Types.core_binary -->

```fren
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

r[types.expression.boolean] spec::types::rule?
With no premises, `Σ; Γ ⊢ BooleanLiteral : Boolean`.
<!-- status: definition -->

r[types.expression.integer] spec::types::rule?
With no premises, `Σ; Γ ⊢ IntegerLiteral : Integer`.
<!-- status: definition -->

r[types.expression.local] spec::types::rule?
If 0 ≤ i < |Γ| and Γ[i] = τ, then `Σ; Γ ⊢ Local(i) : τ`.
<!-- status: definition -->

r[types.expression.constructor] spec::types::rule?
If Σ records constructor c with owner a, then
`Σ; Γ ⊢ ConstructorValue(c) : Nominal(a)`.
<!-- status: definition -->

r[types.expression.unary] spec::types::rule?
If `Σ; Γ ⊢ e : σ` and `unary_type?(op, σ, τ)`, then
`Σ; Γ ⊢ UnaryExpression(op, e) : τ`.
<!-- status: definition -->

r[types.expression.binary] spec::types::rule?
If `Σ; Γ ⊢ l : σ`, `Σ; Γ ⊢ r : υ` and `binary_type?(op, σ, υ, τ)`,
then `Σ; Γ ⊢ BinaryExpression(op, l, r) : τ`.
<!-- status: definition -->

r[types.expression.call] spec::types::rule?
If Σ records f with parameter types σ₀ … σₙ₋₁ and result τ, there are
exactly n arguments, and `Σ; Γ ⊢ aᵢ : σᵢ` for each i, then
`Σ; Γ ⊢ Call(f, [a₀, …, aₙ₋₁]) : τ`.
<!-- status: definition -->

r[types.expression.let] spec::types::rule?
If `Σ; Γ ⊢ v : σ`, `binder?(q, σ)` and `Σ; [σ] ++ Γ ⊢ b : τ`,
then `Σ; Γ ⊢ Let(q, v, b) : τ`. The new binder is absent from v's context.
<!-- status: definition -->

r[types.expression.if] spec::types::rule?
If `Σ; Γ ⊢ c : Boolean`, `Σ; Γ ⊢ y : τ` and `Σ; Γ ⊢ n : τ`,
then `Σ; Γ ⊢ Conditional(c, y, n) : τ`.
<!-- status: definition -->

r[types.expression.match] spec::types::rule?
If `Σ; Γ ⊢ s : Nominal(a)`, the arms are nonempty, every pattern is a
constructor owned by a, and `Σ; Γ ⊢ b : τ` for each arm body b, then
`Σ; Γ ⊢ Match(s, arms) : τ`. No arm extends Γ.
<!-- status: definition -->

r[types.expression.parentheses] spec::types::rule?
If `Σ; Γ ⊢ e : τ`, then `Σ; Γ ⊢ Parenthesized(e) : τ`.
<!-- status: definition -->

```fren
-- Bounded table quantifiers and exact let-context concatenation exceed the solver lint's decidable core.
set_option fren.lint.undecidable "allow" in
pub fn rule?<E>(
    s: Symbols,
    context: Context,
    form: ExprF<E>,
    annotation: fn(E) -> Judgment,
    ty: Ty
) := match form {
    ExprF::BooleanLiteral => ty = Ty::Boolean,
    ExprF::IntegerLiteral => ty = Ty::Integer,
    ExprF::Local(slot) => 0 <= slot < context.len and ty = context[slot],
    ExprF::ConstructorValue(item) =>
        (exists (k: Int), 0 <= k < s.constructors.len and s.constructors[k].item = item)
        and (forall (k: Int), when 0 <= k < s.constructors.len, when s.constructors[k].item = item,
            ty = Ty::Nominal(s.constructors[k].owner)),
    ExprF::UnaryExpression(op, child) => annotation(child).context = context
        and unary_type?(op, annotation(child).ty, ty),
    ExprF::BinaryExpression(op, left, right) => annotation(left).context = context
        and annotation(right).context = context
        and binary_type?(op, annotation(left).ty, annotation(right).ty, ty),
    ExprF::Call(item, args) =>
        (exists (k: Int), 0 <= k < s.functions.len and s.functions[k].item = item)
        and (forall (k: Int), when 0 <= k < s.functions.len, when s.functions[k].item = item,
            args.len = s.functions[k].parameters.len and ty = s.functions[k].result
            and (forall (j: Int), when 0 <= j < args.len,
            annotation(args[j]).context = context and annotation(args[j]).ty = s.functions[k].parameters[j])),
    ExprF::Let(question?, value, body) => annotation(value).context = context
        and binder?(question?, annotation(value).ty)
        and annotation(body).context = [annotation(value).ty] ++ context and annotation(body).ty = ty,
    ExprF::Conditional(condition, yes, no) => annotation(condition).context = context
        and annotation(condition).ty = Ty::Boolean
        and annotation(yes).context = context and annotation(yes).ty = ty
        and annotation(no).context = context and annotation(no).ty = ty,
    ExprF::Match(scrutinee, arms) => arms != [] and annotation(scrutinee).context = context
        and (forall (j: Int), when 0 <= j < arms.len,
        annotation(arms[j].body).context = context and annotation(arms[j].body).ty = ty
        and (exists (k: Int), 0 <= k < s.constructors.len
        and s.constructors[k].item = arms[j].constructor
        and annotation(scrutinee).ty = Ty::Nominal(s.constructors[k].owner))),
    ExprF::Parenthesized(child) =>
        annotation(child).context = context and annotation(child).ty = ty,
}

pub fn layer_rule?(s: Symbols, context: Context, form: ExprF<Judgment>, ty: Ty) :=
    rule?(s, context, form, |child| child, ty)
```

r[types.declaration.result] spec::types::derivation?
A function body has a derivation at its declared result type in its parameter
context.
<!-- status: definition -->

r[types.declaration.conditions] spec::types::derivation?
Each assume or expect body has a derivation at Boolean in its parameter
context.
<!-- status: definition -->

Match coverage and absence of recursive function cycles are further static
conditions. Typing admits repeated or missing constructors in a nonempty
match. Operation domains, including nonzero divisors, belong to verification.
No dynamic behavior is assigned here to an unverified `x div 0` or to an
evaluation order.

## Properties of typing

r[types.layer.determinism] spec::types::layer_properties
For a valid Σ and fixed child annotations, a layer has at most one result
type: if it satisfies the rule at τ and υ, then τ = υ. The expectations
cover every constructor of `ExprF`.
<!-- status: smt -->

r[types.layer.context] spec::types::context_properties
Every ordinary child uses Γ. In a let, the value uses Γ and the body uses
exactly `[type(value)] ++ Γ`. Match arms introduce no binder.
<!-- status: smt -->

r[types.layer.operators] spec::types::operator_properties
Each unary or binary operator has at most one result type for fixed operand
types.
<!-- status: smt -->

```fren
pub proc operator_properties(op: Binary, unary_op: Unary, left: Ty, right: Ty, a: Ty, b: Ty) {
    expect unary_unique: when unary_type?(unary_op, left, a) and unary_type?(unary_op, left, b), a = b
    expect binary_unique: when binary_type?(op, left, right, a) and binary_type?(op, left, right, b), a = b
}

pub proc layer_properties(
    s: Symbols,
    context: Context,
    item: ItemId,
    slot: Int,
    op: Binary,
    unary_op: Unary,
    left: Judgment,
    right: Judgment,
    body: Judgment,
    q?,
    args: Seq<Judgment>,
    arms: Seq<ArmF<Judgment>>,
    a: Ty,
    b: Ty,
) {
    require valid: symbols_valid?(s)
    expect boolean: when layer_rule?(s, context, ExprF::BooleanLiteral, a) and layer_rule?(s, context, ExprF::BooleanLiteral, b), a = b
    expect integer: when layer_rule?(s, context, ExprF::IntegerLiteral, a) and layer_rule?(s, context, ExprF::IntegerLiteral, b), a = b
    expect local_case: when layer_rule?(s, context, ExprF::Local(slot), a) and layer_rule?(s, context, ExprF::Local(slot), b), a = b
    expect constructor: when layer_rule?(s, context, ExprF::ConstructorValue(item), a) and layer_rule?(s, context, ExprF::ConstructorValue(item), b), a = b
    expect unary: when layer_rule?(s, context, ExprF::UnaryExpression(unary_op, left), a) and layer_rule?(s, context, ExprF::UnaryExpression(unary_op, left), b), a = b
    expect binary: when layer_rule?(s, context, ExprF::BinaryExpression(op, left, right), a) and layer_rule?(s, context, ExprF::BinaryExpression(op, left, right), b), a = b
    expect call: when layer_rule?(s, context, ExprF::Call(item, args), a) and layer_rule?(s, context, ExprF::Call(item, args), b), a = b
    expect let_case: when layer_rule?(s, context, ExprF::Let(q?, left, body), a) and layer_rule?(s, context, ExprF::Let(q?, left, body), b), a = b
    expect conditional: when layer_rule?(s, context, ExprF::Conditional(left, right, body), a) and layer_rule?(s, context, ExprF::Conditional(left, right, body), b), a = b
    expect match_case: when layer_rule?(s, context, ExprF::Match(left, arms), a) and layer_rule?(s, context, ExprF::Match(left, arms), b), a = b
    expect parentheses: when layer_rule?(s, context, ExprF::Parenthesized(left), a) and layer_rule?(s, context, ExprF::Parenthesized(left), b), a = b
}

-- Exact let-context extension uses a sequence concatenation equation.
set_option fren.lint.undecidable "allow" in
pub proc context_properties(
    s: Symbols,
    context: Context,
    q?,
    value: Judgment,
    body: Judgment,
    c: Judgment,
    y: Judgment,
    n: Judgment,
    ty: Ty,
    op: Binary,
    unary_op: Unary,
    item: ItemId,
    args: Seq<Judgment>,
    arms: Seq<ArmF<Judgment>>,
    j: Int,
) {
    expect let_context: when layer_rule?(s, context, ExprF::Let(q?, value, body), ty),
        value.context = context and body.context = [value.ty] ++ context and body.ty = ty
    expect conditional_context: when layer_rule?(s, context, ExprF::Conditional(c, y, n), ty),
        c.context = context and c.ty = Ty::Boolean and y.context = context and n.context = context
    expect unary_context: when layer_rule?(s, context, ExprF::UnaryExpression(unary_op, value), ty), value.context = context
    expect binary_context: when layer_rule?(s, context, ExprF::BinaryExpression(op, value, body), ty), value.context = context and body.context = context
    expect call_context: when layer_rule?(s, context, ExprF::Call(item, args), ty) and 0 <= j < args.len, args[j].context = context
    expect match_context: when layer_rule?(s, context, ExprF::Match(value, arms), ty) and 0 <= j < arms.len, value.context = context and arms[j].body.context = context
    expect parentheses_context: when layer_rule?(s, context, ExprF::Parenthesized(value), ty), value.context = context
}
```

r[types.derivation.unique]
If `Σ; Γ ⊢ e : τ` and `Σ; Γ ⊢ e : υ`, then τ = υ. The claim is for the
same complete expression with the same resolved identities and local indices.
<!-- status: open -->

r[types.derivation.weakening]
If `Σ; Γ ⊢ e : τ`, extending Γ with fresh slots preserves typing after
capture-avoiding adjustment of local indices. Under each let the adjustment
protects the body's new slot and acts on the value in its incoming context.
<!-- status: open -->

r[types.derivation.correspondence]
For an admitted resolved expression in this Core domain, a successful
production typing traversal yields exactly a derivation of its reported type
in its resolved context, and every such derivation is accepted by that
traversal. The correspondence retains every written occurrence.
<!-- status: open -->

## Primitive contracts

The following contracts express operator decisions with a finite tag and a
separate nominal equality atom. `Ty` retains complete canonical identities.

r[types.primitive.compatibility] spec::types::compatible::{meaning, builtin, nominal, distinct, disjoint}
Compatibility compares tags and, only for nominal types, identity atoms.
<!-- status: lean Spec.Language.Types.compatibility -->

```fren
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
<!-- status: lean Spec.Language.Types.unary -->

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
<!-- status: lean Spec.Language.Types.binary -->

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


## Values and arithmetic domains

r[types.value.owner] spec::types::value_valid?
A nominal value records its enumeration owner and a constructor belonging
to that owner in Σ. Boolean and integer values have their built-in type.
<!-- status: definition -->

r[types.value.domain] spec::types::integer_domain?
Integer division and remainder require a nonzero divisor for verification.
This condition does not restrict their typing rule.
<!-- status: definition -->

```fren
pub enum Value { Boolean(Bool), Integer(Int), Nominal(ItemId, ItemId) }

pub fn value_type(value: Value): Ty := match value {
    Value::Boolean(_) => Ty::Boolean,
    Value::Integer(_) => Ty::Integer,
    Value::Nominal(owner, _) => Ty::Nominal(owner),
}

-- Constructor lookup quantifies over a supplied finite sequence.
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

## Derivation representation

r[types.derivation.table] spec::types::derivation?
A derivation may be represented by rows in postorder. Each child index is
strictly smaller than its parent index. Every row satisfies the same
one-layer rule under its recorded context and type. The last row is the
root; all rows, including any extra rows, are checked. Unfolding shared rows
produces a finite tree. Sharing requires identical contexts and types.
<!-- status: definition -->

```fren
pub type Form := ExprF<Int>
pub type Arm := ArmF<Int>
pub struct Row { form: Form, context: Context, ty: Ty }

-- Match-pattern membership quantifies over the finite arm sequence.
set_option fren.lint.undecidable "allow" in
pub fn direct_item?(form: Form, item: ItemId) := match form {
    ExprF::ConstructorValue(target) => item = target,
    ExprF::Call(target, _) => item = target,
    ExprF::Match(_, arms) => (exists (j: Int), 0 <= j < arms.len and item = arms[j].constructor),
    _ => false,
}

pub fn edge?(rows: Seq<Row>, parent: Int, child: Int, context: Context, ty: Ty) :=
    0 <= child < parent < rows.len and rows[child].context = context and compatible_type?(rows[child].ty, ty)

-- Child-position checks quantify only over finite argument and arm sequences.
set_option fren.lint.undecidable "allow" in
pub fn children_before?(form: Form, parent: Int) := match form {
    ExprF::UnaryExpression(_, child) => 0 <= child < parent,
    ExprF::BinaryExpression(_, left, right) => 0 <= left < parent and 0 <= right < parent,
    ExprF::Call(_, args) => (forall (j: Int), when 0 <= j < args.len, 0 <= args[j] < parent),
    ExprF::Let(_, value, body) => 0 <= value < parent and 0 <= body < parent,
    ExprF::Conditional(condition, yes, no) =>
        0 <= condition < parent and 0 <= yes < parent and 0 <= no < parent,
    ExprF::Match(scrutinee, arms) => 0 <= scrutinee < parent
        and (forall (j: Int), when 0 <= j < arms.len, 0 <= arms[j].body < parent),
    ExprF::Parenthesized(child) => 0 <= child < parent,
    _ => true,
}

pub fn local_rule?(s: Symbols, rows: Seq<Row>, i: Int) := 0 <= i < rows.len
    and children_before?(rows[i].form, i)
    and rule?(
        s,
        rows[i].context,
        rows[i].form,
        |child| Judgment {
            context := rows[child].context,
            ty := rows[child].ty,
        },
        rows[i].ty
    )

-- The derivation check quantifies over all rows of the supplied finite table.
set_option fren.lint.undecidable "allow" in
pub fn derivation?(s: Symbols, rows: Seq<Row>, context: Context, ty: Ty) :=
    symbols_valid?(s) and rows != []
    and rows[rows.len - 1].context = context and rows[rows.len - 1].ty = ty
    and (forall (i: Int), when 0 <= i < rows.len, local_rule?(s, rows, i))
```

A representation of a source expression retains its complete occurrence tree;
a table alone does not identify which source expression it represents.

## Worked derivations

Examples use the shared definitions, including negative derivations. A
nearest-first context `[Boolean, Integer]` gives local 0 type Boolean,
never Integer. A let value does not have access to its new slot.

```fren
pub const EMPTY_SYMBOLS: Symbols := Symbols { functions := [], constructors := [] }

pub fn literal(ty: Ty): Row := Row {
    form := ExprF::IntegerLiteral,
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
                form := ExprF::Local(0),
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
                form := ExprF::Local(0),
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
                form := ExprF::Local(0),
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
                form := ExprF::Parenthesized(0),
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
The examples instantiate the rules at particular contexts, types and symbols.

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
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::UnaryExpression(Unary::Negate, 0), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const UNARY_REJECT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::BooleanLiteral, [], Ty::Boolean),
            node(ExprF::UnaryExpression(Unary::Negate, 0), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const BINARY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::BinaryExpression(Binary::Add, 0, 1), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const BINARY_REJECT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::BooleanLiteral, [], Ty::Boolean),
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::BinaryExpression(Binary::Add, 0, 1), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const BOOLEAN_RIGHT_CHECKED_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::BooleanLiteral, [], Ty::Boolean),
            node(ExprF::Local(0), [], Ty::Boolean),
            node(ExprF::BinaryExpression(Binary::And, 0, 1), [], Ty::Boolean),
        ],
        [],
        Ty::Boolean
    )

pub const LET_BODY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::Local(0), [Ty::Integer], Ty::Integer),
        node(ExprF::Let(false, 0, 1), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const SUFFIX_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::Local(0), [Ty::Integer], Ty::Integer),
            node(ExprF::Let(true, 0, 1), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const LET_VALUE_SCOPE_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::Local(0), [], Ty::Integer),
            node(ExprF::Local(0), [Ty::Integer], Ty::Integer),
            node(ExprF::Let(false, 0, 1), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CONDITIONAL_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    [
        node(ExprF::BooleanLiteral, [], Ty::Boolean),
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::Conditional(0, 1, 2), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const BOTH_BRANCHES_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::BooleanLiteral, [], Ty::Boolean),
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::BooleanLiteral, [], Ty::Boolean),
            node(ExprF::Conditional(0, 1, 2), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CONDITION_TYPE_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::Conditional(0, 1, 2), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const MATCH_ARMS_EXAMPLE: Bool := derivation?(
    MATCH_SYMBOLS,
    [
        node(
            ExprF::ConstructorValue(["M", "Light", "Red"]),
            [],
            Ty::Nominal(["M", "Light"])
        ),
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(
            ExprF::Match(
                0,
                [
                    ArmF {
                        constructor := ["M", "Light", "Red"],
                        body := 1,
                    },
                    ArmF {
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
                ExprF::ConstructorValue(["M", "Light", "Red"]),
                [],
                Ty::Nominal(["M", "Light"])
            ),
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(
                ExprF::Match(
                    0,
                    [
                        ArmF {
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
                ExprF::ConstructorValue(["M", "Light", "Red"]),
                [],
                Ty::Nominal(["M", "Light"])
            ),
            node(ExprF::Match(0, []), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const MATCH_ALL_BODIES_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        [
            node(
                ExprF::ConstructorValue(["M", "Light", "Red"]),
                [],
                Ty::Nominal(["M", "Light"])
            ),
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::BooleanLiteral, [], Ty::Boolean),
            node(
                ExprF::Match(
                    0,
                    [
                        ArmF {
                            constructor := ["M", "Light", "Red"],
                            body := 1,
                        },
                        ArmF {
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
            ExprF::ConstructorValue(["M", "Light", "Red"]),
            [],
            Ty::Nominal(["M", "Light"])
        ),
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(
            ExprF::Match(
                0,
                [
                    ArmF {
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
            ExprF::ConstructorValue(["M", "Light", "Red"]),
            [],
            Ty::Nominal(["M", "Light"])
        ),
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(
            ExprF::Match(
                0,
                [
                    ArmF {
                        constructor := ["M", "Light", "Red"],
                        body := 1,
                    },
                    ArmF {
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
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::Call(["M", "f"], [0]), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const CALL_ARITY_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        [
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::Call(["M", "f"], [0, 0]), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CALL_ARGUMENT_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        [
            node(ExprF::BooleanLiteral, [], Ty::Boolean),
            node(ExprF::Call(["M", "f"], [0]), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const CONSTRUCTOR_NOT_CALLABLE_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        [
            node(ExprF::IntegerLiteral, [], Ty::Integer),
            node(ExprF::Call(["M", "Light", "Red"], [0]), [], Ty::Integer),
        ],
        [],
        Ty::Integer
    )

pub const FUNCTION_NOT_VALUE_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        [node(ExprF::ConstructorValue(["M", "f"]), [], Ty::Integer)],
        [],
        Ty::Integer
    )

pub const CONSTRUCTOR_TYPE_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        [
            node(
                ExprF::ConstructorValue(["M", "Light", "Red"]),
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
        node(ExprF::IntegerLiteral, [], Ty::Integer),
        node(ExprF::Parenthesized(0), [], Ty::Integer),
    ],
    [],
    Ty::Integer
)

pub const CONTEXT_ALIGNMENT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        [
            node(ExprF::Local(0), [Ty::Integer], Ty::Integer),
            node(ExprF::Parenthesized(0), [], Ty::Integer),
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

pub const DIRECT_CALLEE_EXAMPLE: Bool := direct_item?(ExprF::Call(["M", "f"], []), ["M", "f"])
```

Typing does not decide integer division's domain or a Boolean goal's truth.
The following isolated source example pins the diagnostic at its original
line 5 column 28, byte span `[71, 72)`. Canonical type display uses `::`.

```fren example
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := l + 1  --~ error: type mismatch: expected `Int`, found `bad::Light`
```
