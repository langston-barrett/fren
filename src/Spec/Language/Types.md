# Core typing

The Core is the typed high-level intermediate representation (THIR). Source
constructs are defined by translation into Core forms. Static semantics comprises resolution, typing,
and verification, including definedness. This chapter defines typing;
[resolution](NamesAndScope.md) supplies identities, and
[expression obligations](Expressions.md) supply verification hypotheses to
be discharged by SMT. Dynamic semantics applies only to well-typed, verified
programs. Typing alone establishes neither definedness nor logical truth.

## Semantic objects

r[types.walking.identity] spec::types::{ItemId, Ty}
An *item identity* is the canonical sequence of enclosing module and item
names supplied by resolution. Constructor identities include their enumeration
name. Value types are Boolean, mathematical integer, and nominal enumeration
types; their constructors are disjoint.
<!-- status: definition -->

r[types.walking.compatibility] spec::types::{compatible_type?, compatibility}
Two value types are *compatible* exactly when they are equal, including every
component of a nominal identity.
<!-- status: smt -->

```fren
pub mod spec
pub mod spec::types

pub type ItemId := Seq<String>
pub enum Ty { Boolean, Integer, Nominal(ItemId) }

pub fn compatible_type?(left: Ty, right: Ty) := left = right

expect compatibility(a: ItemId, b: ItemId) {
    expect disjoint: Ty::Boolean != Ty::Integer and not Ty::Nominal(a) is Ty::Boolean | Ty::Integer
    expect nominal: compatible_type?(Ty::Nominal(a), Ty::Nominal(b)) iff a = b
}
```

r[types.sequence.snoc] spec::types::{Snoc, length, lookup}
A *snoc sequence* is either empty, written `·`, or an earlier snoc sequence
extended by one newest entry x, written `xs, x`. Its length `|xs|` counts
its entries. The *level* of an entry is the number of entries before it, so
the oldest entry has level 0 and the newest has level `|xs| - 1`. `xs(i)`
is the entry at level i, defined exactly when `0 ≤ i < |xs|`. A negative
level names no entry, so no rule needs a separate `0 ≤ i` premise.
<!-- status: definition -->

```fren
pub enum Snoc<T> { Empty, Extend(Snoc<T>, T) }

use self::Snoc::{Empty, Extend}

pub fn length<T>(xs: Snoc<T>): Nat := match xs {
    Empty => 0,
    Extend(earlier, _) => length(earlier) + 1,
}

pub fn lookup<T>(xs: Snoc<T>, level: Int): Option<T> := match xs {
    Empty => Option::None,
    Extend(earlier, x) =>
        if level = length(earlier) then Option::Some(x) else lookup(earlier, level),
}
```

r[types.context.slots] spec::types::Context
A *context* Γ is a snoc sequence of value types. Extending Γ by τ produces
`Γ, τ`, whose new entry has level `|Γ|`. A local refers to its entry by level,
which no later extension changes. The compiler's
[binding](../Compiler/Bindings.md#contexts-and-scope) representation numbers
the same entries nearest first; relating the two is part of the refinement
relation between this Core and the compiler.
<!-- status: definition -->

r[types.context.indices]
Production contexts list the same entries nearest first. For `0 ≤ i < |Γ|`, the
entry at level i is the production entry at index `|Γ| - 1 - i`.
<!-- status: lean Spec.Language.Types.lookup_nearest -->

r[types.context.bound] spec::types::lookup_bound
If `Γ(i) = τ`, then `0 ≤ i < |Γ|`.
<!-- status: smt -->

r[types.context.weakening] spec::types::lookup_weakening
Extension leaves every existing level unchanged: if `i < |Γ|`, then
`(Γ, σ)(i) = Γ(i)`, and `(Γ, σ)(|Γ|) = σ`.
<!-- status: smt -->

```fren
pub type Context := Snoc<Ty>

expect lookup_bound(context: Context, level: Int, ty: Ty) {
    expect below: when lookup(context, level) = Option::Some(ty), 0 <= level < length(context)
}

expect lookup_weakening(context: Context, extra: Ty, level: Int) {
    expect older: when 0 <= level < length(context), lookup(Extend(context, extra), level) = lookup(context, level)
    expect newest: lookup(Extend(context, extra), length(context)) = Option::Some(extra)
}
```

r[types.symbols.valid] spec::types::{Signature, ItemKind, Entry, Symbols, entry}
A *symbol environment* Σ is a finite map from item identities to entries.
An entry is either a function signature or a constructor's owning
enumeration, so no item is both. A signature contains the parameter types
as a context, in written order, and a result type. Σ is written as a snoc
sequence of bindings; `Σ(f)` is the newest binding of f, so the map is a
function by construction and needs no validity condition. All signatures
are available when bodies are typed.
<!-- status: definition -->

r[types.symbols.lookup] spec::types::entry_shadowing
Adding a binding for f determines `Σ(f)` and leaves every other item's
entry unchanged.
<!-- status: smt -->

```fren
pub struct Signature { parameters: Context, result: Ty }
pub enum ItemKind { Function(Signature), Constructor(ItemId) }
pub struct Entry { item: ItemId, kind: ItemKind }
pub type Symbols := Snoc<Entry>

pub fn entry(s: Symbols, item: ItemId): Option<ItemKind> := match s {
    Empty => Option::None,
    Extend(earlier, binding) =>
        if binding.item = item then Option::Some(binding.kind) else entry(earlier, item),
}

expect entry_shadowing(s: Symbols, binding: Entry, other: ItemId) {
    expect bound: entry(Extend(s, binding), binding.item) = Option::Some(binding.kind)
    expect others: when other != binding.item, entry(Extend(s, binding), other) = entry(s, other)
}
```

r[types.walking.annotations] spec::types::annotation_type?
A parameter or result annotation denotes its resolved value type. An omitted
parameter annotation denotes Boolean only when its name ends in `?`.
<!-- status: definition -->

r[types.walking.suffix] spec::types::suffix_rule?
The *`?` suffix rule*: a parameter or let binder whose name ends in `?` has
type Boolean, including when a parameter has an explicit annotation.
<!-- status: definition -->

```fren
pub enum Annotation { Boolean, Integer, Nominal(ItemId), Omitted }

pub fn annotation_type?(annotation: Annotation, question?, ty: Ty) := match annotation {
    Annotation::Boolean => ty = Ty::Boolean,
    Annotation::Integer => ty = Ty::Integer,
    Annotation::Nominal(item) => ty = Ty::Nominal(item),
    Annotation::Omitted => question? and ty = Ty::Boolean,
}

pub fn suffix_rule?(question?, ty: Ty) := not question? or ty = Ty::Boolean
```

There are no coercions or integer subtypes. A written `b?: Int` fails typing;
the suffix does not overwrite its annotation.

r[types.context.parameters] spec::types::{Parameter, parameter_context, parameters_valid?}
A declaration's body context lists its parameter types in written order:
the first parameter has level 0. Every parameter satisfies the `?` suffix
rule.
<!-- status: definition -->

```fren
pub struct Parameter { ty: Ty, question? }

pub fn parameter_context(parameters: Snoc<Parameter>): Context := match parameters {
    Empty => Empty,
    Extend(earlier, parameter) => Extend(parameter_context(earlier), parameter.ty),
}

pub fn parameters_valid?(parameters: Snoc<Parameter>) := match parameters {
    Empty => true,
    Extend(earlier, parameter) =>
        suffix_rule?(parameter.question?, parameter.ty) and parameters_valid?(earlier),
}
```

<a id="finite-expression-derivations"></a>

## Core forms and judgments

r[types.expression.syntax] spec::types::{ExprF, ArmF}
An expression has one of the forms of `ExprF<E>`, where E is the position
occupied by a child expression. The forms are complete: the dynamic
semantics reads the same syntax, so a literal carries its value. A call's
arguments and a match's arms are snoc sequences in written order. An arm has
a resolved constructor pattern and a body, with no binder. Parentheses are
concrete syntax, removed before the Core, and have no form here. A local's
level is an `Int` rather than a `Nat` because the checker of this chapter
does not admit a `Nat` within a recursive enumeration's payload, where the
derivation rows below hold forms.
<!-- status: definition -->

```fren
-- The operator enums move to the Syntax chapter, as `spec::syntax::UnaryOp` and `spec::syntax::BinaryOp`.
pub enum UnaryOp { Neg, Not }
pub enum BinaryOp { Add, Sub, Mul, Div, Mod, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Iff }

pub struct ArmF<E> { constructor: ItemId, body: E }

pub enum ExprF<E> {
    BooleanLiteral(Bool),
    IntegerLiteral(Int),
    Local(Int),
    ConstructorValue(ItemId),
    UnaryExpression(UnaryOp, E),
    BinaryExpression(BinaryOp, E, E),
    Call(ItemId, Snoc<E>),
    Let(Bool, E, E),
    Conditional(E, E, E),
    Match(E, Snoc<ArmF<E>>),
}

pub struct Judgment { context: Context, ty: Ty }
```

r[types.judgment.typing] spec::types::layer_rule?
The judgment `Σ; Γ ⊢ e : τ` holds when e has a finite derivation tree with
root context Γ and type τ. Each node satisfies `layer_rule?` for its form,
with each child position replaced by the judgment derived for that child.
A child judgment contains its own context and type; it is justified by that
child's subtree.
<!-- status: definition -->

r[types.judgment.layer] spec::types::layer_rule?
The one-layer judgment takes Σ, Γ, a form `ExprF<Judgment>` whose child
positions hold the children's judgments, and τ. It checks exactly the
matching rule below. The symbol environment is shared by every node of a
derivation.
<!-- status: definition -->

All written children require derivations, including unused let values,
both conditional branches and every match body. Verification is a further
static judgment, not a premise that may excuse a missing typing derivation.

## Typing rules

r[types.expression.values] spec::types::layer_rule?
The literal and constructor rules are the only rules for value leaves.
<!-- status: definition -->

r[types.expression.items] spec::types::layer_rule?
Only constructor items are values; only function items are callable.
Enumeration declarations, modules, assumptions, expectations and bare
functions are not value forms.
<!-- status: definition -->

r[types.operator.unary] spec::types::unary_type?
UnaryOp minus takes and returns integers; `not` takes and returns Booleans.
<!-- status: lean Spec.Language.Types.core_unary -->

r[types.operator.binary] spec::types::binary_type?
Arithmetic takes integers and returns an integer; integer comparisons return
a Boolean. Boolean operators take and return Booleans. Equality and
inequality take two compatible operands and return a Boolean.
<!-- status: lean Spec.Language.Types.core_binary -->

```fren
pub fn integer_binary?(op: BinaryOp) :=
    op in {
        BinaryOp::Add,
        BinaryOp::Sub,
        BinaryOp::Mul,
        BinaryOp::Div,
        BinaryOp::Mod,
    }

pub fn comparison?(op: BinaryOp) := op in {BinaryOp::Lt, BinaryOp::Le, BinaryOp::Gt, BinaryOp::Ge}
pub fn boolean_binary?(op: BinaryOp) := op in {BinaryOp::And, BinaryOp::Or, BinaryOp::Iff}

pub fn unary_type?(op: UnaryOp, operand: Ty, result: Ty) := match op {
    UnaryOp::Neg => operand = Ty::Integer and result = Ty::Integer,
    UnaryOp::Not => operand = Ty::Boolean and result = Ty::Boolean,
}

pub fn binary_type?(op: BinaryOp, left: Ty, right: Ty, result: Ty) :=
    if integer_binary?(op) then left = Ty::Integer and right = Ty::Integer and result = Ty::Integer
    else if comparison?(op) then left = Ty::Integer and right = Ty::Integer and result = Ty::Boolean
    else if boolean_binary?(op) then left = Ty::Boolean and right = Ty::Boolean and result = Ty::Boolean
    else compatible_type?(left, right) and result = Ty::Boolean
```

r[types.expression.boolean] spec::types::layer_rule?
With no premises, `Σ; Γ ⊢ BooleanLiteral(b) : Boolean`.
<!-- status: definition -->

r[types.expression.integer] spec::types::layer_rule?
With no premises, `Σ; Γ ⊢ IntegerLiteral(n) : Integer`.
<!-- status: definition -->

r[types.expression.local] spec::types::layer_rule?
If `Γ(i) = τ`, then `Σ; Γ ⊢ Local(i) : τ`.
<!-- status: definition -->

r[types.expression.constructor] spec::types::layer_rule?
If `Σ(c)` is a constructor of a, then
`Σ; Γ ⊢ ConstructorValue(c) : Nominal(a)`.
<!-- status: definition -->

r[types.expression.unary] spec::types::layer_rule?
If `Σ; Γ ⊢ e : σ` and `unary_type?(op, σ, τ)`, then
`Σ; Γ ⊢ UnaryExpression(op, e) : τ`.
<!-- status: definition -->

r[types.expression.binary] spec::types::layer_rule?
If `Σ; Γ ⊢ l : σ`, `Σ; Γ ⊢ r : υ` and `binary_type?(op, σ, υ, τ)`,
then `Σ; Γ ⊢ BinaryExpression(op, l, r) : τ`.
<!-- status: definition -->

r[types.expression.call] spec::types::{layer_rule?, in_context?, argument_types?}
If `Σ(f)` is a function with parameters `·, σ₀, …, σₙ₋₁` and result τ,
and `Σ; Γ ⊢ aᵢ : σᵢ` for each i < n, then
`Σ; Γ ⊢ Call(f, (·, a₀, …, aₙ₋₁)) : τ`. The arguments and parameters
correspond level by level, so their numbers are equal.
<!-- status: definition -->

r[types.expression.let] spec::types::layer_rule?
If `Σ; Γ ⊢ v : σ`, `suffix_rule?(q, σ)` and `Σ; Γ, σ ⊢ b : τ`,
then `Σ; Γ ⊢ Let(q, v, b) : τ`. The new binder has level `|Γ|` in b and is
absent from v's context.
<!-- status: definition -->

r[types.expression.if] spec::types::layer_rule?
If `Σ; Γ ⊢ c : Boolean`, `Σ; Γ ⊢ y : τ` and `Σ; Γ ⊢ n : τ`,
then `Σ; Γ ⊢ Conditional(c, y, n) : τ`.
<!-- status: definition -->

r[types.expression.match] spec::types::{layer_rule?, arm?, arms?}
If `Σ; Γ ⊢ s : Nominal(a)`, the arms are nonempty, every pattern's `Σ`
entry is a constructor of a, and `Σ; Γ ⊢ b : τ` for each arm body b, then
`Σ; Γ ⊢ Match(s, arms) : τ`. No arm extends Γ.
<!-- status: definition -->

```fren
pub fn in_context?(children: Snoc<Judgment>, context: Context) := match children {
    Empty => true,
    Extend(earlier, child) => child.context = context and in_context?(earlier, context),
}

pub fn argument_types?(args: Snoc<Judgment>, parameters: Context) := match args, parameters {
    Empty, Empty => true,
    Extend(earlier, arg), Extend(earlier_parameters, parameter) =>
        arg.ty = parameter and argument_types?(earlier, earlier_parameters),
    _, _ => false,
}

pub fn arm?(s: Symbols, arm: ArmF<Judgment>, owner: ItemId, context: Context, ty: Ty) :=
    arm.body.context = context and arm.body.ty = ty
    and entry(s, arm.constructor) = Option::Some(ItemKind::Constructor(owner))

pub fn arms?(s: Symbols, arms: Snoc<ArmF<Judgment>>, owner: ItemId, context: Context, ty: Ty) :=
    match arms {
        Empty => true,
        Extend(earlier, arm) =>
            arm?(s, arm, owner, context, ty) and arms?(s, earlier, owner, context, ty),
    }

pub fn layer_rule?(s: Symbols, context: Context, form: ExprF<Judgment>, ty: Ty) := match form {
    ExprF::BooleanLiteral(_) => ty = Ty::Boolean,
    ExprF::IntegerLiteral(_) => ty = Ty::Integer,
    ExprF::Local(level) => lookup(context, level) = Option::Some(ty),
    ExprF::ConstructorValue(item) => match entry(s, item) {
        Option::Some(ItemKind::Constructor(owner)) => ty = Ty::Nominal(owner),
        _ => false,
    },
    ExprF::UnaryExpression(op, operand) =>
        operand.context = context and unary_type?(op, operand.ty, ty),
    ExprF::BinaryExpression(op, left, right) => left.context = context and right.context = context
        and binary_type?(op, left.ty, right.ty, ty),
    ExprF::Call(item, args) => match entry(s, item) {
        Option::Some(ItemKind::Function(signature)) => ty = signature.result
            and in_context?(args, context) and argument_types?(args, signature.parameters),
        _ => false,
    },
    ExprF::Let(question?, value, body) =>
        value.context = context and suffix_rule?(question?, value.ty)
        and body.context = Extend(context, value.ty) and body.ty = ty,
    ExprF::Conditional(condition, yes, no) =>
        condition.context = context and condition.ty = Ty::Boolean
        and yes.context = context and yes.ty = ty and no.context = context and no.ty = ty,
    ExprF::Match(scrutinee, arms) =>
        scrutinee.context = context and match scrutinee.ty, arms {
            Ty::Nominal(owner), Extend(earlier, last) =>
                arm?(s, last, owner, context, ty) and arms?(s, earlier, owner, context, ty),
            _, _ => false,
        },
}
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

Each property below is its own rule, stated for all symbol environments,
contexts and child judgments. Its evidence is a Fren expectation checked by
the solver, or, where it needs induction over a snoc sequence, a theorem in
the chapter's wrapper.

r[types.operator.unary-unique] spec::types::unique_unary_operator
A unary operator has at most one result type for a fixed operand type.
<!-- status: smt -->

r[types.operator.binary-unique] spec::types::unique_binary_operator
A binary operator has at most one result type for fixed operand types.
<!-- status: smt -->

```fren
expect unique_unary_operator(op: UnaryOp, operand: Ty, a: Ty, b: Ty) {
    expect unique: when unary_type?(op, operand, a) and unary_type?(op, operand, b), a = b
}

expect unique_binary_operator(op: BinaryOp, left: Ty, right: Ty, a: Ty, b: Ty) {
    expect unique: when binary_type?(op, left, right, a) and binary_type?(op, left, right, b), a = b
}
```

For fixed Σ, Γ and child judgments, a layer of each form has at most one
type: if it satisfies its rule at τ and at υ, then τ = υ.

r[types.layer.unique-boolean] spec::types::unique_boolean
A Boolean literal layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-integer] spec::types::unique_integer
An integer literal layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-local] spec::types::unique_local
A local layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-constructor] spec::types::unique_constructor
A constructor layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-unary] spec::types::unique_unary
A unary layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-binary] spec::types::unique_binary
A binary layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-call] spec::types::unique_call
A call layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-let] spec::types::unique_let
A let layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-conditional] spec::types::unique_conditional
A conditional layer has at most one type.
<!-- status: smt -->

r[types.layer.unique-match] spec::types::unique_match
A match layer has at most one type.
<!-- status: smt -->

```fren
expect unique_boolean(s: Symbols, context: Context, value?, a: Ty, b: Ty) {
    expect unique: when layer_rule?(s, context, ExprF::BooleanLiteral(value?), a)
        and layer_rule?(s, context, ExprF::BooleanLiteral(value?), b), a = b
}

expect unique_integer(s: Symbols, context: Context, value: Int, a: Ty, b: Ty) {
    expect unique: when layer_rule?(s, context, ExprF::IntegerLiteral(value), a)
        and layer_rule?(s, context, ExprF::IntegerLiteral(value), b), a = b
}

expect unique_local(s: Symbols, context: Context, level: Int, a: Ty, b: Ty) {
    expect unique: when layer_rule?(s, context, ExprF::Local(level), a)
        and layer_rule?(s, context, ExprF::Local(level), b), a = b
}

expect unique_constructor(s: Symbols, context: Context, item: ItemId, a: Ty, b: Ty) {
    expect unique: when layer_rule?(s, context, ExprF::ConstructorValue(item), a)
        and layer_rule?(s, context, ExprF::ConstructorValue(item), b), a = b
}

expect unique_unary(s: Symbols, context: Context, op: UnaryOp, operand: Judgment, a: Ty, b: Ty) {
    expect unique: when layer_rule?(s, context, ExprF::UnaryExpression(op, operand), a)
        and layer_rule?(s, context, ExprF::UnaryExpression(op, operand), b), a = b
}

expect unique_binary(
    s: Symbols,
    context: Context,
    op: BinaryOp,
    left: Judgment,
    right: Judgment,
    a: Ty,
    b: Ty,
) {
    expect unique: when layer_rule?(s, context, ExprF::BinaryExpression(op, left, right), a)
        and layer_rule?(s, context, ExprF::BinaryExpression(op, left, right), b), a = b
}

expect unique_call(s: Symbols, context: Context, item: ItemId, args: Snoc<Judgment>, a: Ty, b: Ty) {
    expect unique: when layer_rule?(s, context, ExprF::Call(item, args), a)
        and layer_rule?(s, context, ExprF::Call(item, args), b), a = b
}

expect unique_let(
    s: Symbols,
    context: Context,
    question?,
    value: Judgment,
    body: Judgment,
    a: Ty,
    b: Ty,
) {
    expect unique: when layer_rule?(s, context, ExprF::Let(question?, value, body), a)
        and layer_rule?(s, context, ExprF::Let(question?, value, body), b), a = b
}

expect unique_conditional(
    s: Symbols,
    context: Context,
    condition: Judgment,
    yes: Judgment,
    no: Judgment,
    a: Ty,
    b: Ty,
) {
    expect unique: when layer_rule?(s, context, ExprF::Conditional(condition, yes, no), a)
        and layer_rule?(s, context, ExprF::Conditional(condition, yes, no), b), a = b
}

expect unique_match(
    s: Symbols,
    context: Context,
    scrutinee: Judgment,
    arms: Snoc<ArmF<Judgment>>,
    a: Ty,
    b: Ty,
) {
    expect unique: when layer_rule?(s, context, ExprF::Match(scrutinee, arms), a)
        and layer_rule?(s, context, ExprF::Match(scrutinee, arms), b), a = b
}
```

Each child's context is fixed by its position: every ordinary child uses Γ,
and only a let body extends it.

r[types.layer.context-unary] spec::types::context_unary
A unary operand uses Γ.
<!-- status: smt -->

r[types.layer.context-binary] spec::types::context_binary
Both binary operands use Γ, including both sides of `and` and `or`.
<!-- status: smt -->

r[types.layer.context-call] spec::types::context_call
Every argument of a call uses Γ.
<!-- status: smt -->

r[types.layer.context-let] spec::types::context_let
A let value uses Γ, and its body uses exactly `Γ, σ` for the value's type σ.
<!-- status: smt -->

r[types.layer.context-conditional] spec::types::context_conditional
A condition is a Boolean in Γ, and both branches use Γ.
<!-- status: smt -->

r[types.layer.context-match] spec::types::context_match
A match scrutinee uses Γ, and so does the newest arm body.
<!-- status: smt -->

r[types.layer.children-each] spec::types::children_each
If children satisfy `in_context?` for Γ, the child at every level uses Γ.
<!-- status: smt -->

r[types.layer.arms-each]
If arms satisfy `arms?` for owner a, Γ and τ, the arm at every level has a
body judged in Γ at τ, and its pattern is a constructor of a.
<!-- status: lean Spec.Language.Types.arms_each -->

r[types.layer.call-arity]
If `argument_types?(args, Δ)`, then `|args| = |Δ|`.
<!-- status: lean Spec.Language.Types.argument_types_length -->

```fren
expect context_unary(s: Symbols, context: Context, op: UnaryOp, operand: Judgment, ty: Ty) {
    expect operand_context: when layer_rule?(s, context, ExprF::UnaryExpression(op, operand), ty),
        operand.context = context
}

expect context_binary(
    s: Symbols,
    context: Context,
    op: BinaryOp,
    left: Judgment,
    right: Judgment,
    ty: Ty,
) {
    expect operands_context: when layer_rule?(
        s,
        context,
        ExprF::BinaryExpression(op, left, right),
        ty
    ),
        left.context = context and right.context = context
}

expect context_call(s: Symbols, context: Context, item: ItemId, args: Snoc<Judgment>, ty: Ty) {
    expect arguments_context: when layer_rule?(s, context, ExprF::Call(item, args), ty), in_context?(args, context)
}

expect context_let(
    s: Symbols,
    context: Context,
    question?,
    value: Judgment,
    body: Judgment,
    ty: Ty,
) {
    expect let_context: when layer_rule?(s, context, ExprF::Let(question?, value, body), ty),
        value.context = context and body.context = Extend(context, value.ty) and body.ty = ty
}

expect context_conditional(
    s: Symbols,
    context: Context,
    condition: Judgment,
    yes: Judgment,
    no: Judgment,
    ty: Ty,
) {
    expect branches_context: when layer_rule?(
        s,
        context,
        ExprF::Conditional(condition, yes, no),
        ty
    ),
        condition.context = context and condition.ty = Ty::Boolean and yes.context = context and no.context = context
}

expect context_match(
    s: Symbols,
    context: Context,
    scrutinee: Judgment,
    earlier: Snoc<ArmF<Judgment>>,
    last: ArmF<Judgment>,
    ty: Ty,
) {
    expect match_context: when layer_rule?(
        s,
        context,
        ExprF::Match(scrutinee, Extend(earlier, last)),
        ty
    ),
        scrutinee.context = context and last.body.context = context
}

expect children_each(children: Snoc<Judgment>, context: Context, level: Int, child: Judgment) {
    expect each: when in_context?(children, context) and lookup(children, level) = Option::Some(child),
        child.context = context
}
```

r[types.derivation.unique]
If `Σ; Γ ⊢ e : τ` and `Σ; Γ ⊢ e : υ`, then τ = υ. The claim is for the
same complete expression with the same resolved identities and local levels.
<!-- status: open -->

r[types.derivation.weakening]
If `Σ; Γ ⊢ e : τ`, then `Σ; Γ, σ ⊢ e' : τ`, where e' is e with every local
level of at least `|Γ|` increased by one. Those are exactly the levels bound
within e. Levels below `|Γ|` are unchanged, as
[context weakening](#r-types.context.weakening) states for lookup.
<!-- status: open -->

r[types.derivation.correspondence]
For an admitted resolved expression in this Core domain, a successful
production typing traversal yields exactly a derivation of its reported type
in its resolved context, and every such derivation is accepted by that
traversal. The correspondence retains every written occurrence and relates
each production nearest-first index i in a context Γ to the level
`|Γ| - 1 - i`.
<!-- status: open -->

## Primitive contracts

The following contracts express operator decisions with a finite tag and a
separate nominal equality atom. `Ty` retains complete canonical identities.

r[types.primitive.compatibility] spec::types::compatible::{meaning, builtin, nominal, distinct, disjoint}
Compatibility compares tags and, only for nominal types, identity atoms.
<!-- status: lean Spec.Language.Types.compatibility -->

```fren
pub enum ValueKind { Boolean, Integer, Nominal }

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
pub proc unary(op: UnaryOp, operand: ValueKind): (accepted?, result: ValueKind) {
    ensure meaning: accepted? iff (op = UnaryOp::Neg and operand = ValueKind::Integer) or (op = UnaryOp::Not and operand = ValueKind::Boolean)
    ensure result_type: when accepted?, result = operand

    expect negate_bool: when op = UnaryOp::Neg and operand = ValueKind::Boolean, not accepted?
    expect not_int: when op = UnaryOp::Not and operand = ValueKind::Integer, not accepted?
}
```

r[types.primitive.binary] spec::types::binary::{meaning, result_type, enum_add, mixed_equality, distinct_enums, same_enum}
A binary operator accepts exactly its table operands and returns its table
tag, including nominal identity comparison for equality.
<!-- status: lean Spec.Language.Types.binary -->

```fren
pub proc binary(op: BinaryOp, left: ValueKind, right: ValueKind, left_id: Int, right_id: Int): (
    accepted?,
    result: ValueKind,
) {
    ensure meaning: accepted? iff match op {
        BinaryOp::Add => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Sub => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Mul => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Div => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Mod => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Lt => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Le => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Gt => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::Ge => left = ValueKind::Integer and right = ValueKind::Integer,
        BinaryOp::And => left = ValueKind::Boolean and right = ValueKind::Boolean,
        BinaryOp::Or => left = ValueKind::Boolean and right = ValueKind::Boolean,
        BinaryOp::Iff => left = ValueKind::Boolean and right = ValueKind::Boolean,
        BinaryOp::Eq => left = right and (left != ValueKind::Nominal or left_id = right_id),
        BinaryOp::Ne => left = right and (left != ValueKind::Nominal or left_id = right_id),
    }
    ensure result_type: when accepted?, result = match op {
        BinaryOp::Add => ValueKind::Integer,
        BinaryOp::Sub => ValueKind::Integer,
        BinaryOp::Mul => ValueKind::Integer,
        BinaryOp::Div => ValueKind::Integer,
        BinaryOp::Mod => ValueKind::Integer,
        BinaryOp::Lt => ValueKind::Boolean,
        BinaryOp::Le => ValueKind::Boolean,
        BinaryOp::Gt => ValueKind::Boolean,
        BinaryOp::Ge => ValueKind::Boolean,
        BinaryOp::And => ValueKind::Boolean,
        BinaryOp::Or => ValueKind::Boolean,
        BinaryOp::Iff => ValueKind::Boolean,
        BinaryOp::Eq => ValueKind::Boolean,
        BinaryOp::Ne => ValueKind::Boolean,
    }

    expect enum_add: when op = BinaryOp::Add and left = ValueKind::Nominal, not accepted?
    expect mixed_equality: when op = BinaryOp::Eq and left != right, not accepted?
    expect distinct_enums: when op = BinaryOp::Ne and left = ValueKind::Nominal and right = left and left_id != right_id, not accepted?
    expect same_enum: when op = BinaryOp::Eq and left = ValueKind::Nominal and right = left and left_id = right_id, accepted? and result = ValueKind::Boolean
}
```


## Values and arithmetic domains

r[types.value.owner] spec::types::value_valid?
A nominal value records its enumeration owner and a constructor whose `Σ`
entry names that owner. Boolean and integer values have their built-in type.
<!-- status: definition -->

r[types.value.domain] spec::types::integer_domain?
Integer division and remainder require a nonzero divisor for verification.
This condition does not restrict their typing rule.
<!-- status: definition -->

r[types.value.examples] spec::types::meaning_examples
Addition and subtraction have their integer meanings within their domain,
division and remainder are Euclidean, and a zero divisor is outside the
domain of both.
<!-- status: smt -->

```fren
pub enum Value { Boolean(Bool), Integer(Int), Nominal(ItemId, ItemId) }

pub fn value_type(value: Value): Ty := match value {
    Value::Boolean(_) => Ty::Boolean,
    Value::Integer(_) => Ty::Integer,
    Value::Nominal(owner, _) => Ty::Nominal(owner),
}

pub fn value_valid?(s: Symbols, value: Value) := match value {
    Value::Nominal(owner, item) => entry(s, item) = Option::Some(ItemKind::Constructor(owner)),
    _ => true,
}

pub fn integer_domain?(op: BinaryOp, right: Int) :=
    not op in {BinaryOp::Div, BinaryOp::Mod} or right != 0

pub fn linear_meaning?(op: BinaryOp, left: Int, right: Int, result: Int) :=
    integer_domain?(op, right) and match op {
        BinaryOp::Add => result = left + right,
        BinaryOp::Sub => result = left - right,
        _ => false,
    }

set_option fren.lint.assertions_on_constants "allow" in
expect meaning_examples(n: Int) {
    expect addition: linear_meaning?(BinaryOp::Add, n, 1, n + 1)
    expect order: not linear_meaning?(BinaryOp::Sub, 7, 2, -5)
    expect quotient: -9 div (-2) = 5
    expect remainder: -9 mod (-2) = 1
    expect zero_domain: not integer_domain?(BinaryOp::Div, 0) and not integer_domain?(BinaryOp::Mod, 0)
}
```

## Derivation representation

r[types.derivation.table] spec::types::{Row, judgment_at, annotate, rows_valid?, derivation?}
A derivation may be represented by a snoc sequence of rows in postorder.
A row's form names each child by the level of an earlier row; a level that
names no earlier row fails. Every row satisfies the same one-layer rule,
with each child replaced by that earlier row's recorded context and type.
The newest row is the root; all rows, including any extra rows, are checked.
Unfolding shared rows produces a finite tree, and sharing requires
identical contexts and types.
<!-- status: definition -->

```fren
pub type Form := ExprF<Int>
pub type Arm := ArmF<Int>
pub struct Row { form: Form, context: Context, ty: Ty }

pub fn judgment_at(rows: Snoc<Row>, position: Int): Option<Judgment> := match rows {
    Empty => Option::None,
    Extend(earlier, row) =>
        if position = length(earlier)
        then Option::Some(Judgment { context := row.context, ty := row.ty })
        else judgment_at(earlier, position),
}

pub fn annotate_arguments(rows: Snoc<Row>, args: Snoc<Int>): Option<Snoc<Judgment>> := match args {
    Empty => Option::Some(Empty),
    Extend(earlier, arg) => match annotate_arguments(rows, earlier), judgment_at(rows, arg) {
        Option::Some(judged), Option::Some(child) => Option::Some(Extend(judged, child)),
        _, _ => Option::None,
    },
}

pub fn annotate_arms(rows: Snoc<Row>, arms: Snoc<Arm>): Option<Snoc<ArmF<Judgment>>> := match arms {
    Empty => Option::Some(Empty),
    Extend(earlier, arm) => match annotate_arms(rows, earlier), judgment_at(rows, arm.body) {
        Option::Some(judged), Option::Some(body) => Option::Some(
            Extend(judged, ArmF { constructor := arm.constructor, body })
        ),
        _, _ => Option::None,
    },
}

pub fn annotate(rows: Snoc<Row>, form: Form): Option<ExprF<Judgment>> := match form {
    ExprF::BooleanLiteral(value?) => Option::Some(ExprF::BooleanLiteral(value?)),
    ExprF::IntegerLiteral(value) => Option::Some(ExprF::IntegerLiteral(value)),
    ExprF::Local(level) => Option::Some(ExprF::Local(level)),
    ExprF::ConstructorValue(item) => Option::Some(ExprF::ConstructorValue(item)),
    ExprF::UnaryExpression(op, operand) => match judgment_at(rows, operand) {
        Option::Some(child) => Option::Some(ExprF::UnaryExpression(op, child)),
        Option::None => Option::None,
    },
    ExprF::BinaryExpression(op, left, right) =>
        match judgment_at(rows, left), judgment_at(rows, right) {
            Option::Some(l), Option::Some(r) => Option::Some(ExprF::BinaryExpression(op, l, r)),
            _, _ => Option::None,
        },
    ExprF::Call(item, args) => match annotate_arguments(rows, args) {
        Option::Some(judged) => Option::Some(ExprF::Call(item, judged)),
        Option::None => Option::None,
    },
    ExprF::Let(question?, value, body) => match judgment_at(rows, value), judgment_at(rows, body) {
        Option::Some(v), Option::Some(b) => Option::Some(ExprF::Let(question?, v, b)),
        _, _ => Option::None,
    },
    ExprF::Conditional(condition, yes, no) =>
        match judgment_at(rows, condition), judgment_at(rows, yes), judgment_at(rows, no) {
            Option::Some(c), Option::Some(y), Option::Some(n) =>
                Option::Some(ExprF::Conditional(c, y, n)),
            _, _, _ => Option::None,
        },
    ExprF::Match(scrutinee, arms) => match judgment_at(rows, scrutinee), annotate_arms(rows, arms) {
        Option::Some(judged), Option::Some(judged_arms) =>
            Option::Some(ExprF::Match(judged, judged_arms)),
        _, _ => Option::None,
    },
}

pub fn rows_valid?(s: Symbols, rows: Snoc<Row>) := match rows {
    Empty => true,
    Extend(earlier, row) =>
        rows_valid?(s, earlier) and match annotate(earlier, row.form) {
            Option::Some(form) => layer_rule?(s, row.context, form, row.ty),
            Option::None => false,
        },
}

pub fn derivation?(s: Symbols, rows: Snoc<Row>, context: Context, ty: Ty) :=
    rows_valid?(s, rows) and match rows {
        Empty => false,
        Extend(_, root) => root.context = context and root.ty = ty,
    }

pub fn arm_mentions?(arms: Snoc<Arm>, item: ItemId) := match arms {
    Empty => false,
    Extend(earlier, arm) => arm.constructor = item or arm_mentions?(earlier, item),
}

pub fn direct_item?(form: Form, item: ItemId) := match form {
    ExprF::ConstructorValue(target) => item = target,
    ExprF::Call(target, _) => item = target,
    ExprF::Match(_, arms) => arm_mentions?(arms, item),
    _ => false,
}
```

A representation of a source expression retains its complete occurrence tree;
a table alone does not identify which source expression it represents.

## Worked derivations

Examples use the shared definitions, including negative derivations. In the
context `·, Boolean, Integer`, local 0 has type Boolean, never Integer, and
local 1 has type Integer. A let value does not have access to its new level.

```fren
pub const EMPTY_SYMBOLS: Symbols := Empty

pub fn function(item: ItemId, parameters: Context, result: Ty): Entry := Entry {
    item,
    kind := ItemKind::Function(Signature { parameters, result }),
}

pub fn constructor(item: ItemId, owner: ItemId): Entry := Entry {
    item,
    kind := ItemKind::Constructor(owner),
}

pub fn node(form: Form, context: Context, ty: Ty): Row := Row { form, context, ty }

pub fn one(row: Row): Snoc<Row> := Extend(Empty, row)

pub const BOOLEAN_INTEGER: Context := Extend(Extend(Empty, Ty::Boolean), Ty::Integer)

pub const INTEGER_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    one(node(ExprF::IntegerLiteral(7), Empty, Ty::Integer)),
    Empty,
    Ty::Integer
)

pub const WRONG_LITERAL_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        one(node(ExprF::IntegerLiteral(7), Empty, Ty::Boolean)),
        Empty,
        Ty::Boolean
    )

pub const ABSENT_LOCAL_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        one(node(ExprF::Local(0), Empty, Ty::Integer)),
        Empty,
        Ty::Integer
    )

pub const OLDEST_LEVEL_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    one(node(ExprF::Local(0), BOOLEAN_INTEGER, Ty::Boolean)),
    BOOLEAN_INTEGER,
    Ty::Boolean
)

pub const WRONG_LEVEL_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        one(node(ExprF::Local(0), BOOLEAN_INTEGER, Ty::Integer)),
        BOOLEAN_INTEGER,
        Ty::Integer
    )

pub const NEWEST_LEVEL_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    one(node(ExprF::Local(1), BOOLEAN_INTEGER, Ty::Integer)),
    BOOLEAN_INTEGER,
    Ty::Integer
)

pub const MISSING_CHILD_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        one(
            node(ExprF::UnaryExpression(UnaryOp::Neg, 0), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const NOMINAL_EQUALITY_EXAMPLE: Bool :=
    not binary_type?(
        BinaryOp::Eq,
        Ty::Nominal(["M", "Light"]),
        Ty::Nominal(["M", "Signal"]),
        Ty::Boolean
    )

pub const DOMAIN_SEPARATE_EXAMPLE: Bool :=
    binary_type?(BinaryOp::Div, Ty::Integer, Ty::Integer, Ty::Integer)
```

The following examples exercise every expression form. Each case checks a
complete derivation, including every written row. The partial and repeated-arm
examples deliberately pass typing: coverage is separate. Wrong contexts,
argument counts, owners and branch types deliberately fail.
The examples instantiate the rules at particular contexts, types and symbols.

```fren
pub const EXAMPLE_SYMBOLS: Symbols := Extend(
    Extend(
        Extend(
            Extend(
                Empty,
                function(["M", "f"], Extend(Empty, Ty::Integer), Ty::Integer)
            ),
            constructor(["M", "Light", "Red"], ["M", "Light"])
        ),
        constructor(["M", "Light", "Green"], ["M", "Light"])
    ),
    constructor(["M", "Signal", "Red"], ["M", "Signal"])
)

pub const CALL_SYMBOLS: Symbols := Extend(
    Empty,
    function(["M", "f"], Extend(Empty, Ty::Integer), Ty::Integer)
)

pub const MATCH_SYMBOLS: Symbols := Extend(
    Extend(Empty, constructor(["M", "Light", "Red"], ["M", "Light"])),
    constructor(["M", "Light", "Green"], ["M", "Light"])
)

pub const LIGHT: Ty := Ty::Nominal(["M", "Light"])

pub const RED_ROW: Row := node(ExprF::ConstructorValue(["M", "Light", "Red"]), Empty, LIGHT)

pub fn arm(pattern: ItemId, body: Int): Arm := ArmF { constructor := pattern, body }

pub const UNARY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    Extend(
        one(node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
        node(ExprF::UnaryExpression(UnaryOp::Neg, 0), Empty, Ty::Integer)
    ),
    Empty,
    Ty::Integer
)

pub const UNARY_REJECT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            one(node(ExprF::BooleanLiteral(true), Empty, Ty::Boolean)),
            node(ExprF::UnaryExpression(UnaryOp::Neg, 0), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const BINARY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    Extend(
        Extend(
            one(node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
            node(ExprF::IntegerLiteral(2), Empty, Ty::Integer)
        ),
        node(
            ExprF::BinaryExpression(BinaryOp::Add, 0, 1),
            Empty,
            Ty::Integer
        )
    ),
    Empty,
    Ty::Integer
)

pub const BINARY_REJECT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            Extend(
                one(node(ExprF::BooleanLiteral(false), Empty, Ty::Boolean)),
                node(ExprF::IntegerLiteral(2), Empty, Ty::Integer)
            ),
            node(
                ExprF::BinaryExpression(BinaryOp::Add, 0, 1),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

pub const BOOLEAN_RIGHT_CHECKED_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            Extend(
                one(node(ExprF::BooleanLiteral(false), Empty, Ty::Boolean)),
                node(ExprF::Local(0), Empty, Ty::Boolean)
            ),
            node(
                ExprF::BinaryExpression(BinaryOp::And, 0, 1),
                Empty,
                Ty::Boolean
            )
        ),
        Empty,
        Ty::Boolean
    )

pub const LET_BODY_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    Extend(
        Extend(
            one(node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
            node(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
        ),
        node(ExprF::Let(false, 0, 1), Empty, Ty::Integer)
    ),
    Empty,
    Ty::Integer
)

pub const LET_LEVEL_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    Extend(
        Extend(
            one(
                node(
                    ExprF::IntegerLiteral(1),
                    Extend(Empty, Ty::Boolean),
                    Ty::Integer
                )
            ),
            node(ExprF::Local(1), BOOLEAN_INTEGER, Ty::Integer)
        ),
        node(
            ExprF::Let(false, 0, 1),
            Extend(Empty, Ty::Boolean),
            Ty::Integer
        )
    ),
    Extend(Empty, Ty::Boolean),
    Ty::Integer
)

pub const SUFFIX_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            Extend(
                one(node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
                node(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
            ),
            node(ExprF::Let(true, 0, 1), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const LET_VALUE_SCOPE_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            Extend(
                one(node(ExprF::Local(0), Empty, Ty::Integer)),
                node(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
            ),
            node(ExprF::Let(false, 0, 1), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const CONDITIONAL_EXAMPLE: Bool := derivation?(
    EMPTY_SYMBOLS,
    Extend(
        Extend(
            Extend(
                one(node(ExprF::BooleanLiteral(true), Empty, Ty::Boolean)),
                node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
            ),
            node(ExprF::IntegerLiteral(2), Empty, Ty::Integer)
        ),
        node(ExprF::Conditional(0, 1, 2), Empty, Ty::Integer)
    ),
    Empty,
    Ty::Integer
)

pub const BOTH_BRANCHES_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            Extend(
                Extend(
                    one(node(ExprF::BooleanLiteral(true), Empty, Ty::Boolean)),
                    node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
                ),
                node(ExprF::BooleanLiteral(false), Empty, Ty::Boolean)
            ),
            node(ExprF::Conditional(0, 1, 2), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const CONDITION_TYPE_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            Extend(
                Extend(
                    one(node(ExprF::IntegerLiteral(0), Empty, Ty::Integer)),
                    node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
                ),
                node(ExprF::IntegerLiteral(2), Empty, Ty::Integer)
            ),
            node(ExprF::Conditional(0, 1, 2), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const MATCH_ARMS_EXAMPLE: Bool := derivation?(
    MATCH_SYMBOLS,
    Extend(
        Extend(
            Extend(
                one(RED_ROW),
                node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
            ),
            node(ExprF::IntegerLiteral(2), Empty, Ty::Integer)
        ),
        node(
            ExprF::Match(
                0,
                Extend(
                    Extend(Empty, arm(["M", "Light", "Red"], 1)),
                    arm(["M", "Light", "Green"], 2)
                )
            ),
            Empty,
            Ty::Integer
        )
    ),
    Empty,
    Ty::Integer
)

pub const MATCH_OWNER_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            Extend(
                one(RED_ROW),
                node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
            ),
            node(
                ExprF::Match(0, Extend(Empty, arm(["M", "Signal", "Red"], 1))),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

pub const MATCH_EMPTY_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        Extend(
            one(RED_ROW),
            node(ExprF::Match(0, Empty), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const MATCH_ALL_BODIES_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        Extend(
            Extend(
                Extend(
                    one(RED_ROW),
                    node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
                ),
                node(ExprF::BooleanLiteral(true), Empty, Ty::Boolean)
            ),
            node(
                ExprF::Match(
                    0,
                    Extend(
                        Extend(Empty, arm(["M", "Light", "Red"], 1)),
                        arm(["M", "Light", "Green"], 2)
                    )
                ),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

pub const COVERAGE_SEPARATE_EXAMPLE: Bool := derivation?(
    MATCH_SYMBOLS,
    Extend(
        Extend(
            one(RED_ROW),
            node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
        ),
        node(
            ExprF::Match(0, Extend(Empty, arm(["M", "Light", "Red"], 1))),
            Empty,
            Ty::Integer
        )
    ),
    Empty,
    Ty::Integer
)

pub const DUPLICATES_SEPARATE_EXAMPLE: Bool := derivation?(
    MATCH_SYMBOLS,
    Extend(
        Extend(
            one(RED_ROW),
            node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
        ),
        node(
            ExprF::Match(
                0,
                Extend(
                    Extend(Empty, arm(["M", "Light", "Red"], 1)),
                    arm(["M", "Light", "Red"], 1)
                )
            ),
            Empty,
            Ty::Integer
        )
    ),
    Empty,
    Ty::Integer
)

pub const CALL_EXAMPLE: Bool := derivation?(
    CALL_SYMBOLS,
    Extend(
        one(node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
        node(
            ExprF::Call(["M", "f"], Extend(Empty, 0)),
            Empty,
            Ty::Integer
        )
    ),
    Empty,
    Ty::Integer
)

pub const CALL_ARITY_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        Extend(
            one(node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
            node(
                ExprF::Call(["M", "f"], Extend(Extend(Empty, 0), 0)),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

pub const CALL_ARGUMENT_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        Extend(
            one(node(ExprF::BooleanLiteral(true), Empty, Ty::Boolean)),
            node(
                ExprF::Call(["M", "f"], Extend(Empty, 0)),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

pub const CONSTRUCTOR_NOT_CALLABLE_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            one(node(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
            node(
                ExprF::Call(["M", "Light", "Red"], Extend(Empty, 0)),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

pub const FUNCTION_NOT_VALUE_EXAMPLE: Bool :=
    not derivation?(
        CALL_SYMBOLS,
        one(
            node(ExprF::ConstructorValue(["M", "f"]), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const CONSTRUCTOR_TYPE_EXAMPLE: Bool :=
    not derivation?(
        MATCH_SYMBOLS,
        one(
            node(
                ExprF::ConstructorValue(["M", "Light", "Red"]),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

pub const CONTEXT_ALIGNMENT_EXAMPLE: Bool :=
    not derivation?(
        EMPTY_SYMBOLS,
        Extend(
            one(
                node(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
            ),
            node(ExprF::UnaryExpression(UnaryOp::Neg, 0), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

pub const PARAMETER_ORDER_EXAMPLE: Bool :=
    parameter_context(
        Extend(
            Extend(Empty, Parameter { ty := Ty::Integer, question? := false }),
            Parameter { ty := Ty::Boolean, question? := true }
        )
    ) = Extend(Extend(Empty, Ty::Integer), Ty::Boolean)

pub const PARAMETER_SUFFIX_EXAMPLE: Bool :=
    not parameters_valid?(
        Extend(Empty, Parameter { ty := Ty::Integer, question? := true })
    )

pub const IMPLICIT_BOOLEAN_EXAMPLE: Bool := annotation_type?(Annotation::Omitted, true, Ty::Boolean)

pub const MISSING_ANNOTATION_EXAMPLE: Bool :=
    not annotation_type?(Annotation::Omitted, false, Ty::Boolean)

pub const EXPLICIT_NOT_OVERWRITTEN_EXAMPLE: Bool :=
    annotation_type?(Annotation::Integer, true, Ty::Integer) and not suffix_rule?(true, Ty::Integer)

pub const VALUE_OWNER_EXAMPLE: Bool := value_valid?(
    MATCH_SYMBOLS,
    Value::Nominal(["M", "Light"], ["M", "Light", "Red"])
)

pub const WRONG_VALUE_OWNER_EXAMPLE: Bool :=
    not value_valid?(
        EXAMPLE_SYMBOLS,
        Value::Nominal(["M", "Signal"], ["M", "Light", "Red"])
    )

pub const DIRECT_CALLEE_EXAMPLE: Bool := direct_item?(ExprF::Call(["M", "f"], Empty), ["M", "f"])
```

Typing does not decide integer division's domain or a Boolean goal's truth.
The following isolated source example pins the diagnostic at its original
line 5 column 28, byte span `[71, 72)`. Canonical type display uses `::`.

```fren example
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := l + 1  --~ error: type mismatch: expected `Int`, found `bad::Light`
```
