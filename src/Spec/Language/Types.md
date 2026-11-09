# Core typing

The Core is the typed high-level intermediate representation (THIR). Source
constructs are defined by translation into Core forms. Static semantics comprises resolution, typing,
and verification, including definedness. This chapter defines typing;
[resolution](NamesAndScope.md) supplies identities, and
[expression obligations](Expressions.md) supply verification hypotheses to
be discharged by SMT. Dynamic semantics applies only to well-typed, verified
programs. Typing alone establishes neither definedness nor logical truth.

The Core has no names for locals: a local is written `#i`, its de Bruijn
level, and a let binds the next level. Its grammar, informally:

```text
τ ::= Boolean | Integer | Nominal(a)
Γ ::= · | Γ, τ
e ::= b | n | #i | c | ⊖ e | e ⊕ e | f(e, …, e)
    | let[: τ] e in e | if e then e else e | match e { c ⇒ e | … | c ⇒ e }
```

Here b is a Boolean, n an integer, c a constructor and f a function, each
item named by its canonical identity; ⊖ is a unary and ⊕ a binary operator.
A match has at least one arm. The rules of this chapter, in the notation of
[The Definition of Standard ML](https://smlfamily.github.io/sml97-defn.pdf),
are summarized below; the numbered rules that follow are normative.

```text
                                      Γ(i) = τ                   Σ(c) = constructor of a
  Σ; Γ ⊢ b : Boolean                  ─────────────              ───────────────────────
  Σ; Γ ⊢ n : Integer                  Σ; Γ ⊢ #i : τ              Σ; Γ ⊢ c : Nominal(a)

  Σ; Γ ⊢ e : σ   σ ⊖ ⇒ τ              Σ; Γ ⊢ l : σ   Σ; Γ ⊢ r : υ   σ ⊕ υ ⇒ τ
  ──────────────────────              ─────────────────────────────────────
  Σ; Γ ⊢ ⊖ e : τ                      Σ; Γ ⊢ l ⊕ r : τ

  Σ(f) = function (·, σ₀, …, σₙ₋₁) → τ    Σ; Γ ⊢ aₖ : σₖ  (each k < n)
  ──────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ f(a₀, …, aₙ₋₁) : τ

  Σ; Γ ⊢ v : σ   (σ' = σ if annotated with σ')   Σ; Γ, σ ⊢ b : τ
  ──────────────────────────────────────────────────────────────
  Σ; Γ ⊢ let[: σ'] v in b : τ

  Σ; Γ ⊢ c : Boolean   Σ; Γ ⊢ t : τ   Σ; Γ ⊢ e : τ
  ────────────────────────────────────────────────
  Σ; Γ ⊢ if c then t else e : τ

  Σ; Γ ⊢ s : Nominal(a)   Σ(cₖ) = constructor of a   Σ; Γ ⊢ bₖ : τ  (each arm)
  ──────────────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ match s { c₀ ⇒ b₀ | … | cₘ ⇒ bₘ } : τ
```

## Semantic objects

r[types.object.identity] spec::types::{ItemId, Ty}
An *item identity* is the canonical sequence of enclosing module and item
names supplied by resolution. Constructor identities include their enumeration
name. Value types are Boolean, mathematical integer, and nominal enumeration
types; their constructors are disjoint. Two types are the same type exactly
when they are equal, including every component of a nominal identity; there
are no coercions or subtypes.
<!-- status: definition -->

```fren
pub mod spec
pub mod spec::types

pub type ItemId := Seq<String>
pub enum Ty { Boolean, Integer, Nominal(ItemId) }
```

r[types.sequence.snoc] spec::types::{Snoc, length, lookup}
A *snoc sequence* is either empty, written `·`, or an earlier snoc sequence
extended by one newest entry x, written `xs, x`. Its length `|xs|` counts
its entries. The *level* of an entry is the number of entries before it, so
the oldest entry has level 0 and the newest has level `|xs| - 1`. `xs(i)`
is the entry at level i, defined exactly when `0 ≤ i < |xs|`.
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
which no later extension changes.
<!-- status: definition -->

r[types.context.bound] spec::types::lookup_bound
If `Γ(i) = τ`, then `0 ≤ i < |Γ|`.
<!-- status: smt -->

r[types.context.weakening] spec::types::lookup_weakening
Extension leaves every existing level unchanged: if `0 ≤ i < |Γ|`, then
`(Γ, σ)(i) = Γ(i)`, and `(Γ, σ)(|Γ|) = σ`.
<!-- status: smt -->

```fren
pub type Context := Snoc<Ty>

expect lookup_bound(context: Context, level: Int, ty: Ty) {
    expect below: when lookup(context, level) = Option::Some(ty), 0 <= level < length(context)
}

expect lookup_weakening(context: Context, extra: Ty, level: Int) {
    expect older: when 0 <= level < length(context),
        lookup(Extend(context, extra), level) = lookup(context, level)
    expect newest: lookup(Extend(context, extra), length(context)) = Option::Some(extra)
}
```

r[types.symbols.environment] spec::types::{Signature, ItemKind, Entry, Symbols, entry}
A *symbol environment* Σ binds item identities to entries. An entry is a
function signature, a constructor's owning enumeration, or an enumeration
with its constructors, so no item is two of these. A signature has the
parameter types as a context, in written order, and a result type. `Σ(x)`
is x's entry. The environment is shared by every body of a program, so all
signatures are available when any body is typed.
<!-- status: definition -->

r[types.symbols.well-formed] spec::types::{type_ok?, context_ok?, symbols_ok?}
A type is *well formed* in Σ when it is Boolean, Integer, or `Nominal(a)`
with `Σ(a)` an enumeration. Σ is well formed when it binds each item once,
every signature's types are well formed, every constructor's owner is an
enumeration that lists it, and every constructor that an enumeration lists
is bound as a constructor of that enumeration. Resolution rejects a
duplicate item, so a well-formed Σ never binds one twice.
<!-- status: definition -->

```fren
pub struct Signature { parameters: Context, result: Ty }
pub enum ItemKind { Function(Signature), Constructor(ItemId), Enumeration(Snoc<ItemId>) }
pub struct Entry { item: ItemId, kind: ItemKind }
pub type Symbols := Snoc<Entry>

pub fn entry(symbols: Symbols, item: ItemId): Option<ItemKind> := match symbols {
    Empty => Option::None,
    Extend(earlier, binding) =>
        if binding.item = item then Option::Some(binding.kind) else entry(earlier, item),
}

pub fn type_ok?(symbols: Symbols, ty: Ty) := match ty {
    Ty::Nominal(owner) => entry(symbols, owner) is Option::Some(ItemKind::Enumeration(_)),
    _ => true,
}

pub fn context_ok?(symbols: Symbols, context: Context) := match context {
    Empty => true,
    Extend(earlier, ty) => type_ok?(symbols, ty) and context_ok?(symbols, earlier),
}

pub fn member?(items: Snoc<ItemId>, item: ItemId) := match items {
    Empty => false,
    Extend(earlier, other) => other = item or member?(earlier, item),
}

pub fn constructors_ok?(symbols: Symbols, constructors: Snoc<ItemId>, owner: ItemId) :=
    match constructors {
        Empty => true,
        Extend(earlier, constructor) =>
            entry(symbols, constructor) = Option::Some(ItemKind::Constructor(owner))
            and constructors_ok?(symbols, earlier, owner),
    }

pub fn binding_ok?(symbols: Symbols, binding: Entry) := match binding.kind {
    ItemKind::Function(signature) =>
        context_ok?(symbols, signature.parameters) and type_ok?(symbols, signature.result),
    ItemKind::Constructor(owner) => match entry(symbols, owner) {
        Option::Some(ItemKind::Enumeration(constructors)) => member?(constructors, binding.item),
        _ => false,
    },
    ItemKind::Enumeration(constructors) => constructors_ok?(symbols, constructors, binding.item),
}

pub fn bindings_ok?(symbols: Symbols, bindings: Symbols) := match bindings {
    Empty => true,
    Extend(earlier, binding) =>
        entry(earlier, binding.item) = Option::None
        and binding_ok?(symbols, binding)
        and bindings_ok?(symbols, earlier),
}

pub fn symbols_ok?(symbols: Symbols) := bindings_ok?(symbols, symbols)
```

<a id="finite-expression-derivations"></a>

## Core forms and judgments

r[types.expression.syntax] spec::types::{ExprF, ArmF, UnaryOp, BinaryOp}
An expression has one of the forms of `ExprF<E>`, where E is the position
occupied by a child expression. The forms are complete: the dynamic
semantics reads the same syntax, so a literal carries its value, and a let
carries the type annotation written on it, if any. A call's arguments and a
match's arms are snoc sequences in written order. An arm has a resolved
constructor pattern and a body, with no binder. Parentheses are concrete
syntax, removed before the Core, and have no form here.
<!-- status: definition -->

Fren, the language of this chapter's definitions, cannot yet declare a
datatype that contains itself inside another type, so an expression is
given one layer at a time, and a whole derivation as a table of rows.

```fren
pub enum UnaryOp { Neg, Not }
pub enum BinaryOp { Add, Sub, Mul, Div, Mod, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Iff }

pub struct ArmF<E> { constructor: ItemId, body: E }

pub enum ExprF<E> {
    BooleanLiteral(Bool),
    IntegerLiteral(Int),
    Local(Int),
    Constructor(ItemId),
    Unary(UnaryOp, E),
    Binary(BinaryOp, E, E),
    Call(ItemId, Snoc<E>),
    Let(Option<Ty>, E, E),
    Conditional(E, E, E),
    Match(E, Snoc<ArmF<E>>),
}

pub struct Typing { context: Context, ty: Ty }
```

r[types.judgment.typing] spec::types::{derivation?, rule?}
The judgment `Σ; Γ ⊢ e : τ` is defined for a well-formed Σ. It holds when e
has a finite derivation tree with root context Γ and type τ. Each node satisfies `rule?` for its form, with
each child position replaced by the typing derived for that child. A child
typing contains its own context and type; it is justified by that child's
subtree. `derivation?` checks such a tree, given as a table.
<!-- status: definition -->

r[types.judgment.layer] spec::types::rule?
The one-layer judgment takes Σ, Γ, a form `ExprF<Typing>` whose child
positions hold the children's typings, and τ. It checks exactly the
matching rule below.
<!-- status: definition -->

r[types.judgment.children]
Every written child requires a derivation, including unused let values,
both conditional branches and every match body. Verification is a further
static judgment, not a premise that may excuse a missing typing derivation.
<!-- status: definition -->

r[types.judgment.separate]
Match coverage and the absence of recursive function cycles are further
static conditions; typing admits repeated or missing constructors in a
nonempty match. Operation domains, including nonzero divisors, belong to
verification. No dynamic behavior is assigned here to an unverified
`x div 0` or to an evaluation order.
<!-- status: definition -->

## Typing rules

r[types.operator.unary] spec::types::unary_type?
Unary minus takes and returns integers; `not` takes and returns Booleans.
<!-- status: definition -->

r[types.operator.binary] spec::types::binary_type?
Arithmetic takes integers and returns an integer; integer comparisons return
a Boolean. Boolean operators take and return Booleans. Equality and
inequality take two operands of the same type and return a Boolean.
<!-- status: definition -->

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
    else left = right and result = Ty::Boolean
```

r[types.expression.boolean] spec::types::boolean_rule?
With no premises, `Σ; Γ ⊢ b : Boolean`.
<!-- status: definition -->

```fren
pub fn boolean_rule?(ty: Ty) := ty = Ty::Boolean
```

r[types.expression.integer] spec::types::integer_rule?
With no premises, `Σ; Γ ⊢ n : Integer`.
<!-- status: definition -->

```fren
pub fn integer_rule?(ty: Ty) := ty = Ty::Integer
```

r[types.expression.local] spec::types::local_rule?
If `Γ(i) = τ`, then `Σ; Γ ⊢ #i : τ`.
<!-- status: definition -->

```fren
pub fn local_rule?(context: Context, level: Int, ty: Ty) :=
    lookup(context, level) = Option::Some(ty)
```

r[types.expression.constructor] spec::types::constructor_rule?
If `Σ(c)` is a constructor of a, then `Σ; Γ ⊢ c : Nominal(a)`.
<!-- status: definition -->

```fren
pub fn constructor_rule?(symbols: Symbols, item: ItemId, ty: Ty) := match entry(symbols, item) {
    Option::Some(ItemKind::Constructor(owner)) => ty = Ty::Nominal(owner),
    _ => false,
}
```

r[types.expression.unary] spec::types::unary_rule?
If `Σ; Γ ⊢ e : σ` and `unary_type?(⊖, σ, τ)`, then `Σ; Γ ⊢ ⊖ e : τ`.
<!-- status: definition -->

```fren
pub fn unary_rule?(context: Context, op: UnaryOp, operand: Typing, ty: Ty) :=
    operand.context = context
    and unary_type?(op, operand.ty, ty)
```

r[types.expression.binary] spec::types::binary_rule?
If `Σ; Γ ⊢ l : σ`, `Σ; Γ ⊢ r : υ` and `binary_type?(⊕, σ, υ, τ)`, then
`Σ; Γ ⊢ l ⊕ r : τ`.
<!-- status: definition -->

```fren
pub fn binary_rule?(context: Context, op: BinaryOp, left: Typing, right: Typing, ty: Ty) :=
    left.context = context
    and right.context = context
    and binary_type?(op, left.ty, right.ty, ty)
```

r[types.expression.call] spec::types::{call_rule?, in_context?, argument_types?}
If `Σ(f)` is a function with parameters `·, σ₀, …, σₙ₋₁` and result τ,
and `Σ; Γ ⊢ aₖ : σₖ` for each k < n, then `Σ; Γ ⊢ f(a₀, …, aₙ₋₁) : τ`. The
arguments and parameters correspond level by level, so their numbers are
equal.
<!-- status: definition -->

```fren
pub fn in_context?(children: Snoc<Typing>, context: Context) := match children {
    Empty => true,
    Extend(earlier, child) => child.context = context and in_context?(earlier, context),
}

pub fn argument_types?(args: Snoc<Typing>, parameters: Context) := match args, parameters {
    Empty, Empty => true,
    Extend(earlier, arg), Extend(earlier_parameters, parameter) =>
        arg.ty = parameter and argument_types?(earlier, earlier_parameters),
    _, _ => false,
}

pub fn call_rule?(symbols: Symbols, context: Context, item: ItemId, args: Snoc<Typing>, ty: Ty) :=
    match entry(symbols, item) {
        Option::Some(ItemKind::Function(signature)) =>
            ty = signature.result
            and in_context?(args, context)
            and argument_types?(args, signature.parameters),
        _ => false,
    }
```

r[types.expression.let] spec::types::let_rule?
If `Σ; Γ ⊢ v : σ`, the annotation, if any, is σ, and `Σ; Γ, σ ⊢ b : τ`,
then `Σ; Γ ⊢ let[: σ] v in b : τ`. The new binder has level `|Γ|` in b and
is absent from v's context.
<!-- status: definition -->

```fren
pub fn annotation_matches?(annotation: Option<Ty>, ty: Ty) := match annotation {
    Option::Some(written) => written = ty,
    Option::None => true,
}

pub fn let_rule?(context: Context, annotation: Option<Ty>, value: Typing, body: Typing, ty: Ty) :=
    value.context = context
    and annotation_matches?(annotation, value.ty)
    and body.context = Extend(context, value.ty)
    and body.ty = ty
```

r[types.expression.if] spec::types::if_rule?
If `Σ; Γ ⊢ c : Boolean`, `Σ; Γ ⊢ t : τ` and `Σ; Γ ⊢ e : τ`,
then `Σ; Γ ⊢ if c then t else e : τ`.
<!-- status: definition -->

```fren
pub fn if_rule?(
    context: Context,
    condition: Typing,
    then_branch: Typing,
    else_branch: Typing,
    ty: Ty
) :=
    condition.context = context
    and condition.ty = Ty::Boolean
    and then_branch.context = context
    and then_branch.ty = ty
    and else_branch.context = context
    and else_branch.ty = ty
```

r[types.expression.match] spec::types::{match_rule?, bodies?, patterns?}
If `Σ; Γ ⊢ s : Nominal(a)`, the arms are nonempty, every pattern's `Σ`
entry is a constructor of a, and `Σ; Γ ⊢ b : τ` for each arm body b, then
`Σ; Γ ⊢ match s { … } : τ`. No arm extends Γ.
<!-- status: definition -->

```fren
pub fn bodies?(arms: Snoc<ArmF<Typing>>, context: Context, ty: Ty) := match arms {
    Empty => true,
    Extend(earlier, arm) =>
        arm.body.context = context and arm.body.ty = ty and bodies?(earlier, context, ty),
}

pub fn patterns?(symbols: Symbols, arms: Snoc<ArmF<Typing>>, owner: ItemId) := match arms {
    Empty => true,
    Extend(earlier, arm) =>
        entry(symbols, arm.constructor) = Option::Some(ItemKind::Constructor(owner))
        and patterns?(symbols, earlier, owner),
}

pub fn match_rule?(
    symbols: Symbols,
    context: Context,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
    ty: Ty
) :=
    scrutinee.context = context
    and match scrutinee.ty, arms {
        Ty::Nominal(owner), Extend(earlier, last) =>
            last.body.context = context
            and last.body.ty = ty
            and entry(symbols, last.constructor) = Option::Some(ItemKind::Constructor(owner))
            and bodies?(earlier, context, ty)
            and patterns?(symbols, earlier, owner),
        _, _ => false,
    }
```

The one-layer judgment dispatches on the form:

```fren
pub fn rule?(symbols: Symbols, context: Context, form: ExprF<Typing>, ty: Ty) := match form {
    ExprF::BooleanLiteral(_) => boolean_rule?(ty),
    ExprF::IntegerLiteral(_) => integer_rule?(ty),
    ExprF::Local(level) => local_rule?(context, level, ty),
    ExprF::Constructor(item) => constructor_rule?(symbols, item, ty),
    ExprF::Unary(op, operand) => unary_rule?(context, op, operand, ty),
    ExprF::Binary(op, left, right) => binary_rule?(context, op, left, right, ty),
    ExprF::Call(item, args) => call_rule?(symbols, context, item, args, ty),
    ExprF::Let(annotation, value, body) => let_rule?(context, annotation, value, body, ty),
    ExprF::Conditional(condition, then_branch, else_branch) =>
        if_rule?(context, condition, then_branch, else_branch, ty),
    ExprF::Match(scrutinee, arms) => match_rule?(symbols, context, scrutinee, arms, ty),
}
```

## Derivations

r[types.derivation.table] spec::types::{Row, typing_at, annotate, rows_valid?, derivation?}
A derivation is given as a snoc sequence of rows in postorder. A row's form
names each child by the level of an earlier row; a level that names no
earlier row fails. Every row satisfies `rule?`, with each child replaced by
that earlier row's recorded context and type. The newest row is the root;
all rows, including any extra rows, are checked. Unfolding shared rows
produces a finite tree, and sharing requires identical contexts and types.
A table records forms, contexts and types; which source occurrences it
represents is retained separately.
<!-- status: definition -->

```fren
pub type Form := ExprF<Int>
pub type Arm := ArmF<Int>
pub struct Row { form: Form, context: Context, ty: Ty }

pub fn typing_at(rows: Snoc<Row>, position: Int): Option<Typing> := match rows {
    Empty => Option::None,
    Extend(earlier, row) =>
        if position = length(earlier)
        then Option::Some(Typing { context := row.context, ty := row.ty })
        else typing_at(earlier, position),
}

pub fn annotate_arguments(rows: Snoc<Row>, args: Snoc<Int>): Option<Snoc<Typing>> := match args {
    Empty => Option::Some(Empty),
    Extend(earlier, arg) => match annotate_arguments(rows, earlier), typing_at(rows, arg) {
        Option::Some(typed), Option::Some(child) => Option::Some(Extend(typed, child)),
        _, _ => Option::None,
    },
}

pub fn annotate_arms(rows: Snoc<Row>, arms: Snoc<Arm>): Option<Snoc<ArmF<Typing>>> := match arms {
    Empty => Option::Some(Empty),
    Extend(earlier, arm) => match annotate_arms(rows, earlier), typing_at(rows, arm.body) {
        Option::Some(typed), Option::Some(body) =>
            Option::Some(Extend(typed, ArmF { constructor := arm.constructor, body })),
        _, _ => Option::None,
    },
}

pub fn annotate(rows: Snoc<Row>, form: Form): Option<ExprF<Typing>> := match form {
    ExprF::BooleanLiteral(value?) => Option::Some(ExprF::BooleanLiteral(value?)),
    ExprF::IntegerLiteral(value) => Option::Some(ExprF::IntegerLiteral(value)),
    ExprF::Local(level) => Option::Some(ExprF::Local(level)),
    ExprF::Constructor(item) => Option::Some(ExprF::Constructor(item)),
    ExprF::Unary(op, operand) => match typing_at(rows, operand) {
        Option::Some(child) => Option::Some(ExprF::Unary(op, child)),
        Option::None => Option::None,
    },
    ExprF::Binary(op, left, right) => match typing_at(rows, left), typing_at(rows, right) {
        Option::Some(l), Option::Some(r) => Option::Some(ExprF::Binary(op, l, r)),
        _, _ => Option::None,
    },
    ExprF::Call(item, args) => match annotate_arguments(rows, args) {
        Option::Some(typed) => Option::Some(ExprF::Call(item, typed)),
        Option::None => Option::None,
    },
    ExprF::Let(annotation, value, body) => match typing_at(rows, value), typing_at(rows, body) {
        Option::Some(v), Option::Some(b) => Option::Some(ExprF::Let(annotation, v, b)),
        _, _ => Option::None,
    },
    ExprF::Conditional(condition, then_branch, else_branch) =>
        match typing_at(rows, condition), typing_at(rows, then_branch), typing_at(
            rows,
            else_branch
        ) {
            Option::Some(c), Option::Some(t), Option::Some(e) =>
                Option::Some(ExprF::Conditional(c, t, e)),
            _, _, _ => Option::None,
        },
    ExprF::Match(scrutinee, arms) => match typing_at(rows, scrutinee), annotate_arms(rows, arms) {
        Option::Some(typed), Option::Some(typed_arms) =>
            Option::Some(ExprF::Match(typed, typed_arms)),
        _, _ => Option::None,
    },
}

pub fn rows_valid?(symbols: Symbols, rows: Snoc<Row>) := match rows {
    Empty => true,
    Extend(earlier, row) =>
        rows_valid?(symbols, earlier) and match annotate(earlier, row.form) {
            Option::Some(form) => rule?(symbols, row.context, form, row.ty),
            Option::None => false,
        },
}

pub fn derivation?(symbols: Symbols, rows: Snoc<Row>, context: Context, ty: Ty) :=
    symbols_ok?(symbols) and rows_valid?(symbols, rows) and match rows {
        Empty => false,
        Extend(_, root) => root.context = context and root.ty = ty,
    }
```

## Declarations and programs

r[types.context.parameters]
A declaration's body context is its parameter types in written order: the
first parameter has level 0. A function's signature records that context.
<!-- status: definition -->

r[types.declaration.result] spec::types::{Declaration, declaration_ok?}
A function body has a derivation at its declared result type in its
parameter context.
<!-- status: definition -->

r[types.declaration.conditions] spec::types::declaration_ok?
Each assume or expect body has a derivation at Boolean in its parameter
context, whose types are well formed.
<!-- status: definition -->

r[types.program.typing] spec::types::{declarations_ok?, bodies_of, functions_defined?, program_ok?}
A Core program is well typed when its symbol environment is well formed,
every declaration is well typed in that one environment, and every function
that the environment binds has exactly one body among the declarations.
<!-- status: definition -->

r[types.program.source]
A source program is well typed exactly when its translation into a Core
program is. The derived-forms chapter, not yet written, is to define that
translation, including which rows of each body's table represent which
source occurrences.
<!-- status: open -->

```fren
pub enum Declaration { Function(ItemId, Snoc<Row>), Condition(Context, Snoc<Row>) }

pub fn declaration_ok?(symbols: Symbols, declaration: Declaration) := match declaration {
    Declaration::Function(item, body) => match entry(symbols, item) {
        Option::Some(ItemKind::Function(signature)) =>
            derivation?(symbols, body, signature.parameters, signature.result),
        _ => false,
    },
    Declaration::Condition(parameters, body) =>
        context_ok?(symbols, parameters) and derivation?(symbols, body, parameters, Ty::Boolean),
}

pub fn declarations_ok?(symbols: Symbols, declarations: Snoc<Declaration>) := match declarations {
    Empty => true,
    Extend(earlier, declaration) =>
        declaration_ok?(symbols, declaration) and declarations_ok?(symbols, earlier),
}

pub fn bodies_of(declarations: Snoc<Declaration>, item: ItemId): Int := match declarations {
    Empty => 0,
    Extend(earlier, declaration) =>
        bodies_of(earlier, item) + match declaration {
            Declaration::Function(name, _) => if name = item then 1 else 0,
            Declaration::Condition(_, _) => 0,
        },
}

pub fn functions_defined?(bindings: Symbols, declarations: Snoc<Declaration>) := match bindings {
    Empty => true,
    Extend(earlier, binding) =>
        (not binding.kind is ItemKind::Function(_) or bodies_of(declarations, binding.item) = 1)
        and functions_defined?(earlier, declarations),
}

pub fn program_ok?(symbols: Symbols, declarations: Snoc<Declaration>) :=
    symbols_ok?(symbols)
    and declarations_ok?(symbols, declarations)
    and functions_defined?(symbols, declarations)
```

## Properties of typing

Each family of properties is one rule, checked by one expectation with a
named claim per form or, where it needs induction over a table, by a
theorem in the chapter's wrapper.

r[types.expression.values] spec::types::value_inversion::{boolean, integer, local_level, constructor, constructor_owner}
Inversion for leaves: a typed literal has its literal's type, a typed local
has its context entry's type, and a typed constructor's entry is a
constructor whose owner is the type.
<!-- status: smt -->

r[types.expression.items] spec::types::item_inversion::{constructor, call, call_result, match_scrutinee}
Only constructor items are values and only function items are callable: a
typed constructor's entry is a constructor, a typed call's entry is a
function whose result is the type, and a typed match's scrutinee is nominal.
<!-- status: smt -->

```fren
expect value_inversion(
    symbols: Symbols,
    context: Context,
    value?,
    number: Int,
    level: Int,
    item: ItemId,
    owner: ItemId,
    ty: Ty,
) {
    expect boolean: when rule?(symbols, context, ExprF::BooleanLiteral(value?), ty), ty = Ty::Boolean
    expect integer: when rule?(symbols, context, ExprF::IntegerLiteral(number), ty), ty = Ty::Integer
    expect local_level: when rule?(symbols, context, ExprF::Local(level), ty),
        lookup(context, level) = Option::Some(ty) and 0 <= level < length(context)
    expect constructor: when rule?(symbols, context, ExprF::Constructor(item), ty), ty is Ty::Nominal(_)
    expect constructor_owner: when rule?(
        symbols,
        context,
        ExprF::Constructor(item),
        Ty::Nominal(owner)
    ),
        entry(symbols, item) = Option::Some(ItemKind::Constructor(owner))
}

expect item_inversion(
    symbols: Symbols,
    context: Context,
    item: ItemId,
    args: Snoc<Typing>,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
    signature: Signature,
    ty: Ty,
) {
    expect constructor: when rule?(symbols, context, ExprF::Constructor(item), ty),
        entry(symbols, item) is Option::Some(ItemKind::Constructor(_))
    expect call: when rule?(symbols, context, ExprF::Call(item, args), ty),
        entry(symbols, item) is Option::Some(ItemKind::Function(_))
    expect call_result: when rule?(symbols, context, ExprF::Call(item, args), ty)
        and entry(symbols, item) = Option::Some(ItemKind::Function(signature)), signature.result = ty
    expect match_scrutinee: when rule?(symbols, context, ExprF::Match(scrutinee, arms), ty),
        scrutinee.ty is Ty::Nominal(_) and arms != Empty
}
```

r[types.layer.operators] spec::types::operator_unique::{unary, binary}
Each unary or binary operator has at most one result type for fixed operand
types.
<!-- status: smt -->

r[types.layer.determinism] spec::types::layer_unique::{boolean, integer, local_level, constructor, unary, binary, call, let_expression, conditional, match_expression}
For fixed Σ, Γ and child typings, a layer of every form has at most one
type: if it satisfies its rule at τ and at υ, then τ = υ.
<!-- status: smt -->

r[types.layer.context] spec::types::layer_context::{unary, binary, call, let_expression, conditional, match_expression}
Each child's context is fixed by its position: every ordinary child uses Γ,
the body of a let uses exactly `Γ, σ` for its value's type σ, and match arms
introduce no binder.
<!-- status: smt -->

r[types.layer.each] spec::types::children_each::{argument, arm_body}
The argument at every level of a call uses Γ, and the arm body at every
level of a match uses Γ and has the match's type. That each argument has
its parameter's type is `argument_types?` itself.
<!-- status: smt -->

r[types.layer.call-arity]
If `argument_types?(args, Δ)`, then `|args| = |Δ|`.
<!-- status: lean Spec.Language.Types.argument_types_length -->

```fren
expect operator_unique(unary_op: UnaryOp, op: BinaryOp, left: Ty, right: Ty, a: Ty, b: Ty) {
    expect unary: when unary_type?(unary_op, left, a) and unary_type?(unary_op, left, b), a = b
    expect binary: when binary_type?(op, left, right, a) and binary_type?(op, left, right, b), a = b
}

expect layer_unique(
    symbols: Symbols,
    context: Context,
    value?,
    number: Int,
    level: Int,
    item: ItemId,
    unary_op: UnaryOp,
    op: BinaryOp,
    first: Typing,
    second: Typing,
    third: Typing,
    annotation: Option<Ty>,
    args: Snoc<Typing>,
    arms: Snoc<ArmF<Typing>>,
    a: Ty,
    b: Ty,
) {
    expect boolean: when rule?(symbols, context, ExprF::BooleanLiteral(value?), a)
        and rule?(symbols, context, ExprF::BooleanLiteral(value?), b), a = b
    expect integer: when rule?(symbols, context, ExprF::IntegerLiteral(number), a)
        and rule?(symbols, context, ExprF::IntegerLiteral(number), b), a = b
    expect local_level: when rule?(symbols, context, ExprF::Local(level), a)
        and rule?(symbols, context, ExprF::Local(level), b), a = b
    expect constructor: when rule?(symbols, context, ExprF::Constructor(item), a)
        and rule?(symbols, context, ExprF::Constructor(item), b), a = b
    expect unary: when rule?(symbols, context, ExprF::Unary(unary_op, first), a)
        and rule?(symbols, context, ExprF::Unary(unary_op, first), b), a = b
    expect binary: when rule?(symbols, context, ExprF::Binary(op, first, second), a)
        and rule?(symbols, context, ExprF::Binary(op, first, second), b), a = b
    expect call: when rule?(symbols, context, ExprF::Call(item, args), a)
        and rule?(symbols, context, ExprF::Call(item, args), b), a = b
    expect let_expression: when rule?(symbols, context, ExprF::Let(annotation, first, second), a)
        and rule?(symbols, context, ExprF::Let(annotation, first, second), b), a = b
    expect conditional: when rule?(
        symbols,
        context,
        ExprF::Conditional(first, second, third),
        a
    )
        and rule?(
            symbols,
            context,
            ExprF::Conditional(first, second, third),
            b
        ), a = b
    expect match_expression: when rule?(symbols, context, ExprF::Match(first, arms), a)
        and rule?(symbols, context, ExprF::Match(first, arms), b), a = b
}

expect layer_context(
    symbols: Symbols,
    context: Context,
    item: ItemId,
    unary_op: UnaryOp,
    op: BinaryOp,
    first: Typing,
    second: Typing,
    third: Typing,
    annotation: Option<Ty>,
    args: Snoc<Typing>,
    arms: Snoc<ArmF<Typing>>,
    ty: Ty,
) {
    expect unary: when rule?(symbols, context, ExprF::Unary(unary_op, first), ty), first.context = context
    expect binary: when rule?(symbols, context, ExprF::Binary(op, first, second), ty),
        first.context = context and second.context = context
    expect call: when rule?(symbols, context, ExprF::Call(item, args), ty), in_context?(args, context)
    expect let_expression: when rule?(symbols, context, ExprF::Let(annotation, first, second), ty),
        first.context = context and second.context = Extend(context, first.ty) and second.ty = ty
    expect conditional: when rule?(
        symbols,
        context,
        ExprF::Conditional(first, second, third),
        ty
    ),
        first.context = context and second.context = context and third.context = context
    expect match_expression: when rule?(symbols, context, ExprF::Match(first, arms), ty),
        first.context = context and bodies?(arms, context, ty)
}

expect children_each(
    args: Snoc<Typing>,
    arms: Snoc<ArmF<Typing>>,
    context: Context,
    ty: Ty,
    level: Int,
    arg: Typing,
    arm: ArmF<Typing>,
) {
    expect argument: when in_context?(args, context) and lookup(args, level) = Option::Some(arg),
        arg.context = context
    expect arm_body: when bodies?(arms, context, ty) and lookup(arms, level) = Option::Some(arm),
        arm.body.context = context and arm.body.ty = ty
}
```

r[types.derivation.scoped]
Every local of a valid table is in scope: if a row `#i` has context Γ, then
`0 ≤ i < |Γ|`.
<!-- status: lean Spec.Language.Types.table_scoped -->

r[types.derivation.unique] spec::types::same_shape?
Typing is deterministic for a table: two valid tables with the same forms
and contexts, row by row, have the same types row by row.
<!-- status: lean Spec.Language.Types.table_unique -->

r[types.derivation.unique-expression]
Typing is deterministic for an expression: two valid tables that represent
the same expression, with any sharing of rows and any extra rows, give its
root the same type.
<!-- status: open -->

```fren
pub fn same_shape?(left: Snoc<Row>, right: Snoc<Row>) := match left, right {
    Empty, Empty => true,
    Extend(left_earlier, l), Extend(right_earlier, r) =>
        l.form = r.form and l.context = r.context and same_shape?(left_earlier, right_earlier),
    _, _ => false,
}
```

r[types.derivation.weakening] spec::types::{shift, insert_type, weaken, long_enough?}
Typing is preserved by inserting a type at level n into every row's context
and adding one to every local level of at least n, provided `0 ≤ n` and
every row's context has at least n entries. With n = |Γ|, this extends Γ by a fresh
entry, leaves levels below |Γ| unchanged, and renumbers the locals bound
within the expression.
<!-- status: open -->

r[types.derivation.weakening-lookup]
The step for locals holds: if `0 ≤ n ≤ |Γ|`, the shifted level of i in Γ
with σ inserted at level n holds `Γ(i)`, and level n holds σ.
<!-- status: lean Spec.Language.Types.lookup_shift -->

```fren
pub fn shift(level: Int, cutoff: Int): Int := if level >= cutoff then level + 1 else level

pub fn insert_type(context: Context, cutoff: Int, extra: Ty): Context := match context {
    Empty => if cutoff = 0 then Extend(Empty, extra) else Empty,
    Extend(earlier, ty) =>
        if cutoff = length(earlier) + 1 then Extend(context, extra)
        else Extend(insert_type(earlier, cutoff, extra), ty),
}

pub fn shift_form(form: Form, cutoff: Int): Form := match form {
    ExprF::Local(level) => ExprF::Local(shift(level, cutoff)),
    _ => form,
}

pub fn weaken(rows: Snoc<Row>, cutoff: Int, extra: Ty): Snoc<Row> := match rows {
    Empty => Empty,
    Extend(earlier, row) => Extend(
        weaken(earlier, cutoff, extra),
        Row {
            form := shift_form(row.form, cutoff),
            context := insert_type(row.context, cutoff, extra),
            ty := row.ty,
        }
    ),
}

pub fn long_enough?(rows: Snoc<Row>, cutoff: Int) := match rows {
    Empty => true,
    Extend(earlier, row) => 0 <= cutoff <= length(row.context) and long_enough?(earlier, cutoff),
}
```

r[types.safety]
Typing is sound for the dynamic semantics: in a well-typed, verified
program, evaluating a well-typed expression under values of its context's
types is defined and gives a value of its type, as the
[expressions chapter](Expressions.md#values-interpretation-and-mentioned-names)
defines evaluation.
<!-- status: open -->

## Surface elaboration

This section belongs to the derived-forms chapter, which will own it once
that chapter is written. It states how written annotations and binder names
become Core types; the Core itself has no names.

r[types.surface.annotation] spec::types::parameter_type?
A parameter's type is its written annotation. An omitted parameter
annotation denotes Boolean only when the parameter's name ends in `?`.
<!-- status: definition -->

r[types.surface.suffix] spec::types::{suffix_rule?, let_annotation?}
The *`?` suffix rule*: a parameter or let binder whose name ends in `?` has
type Boolean, including when it has an explicit annotation, which the suffix
does not overwrite; a written `b?: Int` fails typing. A let binder `x?`
without an annotation elaborates to a Core let annotated Boolean.
<!-- status: definition -->

```fren
pub fn suffix_rule?(question?, ty: Ty) := not question? or ty = Ty::Boolean

pub fn parameter_type?(written: Option<Ty>, question?, ty: Ty) :=
    suffix_rule?(question?, ty)
    and match written {
        Option::Some(annotation) => ty = annotation,
        Option::None => question?,
    }

pub fn let_annotation?(written: Option<Ty>, question?, core: Option<Ty>) := match written {
    Option::Some(annotation) => suffix_rule?(question?, annotation) and core = written,
    Option::None => core = (if question? then Option::Some(Ty::Boolean) else Option::None),
}
```

## Definitions for the Expressions chapter

The [expressions chapter](Expressions.md) owns the rules for these
definitions; they are declared here because that chapter builds on this
one.

r[types.value.owner] spec::types::{Value, value_type, value_valid?}
A nominal value records its enumeration owner and a constructor whose `Σ`
entry names that owner. Boolean and integer values have their built-in type.
<!-- status: definition -->

r[types.value.domain] spec::types::integer_domain?
Integer division and remainder require a nonzero divisor for verification.
This condition does not restrict their typing rule.
<!-- status: definition -->

r[types.value.examples] spec::types::{linear_meaning?, meaning_examples}
Checked examples of arithmetic meaning: `n + 1` is addition for every n,
`7 - 2` is not `-5`, `-9 div -2 = 5` and `-9 mod -2 = 1` are Euclidean, and
a zero divisor is outside the domain of division and remainder. These are
examples, not the general meaning, which the expressions chapter states.
<!-- status: smt -->

r[types.value.mentions] spec::types::{direct_item?, arm_mentions?}
A form directly mentions its constructor, its callee, or its match
patterns' constructors.
<!-- status: definition -->

```fren
pub enum Value { Boolean(Bool), Integer(Int), Nominal(ItemId, ItemId) }

pub fn value_type(value: Value): Ty := match value {
    Value::Boolean(_) => Ty::Boolean,
    Value::Integer(_) => Ty::Integer,
    Value::Nominal(owner, _) => Ty::Nominal(owner),
}

pub fn value_valid?(symbols: Symbols, value: Value) := match value {
    Value::Nominal(owner, item) =>
        entry(symbols, item) = Option::Some(ItemKind::Constructor(owner)),
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

pub fn arm_mentions?(arms: Snoc<Arm>, item: ItemId) := match arms {
    Empty => false,
    Extend(earlier, arm) => arm.constructor = item or arm_mentions?(earlier, item),
}

pub fn direct_item?(form: Form, item: ItemId) := match form {
    ExprF::Constructor(target) => item = target,
    ExprF::Call(target, _) => item = target,
    ExprF::Match(_, arms) => arm_mentions?(arms, item),
    _ => false,
}
```

## Worked derivations

r[types.examples.derivations] spec::types::{EXAMPLE_SYMBOLS, row, single}
Each example below checks a complete table, every row included, against the
rules, and is preceded by the Core judgment it shows in the notation above.
Rejected judgments fail at the premise they name. Further cases, one at
least for each rule, are checked in the chapter's wrapper.
<!-- status: lean Spec.Language.Types.worked_examples -->

The examples use an enumeration `M::Light` with constructors `Red` and
`Green`, an enumeration `M::Signal` with constructor `Red`, and a function
`M::f` from Integer to Integer.

```fren
pub const LIGHT: ItemId := ["M", "Light"]
pub const LIGHT_RED: ItemId := ["M", "Light", "Red"]
pub const LIGHT_GREEN: ItemId := ["M", "Light", "Green"]
pub const SIGNAL: ItemId := ["M", "Signal"]
pub const SIGNAL_RED: ItemId := ["M", "Signal", "Red"]
pub const F: ItemId := ["M", "f"]

pub fn binding(item: ItemId, kind: ItemKind): Entry := Entry { item, kind }

pub const EXAMPLE_SYMBOLS: Symbols := Extend(
    Extend(
        Extend(
            Extend(
                Extend(
                    Extend(
                        Empty,
                        binding(
                            LIGHT,
                            ItemKind::Enumeration(Extend(Extend(Empty, LIGHT_RED), LIGHT_GREEN))
                        )
                    ),
                    binding(LIGHT_RED, ItemKind::Constructor(LIGHT))
                ),
                binding(LIGHT_GREEN, ItemKind::Constructor(LIGHT))
            ),
            binding(SIGNAL, ItemKind::Enumeration(Extend(Empty, SIGNAL_RED)))
        ),
        binding(SIGNAL_RED, ItemKind::Constructor(SIGNAL))
    ),
    binding(
        F,
        ItemKind::Function(
            Signature {
                parameters := Extend(Empty, Ty::Integer),
                result := Ty::Integer,
            }
        )
    )
)

pub fn row(form: Form, context: Context, ty: Ty): Row := Row { form, context, ty }

pub fn single(only: Row): Snoc<Row> := Extend(Empty, only)

pub const BOOLEAN_INTEGER: Context := Extend(Extend(Empty, Ty::Boolean), Ty::Integer)

pub const WELL_FORMED_EXAMPLE: Bool := symbols_ok?(EXAMPLE_SYMBOLS)

-- Σ; ·, Boolean, Integer ⊢ #0 : Boolean, and not at Integer.
pub const OLDEST_LEVEL_EXAMPLE: Bool :=
    derivation?(
        EXAMPLE_SYMBOLS,
        single(row(ExprF::Local(0), BOOLEAN_INTEGER, Ty::Boolean)),
        BOOLEAN_INTEGER,
        Ty::Boolean
    )
    and not derivation?(
        EXAMPLE_SYMBOLS,
        single(row(ExprF::Local(0), BOOLEAN_INTEGER, Ty::Integer)),
        BOOLEAN_INTEGER,
        Ty::Integer
    )

-- Σ; · ⊢ let: Integer 1 in #0 : Integer. The body's context is ·, Integer.
pub const LET_EXAMPLE: Bool := derivation?(
    EXAMPLE_SYMBOLS,
    Extend(
        Extend(
            single(row(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
            row(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
        ),
        row(
            ExprF::Let(Option::Some(Ty::Integer), 0, 1),
            Empty,
            Ty::Integer
        )
    ),
    Empty,
    Ty::Integer
)

-- Rejected: Σ; · ⊢ let #0 in #0 : Integer. The value's context is ·, where #0 has no entry.
pub const LET_VALUE_SCOPE_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            Extend(
                single(row(ExprF::Local(0), Empty, Ty::Integer)),
                row(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
            ),
            row(ExprF::Let(Option::None, 0, 1), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

-- Rejected: Σ; · ⊢ if true then 1 else false : Integer. Both branches are checked.
pub const BOTH_BRANCHES_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            Extend(
                Extend(
                    single(row(ExprF::BooleanLiteral(true), Empty, Ty::Boolean)),
                    row(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
                ),
                row(ExprF::BooleanLiteral(false), Empty, Ty::Boolean)
            ),
            row(ExprF::Conditional(0, 1, 2), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

-- Σ; · ⊢ match M::Light::Red { M::Light::Red ⇒ 1 | M::Light::Green ⇒ 2 } : Integer.
pub const MATCH_EXAMPLE: Bool := derivation?(
    EXAMPLE_SYMBOLS,
    Extend(
        Extend(
            Extend(
                single(
                    row(ExprF::Constructor(LIGHT_RED), Empty, Ty::Nominal(LIGHT))
                ),
                row(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
            ),
            row(ExprF::IntegerLiteral(2), Empty, Ty::Integer)
        ),
        row(
            ExprF::Match(
                0,
                Extend(
                    Extend(Empty, ArmF { constructor := LIGHT_RED, body := 1 }),
                    ArmF { constructor := LIGHT_GREEN, body := 2 }
                )
            ),
            Empty,
            Ty::Integer
        )
    ),
    Empty,
    Ty::Integer
)

-- Rejected: Σ; · ⊢ match M::Light::Red { M::Signal::Red ⇒ 1 } : Integer. The pattern's owner is M::Signal.
pub const MATCH_OWNER_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            Extend(
                single(
                    row(ExprF::Constructor(LIGHT_RED), Empty, Ty::Nominal(LIGHT))
                ),
                row(ExprF::IntegerLiteral(1), Empty, Ty::Integer)
            ),
            row(
                ExprF::Match(
                    0,
                    Extend(Empty, ArmF { constructor := SIGNAL_RED, body := 1 })
                ),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

-- Σ; · ⊢ M::f(1) : Integer, and rejected with two arguments, M::f(1, 1).
pub const CALL_EXAMPLE: Bool :=
    derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            single(row(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
            row(ExprF::Call(F, Extend(Empty, 0)), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )
    and not derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            single(row(ExprF::IntegerLiteral(1), Empty, Ty::Integer)),
            row(
                ExprF::Call(F, Extend(Extend(Empty, 0), 0)),
                Empty,
                Ty::Integer
            )
        ),
        Empty,
        Ty::Integer
    )

-- Rejected: Σ; · ⊢ -#0 : Integer, whose operand row has context ·, Integer.
pub const CONTEXT_ALIGNMENT_EXAMPLE: Bool :=
    not derivation?(
        EXAMPLE_SYMBOLS,
        Extend(
            single(
                row(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
            ),
            row(ExprF::Unary(UnaryOp::Neg, 0), Empty, Ty::Integer)
        ),
        Empty,
        Ty::Integer
    )

-- A program: the function M::f with body #0 + 1 in its parameter context ·, Integer.
pub const PROGRAM_EXAMPLE: Bool := program_ok?(
    EXAMPLE_SYMBOLS,
    Extend(
        Empty,
        Declaration::Function(
            F,
            Extend(
                Extend(
                    single(
                        row(ExprF::Local(0), Extend(Empty, Ty::Integer), Ty::Integer)
                    ),
                    row(
                        ExprF::IntegerLiteral(1),
                        Extend(Empty, Ty::Integer),
                        Ty::Integer
                    )
                ),
                row(
                    ExprF::Binary(BinaryOp::Add, 0, 1),
                    Extend(Empty, Ty::Integer),
                    Ty::Integer
                )
            )
        )
    )
)
```

r[types.examples.source]
Each source program below is checked by both of today's front ends, with
the diagnostic it expects. A typing failure is reported even when resolution
succeeds.
<!-- status: tested manualExamples -->

```fren example
--@ reference: types.examples.source
--@ reference: types.operator.binary
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := l + 1  --~ error: type mismatch: expected `Int`, found `bad::Light`
```

```fren example
--@ reference: types.examples.source
--@ reference: types.expression.let
pub mod bad

pub fn f(n: Int): Int := let b: Bool := n in 0  --~ error: the definition of `b` has type `Int`, not `Bool`
```

```fren example
--@ reference: types.examples.source
--@ reference: types.surface.suffix
pub mod bad

pub fn f(b?: Int): Int := b?  --~ error: `b?` ends in `?` but is not a `Bool`
```

```fren example
--@ reference: types.examples.source
--@ reference: types.expression.call
pub mod bad

pub fn g(n: Int): Int := n

pub fn f(n: Int): Int := g(n, n)  --~ error: `bad::g` takes 1 argument, but 2 were given
```

```fren example
--@ reference: types.examples.source
--@ reference: types.expression.if
pub mod bad

pub fn f(n: Int): Int := if n then 1 else 0  --~ error: type mismatch: expected `Bool`, found `Int`
```

```fren example
--@ reference: types.examples.source
--@ reference: types.expression.if
pub mod bad

pub fn f(b?): Int := if b? then 1 else false  --~ error: the branches of `if` have different types: `Int` and `Bool`
```

```fren example
--@ reference: types.examples.source
--@ reference: types.operator.binary
pub mod bad

pub enum Light { Red, Green }
pub enum Signal { Red, Green }

pub fn same?(l: Light, s: Signal) := l = s  --~ error: cannot compare `bad::Light` with `bad::Signal`
```

```fren example
--@ reference: types.examples.source
--@ reference: types.expression.match
pub mod bad

pub enum Light { Red, Green }

pub fn f(n: Int): Int := match n {
    Light::Red => 0,  --~ error: expected a pattern of `Int`, but this is a pattern of `bad::Light`
    Light::Green => 1,
}
```
