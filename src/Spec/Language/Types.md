# Core typing

Source programs are defined by translation into the Core, a small typed
language; the [THIR chapter](../Compiler/Thir.md) relates it to the
compiler's typed representation. Static semantics comprises resolution,
typing, and verification, including definedness. This chapter defines
typing; [resolution](NamesAndScope.md) supplies identities, and
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
A match has at least one arm.

The chapter's judgments, and the Fren definitions that state them:

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `Σ ⊢ τ ok` | τ is a well-formed type | `ty_ok?` |
| `Σ ⊢ Γ ok` | every type of Γ is well formed | `ctx_ok?` |
| `⊢ Σ ok` | Σ is a well-formed symbol environment | `symb_ok?` |
| `Σ; Γ ⊢ e : τ` | e has type τ in Γ | `derivation?`, with a table whose root unfolds to e |
| `Σ; Γ ⊢ l ▷ τ` | one layer l, its children already typed, has type τ | `rule?` |
| `Σ ⊢ d ok` | a declaration is well typed | `decl_ok?` |
| `⊢ (Σ, ds) ok` | a program is well typed | `prog_ok?` |

The typing rules are summarized below, in the notation of
[The Definition of Standard ML](https://smlfamily.github.io/sml97-defn.pdf).
`unary(⊖, σ) = τ` and `binary(⊕, σ, υ) = τ` are the operator tables of
`unary_type?` and `binary_type?`. The figure gives every rule of the
chapter; it is informative, and the numbered rules that follow are
normative.

```text
                                      Γ(i) = τ                   Σ(c) = constructor of a
  Σ; Γ ⊢ b : Boolean                  ─────────────              ───────────────────────
  Σ; Γ ⊢ n : Integer                  Σ; Γ ⊢ #i : τ              Σ; Γ ⊢ c : Nominal(a)

  Σ; Γ ⊢ e : σ   unary(⊖, σ) = τ      Σ; Γ ⊢ l : σ   Σ; Γ ⊢ r : υ   binary(⊕, σ, υ) = τ
  ──────────────────────────────      ─────────────────────────────────────────────────
  Σ; Γ ⊢ ⊖ e : τ                      Σ; Γ ⊢ l ⊕ r : τ

  Σ(f) = function with parameters σ₀, …, σₙ₋₁ and result τ    Σ; Γ ⊢ aₖ : σₖ  (each k < n)
  ─────────────────────────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ f(a₀, …, aₙ₋₁) : τ

  Σ; Γ ⊢ v : σ   (σ' = σ if annotated with σ')   Σ; Γ, σ ⊢ b : τ
  ──────────────────────────────────────────────────────────────
  Σ; Γ ⊢ let[: σ'] v in b : τ

  Σ; Γ ⊢ c : Boolean   Σ; Γ ⊢ t : τ   Σ; Γ ⊢ e : τ
  ────────────────────────────────────────────────
  Σ; Γ ⊢ if c then t else e : τ

  Σ; Γ ⊢ s : Nominal(a)   Σ(cₖ) = constructor of a   Σ; Γ ⊢ bₖ : τ  (each arm k)
  ────────────────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ match s { c₀ ⇒ b₀ | … | cₘ ⇒ bₘ } : τ

                                      Σ(a) = enumeration     Σ ⊢ Γ ok   Σ ⊢ τ ok
  Σ ⊢ Boolean ok   Σ ⊢ Integer ok     ──────────────────     ───────────────────     Σ ⊢ · ok
                                      Σ ⊢ Nominal(a) ok      Σ ⊢ Γ, τ ok

  each item bound once   every signature well formed   owners and constructors agree
  ─────────────────────────────────────────────────────────────────────────────────
  ⊢ Σ ok

  ⊢ Σ ok   Σ ⊢ Γ ok   a valid table, its contexts extending Γ, has a root Γ, τ that unfolds to e
  ─────────────────────────────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ e : τ

  Σ(f) = function with parameters Δ and result τ   Σ; Δ ⊢ b : τ       Σ; Δ ⊢ b : Boolean
  ─────────────────────────────────────────────────────────────       ──────────────────────────
  Σ ⊢ function f with body b ok                                       Σ ⊢ condition Δ. b ok

  ⊢ Σ ok   Σ ⊢ d ok (each declaration d)   each function of Σ has exactly one body
  ────────────────────────────────────────────────────────────────────────────────
  ⊢ (Σ, ds) ok
```

The one-layer judgment `Σ; Γ ⊢ l ▷ τ` checks one of the expression rules
above for l's form, with its children's typings given instead of derived.

## Semantic objects

r[types.object.identity] spec::types::{ItemId, Ty}
An *item identity* is the canonical sequence of enclosing module and item
names supplied by resolution. Value types are Boolean, mathematical integer, and nominal enumeration
types. Types are compared by equality, including every component of a
nominal identity.
<!-- status: definition -->

```fren
pub mod spec
pub mod spec::types

pub type ItemId := Seq<String>
pub enum Ty { Boolean, Integer, Nominal(ItemId) }
```

r[types.sequence.snoc] spec::types::{Snoc, length, lookup, one, two, three, four}
A *snoc sequence* is either empty, written `·`, or an earlier snoc sequence
extended by one newest entry x, written `xs, x`. Its length `|xs|` counts
its entries. The *level* of an entry is the number of entries before it, so
the oldest entry has level 0 and the newest has level `|xs| - 1`. `xs(i)`
is the entry at level i, defined exactly when `0 ≤ i < |xs|`. `one` to `four`
build sequences of one to four entries, oldest first.
<!-- status: definition -->

```fren
pub enum Snoc<T> { Empty, Extend(Snoc<T>, T) }

use self::Snoc::{Empty, Extend}

pub fn length<T>(xs: Snoc<T>): Nat := match xs {
    Empty => 0,
    Extend(earlier, _) => length(earlier) + 1,
}

pub fn lookup<T>(xs: Snoc<T>, level: Int): Option<T> := match xs {
    Empty => None,
    Extend(earlier, x) => if level = length(earlier) then Some(x) else lookup(earlier, level),
}

pub fn one<T>(a: T): Snoc<T> := Extend(Empty, a)
pub fn two<T>(a: T, b: T): Snoc<T> := Extend(one(a), b)
pub fn three<T>(a: T, b: T, c: T): Snoc<T> := Extend(two(a, b), c)
pub fn four<T>(a: T, b: T, c: T, d: T): Snoc<T> := Extend(three(a, b, c), d)
```

r[types.context.slots] spec::types::Context
A *context* Γ is a snoc sequence of value types. Extending Γ by τ produces
`Γ, τ`, whose new entry has level `|Γ|`. A local refers to its entry by level.
<!-- status: definition -->

r[types.context.bound] spec::types::lookup_bound
If `Γ(i) = τ`, then `0 ≤ i < |Γ|`.
<!-- status: smt -->

r[types.context.weakening] spec::types::lookup_weakening
Extension leaves every existing level unchanged: if `0 ≤ i < |Γ|`, then
`(Γ, σ)(i) = Γ(i)`, and `(Γ, σ)(|Γ|) = σ`.
<!-- status: smt -->

```fren
pub type Ctx := Snoc<Ty>

expect lookup_bound(ctx: Ctx, level: Int, ty: Ty) {
    expect below: when lookup(ctx, level) = Some(ty), 0 <= level < length(ctx)
}

expect lookup_weakening(ctx: Ctx, extra: Ty, level: Int) {
    expect older: when 0 <= level < length(ctx),
        lookup(Extend(ctx, extra), level) = lookup(ctx, level)
    expect newest: lookup(Extend(ctx, extra), length(ctx)) = Some(extra)
}
```

r[types.symbols.environment] spec::types::{Signature, ItemKind, Entry, Symbols, entry}
A *symbol environment* Σ binds item identities to entries. An entry is a
function signature, a constructor's owning enumeration, or an enumeration
with its constructors. A signature has the parameter types as a context, in
written order, and a result type. `Σ(x)` is the newest entry bound to x.
The environment is shared by every body of a program.
<!-- status: definition -->

r[types.symbols.well-formed] spec::types::{type_ok?, context_ok?, symbols_ok?}
A type is *well formed* in Σ, `Σ ⊢ τ ok`, when it is Boolean, Integer, or
`Nominal(a)` with `Σ(a)` an enumeration; a context is well formed when each
of its types is. Σ is well formed, `⊢ Σ ok`, when it binds each item once,
every signature's types are well formed, every constructor's owner is an
enumeration that lists it, and every enumeration lists distinct
constructors, each bound as a constructor of that enumeration.
<!-- status: definition -->

r[types.symbols.resolution]
The symbol environment that [resolution](NamesAndScope.md) produces for a
program is well formed; in particular, resolution rejects an item declared
twice.
<!-- status: open -->

```fren
pub struct Sig { params: Ctx, result: Ty }
pub enum ItemKind { Function(Sig), Constructor(ItemId), Enumeration(Snoc<ItemId>) }
pub struct Entry { item: ItemId, kind: ItemKind }
pub type Symb := Snoc<Entry>

pub fn entry(symb: Symb, item: ItemId): Option<ItemKind> := match symb {
    Empty => None,
    Extend(earlier, binding) =>
        if binding.item = item then Some(binding.kind) else entry(earlier, item),
}

pub fn ty_ok?(symb: Symb, ty: Ty) := match ty {
    Ty::Nominal(owner) => entry(symb, owner) is Some(ItemKind::Enumeration(_)),
    _ => true,
}

pub fn ctx_ok?(symb: Symb, ctx: Ctx) := match ctx {
    Empty => true,
    Extend(earlier, ty) => ty_ok?(symb, ty) and ctx_ok?(symb, earlier),
}

pub fn member?(items: Snoc<ItemId>, item: ItemId) := match items {
    Empty => false,
    Extend(earlier, other) => other = item or member?(earlier, item),
}

pub fn constructors_ok?(symb: Symb, constructors: Snoc<ItemId>, owner: ItemId) :=
    match constructors {
        Empty => true,
        Extend(earlier, constructor) =>
            entry(symb, constructor) = Some(ItemKind::Constructor(owner))
            and not member?(earlier, constructor)
            and constructors_ok?(symb, earlier, owner),
    }

pub fn binding_ok?(symb: Symb, binding: Entry) := match binding.kind {
    ItemKind::Function(sig) =>
        ctx_ok?(symb, sig.params) and ty_ok?(symb, sig.result),
    ItemKind::Constructor(owner) => match entry(symb, owner) {
        Some(ItemKind::Enumeration(constructors)) => member?(constructors, binding.item),
        _ => false,
    },
    ItemKind::Enumeration(constructors) => constructors_ok?(symb, constructors, binding.item),
}

pub fn bindings_ok?(symb: Symb, bindings: Symb) := match bindings {
    Empty => true,
    Extend(earlier, binding) =>
        entry(earlier, binding.item) = None
        and binding_ok?(symb, binding)
        and bindings_ok?(symb, earlier),
}

pub fn symb_ok?(symb: Symb) := bindings_ok?(symb, symb)
```

<a id="finite-expression-derivations"></a>

## Core expressions and layers

r[types.expression.syntax] spec::types::{ExprF, ArmF, UnaryOp, BinaryOp}
A Core expression is a finite tree whose nodes have the forms of `ExprF<E>`,
where E is the position of a child. A literal carries its value, and a let
carries the type annotation written on it, if any. A call's arguments and a
match's arms are snoc sequences in written order. An arm has a resolved
constructor pattern and a body, with no binder. Parentheses are concrete
syntax, removed before the Core, and have no form here.
<!-- status: definition -->

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
    If(E, E, E),
    Match(E, Snoc<ArmF<E>>),
}
```

r[types.expression.layer] spec::types::Typing
A *layer* is one form `ExprF<E>` whose children are E: each child's typing,
or the level of a row of a table. A *typing* records a context and a type.
<!-- status: definition -->

```fren
pub struct Typing { ctx: Ctx, ty: Ty }
```

r[types.judgment.layer] spec::types::rule?
The one-layer judgment `Σ; Γ ⊢ l ▷ τ` takes Σ, Γ, a layer `ExprF<Typing>`
whose child positions hold the children's typings, and τ. It checks exactly
the matching rule below.
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
pub fn local_rule?(ctx: Ctx, level: Int, ty: Ty) := lookup(ctx, level) = Some(ty)
```

r[types.expression.constructor] spec::types::constructor_rule?
If `Σ(c)` is a constructor of a, then `Σ; Γ ⊢ c : Nominal(a)`.
<!-- status: definition -->

```fren
pub fn constructor_rule?(symb: Symb, item: ItemId, ty: Ty) := match entry(symb, item) {
    Some(ItemKind::Constructor(owner)) => ty = Ty::Nominal(owner),
    _ => false,
}
```

r[types.expression.unary] spec::types::unary_rule?
If `Σ; Γ ⊢ e : σ` and `unary_type?(⊖, σ, τ)`, then `Σ; Γ ⊢ ⊖ e : τ`.
<!-- status: definition -->

```fren
pub fn unary_rule?(ctx: Ctx, op: UnaryOp, operand: Typing, ty: Ty) :=
    operand.ctx = ctx
    and unary_type?(op, operand.ty, ty)
```

r[types.expression.binary] spec::types::binary_rule?
If `Σ; Γ ⊢ l : σ`, `Σ; Γ ⊢ r : υ` and `binary_type?(⊕, σ, υ, τ)`, then
`Σ; Γ ⊢ l ⊕ r : τ`.
<!-- status: definition -->

```fren
pub fn binary_rule?(ctx: Ctx, op: BinaryOp, left: Typing, right: Typing, ty: Ty) :=
    left.ctx = ctx
    and right.ctx = ctx
    and binary_type?(op, left.ty, right.ty, ty)
```

r[types.expression.call] spec::types::{call_rule?, in_context?, argument_types?}
If `Σ(f)` is a function with parameters σ₀, …, σₙ₋₁ and result τ, and
`Σ; Γ ⊢ aₖ : σₖ` for each k < n, then `Σ; Γ ⊢ f(a₀, …, aₙ₋₁) : τ`.
`argument_types?` pairs the arguments and parameters level by level.
<!-- status: definition -->

```fren
pub fn in_context?(children: Snoc<Typing>, ctx: Ctx) := match children {
    Empty => true,
    Extend(earlier, child) => child.ctx = ctx and in_context?(earlier, ctx),
}

pub fn argument_types?(args: Snoc<Typing>, params: Ctx) := match args, params {
    Empty, Empty => true,
    Extend(earlier, arg), Extend(earlier_params, param) =>
        arg.ty = param and argument_types?(earlier, earlier_params),
    _, _ => false,
}

pub fn call_rule?(symb: Symb, ctx: Ctx, item: ItemId, args: Snoc<Typing>, ty: Ty) :=
    match entry(symb, item) {
        Some(ItemKind::Function(sig)) =>
            ty = sig.result
            and in_context?(args, ctx)
            and argument_types?(args, sig.params),
        _ => false,
    }
```

r[types.expression.let] spec::types::let_rule?
If `Σ; Γ ⊢ v : σ`, the annotation, if any, is σ, and `Σ; Γ, σ ⊢ b : τ`,
then `Σ; Γ ⊢ let[: σ] v in b : τ`.
<!-- status: definition -->

```fren
pub fn annotation_matches?(annotation: Option<Ty>, ty: Ty) := match annotation {
    Some(written) => written = ty,
    None => true,
}

pub fn let_rule?(ctx: Ctx, annotation: Option<Ty>, value: Typing, body: Typing, ty: Ty) :=
    value.ctx = ctx
    and annotation_matches?(annotation, value.ty)
    and body.ctx = Extend(ctx, value.ty)
    and body.ty = ty
```

r[types.expression.if] spec::types::if_rule?
If `Σ; Γ ⊢ c : Boolean`, `Σ; Γ ⊢ t : τ` and `Σ; Γ ⊢ e : τ`,
then `Σ; Γ ⊢ if c then t else e : τ`.
<!-- status: definition -->

```fren
pub fn if_rule?(
    ctx: Ctx,
    condition: Typing,
    then_branch: Typing,
    else_branch: Typing,
    ty: Ty
) :=
    condition.ctx = ctx
    and condition.ty = Ty::Boolean
    and then_branch.ctx = ctx
    and then_branch.ty = ty
    and else_branch.ctx = ctx
    and else_branch.ty = ty
```

r[types.expression.match] spec::types::{match_rule?, arm_bodies?, arm_patterns?}
If `Σ; Γ ⊢ s : Nominal(a)`, the arms are nonempty, every pattern's `Σ`
entry is a constructor of a, and `Σ; Γ ⊢ b : τ` for each arm body b, then
`Σ; Γ ⊢ match s { … } : τ`, each arm body typed in Γ itself.
<!-- status: definition -->

```fren
pub fn arm_bodies?(arms: Snoc<ArmF<Typing>>, ctx: Ctx, ty: Ty) := match arms {
    Empty => true,
    Extend(earlier, arm) =>
        arm.body.ctx = ctx and arm.body.ty = ty and arm_bodies?(earlier, ctx, ty),
}

pub fn arm_patterns?(symb: Symb, arms: Snoc<ArmF<Typing>>, owner: ItemId) := match arms {
    Empty => true,
    Extend(earlier, arm) =>
        entry(symb, arm.constructor) = Some(ItemKind::Constructor(owner))
        and arm_patterns?(symb, earlier, owner),
}

pub fn match_rule?(
    symb: Symb,
    ctx: Ctx,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
    ty: Ty
) :=
    scrutinee.ctx = ctx
    and arms != Empty
    and arm_bodies?(arms, ctx, ty)
    and match scrutinee.ty {
        Ty::Nominal(owner) => arm_patterns?(symb, arms, owner),
        _ => false,
    }
```

The one-layer judgment dispatches on the form:

```fren
pub fn rule?(symb: Symb, ctx: Ctx, form: ExprF<Typing>, ty: Ty) := match form {
    ExprF::BooleanLiteral(_) => boolean_rule?(ty),
    ExprF::IntegerLiteral(_) => integer_rule?(ty),
    ExprF::Local(level) => local_rule?(ctx, level, ty),
    ExprF::Constructor(item) => constructor_rule?(symb, item, ty),
    ExprF::Unary(op, operand) => unary_rule?(ctx, op, operand, ty),
    ExprF::Binary(op, left, right) => binary_rule?(ctx, op, left, right, ty),
    ExprF::Call(item, args) => call_rule?(symb, ctx, item, args, ty),
    ExprF::Let(annotation, value, body) => let_rule?(ctx, annotation, value, body, ty),
    ExprF::If(condition, then_branch, else_branch) =>
        if_rule?(ctx, condition, then_branch, else_branch, ty),
    ExprF::Match(scrutinee, arms) => match_rule?(symb, ctx, scrutinee, arms, ty),
}
```

## Derivations

r[types.derivation.table] spec::types::{Row, typing_at, annotate, rows_valid?}
A *derivation table* is a snoc sequence of rows. A row has a layer whose
children are the levels of earlier rows, a context and a type. A table is
valid in Σ when every row's context is well formed and every row satisfies
`rule?` with each child replaced by that earlier row's context and type; a
child level that names no earlier row fails. Every row is checked,
including rows that no other row uses.
<!-- status: definition -->

```fren
pub type Form := ExprF<Int>
pub type Arm := ArmF<Int>
pub struct Row { form: Form, ctx: Ctx, ty: Ty }

pub fn typing_at(rows: Snoc<Row>, position: Int): Option<Typing> := match lookup(rows, position) {
    Some(row) => Some(Typing { ctx := row.ctx, ty := row.ty }),
    None => None,
}

pub fn annotate_arguments(rows: Snoc<Row>, args: Snoc<Int>): Option<Snoc<Typing>> := match args {
    Empty => Some(Empty),
    Extend(earlier, arg) => match annotate_arguments(rows, earlier), typing_at(rows, arg) {
        Some(typed), Some(child) => Some(Extend(typed, child)),
        _, _ => None,
    },
}

pub fn annotate_arms(rows: Snoc<Row>, arms: Snoc<Arm>): Option<Snoc<ArmF<Typing>>> := match arms {
    Empty => Some(Empty),
    Extend(earlier, arm) => match annotate_arms(rows, earlier), typing_at(rows, arm.body) {
        Some(typed), Some(body) =>
            Some(Extend(typed, ArmF { constructor := arm.constructor, body })),
        _, _ => None,
    },
}

pub fn annotate(rows: Snoc<Row>, form: Form): Option<ExprF<Typing>> := match form {
    ExprF::BooleanLiteral(value?) => Some(ExprF::BooleanLiteral(value?)),
    ExprF::IntegerLiteral(value) => Some(ExprF::IntegerLiteral(value)),
    ExprF::Local(level) => Some(ExprF::Local(level)),
    ExprF::Constructor(item) => Some(ExprF::Constructor(item)),
    ExprF::Unary(op, operand) => match typing_at(rows, operand) {
        Some(child) => Some(ExprF::Unary(op, child)),
        None => None,
    },
    ExprF::Binary(op, left, right) => match typing_at(rows, left), typing_at(rows, right) {
        Some(l), Some(r) => Some(ExprF::Binary(op, l, r)),
        _, _ => None,
    },
    ExprF::Call(item, args) => match annotate_arguments(rows, args) {
        Some(typed) => Some(ExprF::Call(item, typed)),
        None => None,
    },
    ExprF::Let(annotation, value, body) => match typing_at(rows, value), typing_at(rows, body) {
        Some(v), Some(b) => Some(ExprF::Let(annotation, v, b)),
        _, _ => None,
    },
    ExprF::If(condition, then_branch, else_branch) =>
        match typing_at(rows, condition), typing_at(rows, then_branch), typing_at(
            rows,
            else_branch
        ) {
            Some(c), Some(t), Some(e) => Some(ExprF::If(c, t, e)),
            _, _, _ => None,
        },
    ExprF::Match(scrutinee, arms) => match typing_at(rows, scrutinee), annotate_arms(rows, arms) {
        Some(typed), Some(typed_arms) => Some(ExprF::Match(typed, typed_arms)),
        _, _ => None,
    },
}

pub fn rows_valid?(symb: Symb, rows: Snoc<Row>) := match rows {
    Empty => true,
    Extend(earlier, row) =>
        rows_valid?(symb, earlier)
        and ctx_ok?(symb, row.ctx)
        and match annotate(earlier, row.form) {
            Some(form) => rule?(symb, row.ctx, form, row.ty),
            None => false,
        },
}
```

r[types.derivation.unfolding]
A row *unfolds* to the expression whose root form is the row's layer, with
each child level replaced by the expression that the row at that level
unfolds to, and argument and arm sequences replaced element by element.
Every written child of the
expression is a row, including an unused let value, both branches of a
conditional and every arm body; several occurrences may share a row.
<!-- status: definition -->

r[types.judgment.typing] spec::types::{extends?, rows_extend?, derivation?}
`Σ; Γ ⊢ e : τ` holds when Σ and Γ are well formed and some valid table,
every row of which has a context that extends Γ, has a newest row, its
*root*, with context Γ and type τ that unfolds to e. A context *extends* Γ
when it is Γ or Γ followed by further entries. `derivation?` checks that a
table is valid in this way with such a root.
<!-- status: definition -->

```fren
pub fn extends?(ctx: Ctx, base: Ctx) :=
    ctx = base or match ctx {
        Empty => false,
        Extend(earlier, _) => extends?(earlier, base),
    }

pub fn rows_extend?(rows: Snoc<Row>, base: Ctx) := match rows {
    Empty => true,
    Extend(earlier, row) => extends?(row.ctx, base) and rows_extend?(earlier, base),
}

pub fn derivation?(symb: Symb, rows: Snoc<Row>, ctx: Ctx, ty: Ty) :=
    symb_ok?(symb)
    and ctx_ok?(symb, ctx)
    and rows_valid?(symb, rows)
    and rows_extend?(rows, ctx)
    and match rows {
        Empty => false,
        Extend(_, root) => root.ctx = ctx and root.ty = ty,
    }
```

r[types.judgment.separate]
Match coverage, the absence of recursive call cycles and operation domains,
including nonzero divisors, are not premises of typing. No dynamic behavior
is assigned here to an unverified division by zero or to an evaluation
order.
<!-- status: definition -->

r[types.judgment.coverage-separate] spec::types::coverage_separate::{repeated, omitted}
Typing does not depend on coverage: a typed match stays typed when its
newest arm is repeated, or dropped while another arm remains.
<!-- status: smt -->

```fren
expect coverage_separate(
    symb: Symb,
    ctx: Ctx,
    scrutinee: Typing,
    earlier: Snoc<ArmF<Typing>>,
    last: ArmF<Typing>,
    ty: Ty,
) {
    let typed? := rule?(
        symb,
        ctx,
        ExprF::Match(scrutinee, Extend(earlier, last)),
        ty
    )
    expect repeated: not typed?
        or rule?(
            symb,
            ctx,
            ExprF::Match(scrutinee, Extend(Extend(earlier, last), last)),
            ty
        )
    expect omitted: not typed? or earlier = Empty or rule?(symb, ctx, ExprF::Match(scrutinee, earlier), ty)
}
```

## Declarations and programs

r[types.context.parameters]
A declaration's body context is its parameter types in written order: the
first parameter has level 0. A function's signature records that context.
<!-- status: definition -->

r[types.declaration.result] spec::types::{Declaration, declaration_ok?}
A function body is typed at its declared result type in its parameter
context. A declaration carries the table whose root unfolds to its body.
<!-- status: definition -->

r[types.declaration.conditions] spec::types::declaration_ok?
Each assume or expect body is typed at Boolean in its parameter context.
<!-- status: definition -->

r[types.program.typing] spec::types::{declarations_ok?, bodies_of, functions_defined?, program_ok?}
A Core program is well typed when its symbol environment is well formed,
every declaration is well typed in that one environment, and every function
that the environment binds has exactly one body among the declarations.
<!-- status: definition -->

r[types.program.source]
A source program is well typed exactly when its translation into a Core
program is. The derived-forms chapter, not yet written, is to define that
translation.
<!-- status: definition -->

r[types.program.nonrecursive]
A Core program has no recursive call cycles: no function's body calls
itself, directly or through other functions. This is a static condition
separate from typing; the [THIR chapter](../Compiler/Thir.md) states its
check.
<!-- status: definition -->

```fren
pub enum Decl { Function(ItemId, Snoc<Row>), Condition(Ctx, Snoc<Row>) }

pub fn decl_ok?(symb: Symb, decl: Decl) := match decl {
    Decl::Function(item, body) => match entry(symb, item) {
        Some(ItemKind::Function(sig)) =>
            derivation?(symb, body, sig.params, sig.result),
        _ => false,
    },
    Decl::Condition(params, body) => derivation?(symb, body, params, Ty::Boolean),
}

pub fn decls_ok?(symb: Symb, decls: Snoc<Decl>) := match decls {
    Empty => true,
    Extend(earlier, decl) =>
        decl_ok?(symb, decl) and decls_ok?(symb, earlier),
}

pub fn bodies_of(decls: Snoc<Decl>, item: ItemId): Int := match decls {
    Empty => 0,
    Extend(earlier, decl) =>
        bodies_of(earlier, item) + match decl {
            Decl::Function(name, _) => if name = item then 1 else 0,
            Decl::Condition(_, _) => 0,
        },
}

pub fn functions_defined?(bindings: Symb, decls: Snoc<Decl>) := match bindings {
    Empty => true,
    Extend(earlier, binding) =>
        (not binding.kind is ItemKind::Function(_) or bodies_of(decls, binding.item) = 1)
        and functions_defined?(earlier, decls),
}

pub fn prog_ok?(symb: Symb, decls: Snoc<Decl>) :=
    symb_ok?(symb)
    and decls_ok?(symb, decls)
    and functions_defined?(symb, decls)
```

## Properties of typing

r[types.layer.operators] spec::types::operator_unique::{unary, binary}
Each unary or binary operator has at most one result type for fixed operand
types.
<!-- status: smt -->

r[types.layer.determinism] spec::types::layer_unique::unique
For fixed Σ, Γ and child typings, a layer has at most one type.
<!-- status: smt -->

r[types.layer.decidability] spec::types::{unary_result, binary_result, provided, infer_layer, layer_inference::exact}
The one-layer judgment is decidable: `infer_layer` computes a layer's type,
if it has one, and `Σ; Γ ⊢ l ▷ τ` holds exactly when `infer_layer(Σ, Γ, l)`
is τ.
<!-- status: smt -->

```fren
expect operator_unique(unary_op: UnaryOp, op: BinaryOp, left: Ty, right: Ty, a: Ty, b: Ty) {
    expect unary: when unary_type?(unary_op, left, a) and unary_type?(unary_op, left, b), a = b
    expect binary: when binary_type?(op, left, right, a) and binary_type?(op, left, right, b), a = b
}

expect layer_unique(symb: Symb, ctx: Ctx, form: ExprF<Typing>, a: Ty, b: Ty) {
    expect unique: when rule?(symb, ctx, form, a) and rule?(symb, ctx, form, b), a = b
}

pub fn unary_result(op: UnaryOp, operand: Ty): Option<Ty> := match op, operand {
    UnaryOp::Neg, Ty::Integer => Some(Ty::Integer),
    UnaryOp::Not, Ty::Boolean => Some(Ty::Boolean),
    _, _ => None,
}

pub fn binary_result(op: BinaryOp, left: Ty, right: Ty): Option<Ty> :=
    if binary_type?(op, left, right, Ty::Integer) then Some(Ty::Integer)
    else if binary_type?(op, left, right, Ty::Boolean) then Some(Ty::Boolean)
    else None

-- The type `ty`, provided that the premises `holds?` hold.
pub fn provided(holds?, ty: Option<Ty>): Option<Ty> := if holds? then ty else None

pub fn infer_layer(symb: Symb, ctx: Ctx, form: ExprF<Typing>): Option<Ty> :=
    match form {
        ExprF::BooleanLiteral(_) => Some(Ty::Boolean),
        ExprF::IntegerLiteral(_) => Some(Ty::Integer),
        ExprF::Local(level) => lookup(ctx, level),
        ExprF::Constructor(item) => match entry(symb, item) {
            Some(ItemKind::Constructor(owner)) => Some(Ty::Nominal(owner)),
            _ => None,
        },
        ExprF::Unary(op, operand) =>
            provided(operand.ctx = ctx, unary_result(op, operand.ty)),
        ExprF::Binary(op, left, right) => provided(
            left.ctx = ctx and right.ctx = ctx,
            binary_result(op, left.ty, right.ty)
        ),
        ExprF::Call(item, args) => match entry(symb, item) {
            Some(ItemKind::Function(sig)) => provided(
                in_context?(args, ctx) and argument_types?(args, sig.params),
                Some(sig.result)
            ),
            _ => None,
        },
        ExprF::Let(annotation, value, body) => provided(
            value.ctx = ctx
                and annotation_matches?(annotation, value.ty)
                and body.ctx = Extend(ctx, value.ty),
            Some(body.ty)
        ),
        ExprF::If(condition, then_branch, else_branch) => provided(
            condition.ctx = ctx
                and condition.ty = Ty::Boolean
                and then_branch.ctx = ctx
                and else_branch.ctx = ctx
                and then_branch.ty = else_branch.ty,
            Some(then_branch.ty)
        ),
        ExprF::Match(scrutinee, arms) => match scrutinee.ty, arms {
            Ty::Nominal(owner), Extend(_, last) => provided(
                scrutinee.ctx = ctx
                    and arm_bodies?(arms, ctx, last.body.ty)
                    and arm_patterns?(symb, arms, owner),
                Some(last.body.ty)
            ),
            _, _ => None,
        },
    }

expect layer_inference(symb: Symb, ctx: Ctx, form: ExprF<Typing>, ty: Ty) {
    expect exact: rule?(symb, ctx, form, ty) iff infer_layer(symb, ctx, form) = Some(ty)
}
```

r[types.layer.call-arity]
If `argument_types?(args, Δ)`, then `|args| = |Δ|`.
<!-- status: lean Spec.Language.Types.argument_types_length -->

r[types.layer.regularity] spec::types::{typings_ok?, arm_typings, children, children_ok?}
Typing produces well-formed types: if ⊢ Σ ok, `Σ ⊢ Γ ok`, every child
typing's type is well formed and `Σ; Γ ⊢ l ▷ τ`, then `Σ ⊢ τ ok`.
<!-- status: lean Spec.Language.Types.layer_regular -->

```fren
pub fn typings_ok?(symb: Symb, typings: Snoc<Typing>) := match typings {
    Empty => true,
    Extend(earlier, typing) => ty_ok?(symb, typing.ty) and typings_ok?(symb, earlier),
}

pub fn arm_typings(arms: Snoc<ArmF<Typing>>): Snoc<Typing> := match arms {
    Empty => Empty,
    Extend(earlier, arm) => Extend(arm_typings(earlier), arm.body),
}

-- A layer's child typings, in order.
pub fn children(form: ExprF<Typing>): Snoc<Typing> := match form {
    ExprF::Unary(_, operand) => one(operand),
    ExprF::Binary(_, left, right) => two(left, right),
    ExprF::Call(_, args) => args,
    ExprF::Let(_, value, body) => two(value, body),
    ExprF::If(condition, then_branch, else_branch) => three(condition, then_branch, else_branch),
    ExprF::Match(scrutinee, arms) => Extend(arm_typings(arms), scrutinee),
    _ => Empty,
}

pub fn children_ok?(symb: Symb, form: ExprF<Typing>) := typings_ok?(symb, children(form))
```

r[types.derivation.regularity]
In a valid table over a well-formed Σ, every row's type is well formed.
<!-- status: lean Spec.Language.Types.table_regular -->

r[types.judgment.regularity]
If `derivation?(Σ, rows, Γ, τ)`, then `Σ ⊢ τ ok`: if `Σ; Γ ⊢ e : τ`, then τ
is well formed.
<!-- status: lean Spec.Language.Types.judgment_regular -->

r[types.derivation.scoped]
Every local of a valid table is in scope: if a row `#i` has context Γ, then
`0 ≤ i < |Γ|`.
<!-- status: lean Spec.Language.Types.table_scoped -->

r[types.derivation.unique] spec::types::same_shape?
Typing is deterministic for a table: two valid tables with the same forms
and contexts, row by row, have the same types row by row.
<!-- status: lean Spec.Language.Types.table_unique -->

```fren
pub fn same_shape?(left: Snoc<Row>, right: Snoc<Row>) := match left, right {
    Empty, Empty => true,
    Extend(left_earlier, l), Extend(right_earlier, r) =>
        l.form = r.form and l.ctx = r.ctx and same_shape?(left_earlier, right_earlier),
    _, _ => false,
}
```

r[types.layer.weakening] spec::types::{shift, insert_type, weaken_typing, weaken_layer}
A layer stays typed when a type σ is inserted at level n of its context and
of every child's context and every local level of at least n is shifted by
one, provided `0 ≤ n ≤ |Γ|`.
<!-- status: lean Spec.Language.Types.layer_weakening -->

```fren
pub fn shift(level: Int, cutoff: Int): Int := if level >= cutoff then level + 1 else level

pub fn insert_type(ctx: Ctx, cutoff: Int, extra: Ty): Ctx := match ctx {
    Empty => if cutoff = 0 then Extend(Empty, extra) else Empty,
    Extend(earlier, ty) =>
        if cutoff = length(earlier) + 1 then Extend(ctx, extra)
        else Extend(insert_type(earlier, cutoff, extra), ty),
}

pub fn weaken_typing(typing: Typing, cutoff: Int, extra: Ty): Typing := Typing {
    ctx := insert_type(typing.ctx, cutoff, extra),
    ty := typing.ty,
}

pub fn weaken_typings(typings: Snoc<Typing>, cutoff: Int, extra: Ty): Snoc<Typing> :=
    match typings {
        Empty => Empty,
        Extend(earlier, typing) => Extend(
            weaken_typings(earlier, cutoff, extra),
            weaken_typing(typing, cutoff, extra)
        ),
    }

pub fn weaken_arms(arms: Snoc<ArmF<Typing>>, cutoff: Int, extra: Ty): Snoc<ArmF<Typing>> :=
    match arms {
        Empty => Empty,
        Extend(earlier, arm) => Extend(
            weaken_arms(earlier, cutoff, extra),
            ArmF {
                constructor := arm.constructor,
                body := weaken_typing(arm.body, cutoff, extra),
            }
        ),
    }

pub fn weaken_layer(form: ExprF<Typing>, cutoff: Int, extra: Ty): ExprF<Typing> := match form {
    ExprF::BooleanLiteral(value?) => ExprF::BooleanLiteral(value?),
    ExprF::IntegerLiteral(value) => ExprF::IntegerLiteral(value),
    ExprF::Local(level) => ExprF::Local(shift(level, cutoff)),
    ExprF::Constructor(item) => ExprF::Constructor(item),
    ExprF::Unary(op, operand) => ExprF::Unary(op, weaken_typing(operand, cutoff, extra)),
    ExprF::Binary(op, left, right) => ExprF::Binary(
        op,
        weaken_typing(left, cutoff, extra),
        weaken_typing(right, cutoff, extra)
    ),
    ExprF::Call(item, args) => ExprF::Call(item, weaken_typings(args, cutoff, extra)),
    ExprF::Let(annotation, value, body) => ExprF::Let(
        annotation,
        weaken_typing(value, cutoff, extra),
        weaken_typing(body, cutoff, extra)
    ),
    ExprF::If(condition, then_branch, else_branch) => ExprF::If(
        weaken_typing(condition, cutoff, extra),
        weaken_typing(then_branch, cutoff, extra),
        weaken_typing(else_branch, cutoff, extra)
    ),
    ExprF::Match(scrutinee, arms) => ExprF::Match(
        weaken_typing(scrutinee, cutoff, extra),
        weaken_arms(arms, cutoff, extra)
    ),
}
```

r[types.derivation.weakening] spec::types::{shift_form, weaken, contexts_reach?}
A valid table stays valid when a well-formed type is inserted at level n of
every row's context and every local level of at least n is shifted by one,
provided `0 ≤ n` and every row's context has at least n entries.
<!-- status: lean Spec.Language.Types.table_weakening -->

```fren
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
            ctx := insert_type(row.ctx, cutoff, extra),
            ty := row.ty,
        }
    ),
}

pub fn contexts_reach?(rows: Snoc<Row>, cutoff: Int) := match rows {
    Empty => true,
    Extend(earlier, row) => 0 <= cutoff <= length(row.ctx) and contexts_reach?(earlier, cutoff),
}
```

r[types.derivation.weakening-lookup]
The step for locals holds: if `0 ≤ n ≤ |Γ|`, the shifted level of i in Γ
with σ inserted at level n holds `Γ(i)`, and level n holds σ.
<!-- status: lean Spec.Language.Types.lookup_shift -->

r[types.safety]
Typing is sound for the dynamic semantics: in a well-typed, verified
program, evaluating a well-typed expression under values of its context's
types is defined and gives a value of its type, as the
[expressions chapter](Expressions.md#values-interpretation-and-mentioned-names)
defines evaluation.
<!-- status: open -->

## Whole-expression properties

The properties in this section concern the expression that a table's root
unfolds to.

r[types.derivation.alike] spec::types::{Pair, paired?, children_paired?, arms_paired?, layers_paired?, pairs_agree?, alike?}
Two rows *unfold alike* when a set of position pairs that contains them
pairs every pair's layers: the same form and payloads, with each pair of
corresponding children, argument by argument and arm by arm, again a pair
of the set. `alike?(l, p, r, q, pairs)` checks that `pairs` is such a set
for the row at level p of l and the row at level q of r.
<!-- status: definition -->

```fren
pub struct Pair { left: Int, right: Int }

pub fn paired?(pairs: Snoc<Pair>, left: Int, right: Int) := match pairs {
    Empty => false,
    Extend(earlier, pair) =>
        (pair.left = left and pair.right = right) or paired?(earlier, left, right),
}

pub fn children_paired?(pairs: Snoc<Pair>, left: Snoc<Int>, right: Snoc<Int>) := match left, right {
    Empty, Empty => true,
    Extend(left_earlier, l), Extend(right_earlier, r) =>
        paired?(pairs, l, r) and children_paired?(pairs, left_earlier, right_earlier),
    _, _ => false,
}

pub fn arms_paired?(pairs: Snoc<Pair>, left: Snoc<Arm>, right: Snoc<Arm>) := match left, right {
    Empty, Empty => true,
    Extend(left_earlier, l), Extend(right_earlier, r) =>
        l.constructor = r.constructor
        and paired?(pairs, l.body, r.body)
        and arms_paired?(pairs, left_earlier, right_earlier),
    _, _ => false,
}

pub fn layers_paired?(pairs: Snoc<Pair>, left: Form, right: Form) := match left, right {
    ExprF::Unary(l_op, l), ExprF::Unary(r_op, r) => l_op = r_op and paired?(pairs, l, r),
    ExprF::Binary(l_op, l1, l2), ExprF::Binary(r_op, r1, r2) =>
        l_op = r_op and paired?(pairs, l1, r1) and paired?(pairs, l2, r2),
    ExprF::Call(l_item, l_args), ExprF::Call(r_item, r_args) =>
        l_item = r_item and children_paired?(pairs, l_args, r_args),
    ExprF::Let(l_annotation, l1, l2), ExprF::Let(r_annotation, r1, r2) =>
        l_annotation = r_annotation and paired?(pairs, l1, r1) and paired?(pairs, l2, r2),
    ExprF::If(l1, l2, l3), ExprF::If(r1, r2, r3) =>
        paired?(pairs, l1, r1) and paired?(pairs, l2, r2) and paired?(pairs, l3, r3),
    ExprF::Match(l1, l_arms), ExprF::Match(r1, r_arms) =>
        paired?(pairs, l1, r1) and arms_paired?(pairs, l_arms, r_arms),
    _, _ => left = right,
}

pub fn pairs_agree?(left: Snoc<Row>, right: Snoc<Row>, pairs: Snoc<Pair>, remaining: Snoc<Pair>) :=
    match remaining {
        Empty => true,
        Extend(earlier, pair) =>
            match lookup(left, pair.left), lookup(right, pair.right) {
                Some(l), Some(r) => layers_paired?(pairs, l.form, r.form),
                _, _ => false,
            }
            and pairs_agree?(left, right, pairs, earlier),
    }

pub fn alike?(
    left: Snoc<Row>,
    left_position: Int,
    right: Snoc<Row>,
    right_position: Int,
    pairs: Snoc<Pair>
) :=
    paired?(pairs, left_position, right_position) and pairs_agree?(left, right, pairs, pairs)
```

r[types.judgment.adequacy]
The judgment agrees with the inductive reading of the rules in the figure:
`Σ; Γ ⊢ e : τ` holds exactly when a finite tree of rule instances concludes
it.
<!-- status: open -->

r[types.derivation.unique-expression]
Typing is deterministic for an expression: if `derivation?(Σ, l, Γ, τ)` and
`derivation?(Σ, r, Γ, υ)` and their roots unfold alike, then τ = υ, whatever
the two tables' sharing of rows and extra rows.
<!-- status: open -->

r[types.judgment.weakening]
Typing is preserved by extending its context: if `derivation?(Σ, rows, Γ, τ)`
and `Σ ⊢ σ ok`, then `derivation?(Σ, weaken(rows, |Γ|, σ), (Γ, σ), τ)`. By
the definition of unfolding, the weakened root unfolds to e', the expression
e that the root unfolded to with every local level of at least `|Γ|`, those
bound within e, shifted by one; so if `Σ; Γ ⊢ e : τ` then `Σ; Γ, σ ⊢ e' : τ`.
<!-- status: lean Spec.Language.Types.judgment_weakening -->

r[types.judgment.decidability]
Typing is decidable: an algorithm, given Σ, Γ and e, finds the τ with
`Σ; Γ ⊢ e : τ` or reports that there is none. Building a table bottom-up
with `infer_layer`, in the contexts that `rule?` prescribes for the
children, is such an algorithm.
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
The *`?` suffix rule*: a parameter or let binder whose name ends in `?` must
have type Boolean, including when it has an explicit annotation, which the
suffix does not overwrite. A let binder `x?` without an annotation
elaborates to a Core let annotated Boolean.
<!-- status: definition -->

```fren
pub fn suffix_rule?(question?, ty: Ty) := not question? or ty = Ty::Boolean

pub fn parameter_type?(written: Option<Ty>, question?, ty: Ty) :=
    suffix_rule?(question?, ty)
    and match written {
        Some(annotation) => ty = annotation,
        None => question?,
    }

pub fn let_annotation?(written: Option<Ty>, question?, core: Option<Ty>) := match written {
    Some(annotation) => suffix_rule?(question?, annotation) and core = written,
    None => core = (if question? then Some(Ty::Boolean) else None),
}
```

## Examples

r[types.examples.derivations] spec::types::{EXAMPLE_SYMBOLS, SYMBOLS, bind, row, BOOLEAN_INTEGER, OLDEST_LEVEL_EXAMPLE, LET_EXAMPLE, MATCH_EXAMPLE, CALL_EXAMPLE, PROGRAM_EXAMPLE}
Each accepted example below gives a Core judgment and a table that types
it, shown as rows numbered by level; its root, the last row, unfolds to the
judgment's expression. The wrapper's theorem `worked_examples` evaluates
each example's Fren constant and so confirms that the table is valid with
that root's context and type. The wrapper also checks further tables,
accepted and rejected, at least one for each rule.
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

pub fn bind(item: ItemId, kind: ItemKind): Entry := Entry { item, kind }

pub const EXAMPLE_SYMB: Symb := Extend(
    four(
        bind(LIGHT, ItemKind::Enumeration(two(LIGHT_RED, LIGHT_GREEN))),
        bind(LIGHT_RED, ItemKind::Constructor(LIGHT)),
        bind(LIGHT_GREEN, ItemKind::Constructor(LIGHT)),
        bind(SIGNAL, ItemKind::Enumeration(one(SIGNAL_RED)))
    ),
    bind(SIGNAL_RED, ItemKind::Constructor(SIGNAL))
)

pub const SYMB: Symb := Extend(
    EXAMPLE_SYMB,
    bind(
        F,
        ItemKind::Function(
            Sig {
                params := one(Ty::Integer),
                result := Ty::Integer,
            }
        )
    )
)

pub fn row(form: Form, ctx: Ctx, ty: Ty): Row := Row { form, ctx, ty }
```

`Σ; ·, Boolean, Integer ⊢ #0 : Boolean`: level 0 is the oldest entry.

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `#0` | `·, Boolean, Integer` | Boolean |

`Σ; · ⊢ let: Integer 1 in #0 : Integer`: the body's context is `·, Integer`.

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `1` | `·` | Integer |
| 1 | `#0` | `·, Integer` | Integer |
| 2 | `let: Integer row 0 in row 1` | `·` | Integer |

`Σ; · ⊢ match M::Light::Red { M::Light::Red ⇒ 1 | M::Light::Green ⇒ 2 } : Integer`:

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `M::Light::Red` | `·` | `Nominal(M::Light)` |
| 1 | `1` | `·` | Integer |
| 2 | `2` | `·` | Integer |
| 3 | `match row 0 { M::Light::Red ⇒ row 1 \| M::Light::Green ⇒ row 2 }` | `·` | Integer |

`Σ; · ⊢ M::f(1) : Integer`:

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `1` | `·` | Integer |
| 1 | `M::f(row 0)` | `·` | Integer |

A program whose one function, `M::f`, has the body `#0 + 1` in its parameter
context `·, Integer`, is well typed, with this table for the body:

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `#0` | `·, Integer` | Integer |
| 1 | `1` | `·, Integer` | Integer |
| 2 | `row 0 + row 1` | `·, Integer` | Integer |

```fren
pub const BOOLEAN_INTEGER: Ctx := two(Ty::Boolean, Ty::Integer)

pub const OLDEST_LEVEL_EXAMPLE: Bool := derivation?(
    SYMB,
    one(row(ExprF::Local(0), BOOLEAN_INTEGER, Ty::Boolean)),
    BOOLEAN_INTEGER,
    Ty::Boolean
)

pub const LET_EXAMPLE: Bool := derivation?(
    SYMB,
    three(
        row(ExprF::IntegerLiteral(1), Empty, Ty::Integer),
        row(ExprF::Local(0), one(Ty::Integer), Ty::Integer),
        row(ExprF::Let(Some(Ty::Integer), 0, 1), Empty, Ty::Integer)
    ),
    Empty,
    Ty::Integer
)

pub const MATCH_EXAMPLE: Bool := derivation?(
    SYMB,
    four(
        row(ExprF::Constructor(LIGHT_RED), Empty, Ty::Nominal(LIGHT)),
        row(ExprF::IntegerLiteral(1), Empty, Ty::Integer),
        row(ExprF::IntegerLiteral(2), Empty, Ty::Integer),
        row(
            ExprF::Match(
                0,
                two(
                    ArmF { constructor := LIGHT_RED, body := 1 },
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

pub const CALL_EXAMPLE: Bool := derivation?(
    SYMB,
    two(
        row(ExprF::IntegerLiteral(1), Empty, Ty::Integer),
        row(ExprF::Call(F, one(0)), Empty, Ty::Integer)
    ),
    Empty,
    Ty::Integer
)

pub const PROGRAM_EXAMPLE: Bool := prog_ok?(
    SYMB,
    one(
        Decl::Function(
            F,
            three(
                row(ExprF::Local(0), one(Ty::Integer), Ty::Integer),
                row(ExprF::IntegerLiteral(1), one(Ty::Integer), Ty::Integer),
                row(
                    ExprF::Binary(BinaryOp::Add, 0, 1),
                    one(Ty::Integer),
                    Ty::Integer
                )
            )
        )
    )
)
```

r[types.examples.rejected] spec::types::rejected::{out_of_scope, branches, foreign_pattern, no_arms, extra_argument}
Each rejected example is a layer that has no type, whatever the typings of
the children its premises leave free: the local `#0` in `·`; a conditional
whose branches have types Integer and Boolean, such as `1` and `false`; a
match on a value of `Nominal(a)` whose one arm's pattern is a constructor
of another enumeration; a match with no arms; and a call with two arguments
of a function with one parameter.
<!-- status: smt -->

```fren
expect rejected(
    symb: Symb,
    ctx: Ctx,
    item: ItemId,
    owner: ItemId,
    other: ItemId,
    first: Typing,
    second: Typing,
    third: Typing,
    ty: Ty,
) {
    expect out_of_scope: not rule?(symb, Empty, ExprF::Local(0), ty)
    expect branches: when second.ty = Ty::Integer and third.ty = Ty::Boolean,
        not rule?(symb, ctx, ExprF::If(first, second, third), ty)
    expect foreign_pattern: when first.ty = Ty::Nominal(owner)
        and entry(symb, item) = Some(ItemKind::Constructor(other))
        and other != owner,
        not rule?(
            symb,
            ctx,
            ExprF::Match(first, one(ArmF { constructor := item, body := second })),
            ty
        )
    expect no_arms: not rule?(symb, ctx, ExprF::Match(first, Empty), ty)
    expect extra_argument: when entry(symb, item) = Some(
        ItemKind::Function(
            Sig {
                params := one(third.ty),
                result := ty,
            }
        )
    ),
        not rule?(symb, ctx, ExprF::Call(item, two(first, second)), ty)
}
```

## Informative source examples

These source programs are checked, with the diagnostics they expect, by
both of today's front ends. They are informative: the translation from
source programs to the Core is not yet specified.

```fren example
--@ reference: types.operator.binary
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := l + 1  --~ error: type mismatch: expected `Int`, found `bad::Light`
```

```fren example
--@ reference: types.expression.let
pub mod bad

pub fn f(n: Int): Int := let b: Bool := n in 0  --~ error: the definition of `b` has type `Int`, not `Bool`
```

```fren example
--@ reference: types.surface.suffix
pub mod bad

pub fn f(b?: Int): Int := b?  --~ error: `b?` ends in `?` but is not a `Bool`
```

```fren example
--@ reference: types.expression.call
pub mod bad

pub fn g(n: Int): Int := n

pub fn f(n: Int): Int := g(n, n)  --~ error: `bad::g` takes 1 argument, but 2 were given
```

```fren example
--@ reference: types.expression.if
pub mod bad

pub fn f(n: Int): Int := if n then 1 else 0  --~ error: type mismatch: expected `Bool`, found `Int`
```

```fren example
--@ reference: types.expression.if
pub mod bad

pub fn f(b?): Int := if b? then 1 else false  --~ error: the branches of `if` have different types: `Int` and `Bool`
```

```fren example
--@ reference: types.operator.binary
pub mod bad

pub enum Light { Red, Green }
pub enum Signal { Red, Green }

pub fn same?(l: Light, s: Signal) := l = s  --~ error: cannot compare `bad::Light` with `bad::Signal`
```

```fren example
--@ reference: types.expression.match
pub mod bad

pub enum Light { Red, Green }

pub fn f(n: Int): Int := match n {
    Light::Red => 0,  --~ error: expected a pattern of `Int`, but this is a pattern of `bad::Light`
    Light::Green => 1,
}
```
