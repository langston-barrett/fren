# Core typing

Source programs are defined by translation into the Core, a small typed
language; the [THIR chapter](../Compiler/Thir.md) relates it to the
compiler's typed representation. Static semantics comprises resolution,
typing, and verification, including definedness. This chapter defines
typing; [resolution](NamesAndScope.md), the chapter before this one,
defines the Core's expressions and the semantic objects that this chapter
types them with, and supplies identities, and
[Definedness and verification](PropertiesAndChecks.md) defines the
obligations that verification proves. Dynamic semantics applies only to
well-typed, verified programs. Typing alone establishes neither definedness nor logical truth.

## Overview

The chapter's judgments, and the Fren definitions that state them; the
first three are [defined by resolution](NamesAndScope.md#r-names.symbols.types-ok):

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `Σ ⊢ τ ok` | τ is a well-formed type | `ty_ok?` |
| `Σ ⊢ Γ ok` | every type of Γ is well formed | `ctx_ok?` |
| `⊢ Σ ok` | Σ is a well-formed symbol environment | `symb_ok?` |
| `Σ; Γ ⊢ l ▷ τ` | one layer l, its children's typings given, has type τ | `rule?` |
| `Σ; Γ ⊢ e : τ` | e has type τ in Γ | `derivation?`, given a table for e |
| `Σ ⊢ d ok` | a declaration is well typed | `decl_ok?` |
| `⊢ (Σ, ds) ok` | a program is well typed | `prog_ok?` |

r[types.overview.laws]
In outline, typing is a decidable relation `derives?(Σ, Γ, d, τ)` between a
symbol environment, a context, a derivation d of an expression and a type:

```text
  derives? : Symb × Ctx × Derivation × Ty → Bool
  type_of  : Symb × Ctx × Derivation → Ty

  derives?(Σ, Γ, d, τ)  implies  τ = type_of(Σ, Γ, d)
                                 ⊢ Σ ok  and  Σ ⊢ Γ ok  and  Σ ⊢ τ ok
```

A derivation records the type it derives, so it derives at most one type;
only well-formed environments and contexts admit derivations; and every
derived type is well formed. The [interface](#r-types.overview.interface)
at the end of the chapter states these as a contract of uninterpreted
functions, which the chapter's wrapper interprets by the detailed
definitions. That an *expression* has at most one type, whatever
derivation types it, is the [uniqueness of an expression's
type](#r-types.derivation.unique-expression); two tables with the same rows
have the same types by [determinism for a table](#r-types.derivation.unique).
The other headline laws are stated with the detailed definitions:
[regularity](#r-types.judgment.regularity), that a derived type is well
formed; [weakening](#r-types.judgment.weakening), that a derivation
survives extending its context; [inference for a
layer](#r-types.layer.inference), that a layer's type can be computed; and,
open, [decidability of the judgment](#r-types.judgment.decidability).
That the tables mean what the rules mean read as trees is
[adequacy](#r-types.judgment.adequacy), which is proved in Lean.
`fren trace` reports the evidence for each law stated as a procedure.

## Semantic objects

r[types.object.resolution]
The semantic objects of typing are those that
[resolution](NamesAndScope.md#semantic-objects) defines, and this chapter
imports them: item identities and types
([`ItemId`, `Ty`](NamesAndScope.md#r-names.object.identity)), snoc sequences
([`Snoc`](Syntax.md#r-syntax.tree.types), which the syntax chapter defines)
with their lengths and lookups
([`length`, `lookup`](NamesAndScope.md#r-names.sequence.snoc)),
contexts ([`Ctx`](NamesAndScope.md#r-names.context.slots)) and symbol
environments ([`Symb`](NamesAndScope.md#r-names.symbols.environment)) with
their well-formedness judgments
([`ty_ok?`, `ctx_ok?`](NamesAndScope.md#r-names.symbols.types-ok) and
[`symb_ok?`](NamesAndScope.md#r-names.symbols.well-formed)).

```fren
pub mod spec
pub mod spec::types

use spec::names::{
    ArmF,
    CoreF,
    Ctx,
    Entry,
    Form,
    ItemId,
    ItemKind,
    LIGHT,
    LIGHT_GREEN,
    LIGHT_RED,
    Sig,
    Symb,
    Ty,
    ctx_ok?,
    entry,
    four,
    length,
    lookup,
    one,
    shift,
    shift_form,
    symb_ok?,
    three,
    two,
    ty_ok?,
}

use spec::surface::{BinaryOp, Snoc, UnaryOp}

use spec::surface::Snoc::{Empty, Extend}
```

r[types.context.bound] spec::types::lookup_bound::below
If `Γ(i) = τ`, then `0 ≤ i < |Γ|`.

```fren
expect lookup_bound(ctx: Ctx, level: Int, ty: Ty) {
    expect below: when lookup(ctx, level) = Some(ty), 0 <= level < length(ctx)
}
```

r[types.context.weakening] spec::types::lookup_weakening::{older, newest}
Extension leaves every existing level unchanged: if `0 ≤ i < |Γ|`, then
`(Γ, σ)(i) = Γ(i)`, and `(Γ, σ)(|Γ|) = σ`.

```fren
expect lookup_weakening(ctx: Ctx, extra: Ty, level: Int) {
    expect older: when 0 <= level < length(ctx),
        lookup(Extend(ctx, extra), level) = lookup(ctx, level)
    expect newest: lookup(Extend(ctx, extra), length(ctx)) = Some(extra)
}
```

r[types.symbols.resolution]
The symbol environment that [resolution](NamesAndScope.md) produces for a
program is well formed; in particular, resolution rejects an item declared
twice. Resolution states and proves this as the [well-formed
environment of collection](NamesAndScope.md#r-names.handoff.environment).

<a id="finite-expression-derivations"></a>

## Core expressions and layers

The Core's grammar and the forms of its expressions, `CoreF<E>`, are
[defined by resolution](NamesAndScope.md#r-names.core.syntax), which
produces them. Figures and prose name locals, as in
`let x := e₁ in e₂`, but each name stands for a de Bruijn level: the Core
writes a local as `#i`, for the entry at level i, and a let binds the next
level. In a figure, `Γ, x : σ` is the context `Γ, σ`, with x naming its new
level `|Γ|`, and `Γ(x) = τ` says that x's entry is τ.

r[types.expression.layer] spec::types::Typing
A *layer* is one form `CoreF<E>` whose children are E: each child's typing,
or the level of a row of a table. A *typing* records a context and a type.

```fren
pub struct Typing { ctx: Ctx, ty: Ty }
```

## Typing rules

Each rule below is a premise check on one layer, whose children's typings
are given; the derivation section assembles layers into derivations.

r[types.operator.unary] spec::types::unary_type?
Unary minus takes and returns `Int`; `not` takes and returns `Bool`.

```fren
pub fn unary_type?(op: UnaryOp, operand: Ty, result: Ty) := match op {
    UnaryOp::Neg => operand = Ty::Integer and result = Ty::Integer,
    UnaryOp::Not => operand = Ty::Boolean and result = Ty::Boolean,
}
```

r[types.operator.binary] spec::types::{integer_binary?, comparison?, boolean_binary?, binary_type?}
Arithmetic takes `Int` operands and returns an `Int`; integer comparisons
return a `Bool`. Boolean operators take and return `Bool`. Equality and
inequality take two operands of the same type and return a `Bool`.

```fren
pub fn integer_binary?(op: BinaryOp) :=
    op in {
        BinaryOp::Add,
        BinaryOp::Sub,
        BinaryOp::Mul,
        BinaryOp::Div,
        BinaryOp::Rem,
    }

pub fn comparison?(op: BinaryOp) := op in {BinaryOp::Lt, BinaryOp::Le, BinaryOp::Gt, BinaryOp::Ge}
pub fn boolean_binary?(op: BinaryOp) := op in {BinaryOp::And, BinaryOp::Or, BinaryOp::Iff}

pub fn binary_type?(op: BinaryOp, left: Ty, right: Ty, result: Ty) :=
    if integer_binary?(op) then left = Ty::Integer and right = Ty::Integer and result = Ty::Integer
    else if comparison?(op) then left = Ty::Integer and right = Ty::Integer and result = Ty::Boolean
    else if boolean_binary?(op) then left = Ty::Boolean and right = Ty::Boolean and result = Ty::Boolean
    else left = right and result = Ty::Boolean
```

r[types.expression.boolean] spec::types::boolean_rule?
With no premises, `Σ; Γ ⊢ b : Bool`.

```fren
pub fn boolean_rule?(ty: Ty) := ty = Ty::Boolean
```

r[types.expression.integer] spec::types::integer_rule?
With no premises, `Σ; Γ ⊢ n : Int`.

```fren
pub fn integer_rule?(ty: Ty) := ty = Ty::Integer
```

r[types.expression.local] spec::types::local_rule?
A local has the type of its context entry.

```text
  Γ(x) = τ
  ─────────────
  Σ; Γ ⊢ x : τ
```

```fren
pub fn local_rule?(ctx: Ctx, level: Int, ty: Ty) := lookup(ctx, level) = Some(ty)
```

r[types.expression.constructor] spec::types::constructor_rule?
A constructor has its owner's nominal type.

```text
  Σ(c) = constructor of a
  ───────────────────────
  Σ; Γ ⊢ c : Nominal(a)
```

```fren
pub fn constructor_rule?(symb: Symb, item: ItemId, ty: Ty) := match entry(symb, item) {
    Some(ItemKind::Constructor(owner)) => ty = Ty::Nominal(owner),
    _ => false,
}
```

r[types.expression.unary] spec::types::unary_rule?
A unary operation follows `unary_type?`.

```text
  Σ; Γ ⊢ e : σ   unary_type?(⊖, σ, τ)
  ───────────────────────────────────
  Σ; Γ ⊢ ⊖ e : τ
```

```fren
pub fn unary_rule?(ctx: Ctx, op: UnaryOp, operand: Typing, ty: Ty) :=
    operand.ctx = ctx
    and unary_type?(op, operand.ty, ty)
```

r[types.expression.binary] spec::types::binary_rule?
A binary operation follows `binary_type?`.

```text
  Σ; Γ ⊢ l : σ   Σ; Γ ⊢ r : υ   binary_type?(⊕, σ, υ, τ)
  ──────────────────────────────────────────────────────
  Σ; Γ ⊢ l ⊕ r : τ
```

```fren
pub fn binary_rule?(ctx: Ctx, op: BinaryOp, left: Typing, right: Typing, ty: Ty) :=
    left.ctx = ctx
    and right.ctx = ctx
    and binary_type?(op, left.ty, right.ty, ty)
```

r[types.expression.call] spec::types::{in_context?, argument_types?, call_rule?}
A call's arguments have its function's parameter types, level by level, and
the call has its result type.

```text
  Σ(f) = function with parameters σ₀, …, σₙ₋₁ and result τ
  Σ; Γ ⊢ aₖ : σₖ   (each k < n)
  ────────────────────────────────────────────────────────
  Σ; Γ ⊢ f(a₀, …, aₙ₋₁) : τ
```

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
A let types its value in Γ and its body in Γ extended by the value's type.

```text
  Σ; Γ ⊢ e₁ : σ   Σ; Γ, x : σ ⊢ e₂ : τ
  ─────────────────────────────────────
  Σ; Γ ⊢ let x := e₁ in e₂ : τ
```

```fren
pub fn let_rule?(ctx: Ctx, value: Typing, body: Typing, ty: Ty) :=
    value.ctx = ctx
    and body.ctx = Extend(ctx, value.ty)
    and body.ty = ty
```

r[types.expression.let-annotated] spec::types::let_annotated_rule?
A let with an annotation σ is typed as a let whose value has type σ.

```text
  Σ; Γ ⊢ e₁ : σ   Σ; Γ, x : σ ⊢ e₂ : τ
  ─────────────────────────────────────
  Σ; Γ ⊢ let x : σ := e₁ in e₂ : τ
```

```fren
pub fn let_annotated_rule?(ctx: Ctx, written: Ty, value: Typing, body: Typing, ty: Ty) :=
    value.ty = written
    and let_rule?(ctx, value, body, ty)
```

r[types.expression.if] spec::types::if_rule?
A conditional has a `Bool` condition and two branches of one type.

```text
  Σ; Γ ⊢ c : Bool   Σ; Γ ⊢ e₁ : τ   Σ; Γ ⊢ e₂ : τ
  ─────────────────────────────────────────────────
  Σ; Γ ⊢ if c then e₁ else e₂ : τ
```

```fren
pub fn if_rule?(ctx: Ctx, condition: Typing, then_branch: Typing, else_branch: Typing, ty: Ty) :=
    condition.ctx = ctx
    and condition.ty = Ty::Boolean
    and then_branch.ctx = ctx
    and then_branch.ty = ty
    and else_branch.ctx = ctx
    and else_branch.ty = ty
```

r[types.expression.match] spec::types::{arm_bodies?, arm_patterns?, match_rule?}
A match's scrutinee is nominal, its arms are nonempty, each pattern is a
constructor of the scrutinee's enumeration, and each arm body is typed in Γ
at the match's type.

```text
  Σ; Γ ⊢ s : Nominal(a)   at least one arm
  Σ(cₖ) = constructor of a   Σ; Γ ⊢ eₖ : τ   (each arm k)
  ─────────────────────────────────────────────────────────
  Σ; Γ ⊢ match s { c₀ ⇒ e₀ | … | cₘ ⇒ eₘ } : τ
```

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

pub fn match_rule?(symb: Symb, ctx: Ctx, scrutinee: Typing, arms: Snoc<ArmF<Typing>>, ty: Ty) :=
    scrutinee.ctx = ctx
    and arms != Empty
    and arm_bodies?(arms, ctx, ty)
    and match scrutinee.ty {
        Ty::Nominal(owner) => arm_patterns?(symb, arms, owner),
        _ => false,
    }
```

r[types.judgment.layer] spec::types::rule?
The one-layer judgment `Σ; Γ ⊢ l ▷ τ` takes Σ, Γ, a layer `CoreF<Typing>`
whose child positions hold the children's typings, and τ. It checks exactly
the rule above for l's form.

```fren
pub fn rule?(symb: Symb, ctx: Ctx, form: CoreF<Typing>, ty: Ty) := match form {
    CoreF::BooleanLiteral(_) => boolean_rule?(ty),
    CoreF::IntegerLiteral(_) => integer_rule?(ty),
    CoreF::Local(level) => local_rule?(ctx, level, ty),
    CoreF::Constructor(item) => constructor_rule?(symb, item, ty),
    CoreF::Unary(op, operand) => unary_rule?(ctx, op, operand, ty),
    CoreF::Binary(op, left, right) => binary_rule?(ctx, op, left, right, ty),
    CoreF::Call(item, args) => call_rule?(symb, ctx, item, args, ty),
    CoreF::Let(None, value, body) => let_rule?(ctx, value, body, ty),
    CoreF::Let(Some(written), value, body) => let_annotated_rule?(ctx, written, value, body, ty),
    CoreF::If(condition, then_branch, else_branch) =>
        if_rule?(ctx, condition, then_branch, else_branch, ty),
    CoreF::Match(scrutinee, arms) => match_rule?(symb, ctx, scrutinee, arms, ty),
}
```

## Derivations

r[types.derivation.table] spec::types::{Arm, Row, typing_at, annotate_arguments, annotate_arms, annotate, rows_valid?}
A *derivation table* is a snoc sequence of rows. A row has a layer whose
children are the levels of earlier rows, a context and a type. A table is
valid in Σ when every row's context is well formed and every row satisfies
`rule?` with each child replaced by that earlier row's context and type; a
child level that names no earlier row fails. Every row is checked,
including rows that no other row uses.

```fren
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

pub fn annotate(rows: Snoc<Row>, form: Form): Option<CoreF<Typing>> := match form {
    CoreF::BooleanLiteral(value?) => Some(CoreF::BooleanLiteral(value?)),
    CoreF::IntegerLiteral(value) => Some(CoreF::IntegerLiteral(value)),
    CoreF::Local(level) => Some(CoreF::Local(level)),
    CoreF::Constructor(item) => Some(CoreF::Constructor(item)),
    CoreF::Unary(op, operand) => match typing_at(rows, operand) {
        Some(child) => Some(CoreF::Unary(op, child)),
        None => None,
    },
    CoreF::Binary(op, left, right) => match typing_at(rows, left), typing_at(rows, right) {
        Some(l), Some(r) => Some(CoreF::Binary(op, l, r)),
        _, _ => None,
    },
    CoreF::Call(item, args) => match annotate_arguments(rows, args) {
        Some(typed) => Some(CoreF::Call(item, typed)),
        None => None,
    },
    CoreF::Let(annotation, value, body) => match typing_at(rows, value), typing_at(rows, body) {
        Some(v), Some(b) => Some(CoreF::Let(annotation, v, b)),
        _, _ => None,
    },
    CoreF::If(condition, then_branch, else_branch) =>
        match typing_at(rows, condition), typing_at(rows, then_branch), typing_at(
            rows,
            else_branch
        ) {
            Some(c), Some(t), Some(e) => Some(CoreF::If(c, t, e)),
            _, _, _ => None,
        },
    CoreF::Match(scrutinee, arms) => match typing_at(rows, scrutinee), annotate_arms(rows, arms) {
        Some(typed), Some(typed_arms) => Some(CoreF::Match(typed, typed_arms)),
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
A valid table's children name only earlier rows, so unfolding ends.
Every written child of the expression is a row, including an unused let
value, both branches of a conditional and every arm body; several
occurrences may share a row.

r[types.judgment.typing] spec::types::{extends?, rows_extend?, derivation?}
`Σ; Γ ⊢ e : τ` holds when Σ and Γ are well formed and some valid table,
every row of which has a context that extends Γ, has a newest row, its
*root*, with context Γ and type τ that unfolds to e. A context *extends* Γ
when it is Γ or Γ followed by further entries. `derivation?` checks that a
table is valid in this way with such a root.

```text
  ⊢ Σ ok   Σ ⊢ Γ ok
  a valid table, its contexts extending Γ, has a root
  with context Γ and type τ that unfolds to e
  ───────────────────────────────────────────────────
  Σ; Γ ⊢ e : τ
```

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

r[types.judgment.coverage-separate] spec::types::coverage_separate::{repeated, omitted}
Typing does not depend on coverage: a typed match stays typed when its
newest arm is repeated, or dropped while another arm remains.

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
        CoreF::Match(scrutinee, Extend(earlier, last)),
        ty
    )
    expect repeated: not typed?
        or rule?(
            symb,
            ctx,
            CoreF::Match(scrutinee, Extend(Extend(earlier, last), last)),
            ty
        )
    expect omitted: not typed? or earlier = Empty or rule?(symb, ctx, CoreF::Match(scrutinee, earlier), ty)
}
```

## Declarations and programs

r[types.context.parameters]
A declaration's body context is its parameter types in written order: the
first parameter has level 0. A function's signature records that context.

r[types.declaration.result] spec::types::{Decl, decl_ok?}
A function body is typed at its declared result type in its parameter
context, and each assume or expect body at `Bool` in its parameter context.
A declaration carries the table whose root unfolds to its body.

```text
  Σ(f) = function with parameters Δ and result τ   Σ; Δ ⊢ e : τ
  ─────────────────────────────────────────────────────────────
  Σ ⊢ function f with body e ok

  Σ; Δ ⊢ e : Bool
  ─────────────────────────────
  Σ ⊢ condition over Δ, e ok
```

```fren
pub enum Decl { Function(ItemId, Snoc<Row>), Condition(Ctx, Snoc<Row>) }

pub fn decl_ok?(symb: Symb, decl: Decl) := match decl {
    Decl::Function(item, body) => match entry(symb, item) {
        Some(ItemKind::Function(sig)) => derivation?(symb, body, sig.params, sig.result),
        _ => false,
    },
    Decl::Condition(params, body) => derivation?(symb, body, params, Ty::Boolean),
}
```

r[types.program.typing] spec::types::{decls_ok?, bodies_of, functions_defined?, prog_ok?}
A Core program is well typed when its symbol environment is well formed,
every declaration is well typed in that one environment, and every function
that the environment binds has exactly one body among the declarations.

```text
  ⊢ Σ ok   Σ ⊢ d ok (each d in ds)
  each function of Σ has exactly one body in ds
  ─────────────────────────────────────────────
  ⊢ (Σ, ds) ok
```

```fren
pub fn decls_ok?(symb: Symb, decls: Snoc<Decl>) := match decls {
    Empty => true,
    Extend(earlier, decl) => decl_ok?(symb, decl) and decls_ok?(symb, earlier),
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

r[types.program.source]
A source program is well typed exactly when its translation into a Core
program is. The derived-forms chapter, not yet written, is to define that
translation.

r[types.program.nonrecursive]
A Core program has no recursive call cycles: no function's body calls
itself, directly or through other functions. This is a static condition
separate from typing; the [THIR chapter](../Compiler/Thir.md) states its
check.

## Properties of typing

An `expect` below is proved by the solver. A procedure states a law that
the chapter's wrapper proves in Lean, by an `impl` bound to the procedure,
or that is open, with no `impl`; `fren trace` reports which. Each law's
procedure has one output, `holds?`, so that its evidence is its own. Its own
checks are set to random testing, and that testing is not claimed as
evidence.

r[types.layer.operators] spec::types::operator_unique::{unary, binary}
Each unary or binary operator has at most one result type for fixed operand
types.

```fren
expect operator_unique(unary_op: UnaryOp, op: BinaryOp, left: Ty, right: Ty, a: Ty, b: Ty) {
    expect unary: when unary_type?(unary_op, left, a) and unary_type?(unary_op, left, b), a = b
    expect binary: when binary_type?(op, left, right, a) and binary_type?(op, left, right, b), a = b
}
```

r[types.layer.determinism] spec::types::layer_unique::unique
For fixed Σ, Γ and child typings, a layer has at most one type.

```fren
expect layer_unique(symb: Symb, ctx: Ctx, form: CoreF<Typing>, a: Ty, b: Ty) {
    expect unique: when rule?(symb, ctx, form, a) and rule?(symb, ctx, form, b), a = b
}
```

r[types.layer.inference] spec::types::{unary_result, binary_result, provided, infer_layer, layer_inference::exact}
Inference for a layer: a layer's type, if it has one, can be computed from Σ,
Γ and its children's typings. `infer_layer` computes it, and
`Σ; Γ ⊢ l ▷ τ` holds exactly when `infer_layer(Σ, Γ, l)` is τ. Checking
`rule?` at a given type is already a computation; this law adds that the
type need not be given. `infer_layer` restates each rule as a computation,
so the law mostly confirms that the two agree.

```fren
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

pub fn infer_layer(symb: Symb, ctx: Ctx, form: CoreF<Typing>): Option<Ty> := match form {
    CoreF::BooleanLiteral(_) => Some(Ty::Boolean),
    CoreF::IntegerLiteral(_) => Some(Ty::Integer),
    CoreF::Local(level) => lookup(ctx, level),
    CoreF::Constructor(item) => match entry(symb, item) {
        Some(ItemKind::Constructor(owner)) => Some(Ty::Nominal(owner)),
        _ => None,
    },
    CoreF::Unary(op, operand) => provided(operand.ctx = ctx, unary_result(op, operand.ty)),
    CoreF::Binary(op, left, right) => provided(
        left.ctx = ctx and right.ctx = ctx,
        binary_result(op, left.ty, right.ty)
    ),
    CoreF::Call(item, args) => match entry(symb, item) {
        Some(ItemKind::Function(sig)) => provided(
            in_context?(args, ctx) and argument_types?(args, sig.params),
            Some(sig.result)
        ),
        _ => None,
    },
    CoreF::Let(annotation, value, body) => provided(
        value.ctx = ctx
            and (annotation = None or annotation = Some(value.ty))
            and body.ctx = Extend(ctx, value.ty),
        Some(body.ty)
    ),
    CoreF::If(condition, then_branch, else_branch) => provided(
        condition.ctx = ctx
            and condition.ty = Ty::Boolean
            and then_branch.ctx = ctx
            and else_branch.ctx = ctx
            and then_branch.ty = else_branch.ty,
        Some(then_branch.ty)
    ),
    CoreF::Match(scrutinee, arms) => match scrutinee.ty, arms {
        Ty::Nominal(owner), Extend(_, last) => provided(
            scrutinee.ctx = ctx
                and arm_bodies?(arms, ctx, last.body.ty)
                and arm_patterns?(symb, arms, owner),
            Some(last.body.ty)
        ),
        _, _ => None,
    },
}

expect layer_inference(symb: Symb, ctx: Ctx, form: CoreF<Typing>, ty: Ty) {
    expect exact: rule?(symb, ctx, form, ty) iff infer_layer(symb, ctx, form) = Some(ty)
}
```

r[types.layer.call-arity] spec::types::call_arity::equal
If `argument_types?(args, Δ)`, then `|args| = |Δ|`.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc call_arity(args: Snoc<Typing>, params: Ctx): (holds?) {
    ensure output: holds?
    ensure equal: when argument_types?(args, params), length(args) = length(params)
}
```

r[types.layer.regularity] spec::types::{typings_ok?, arm_typings, children, children_ok?, layer_regularity::regular}
Typing produces well-formed types, layer by layer: if Σ and Γ are well
formed, every child typing's type is well formed and `Σ; Γ ⊢ l ▷ τ`, then
`Σ ⊢ τ ok`.

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
pub fn children(form: CoreF<Typing>): Snoc<Typing> := match form {
    CoreF::Unary(_, operand) => one(operand),
    CoreF::Binary(_, left, right) => two(left, right),
    CoreF::Call(_, args) => args,
    CoreF::Let(_, value, body) => two(value, body),
    CoreF::If(condition, then_branch, else_branch) => three(condition, then_branch, else_branch),
    CoreF::Match(scrutinee, arms) => Extend(arm_typings(arms), scrutinee),
    _ => Empty,
}

pub fn children_ok?(symb: Symb, form: CoreF<Typing>) := typings_ok?(symb, children(form))

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc layer_regularity(symb: Symb, ctx: Ctx, form: CoreF<Typing>, ty: Ty): (holds?) {
    ensure output: holds?
    ensure regular: when symb_ok?(symb) and ctx_ok?(symb, ctx) and children_ok?(symb, form)
        and rule?(symb, ctx, form, ty),
        ty_ok?(symb, ty)
}
```

r[types.derivation.regularity] spec::types::table_regularity::regular
In a valid table over a well-formed Σ, every row's type is well formed.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc table_regularity(symb: Symb, rows: Snoc<Row>, pos: Int, found: Row): (holds?) {
    ensure output: holds?
    ensure regular: when symb_ok?(symb) and rows_valid?(symb, rows) and lookup(rows, pos) = Some(found),
        ty_ok?(symb, found.ty)
}
```

r[types.judgment.regularity] spec::types::judgment_regularity::regular
If `derivation?(Σ, rows, Γ, τ)`, then `Σ ⊢ τ ok`: if `Σ; Γ ⊢ e : τ`, then τ
is well formed.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc judgment_regularity(symb: Symb, rows: Snoc<Row>, ctx: Ctx, ty: Ty): (holds?) {
    ensure output: holds?
    ensure regular: when derivation?(symb, rows, ctx, ty), ty_ok?(symb, ty)
}
```

r[types.derivation.scoped] spec::types::table_scoping::in_scope
Every local of a valid table is in scope: if a row `#i` has context Γ, then
`0 ≤ i < |Γ|`.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc table_scoping(symb: Symb, rows: Snoc<Row>, pos: Int, found: Row, level: Int): (holds?) {
    ensure output: holds?
    ensure in_scope: when rows_valid?(symb, rows) and lookup(rows, pos) = Some(found)
        and found.form = CoreF::Local(level),
        0 <= level < length(found.ctx)
}
```

r[types.derivation.unique] spec::types::{same_shape?, table_uniqueness::equal}
Typing is deterministic for a table: two valid tables with the same forms
and contexts, row by row, are equal, and so have the same types row by row.

```fren
pub fn same_shape?(left: Snoc<Row>, right: Snoc<Row>) := match left, right {
    Empty, Empty => true,
    Extend(left_earlier, l), Extend(right_earlier, r) =>
        l.form = r.form and l.ctx = r.ctx and same_shape?(left_earlier, right_earlier),
    _, _ => false,
}

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc table_uniqueness(symb: Symb, left: Snoc<Row>, right: Snoc<Row>): (holds?) {
    ensure output: holds?
    ensure equal: when rows_valid?(symb, left) and rows_valid?(symb, right) and same_shape?(left, right),
        left = right
}
```

r[types.layer.weakening] spec::types::{insert_type, weaken_typing, weaken_typings, weaken_arms, weaken_layer, layer_weakening::weakened}
A layer stays typed when a type σ is inserted at level n of its context and
of every child's context and every local level of at least n is shifted by
one, provided `0 ≤ n ≤ |Γ|`.

```fren
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

pub fn weaken_layer(form: CoreF<Typing>, cutoff: Int, extra: Ty): CoreF<Typing> := match form {
    CoreF::BooleanLiteral(value?) => CoreF::BooleanLiteral(value?),
    CoreF::IntegerLiteral(value) => CoreF::IntegerLiteral(value),
    CoreF::Local(level) => CoreF::Local(shift(level, cutoff)),
    CoreF::Constructor(item) => CoreF::Constructor(item),
    CoreF::Unary(op, operand) => CoreF::Unary(op, weaken_typing(operand, cutoff, extra)),
    CoreF::Binary(op, left, right) => CoreF::Binary(
        op,
        weaken_typing(left, cutoff, extra),
        weaken_typing(right, cutoff, extra)
    ),
    CoreF::Call(item, args) => CoreF::Call(item, weaken_typings(args, cutoff, extra)),
    CoreF::Let(annotation, value, body) => CoreF::Let(
        annotation,
        weaken_typing(value, cutoff, extra),
        weaken_typing(body, cutoff, extra)
    ),
    CoreF::If(condition, then_branch, else_branch) => CoreF::If(
        weaken_typing(condition, cutoff, extra),
        weaken_typing(then_branch, cutoff, extra),
        weaken_typing(else_branch, cutoff, extra)
    ),
    CoreF::Match(scrutinee, arms) => CoreF::Match(
        weaken_typing(scrutinee, cutoff, extra),
        weaken_arms(arms, cutoff, extra)
    ),
}

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc layer_weakening(
    symb: Symb,
    ctx: Ctx,
    form: CoreF<Typing>,
    ty: Ty,
    cutoff: Int,
    extra: Ty,
): (holds?) {
    ensure output: holds?
    ensure weakened: when 0 <= cutoff <= length(ctx) and rule?(symb, ctx, form, ty),
        rule?(
            symb,
            insert_type(ctx, cutoff, extra),
            weaken_layer(form, cutoff, extra),
            ty
        )
}
```

r[types.derivation.weakening-lookup] spec::types::lookup_shifting::{shifted, inserted}
The step for locals: if `0 ≤ n ≤ |Γ|`, the shifted level of i in Γ with σ
inserted at level n holds `Γ(i)`, and level n holds σ.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc lookup_shifting(ctx: Ctx, cutoff: Int, extra: Ty, level: Int): (holds?) {
    ensure output: holds?
    ensure shifted: when 0 <= cutoff <= length(ctx),
        lookup(insert_type(ctx, cutoff, extra), shift(level, cutoff)) = lookup(ctx, level)
    ensure inserted: when 0 <= cutoff <= length(ctx), lookup(insert_type(ctx, cutoff, extra), cutoff) = Some(extra)
}
```

r[types.derivation.weakening] spec::types::{weaken, contexts_reach?, table_weakening::valid}
A valid table stays valid when a well-formed type is inserted at level n of
every row's context and every local level of at least n is shifted by one,
provided `0 ≤ n` and every row's context has at least n entries.

```fren
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

-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc table_weakening(symb: Symb, rows: Snoc<Row>, cutoff: Int, extra: Ty): (holds?) {
    ensure output: holds?
    ensure valid: when ty_ok?(symb, extra) and 0 <= cutoff and rows_valid?(symb, rows)
        and contexts_reach?(rows, cutoff),
        rows_valid?(symb, weaken(rows, cutoff, extra))
}
```

r[types.judgment.weakening] spec::types::judgment_weakening::weakened
Typing is preserved by extending its context: if `derivation?(Σ, rows, Γ, τ)`
and `Σ ⊢ σ ok`, then `derivation?(Σ, weaken(rows, |Γ|, σ), (Γ, σ), τ)`. By
the definition of unfolding, the weakened root unfolds to e', the expression
e that the root unfolded to with every local level of at least `|Γ|`, those
bound within e, shifted by one; so if `Σ; Γ ⊢ e : τ` then `Σ; Γ, σ ⊢ e' : τ`.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc judgment_weakening(symb: Symb, rows: Snoc<Row>, ctx: Ctx, ty: Ty, extra: Ty): (holds?) {
    ensure output: holds?
    ensure weakened: when ty_ok?(symb, extra) and derivation?(symb, rows, ctx, ty),
        derivation?(
            symb,
            weaken(rows, length(ctx), extra),
            Extend(ctx, extra),
            ty
        )
}
```

r[types.safety]
Typing is sound for the dynamic semantics: in a well-typed, verified
program, evaluating a well-typed expression under values of its context's
types is defined and gives a value of its type, as the
[expressions chapter](Expressions.md#values-interpretation-and-mentioned-names)
defines evaluation. This needs the dynamic semantics as a Fren definition
and is open.

## Whole-expression properties

The properties in this section concern the expression that a table's root
unfolds to.

r[types.derivation.alike] spec::types::{Pair, paired?, children_paired?, arms_paired?, layers_paired?, pairs_agree?, alike?}
Two rows *unfold alike* when a set of position pairs that contains them
pairs every pair's layers: the same form and payloads, with each pair of
corresponding children, argument by argument and arm by arm, again a pair
of the set. `alike?(l, p, r, q, pairs)` checks that `pairs` is such a set
for the row at level p of l and the row at level q of r.

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
    CoreF::Unary(l_op, l), CoreF::Unary(r_op, r) => l_op = r_op and paired?(pairs, l, r),
    CoreF::Binary(l_op, l1, l2), CoreF::Binary(r_op, r1, r2) =>
        l_op = r_op and paired?(pairs, l1, r1) and paired?(pairs, l2, r2),
    CoreF::Call(l_item, l_args), CoreF::Call(r_item, r_args) =>
        l_item = r_item and children_paired?(pairs, l_args, r_args),
    CoreF::Let(l_annotation, l1, l2), CoreF::Let(r_annotation, r1, r2) =>
        l_annotation = r_annotation and paired?(pairs, l1, r1) and paired?(pairs, l2, r2),
    CoreF::If(l1, l2, l3), CoreF::If(r1, r2, r3) =>
        paired?(pairs, l1, r1) and paired?(pairs, l2, r2) and paired?(pairs, l3, r3),
    CoreF::Match(l1, l_arms), CoreF::Match(r1, r_arms) =>
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
The judgment agrees with the inductive reading of the rules: `Σ; Γ ⊢ e : τ`
holds exactly when Σ and Γ are well formed and a finite tree of rule
instances concludes it. Each node of the tree is an instance of the rule for
its form, with one subtree for each written child of the form, in the
context that the rule gives that child. The two well-formedness conditions
are part of the reading and do not follow from the tree: a rule with no
premises has an instance under any Σ and Γ. Fren cannot state the tree
reading, so no procedure states this law; it is proved in Lean beside the
chapter's wrapper. By it, [regularity](#r-types.judgment.regularity),
[weakening](#r-types.judgment.weakening) and the uniqueness below hold of an
expression and its trees as they do of tables.

r[types.derivation.unique-expression] spec::types::expression_uniqueness::unique
Typing is deterministic for an expression: if `derivation?(Σ, l, Γ, τ)` and
`derivation?(Σ, r, Γ, υ)` and their roots unfold alike, then τ = υ, whatever
the two tables' sharing of rows and extra rows.

```fren
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc expression_uniqueness(
    symb: Symb,
    ctx: Ctx,
    left: Snoc<Row>,
    right: Snoc<Row>,
    pairs: Snoc<Pair>,
    a: Ty,
    b: Ty,
): (holds?) {
    ensure output: holds?
    ensure unique: when derivation?(symb, left, ctx, a) and derivation?(symb, right, ctx, b)
        and alike?(left, length(left) - 1, right, length(right) - 1, pairs),
        a = b
}
```

r[types.judgment.decidability]
Typing is decidable: an algorithm, given Σ, Γ and e, finds the τ with
`Σ; Γ ⊢ e : τ` or reports that there is none. Building a table bottom-up
with `infer_layer`, in the contexts that `rule?` prescribes for the
children, is such an algorithm. This is open.

## Examples

r[types.examples.derivations] spec::types::{SIGNAL, SIGNAL_RED, F, bind, EXAMPLE_SYMB, SYMB, row, BOOLEAN_INTEGER, OLDEST_LEVEL_EXAMPLE, LET_EXAMPLE, MATCH_EXAMPLE, CALL_EXAMPLE, PROGRAM_EXAMPLE, worked_examples::valid}
Each accepted example below gives a Core judgment and a table that types
it, shown as rows numbered by level; its root, the last row, unfolds to the
judgment's expression. The procedure `worked_examples` states that each
example's table is valid with that root's context and type; the chapter's
wrapper proves it by evaluation, and also checks further tables, accepted
and rejected, at least one for each rule.

The examples use an enumeration `M::Light` with constructors `Red` and
`Green`, an enumeration `M::Signal` with constructor `Red`, and a function
`M::f` from Int to Int.

```fren
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

`Σ; ·, Bool, Int ⊢ #0 : Bool`: level 0 is the oldest entry.

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `#0` | `·, Bool, Int` | Bool |

`Σ; · ⊢ let x : Int := 1 in x : Int`: x is level 0, and the body's context is `·, Int`.

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `1` | `·` | Int |
| 1 | `#0` | `·, Int` | Int |
| 2 | `let x : Int := row 0 in row 1` | `·` | Int |

`Σ; · ⊢ match M::Light::Red { M::Light::Red ⇒ 1 | M::Light::Green ⇒ 2 } : Int`:

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `M::Light::Red` | `·` | `Nominal(M::Light)` |
| 1 | `1` | `·` | Int |
| 2 | `2` | `·` | Int |
| 3 | `match row 0 { M::Light::Red ⇒ row 1 \| M::Light::Green ⇒ row 2 }` | `·` | Int |

`Σ; · ⊢ M::f(1) : Int`:

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `1` | `·` | Int |
| 1 | `M::f(row 0)` | `·` | Int |

A program whose one function, `M::f`, has the body `#0 + 1` in its parameter
context `·, Int`, is well typed, with this table for the body:

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `#0` | `·, Int` | Int |
| 1 | `1` | `·, Int` | Int |
| 2 | `row 0 + row 1` | `·, Int` | Int |

```fren
pub const BOOLEAN_INTEGER: Ctx := two(Ty::Boolean, Ty::Integer)

pub const OLDEST_LEVEL_EXAMPLE: Bool := derivation?(
    SYMB,
    one(row(CoreF::Local(0), BOOLEAN_INTEGER, Ty::Boolean)),
    BOOLEAN_INTEGER,
    Ty::Boolean
)

pub const LET_EXAMPLE: Bool := derivation?(
    SYMB,
    three(
        row(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
        row(CoreF::Local(0), one(Ty::Integer), Ty::Integer),
        row(CoreF::Let(Some(Ty::Integer), 0, 1), Empty, Ty::Integer)
    ),
    Empty,
    Ty::Integer
)

pub const MATCH_EXAMPLE: Bool := derivation?(
    SYMB,
    four(
        row(CoreF::Constructor(LIGHT_RED), Empty, Ty::Nominal(LIGHT)),
        row(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
        row(CoreF::IntegerLiteral(2), Empty, Ty::Integer),
        row(
            CoreF::Match(
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
        row(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
        row(CoreF::Call(F, one(0)), Empty, Ty::Integer)
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
                row(CoreF::Local(0), one(Ty::Integer), Ty::Integer),
                row(CoreF::IntegerLiteral(1), one(Ty::Integer), Ty::Integer),
                row(
                    CoreF::Binary(BinaryOp::Add, 0, 1),
                    one(Ty::Integer),
                    Ty::Integer
                )
            )
        )
    )
)

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
-- TODO: make this law an `expect` once Fren lets a Lean proof discharge one;
-- `holds?` exists only to carry the evidence of the `impl` in the wrapper.
set_option fren.evidence "random" in
pub proc worked_examples(): (holds?) {
    ensure output: holds?
    ensure valid: OLDEST_LEVEL_EXAMPLE and LET_EXAMPLE and MATCH_EXAMPLE and CALL_EXAMPLE and PROGRAM_EXAMPLE
}
```

r[types.examples.rejected] spec::types::rejected::{out_of_scope, branches, foreign_pattern, no_arms, extra_argument}
Each rejected example is a layer that has no type, whatever the typings of
the children its premises leave free: the local `#0` in `·`; a conditional
whose branches have types Int and Bool, such as `1` and `false`; a
match on a value of `Nominal(a)` whose one arm's pattern is a constructor
of another enumeration; a match with no arms; and a call with two arguments
of a function with one parameter.
The call example also states the step it rests
on: one argument does not fit an empty parameter list.

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
    expect out_of_scope: not rule?(symb, Empty, CoreF::Local(0), ty)
    expect branches: when second.ty = Ty::Integer and third.ty = Ty::Boolean,
        not rule?(symb, ctx, CoreF::If(first, second, third), ty)
    expect foreign_pattern: when first.ty = Ty::Nominal(owner)
        and entry(symb, item) = Some(ItemKind::Constructor(other))
        and other != owner,
        not rule?(
            symb,
            ctx,
            CoreF::Match(first, one(ArmF { constructor := item, body := second })),
            ty
        )
    expect no_arms: not rule?(symb, ctx, CoreF::Match(first, Empty), ty)
    expect extra_argument: when entry(symb, item) = Some(
        ItemKind::Function(Sig { params := one(third.ty), result := ty })
    ),
        -- The first conjunct is the step that the second needs: a check unfolds
        -- `argument_types?` once, and this call fails at its second unfolding.
        not argument_types?(one(first), Empty)
        and not rule?(symb, ctx, CoreF::Call(item, two(first, second)), ty)
}
```

## Interface

r[types.overview.interface] spec::typing::{type_of, derives?}
The overview's interface: `derives?` and `type_of` are uninterpreted
functions over this chapter's types, whose contract states that a
derivation records the type it derives, that only well-formed environments
and contexts admit derivations, and that every derived type is well formed.
The chapter's wrapper interprets `derives?` by `derivation?` and `type_of`
by the type of a table's root, and so proves the contract for the detailed
definitions: the interpretation is the refinement relation.

```fren
pub mod spec::typing

use spec::names::{Ctx, Symb, Ty, ctx_ok?, symb_ok?, ty_ok?}
use spec::surface::Snoc
use spec::types::Row

pub fn type_of(Symb, Ctx, Snoc<Row>): Ty

pub fn derives?(symb: Symb, ctx: Ctx, rows: Snoc<Row>, ty: Ty): (holds?) {
    ensure records_type: when holds?, ty = type_of(symb, ctx, rows)
    ensure well_formed: when holds?, symb_ok?(symb) and ctx_ok?(symb, ctx)
    ensure regular: when holds?, ty_ok?(symb, ty)
}
```

r[types.overview.determinism] spec::typing::determinism::unique
A derivation derives at most one type, the type it records.

```fren
expect determinism(symb: Symb, ctx: Ctx, rows: Snoc<Row>, a: Ty, b: Ty) {
    expect unique: not derives?(symb, ctx, rows, a) or not derives?(symb, ctx, rows, b) or a = b
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
--@ reference: types.expression.let-annotated
pub mod bad

pub fn f(n: Int): Int := let b: Bool := n in 0  --~ error: the definition of `b` has type `Int`, not `Bool`
```

```fren example
--@ reference: names.surface.suffix
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

