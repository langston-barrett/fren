module

public import FrenModule.Core

/-! THIR → desugared THIR, over the THIR module alone.

The input is the type checker's output, `FrenModule.Core.Thir`; the pass reads
no source text, syntax tree or resolver table, and runs no other pass. It is a
fold of each body (`Expr.fold step`) that drops the forms the `Surface` gate
marks: today, written parentheses. A parenthesised expression becomes its
desugared body, so it carries the origin and annotation of that result: for
`((x))` those of `x`, with both parentheses' origins removed. Every other node
is rebuilt with its origin and type over its desugared children. The output phase cannot hold a surface form at all
(`no_surface`), so that invariant needs no check. Items are independent: an
item's output depends on that item only. -/

public section
namespace FrenThirDesugar
open FrenExpr FrenModule.Core

/-- A module of desugared THIR expressions. -/
abbrev Dthir := Module (Expr .dthir)

/-- The output phase has no surface form. -/
theorem no_surface : ¬ Phase.Surface .dthir := by decide

/-- One layer: a parenthesis gives its (already desugared) body; any other
node is the same node over the desugared children. -/
@[expose] def step (o : OriginId) (ty : Ann .thir) : ExprF .thir (Expr .dthir) → Expr .dthir
  | .bool v => ⟨o, ty, .bool v⟩
  | .int v => ⟨o, ty, .int v⟩
  | .var i => ⟨o, ty, .var i⟩
  | .item g _ => absurd g (by decide)
  | .ctor _ id => ⟨o, ty, .ctor (by decide) id⟩
  | .apply g _ _ => absurd g (by decide)
  | .call _ fn args => ⟨o, ty, .call (by decide) fn args⟩
  | .unary op e => ⟨o, ty, .unary op e⟩
  | .binary op l r => ⟨o, ty, .binary op l r⟩
  | .ite c y n => ⟨o, ty, .ite c y n⟩
  | .letE b v e => ⟨o, ty, .letE b v e⟩
  | .matchE s arms => ⟨o, ty, .matchE s arms⟩
  | .paren _ e => e

/-- Desugar one expression (a fold). -/
@[expose] def desugarExpr : Expr .thir → Expr .dthir := Expr.fold step

/-- Desugar one item: its bodies only. Identities, signatures, member kinds
and labels, and the origin table are kept. -/
@[expose] def desugarItem : Item (Expr .thir) → Item (Expr .dthir)
  | .enum e os => .enum e os
  | .function f os => .function {f with body := desugarExpr f.body} os
  | .check c os =>
    .check {c with members := c.members.map fun m => {m with body := desugarExpr m.body}} os

/-- Desugar a module, item by item in declaration order. The pass is total:
it has no error of its own. -/
@[expose] def desugar (m : Thir) : Dthir := ⟨m.id, m.items.map desugarItem⟩

/-- The pass's defining equation, by which it is the unique such function
(`Expr.fold_unique`). -/
theorem desugarExpr_mk (o : OriginId) (ty : Ann .thir) (n : ExprF .thir (Expr .thir)) :
    desugarExpr ⟨o, ty, n⟩ = step o ty (n.map desugarExpr) := Expr.fold_mk step o ty n

/-- A parenthesised expression desugars to what its body desugars to. -/
theorem desugarExpr_paren (o : OriginId) (ty : Ann .thir) (g : Phase.Surface .thir) (e : Expr .thir) :
    desugarExpr ⟨o, ty, .paren g e⟩ = desugarExpr e := by
  rw [desugarExpr_mk]; rfl

/-- Nested parentheses give the innermost body's result, with its origin and
type: neither parenthesis's origin or annotation survives. -/
theorem desugarExpr_nested (o₁ o₂ o : OriginId) (t₁ t₂ ty : Ann .thir)
    (g₁ g₂ : Phase.Surface .thir) (i : Nat) :
    desugarExpr ⟨o₁, t₁, .paren g₁ ⟨o₂, t₂, .paren g₂ ⟨o, ty, .var i⟩⟩⟩ = ⟨o, ty, .var i⟩ := by
  rw [desugarExpr_paren, desugarExpr_paren, desugarExpr_mk]; rfl

/-- Any node but a parenthesis keeps its origin and its type. -/
theorem desugarExpr_keeps (o : OriginId) (ty : Ann .thir) (n : ExprF .thir (Expr .thir))
    (h : ∀ g e, n ≠ .paren g e) :
    (desugarExpr ⟨o, ty, n⟩).origin = o ∧ (desugarExpr ⟨o, ty, n⟩).ann = ty := by
  rw [desugarExpr_mk]
  cases n with
  | item g _ => exact absurd g (by decide)
  | apply g _ _ => exact absurd g (by decide)
  | paren g e => exact absurd rfl (h g e)
  | _ => exact ⟨rfl, rfl⟩

/-- Items are desugared one for one, in order, each from itself alone. -/
theorem desugar_items (m : Thir) : (desugar m).items = m.items.map desugarItem := rfl

theorem desugarItem_id (i : Item (Expr .thir)) : (desugarItem i).id = i.id := by
  cases i <;> rfl

theorem desugarItem_origins (i : Item (Expr .thir)) : (desugarItem i).origins = i.origins := by
  cases i <;> rfl

end FrenThirDesugar
