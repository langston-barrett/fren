module

public import FrenGen.Thir

/-! Parentheses anywhere: the input generator of the desugaring pass.

`FrenGen.Thir` writes a parenthesis only where the printed source needs one.
A THIR module may hold one around any node, and several around the same node,
and all of these are well typed (a parenthesis has its body's type). `parens`
adds them to a generated module: for each node, the salt and the node's origin
decide whether it gets none, one or two. The result is well typed exactly when
its argument is, and no existing node changes: each item's origin table only
grows, by two entries for every old one, and the new parentheses take their
origins from the added part. -/

public section
namespace FrenGen.Thir
open FrenExpr FrenModule.Core

/-- How many parentheses the node of origin `o` gets: none for half the
nodes, one for a quarter and two for a quarter. -/
def parenCount (salt : Nat) (o : OriginId) : Nat :=
  match (hash (salt, o)).toNat % 4 with
  | 0 => 2
  | 1 => 1
  | _ => 0

/-- Wrap the nodes of one body; `base` is the size of the item's origin table. -/
def parensExpr (salt base : Nat) : Expr .thir → Expr .thir :=
  Expr.fold fun o ty n =>
    let e : Expr .thir := ⟨o, ty, n⟩
    let wrap (k : Nat) (e : Expr .thir) : Expr .thir := ⟨base + 2 * o + k, ty, .paren (Or.inr rfl) e⟩
    match parenCount salt o with
    | 0 => e
    | 1 => wrap 0 e
    | _ => wrap 0 (wrap 1 e)

def parensItem (salt : Nat) : Item (Expr .thir) → Item (Expr .thir)
  | .enum e os => .enum e os
  | .function f os =>
    .function {f with body := parensExpr salt os.size f.body} (os ++ Array.replicate (2 * os.size) {})
  | .check c os =>
    .check {c with members := c.members.map fun m => {m with body := parensExpr salt os.size m.body}}
      (os ++ Array.replicate (2 * os.size) {})

/-- The module with parentheses added around its nodes, as `salt` decides. -/
def parens (salt : Nat) (m : Thir) : Thir := ⟨m.id, m.items.map (parensItem salt)⟩

/-- How many parentheses an expression holds (a fold). -/
def parenNodes : Expr .thir → Nat :=
  Expr.fold fun _ _ n => n.children.foldl (· + ·) (match n with | .paren _ _ => 1 | _ => 0)

end FrenGen.Thir
