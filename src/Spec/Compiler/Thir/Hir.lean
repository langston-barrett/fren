import Spec.Compiler.Thir

/-!
# HIR expressions as trees

`HirF` is the one layer of a HIR expression (`thir.algorithmic.layer`). This
module makes it a `Spec.Tables.Layer` and ties the knot: `Hir` is the type of
whole HIR expressions, which Fren cannot define. `Hir.fold` is its recursor
for one-layer algebras, `Hir.ind` its induction principle, and `desugar` the
desugaring `|e|` of `desugaring.pass.parens`, which replaces every
parenthesis by its body.
-/

open Fren.Lang

namespace Spec.Compiler.Thir

open spec.surface spec.names spec.types spec.algorithmic
open Spec.Tables

/-- Map over the subexpressions of one layer. -/
def mapH {α β : Type} (f : α → β) : HirF α → HirF β
  | .Core l => .Core (mapF f l)
  | .Paren e => .Paren (f e)

/-- The subexpressions of one layer. -/
def childrenH {α : Type} : HirF α → List α
  | .Core l => childrenF l
  | .Paren e => [e]

instance : Layer HirF where
  map := mapH
  children := childrenH
  map_id l := by
    cases l with
    | Core l => exact congrArg HirF.Core (Layer.map_id (F := CoreF) l)
    | Paren e => rfl
  map_map f g l := by
    cases l with
    | Core l => exact congrArg HirF.Core (Layer.map_map (F := CoreF) f g l)
    | Paren e => rfl
  children_map f l := by
    cases l with
    | Core l => exact Layer.children_map (F := CoreF) f l
    | Paren e => rfl
  map_congr f g l h := by
    cases l with
    | Core l => exact congrArg HirF.Core (Layer.map_congr (F := CoreF) f g l h)
    | Paren e => simp only [mapH]; rw [h e (by simp [childrenH])]
  zip f g l m h := by
    cases l with
    | Core l =>
      cases m with
      | Core m =>
        simp only [mapH, HirF.Core.injEq] at h
        obtain ⟨z, h1, h2, h3⟩ := Layer.zip (F := CoreF) f g l m h
        exact ⟨.Core z, congrArg HirF.Core h1, congrArg HirF.Core h2, h3⟩
      | Paren e => simp [mapH] at h
    | Paren x =>
      cases m with
      | Core m => simp [mapH] at h
      | Paren y =>
        simp only [mapH, HirF.Paren.injEq] at h
        exact ⟨.Paren (x, y), rfl, rfl, by simp [childrenH, h]⟩

/-- A HIR expression: a tree whose every layer is a `HirF`. -/
inductive Hir : Type
  | mk : HirF Hir → Hir

instance : Nonempty Hir := ⟨.mk (.Core (.BooleanLiteral true))⟩

mutual
/-- The fold of a one-layer algebra over an expression. -/
def Hir.fold {β : Type} (alg : HirF β → β) : Hir → β
  | .mk l => alg (foldH alg l)
def foldH {β : Type} (alg : HirF β → β) : HirF Hir → HirF β
  | .Core l => .Core (foldC alg l)
  | .Paren e => .Paren (Hir.fold alg e)
def foldC {β : Type} (alg : HirF β → β) : CoreF Hir → CoreF β
  | .BooleanLiteral b => .BooleanLiteral b
  | .IntegerLiteral n => .IntegerLiteral n
  | .Local level => .Local level
  | .Constructor item => .Constructor item
  | .Unary op x => .Unary op (Hir.fold alg x)
  | .Binary op x y => .Binary op (Hir.fold alg x) (Hir.fold alg y)
  | .Call item args => .Call item (foldS alg args)
  | .Let annotation value body => .Let annotation (Hir.fold alg value) (Hir.fold alg body)
  | .If c t e => .If (Hir.fold alg c) (Hir.fold alg t) (Hir.fold alg e)
  | .Match scrutinee arms => .Match (Hir.fold alg scrutinee) (foldA alg arms)
def foldS {β : Type} (alg : HirF β → β) : Snoc Hir → Snoc β
  | .Empty => .Empty
  | .Extend earlier x => .Extend (foldS alg earlier) (Hir.fold alg x)
def foldA {β : Type} (alg : HirF β → β) : Snoc (ArmF Hir) → Snoc (ArmF β)
  | .Empty => .Empty
  | .Extend earlier arm => .Extend (foldA alg earlier) (foldArm alg arm)
def foldArm {β : Type} (alg : HirF β → β) : ArmF Hir → ArmF β
  | ⟨constructor, body⟩ => ⟨constructor, Hir.fold alg body⟩
end

theorem foldS_eq {β : Type} (alg : HirF β → β) (xs : Snoc Hir) :
    foldS alg xs = mapS (Hir.fold alg) xs := by
  induction xs with
  | Empty => simp [foldS, mapS]
  | Extend e x ih => simp [foldS, mapS, ih]

theorem foldA_eq {β : Type} (alg : HirF β → β) (xs : Snoc (ArmF Hir)) :
    foldA alg xs = mapS (mapArm (Hir.fold alg)) xs := by
  induction xs with
  | Empty => simp [foldA, mapS]
  | Extend e x ih => cases x; simp [foldA, foldArm, mapS, mapArm, ih]

/-- The fold computes one layer from the folds of its children. -/
theorem Hir.fold_mk {β : Type} (alg : HirF β → β) (l : HirF Hir) :
    Hir.fold alg (.mk l) = alg (mapH (Hir.fold alg) l) := by
  rw [Hir.fold]
  congr 1
  cases l with
  | Paren e => simp [foldH, mapH]
  | Core l => cases l <;> simp [foldH, foldC, mapH, mapF, foldS_eq, foldA_eq]

/-- The number of nodes of an expression. -/
def Hir.size (e : Hir) : Nat := Hir.fold (fun l => 1 + (childrenH l).sum) e

theorem mem_le_sum (xs : List Nat) (x : Nat) (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => nomatch h
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem Hir.size_child (l : HirF Hir) (c : Hir) (h : c ∈ childrenH l) :
    c.size < (Hir.mk l).size := by
  have hs : (Hir.mk l).size = 1 + ((childrenH l).map Hir.size).sum := by
    unfold Hir.size
    rw [Hir.fold_mk, show childrenH (mapH _ l) = _ from Layer.children_map (F := HirF) _ l]
    rfl
  rw [hs]
  have := mem_le_sum _ c.size (List.mem_map.2 ⟨c, h, rfl⟩)
  omega

/-- Induction on expressions: a property that holds of an expression when it
holds of its children holds of every expression. -/
theorem Hir.ind {P : Hir → Prop} (h : ∀ l, (∀ c ∈ childrenH l, P c) → P (.mk l)) :
    ∀ e, P e := by
  suffices hn : ∀ (n : Nat) (e : Hir), e.size < n → P e from fun e => hn _ e (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he
    cases e with
    | mk l => exact h l (fun c hc => ih c (by have := Hir.size_child l c hc; omega))

/-- The desugaring `|e|`: the Core expression with every parenthesis replaced by its body. -/
def desugar : Hir → Core :=
  Hir.fold fun
    | .Core l => .mk l
    | .Paren body => body

theorem desugar_core (l : CoreF Hir) : desugar (.mk (.Core l)) = .mk (mapF desugar l) := by
  unfold desugar; rw [Hir.fold_mk]; rfl

theorem desugar_paren (e : Hir) : desugar (.mk (.Paren e)) = desugar e := by
  unfold desugar; rw [Hir.fold_mk]; rfl

end Spec.Compiler.Thir
