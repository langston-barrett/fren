import Fren.Impl
import Fren.Literate
import Spec.Compiler.Thir
import FrenThirDesugar

open Fren.Lang

#fren_md "Desugaring.md"

namespace Spec.Compiler.Desugaring
open FrenModule FrenAst

/-! ## The desugaring pass

`FrenThirDesugar.desugar` maps the THIR module to the desugared THIR module.
The contract below is stated over the production expression and module types
as relations of their own. They do not mention the production functions
(`step`, `desugarExpr`, `desugarItem`, `desugar`); the theorems then relate
the two. -/

section Pass
open FrenExpr FrenModule.Core

/-- `Erases e d`: `d` is `e` with its parentheses erased and everything else
kept. A parenthesis has whatever its body has, at any depth, so the result of
`((x))` is the result of `x`. Every other node relates to a node of the same
form with the same origin, the same type and the same data, over related
children in the same order. -/
inductive Erases : Expr .thir → Expr .dthir → Prop where
  | paren : Erases e d → Erases ⟨o, ty, .paren g e⟩ d
  | bool : Erases ⟨o, ty, .bool v⟩ ⟨o, ty, .bool v⟩
  | int : Erases ⟨o, ty, .int v⟩ ⟨o, ty, .int v⟩
  | var : Erases ⟨o, ty, .var i⟩ ⟨o, ty, .var i⟩
  | ctor : Erases ⟨o, ty, .ctor g k⟩ ⟨o, ty, .ctor g' k⟩
  | call {args : Array (Expr .thir)} {args' : Array (Expr .dthir)} :
      args'.size = args.size →
      (∀ i (h : i < args.size) (h' : i < args'.size), Erases args[i] args'[i]) →
      Erases ⟨o, ty, .call g callee args⟩ ⟨o, ty, .call g' callee args'⟩
  | unary : Erases e d → Erases ⟨o, ty, .unary op e⟩ ⟨o, ty, .unary op d⟩
  | binary : Erases l l' → Erases r r' →
      Erases ⟨o, ty, .binary op l r⟩ ⟨o, ty, .binary op l' r'⟩
  | ite : Erases c c' → Erases y y' → Erases n n' →
      Erases ⟨o, ty, .ite c y n⟩ ⟨o, ty, .ite c' y' n'⟩
  | letE : Erases v v' → Erases b b' →
      Erases ⟨o, ty, .letE x v b⟩ ⟨o, ty, .letE x v' b'⟩
  | matchE {o : OriginId} {ty : FrenExpr.Ty} {s : Expr .thir} {s' : Expr .dthir}
      {arms : Array (Pattern × Expr .thir)} {arms' : Array (Pattern × Expr .dthir)} :
      Erases s s' → arms'.size = arms.size →
      (∀ i (h : i < arms.size) (h' : i < arms'.size), arms'[i].1 = arms[i].1) →
      (∀ i (h : i < arms.size) (h' : i < arms'.size), Erases arms[i].2 arms'[i].2) →
      Erases ⟨o, ty, .matchE s arms⟩ ⟨o, ty, .matchE s' arms'⟩

/-- The production pass satisfies the specification. -/
theorem desugar_sound : (e : Expr .thir) → Erases e (FrenThirDesugar.desugarExpr e)
  | ⟨o, ty, n⟩ => by
    rw [FrenThirDesugar.desugarExpr_mk]
    cases n with
    | bool v => exact .bool
    | int v => exact .int
    | var i => exact .var
    | item g _ => exact absurd g (by decide)
    | ctor g id => exact .ctor
    | apply g _ _ => exact absurd g (by decide)
    | call g callee args =>
      exact .call (by simp) fun i h h' => by simpa using desugar_sound args[i]
    | unary op e => exact .unary (desugar_sound e)
    | binary op l r => exact .binary (desugar_sound l) (desugar_sound r)
    | ite c y n => exact .ite (desugar_sound c) (desugar_sound y) (desugar_sound n)
    | letE x v b => exact .letE (desugar_sound v) (desugar_sound b)
    | matchE s arms =>
      exact .matchE (desugar_sound s) (by simp) (fun i h h' => by simp)
        fun i h h' => by simpa using desugar_sound arms[i].2
    | paren g e => exact .paren (desugar_sound e)
termination_by e => sizeOf e
decreasing_by
  all_goals apply Expr.sizeOf_child
  all_goals first
    | (simp [ExprF.children]; done)
    | exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem _), rfl⟩)

/-- The specification determines the result: whatever it relates to an input
is the production pass's output. -/
theorem desugar_unique {e : Expr .thir} {d : Expr .dthir} (h : Erases e d) :
    d = FrenThirDesugar.desugarExpr e := by
  induction h with
  | paren _ ih => rw [FrenThirDesugar.desugarExpr_paren]; exact ih
  | bool | int | var | ctor => rw [FrenThirDesugar.desugarExpr_mk]; rfl
  | call hs _ ih =>
    rw [FrenThirDesugar.desugarExpr_mk]
    have : _ = Array.map FrenThirDesugar.desugarExpr _ :=
      Array.ext (by simpa using hs) fun i h1 h2 => by simpa using ih i (by simpa using h2) h1
    rw [this]; rfl
  | unary _ ih => rw [FrenThirDesugar.desugarExpr_mk]; subst ih; rfl
  | binary _ _ ih1 ih2 => rw [FrenThirDesugar.desugarExpr_mk]; subst ih1 ih2; rfl
  | ite _ _ _ ih1 ih2 ih3 => rw [FrenThirDesugar.desugarExpr_mk]; subst ih1 ih2 ih3; rfl
  | letE _ _ ih1 ih2 => rw [FrenThirDesugar.desugarExpr_mk]; subst ih1 ih2; rfl
  | @matchE o ty s s' arms arms' _ hs hp _ ihs ih =>
    rw [FrenThirDesugar.desugarExpr_mk]
    have : arms' = arms.map fun (c, e) => (c, FrenThirDesugar.desugarExpr e) :=
      Array.ext (by simpa using hs) fun i h1 h2 => by
        have h3 : i < arms.size := by simpa using h2
        exact Prod.ext (by simpa using hp i h3 h1) (by simpa using ih i h3 h1)
    subst ihs this; rfl

/-- The relation is exactly the graph of the production pass. -/
theorem erases_iff (e : Expr .thir) (d : Expr .dthir) :
    Erases e d ↔ d = FrenThirDesugar.desugarExpr e :=
  ⟨desugar_unique, fun h => h ▸ desugar_sound e⟩

/-- Nested parentheses: the result carries the origin and type of the
innermost body's result, not of any parenthesis. -/
example (o₁ o₂ o : OriginId) (t₁ t₂ ty : FrenExpr.Ty) (g₁ g₂) (i : Nat) :
    FrenThirDesugar.desugarExpr ⟨o₁, t₁, .paren g₁ ⟨o₂, t₂, .paren g₂ ⟨o, ty, .var i⟩⟩⟩ =
      ⟨o, ty, .var i⟩ :=
  (desugar_unique (.paren (.paren .var))).symm

/-- The output phase admits no parenthesis, so none can remain. -/
theorem output_has_no_paren (n : ExprF .dthir (Expr .dthir)) (g) (e) :
    n ≠ .paren g e :=
  fun _ => FrenThirDesugar.no_surface g

/-- One member: same kind, label and origin, over a related body. -/
def ErasesMember (m : Member (Expr .thir)) (m' : Member (Expr .dthir)) : Prop :=
  m'.kind = m.kind ∧ m'.label = m.label ∧ m'.origin = m.origin ∧ Erases m.body m'.body

/-- One item: an enum is unchanged; a function keeps its identity, origin,
parameters and result type over a related body; a check keeps its identity,
origin and parameters, and its members one for one in order. The origin table
is the same table. An item never changes kind. -/
def ErasesItem : Item (Expr .thir) → Item (Expr .dthir) → Prop
  | .enum e os, .enum e' os' => e' = e ∧ os' = os
  | .function f os, .function f' os' =>
    f'.id = f.id ∧ f'.origin = f.origin ∧ f'.params = f.params ∧ f'.result = f.result ∧
      Erases f.body f'.body ∧ os' = os
  | .check c os, .check c' os' =>
    c'.id = c.id ∧ c'.origin = c.origin ∧ c'.params = c.params ∧
      c'.members.size = c.members.size ∧
      (∀ i (h : i < c.members.size) (h' : i < c'.members.size),
        ErasesMember c.members[i] c'.members[i]) ∧ os' = os
  | _, _ => False

/-- The module: same identity, and items one for one in declaration order. -/
def ErasesModule (m : Thir) (d : FrenThirDesugar.Dthir) : Prop :=
  d.id = m.id ∧ d.items.size = m.items.size ∧
    ∀ i (h : i < m.items.size) (h' : i < d.items.size), ErasesItem m.items[i] d.items[i]

theorem item_sound (i : Item (Expr .thir)) : ErasesItem i (FrenThirDesugar.desugarItem i) := by
  cases i with
  | «enum» e os => exact ⟨rfl, rfl⟩
  | function f os => exact ⟨rfl, rfl, rfl, rfl, desugar_sound _, rfl⟩
  | check c os =>
    refine ⟨rfl, rfl, rfl, by simp, fun i h h' => ?_, rfl⟩
    simp only [Array.getElem_map]
    exact ⟨rfl, rfl, rfl, desugar_sound _⟩

theorem member_unique {m : Member (Expr .thir)} {m' : Member (Expr .dthir)}
    (h : ErasesMember m m') : m' = {m with body := FrenThirDesugar.desugarExpr m.body} := by
  obtain ⟨k, l, o, b⟩ := m
  obtain ⟨k', l', o', b'⟩ := m'
  obtain ⟨hk, hl, ho, hb⟩ := h
  dsimp only at hk hl ho hb
  subst hk hl ho
  rw [desugar_unique hb]

theorem item_unique {i : Item (Expr .thir)} {d : Item (Expr .dthir)} (h : ErasesItem i d) :
    d = FrenThirDesugar.desugarItem i := by
  cases i with
  | «enum» e os =>
    cases d with
    | «enum» e' os' => obtain ⟨rfl, rfl⟩ := h; rfl
    | function _ _ | check _ _ => exact h.elim
  | function f os =>
    cases d with
    | function f' os' =>
      obtain ⟨id, o, ps, res, b⟩ := f
      obtain ⟨id', o', ps', res', b'⟩ := f'
      obtain ⟨h1, h2, h3, h4, hb, rfl⟩ := h
      dsimp only at h1 h2 h3 h4 hb
      subst h1 h2 h3 h4
      rw [desugar_unique hb]; rfl
    | «enum» _ _ | check _ _ => exact h.elim
  | check c os =>
    cases d with
    | check c' os' =>
      obtain ⟨id, o, ps, ms⟩ := c
      obtain ⟨id', o', ps', ms'⟩ := c'
      obtain ⟨h1, h2, h3, hs, hm, rfl⟩ := h
      dsimp only at h1 h2 h3 hs hm
      subst h1 h2 h3
      have : ms' = ms.map fun m => {m with body := FrenThirDesugar.desugarExpr m.body} :=
        Array.ext (by simpa using hs) fun i h1 h2 => by
          have h3 : i < ms.size := by simpa using h2
          simpa using member_unique (hm i h3 h1)
      subst this; rfl
    | «enum» _ _ | function _ _ => exact h.elim

/-- The production pass satisfies the module specification. -/
theorem module_sound (m : Thir) : ErasesModule m (FrenThirDesugar.desugar m) := by
  refine ⟨rfl, by simp [FrenThirDesugar.desugar], fun i h h' => ?_⟩
  simp only [FrenThirDesugar.desugar, Array.getElem_map]
  exact item_sound _

/-- The module specification determines the output module. -/
theorem module_unique {m : Thir} {d : FrenThirDesugar.Dthir} (h : ErasesModule m d) :
    d = FrenThirDesugar.desugar m := by
  obtain ⟨id, items⟩ := d
  obtain ⟨hid, hs, hi⟩ := h
  dsimp only at hid hs hi
  subst hid
  have : items = m.items.map FrenThirDesugar.desugarItem :=
    Array.ext (by simpa using hs) fun i h1 h2 => by
      have h3 : i < m.items.size := by simpa using h2
      simpa using item_unique (hi i h3 h1)
  subst this; rfl

end Pass

#print axioms desugar_unique
#print axioms module_unique
#print axioms desugar_sound
#print axioms module_sound

end Spec.Compiler.Desugaring
