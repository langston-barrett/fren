module

public import FrenExpr.Types
public import FrenSexp

/-! The phase-indexed expression core shared by HIR through flat.

Expressions are a one-layer functor `ExprF p R` whose recursive positions are
the parameter `R`; `Expr p` ties the knot and adds the per-node origin and the
phase's annotation. A form that exists only in some phases takes a gate, a
decidable `Prop` that is `False` elsewhere, so a pass dismisses forms that its
input phase cannot contain with `nomatch`/`absurd`. Traversals are derived
once from the functor (`ExprF.map`, `ExprF.children`, `Expr.fold`) and the
fold's universal property is proved here, once, for every pass written as a
fold. Locals are plain de Bruijn indices (nearest binder is zero); scoping is
the separate predicate `Expr.Scoped`, as the design's fallback encoding. -/

public section
namespace FrenExpr

open FrenAst (UnaryOp BinaryOp)

/-- The expression phases, in pipeline order. -/
inductive Phase where
  | hir | thir | dthir | mir | mono | fo | flat
  deriving Repr, BEq, DecidableEq

namespace Phase

/-- Forms that exist only before type checking decides what a resolved
reference denotes (a value, a constructor or a callee). -/
@[expose] def Untyped (p : Phase) : Prop := p = .hir

/-- Forms whose meaning the type checker decided. -/
@[expose] def Typed (p : Phase) : Prop := p ≠ .hir

/-- Surface forms kept for type errors and lints, removed by desugaring. -/
@[expose] def Surface (p : Phase) : Prop := p = .hir ∨ p = .thir

instance (p : Phase) : Decidable p.Untyped := inferInstanceAs (Decidable (p = .hir))
instance (p : Phase) : Decidable p.Typed := inferInstanceAs (Decidable (p ≠ .hir))
instance (p : Phase) : Decidable p.Surface := inferInstanceAs (Decidable (p = .hir ∨ p = .thir))

theorem untyped_not_typed {p : Phase} (h : p.Untyped) (h' : p.Typed) : False := h' h

end Phase

/-- Index into the enclosing item's origin table. Origins are message data
only: equality of expressions (`Expr.same`) ignores them. -/
abbrev OriginId := Nat

/-- What an origin records: the span (absent for generated terms) and the
display name of the variable or item it introduces, if any. -/
structure Origin where
  span : Option FrenSource.Span := none
  name : Option String := none
  deriving Repr, BEq

/-- Node annotations: nothing in HIR, a value type from THIR on. -/
@[expose] def Ann : Phase → Type
  | .hir => Unit
  | _ => Ty

instance instBEqAnn : (p : Phase) → BEq (Ann p)
  | .hir => inferInstanceAs (BEq Unit)
  | .thir | .dthir | .mir | .mono | .fo | .flat => inferInstanceAs (BEq Ty)

instance instReprAnn : (p : Phase) → Repr (Ann p)
  | .hir => inferInstanceAs (Repr Unit)
  | .thir | .dthir | .mir | .mono | .fo | .flat => inferInstanceAs (Repr Ty)

/-- A resolved reference before type checking decides its kind. -/
inductive Ref where
  | item (id : FrenBase.ItemId)
  | local (index : Nat)
  deriving Repr, BEq, DecidableEq

/-- The variable a `let` binds. Its display name lives in its origin. `suffix`
records that the name was written with `?`, which decides a typing rule, so it
is data on the node rather than origin. -/
structure Binder where
  origin : OriginId
  suffix : Bool
  deriving Repr, BEq, DecidableEq

/-- A constructor pattern of a `match` arm, with its own origin. -/
structure Pattern where
  origin : OriginId
  ctor : FrenBase.ItemId
  deriving Repr, BEq, DecidableEq

/-- One layer of an expression; `R` is the type of the recursive positions. -/
inductive ExprF (p : Phase) (R : Type) where
  | bool (value : Bool)
  | int (value : Nat)
  /-- A local variable, as a de Bruijn index (nearest binder is zero). -/
  | var (index : Nat)
  /-- A resolved item in value position; the type checker decides whether it
  is a constructor. -/
  | item (gate : p.Untyped) (id : FrenBase.ItemId)
  /-- A constructor value, as the type checker decided. -/
  | ctor (gate : p.Typed) (id : FrenBase.ItemId)
  /-- A call whose callee is a resolved reference, not yet checked callable. -/
  | apply (gate : p.Untyped) (callee : Ref) (args : Array R)
  /-- A call of a function, as the type checker decided. -/
  | call (gate : p.Typed) (fn : FrenBase.ItemId) (args : Array R)
  | unary (op : UnaryOp) (operand : R)
  | binary (op : BinaryOp) (left right : R)
  | ite (condition yes no : R)
  /-- `let` binds one variable in `body`, not in `value`. -/
  | letE (binder : Binder) (value body : R)
  /-- Arms in written order. -/
  | matchE (scrutinee : R) (arms : Array (Pattern × R))
  /-- Written parentheses, kept until desugaring. -/
  | paren (gate : p.Surface) (body : R)

namespace ExprF

variable {p : Phase} {R S : Type}

/-- The functor map: the one traversal every pass reuses. -/
@[expose] def map (f : R → S) : ExprF p R → ExprF p S
  | .bool v => .bool v
  | .int v => .int v
  | .var i => .var i
  | .item g id => .item g id
  | .ctor g id => .ctor g id
  | .apply g c args => .apply g c (args.map f)
  | .call g fn args => .call g fn (args.map f)
  | .unary op e => .unary op (f e)
  | .binary op l r => .binary op (f l) (f r)
  | .ite c y n => .ite (f c) (f y) (f n)
  | .letE s v b => .letE s (f v) (f b)
  | .matchE s arms => .matchE (f s) (arms.map fun (c, e) => (c, f e))
  | .paren g e => .paren g (f e)

/-- Children in written order. -/
@[expose] def children : ExprF p R → List R
  | .bool _ | .int _ | .var _ | .item _ _ | .ctor _ _ => []
  | .apply _ _ args | .call _ _ args => args.toList
  | .unary _ e | .paren _ e => [e]
  | .binary _ l r => [l, r]
  | .ite c y n => [c, y, n]
  | .letE _ v b => [v, b]
  | .matchE s arms => s :: arms.toList.map Prod.snd

/-- `map` with access to membership, used to define recursion once. -/
@[expose] def pmap : (e : ExprF p R) → ((r : R) → r ∈ e.children → S) → ExprF p S
  | .bool v, _ => .bool v
  | .int v, _ => .int v
  | .var i, _ => .var i
  | .item g id, _ => .item g id
  | .ctor g id, _ => .ctor g id
  | .apply g c args, f => .apply g c (args.attach.map fun ⟨a, h⟩ => f a (by simpa [children] using h))
  | .call g fn args, f => .call g fn (args.attach.map fun ⟨a, h⟩ => f a (by simpa [children] using h))
  | .unary op e, f => .unary op (f e (by simp [children]))
  | .binary op l r, f => .binary op (f l (by simp [children])) (f r (by simp [children]))
  | .ite c y n, f => .ite (f c (by simp [children])) (f y (by simp [children])) (f n (by simp [children]))
  | .letE s v b, f => .letE s (f v (by simp [children])) (f b (by simp [children]))
  | .matchE s arms, f => .matchE (f s (by simp [children]))
      (arms.attach.map fun ⟨(c, a), h⟩ => (c, f a (by
        simp only [children, List.mem_cons, List.mem_map]
        exact Or.inr ⟨(c, a), Array.mem_toList_iff.mpr h, rfl⟩)))
  | .paren g e, f => .paren g (f e (by simp [children]))

theorem pmap_eq_map (e : ExprF p R) (f : R → S) : e.pmap (fun r _ => f r) = e.map f := by
  cases e <;> simp [pmap, map, Array.map_attach_eq_pmap, Array.pmap_eq_map]

theorem map_id (e : ExprF p R) : e.map id = e := by
  cases e <;> simp [map]

theorem map_comp {T : Type} (e : ExprF p R) (f : R → S) (g : S → T) :
    (e.map f).map g = e.map (g ∘ f) := by
  cases e <;> simp [map, Function.comp_def]

theorem map_congr (e : ExprF p R) {f g : R → S} (h : ∀ r ∈ e.children, f r = g r) :
    e.map f = e.map g := by
  cases e <;> simp_all [map, children]
  all_goals first
    | (apply Array.map_congr_left; intro x hx; exact h x hx)
    | (intro x y hm; exact h.2 y x hm)
    | skip

theorem children_map (e : ExprF p R) (f : R → S) : (e.map f).children = e.children.map f := by
  cases e <;> simp [map, children, Function.comp_def]

end ExprF

/-- An expression of phase `p`: one layer whose recursive positions are again
expressions, with its origin and annotation. -/
structure Expr (p : Phase) where
  origin : OriginId
  ann : Ann p
  node : ExprF p (Expr p)

namespace Expr

variable {p : Phase} {S : Type}

theorem sizeOf_child (o : OriginId) (a : Ann p) (n : ExprF p (Expr p)) (c : Expr p)
    (h : c ∈ n.children) : sizeOf c < sizeOf (Expr.mk o a n) := by
  have : sizeOf c < sizeOf n := by
    cases n with
    | bool | int | var | item | ctor => simp [ExprF.children] at h
    | apply g callee args | call g fn args =>
      have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp h)
      simp only [ExprF.apply.sizeOf_spec, ExprF.call.sizeOf_spec]
      omega
    | unary op e | paren g e =>
      simp only [ExprF.children, List.mem_singleton] at h
      subst h
      simp only [ExprF.unary.sizeOf_spec, ExprF.paren.sizeOf_spec]
      omega
    | binary op l r =>
      simp only [ExprF.children, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [ExprF.binary.sizeOf_spec]
      rcases h with rfl | rfl <;> omega
    | ite x y z =>
      simp only [ExprF.children, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [ExprF.ite.sizeOf_spec]
      rcases h with rfl | rfl | rfl <;> omega
    | letE s v b =>
      simp only [ExprF.children, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [ExprF.letE.sizeOf_spec]
      rcases h with rfl | rfl <;> omega
    | matchE s arms =>
      simp only [ExprF.children, List.mem_cons, List.mem_map] at h
      simp only [ExprF.matchE.sizeOf_spec]
      rcases h with rfl | ⟨⟨k, v⟩, hm, rfl⟩
      · omega
      · have h1 := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp hm)
        simp only [Prod.mk.sizeOf_spec] at h1 ⊢
        omega
  simp only [Expr.mk.sizeOf_spec]
  omega

/-- The catamorphism: every fold pass is an algebra for it. -/
@[expose] def fold (alg : OriginId → Ann p → ExprF p S → S) : Expr p → S
  | ⟨o, a, n⟩ => alg o a (n.pmap fun c _ => fold alg c)
termination_by e => sizeOf e
decreasing_by exact sizeOf_child o a n c (by assumption)

theorem fold_mk (alg : OriginId → Ann p → ExprF p S → S) (o : OriginId) (a : Ann p)
    (n : ExprF p (Expr p)) : fold alg ⟨o, a, n⟩ = alg o a (n.map (fold alg)) := by
  rw [fold, ExprF.pmap_eq_map]

/-- The generic fold theorem: any function satisfying the fold's equation is
the fold. Proved once; a pass written as an algebra inherits it. -/
theorem fold_unique (alg : OriginId → Ann p → ExprF p S → S) (h : Expr p → S)
    (eqn : ∀ o a n, h ⟨o, a, n⟩ = alg o a (n.map h)) (e : Expr p) : h e = fold alg e := by
  match e with
  | ⟨o, a, n⟩ =>
    rw [eqn, fold_mk]
    congr 1
    exact ExprF.map_congr n fun c hc => fold_unique alg h eqn c
termination_by sizeOf e
decreasing_by exact sizeOf_child o a n c hc

/-- Postorder node count (a fold). -/
@[expose] def size : Expr p → Nat :=
  fold fun _ _ n => n.children.foldl (· + ·) 1

/-- Well-scopedness under `n` enclosing binders (a fold): every local index,
including a local callee, points at an enclosing binder. -/
@[expose] def scopedIn : Expr p → Nat → Bool :=
  fold fun _ _ n k => match n with
    | .var i => i < k
    | .apply _ (.local i) args => i < k && args.all (· k)
    | .letE _ v b => v k && b (k + 1)
    | n => n.children.all (· k)

/-- Erase the type checker's decisions and annotations (a fold). -/
@[expose] def eraseTypes : Expr .thir → Expr .hir :=
  fold fun o _ n => ⟨o, (), match n with
    | .bool v => .bool v
    | .int v => .int v
    | .var i => .var i
    | .item g _ => absurd g (by decide)
    | .ctor _ id => .item rfl id
    | .apply g _ _ => absurd g (by decide)
    | .call _ fn args => .apply rfl (.item fn) args
    | .unary op e => .unary op e
    | .binary op l r => .binary op l r
    | .ite c y n => .ite c y n
    | .letE b v e => .letE b v e
    | .matchE s arms => .matchE s arms
    | .paren _ e => .paren (Or.inl rfl) e⟩

end Expr

/-! ### The S-expression form

One printer for every phase. By default it omits origins, so equal printed
forms are the design's structural equality ("origins are excluded from
equality"); `origins := true` prints them too, for exact comparisons. -/

namespace Sexp
open Fren (Sexp)

@[expose] def item (id : FrenBase.ItemId) : Sexp :=
  .list <| id.components.toArray.map fun
    | .named n => .string n
    | .generated k i => .list #[.string k, Sexp.symbol (toString i)]

@[expose] def ty : Ty → Sexp
  | .bool => Sexp.symbol "Bool"
  | .int => Sexp.symbol "Int"
  | .enum id => .list #[Sexp.symbol "enum", item id]

@[expose] def ann : (p : Phase) → Ann p → Option Sexp
  | .hir, _ => none
  | .thir, t | .dthir, t | .mir, t | .mono, t | .fo, t | .flat, t => some (ty t)

@[expose] def unary : UnaryOp → String
  | .neg => "neg" | .not => "not"

@[expose] def binary : BinaryOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .and => "and" | .or => "or" | .iff => "iff"

end Sexp

namespace Expr
open Fren (Sexp)

variable {p : Phase}

/-- Print an expression (a fold). -/
@[expose] def toSexp (origins : Bool := false) : Expr p → Sexp :=
  fold fun o a n =>
    let nat (k : Nat) := Sexp.symbol (toString k)
    let header := (if origins then #[Sexp.list #[Sexp.symbol "@", nat o]] else #[]) ++
      (FrenExpr.Sexp.ann p a).toArray
    let at_ (k : Nat) := if origins then #[Sexp.list #[Sexp.symbol "@", nat k]] else #[]
    let node (tag : String) (rest : Array Sexp) := Sexp.list (#[Sexp.symbol tag] ++ header ++ rest)
    match n with
    | .bool v => node "bool" #[Sexp.symbol (toString v)]
    | .int v => node "int" #[nat v]
    | .var i => node "var" #[nat i]
    | .item _ id => node "item" #[FrenExpr.Sexp.item id]
    | .ctor _ id => node "ctor" #[FrenExpr.Sexp.item id]
    | .apply _ (.item id) args => node "apply" (#[FrenExpr.Sexp.item id] ++ args)
    | .apply _ (.local i) args => node "apply-local" (#[nat i] ++ args)
    | .call _ fn args => node "call" (#[FrenExpr.Sexp.item fn] ++ args)
    | .unary op e => node (FrenExpr.Sexp.unary op) #[e]
    | .binary op l r => node (FrenExpr.Sexp.binary op) #[l, r]
    | .ite c y e => node "if" #[c, y, e]
    | .letE b v e => node "let"
        (#[Sexp.list (#[Sexp.symbol (if b.suffix then "suffix" else "plain")] ++ at_ b.origin), v, e])
    | .matchE s arms => node "match" (#[s] ++ arms.map fun (pat, e) =>
        Sexp.list (#[FrenExpr.Sexp.item pat.ctor] ++ at_ pat.origin ++ #[e]))
    | .paren _ e => node "paren" #[e]

/-- Structural equality that ignores origins. -/
@[expose] def same (a b : Expr p) : Bool := a.toSexp == b.toSexp

end Expr

end FrenExpr
