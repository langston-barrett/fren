import Spec.Compiler.Thir.Adequacy

/-!
# Inference

`inferTable` computes a synthesis table from a HIR expression. It walks the
expression once, children before parents and in order, and adds one row for
each node. A node's context is the one that its parent's rule prescribes
(`placed?`), and its type is what `synth_layer` gives for its children's
types. It then returns the table and the root's type if `synthesis?` accepts
them.

* `inferTable_sound`: a table that inference returns is accepted by
  `synthesis?`, and its root unfolds to the expression.
* `inferTable_complete`: inference returns a table with the type τ whenever
  `Synth` holds of the expression at τ.
* `infer_iff` joins them, and `Synth` is decidable by it.

`travH` is the traversal of one layer that threads a state through its
children, and `travH_spec` is its specification.
-/

open Fren.Lang

namespace Spec.Compiler.Thir

open spec.surface spec.names spec.types spec.algorithmic
open Spec.Tables Spec.Language.Types

/-! ## Traversal of one layer with a state -/

section Traverse

variable {α β γ σ : Type}

/-- Run `g` on each element of a snoc-list, earliest first, threading the state. -/
def travS (g : α → σ → β × σ) : Snoc α → σ → Snoc β × σ
  | .Empty, s => (.Empty, s)
  | .Extend earlier x, s =>
    let r := travS g earlier s
    let q := g x r.2
    (.Extend r.1 q.1, q.2)

/-- Run `g` on the body of each arm, earliest first, threading the state. -/
def travA (g : α → σ → β × σ) : Snoc (ArmF α) → σ → Snoc (ArmF β) × σ
  | .Empty, s => (.Empty, s)
  | .Extend earlier arm, s =>
    let r := travA g earlier s
    let q := g arm.body r.2
    (.Extend r.1 ⟨arm.constructor, q.1⟩, q.2)

/-- Run `g` on each child of a Core layer, in order, threading the state. -/
def travF (g : α → σ → β × σ) : CoreF α → σ → CoreF β × σ
  | .BooleanLiteral b, s => (.BooleanLiteral b, s)
  | .IntegerLiteral n, s => (.IntegerLiteral n, s)
  | .Local level, s => (.Local level, s)
  | .Constructor item, s => (.Constructor item, s)
  | .Unary op x, s =>
    let r := g x s
    (.Unary op r.1, r.2)
  | .Binary op x y, s =>
    let r := g x s
    let q := g y r.2
    (.Binary op r.1 q.1, q.2)
  | .Call item args, s =>
    let r := travS g args s
    (.Call item r.1, r.2)
  | .Let annotation value body, s =>
    let r := g value s
    let q := g body r.2
    (.Let annotation r.1 q.1, q.2)
  | .If c t e, s =>
    let r := g c s
    let q := g t r.2
    let u := g e q.2
    (.If r.1 q.1 u.1, u.2)
  | .Match scrutinee arms, s =>
    let r := g scrutinee s
    let q := travA g arms r.2
    (.Match r.1 q.1, q.2)

/-- Run `g` on each child of a HIR layer, in order, threading the state. -/
def travH (g : α → σ → β × σ) : HirF α → σ → HirF β × σ
  | .Core l, s =>
    let r := travF g l s
    (.Core r.1, r.2)
  | .Paren e, s =>
    let r := g e s
    (.Paren r.1, r.2)

/-- What a traversal preserves: an invariant `Inv` of the state, a preorder
`Rel` in which the state only grows, and a property `P` of a child and its
result that survives growth. -/
structure Thread (Inv : σ → Prop) (Rel : σ → σ → Prop) (P : γ → β → σ → Prop) : Prop where
  refl : ∀ s, Rel s s
  trans : ∀ {a b c}, Rel a b → Rel b c → Rel a c
  mono : ∀ {c b s s'}, P c b s → Rel s' s → P c b s'

/-- `g` keeps the invariant on the child `c`, grows the state and establishes `P`. -/
def Steps (Inv : σ → Prop) (Rel : σ → σ → Prop) (P : γ → β → σ → Prop)
    (g : α → σ → β × σ) (π : γ → α) (c : γ) : Prop :=
  ∀ s, Inv s → Inv (g (π c) s).2 ∧ Rel (g (π c) s).2 s ∧ P c (g (π c) s).1 (g (π c) s).2

variable {Inv : σ → Prop} {Rel : σ → σ → Prop} {P : γ → β → σ → Prop}

theorem travS_spec (T : Thread Inv Rel P) (g : α → σ → β × σ) (π : γ → α) (xs : Snoc γ)
    (h : ∀ c ∈ toList xs, Steps Inv Rel P g π c) (s : σ) (hs : Inv s) :
    Inv (travS g (mapS π xs) s).2 ∧ Rel (travS g (mapS π xs) s).2 s ∧
      ∃ zs : Snoc (γ × β), mapS Prod.fst zs = xs ∧ mapS Prod.snd zs = (travS g (mapS π xs) s).1 ∧
        ∀ c ∈ toList zs, P c.1 c.2 (travS g (mapS π xs) s).2 := by
  induction xs with
  | Empty => exact ⟨hs, T.refl s, .Empty, rfl, rfl, fun _ hc => nomatch hc⟩
  | Extend e x ih =>
    obtain ⟨h1, h2, zs, e1, e2, h3⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    obtain ⟨k1, k2, k3⟩ := h x List.mem_cons_self _ h1
    refine ⟨k1, T.trans k2 h2, .Extend zs (x, (g (π x) (travS g (mapS π e) s).2).1), ?_, ?_, ?_⟩
    · simp only [mapS, e1]
    · simp only [mapS, e2]; rfl
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact k3
      · exact T.mono (h3 c hc) k2

theorem travA_spec (T : Thread Inv Rel P) (g : α → σ → β × σ) (π : γ → α) (xs : Snoc (ArmF γ))
    (h : ∀ c ∈ toList xs, Steps Inv Rel P g π c.body) (s : σ) (hs : Inv s) :
    Inv (travA g (mapS (mapArm π) xs) s).2 ∧ Rel (travA g (mapS (mapArm π) xs) s).2 s ∧
      ∃ zs : Snoc (ArmF (γ × β)), mapS (mapArm Prod.fst) zs = xs ∧
        mapS (mapArm Prod.snd) zs = (travA g (mapS (mapArm π) xs) s).1 ∧
        ∀ c ∈ toList zs, P c.body.1 c.body.2 (travA g (mapS (mapArm π) xs) s).2 := by
  induction xs with
  | Empty => exact ⟨hs, T.refl s, .Empty, rfl, rfl, fun _ hc => nomatch hc⟩
  | Extend e x ih =>
    obtain ⟨h1, h2, zs, e1, e2, h3⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    obtain ⟨k1, k2, k3⟩ := h x List.mem_cons_self _ h1
    refine ⟨k1, T.trans k2 h2,
      .Extend zs ⟨x.constructor, (x.body, (g (π x.body) (travA g (mapS (mapArm π) e) s).2).1)⟩,
      ?_, ?_, ?_⟩
    · simp only [mapS, e1]; rfl
    · simp only [mapS, e2]; rfl
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact k3
      · exact T.mono (h3 c hc) k2

theorem travF_spec (T : Thread Inv Rel P) (g : α → σ → β × σ) (π : γ → α) (l : CoreF γ)
    (h : ∀ c ∈ childrenF l, Steps Inv Rel P g π c) (s : σ) (hs : Inv s) :
    Inv (travF g (mapF π l) s).2 ∧ Rel (travF g (mapF π l) s).2 s ∧
      ∃ z : CoreF (γ × β), mapF Prod.fst z = l ∧ mapF Prod.snd z = (travF g (mapF π l) s).1 ∧
        ∀ c ∈ childrenF z, P c.1 c.2 (travF g (mapF π l) s).2 := by
  cases l with
  | BooleanLiteral b => exact ⟨hs, T.refl s, .BooleanLiteral b, rfl, rfl, by simp [childrenF]⟩
  | IntegerLiteral n => exact ⟨hs, T.refl s, .IntegerLiteral n, rfl, rfl, by simp [childrenF]⟩
  | Local level => exact ⟨hs, T.refl s, .Local level, rfl, rfl, by simp [childrenF]⟩
  | Constructor item => exact ⟨hs, T.refl s, .Constructor item, rfl, rfl, by simp [childrenF]⟩
  | Unary op x =>
    obtain ⟨k1, k2, k3⟩ := h x (by simp [childrenF]) s hs
    exact ⟨k1, k2, .Unary op (x, (g (π x) s).1), rfl, rfl, fun c hc => by rw [List.mem_singleton.1 hc]; exact k3⟩
  | Binary op x y =>
    obtain ⟨k1, k2, k3⟩ := h x (by simp [childrenF]) s hs
    obtain ⟨m1, m2, m3⟩ := h y (by simp [childrenF]) _ k1
    refine ⟨m1, T.trans m2 k2, .Binary op (x, (g (π x) s).1) (y, (g (π y) (g (π x) s).2).1),
      rfl, rfl, ?_⟩
    intro c hc
    simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact T.mono k3 m2
    · exact m3
  | Call item args =>
    obtain ⟨k1, k2, zs, e1, e2, k3⟩ := travS_spec T g π args (fun c hc => h c hc) s hs
    exact ⟨k1, k2, .Call item zs, congrArg (CoreF.Call item) e1, congrArg (CoreF.Call item) e2, k3⟩
  | Let ann x y =>
    obtain ⟨k1, k2, k3⟩ := h x (by simp [childrenF]) s hs
    obtain ⟨m1, m2, m3⟩ := h y (by simp [childrenF]) _ k1
    refine ⟨m1, T.trans m2 k2, .Let ann (x, (g (π x) s).1) (y, (g (π y) (g (π x) s).2).1),
      rfl, rfl, ?_⟩
    intro c hc
    simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact T.mono k3 m2
    · exact m3
  | If x y w =>
    obtain ⟨k1, k2, k3⟩ := h x (by simp [childrenF]) s hs
    obtain ⟨m1, m2, m3⟩ := h y (by simp [childrenF]) _ k1
    obtain ⟨n1, n2, n3⟩ := h w (by simp [childrenF]) _ m1
    refine ⟨n1, T.trans n2 (T.trans m2 k2),
      .If (x, (g (π x) s).1) (y, (g (π y) (g (π x) s).2).1)
        (w, (g (π w) (g (π y) (g (π x) s).2).2).1), rfl, rfl, ?_⟩
    intro c hc
    simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact T.mono k3 (T.trans n2 m2)
    · exact T.mono m3 n2
    · exact n3
  | Match x arms =>
    obtain ⟨k1, k2, k3⟩ := h x (by simp [childrenF]) s hs
    obtain ⟨m1, m2, zs, e1, e2, m3⟩ := travA_spec T g π arms
      (fun c hc => h c.body (List.mem_cons_of_mem _ (List.mem_map.2 ⟨c, hc, rfl⟩))) _ k1
    refine ⟨m1, T.trans m2 k2, .Match (x, (g (π x) s).1) zs,
      congrArg (CoreF.Match x) e1, congrArg (CoreF.Match (g (π x) s).1) e2, ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact T.mono k3 m2
    · obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 hc
      exact m3 c0 h0

/-- The traversal of a layer keeps the invariant, grows the state and pairs
each child with a result that satisfies `P` in the final state, when `g`
does so for each child. -/
theorem travH_spec (T : Thread Inv Rel P) (g : α → σ → β × σ) (π : γ → α) (l : HirF γ)
    (h : ∀ c ∈ childrenH l, Steps Inv Rel P g π c) (s : σ) (hs : Inv s) :
    Inv (travH g (mapH π l) s).2 ∧ Rel (travH g (mapH π l) s).2 s ∧
      ∃ z : HirF (γ × β), mapH Prod.fst z = l ∧ mapH Prod.snd z = (travH g (mapH π l) s).1 ∧
        ∀ c ∈ childrenH z, P c.1 c.2 (travH g (mapH π l) s).2 := by
  cases l with
  | Core b =>
    obtain ⟨k1, k2, z, e1, e2, k3⟩ := travF_spec T g π b (fun c hc => h c hc) s hs
    exact ⟨k1, k2, .Core z, congrArg HirF.Core e1, congrArg HirF.Core e2, k3⟩
  | Paren x =>
    obtain ⟨k1, k2, k3⟩ := h x (by simp [childrenH]) s hs
    exact ⟨k1, k2, .Paren (x, (g (π x) s).1), rfl, rfl, fun c hc => by rw [List.mem_singleton.1 hc]; exact k3⟩

end Traverse

/-! ## The contexts of a layer's children -/

/-- What inference computes of an expression in a context: its type, and the
rows that it adds to a table. -/
abbrev Built : Type := Ty × (Snoc HirRow → Snoc HirRow)

/-- Each child of a Core layer in the context that `placed_core?` prescribes:
the body of a let in Γ extended by the value's type, and every other child in Γ. -/
def scopeF (ctx : Snoc Ty) : CoreF (Snoc Ty → Built) → CoreF (Snoc Ty × Built)
  | .Let annotation value body =>
    .Let annotation (ctx, value ctx)
      (.Extend ctx (value ctx).1, body (.Extend ctx (value ctx).1))
  | l => mapF (fun x => (ctx, x ctx)) l

/-- Each child of a layer in the context that `placed?` prescribes. -/
def scopeH (ctx : Snoc Ty) : HirF (Snoc Ty → Built) → HirF (Snoc Ty × Built)
  | .Core l => .Core (scopeF ctx l)
  | .Paren body => .Paren (ctx, body ctx)

/-- Every child of a layer gets some context. -/
theorem scope_shape {γ : Type} (ctx : Snoc Ty) (π : γ → Snoc Ty → Built) (l : HirF γ) :
    ∃ z : HirF (γ × Snoc Ty), mapH Prod.fst z = l ∧
      scopeH ctx (mapH π l) = mapH (fun c => (c.2, π c.1 c.2)) z := by
  cases l with
  | Paren x => exact ⟨.Paren (x, ctx), rfl, rfl⟩
  | Core b =>
    cases b with
    | Let ann v w => exact ⟨.Core (.Let ann (v, ctx) (w, .Extend ctx (π v ctx).1)), rfl, rfl⟩
    | _ =>
      refine ⟨.Core (mapF (fun c : γ => (c, ctx)) _), congrArg HirF.Core
        ((Layer.map_map (F := CoreF) (fun c : γ => (c, ctx)) Prod.fst _).trans
          (Layer.map_id (F := CoreF) _)), congrArg HirF.Core ?_⟩
      exact (Layer.map_map (F := CoreF) π (fun x => (ctx, x ctx)) _).trans
        (Layer.map_map (F := CoreF) (fun c : γ => (c, ctx))
          (fun c : γ × Snoc Ty => (c.2, π c.1 c.2)) _).symm

/-- The children of a rule instance get the contexts of its premises, when
each premise's type is the type computed for its child. -/
theorem scope_placed {γ : Type} (symb : Snoc Entry) (π : γ → Snoc Ty → Built)
    (a : HirF (γ × Typing)) (j : Typing) (hr : HRule symb (mapH Prod.snd a) j)
    (hty : ∀ c ∈ childrenH a, (π c.1 c.2.ctx).1 = c.2.ty) :
    scopeH j.ctx (mapH (fun c => π c.1) a) = mapH (fun c => (c.2.ctx, π c.1 c.2.ctx)) a := by
  cases a with
  | Paren t =>
    have ht : t.2 = j := (hrule_paren symb t.2 j).1 hr
    show HirF.Paren (j.ctx, π t.1 j.ctx) = HirF.Paren (t.2.ctx, π t.1 t.2.ctx)
    rw [ht]
  | Core b =>
    have hctx := rule_child_ctx symb j.ctx (mapF Prod.snd b) j.ty ((hrule_core symb _ j).1 hr)
    cases b with
    | Let ann v w =>
      obtain ⟨hv, hb⟩ : v.2.ctx = j.ctx ∧ w.2.ctx = .Extend j.ctx v.2.ty := hctx
      have hvt : (π v.1 v.2.ctx).1 = v.2.ty := hty v (by simp [childrenH, childrenF])
      show HirF.Core (.Let ann (j.ctx, π v.1 j.ctx)
          (.Extend j.ctx (π v.1 j.ctx).1, π w.1 (.Extend j.ctx (π v.1 j.ctx).1)))
        = HirF.Core (.Let ann (v.2.ctx, π v.1 v.2.ctx) (w.2.ctx, π w.1 w.2.ctx))
      rw [hb, ← hvt, hv]
    | _ =>
      refine congrArg HirF.Core ((Layer.map_map (F := CoreF) (fun c : γ × Typing => π c.1)
        (fun x => (j.ctx, x j.ctx)) _).trans (Layer.map_congr (F := CoreF) _ _ _ (fun c hc => ?_)))
      show (j.ctx, π c.1 j.ctx) = (c.2.ctx, π c.1 c.2.ctx)
      rw [hctx c.2 (mem_map_of_mem (F := CoreF) Prod.snd hc)]

/-! ## Building the table -/

/-- The type that the synthesis rule gives a layer whose children have the
computed contexts and types. It is the Boolean type when the rule gives none;
`inferTable` rejects the table then. -/
def rowTy (symb : Snoc Entry) (ctx : Snoc Ty) (sc : HirF (Snoc Ty × Built)) : Ty :=
  (synth_layer symb ctx (mapH (fun p => (⟨p.1, p.2.1⟩ : Typing)) sc)).getD .Boolean

/-- Add a child's rows to the table and give the position of its root. -/
def child (p : Snoc Ty × Built) (s : Snoc HirRow) : Int × Snoc HirRow :=
  let s' := p.2.2 s
  ((length HirRow s' : Int) - 1, s')

/-- Inference of one layer from the inference of its children: it adds the
children's rows in order and then the layer's row. -/
def buildAlg (symb : Snoc Entry) (l : HirF (Snoc Ty → Built)) (ctx : Snoc Ty) : Built :=
  (rowTy symb ctx (scopeH ctx l), fun s =>
    let r := travH child (scopeH ctx l) s
    .Extend r.2 ⟨r.1, ctx, rowTy symb ctx (scopeH ctx l)⟩)

/-- Inference of an expression in a context: its type and the rows it adds. -/
def build (symb : Snoc Entry) : Hir → Snoc Ty → Built := Hir.fold (buildAlg symb)

theorem build_mk (symb : Snoc Entry) (l : HirF Hir) (ctx : Snoc Ty) :
    build symb (.mk l) ctx = buildAlg symb (mapH (build symb) l) ctx := by
  unfold build; rw [Hir.fold_mk]

/-- The table and type that inference computes for an expression in a
context, when `synthesis?` accepts them. -/
def inferTable (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) : Option (Snoc HirRow × Ty) :=
  let b := build symb e ctx
  if synthesis? symb (b.2 .Empty) ctx b.1 = true then some (b.2 .Empty, b.1) else none

/-- The type that inference computes for an expression in a context. -/
def infer (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) : Option Ty :=
  (inferTable symb ctx e).map Prod.snd

/-! ## Soundness and completeness -/

/-- The rows of a child in its premise's context, as `scope_placed` gives them. -/
abbrev premise (symb : Snoc Entry) (c : Hir × Typing) : Snoc Ty × Built :=
  (c.2.ctx, build symb c.1 c.2.ctx)

theorem rowTy_placed (symb : Snoc Entry) (a : HirF (Hir × Typing)) (j : Typing)
    (hr : HRule symb (mapH Prod.snd a) j)
    (hty : ∀ c ∈ childrenH a, (build symb c.1 c.2.ctx).1 = c.2.ty) :
    rowTy symb j.ctx (mapH (premise symb) a) = j.ty := by
  have e2 : mapH (fun p : Snoc Ty × Built => (⟨p.1, p.2.1⟩ : Typing)) (mapH (premise symb) a)
      = mapH Prod.snd a :=
    (Layer.map_map (F := HirF) (premise symb)
      (fun p : Snoc Ty × Built => (⟨p.1, p.2.1⟩ : Typing)) a).trans
      (Layer.map_congr (F := HirF) _ _ a (fun c hc => by
        show (⟨c.2.ctx, (build symb c.1 c.2.ctx).1⟩ : Typing) = c.2
        rw [hty c hc]))
  have hs : synth_layer symb j.ctx (mapH Prod.snd a) = some j.ty := hr
  unfold rowTy
  rw [e2, hs]; rfl

theorem build_scope (symb : Snoc Entry) (a : HirF (Hir × Typing)) (j : Typing)
    (hr : HRule symb (mapH Prod.snd a) j)
    (hty : ∀ c ∈ childrenH a, (build symb c.1 c.2.ctx).1 = c.2.ty) :
    scopeH j.ctx (mapH (build symb) (mapH Prod.fst a)) = mapH (premise symb) a :=
  (congrArg (scopeH j.ctx) (Layer.map_map (F := HirF) Prod.fst (build symb) a)).trans
    (scope_placed symb (build symb) a j hr hty)

/-- Inference computes the type of every tree of rule instances. -/
theorem build_type (symb : Snoc Entry) {e : Hir} {j : Typing}
    (h : Derives Hir.mk (HRule symb) e j) : (build symb e j.ctx).1 = j.ty := by
  induction h with
  | node a j _ hr ih =>
    rw [build_mk]
    show rowTy symb j.ctx (scopeH j.ctx (mapH (build symb) (mapH Prod.fst a))) = j.ty
    rw [build_scope symb a j hr ih]
    exact rowTy_placed symb a j hr ih

/-- Inference extends a valid table to a valid table whose newest row
concludes the judgment of a tree of rule instances. -/
theorem build_valid (symb : Snoc Entry) (R : HirF Typing → Typing → Prop)
    (hR : ∀ l j, R l j → HRule symb l j) {e : Hir} {j : Typing} (h : Derives Hir.mk R e j) :
    ∀ s, Valid hirView R s →
      Valid hirView R ((build symb e j.ctx).2 s) ∧ Extends ((build symb e j.ctx).2 s) s ∧
      ∃ r, lookup HirRow ((build symb e j.ctx).2 s)
          ((length HirRow ((build symb e j.ctx).2 s) : Int) - 1) = some r ∧
        hirView.concl r = j := by
  induction h with
  | node a j hch hr ih =>
    intro s hv
    have hty : ∀ c ∈ childrenH a, (build symb c.1 c.2.ctx).1 = c.2.ty :=
      fun c hc => build_type symb (Derives.mono hR (hch c hc))
    have T : Thread (Valid hirView R) Extends (fun (c : Hir × Typing) (p : Int) st =>
        ∃ r, lookup HirRow st p = some r ∧ hirView.concl r = c.2) :=
      ⟨Extends.refl, Extends.trans, fun ⟨r, hl, hcl⟩ he => ⟨r, he _ _ hl, hcl⟩⟩
    obtain ⟨k1, k2, z, e1, e2, k3⟩ := travH_spec T child (premise symb) a
      (fun c hc st hst => ih c hc st hst) s hv
    have hb : (build symb (Hir.mk (mapH Prod.fst a)) j.ctx).2 s
        = .Extend (travH child (mapH (premise symb) a) s).2
            ⟨(travH child (mapH (premise symb) a) s).1, j.ctx, j.ty⟩ := by
      rw [build_mk]
      show Snoc.Extend
          (travH child (scopeH j.ctx (mapH (build symb) (mapH Prod.fst a))) s).2
          ⟨(travH child (scopeH j.ctx (mapH (build symb) (mapH Prod.fst a))) s).1, j.ctx,
            rowTy symb j.ctx (scopeH j.ctx (mapH (build symb) (mapH Prod.fst a)))⟩ = _
      rw [build_scope symb a j (hR _ _ hr) hty, rowTy_placed symb a j (hR _ _ hr) hty]
    show Valid hirView R ((build symb (Hir.mk (mapH Prod.fst a)) j.ctx).2 s) ∧
      Extends ((build symb (Hir.mk (mapH Prod.fst a)) j.ctx).2 s) s ∧
      ∃ r, lookup HirRow ((build symb (Hir.mk (mapH Prod.fst a)) j.ctx).2 s)
          ((length HirRow ((build symb (Hir.mk (mapH Prod.fst a)) j.ctx).2 s) : Int) - 1) = some r ∧
        hirView.concl r = j
    rw [hb]
    generalize travH child (mapH (premise symb) a) s = t at k1 k2 e2 k3
    refine ⟨(valid_extend _ _ _ _).2 ⟨k1, mapH (fun c => (c.2, c.1.2)) z, ?_, ?_, ?_⟩,
      (Extends.extend _ _).trans k2, ⟨t.1, j.ctx, j.ty⟩, ?_, ?_⟩
    · exact (Layer.map_map (F := HirF) (fun c : (Hir × Typing) × Int => (c.2, c.1.2)) Prod.fst z).trans e2
    · have hm : mapH Prod.snd (mapH (fun c : (Hir × Typing) × Int => (c.2, c.1.2)) z)
          = mapH Prod.snd a := by
        refine (Layer.map_map (F := HirF) (fun c : (Hir × Typing) × Int => (c.2, c.1.2))
          Prod.snd z).trans ?_
        rw [← e1]
        exact (Layer.map_map (F := HirF) Prod.fst Prod.snd z).symm
      show R (mapH Prod.snd (mapH (fun c : (Hir × Typing) × Int => (c.2, c.1.2)) z)) j
      rw [hm]; exact hr
    · intro c hc
      obtain ⟨c0, h0, rfl⟩ := List.mem_map.1
        ((Layer.children_map (F := HirF) _ z) ▸ hc)
      obtain ⟨r, hl, hcl⟩ := k3 c0 h0
      exact ⟨lookup_lt hl, r, hl, hcl⟩
    · rw [hir_root_position, lookup_extend, if_pos rfl]
    · rfl

/-- The rows that inference adds extend the table, and the newest unfolds to
the expression. -/
theorem build_unfolds (symb : Snoc Entry) (e : Hir) : ∀ (ctx : Snoc Ty) (s : Snoc HirRow),
    Extends ((build symb e ctx).2 s) s ∧
      Unfolds hirView Hir.mk ((build symb e ctx).2 s)
        ((length HirRow ((build symb e ctx).2 s) : Int) - 1) e := by
  induction e using Hir.ind with
  | h l ih =>
    intro ctx s
    obtain ⟨zc, ec1, ec2⟩ := scope_shape ctx (build symb) l
    have T : Thread (fun _ : Snoc HirRow => True) Extends
        (fun (c : Hir × Snoc Ty) (p : Int) st => Unfolds hirView Hir.mk st p c.1) :=
      ⟨Extends.refl, Extends.trans, fun hu he => hu.mono he⟩
    obtain ⟨-, k2, z, e1, e2, k3⟩ := travH_spec T child
      (fun c : Hir × Snoc Ty => (c.2, build symb c.1 c.2)) zc
      (fun c hc st _ => ⟨trivial, ih c.1 (ec1 ▸ mem_map_of_mem (F := HirF) Prod.fst hc) c.2 st⟩)
      s trivial
    rw [← ec2] at k2 e2 k3
    have hb : (build symb (Hir.mk l) ctx).2 s
        = .Extend (travH child (scopeH ctx (mapH (build symb) l)) s).2
            ⟨(travH child (scopeH ctx (mapH (build symb) l)) s).1, ctx,
              rowTy symb ctx (scopeH ctx (mapH (build symb) l))⟩ := by
      rw [build_mk]; rfl
    rw [hb]
    generalize travH child (scopeH ctx (mapH (build symb) l)) s = t at k2 e2 k3
    refine ⟨(Extends.extend _ _).trans k2, ?_⟩
    rw [hir_root_position]
    have hu := Unfolds.node (V := hirView) (con := Hir.mk)
      (rows := .Extend t.2 ⟨t.1, ctx, rowTy symb ctx (scopeH ctx (mapH (build symb) l))⟩)
      (length HirRow t.2) ⟨t.1, ctx, rowTy symb ctx (scopeH ctx (mapH (build symb) l))⟩
      (mapH (fun c : (Hir × Snoc Ty) × Int => (c.2, c.1.1)) z)
      (lookup_extend _ _ _ |>.trans (if_pos rfl))
      ((Layer.map_map (F := HirF) (fun c : (Hir × Snoc Ty) × Int => (c.2, c.1.1)) Prod.fst z).trans e2)
      (fun c hc => by
        obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 ((Layer.children_map (F := HirF) _ z) ▸ hc)
        exact (k3 c0 h0).mono (Extends.extend _ _))
    have hm : mapH Prod.snd (mapH (fun c : (Hir × Snoc Ty) × Int => (c.2, c.1.1)) z) = l := by
      refine (Layer.map_map (F := HirF) (fun c : (Hir × Snoc Ty) × Int => (c.2, c.1.1))
        Prod.snd z).trans ?_
      rw [← ec1, ← e1]
      exact (Layer.map_map (F := HirF) Prod.fst Prod.fst z).symm
    exact hm ▸ hu

/-- Soundness of inference: a table that it returns is accepted by
`synthesis?` for the type it returns, and its root unfolds to the expression. -/
theorem inferTable_sound (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (rows : Snoc HirRow)
    (ty : Ty) (h : inferTable symb ctx e = some (rows, ty)) :
    synthesis? symb rows ctx ty = true ∧ HRootUnfolds rows e := by
  unfold inferTable at h
  dsimp only at h
  split at h
  · next hs =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨hs, (build_unfolds symb e ctx .Empty).2⟩
  · nomatch h

/-- Completeness of inference: it returns a table with the type of every
expression that the rules type. -/
theorem inferTable_complete (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty)
    (h : Synth symb ctx e ty) :
    inferTable symb ctx e = some ((build symb e ctx).2 .Empty, ty) := by
  have h2 := Derives.strengthen (F := HirF) (fun j : Typing => extends? j.ctx ctx = true)
    (fun l j hr hq => hrule_extends symb ctx l j hr hq) (synth_contexts_ok symb ctx e ty h)
    (extends_refl ctx)
  obtain ⟨hv, -, r, hl, hcl⟩ := build_valid symb _ (fun _ _ hr => hr.1.2) h2 .Empty
    (Valid.empty _ _)
  have hty : (build symb e ctx).1 = ty := build_type symb h.2.2
  have hs : synthesis? symb ((build symb e ctx).2 .Empty) ctx ty = true := by
    change Valid hirView _ ((build symb e ctx).2 .Empty) at hv
    change lookup HirRow ((build symb e ctx).2 .Empty)
      ((length HirRow ((build symb e ctx).2 .Empty) : Int) - 1) = some r at hl
    generalize (build symb e ctx).2 .Empty = rows at hv hl
    cases rows with
    | Empty => simp [lookup] at hl
    | Extend earlier root =>
      rw [hir_root_position, lookup_extend, if_pos rfl] at hl
      obtain rfl := Option.some.inj hl
      exact synthesis_of_valid symb ctx ty earlier root h.1 h.2.1 hv hcl
  unfold inferTable
  simp only [hty, hs, if_true]

/-- `Σ; Γ ⊢ e ⇒ τ` holds exactly when inference computes τ for e in Γ. -/
theorem infer_iff (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty) :
    infer symb ctx e = some ty ↔ Synth symb ctx e ty := by
  constructor
  · intro h
    obtain ⟨⟨rows, ty'⟩, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hs, hu⟩ := inferTable_sound symb ctx e rows ty' ht
    exact (synthesis_adequate symb ctx e ty').1 ⟨rows, hs, hu⟩
  · intro h
    unfold infer
    rw [inferTable_complete symb ctx e ty h]; rfl

/-- The synthesis judgment is decidable: inference decides it. -/
instance (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty) :
    Decidable (Synth symb ctx e ty) :=
  decidable_of_iff _ (infer_iff symb ctx e ty)

/-- Whether an expression has some type in a context is decidable too. -/
instance (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) :
    Decidable (∃ ty, Synth symb ctx e ty) :=
  decidable_of_iff ((infer symb ctx e).isSome = true)
    ⟨fun h => ⟨(infer symb ctx e).get h, (infer_iff symb ctx e _).1 (Option.some_get h).symm⟩,
      fun ⟨ty, h⟩ => by rw [(infer_iff symb ctx e ty).2 h]; rfl⟩

/-! ## Examples -/

/-- `(true)`. -/
def parenTrue : Hir := .mk (.Paren (.mk (.Core (.BooleanLiteral true))))

/-- `let x = (1); x`. -/
def letLocal : Hir :=
  .mk (.Core (.Let none (.mk (.Paren (.mk (.Core (.IntegerLiteral 1))))) (.mk (.Core (.Local 0)))))

example : infer .Empty .Empty parenTrue = some .Boolean := by decide

/-- The body of the let is typed in the context extended by the value's type. -/
example : infer .Empty .Empty letLocal = some .Integer := by decide

/-- One row for each node: the literal, its parenthesis, the local and the let. -/
example : (inferTable .Empty .Empty letLocal).map (fun t => length HirRow t.1) = some 4 := by
  decide

/-- A local that is not in scope has no type. -/
example : infer .Empty .Empty (.mk (.Core (.Local 0))) = none := by decide

/-- An operand of the wrong type has no type, and neither has any expression around it. -/
example : infer .Empty .Empty
    (.mk (.Paren (.mk (.Core (.If parenTrue letLocal parenTrue))))) = none := by decide

end Spec.Compiler.Thir
