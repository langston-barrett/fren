import Spec.Language.Types

/-!
# Adequacy of the typing tables

`types.judgment.adequacy`: `Σ; Γ ⊢ e : τ`, which the chapter defines by
derivation tables, holds exactly when Σ and Γ are well formed and a finite
tree of instances of the rules concludes it. The tree reading is `Typed`
(`Spec.Language.Types`): both well-formedness conditions, and
`Spec.Tables.Derives` of the one-layer rule. A rule without premises, such as
the Boolean literal's, has a one-node tree under any environment, so the
conditions are part of the reading and not consequences of the tree.

`judgment_adequate` is the law. One direction, `derivation_typed`, is in the
chapter's wrapper, since the uniqueness law bound there rests on it; it
instantiates `Spec.Tables.Valid.derives`. The other, here, instantiates
`Spec.Tables.Derives.table`: it needs every context of the tree to be well
formed (`derives_regular`) and to extend the root's (`rule_extends`). Both
generic theorems hold of any one-layer form and rule, so a later chapter
that writes its derivations as tables proves its adequacy the same way: an
instance of `Layer`, a `View` of its rows, and its table check as `Valid`.

With adequacy, the laws that the chapter proves of tables hold of
expressions: regularity (`typed_regular`), weakening with the shifted
expression (`typed_weakens`), and uniqueness (`typed_unique`, in the
wrapper).
-/

open Fren.Lang

namespace Spec.Language.Types

open spec.surface spec.names spec.types
open Spec.Tables

/-! ## Regularity for trees -/

theorem typings_ok_iff (symbols : Snoc Entry) (xs : Snoc Typing) :
    typings_ok? symbols xs = true ↔ ∀ c ∈ toList xs, ty_ok? symbols c.ty = true := by
  induction xs with
  | Empty => simp [typings_ok?, toList]
  | Extend earlier x ih =>
    rw [typings_ok_extend, ih]
    simp only [toList, List.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩ c (rfl | hc)
      · exact h1
      · exact h2 c hc
    · intro h; exact ⟨h x (Or.inl rfl), fun c hc => h c (Or.inr hc)⟩

theorem toList_arm_typings (arms : Snoc (ArmF Typing)) :
    toList (arm_typings arms) = (toList arms).map (·.body) := by
  induction arms with
  | Empty => simp [arm_typings, toList]
  | Extend earlier arm ih => simp [arm_typings, toList, ih]

theorem mem_children_iff (l : CoreF Typing) (c : Typing) :
    c ∈ toList (Fren.Generated.spec.types.children l) ↔ c ∈ childrenF l := by
  cases l <;>
    simp only [Fren.Generated.spec.types.children, childrenF, toList, toList_arm_typings,
      List.mem_cons, List.mem_nil_iff, false_or, List.mem_map, or_comm, or_left_comm]

theorem children_ok_iff (symbols : Snoc Entry) (l : CoreF Typing) :
    children_ok? symbols l = true ↔ ∀ c ∈ childrenF l, ty_ok? symbols c.ty = true := by
  have h : children_ok? symbols l = true
      ↔ typings_ok? symbols (Fren.Generated.spec.types.children l) = true := by
    simp only [children_ok?, decide_eq_true_eq]
  rw [h, typings_ok_iff]
  exact ⟨fun h c hc => h c ((mem_children_iff l c).2 hc),
    fun h c hc => h c ((mem_children_iff l c).1 hc)⟩

/-- Regularity for trees: over a well-formed environment and context, every
node of a derivation has a well-formed context and the conclusion a
well-formed type. -/
theorem derives_regular (symbols : Snoc Entry) (hs : symb_ok? symbols = true) {e : Core}
    {j : Typing} (h : Derives Core.mk (Rule symbols) e j) :
    ctx_ok? symbols j.ctx = true →
      Derives Core.mk (RuleOk symbols) e j ∧ ty_ok? symbols j.ty = true := by
  induction h with
  | node a j _ hra ih =>
    intro hc
    have hctx := rule_child_ctx symbols j.ctx (mapF Prod.snd a) j.ty hra
    have hall : ∀ c ∈ childrenF a, ctx_ok? symbols c.2.ctx = true := by
      cases a with
      | Let ann v b =>
        obtain ⟨hv, hb⟩ : v.2.ctx = j.ctx ∧ b.2.ctx = .Extend j.ctx v.2.ty := hctx
        have hvok : ctx_ok? symbols v.2.ctx = true := by rw [hv]; exact hc
        intro c hcm
        simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hcm
        rcases hcm with rfl | rfl
        · exact hvok
        · rw [hb, context_ok_extend]
          exact ⟨(ih v (by simp [Layer.children, childrenF]) hvok).2, hc⟩
      | _ =>
        intro c hcm
        have := hctx c.2 (mem_map_of_mem (F := CoreF) Prod.snd hcm)
        rw [this]; exact hc
    have hty : ty_ok? symbols j.ty = true := by
      refine layer_regular symbols j.ctx (mapF Prod.snd a) j.ty hs hc ?_ hra
      rw [children_ok_iff]
      intro c hcm
      rw [show childrenF (mapF Prod.snd a) = (childrenF a).map Prod.snd from
        Layer.children_map (F := CoreF) Prod.snd a] at hcm
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hcm
      exact (ih c0 hc0 (hall c0 hc0)).2
    exact ⟨Derives.node a j (fun c hcm => (ih c hcm (hall c hcm)).1) ⟨hc, hra⟩, hty⟩

/-! ## Every context of a tree extends the root's -/

theorem extends_refl (context : Snoc Ty) : extends? context context = true := by
  cases context <;> simp [extends?]

theorem extends_step (context base : Snoc Ty) (t : Ty) (h : extends? context base = true) :
    extends? (.Extend context t) base = true := by
  rw [extends?]; simp [h]

theorem rows_extend_of_lookup (rows : Snoc Row) (base : Snoc Ty)
    (h : ∀ p r, lookup Row rows p = some r → extends? r.ctx base = true) :
    rows_extend? rows base = true := by
  induction rows with
  | Empty => simp [rows_extend?]
  | Extend earlier row ih =>
    simp only [rows_extend?, decide_eq_true_eq]
    refine ⟨h (length Row earlier) row (by rw [lookup_extend, if_pos rfl]), ih ?_⟩
    exact fun p r hl => h p r (Extends.extend earlier row p r hl)

theorem rule_extends (symbols : Snoc Entry) (base : Snoc Ty) (l : CoreF Typing) (j : Typing)
    (h : RuleOk symbols l j) (hq : extends? j.ctx base = true) :
    ∀ c ∈ childrenF l, extends? c.ctx base = true := by
  have hctx := rule_child_ctx symbols j.ctx l j.ty h.2
  cases l with
  | Let ann v b =>
    obtain ⟨hv, hb⟩ : v.ctx = j.ctx ∧ b.ctx = .Extend j.ctx v.ty := hctx
    intro c hcm
    simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hcm
    rcases hcm with rfl | rfl
    · rw [hv]; exact hq
    · rw [hb]; exact extends_step _ _ _ hq
  | _ => intro c hcm; rw [hctx c hcm]; exact hq

/-! ## Adequacy -/

/-- Adequacy: the table judgment agrees with the inductive reading of the
rules. Some table is a derivation of `ty` in `context` whose root unfolds to
`e` exactly when Σ and Γ are well formed and a tree of rule instances
concludes it. -/
theorem judgment_adequate (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (ty : Ty) :
    (∃ rows, derivation? symbols rows context ty = true ∧ RootUnfolds rows e)
      ↔ Typed symbols context e ty := by
  constructor
  · rintro ⟨rows, h, hu⟩
    obtain ⟨t, hut, ht⟩ := derivation_typed symbols rows context ty h
    rw [← Unfolds.unique hut hu]; exact ht
  · rintro ⟨hs, hc, hd⟩
    have h1 := (derives_regular symbols hs hd hc).1
    have h2 := Derives.strengthen (F := CoreF) (fun j : Typing => extends? j.ctx context = true)
      (fun l j hr hq => rule_extends symbols context l j hr hq) h1 (extends_refl context)
    obtain ⟨rows', r, -, hv, hcl, hu⟩ := Derives.table (V := rowView)
      (fun l j => (⟨l, j.ctx, j.ty⟩ : Row)) (fun _ _ => rfl) (fun _ _ => rfl) h2 .Empty
      (Valid.empty _ _)
    refine ⟨.Extend rows' r, ?_, ?_⟩
    · have hcl' : r.ctx = context ∧ r.ty = ty := by
        have := congrArg Typing.ctx hcl; have := congrArg Typing.ty hcl; constructor <;> assumption
      have hvalid : rows_valid? symbols (.Extend rows' r) = true :=
        (valid_iff symbols _).2 (Valid.mono (fun _ _ hr => hr.1) hv)
      have hext : rows_extend? (.Extend rows' r) context = true :=
        rows_extend_of_lookup _ _ (fun p r' hl => Valid.invariant hv hl)
      have hs' : bindings_ok? symbols symbols = true := by
        simpa only [symb_ok?, decide_eq_true_eq] using hs
      simp only [derivation?, decide_eq_true_eq]
      refine ⟨⟨⟨⟨hs', hc⟩, hvalid⟩, hext⟩, ?_⟩
      simp [fren_spec, hcl'.1, hcl'.2]
    · unfold RootUnfolds; rw [root_position]; exact hu

/-- Regularity for expressions: a typed expression has a well-formed type. -/
theorem typed_regular (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (ty : Ty)
    (h : Typed symbols context e ty) : ty_ok? symbols ty = true :=
  (derives_regular symbols h.1 h.2.2 h.2.1).2

/-! ## Weakening for expressions -/

/-- `e'` is `e` with every local level of at least `cutoff` shifted by one. -/
def Shifted (cutoff : Int) (e e' : Core) : Prop := Mapped (shiftF cutoff) Core.mk e e'

/-- Weakening for expressions: a typed expression, its outer locals shifted
past a new context entry, has the same type in the extended context. -/
theorem typed_weakens (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (ty extra : Ty)
    (hx : ty_ok? symbols extra = true) (h : Typed symbols context e ty) :
    ∃ e', Shifted (length Ty context) e e' ∧ Typed symbols (.Extend context extra) e' ty := by
  obtain ⟨rows, hd, hu⟩ := (judgment_adequate symbols context e ty).2 h
  have hd' := judgment_weakens symbols rows context ty extra hx hd
  obtain ⟨e', hu', hm⟩ := Unfolds.mapped (V := rowView) (V' := rowView) (con := Core.mk)
    (shiftF (length Ty context)) (shiftF_natural _) (shiftF_within _)
    (rows' := weaken rows (length Ty context) extra)
    (fun p r hl => ⟨weakenRow (length Ty context) extra r, by rw [lookup_weaken, hl]; rfl,
      (shiftF_form _ _).symm⟩) hu
  refine ⟨e', hm, (judgment_adequate symbols _ e' ty).1 ⟨_, hd', ?_⟩⟩
  unfold RootUnfolds
  rw [length_weaken]
  exact hu'

end Spec.Language.Types
