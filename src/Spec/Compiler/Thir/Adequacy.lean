import Spec.Compiler.Thir.Hir
import Spec.Language.Types.Adequacy

/-!
# Adequacy of the synthesis tables

The laws of algorithmic typing about expressions as trees, which Fren cannot
state. `Synth` is the inductive reading of `Σ; Γ ⊢ e ⇒ τ`: Σ and Γ are well
formed and a finite tree of instances of the synthesis rules concludes it.

* `desugared_unfolding` is `thir.algorithmic.desugared-unfolding`.
* `synthesis_adequate` is `thir.algorithmic.tree-lift`: some table that
  `synthesis?` accepts has a root that unfolds to `e` exactly when
  `Synth` holds of `e`. It instantiates `Spec.Tables.Valid.derives` and
  `Spec.Tables.Derives.table` at `HirF`, through `hir_valid_iff`.
* `synth_iff_typed` is `thir.algorithmic.expression-complete` and its
  converse for trees: `e` synthesizes τ exactly when the Core types `|e|`
  at τ. `expression_complete` states it of tables.
* `synth_unique`, `synth_regular` and `synthesis_unique_unfolding` follow.
-/

open Fren.Lang

namespace Spec.Compiler.Thir

open spec.surface spec.names spec.types spec.algorithmic
open Spec.Tables Spec.Language.Types

/-- How `Spec.Tables` reads a HIR row: its form, and its context and type. -/
def hirView : View HirRow HirF Typing := ⟨HirRow.form, fun r => ⟨r.ctx, r.ty⟩⟩

/-- The one-layer synthesis rule as a relation on typings. -/
def HRule (symb : Snoc Entry) (l : HirF Typing) (j : Typing) : Prop :=
  synth_layer symb j.ctx l = some j.ty

/-- The rule that `hir_rows_valid?` checks of a row: its context is well formed too. -/
def HRuleOk (symb : Snoc Entry) (l : HirF Typing) (j : Typing) : Prop :=
  ctx_ok? symb j.ctx = true ∧ HRule symb l j

/-- The inductive reading of `Σ; Γ ⊢ e ⇒ τ`: Σ and Γ are well formed and a
finite tree of instances of the synthesis rules concludes it. -/
def Synth (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty) : Prop :=
  symb_ok? symb = true ∧ ctx_ok? symb ctx = true ∧ Derives Hir.mk (HRule symb) e ⟨ctx, ty⟩

/-- The expression that a HIR table's root unfolds to. -/
def HRootUnfolds (rows : Snoc HirRow) (e : Hir) : Prop :=
  Unfolds hirView Hir.mk rows ((length HirRow rows : Int) - 1) e

/-! ## The rule of one layer -/

/-- `thir.algorithmic.agreement`: the synthesis rule of a Core layer is the Core's rule. -/
theorem hrule_core (symb : Snoc Entry) (l : CoreF Typing) (j : Typing) :
    HRule symb (.Core l) j ↔ Rule symb l j := by
  unfold HRule Rule
  rw [synth_layer_core]
  exact ⟨synth_core_sound symb _ _ _, synth_core_complete symb _ _ _⟩

/-- `thir.algorithmic.parens`: a parenthesis has the typing of its body. -/
theorem hrule_paren (symb : Snoc Entry) (t j : Typing) : HRule symb (.Paren t) j ↔ t = j := by
  obtain ⟨tc, tt⟩ := t
  obtain ⟨jc, jt⟩ := j
  simp [HRule, synth_layer, provided, placed?, outcome_type, fren_spec]

/-! ## Trees of rule instances and desugaring -/

/-- A tree of synthesis rule instances for `e` desugars to a tree of Core
rule instances for `|e|`, with the same conclusion. -/
theorem synth_desugars (symb : Snoc Entry) {e : Hir} {j : Typing}
    (h : Derives Hir.mk (HRule symb) e j) : Derives Core.mk (Rule symb) (desugar e) j := by
  induction h with
  | node a j _ hra ih =>
    cases a with
    | Core b =>
      have he : desugar (Hir.mk (Layer.map Prod.fst (HirF.Core b)))
          = Core.mk (Layer.map Prod.fst (mapF (fun c : Hir × Typing => (desugar c.1, c.2)) b)) := by
        show desugar (.mk (.Core (mapF Prod.fst b))) = _
        rw [desugar_core]
        exact congrArg Core.mk ((Layer.map_map (F := CoreF) Prod.fst desugar b).trans
          (Layer.map_map (F := CoreF) (fun c : Hir × Typing => (desugar c.1, c.2)) Prod.fst b).symm)
      rw [he]
      refine Derives.node (F := CoreF) _ j ?_ ?_
      · exact (forall_mem_children_map (F := CoreF) _ b _).2 ih
      · have hs : Layer.map Prod.snd (mapF (fun c : Hir × Typing => (desugar c.1, c.2)) b)
            = mapF Prod.snd b := Layer.map_map (F := CoreF) _ _ _
        rw [hs]
        exact (hrule_core symb _ j).1 hra
    | Paren x =>
      have ht : x.2 = j := (hrule_paren symb _ j).1 hra
      show Derives Core.mk (Rule symb) (desugar (.mk (.Paren x.1))) j
      rw [desugar_paren, ← ht]
      exact ih x (List.mem_singleton.2 rfl)

/-- A tree of Core rule instances for `|e|` lifts to a tree of synthesis
rule instances for `e`: each node keeps its form, and each parenthesis of `e`
gets an instance with the typing of its body. An invariant `Q` of the Core
tree's conclusions holds of the lifted tree's. -/
theorem desugar_synth_with (symb : Snoc Entry) (Q : Typing → Prop) (e : Hir) :
    ∀ j, Derives Core.mk (fun l j => Rule symb l j ∧ Q j) (desugar e) j →
      Derives Hir.mk (fun l j => HRule symb l j ∧ Q j) e j := by
  refine Hir.ind (P := fun e => ∀ j,
    Derives Core.mk (fun l j => Rule symb l j ∧ Q j) (desugar e) j →
      Derives Hir.mk (fun l j => HRule symb l j ∧ Q j) e j) (fun l ih => ?_) e
  intro j h
  cases l with
  | Paren x =>
    rw [desugar_paren] at h
    have hq : Q j := by
      generalize desugar x = t at h
      cases h with
      | node _ _ _ hra => exact hra.2
    refine Derives.node (F := HirF) (.Paren (x, j)) j ?_ ⟨(hrule_paren symb _ j).2 rfl, hq⟩
    intro c hc
    have hc' : c = (x, j) := List.mem_singleton.1 hc
    rw [hc']
    exact ih x (List.mem_singleton.2 rfl) j h
  | Core b =>
    rw [desugar_core] at h
    generalize ht : Core.mk (mapF desugar b) = t at h
    cases h with
    | node a _ hc hra =>
      obtain ⟨z, hz1, hz2, hz3⟩ := Layer.zip (F := CoreF) desugar Prod.fst b a (Core.mk.inj ht)
      have hb : b = mapF Prod.fst (mapF (fun c : Hir × Core × Typing => (c.1, c.2.2)) z) := by
        rw [← hz1]
        exact (Layer.map_map (F := CoreF) (fun c : Hir × Core × Typing => (c.1, c.2.2))
          Prod.fst z).symm
      rw [hb]
      refine Derives.node (F := HirF)
        (.Core (mapF (fun c : Hir × Core × Typing => (c.1, c.2.2)) z)) j ?_ ?_
      · intro c hcm
        rw [show Layer.children (HirF.Core (mapF (fun c : Hir × Core × Typing => (c.1, c.2.2)) z))
          = _ from Layer.children_map (F := CoreF) _ z] at hcm
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hcm
        have h1 : c0.1 ∈ childrenH (.Core b) := by
          rw [← hz1]; exact mem_map_of_mem (F := CoreF) Prod.fst hc0
        have h2 : c0.2 ∈ Layer.children a := by
          rw [← hz2]; exact mem_map_of_mem (F := CoreF) Prod.snd hc0
        refine ih c0.1 h1 c0.2.2 ?_
        rw [hz3 c0 hc0]
        exact hc c0.2 h2
      · refine ⟨(hrule_core symb _ j).2 ?_, hra.2⟩
        have hs : mapF Prod.snd (mapF (fun c : Hir × Core × Typing => (c.1, c.2.2)) z)
            = Layer.map Prod.snd a := by
          rw [← hz2]
          exact (Layer.map_map (F := CoreF) (fun c : Hir × Core × Typing => (c.1, c.2.2))
            Prod.snd z).trans (Layer.map_map (F := CoreF) Prod.snd Prod.snd z).symm
        show Rule symb (mapF Prod.snd (mapF (fun c : Hir × Core × Typing => (c.1, c.2.2)) z)) j
        rw [hs]; exact hra.1

theorem desugar_synth (symb : Snoc Entry) (e : Hir) (j : Typing)
    (h : Derives Core.mk (Rule symb) (desugar e) j) : Derives Hir.mk (HRule symb) e j :=
  Derives.mono (fun _ _ hr => hr.1)
    (desugar_synth_with symb (fun _ => True) e j (Derives.mono (fun _ _ hr => ⟨hr, trivial⟩) h))

/-- `thir.algorithmic.expression-complete` and its converse, for trees: an
expression synthesizes a type exactly when the Core gives its desugaring
that type. -/
theorem synth_iff_typed (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty) :
    Synth symb ctx e ty ↔ Typed symb ctx (desugar e) ty :=
  ⟨fun h => ⟨h.1, h.2.1, synth_desugars symb h.2.2⟩,
    fun h => ⟨h.1, h.2.1, desugar_synth symb e _ h.2.2⟩⟩

/-- Uniqueness for trees: an expression synthesizes at most one type in a context. -/
theorem synth_unique (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (a b : Ty)
    (ha : Synth symb ctx e a) (hb : Synth symb ctx e b) : a = b :=
  typed_unique symb ctx (desugar e) a b ((synth_iff_typed ..).1 ha) ((synth_iff_typed ..).1 hb)

/-- Regularity for trees: a synthesized type is well formed. -/
theorem synth_regular (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty)
    (h : Synth symb ctx e ty) : ty_ok? symb ty = true :=
  typed_regular symb ctx (desugar e) ty ((synth_iff_typed ..).1 h)

/-! ## Tables and their desugarings -/

/-- The newest row of a desugaring, and the desugaring of the earlier rows. -/
theorem desugar_rows_inv (earlier : Snoc HirRow) (row : HirRow) (core : Snoc Row)
    (hd : desugar_rows (.Extend earlier row) = some core) :
    ∃ c f, desugar_rows earlier = some c ∧ core = .Extend c ⟨f, row.ctx, row.ty⟩ ∧
      match row.form with
      | .Core l => f = l
      | .Paren b => ∃ d, lookup Row c b = some d ∧ f = d.form := by
  simp only [desugar_rows] at hd
  cases hd' : desugar_rows earlier with
  | none => simp [hd'] at hd
  | some c =>
    rcases row with ⟨form, rc, rt⟩
    cases form with
    | Core f =>
      simp only [hd', core_row, Option.some.injEq] at hd
      exact ⟨c, f, rfl, hd.symm, rfl⟩
    | Paren body =>
      cases hl : lookup _ c body with
      | none => simp [hd', hl] at hd
      | some d =>
        simp only [hd', hl, core_row, Option.some.injEq] at hd
        exact ⟨c, d.form, rfl, hd.symm, d, hl, rfl⟩

/-- The desugared row at the level of a HIR row: it has that row's context
and type, and its layer or, for a parenthesis, the layer of its body's
desugared row. -/
theorem desugar_row_at (rows : Snoc HirRow) (core : Snoc Row)
    (hd : desugar_rows rows = some core) (p : Int) (r : HirRow)
    (hl : lookup HirRow rows p = some r) :
    ∃ r', lookup Row core p = some r' ∧ r'.ctx = r.ctx ∧ r'.ty = r.ty ∧
      match r.form with
      | .Core l => r'.form = l
      | .Paren b => ∃ d, lookup Row core b = some d ∧ r'.form = d.form := by
  induction rows generalizing core with
  | Empty => simp [lookup] at hl
  | Extend earlier row ih =>
    obtain ⟨c, f, hc, rfl, hf⟩ := desugar_rows_inv earlier row core hd
    have hlen := desugar_length earlier c hc
    rw [lookup_extend] at hl
    by_cases hp : p = length HirRow earlier
    · rw [if_pos hp] at hl
      have hrr : row = r := Option.some.inj hl
      subst hrr
      refine ⟨⟨f, row.ctx, row.ty⟩, by rw [lookup_extend, hlen, if_pos hp], rfl, rfl, ?_⟩
      cases hfm : row.form with
      | Core l => simp only [hfm] at hf; exact hf
      | Paren b =>
        simp only [hfm] at hf
        obtain ⟨d, hd1, hd2⟩ := hf
        exact ⟨d, Extends.extend c _ b d hd1, hd2⟩
    · rw [if_neg hp] at hl
      obtain ⟨r', h1, h2, h3, h4⟩ := ih c hc hl
      refine ⟨r', Extends.extend c _ p r' h1, h2, h3, ?_⟩
      cases hfm : r.form with
      | Core l => simp only [hfm] at h4; exact h4
      | Paren b =>
        simp only [hfm] at h4
        obtain ⟨d, hd1, hd2⟩ := h4
        exact ⟨d, Extends.extend c _ b d hd1, hd2⟩

/-- A child's typing is the same in a table and its desugaring. -/
theorem desugar_typing_at (rows : Snoc HirRow) (core : Snoc Row)
    (hd : desugar_rows rows = some core) (p : Int) (t : Typing) :
    typing_at core p = some t ↔ ∃ r, lookup HirRow rows p = some r ∧ hirView.concl r = t := by
  rw [typing_at_iff]
  induction rows generalizing core with
  | Empty => simp only [desugar_rows, Option.some.injEq] at hd; subst hd; simp [lookup]
  | Extend earlier row ih =>
    obtain ⟨c, f, hc, rfl, -⟩ := desugar_rows_inv earlier row core hd
    have hlen := desugar_length earlier c hc
    simp only [lookup_extend, hlen]
    by_cases hp : p = length HirRow earlier
    · simp [hp, rowView, hirView]
    · simp only [if_neg hp]; exact ih c hc

theorem hir_annotate_iff (core : Snoc Row) (form : HirF Int) (typed : HirF Typing) :
    hir_annotate core form = some typed ↔ ∃ a : HirF (Int × Typing),
      mapH Prod.fst a = form ∧ mapH Prod.snd a = typed ∧
        ∀ c ∈ childrenH a, typing_at core c.1 = some c.2 := by
  cases form with
  | Core l =>
    simp only [hir_annotate]
    constructor
    · intro h
      cases ha : annotate core l with
      | none => simp [ha] at h
      | some t =>
        simp only [ha, Option.some.injEq] at h; subst h
        obtain ⟨a, h1, h2, h3⟩ := (annotate_iff _ _ _).1 ha
        exact ⟨.Core a, congrArg HirF.Core h1, congrArg HirF.Core h2, h3⟩
    · rintro ⟨a, h1, h2, h3⟩
      cases a with
      | Paren x => simp [mapH] at h1
      | Core a =>
        simp only [mapH, HirF.Core.injEq] at h1
        subst h2
        have := (annotate_iff core l (mapF Prod.snd a)).2 ⟨a, h1, rfl, h3⟩
        simp [this, mapH]
  | Paren b =>
    simp only [hir_annotate]
    constructor
    · intro h
      cases ht : typing_at core b with
      | none => simp [ht] at h
      | some t =>
        simp only [ht, Option.some.injEq] at h; subst h
        exact ⟨.Paren (b, t), rfl, rfl, by simp [childrenH, ht]⟩
    · rintro ⟨a, h1, h2, h3⟩
      cases a with
      | Core a => simp [mapH] at h1
      | Paren x =>
        simp only [mapH, HirF.Paren.injEq] at h1
        subst h2; subst h1
        have := h3 x (by simp [childrenH])
        simp [this, mapH]

theorem hir_justified_iff (symb : Snoc Entry) (earlier : Snoc HirRow) (core : Snoc Row)
    (hd : desugar_rows earlier = some core) (row : HirRow) :
    Justified hirView (HRuleOk symb) earlier (length HirRow earlier) row ↔
      ctx_ok? symb row.ctx = true ∧
        ∃ typed, hir_annotate core row.form = some typed ∧
          synth_layer symb row.ctx typed = some row.ty := by
  constructor
  · rintro ⟨a, hf, ⟨hok, hr⟩, hc⟩
    refine ⟨hok, Layer.map Prod.snd a,
      (hir_annotate_iff _ _ _).2 ⟨a, hf, rfl, fun c hcm => ?_⟩, hr⟩
    obtain ⟨-, r', hl, hcl⟩ := hc c hcm
    exact (desugar_typing_at earlier core hd _ _).2 ⟨r', hl, hcl⟩
  · rintro ⟨hok, typed, ha, hr⟩
    obtain ⟨a, hf, rfl, hc⟩ := (hir_annotate_iff _ _ _).1 ha
    refine ⟨a, hf, ⟨hok, hr⟩, fun c hcm => ?_⟩
    obtain ⟨r, hl, hcl⟩ := (desugar_typing_at earlier core hd _ _).1 (hc c hcm)
    exact ⟨lookup_lt hl, r, hl, hcl⟩

/-- `hir_rows_valid?` is validity for the synthesis rule. -/
theorem hir_valid_iff (symb : Snoc Entry) (rows : Snoc HirRow) :
    hir_rows_valid? symb rows = true ↔ Valid hirView (HRuleOk symb) rows := by
  induction rows with
  | Empty => simp only [hir_rows_valid?, true_iff]; exact Valid.empty _ _
  | Extend earlier row ih =>
    rw [valid_extend, ← ih]
    constructor
    · intro h
      simp only [hir_rows_valid?, decide_eq_true_eq] at h
      obtain ⟨core, hd, -⟩ := desugar_valid symb earlier h.1.1
      refine ⟨h.1.1, (hir_justified_iff symb earlier core hd row).2 ⟨h.1.2, ?_⟩⟩
      have h2 := h.2
      simp only [hd] at h2
      cases ha : hir_annotate core row.form with
      | none => simp [ha] at h2
      | some typed => simp only [ha] at h2; exact ⟨typed, rfl, of_decide_eq_true h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨core, hd, -⟩ := desugar_valid symb earlier h1
      obtain ⟨hok, typed, ha, hr⟩ := (hir_justified_iff symb earlier core hd row).1 h2
      simp only [hir_rows_valid?, decide_eq_true_eq]
      refine ⟨⟨h1, hok⟩, ?_⟩
      simp only [hd, ha]; exact decide_eq_true hr

/-- `thir.algorithmic.desugared-unfolding`: when a row of a HIR table that
has a desugaring unfolds to `e`, the row at the same level of the
desugaring unfolds to `|e|`. A valid table has a desugaring
(`desugar_valid`). -/
theorem desugared_unfolding (rows : Snoc HirRow) (core : Snoc Row)
    (hd : desugar_rows rows = some core) {p : Int} {e : Hir}
    (h : Unfolds hirView Hir.mk rows p e) : Unfolds rowView Core.mk core p (desugar e) := by
  induction h with
  | node p r a hl hf _ ih =>
    obtain ⟨r', hl', -, -, hform⟩ := desugar_row_at rows core hd p r hl
    cases a with
    | Core b =>
      have hf' : r.form = .Core (mapF Prod.fst b) := hf.symm
      simp only [hf'] at hform
      have he : desugar (Hir.mk (Layer.map Prod.snd (HirF.Core b)))
          = Core.mk (Layer.map Prod.snd (mapF (fun c : Int × Hir => (c.1, desugar c.2)) b)) := by
        show desugar (.mk (.Core (mapF Prod.snd b))) = _
        rw [desugar_core]
        exact congrArg Core.mk ((Layer.map_map (F := CoreF) Prod.snd desugar b).trans
          (Layer.map_map (F := CoreF) (fun c : Int × Hir => (c.1, desugar c.2)) Prod.snd b).symm)
      rw [he]
      refine Unfolds.node (F := CoreF) p r' _ hl' ?_ ?_
      · show Layer.map Prod.fst (mapF (fun c : Int × Hir => (c.1, desugar c.2)) b) = r'.form
        rw [hform]
        exact Layer.map_map (F := CoreF) (fun c : Int × Hir => (c.1, desugar c.2)) Prod.fst b
      · exact (forall_mem_children_map (F := CoreF) _ b _).2 ih
    | Paren x =>
      have hf' : r.form = .Paren x.1 := hf.symm
      simp only [hf'] at hform
      obtain ⟨d, hd1, hd2⟩ := hform
      have hx := ih x (List.mem_singleton.2 rfl)
      show Unfolds rowView Core.mk core p (desugar (.mk (.Paren x.2)))
      rw [desugar_paren]
      generalize desugar x.2 = t at hx
      cases hx with
      | node _ r2 a2 hl2 hf2 hch2 =>
        rw [hd1] at hl2; cases hl2
        exact Unfolds.node p r' a2 hl' (hf2.trans hd2.symm) hch2

/-! ## Adequacy of the synthesis judgment -/

theorem hir_root_position (earlier : Snoc HirRow) (root : HirRow) :
    ((length HirRow (.Extend earlier root) : Nat) : Int) - 1 = length HirRow earlier := by
  simp only [length]; omega

theorem hir_rows_extend_of_lookup (rows : Snoc HirRow) (base : Snoc Ty)
    (h : ∀ p r, lookup HirRow rows p = some r → extends? r.ctx base = true) :
    hir_rows_extend? rows base = true := by
  induction rows with
  | Empty => simp [hir_rows_extend?]
  | Extend earlier row ih =>
    simp only [hir_rows_extend?, decide_eq_true_eq]
    refine ⟨h (length HirRow earlier) row (lookup_last earlier row), ih ?_⟩
    exact fun p r hl => h p r (Extends.extend earlier row p r hl)

/-- Every context of a tree of synthesis rule instances extends the root's. -/
theorem hrule_extends (symb : Snoc Entry) (base : Snoc Ty) (l : HirF Typing) (j : Typing)
    (h : HRuleOk symb l j) (hq : extends? j.ctx base = true) :
    ∀ c ∈ childrenH l, extends? c.ctx base = true := by
  cases l with
  | Core b => exact rule_extends symb base b j ⟨h.1, (hrule_core symb b j).1 h.2⟩ hq
  | Paren t =>
    intro c hc
    rw [List.mem_singleton.1 hc, (hrule_paren symb t j).1 h.2]; exact hq

/-- Soundness of tables: the root of a table that `synthesis?` accepts
unfolds to an expression that the rules type. -/
theorem synthesis_synth (symb : Snoc Entry) (rows : Snoc HirRow) (ctx : Snoc Ty) (ty : Ty)
    (h : synthesis? symb rows ctx ty = true) :
    ∃ e, HRootUnfolds rows e ∧ Synth symb ctx e ty := by
  cases rows with
  | Empty => simp [synthesis?, fren_spec] at h
  | Extend earlier root =>
    simp only [synthesis?, decide_eq_true_eq] at h
    have hroot := h.2
    simp only [reduceCtorEq, ↓reduceIte, Snoc.Extend.x1, Bool.decide_and, Fren.lastArm_eq,
      Bool.and_eq_true, decide_eq_true_eq] at hroot
    have hl := lookup_last earlier root
    obtain ⟨t, hut, hdt⟩ := Valid.derives Hir.mk ((hir_valid_iff symb _).1 h.1.1.2) hl
    have hj : hirView.concl root = ⟨ctx, ty⟩ := by
      rw [← hroot.1, ← hroot.2]; rfl
    rw [hj] at hdt
    have hs : symb_ok? symb = true := by
      simp only [symb_ok?, decide_eq_true_eq]; exact h.1.1.1.1
    refine ⟨t, ?_, hs, h.1.1.1.2, Derives.mono (fun _ _ hr => hr.2) hdt⟩
    unfold HRootUnfolds; rw [hir_root_position]; exact hut

/-- Every node of a tree of synthesis rule instances over well-formed Σ and
Γ has a well-formed context: the Core's regularity, through desugaring. -/
theorem synth_contexts_ok (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty)
    (h : Synth symb ctx e ty) : Derives Hir.mk (HRuleOk symb) e ⟨ctx, ty⟩ :=
  Derives.mono (fun _ _ hr => ⟨hr.2, hr.1⟩)
    (desugar_synth_with symb (fun j => ctx_ok? symb j.ctx = true) e _
      (Derives.mono (fun _ _ hr => ⟨hr.2, hr.1⟩)
        (derives_regular symb h.1 (synth_desugars symb h.2.2) h.2.1).1))

/-- A valid table whose contexts extend Γ and whose newest row concludes
`Γ ⊢ τ` is accepted by `synthesis?`, when Σ and Γ are well formed. -/
theorem synthesis_of_valid (symb : Snoc Entry) (ctx : Snoc Ty) (ty : Ty) (rows : Snoc HirRow)
    (r : HirRow) (hs : symb_ok? symb = true) (hc : ctx_ok? symb ctx = true)
    (hv : Valid hirView (fun l j => HRuleOk symb l j ∧ extends? j.ctx ctx = true) (.Extend rows r))
    (hcl : hirView.concl r = ⟨ctx, ty⟩) : synthesis? symb (.Extend rows r) ctx ty = true := by
  have hcl' : r.ctx = ctx ∧ r.ty = ty := by
    have := congrArg Typing.ctx hcl; have := congrArg Typing.ty hcl; constructor <;> assumption
  have hvalid : hir_rows_valid? symb (.Extend rows r) = true :=
    (hir_valid_iff symb _).2 (Valid.mono (fun _ _ hr => hr.1) hv)
  have hext : hir_rows_extend? (.Extend rows r) ctx = true :=
    hir_rows_extend_of_lookup _ _ (fun p r' hl => Valid.invariant hv hl)
  have hs' : bindings_ok? symb symb = true := by
    simpa only [symb_ok?, decide_eq_true_eq] using hs
  simp only [synthesis?, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hs', hc⟩, hvalid⟩, hext⟩, ?_⟩
  simp [fren_spec, hcl'.1, hcl'.2]

/-- `thir.algorithmic.tree-lift`: the table judgment agrees with the
inductive reading of the rules. Some table that `synthesis?` accepts for
`ty` in `ctx` has a root that unfolds to `e` exactly when Σ and Γ are well
formed and a tree of rule instances concludes it. -/
theorem synthesis_adequate (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty) :
    (∃ rows, synthesis? symb rows ctx ty = true ∧ HRootUnfolds rows e) ↔ Synth symb ctx e ty := by
  constructor
  · rintro ⟨rows, h, hu⟩
    obtain ⟨t, hut, ht⟩ := synthesis_synth symb rows ctx ty h
    rw [← Unfolds.unique hut hu]; exact ht
  · intro h
    have h2 := Derives.strengthen (F := HirF) (fun j : Typing => extends? j.ctx ctx = true)
      (fun l j hr hq => hrule_extends symb ctx l j hr hq) (synth_contexts_ok symb ctx e ty h)
      (extends_refl ctx)
    obtain ⟨rows', r, -, hv, hcl, hu⟩ := Derives.table (V := hirView)
      (fun l j => (⟨l, j.ctx, j.ty⟩ : HirRow)) (fun _ _ => rfl) (fun _ _ => rfl) h2 .Empty
      (Valid.empty _ _)
    refine ⟨.Extend rows' r, synthesis_of_valid symb ctx ty rows' r h.1 h.2.1 hv hcl, ?_⟩
    · unfold HRootUnfolds; rw [hir_root_position]; exact hu

/-- A table that `synthesis?` accepts has a root that unfolds to exactly one
expression. -/
theorem synthesis_unique_unfolding (rows : Snoc HirRow) (e e' : Hir)
    (h : HRootUnfolds rows e) (h' : HRootUnfolds rows e') : e = e' :=
  Unfolds.unique h h'

/-- The pairing lemma of `thir.algorithmic.tree-lift`, for trees: two HIR
tables whose roots unfold to the same expression have desugarings whose
roots unfold to the same Core expression, its desugaring. -/
theorem desugarings_unfold_alike (left right : Snoc HirRow) (cl cr : Snoc Row) (e : Hir)
    (hl : desugar_rows left = some cl) (hr : desugar_rows right = some cr)
    (ul : HRootUnfolds left e) (ur : HRootUnfolds right e) :
    RootUnfolds cl (desugar e) ∧ RootUnfolds cr (desugar e) := by
  unfold RootUnfolds
  rw [desugar_length left cl hl, desugar_length right cr hr]
  exact ⟨desugared_unfolding left cl hl ul, desugared_unfolding right cr hr ur⟩

/-- Uniqueness of the judgment: two tables that `synthesis?` accepts in one
context, whose roots unfold to the same expression, have the same type. -/
theorem synthesis_unique (symb : Snoc Entry) (ctx : Snoc Ty) (left right : Snoc HirRow)
    (e : Hir) (a b : Ty) (hl : synthesis? symb left ctx a = true)
    (hr : synthesis? symb right ctx b = true) (ul : HRootUnfolds left e)
    (ur : HRootUnfolds right e) : a = b :=
  synth_unique symb ctx e a b ((synthesis_adequate ..).1 ⟨left, hl, ul⟩)
    ((synthesis_adequate ..).1 ⟨right, hr, ur⟩)

/-- `thir.algorithmic.expression-complete`, of tables: when the Core has a
derivation of `ty` in `ctx` whose root unfolds to `|e|`, some table that
`synthesis?` accepts for `ty` in `ctx` has a root that unfolds to `e`. The
converse is `thir.algorithmic.expression-sound` for trees. -/
theorem expression_complete (symb : Snoc Entry) (ctx : Snoc Ty) (e : Hir) (ty : Ty) :
    (∃ core, derivation? symb core ctx ty = true ∧ RootUnfolds core (desugar e)) ↔
      ∃ rows, synthesis? symb rows ctx ty = true ∧ HRootUnfolds rows e := by
  rw [judgment_adequate, synthesis_adequate, synth_iff_typed]

end Spec.Compiler.Thir
