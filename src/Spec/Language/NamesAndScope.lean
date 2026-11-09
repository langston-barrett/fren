import Fren.Impl
import Fren.Literate
import Fren.Trace
import FrenAstToHir
import Spec.Language.Types

open Fren.Lang

#fren_md "NamesAndScope.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.NamesAndScope

open spec.types spec.names
open Spec.Language.Types (lookup_bound lookup_none)

/-! ## Scopes -/

theorem local_bound (scope : Snoc String) (name : String) (level : Int)
    (h : resolve_local scope name = some level) : lookup _ scope level = some name := by
  induction scope with
  | Empty => simp [resolve_local] at h
  | Extend earlier newest ih =>
    simp only [resolve_local] at h
    split at h
    · rename_i eq
      simp at h
      simp [lookup, ← h, eq]
    · have found := ih h
      have bound := lookup_bound earlier level name found
      have : level ≠ length _ earlier := by omega
      simp [lookup, this, found]

theorem local_lt (scope : Snoc String) (name : String) (level : Int)
    (h : resolve_local scope name = some level) : 0 ≤ level ∧ level < length _ scope :=
  lookup_bound scope level name (local_bound scope name level h)

theorem local_nearest (scope : Snoc String) (name : String) (level other : Int)
    (h : resolve_local scope name = some level) (later : level < other) :
    lookup _ scope other ≠ some name := by
  induction scope with
  | Empty => simp [resolve_local] at h
  | Extend earlier newest ih =>
    simp only [resolve_local] at h
    split at h
    · simp at h
      have outside : ¬ (0 ≤ other ∧ other < length _ earlier) := by omega
      have : other ≠ length _ earlier := by omega
      simp [lookup, this, lookup_none earlier other outside]
    · rename_i ne
      by_cases at_newest : other = length _ earlier
      · simp [lookup, at_newest, ne]
      · simpa [lookup, at_newest] using ih h

theorem local_complete (scope : Snoc String) (name : String) (other : Int)
    (h : resolve_local scope name = none) : lookup _ scope other ≠ some name := by
  induction scope with
  | Empty => simp [lookup]
  | Extend earlier newest ih =>
    simp only [resolve_local] at h
    split at h
    · simp at h
    · rename_i ne
      by_cases at_newest : other = length _ earlier
      · simp [lookup, at_newest, ne]
      · simpa [lookup, at_newest] using ih h

theorem insert_name_length (scope : Snoc String) (cutoff : Int) (extra : String)
    (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope) :
    length _ (insert_name scope cutoff extra) = length _ scope + 1 := by
  induction scope with
  | Empty =>
    have : cutoff = 0 := by simp [length] at h1; omega
    simp [insert_name, this, length]
  | Extend earlier name ih =>
    simp only [insert_name]
    split
    · simp [length]
    · rename_i ne
      simp only [length] at h1 ⊢
      rw [ih (by omega)]

theorem local_weakens (scope : Snoc String) (cutoff : Int) (extra name : String)
    (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope) (ne : name ≠ extra) :
    resolve_local (insert_name scope cutoff extra) name
      = shifted (resolve_local scope name) cutoff := by
  have ne' : extra ≠ name := fun eq => ne eq.symm
  induction scope with
  | Empty =>
    have : cutoff = 0 := by simp [length] at h1; omega
    simp [insert_name, this, resolve_local, ne']
  | Extend earlier newest ih =>
    simp only [insert_name]
    split
    · rename_i at_end
      simp only [resolve_local, if_neg ne']
      cases found : (if newest = name then some (↑(length _ earlier) : Int) else resolve_local earlier name) with
      | none => rfl
      | some level =>
        have bound := local_lt (.Extend earlier newest) name level (by simpa [resolve_local] using found)
        simp only [length] at bound
        have : ¬ level ≥ cutoff := by omega
        simp [shift, this]
    · rename_i not_end
      simp only [length] at h1
      have h1' : cutoff ≤ length _ earlier := by omega
      simp only [resolve_local]
      split
      · have : (↑(length _ earlier) : Int) ≥ cutoff := by omega
        simp [insert_name_length earlier cutoff extra h0 h1', shift, this]
      · exact ih h1'

/-- A scope as the resolver holds it: nearest first. -/
def nearestFirst : Snoc String → List String
  | .Empty => []
  | .Extend earlier newest => newest :: nearestFirst earlier

theorem nearest_converse (scope : Snoc String) (name : String) :
    (FrenAstToHir.nearest (nearestFirst scope) name).map Int.ofNat
      = match resolve_local scope name with
        | some level => some (↑(length _ scope) - 1 - level)
        | none => none := by
  induction scope with
  | Empty => simp [nearestFirst, FrenAstToHir.nearest, resolve_local]
  | Extend earlier newest ih =>
    simp only [nearestFirst, FrenAstToHir.nearest, resolve_local, length]
    split
    · simp
    · cases found : resolve_local earlier name with
      | none => simp [found] at ih; simp [ih]
      | some level =>
        simp [found] at ih
        obtain ⟨index, hi, eq⟩ := ih
        simp [hi]
        omega

/-! ## Tables -/

theorem resolve_params_length (env : Env) (params : Snoc Param) (ctx : Snoc Ty)
    (h : resolve_params env params = some ctx) :
    length _ ctx = length _ (param_names params) := by
  induction params generalizing ctx with
  | Empty => simp [resolve_params] at h; simp [← h, param_names, length]
  | Extend earlier param ih =>
    simp only [resolve_params] at h
    split at h
    · rename_i earlierCtx ty he _
      simp at h
      simp [← h, param_names, length, ih earlierCtx he]
    · simp at h

theorem item_target_cases (symb : Snoc Entry) (item : Fren.Seq String) :
    item_target symb item = none ∨ item_target symb item = some (.Item item) := by
  simp only [item_target]
  split <;> simp

theorem head_local (env : Env) (scope : Snoc String) (name : String) (level : Int)
    (h : head env scope name = some (.Local level)) : resolve_local scope name = some level := by
  simp only [head] at h
  split at h
  · rename_i found eq
    simp at h
    simp [eq, h]
  · split at h
    · rename_i target eq
      rcases item_target_cases env.symb (child (module_of env) name) with none | item
      · simp [none] at eq
      · simp [item] at eq
        simp [← eq] at h
    · split at h <;> simp at h

theorem descend_not_local (env : Env) (target : Target) (name : String) (level : Int) :
    descend env target name ≠ some (.Local level) := by
  simp only [descend]
  split
  · simp
  · rcases item_target_cases env.symb (child (module_of env) name) with h | h <;> simp [h]
  · split
    · rename_i item _ _ _
      rcases item_target_cases env.symb (child item name) with h | h <;> simp [h]
    · simp

theorem path_target_local (env : Env) (scope : Snoc String) (path : Path) (level : Int)
    (h : path_target env scope path = some (.Local level)) :
    0 ≤ level ∧ level < length _ scope := by
  cases path with
  | Name name =>
    simp only [path_target] at h
    exact local_lt scope name level (head_local env scope name level h)
  | Member qualifier name =>
    simp only [path_target] at h
    split at h
    · exact absurd h (descend_not_local env _ name level)
    · simp at h

theorem layer_local (env : Env) (scope : Snoc String) (form : SrcF Int) (level : Int)
    (h : resolve_layer Int env scope form = some (.Local level)) :
    0 ≤ level ∧ level < length _ scope := by
  cases form with
  | Name path =>
    simp only [resolve_layer, value_form] at h
    split at h
    · rename_i found eq
      simp at h
      exact path_target_local env scope path level (by simpa [h] using eq)
    · split at h <;> simp at h
    · simp at h
  | Call path args => simp only [resolve_layer] at h; split at h <;> simp at h
  | Let name annotation value body => simp only [resolve_layer] at h; split at h <;> simp at h
  | Match scrutinee arms => simp only [resolve_layer] at h; split at h <;> simp at h
  | _ => simp [resolve_layer] at h

theorem rows_aligned (env : Env) (rows : Snoc SrcRow) (forms : Snoc (ExprF Int))
    (h : resolve_rows env rows = some forms) : length _ forms = length _ rows := by
  induction rows generalizing forms with
  | Empty => simp [resolve_rows] at h; simp [← h, length]
  | Extend earlier row ih =>
    simp only [resolve_rows] at h
    split at h
    · rename_i resolved form he _
      split at h
      · simp at h
        simp [← h, length, ih resolved he]
      · simp at h
    · simp at h

theorem rows_scoped (env : Env) (rows : Snoc SrcRow) (forms : Snoc (ExprF Int))
    (position : Int) (row : SrcRow) (level : Int)
    (h : resolve_rows env rows = some forms) (hr : lookup _ rows position = some row)
    (hf : lookup _ forms position = some (.Local level)) :
    0 ≤ level ∧ level < length _ row.scope := by
  induction rows generalizing forms with
  | Empty => simp [lookup] at hr
  | Extend earlier last ih =>
    simp only [resolve_rows] at h
    split at h
    · rename_i resolved form he hl
      split at h
      · simp at h
        subst h
        have aligned := rows_aligned env earlier resolved he
        simp only [lookup, aligned] at hr hf
        split at hr
        · rename_i at_last
          simp [at_last] at hf
          simp at hr
          subst hr
          exact layer_local env last.scope last.form level (by simpa [hf] using hl)
        · rename_i not_last
          simp [not_last] at hf
          exact ih resolved he hr hf
      · simp at h
    · simp at h

/-! ## Collection -/

/-- Membership in a snoc list. -/
def SMem {α : Type} (x : α) : Snoc α → Prop
  | .Empty => False
  | .Extend earlier y => x = y ∨ SMem x earlier

/-- No identity is bound twice. -/
def SNodup : Snoc Entry → Prop
  | .Empty => True
  | .Extend earlier b => entry earlier b.item = none ∧ SNodup earlier

theorem entry_extend (e : Snoc Entry) (b : Entry) (i : Fren.Seq String) :
    entry (.Extend e b) i = if b.item = i then some b.kind else entry e i := by
  simp only [entry]

theorem entry_none_iff (S : Snoc Entry) (i : Fren.Seq String) :
    entry S i = none ↔ ∀ b, SMem b S → b.item ≠ i := by
  induction S with
  | Empty => simp [entry, SMem]
  | Extend e b ih =>
    rw [entry_extend]
    constructor
    · intro h c hc
      by_cases hb : b.item = i
      · simp [hb] at h
      · simp only [hb, if_false] at h
        rcases hc with rfl | hc
        · exact hb
        · exact ih.mp h c hc
    · intro h
      have hb : b.item ≠ i := h b (Or.inl rfl)
      simp only [hb, if_false]
      exact ih.mpr fun c hc => h c (Or.inr hc)

theorem entry_of_mem (S : Snoc Entry) (b : Entry) (hn : SNodup S) (hm : SMem b S) :
    entry S b.item = some b.kind := by
  induction S with
  | Empty => exact hm.elim
  | Extend e c ih =>
    rw [entry_extend]
    rcases hm with rfl | hm
    · simp
    · have : c.item ≠ b.item := fun h => (entry_none_iff e c.item).mp hn.1 b hm h.symm
      simp only [this, if_false]
      exact ih hn.2 hm

theorem mem_of_entry (S : Snoc Entry) (i : Fren.Seq String) (k : ItemKind)
    (h : entry S i = some k) : SMem { item := i, kind := k } S := by
  induction S with
  | Empty => simp [entry] at h
  | Extend e b ih =>
    rw [entry_extend] at h
    by_cases hb : b.item = i
    · simp only [hb, if_true, Option.some.injEq] at h
      left
      cases b
      simp_all
    · simp only [hb, if_false] at h
      exact Or.inr (ih h)

theorem local_none_iff (s : Snoc String) (n : String) :
    resolve_local s n = none ↔ ¬ SMem n s := by
  induction s with
  | Empty => simp [resolve_local, SMem]
  | Extend e m ih =>
    simp only [resolve_local, SMem]
    split
    · rename_i eq
      simp [eq]
    · rename_i ne
      rw [ih]
      constructor
      · intro h h2
        rcases h2 with rfl | h2
        · exact ne rfl
        · exact h h2
      · intro h h2
        exact h (Or.inr h2)

theorem child_inj (p : Fren.Seq String) (a b : String) (h : child p a = child p b) : a = b := by
  have := congrArg Fren.Seq.toList h
  simpa using this

theorem child_ne_deeper (p : Fren.Seq String) (a b c : String) :
    child (child p a) b ≠ child p c := by
  intro h
  have := congrArg (fun q => q.toList.length) h
  simp at this

theorem child_child_inj (p : Fren.Seq String) (a b c d : String)
    (h : child (child p a) b = child (child p c) d) : a = c ∧ b = d := by
  have := congrArg Fren.Seq.toList h
  simpa using this

theorem member_constructors (o : Fren.Seq String) (vs : Snoc String) (i : Fren.Seq String) :
    member? (constructors o vs) i = true ↔ ∃ v, SMem v vs ∧ i = child o v := by
  induction vs with
  | Empty => simp [constructors, member?, SMem]
  | Extend e v ih =>
    simp only [constructors, member?, SMem, decide_eq_true_eq, ih]
    constructor
    · rintro (h | ⟨w, hw, rfl⟩)
      · exact ⟨v, Or.inl rfl, h.symm⟩
      · exact ⟨w, Or.inr hw, rfl⟩
    · rintro ⟨w, rfl | hw, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hw, rfl⟩

theorem mem_bind_constructors (S : Snoc Entry) (o : Fren.Seq String) (vs : Snoc String) (b : Entry) :
    SMem b (bind_constructors S o vs) ↔
      SMem b S ∨ ∃ v, SMem v vs ∧ b = { item := child o v, kind := .Constructor o } := by
  induction vs with
  | Empty => simp [bind_constructors, SMem]
  | Extend e v ih =>
    simp only [bind_constructors, SMem, ih]
    constructor
    · rintro (h | h | ⟨w, hw, h⟩)
      · exact Or.inr ⟨v, Or.inl rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨w, Or.inr hw, h⟩
    · rintro (h | ⟨w, rfl | hw, h⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨w, hw, h⟩)

/-- What the first step of collection binds. -/
theorem mem_collect_types (M : Fren.Seq String) (ds : Snoc SrcDecl) (b : Entry) :
    SMem b (collect_types M ds) ↔ ∃ x vs, SMem (SrcDecl.Enumeration x vs) ds ∧
      (b = { item := child M x, kind := .Enumeration (constructors (child M x) vs) } ∨
        ∃ v, SMem v vs ∧ b = { item := child (child M x) v, kind := .Constructor (child M x) }) := by
  induction ds with
  | Empty => simp [collect_types, SMem]
  | Extend e d ih =>
    cases d with
    | Enumeration x vs =>
      simp only [collect_types, mem_bind_constructors, SMem, ih]
      constructor
      · rintro ((h | ⟨y, ws, hd, h⟩) | h)
        · exact ⟨x, vs, Or.inl rfl, Or.inl h⟩
        · exact ⟨y, ws, Or.inr hd, h⟩
        · exact ⟨x, vs, Or.inl rfl, Or.inr h⟩
      · rintro ⟨y, ws, hd | hd, h⟩
        · cases hd
          rcases h with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · exact Or.inl (Or.inr ⟨y, ws, hd, h⟩)
    | Function f ps r body =>
      simp only [collect_types, SMem, ih]
      constructor
      · rintro ⟨y, ws, hd, h⟩
        exact ⟨y, ws, Or.inr hd, h⟩
      · rintro ⟨y, ws, hd | hd, h⟩
        · cases hd
        · exact ⟨y, ws, hd, h⟩

/-- What the second step of collection adds. -/
theorem mem_collect_functions (env : Env) (ds : Snoc SrcDecl) (S : Snoc Entry) (b : Entry)
    (h : collect_functions env ds = some S) (hb : SMem b S) :
    SMem b env.symb ∨ ∃ f ps r body sig, SMem (SrcDecl.Function f ps r body) ds ∧
      signature env ps r = some sig ∧
      b = { item := child (module_of env) f, kind := .Function sig } := by
  induction ds generalizing S with
  | Empty =>
    simp only [collect_functions, Option.some.injEq] at h
    exact Or.inl (h ▸ hb)
  | Extend e d ih =>
    cases d with
    | Enumeration x vs =>
      simp only [collect_functions] at h
      rcases ih S h hb with h1 | ⟨f, ps, r, body, sig, hd, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨f, ps, r, body, sig, Or.inr hd, h2⟩
    | Function f ps r body =>
      simp only [collect_functions] at h
      split at h
      · rename_i S0 sig hS hsig
        simp only [Option.some.injEq] at h
        subst h
        rcases hb with rfl | hb
        · exact Or.inr ⟨f, ps, r, body, sig, Or.inl rfl, hsig, rfl⟩
        · rcases ih S0 hS hb with h1 | ⟨f', ps', r', body', sig', hd, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨f', ps', r', body', sig', Or.inr hd, h2⟩
      · simp at h

theorem mem_collect_functions_base (env : Env) (ds : Snoc SrcDecl) (S : Snoc Entry) (b : Entry)
    (h : collect_functions env ds = some S) (hb : SMem b env.symb) : SMem b S := by
  induction ds generalizing S with
  | Empty =>
    simp only [collect_functions, Option.some.injEq] at h
    exact h ▸ hb
  | Extend e d ih =>
    cases d with
    | Enumeration x vs =>
      simp only [collect_functions] at h
      exact ih S h
    | Function f ps r body =>
      simp only [collect_functions] at h
      split at h
      · rename_i S0 sig hS hsig
        simp only [Option.some.injEq] at h
        subst h
        exact Or.inr (ih S0 hS)
      · simp at h

theorem decl_name_mem (ds : Snoc SrcDecl) (d : SrcDecl) (h : SMem d ds) :
    SMem (decl_name d) (item_names ds) := by
  induction ds with
  | Empty => exact h.elim
  | Extend e c ih =>
    simp only [item_names, SMem]
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (ih h)

theorem distinct_extend (s : Snoc String) (n : String) :
    distinct? (.Extend s n) = true ↔ ¬ SMem n s ∧ distinct? s = true := by
  simp only [distinct?, decide_eq_true_eq, local_none_iff]

theorem enum_ok_distinct (x : String) (vs : Snoc String)
    (h : decl_names_ok? (SrcDecl.Enumeration x vs) = true) : distinct? vs = true := by
  simp [decl_names_ok?, fren_spec] at h
  exact h.2

theorem decls_ok_mem (ds : Snoc SrcDecl) (d : SrcDecl) (h : decls_names_ok? ds = true)
    (hd : SMem d ds) : decl_names_ok? d = true := by
  induction ds with
  | Empty => exact hd.elim
  | Extend e c ih =>
    simp only [decls_names_ok?, decide_eq_true_eq] at h
    rcases hd with rfl | hd
    · simp only [decl_names_ok?, decide_eq_true_eq]
      exact h.2
    · exact ih h.1 hd

theorem variants_distinct (ds : Snoc SrcDecl) (x : String) (vs : Snoc String)
    (h : decls_names_ok? ds = true) (hd : SMem (SrcDecl.Enumeration x vs) ds) :
    distinct? vs = true := by
  exact enum_ok_distinct x vs (decls_ok_mem ds _ h hd)

theorem nodup_bind (S : Snoc Entry) (o : Fren.Seq String) (vs : Snoc String) (hn : SNodup S)
    (hd : distinct? vs = true) (hf : ∀ v, SMem v vs → entry S (child o v) = none) :
    SNodup (bind_constructors S o vs) := by
  induction vs with
  | Empty => exact hn
  | Extend e v ih =>
    rw [distinct_extend] at hd
    simp only [bind_constructors, SNodup]
    refine ⟨?_, ih hd.2 fun w hw => hf w (Or.inr hw)⟩
    rw [entry_none_iff]
    intro b hb heq
    rw [mem_bind_constructors] at hb
    rcases hb with hb | ⟨w, hw, rfl⟩
    · exact (entry_none_iff S _).mp (hf v (Or.inl rfl)) b hb heq
    · exact hd.1 (child_inj o w v heq ▸ hw)

theorem nodup_types (M : Fren.Seq String) (ds : Snoc SrcDecl)
    (hd : distinct? (item_names ds) = true) (ho : decls_names_ok? ds = true) :
    SNodup (collect_types M ds) := by
  induction ds with
  | Empty => trivial
  | Extend e d ih =>
    simp only [item_names] at hd
    rw [distinct_extend] at hd
    simp only [decls_names_ok?, decide_eq_true_eq] at ho
    cases d with
    | Function f ps r body => exact ih hd.2 ho.1
    | Enumeration x vs =>
      have fresh : ∀ y ws, SMem (SrcDecl.Enumeration y ws) e → y ≠ x := by
        intro y ws hy heq
        have hm : SMem y (item_names e) := decl_name_mem e _ hy
        exact hd.1 (heq ▸ hm)
      simp only [collect_types]
      apply nodup_bind
      · refine ⟨?_, ih hd.2 ho.1⟩
        rw [entry_none_iff]
        intro b hb heq
        rw [mem_collect_types] at hb
        rcases hb with ⟨y, ws, hy, rfl | ⟨v, _, rfl⟩⟩
        · exact fresh y ws hy (child_inj M y x heq)
        · exact child_ne_deeper M y v x heq
      · have h2 := ho.2
        simp [fren_spec] at h2
        exact h2.2
      · intro v _
        rw [entry_none_iff]
        intro b hb heq
        rcases hb with rfl | hb
        · exact child_ne_deeper M x v x heq.symm
        · rw [mem_collect_types] at hb
          rcases hb with ⟨y, ws, hy, rfl | ⟨w, _, rfl⟩⟩
          · exact child_ne_deeper M x v y heq.symm
          · exact fresh y ws hy (child_child_inj M y w x v heq).1

theorem nodup_functions (env : Env) (ds : Snoc SrcDecl) (S : Snoc Entry)
    (h : collect_functions env ds = some S) (hn : SNodup env.symb)
    (hd : distinct? (item_names ds) = true)
    (hf : ∀ b f ps r body, SMem b env.symb → SMem (SrcDecl.Function f ps r body) ds →
      b.item ≠ child (module_of env) f) : SNodup S := by
  induction ds generalizing S with
  | Empty =>
    simp only [collect_functions, Option.some.injEq] at h
    exact h ▸ hn
  | Extend e d ih =>
    simp only [item_names] at hd
    rw [distinct_extend] at hd
    have hf' : ∀ b f ps r body, SMem b env.symb → SMem (SrcDecl.Function f ps r body) e →
        b.item ≠ child (module_of env) f :=
      fun b f ps r body hb hd => hf b f ps r body hb (Or.inr hd)
    cases d with
    | Enumeration x vs =>
      simp only [collect_functions] at h
      exact ih S h hd.2 hf'
    | Function f ps r body =>
      simp only [collect_functions] at h
      split at h
      · rename_i S0 sig hS hsig
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨?_, ih S0 hS hd.2 hf'⟩
        rw [entry_none_iff]
        intro b hb heq
        rcases mem_collect_functions env e S0 b hS hb with hb | ⟨g, ps', r', body', sig', hg, _, rfl⟩
        · exact hf b f ps r body hb (Or.inl rfl) heq
        · have : g = f := child_inj _ g f heq
          have hm : SMem g (item_names e) := decl_name_mem e _ hg
          exact hd.1 (this ▸ hm)
      · simp at h

theorem distinct_decl (ds : Snoc SrcDecl) (d1 d2 : SrcDecl)
    (hd : distinct? (item_names ds) = true) (h1 : SMem d1 ds) (h2 : SMem d2 ds)
    (heq : decl_name d1 = decl_name d2) : d1 = d2 := by
  induction ds with
  | Empty => exact h1.elim
  | Extend e c ih =>
    simp only [item_names] at hd
    rw [distinct_extend] at hd
    rcases h1 with e1 | h1 <;> rcases h2 with e2 | h2
    · rw [e1, e2]
    · rw [e1] at heq
      have hm := decl_name_mem e _ h2
      rw [← heq] at hm
      exact (hd.1 hm).elim
    · rw [e2] at heq
      have hm := decl_name_mem e _ h1
      rw [heq] at hm
      exact (hd.1 hm).elim
    · exact ih hd.2 h1 h2

theorem bindings_ok_iff (S l : Snoc Entry) :
    bindings_ok? S l = true ↔ SNodup l ∧ ∀ b, SMem b l → binding_ok? S b = true := by
  induction l with
  | Empty => simp [bindings_ok?, SNodup, SMem]
  | Extend e b ih =>
    simp only [bindings_ok?, decide_eq_true_eq, ih, SNodup]
    constructor
    · rintro ⟨⟨fresh, ok⟩, nodup, rest⟩
      refine ⟨⟨fresh, nodup⟩, ?_⟩
      intro x hx
      rcases hx with rfl | hx
      · exact ok
      · exact rest x hx
    · rintro ⟨⟨fresh, nodup⟩, all⟩
      exact ⟨⟨fresh, all b (Or.inl rfl)⟩, nodup, fun x hx => all x (Or.inr hx)⟩

theorem binding_ok_function (S : Snoc Entry) (i : Fren.Seq String) (sig : Sig)
    (hp : ctx_ok? S sig.params = true) (hr : ty_ok? S sig.result = true) :
    binding_ok? S { item := i, kind := .Function sig } = true := by
  simp only [ty_ok?, decide_eq_true_eq] at hr
  simp [binding_ok?, fren_spec, hp]
  simp [fren_spec] at hr
  exact (Classical.em _).elim (fun h => Or.inr (hr h)) Or.inl

theorem binding_ok_constructor (S : Snoc Entry) (i o : Fren.Seq String)
    (cs : Snoc (Fren.Seq String)) (h : entry S o = some (.Enumeration cs))
    (hm : member? cs i = true) : binding_ok? S { item := i, kind := .Constructor o } = true := by
  simp [binding_ok?, fren_spec, h, hm]

theorem binding_ok_enumeration (S : Snoc Entry) (i : Fren.Seq String)
    (cs : Snoc (Fren.Seq String)) (h : constructors_ok? S cs i = true) :
    binding_ok? S { item := i, kind := .Enumeration cs } = true := by
  simp [binding_ok?, fren_spec, h]

theorem constructors_ok_of (S : Snoc Entry) (o : Fren.Seq String) (vs : Snoc String)
    (hd : distinct? vs = true)
    (hf : ∀ v, SMem v vs → entry S (child o v) = some (.Constructor o)) :
    constructors_ok? S (constructors o vs) o = true := by
  induction vs with
  | Empty => simp [constructors, constructors_ok?]
  | Extend e v ih =>
    rw [distinct_extend] at hd
    simp only [constructors, constructors_ok?, decide_eq_true_eq]
    refine ⟨⟨hf v (Or.inl rfl), ?_⟩, ih hd.2 fun w hw => hf w (Or.inr hw)⟩
    rw [member_constructors]
    rintro ⟨w, hw, heq⟩
    have := child_inj o v w heq
    subst this
    exact hd.1 hw

theorem resolve_type_ok (env : Env) (S : Snoc Entry) (t : spec.names.TypeName) (ty : Ty)
    (h : resolve_type env t = some ty)
    (mono : ∀ i k, entry env.symb i = some k → entry S i = some k) : ty_ok? S ty = true := by
  cases t with
  | Boolean =>
    simp only [resolve_type, Option.some.injEq] at h
    subst h
    simp [ty_ok?]
  | Integer =>
    simp only [resolve_type, Option.some.injEq] at h
    subst h
    simp [ty_ok?]
  | Named path =>
    simp only [resolve_type, type_item] at h
    split at h
    · rename_i item hitem
      split at hitem
      · split at hitem
        · rename_i cs hentry
          simp only [Option.some.injEq] at hitem h
          subst h hitem
          simp [ty_ok?, fren_spec, mono _ _ hentry]
        · simp at hitem
      · simp at hitem
    · simp at h

theorem resolve_params_ok (env : Env) (S : Snoc Entry) (ps : Snoc Param) (ctx : Snoc Ty)
    (h : resolve_params env ps = some ctx)
    (mono : ∀ i k, entry env.symb i = some k → entry S i = some k) : ctx_ok? S ctx = true := by
  induction ps generalizing ctx with
  | Empty =>
    simp only [resolve_params, Option.some.injEq] at h
    subst h
    simp [ctx_ok?]
  | Extend e p ih =>
    simp only [resolve_params] at h
    split at h
    · rename_i c ty hc hty
      simp only [Option.some.injEq] at h
      subst h
      show decide (ty_ok? S ty = true ∧ ctx_ok? S c = true) = true
      exact decide_eq_true ⟨resolve_type_ok env S p.ty ty hty mono, ih c hc⟩
    · simp at h

/-- Collection yields a well-formed symbol environment. -/
theorem collect_ok (parent : Fren.Seq String) (name : String) (ds : Snoc SrcDecl)
    (S : Snoc Entry) (h : collect parent name ds = some S) : symb_ok? S = true := by
  simp only [collect] at h
  split at h
  · rename_i hok
    simp only [names_ok?, decide_eq_true_eq] at hok
    have hT := nodup_types (child parent name) ds hok.1.1 hok.1.2
    have hN : SNodup S := by
      refine nodup_functions _ ds S h hT hok.1.1 ?_
      intro b f ps r body hb hd heq
      rw [mem_collect_types] at hb
      rcases hb with ⟨y, ws, hy, rfl | ⟨v, _, rfl⟩⟩
      · have : y = f := child_inj _ y f heq
        have e := distinct_decl ds (.Enumeration y ws) (.Function f ps r body) hok.1.1 hy hd this
        cases e
      · exact child_ne_deeper _ y v f heq
    have mono : ∀ i k, entry (collect_types (child parent name) ds) i = some k →
        entry S i = some k := fun i k hk =>
      entry_of_mem S { item := i, kind := k } hN
        (mem_collect_functions_base _ ds S _ h (mem_of_entry _ i k hk))
    simp only [symb_ok?, decide_eq_true_eq]
    rw [bindings_ok_iff]
    refine ⟨hN, ?_⟩
    intro b hb
    rcases mem_collect_functions _ ds S b h hb with hb0 | ⟨f, ps, r, body, sig, hd, hsig, rfl⟩
    · rw [mem_collect_types] at hb0
      rcases hb0 with ⟨x, vs, hx, rfl | ⟨v, hv, rfl⟩⟩
      · apply binding_ok_enumeration
        apply constructors_ok_of _ _ _ (variants_distinct ds x vs hok.1.2 hx)
        intro v hv
        exact mono _ _ (entry_of_mem _ { item := _, kind := .Constructor _ } hT
          ((mem_collect_types _ ds _).mpr ⟨x, vs, hx, Or.inr ⟨v, hv, rfl⟩⟩))
      · exact binding_ok_constructor S _ _ _
          (mono _ _ (entry_of_mem _ { item := _, kind := .Enumeration _ } hT
            ((mem_collect_types _ ds _).mpr ⟨x, vs, hx, Or.inl rfl⟩)))
          ((member_constructors _ vs _).mpr ⟨v, hv, rfl⟩)
    · simp only [signature] at hsig
      split at hsig
      · rename_i ctx ty hc hty
        simp only [Option.some.injEq] at hsig
        subst hsig
        exact binding_ok_function S _ _ (resolve_params_ok _ S ps ctx hc mono)
          (resolve_type_ok _ S r ty hty mono)
      · simp at hsig
  · simp at h

/-! ## Order of declarations -/

theorem entry_congr (A B : Snoc Entry) (hA : SNodup A) (hB : SNodup B)
    (hAB : ∀ b, SMem b A → SMem b B) (hBA : ∀ b, SMem b B → SMem b A) (i : Fren.Seq String) :
    entry A i = entry B i := by
  cases hA' : entry A i with
  | some k => exact (entry_of_mem B { item := i, kind := k } hB (hAB _ (mem_of_entry A i k hA'))).symm
  | none =>
    cases hB' : entry B i with
    | none => rfl
    | some k =>
      have : entry A i = some k :=
        entry_of_mem A { item := i, kind := k } hA (hBA _ (mem_of_entry B i k hB'))
      rw [hA'] at this
      cases this

theorem path_target_congr (p : Fren.Seq String) (n : String) (A B : Snoc Entry)
    (hE : ∀ i, entry A i = entry B i) (scope : Snoc String) (path : Path) :
    path_target { parent := p, name := n, symb := A } scope path =
      path_target { parent := p, name := n, symb := B } scope path := by
  induction path with
  | Name name => simp only [path_target, head, item_target, hE]
  | Member qualifier name ih =>
    simp only [path_target, ih]
    cases path_target { parent := p, name := n, symb := B } scope qualifier with
    | none => rfl
    | some target => cases target <;> simp only [descend, item_target, hE]

theorem signature_congr (p : Fren.Seq String) (n : String) (A B : Snoc Entry)
    (hE : ∀ i, entry A i = entry B i) (ps : Snoc Param) (r : spec.names.TypeName) :
    signature { parent := p, name := n, symb := A } ps r =
      signature { parent := p, name := n, symb := B } ps r := by
  have ty : ∀ t, resolve_type { parent := p, name := n, symb := A } t =
      resolve_type { parent := p, name := n, symb := B } t := by
    intro t
    cases t <;> simp only [resolve_type, type_item, path_target_congr p n A B hE, hE]
  have params : resolve_params { parent := p, name := n, symb := A } ps =
      resolve_params { parent := p, name := n, symb := B } ps := by
    induction ps with
    | Empty => simp only [resolve_params]
    | Extend e q ih => simp only [resolve_params, ih, ty]
  simp only [signature, params, ty]

theorem collect_functions_none (env : Env) (ds : Snoc SrcDecl) :
    collect_functions env ds = none ↔
      ∃ f ps r body, SMem (SrcDecl.Function f ps r body) ds ∧ signature env ps r = none := by
  induction ds with
  | Empty => simp [collect_functions, SMem]
  | Extend e d ih =>
    cases d with
    | Enumeration x vs =>
      simp only [collect_functions, ih]
      constructor
      · rintro ⟨f, ps, r, body, hd, hs⟩
        exact ⟨f, ps, r, body, Or.inr hd, hs⟩
      · rintro ⟨f, ps, r, body, hd | hd, hs⟩
        · cases hd
        · exact ⟨f, ps, r, body, hd, hs⟩
    | Function f ps r body =>
      simp only [collect_functions]
      cases hcf : collect_functions env e with
      | none =>
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        obtain ⟨g, ps', r', body', hd, hs⟩ := ih.mp hcf
        exact ⟨g, ps', r', body', Or.inr hd, hs⟩
      | some S0 =>
        cases hs : signature env ps r with
        | none => exact ⟨fun _ => ⟨f, ps, r, body, Or.inl rfl, hs⟩, fun _ => rfl⟩
        | some sig =>
          refine ⟨fun h => by simp at h, ?_⟩
          rintro ⟨g, ps', r', body', hd | hd, hs'⟩
          · cases hd
            rw [hs] at hs'
            cases hs'
          · have := ih.mpr ⟨g, ps', r', body', hd, hs'⟩
            rw [hcf] at this
            cases this

theorem mem_collect_functions_fn (env : Env) (ds : Snoc SrcDecl) (S : Snoc Entry) (f : String)
    (ps : Snoc Param) (r : spec.names.TypeName) (body : Snoc SrcRow) (sig : Sig)
    (h : collect_functions env ds = some S) (hd : SMem (SrcDecl.Function f ps r body) ds)
    (hsig : signature env ps r = some sig) :
    SMem { item := child (module_of env) f, kind := .Function sig } S := by
  induction ds generalizing S with
  | Empty => exact hd.elim
  | Extend e d ih =>
    cases d with
    | Enumeration x vs =>
      simp only [collect_functions] at h
      rcases hd with hd | hd
      · cases hd
      · exact ih S h hd
    | Function f' ps' r' body' =>
      simp only [collect_functions] at h
      split at h
      · rename_i S0 sig' hS hsig'
        simp only [Option.some.injEq] at h
        subst h
        rcases hd with hd | hd
        · cases hd
          rw [hsig'] at hsig
          cases hsig
          exact Or.inl rfl
        · exact Or.inr (ih S0 hS hd)
      · simp at h

theorem distinct_swap (s : Snoc String) (a b : String)
    (h : distinct? (.Extend (.Extend s a) b) = true) : distinct? (.Extend (.Extend s b) a) = true := by
  rw [distinct_extend, distinct_extend] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun h => ?_, fun h => h1 (Or.inr h), h3⟩
  rcases h with e | h
  · exact h1 (Or.inl e.symm)
  · exact h2 h

theorem declares_function_swap (ds : Snoc SrcDecl) (a b : SrcDecl) (x : String) :
    declares_function? (.Extend (.Extend ds a) b) x
      = declares_function? (.Extend (.Extend ds b) a) x := by
  cases a <;> cases b <;> simp [declares_function?, fren_spec, Bool.or_left_comm]

theorem decls_clear_congr (A B ds : Snoc SrcDecl)
    (h : ∀ x, declares_function? A x = declares_function? B x) :
    decls_clear? A ds = decls_clear? B ds := by
  have ty : ∀ t, type_clear? A t = type_clear? B t := by
    intro t
    cases t <;> simp [type_clear?, h, fren_spec]
  have ps : ∀ p, params_clear? A p = params_clear? B p := by
    intro p
    induction p with
    | Empty => simp [params_clear?]
    | Extend e q ih => simp [params_clear?, ih, ty]
  induction ds with
  | Empty => simp [decls_clear?]
  | Extend e d ih => cases d <;> simp [decls_clear?, ih, ps, h, fren_spec]

theorem decls_clear_exchange (X ds : Snoc SrcDecl) (a b : SrcDecl) :
    decls_clear? X (.Extend (.Extend ds b) a) = decls_clear? X (.Extend (.Extend ds a) b) := by
  cases a <;> cases b <;>
    simp [decls_clear?, fren_spec, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem decls_clear_swap (ds : Snoc SrcDecl) (a b : SrcDecl)
    (h : decls_clear? (.Extend (.Extend ds a) b) (.Extend (.Extend ds a) b) = true) :
    decls_clear? (.Extend (.Extend ds b) a) (.Extend (.Extend ds b) a) = true := by
  rw [decls_clear_congr _ (.Extend (.Extend ds a) b) _
    (fun x => declares_function_swap ds b a x), decls_clear_exchange]
  exact h

theorem names_ok_swap (ds : Snoc SrcDecl) (a b : SrcDecl)
    (h : names_ok? (.Extend (.Extend ds a) b) = true) : names_ok? (.Extend (.Extend ds b) a) = true := by
  simp only [names_ok?, decide_eq_true_eq] at h ⊢
  refine ⟨⟨distinct_swap (item_names ds) (decl_name a) (decl_name b) h.1.1, ?_⟩,
    decls_clear_swap ds a b h.2⟩
  have h2 := h.1.2
  simp only [decls_names_ok?, decide_eq_true_eq] at h2 ⊢
  exact ⟨⟨h2.1.1, h2.2⟩, h2.1.2⟩

theorem types_entry (M : Fren.Seq String) (ds1 ds2 : Snoc SrcDecl)
    (hP : ∀ d, SMem d ds1 → SMem d ds2) (hQ : ∀ d, SMem d ds2 → SMem d ds1)
    (ok1 : names_ok? ds1 = true) (ok2 : names_ok? ds2 = true) (i : Fren.Seq String) :
    entry (collect_types M ds1) i = entry (collect_types M ds2) i := by
  simp only [names_ok?, decide_eq_true_eq] at ok1 ok2
  refine entry_congr _ _ (nodup_types M ds1 ok1.1.1 ok1.1.2) (nodup_types M ds2 ok2.1.1 ok2.1.2) ?_ ?_ i
  · intro b hb
    rw [mem_collect_types] at hb ⊢
    obtain ⟨x, vs, hx, h⟩ := hb
    exact ⟨x, vs, hP _ hx, h⟩
  · intro b hb
    rw [mem_collect_types] at hb ⊢
    obtain ⟨x, vs, hx, h⟩ := hb
    exact ⟨x, vs, hQ _ hx, h⟩

theorem collect_none_sub (p : Fren.Seq String) (n : String) (ds1 ds2 : Snoc SrcDecl)
    (hP : ∀ d, SMem d ds1 → SMem d ds2) (hQ : ∀ d, SMem d ds2 → SMem d ds1)
    (ok12 : names_ok? ds1 = true → names_ok? ds2 = true)
    (ok21 : names_ok? ds2 = true → names_ok? ds1 = true)
    (h : collect p n ds1 = none) : collect p n ds2 = none := by
  simp only [collect] at h ⊢
  by_cases ok1 : names_ok? ds1 = true
  · have ok2 := ok12 ok1
    rw [if_pos ok1] at h
    rw [if_pos ok2]
    rw [collect_functions_none] at h ⊢
    obtain ⟨f, ps, r, body, hd, hs⟩ := h
    refine ⟨f, ps, r, body, hP _ hd, ?_⟩
    exact (signature_congr p n _ _ (fun i => (types_entry _ ds1 ds2 hP hQ ok1 ok2 i).symm) ps r).trans hs
  · have ok2 : ¬ names_ok? ds2 = true := fun h2 => ok1 (ok21 h2)
    rw [if_neg ok2]

theorem collect_mem_sub (p : Fren.Seq String) (n : String) (ds1 ds2 : Snoc SrcDecl)
    (hP : ∀ d, SMem d ds1 → SMem d ds2) (hQ : ∀ d, SMem d ds2 → SMem d ds1)
    (left right : Snoc Entry) (h1 : collect p n ds1 = some left)
    (h2 : collect p n ds2 = some right) (b : Entry) (hb : SMem b left) : SMem b right := by
  simp only [collect] at h1 h2
  split at h1
  · rename_i ok1
    split at h2
    · rename_i ok2
      rcases mem_collect_functions _ ds1 left b h1 hb with hb0 | ⟨f, ps, r, body, sig, hd, hsig, rfl⟩
      · rw [mem_collect_types] at hb0
        obtain ⟨x, vs, hx, h⟩ := hb0
        exact mem_collect_functions_base _ ds2 right b h2
          ((mem_collect_types _ ds2 b).mpr ⟨x, vs, hP _ hx, h⟩)
      · have hs2 : signature { parent := p, name := n, symb := collect_types (child p n) ds2 } ps r =
            some sig :=
          (signature_congr p n (collect_types (child p n) ds2) (collect_types (child p n) ds1)
            (fun i => (types_entry (child p n) ds1 ds2 hP hQ ok1 ok2 i).symm) ps r).trans hsig
        have hm := mem_collect_functions_fn _ ds2 right f ps r body sig h2 (hP _ hd) hs2
        exact hm
    · simp at h2
  · simp at h1

theorem nodup_of_ok (S : Snoc Entry) (h : symb_ok? S = true) : SNodup S := by
  simp only [symb_ok?, decide_eq_true_eq] at h
  exact ((bindings_ok_iff S S).mp h).1

theorem swap_mem (ds : Snoc SrcDecl) (a b d : SrcDecl)
    (h : SMem d (.Extend (.Extend ds a) b)) : SMem d (.Extend (.Extend ds b) a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- Exchanging the last two declarations changes neither whether collection
succeeds nor what it binds. -/
theorem collect_exchange (p : Fren.Seq String) (n : String) (ds : Snoc SrcDecl) (a b : SrcDecl) :
    (collect p n (.Extend (.Extend ds a) b) = none ↔ collect p n (.Extend (.Extend ds b) a) = none) ∧
    ∀ left right item, collect p n (.Extend (.Extend ds a) b) = some left →
      collect p n (.Extend (.Extend ds b) a) = some right → entry left item = entry right item := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact collect_none_sub p n _ _ (swap_mem ds a b) (swap_mem ds b a) (names_ok_swap ds a b)
      (names_ok_swap ds b a)
  · exact collect_none_sub p n _ _ (swap_mem ds b a) (swap_mem ds a b) (names_ok_swap ds b a)
      (names_ok_swap ds a b)
  · intro left right item h1 h2
    exact entry_congr left right (nodup_of_ok left (collect_ok p n _ left h1))
      (nodup_of_ok right (collect_ok p n _ right h2))
      (collect_mem_sub p n _ _ (swap_mem ds a b) (swap_mem ds b a) left right h1 h2)
      (collect_mem_sub p n _ _ (swap_mem ds b a) (swap_mem ds a b) right left h2 h1) item


theorem declares_iff (ds : Snoc SrcDecl) (d : SrcDecl) : declares? ds d = true ↔ SMem d ds := by
  induction ds with
  | Empty => simp [declares?, SMem]
  | Extend e c ih =>
    simp only [declares?, decide_eq_true_eq, ih, SMem]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem included_mem (a b : Snoc SrcDecl) (h : included? a b = true) (d : SrcDecl)
    (hd : SMem d a) : SMem d b := by
  induction a with
  | Empty => exact hd.elim
  | Extend e c ih =>
    simp only [included?, decide_eq_true_eq] at h
    rcases hd with rfl | hd
    · exact (declares_iff b _).mp h.2
    · exact ih h.1 hd

/-- Two sequences of the same declarations, neither with a naming error,
collect alike. -/
theorem collect_same (p : Fren.Seq String) (n : String) (a b : Snoc SrcDecl)
    (hab : included? a b = true) (hba : included? b a = true) :
    (names_ok? a = true → names_ok? b = true →
      (collect p n a = none ↔ collect p n b = none)) ∧
    ∀ left right item, collect p n a = some left → collect p n b = some right →
      entry left item = entry right item := by
  refine ⟨fun oka okb => ⟨?_, ?_⟩, ?_⟩
  · exact collect_none_sub p n a b (included_mem a b hab) (included_mem b a hba) (fun _ => okb)
      (fun _ => oka)
  · exact collect_none_sub p n b a (included_mem b a hba) (included_mem a b hab) (fun _ => oka)
      (fun _ => okb)
  · intro left right item h1 h2
    exact entry_congr left right (nodup_of_ok left (collect_ok p n _ left h1))
      (nodup_of_ok right (collect_ok p n _ right h2))
      (collect_mem_sub p n a b (included_mem a b hab) (included_mem b a hba) left right h1 h2)
      (collect_mem_sub p n b a (included_mem b a hba) (included_mem a b hab) right left h2 h1) item

/-! ## Weakening -/

/-- The shift of a target: only a local has a level. -/
def shiftTarget (cutoff : Int) : Target → Target
  | .Local level => .Local (shift level cutoff)
  | target => target

theorem head_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra name : String)
    (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope) (ne : name ≠ extra) :
    head env (insert_name scope cutoff extra) name
      = (head env scope name).map (shiftTarget cutoff) := by
  simp only [head, local_weakens scope cutoff extra name h0 h1 ne]
  cases resolve_local scope name with
  | some level => simp [shiftTarget]
  | none =>
    rcases item_target_cases env.symb (child (module_of env) name) with h | h
    · simp only [h]; split <;> simp [shiftTarget]
    · simp [h, shiftTarget]

theorem descend_shift (env : Env) (target : Target) (cutoff : Int) (name : String) :
    descend env (shiftTarget cutoff target) name
      = (descend env target name).map (shiftTarget cutoff) := by
  cases target with
  | Local level => simp [descend, shiftTarget]
  | Module =>
    simp only [descend, shiftTarget]
    rcases item_target_cases env.symb (child (module_of env) name) with h | h <;> simp [h, shiftTarget]
  | Item item =>
    simp only [descend, shiftTarget]
    split
    · rcases item_target_cases env.symb (child item name) with h | h <;> simp [h, shiftTarget]
    · simp

theorem path_target_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    path_target env (insert_name scope cutoff extra) path
      = (path_target env scope path).map (shiftTarget cutoff) := by
  induction path with
  | Name name => exact head_weakens env scope cutoff extra name h0 h1 (by simpa [path_head] using ne)
  | Member qualifier name ih =>
    simp only [path_target, ih (by simpa [path_head] using ne)]
    cases path_target env scope qualifier with
    | none => simp
    | some target => simp [descend_shift]

theorem value_form_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    value_form Int env (insert_name scope cutoff extra) path
      = shifted_form (value_form Int env scope path) cutoff := by
  simp only [value_form, path_target_weakens env scope cutoff extra path h0 h1 ne]
  cases path_target env scope path with
  | none => simp [shifted_form]
  | some target =>
    cases target with
    | Local level => simp [shiftTarget, shifted_form, shift_form]
    | Module => simp [shiftTarget, shifted_form]
    | Item item =>
      simp only [Option.map, shiftTarget]
      split <;> simp [shifted_form, shift_form]

theorem callee_item_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    callee_item env (insert_name scope cutoff extra) path = callee_item env scope path := by
  simp only [callee_item, path_target_weakens env scope cutoff extra path h0 h1 ne]
  cases path_target env scope path with
  | none => simp
  | some target => cases target <;> simp [shiftTarget]

theorem pattern_item_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    pattern_item env (insert_name scope cutoff extra) path = pattern_item env scope path := by
  simp only [pattern_item, path_target_weakens env scope cutoff extra path h0 h1 ne]
  cases path_target env scope path with
  | none => simp
  | some target => cases target <;> simp [shiftTarget]

theorem resolve_arms_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (arms : Snoc (SrcArm Int)) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : arms_mention? arms extra = false) :
    resolve_arms Int env (insert_name scope cutoff extra) arms = resolve_arms Int env scope arms := by
  induction arms with
  | Empty => simp [resolve_arms]
  | Extend earlier arm ih =>
    simp [arms_mention?] at ne
    simp only [resolve_arms, ih ne.2,
      pattern_item_weakens env scope cutoff extra arm.pattern h0 h1 ne.1]

theorem layer_weakens (env : Env) (scope : Snoc String) (form : SrcF Int) (cutoff : Int)
    (extra : String) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : mentions? form extra = false) :
    resolve_layer Int env (insert_name scope cutoff extra) form
      = shifted_form (resolve_layer Int env scope form) cutoff := by
  cases form with
  | Name path =>
    simp [mentions?, fren_spec] at ne
    simpa [resolve_layer] using value_form_weakens env scope cutoff extra path h0 h1 ne
  | Call path args =>
    simp [mentions?, fren_spec] at ne
    simp only [resolve_layer, callee_item_weakens env scope cutoff extra path h0 h1 ne]
    cases callee_item env scope path <;> simp [shifted_form, shift_form]
  | Match scrutinee arms =>
    simp [mentions?, fren_spec] at ne
    simp only [resolve_layer, resolve_arms_weakens env scope cutoff extra arms h0 h1 ne]
    cases resolve_arms Int env scope arms <;> simp [shifted_form, shift_form]
  | Let name annotation value body =>
    simp only [resolve_layer]
    cases resolve_annotation env name annotation <;> simp [shifted_form, shift_form]
  | _ => simp [resolve_layer, shifted_form, shift_form]

/-! ## Bound items -/

theorem value_form_constructor (env : Env) (scope : Snoc String) (path : Path)
    (item : Fren.Seq String) (h : value_form Int env scope path = some (.Constructor item)) :
    ∃ owner, entry env.symb item = some (.Constructor owner) := by
  simp only [value_form] at h
  split at h
  · simp at h
  · split at h
    · rename_i found _ _ owner eq
      simp at h
      exact ⟨owner, by simpa [h] using eq⟩
    · simp at h
  · simp at h

theorem callee_item_function (env : Env) (scope : Snoc String) (path : Path)
    (item : Fren.Seq String) (h : callee_item env scope path = some item) :
    ∃ sig, entry env.symb item = some (.Function sig) := by
  simp only [callee_item] at h
  split at h
  · split at h
    · rename_i found _ _ sig eq
      simp at h
      exact ⟨sig, by simpa [h] using eq⟩
    · simp at h
  · simp at h

theorem pattern_item_constructor (env : Env) (scope : Snoc String) (path : Path)
    (item : Fren.Seq String) (h : pattern_item env scope path = some item) :
    ∃ owner, entry env.symb item = some (.Constructor owner) := by
  simp only [pattern_item] at h
  split at h
  · split at h
    · rename_i found _ _ owner eq
      simp at h
      exact ⟨owner, by simpa [h] using eq⟩
    · simp at h
  · simp at h

theorem layer_constructor (env : Env) (scope : Snoc String) (form : SrcF Int)
    (item : Fren.Seq String) (h : resolve_layer Int env scope form = some (.Constructor item)) :
    ∃ owner, entry env.symb item = some (.Constructor owner) := by
  cases form with
  | Name path => exact value_form_constructor env scope path item (by simpa [resolve_layer] using h)
  | Call path args => simp only [resolve_layer] at h; split at h <;> simp at h
  | Let name annotation value body => simp only [resolve_layer] at h; split at h <;> simp at h
  | Match scrutinee arms => simp only [resolve_layer] at h; split at h <;> simp at h
  | _ => simp [resolve_layer] at h

theorem layer_callee (env : Env) (scope : Snoc String) (form : SrcF Int)
    (item : Fren.Seq String) (args : Snoc Int)
    (h : resolve_layer Int env scope form = some (.Call item args)) :
    ∃ sig, entry env.symb item = some (.Function sig) := by
  cases form with
  | Name path =>
    simp only [resolve_layer, value_form] at h
    split at h
    · simp at h
    · split at h <;> simp at h
    · simp at h
  | Call path args =>
    simp only [resolve_layer] at h
    split at h
    · rename_i found eq
      simp at h
      exact callee_item_function env scope path item (by simpa [h.1] using eq)
    · simp at h
  | Let name annotation value body => simp only [resolve_layer] at h; split at h <;> simp at h
  | Match scrutinee arms => simp only [resolve_layer] at h; split at h <;> simp at h
  | _ => simp [resolve_layer] at h

end Spec.Language.NamesAndScope

pub mod spec::names

open spec.types spec.names in
impl local_binding_proof: local_binding for (scope : Snoc String) (name : String)
    (level other : Int) {
  scope := scope, name := name, level := level, other := other, holds? := true
} by
  intro scope name level other _
  simp only [local_binding.ensures, local_binding.ensure.output, local_binding.ensure.bound,
    local_binding.ensure.nearest, local_binding.ensure.complete]
  exact ⟨trivial, Spec.Language.NamesAndScope.local_bound scope name level,
    fun h => Spec.Language.NamesAndScope.local_nearest scope name level other h.1 h.2,
    Spec.Language.NamesAndScope.local_complete scope name other⟩

open spec.types spec.names in
impl local_weakening_proof: local_weakening for (scope : Snoc String) (cutoff : Int)
    (extra name : String) {
  scope := scope, cutoff := cutoff, extra := extra, name := name, holds? := true
} by
  intro scope cutoff extra name _
  simp only [local_weakening.ensures, local_weakening.ensure.output, local_weakening.ensure.shifted]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.NamesAndScope.local_weakens scope cutoff extra name h.1.1 h.1.2 h.2

open spec.types spec.names in
impl nearest_index_production: nearest_index for (scope : Snoc String) (name : String) {
  scope := scope, name := name,
  index := (FrenAstToHir.nearest (Spec.Language.NamesAndScope.nearestFirst scope) name).map Int.ofNat
} by
  intro scope name _
  simp only [nearest_index.ensures, nearest_index.ensure.converse]
  rw [Spec.Language.NamesAndScope.nearest_converse]
  cases resolve_local scope name <;> simp [fren_spec]

open spec.names in
impl same_name_production: same_name for (first second : String) {
  first := first, second := second, same? := FrenAstToHir.sameName first second
} by
  intro first second _
  simp [same_name.ensures, same_name.ensure.meaning, FrenAstToHir.sameName]

open spec.types spec.names in
impl parameters_parallel_proof: parameters_parallel for (env : Env) (params : Snoc Param)
    (result : spec.names.TypeName) (sig : Sig) {
  env := env, params := params, result := result, sig := sig, holds? := true
} by
  intro env params result sig _
  simp only [parameters_parallel.ensures, parameters_parallel.ensure.output,
    parameters_parallel.ensure.parallel]
  refine ⟨trivial, ?_⟩
  intro h
  simp only [signature] at h
  split at h
  · rename_i ctx ty hc _
    simp at h
    simp [← h, Spec.Language.NamesAndScope.resolve_params_length env params ctx hc]
  · simp at h

open spec.types spec.names in
impl names_worked_examples_proof: worked_examples { holds? := true } by
  intro _
  simp only [spec.names.worked_examples.ensures, spec.names.worked_examples.ensure.output,
    spec.names.worked_examples.ensure.valid]
  refine ⟨trivial, ?_⟩
  decide

open spec.types spec.names in
impl names_table_scoping_proof: table_scoping for (env : Env) (rows : Snoc SrcRow)
    (forms : Snoc (ExprF Int)) (position : Int) (row : SrcRow) (level : Int) {
  env := env, rows := rows, forms := forms, position := position, row := row, level := level,
  holds? := true
} by
  intro env rows forms position row level _
  simp only [spec.names.table_scoping.ensures, spec.names.table_scoping.ensure.output,
    spec.names.table_scoping.ensure.aligned, spec.names.table_scoping.ensure.in_scope]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    rw [Spec.Language.NamesAndScope.rows_aligned env rows forms h]
  · intro h
    exact Spec.Language.NamesAndScope.rows_scoped env rows forms position row level h.1.1 h.1.2 h.2

open spec.types spec.names in
impl names_rejected_proof: rejected for (parent : Fren.Seq String) (module name variant : String)
    (first second : Snoc String) (ty : spec.names.TypeName) (body : Snoc SrcRow) {
  parent := parent, module := module, name := name, variant := variant, first := first,
  second := second, ty := ty, body := body, holds? := true
} by
  intro parent module name variant first second ty body _
  simp [spec.names.rejected.ensures, spec.names.rejected.ensure.output,
    spec.names.rejected.ensure.duplicate, spec.names.rejected.ensure.repeated_variant,
    spec.names.rejected.ensure.reserved_name, spec.names.rejected.ensure.repeated_parameter,
    spec.names.rejected.ensure.function_as_qualifier, decls_clear?, declares_function?,
    type_clear?, params_clear?, path_head, collect, names_ok?, distinct?, item_names, decl_name,
    resolve_local, decl_names_ok?, decls_names_ok?, param_names, reserved?, fren_spec]

open spec.types spec.names in
impl names_layer_weakening_proof: layer_weakening for (env : Env) (scope : Snoc String)
    (form : SrcF Int) (cutoff : Int) (extra : String) {
  env := env, scope := scope, form := form, cutoff := cutoff, extra := extra, holds? := true
} by
  intro env scope form cutoff extra _
  simp only [spec.names.layer_weakening.ensures, spec.names.layer_weakening.ensure.output,
    spec.names.layer_weakening.ensure.shifted]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.NamesAndScope.layer_weakens env scope form cutoff extra h.1.1 h.1.2
    (Bool.eq_false_iff.mpr h.2)

open spec.types spec.names in
impl bound_items_proof: bound_items for (env : Env) (scope : Snoc String) (form : SrcF Int)
    (path : Path) (args : Snoc Int) (item : Fren.Seq String) {
  env := env, scope := scope, form := form, path := path, args := args, item := item,
  holds? := true
} by
  intro env scope form path args item _
  simp only [bound_items.ensures, bound_items.ensure.output, bound_items.ensure.constructor,
    bound_items.ensure.function, bound_items.ensure.pattern]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨owner, eq⟩ := Spec.Language.NamesAndScope.layer_constructor env scope form item h
    simp [eq, fren_spec]
  · intro h
    obtain ⟨sig, eq⟩ := Spec.Language.NamesAndScope.layer_callee env scope form item args h
    simp [eq, fren_spec]
  · intro h
    obtain ⟨owner, eq⟩ := Spec.Language.NamesAndScope.pattern_item_constructor env scope path item h
    simp [eq, fren_spec]

open spec.types spec.names in
impl siblings_proof: siblings for (rows : Snoc SrcRow) (scope : Snoc String) (name : String)
    (annotation : Option spec.names.TypeName) (op : BinaryOp) (first second : Int) (row : SrcRow) {
  rows := rows, scope := scope, name := name, annotation := annotation, op := op,
  first := first, second := second, row := row, holds? := true
} by
  intro rows scope name annotation op first second row _
  simp only [siblings.ensures, siblings.ensure.output, siblings.ensure.value,
    siblings.ensure.operand]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    have c := h.1
    simp [children_scoped?, has_scope?, h.2, fren_spec] at c
    exact c.1
  · intro h
    have c := h.1
    simp [children_scoped?, has_scope?, h.2, fren_spec] at c
    exact c.2

open spec.types spec.names in
impl collection_well_formed_proof: collection_well_formed for (parent : Fren.Seq String)
    (name : String) (decls : Snoc SrcDecl) (symb : Snoc Entry) {
  parent := parent, name := name, decls := decls, symb := symb, holds? := true
} by
  intro parent name decls symb _
  simp only [collection_well_formed.ensures, collection_well_formed.ensure.output,
    collection_well_formed.ensure.well_formed]
  refine ⟨trivial, ?_⟩
  exact Spec.Language.NamesAndScope.collect_ok parent name decls symb

open spec.types spec.names in
impl collection_order_proof: collection_order for (parent : Fren.Seq String) (name : String)
    (decls : Snoc SrcDecl) (first second : SrcDecl) (left right : Snoc Entry)
    (item : Fren.Seq String) {
  parent := parent, name := name, decls := decls, first := first, second := second,
  left := left, right := right, item := item, holds? := true
} by
  intro parent name decls first second left right item _
  simp only [collection_order.ensures, collection_order.ensure.output,
    collection_order.ensure.accepted, collection_order.ensure.bindings]
  have h := Spec.Language.NamesAndScope.collect_exchange parent name decls first second
  exact ⟨trivial, h.1, fun hc => h.2 left right item hc.1 hc.2⟩

open spec.types spec.names in
impl let_handoff_proof: let_handoff for (env : Env) (name : String) (written : spec.names.TypeName)
    (ty : Ty) (core : Option Ty) {
  env := env, name := name, written := written, ty := ty, core := core, holds? := true
} by
  intro env name written ty core _
  simp only [let_handoff.ensures, let_handoff.ensure.output, let_handoff.ensure.omitted,
    let_handoff.ensure.kept]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    simp [resolve_annotation] at h
    subst h
    simp [let_annotation?]
  · intro h
    simp [resolve_annotation, h]

open spec.types spec.names in
impl collection_permutation_proof: collection_permutation for (parent : Fren.Seq String)
    (name : String) (first second : Snoc SrcDecl) (left right : Snoc Entry)
    (item : Fren.Seq String) {
  parent := parent, name := name, first := first, second := second, left := left,
  right := right, item := item, holds? := true
} by
  intro parent name first second left right item _
  simp only [collection_permutation.ensures, collection_permutation.ensure.output,
    collection_permutation.ensure.accepted, collection_permutation.ensure.bindings,
    same_declarations?, decide_eq_true_eq]
  refine ⟨trivial, fun h => ?_, fun h => ?_⟩
  · exact (Spec.Language.NamesAndScope.collect_same parent name first second h.1.1.1 h.1.1.2).1
      (by simpa [names_ok?] using h.1.2) (by simpa [names_ok?] using h.2)
  · exact (Spec.Language.NamesAndScope.collect_same parent name first second h.1.1.1 h.1.1.2).2
      left right item h.1.2 h.2

pub mod spec::resolution

interp resolved := fun env scope rows => (spec.names.resolve_expression env scope rows).getD default
interp resolves? := fun env scope rows forms =>
    decide (spec.names.resolve_expression env scope rows = some forms) by
  intro env scope rows forms
  simp only [spec.resolution.resolves?.function, spec.resolution.resolves?.aligned,
    spec.resolution.resolved]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp at h; simp [h]
  · simp at h
    cases rows with
    | Empty => simp [spec.names.resolve_expression] at h
    | Extend earlier root =>
      simp only [spec.names.resolve_expression] at h
      split at h
      · exact Spec.Language.NamesAndScope.rows_aligned env _ forms h
      · simp at h

set_option fren.requireEvidence "trusted" in
#fren_trace
