import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.Types
import FrenHirToThir.Coverage

open Fren.Lang

#fren_md "Patterns.md"

#fren_check

namespace Spec.Language.Patterns

open spec.types spec.patterns

/-! ## Selection -/

theorem occurrences_nonneg {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String) :
    0 ≤ occurrences _ arms c := by
  induction arms with
  | Empty => simp [occurrences]
  | Extend earlier last ih =>
    simp only [occurrences]
    split <;> omega

theorem select_sound {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String)
    (found : ArmF E) (h : select _ arms c = some found) :
    found.constructor = c ∧ 0 < occurrences _ arms c := by
  induction arms with
  | Empty => simp [select] at h
  | Extend earlier last ih =>
    simp only [select] at h
    simp only [occurrences]
    cases hs : select _ earlier c with
    | some f =>
      rw [hs] at h
      have := Option.some.inj h; subst this
      have := ih hs
      refine ⟨this.1, ?_⟩
      split <;> omega
    | none =>
      rw [hs] at h
      simp only at h
      split at h
      · rename_i eq; have := Option.some.inj h; subst this
        refine ⟨eq, ?_⟩
        have := occurrences_nonneg earlier c
        simp [eq]; omega
      · simp at h

theorem select_complete {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String)
    (h : 0 < occurrences _ arms c) : ∃ found, select _ arms c = some found := by
  induction arms with
  | Empty => simp [occurrences] at h
  | Extend earlier last ih =>
    simp only [select]
    cases hs : select _ earlier c with
    | some f => exact ⟨f, rfl⟩
    | none =>
      simp only
      have hz : ¬ 0 < occurrences _ earlier c := fun hp => by
        obtain ⟨f, hf⟩ := ih hp; rw [hs] at hf; simp at hf
      simp only [occurrences] at h
      split
      · exact ⟨_, rfl⟩
      · rename_i ne; simp [ne] at h; exact absurd h hz

theorem select_earlier {E : Type} [Inhabited E] (earlier : Snoc (ArmF E)) (last : ArmF E)
    (c : Fren.Seq String) (h : 0 < occurrences _ earlier c) :
    select _ (Snoc.Extend earlier last) c = select _ earlier c := by
  obtain ⟨f, hf⟩ := select_complete earlier c h
  simp [select, hf]

/-! ## Production coverage -/

/-- Oldest first, the order of the source. -/
def toList {α : Type} : Snoc α → List α
  | .Empty => []
  | .Extend earlier last => toList earlier ++ [last]

def ofList {α : Type} (l : List α) : Snoc α := l.foldl .Extend .Empty

theorem toList_foldl {α : Type} (l : List α) (s : Snoc α) :
    toList (l.foldl .Extend s) = toList s ++ l := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp [List.foldl, ih, toList]

theorem toList_ofList {α : Type} (l : List α) : toList (ofList l) = l := by
  simp [ofList, toList_foldl, toList]

theorem occurrences_pos_iff {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String) :
    0 < occurrences _ arms c ↔ c ∈ (toList arms).map (·.constructor) := by
  induction arms with
  | Empty => simp [occurrences, toList]
  | Extend earlier last ih =>
    have := occurrences_nonneg earlier c
    simp only [occurrences, toList, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton, ← ih]
    by_cases h : last.constructor = c
    · simp [h]; omega
    · simp [h]
      intro e; exact absurd e.symm h

theorem uncovered_toList {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    toList (uncovered _ cs arms) =
      (toList cs).filter (fun c => decide (c ∉ (toList arms).map (·.constructor))) := by
  induction cs with
  | Empty => simp [uncovered, toList]
  | Extend earlier last ih =>
    have hp := occurrences_pos_iff arms last
    have hn := occurrences_nonneg arms last
    simp only [uncovered, toList, List.filter_append, ← ih]
    by_cases h : occurrences _ arms last = 0
    · have : ∀ x ∈ toList arms, ¬ x.constructor = last := fun x hx hc => by
        have := hp.2 (List.mem_map.2 ⟨x, hx, hc⟩); omega
      simp [h, toList, List.filter_cons]
      exact this
    · have : ∃ x ∈ toList arms, x.constructor = last := List.mem_map.1 (hp.1 (by omega))
      simp [h, List.filter_cons]
      exact this

theorem production_missing_eq {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    (@FrenHirToThir.coverage (Fren.Seq String) ⟨fun x y => decide (x = y)⟩ (toList cs).toArray
      ((toList arms).map (·.constructor)).toArray).1.toList = toList (uncovered _ cs arms) := by
  rw [uncovered_toList]
  simp [FrenHirToThir.coverage]
  apply List.filter_congr
  intro c _
  by_cases h : c ∈ (toList arms).map (·.constructor) <;> simp_all

theorem repeats_fold {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) :
    ((toList arms).map (·.constructor)).foldl
      (fun (acc : List (Fren.Seq String) × List (Fren.Seq String)) t =>
        (acc.1 ++ [t], if acc.1.contains t then acc.2 ++ [t] else acc.2)) ([], []) =
      ((toList arms).map (·.constructor), toList (repeats _ arms)) := by
  induction arms with
  | Empty => simp [toList, repeats]
  | Extend earlier last ih =>
    have hp := occurrences_pos_iff earlier last.constructor
    have hn := occurrences_nonneg earlier last.constructor
    simp only [toList, List.map_append, List.foldl_append, ih, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, repeats]
    by_cases h : 0 < occurrences _ earlier last.constructor
    · have hm := hp.1 h
      simp [h, hm, toList]
    · have hm : last.constructor ∉ (toList earlier).map (·.constructor) := fun m => h (hp.2 m)
      simp [h, hm]

theorem fold_arrays (ts : List (Fren.Seq String)) (s r : Array (Fren.Seq String)) :
    (ts.foldl (fun (x : Array (Fren.Seq String) × Array (Fren.Seq String)) t =>
        (x.fst.push t, if x.fst.contains t = true then x.snd.push t else x.snd)) (s, r)).2.toList =
    (ts.foldl (fun (acc : List (Fren.Seq String) × List (Fren.Seq String)) t =>
        (acc.1 ++ [t], if acc.1.contains t then acc.2 ++ [t] else acc.2)) (s.toList, r.toList)).2 := by
  induction ts generalizing s r with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have := ih (s.push t) (if s.contains t = true then r.push t else r)
    rw [this]
    by_cases h : s.contains t = true
    · have hm : t ∈ s := by simpa using h
      simp [hm]
    · have hm : t ∉ s := by simpa using h
      simp [hm]

theorem production_repeated_eq {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    (@FrenHirToThir.coverage (Fren.Seq String) ⟨fun x y => decide (x = y)⟩ (toList cs).toArray
      ((toList arms).map (·.constructor)).toArray).2.toList = toList (repeats _ arms) := by
  have := repeats_fold arms
  simp only [FrenHirToThir.coverage]
  rw [← Array.foldl_toList, List.toList_toArray, fold_arrays]
  have h2 := congrArg Prod.snd this
  simpa using h2

theorem ofList_toList {α : Type} (s : Snoc α) : ofList (toList s) = s := by
  induction s with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [ofList] at ih
    simp only [toList, ofList, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]

/-! ## Laws bound to their procedures -/

pub mod spec::patterns

open spec.patterns in
impl selection_laws_proof: selection_laws for (arms earlier : Snoc (ArmF Typing))
    (last found : ArmF Typing) (constructor : Fren.Seq String) {
  arms := arms, earlier := earlier, last := last, constructor := constructor, found := found,
  holds? := true
} by
  intro arms earlier last found constructor _
  simp only [selection_laws.ensures, selection_laws.ensure.output, selection_laws.ensure.sound,
    selection_laws.ensure.complete, selection_laws.ensure.first_wins]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · intro h; exact select_sound arms constructor found h
  · intro h
    obtain ⟨f, hf⟩ := select_complete arms constructor h
    simp [hf]
    rfl
  · intro h; exact select_earlier earlier last constructor h


/-- The production check, read through the adapters: the inventory and the written
patterns go in as arrays and the two lists come back as snoc sequences. -/
def productionCoverage {E : Type} (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    Array (Fren.Seq String) × Array (Fren.Seq String) :=
  @FrenHirToThir.coverage (Fren.Seq String) ⟨fun x y => decide (x = y)⟩ (toList cs).toArray
    ((toList arms).map (·.constructor)).toArray

interp production_missing := fun cs arms => ofList (productionCoverage cs arms).1.toList
interp production_repeated := fun arms => ofList (productionCoverage Snoc.Empty arms).2.toList

open spec.patterns in
impl check_coverage_proof: check_coverage for (constructors : Snoc (Fren.Seq String))
    (arms : Snoc (ArmF Typing)) {
  constructors := constructors, arms := arms, holds? := true
} by
  intro constructors arms _
  simp only [check_coverage.ensures, check_coverage.ensure.output, check_coverage.ensure.missing,
    check_coverage.ensure.repeated, production_missing, production_repeated]
  refine ⟨trivial, ?_, ?_⟩
  · have := production_missing_eq constructors arms
    simp only [productionCoverage, this, ofList_toList]
  · have := production_repeated_eq Snoc.Empty arms
    simp only [productionCoverage, this, ofList_toList]


/-! ## Written order -/

theorem first_index_bound {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String)
    (i : Int) (h : first_index _ arms c = some i) : 0 ≤ i ∧ i < length _ arms := by
  induction arms with
  | Empty => simp [first_index] at h
  | Extend earlier last ih =>
    simp only [first_index] at h
    simp only [length]
    cases hs : first_index _ earlier c with
    | some j => rw [hs] at h; have := Option.some.inj h; subst this; have := ih hs; omega
    | none =>
      rw [hs] at h; simp only at h
      split at h
      · have := Option.some.inj h; subst this; omega
      · simp at h

theorem lookup_some {α : Type} [Inhabited α] (xs : Snoc α) (level : Int) (h0 : 0 ≤ level)
    (h1 : level < length _ xs) : ∃ x, lookup _ xs level = some x := by
  induction xs with
  | Empty => simp [length] at h1; omega
  | Extend earlier last ih =>
    simp only [length] at h1
    simp only [lookup]
    split
    · exact ⟨_, rfl⟩
    · rename_i ne; exact ih (by omega)

theorem select_position_eq {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String) :
    select _ arms c = match first_index _ arms c with
      | some i => lookup _ arms i
      | none => none := by
  induction arms with
  | Empty => simp [select, first_index]
  | Extend earlier last ih =>
    simp only [select, first_index]
    cases hs : first_index _ earlier c with
    | some j =>
      rw [hs] at ih; simp only at ih
      have hb := first_index_bound earlier c j hs
      obtain ⟨x, hx⟩ := lookup_some earlier j hb.1 hb.2
      have hl : lookup _ (Snoc.Extend earlier last) j = some x := by
        simp only [lookup]; rw [if_neg (by omega)]; exact hx
      rw [hx] at ih
      simp only [ih, hl]
    | none =>
      rw [hs] at ih; simp only at ih
      simp only [ih]
      by_cases h : last.constructor = c <;> simp [h, lookup]

/-! ## Unique arms -/

theorem has_arm_occ {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (arm : ArmF E)
    (h : has_arm? _ arms arm = true) : 0 < occurrences _ arms arm.constructor := by
  induction arms with
  | Empty => simp [has_arm?] at h
  | Extend earlier last ih =>
    have := occurrences_nonneg earlier arm.constructor
    simp only [has_arm?, decide_eq_true_eq] at h
    simp only [occurrences]
    rcases h with h | h
    · subst h; simp; omega
    · have := ih (by simpa using h); split <;> omega

theorem arm_unique {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (arm : ArmF E)
    (h : has_arm? _ arms arm = true) (one : occurrences _ arms arm.constructor = 1) :
    select _ arms arm.constructor = some arm := by
  induction arms with
  | Empty => simp [has_arm?] at h
  | Extend earlier last ih =>
    have hn := occurrences_nonneg earlier arm.constructor
    simp only [has_arm?, decide_eq_true_eq] at h
    simp only [occurrences] at one
    rcases h with h | h
    · subst h
      have h0 : occurrences _ earlier last.constructor = 0 := by simp at one; omega
      cases hs : select _ earlier last.constructor with
      | some f => have := select_sound earlier _ f hs; omega
      | none => simp [select, hs]
    · have hpos := has_arm_occ earlier arm (by simpa using h)
      have h1 : occurrences _ earlier arm.constructor = 1 := by
        by_cases e : last.constructor = arm.constructor
        · simp [e] at one; omega
        · simpa [e] using one
      rw [select_earlier earlier last _ hpos]
      exact ih (by simpa using h) h1

/-! ## Coverage and the inventory -/

theorem member_iff (cs : Snoc (Fren.Seq String)) (c : Fren.Seq String) :
    member? cs c = true ↔ c ∈ toList cs := by
  induction cs with
  | Empty => simp [member?, toList]
  | Extend earlier last ih =>
    simp only [member?, toList, List.mem_append, List.mem_singleton, ← ih,
      decide_eq_true_eq]
    constructor <;> rintro (h | h) <;> simp [h]

theorem exact_cover_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    exact_cover? _ cs arms = true ↔ ∀ c ∈ toList cs, occurrences _ arms c = 1 := by
  induction cs with
  | Empty => simp [exact_cover?, toList]
  | Extend earlier last ih =>
    simp only [exact_cover?, toList, decide_eq_true_eq, ih, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩ c (h | h)
      · exact h2 c h
      · subst h; exact h1
    · intro h; exact ⟨h _ (Or.inr rfl), fun c hc => h c (Or.inl hc)⟩

theorem inventory_selected_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String))
    (arms : Snoc (ArmF E)) :
    inventory_selected? _ cs arms = true ↔ ∀ c ∈ toList cs, 0 < occurrences _ arms c := by
  induction cs with
  | Empty => simp [inventory_selected?, toList]
  | Extend earlier last ih =>
    simp only [inventory_selected?, toList, decide_eq_true_eq, ih, List.mem_append,
      List.mem_singleton]
    have key : ∀ c, (match select _ arms c with | some _ => true | _ => false) = true ↔
        0 < occurrences _ arms c := fun c => by
      constructor
      · intro h
        cases hs : select _ arms c with
        | none => simp [hs] at h
        | some f => exact (select_sound arms c f hs).2
      · intro h; obtain ⟨f, hf⟩ := select_complete arms c h; simp [hf]
    constructor
    · rintro ⟨h1, h2⟩ c (h | h)
      · exact h2 c h
      · subst h; exact (key _).1 h1
    · intro h; exact ⟨(key _).2 (h _ (Or.inr rfl)), fun c hc => h c (Or.inl hc)⟩

theorem uncovered_empty_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String))
    (arms : Snoc (ArmF E)) :
    uncovered _ cs arms = Snoc.Empty ↔ ∀ c ∈ toList cs, 0 < occurrences _ arms c := by
  induction cs with
  | Empty => simp [uncovered, toList]
  | Extend earlier last ih =>
    have hn := occurrences_nonneg arms last
    simp only [uncovered, toList, List.mem_append, List.mem_singleton]
    by_cases h : occurrences _ arms last = 0
    · rw [if_pos h]
      constructor
      · intro hh; cases hh
      · intro hh; have := hh last (Or.inr rfl); omega
    · rw [if_neg h, ih]
      constructor
      · intro h2 c hc; rcases hc with hc | hc
        · exact h2 c hc
        · subst hc; omega
      · intro h2 c hc; exact h2 c (Or.inl hc)

theorem repeats_empty_iff {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) :
    repeats _ arms = Snoc.Empty ↔ ∀ c, occurrences _ arms c ≤ 1 := by
  induction arms with
  | Empty => simp [repeats, occurrences]
  | Extend earlier last ih =>
    have hn := occurrences_nonneg earlier last.constructor
    simp only [repeats]
    by_cases h : 0 < occurrences _ earlier last.constructor
    · rw [if_pos h]
      constructor
      · intro hh; cases hh
      · intro hh; have := hh last.constructor
        simp only [occurrences] at this
        split at this <;> first | omega | (exfalso; simp_all)
    · rw [if_neg h, ih]
      constructor
      · intro h2 c
        have := h2 c
        simp only [occurrences]
        split
        · rename_i e; subst e; omega
        · omega
      · intro h2 c
        have := h2 c
        simp only [occurrences] at this
        split at this
        · rename_i e; subst e; omega
        · omega

theorem targets_listed_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String))
    (arms : Snoc (ArmF E)) :
    targets_listed? _ cs arms = true ↔ ∀ a ∈ toList arms, a.constructor ∈ toList cs := by
  induction arms with
  | Empty => simp [targets_listed?, toList]
  | Extend earlier last ih =>
    simp only [targets_listed?, toList, decide_eq_true_eq, member_iff, ih,
      List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩ a (h | h)
      · exact h2 a h
      · subst h; exact h1
    · intro h; exact ⟨h _ (Or.inr rfl), fun a ha => h a (Or.inl ha)⟩

theorem covered_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E))
    (listed : targets_listed? _ cs arms = true) :
    exact_cover? _ cs arms = true ↔
      inventory_selected? _ cs arms = true ∧ repeats _ arms = Snoc.Empty := by
  rw [exact_cover_iff, inventory_selected_iff, repeats_empty_iff]
  rw [targets_listed_iff] at listed
  constructor
  · intro h
    refine ⟨fun c hc => by have := h c hc; omega, fun c => ?_⟩
    by_cases hc : c ∈ toList cs
    · have := h c hc; omega
    · have : ¬ 0 < occurrences _ arms c := fun hp => by
        obtain ⟨a, ha, he⟩ := List.mem_map.1 ((occurrences_pos_iff arms c).1 hp)
        exact hc (he ▸ listed a ha)
      have := occurrences_nonneg arms c
      omega
  · rintro ⟨h1, h2⟩ c hc
    have := h1 c hc; have := h2 c; omega

theorem ctor_member (symbols bindings : Snoc Entry) (hb : bindings_ok? symbols bindings = true)
    (c owner : Fren.Seq String) (h : entry bindings c = some (.Constructor owner)) :
    ∃ cs, entry symbols owner = some (.Enumeration cs) ∧ member? cs c = true := by
  induction bindings with
  | Empty => simp [entry] at h
  | Extend earlier last ih =>
    rcases last with ⟨litem, lkind⟩
    simp only [bindings_ok?, decide_eq_true_eq] at hb
    simp only [entry] at h
    split at h
    · rename_i eq
      have := Option.some.inj h; subst this
      have h2 := hb.1.2
      subst eq
      cases he : entry symbols owner with
      | none => simp [he, fren_spec] at h2
      | some k => cases k <;> simp [he, fren_spec] at h2 ⊢ <;> exact h2
    · exact ih hb.2 h

theorem arm_patterns_iff (symbols : Snoc Entry) (arms : Snoc (ArmF Typing)) (owner : Fren.Seq String) :
    arm_patterns? symbols arms owner = true ↔
      ∀ a ∈ toList arms, entry symbols a.constructor = some (.Constructor owner) := by
  induction arms with
  | Empty => simp [arm_patterns?, toList]
  | Extend earlier last ih =>
    simp only [arm_patterns?, toList, decide_eq_true_eq, ih, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩ a (h | h)
      · exact h2 a h
      · subst h; exact h1
    · intro h; exact ⟨h _ (Or.inr rfl), fun a ha => h a (Or.inl ha)⟩

theorem arm_bodies_iff (arms : Snoc (ArmF Typing)) (ctx : Snoc Ty) (ty : Ty) :
    arm_bodies? arms ctx ty = true ↔ ∀ a ∈ toList arms, a.body.ctx = ctx ∧ a.body.ty = ty := by
  induction arms with
  | Empty => simp [arm_bodies?, toList]
  | Extend earlier last ih =>
    simp only [arm_bodies?, toList, decide_eq_true_eq, ih, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩ a (h | h)
      · exact h2 a h
      · subst h; exact h1
    · intro h; exact ⟨h _ (Or.inr rfl), fun a ha => h a (Or.inl ha)⟩

theorem select_mem {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String)
    (f : ArmF E) (h : select _ arms c = some f) : f ∈ toList arms := by
  induction arms with
  | Empty => simp [select] at h
  | Extend earlier last ih =>
    simp only [select] at h
    simp only [toList, List.mem_append, List.mem_singleton]
    cases hs : select _ earlier c with
    | some g => rw [hs] at h; have := Option.some.inj h; subst this; exact Or.inl (ih hs)
    | none =>
      rw [hs] at h; simp only at h
      split at h
      · have := Option.some.inj h; subst this; exact Or.inr rfl
      · simp at h

theorem listed_of (symbols : Snoc Entry) (hb : symb_ok? symbols = true)
    (arms : Snoc (ArmF Typing)) (owner : Fren.Seq String) (cs : Snoc (Fren.Seq String))
    (hp : arm_patterns? symbols arms owner = true)
    (he : entry symbols owner = some (.Enumeration cs)) : targets_listed? _ cs arms = true := by
  rw [targets_listed_iff]
  intro a ha
  have h1 := (arm_patterns_iff symbols arms owner).1 hp a ha
  obtain ⟨cs', he', hm⟩ := ctor_member symbols symbols (by simpa only [symb_ok?, decide_eq_true_eq] using hb) a.constructor owner h1
  rw [he] at he'
  have := ItemKind.Enumeration.inj (Option.some.inj he')
  subst this
  exact (member_iff _ _).1 hm

/-! ## Impls of the properties -/

theorem covered_unfold {E : Type} [Inhabited E] (symb : Snoc Entry) (owner : Fren.Seq String)
    (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E))
    (h : entry symb owner = some (.Enumeration cs)) :
    covered? _ symb owner arms = exact_cover? _ cs arms := by
  simp only [covered?, h]
  simp

open spec.patterns in
impl select_position_proof: select_position for (arms : Snoc (ArmF Typing))
    (constructor : Fren.Seq String) {
  arms := arms, constructor := constructor, holds? := true
} by
  intro arms constructor _
  simp only [select_position.ensures, select_position.ensure.output, select_position.ensure.first]
  refine ⟨trivial, ?_⟩
  rw [select_position_eq]
  cases hf : first_index _ arms constructor with
  | none => simp
  | some v =>
    simp only
    have e : Fren.Prelude.Option.some.x0 (some v) = v := rfl
    rw [e]
    simp

open spec.patterns in
impl arm_order_proof: arm_order for (arms : Snoc (ArmF Typing)) (arm : ArmF Typing) {
  arms := arms, arm := arm, holds? := true
} by
  intro arms arm _
  simp only [arm_order.ensures, arm_order.ensure.output, arm_order.ensure.unique]
  refine ⟨trivial, ?_⟩
  intro h
  exact arm_unique arms arm h.1 h.2

open spec.patterns in
impl coverage_characterized_proof: coverage_characterized for (symb : Snoc Entry)
    (owner : Fren.Seq String) (constructors : Snoc (Fren.Seq String))
    (arms : Snoc (ArmF Typing)) {
  symb := symb, owner := owner, constructors := constructors, arms := arms, holds? := true
} by
  intro symb owner constructors arms _
  simp only [coverage_characterized.ensures, coverage_characterized.ensure.output,
    coverage_characterized.ensure.listed, coverage_characterized.ensure.characterized,
    coverage_characterized.ensure.agrees]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · intro h; exact listed_of symb h.1.1 arms owner constructors h.1.2 h.2
  · intro h
    rw [covered_unfold symb owner constructors arms h.2]
    exact covered_iff constructors arms h.1
  · intro h
    rw [covered_unfold symb owner constructors arms h.2, covered_iff constructors arms h.1,
      uncovered_empty_iff, inventory_selected_iff]

theorem covered_selects (symb : Snoc Entry) (hb : symb_ok? symb = true) (owner : Fren.Seq String)
    (arms : Snoc (ArmF Typing)) (c : Fren.Seq String)
    (hc : covered? _ symb owner arms = true) (hp : entry symb c = some (.Constructor owner)) :
    ∃ f, select _ arms c = some f := by
  obtain ⟨cs', he', hm⟩ := ctor_member symb symb (by simpa only [symb_ok?, decide_eq_true_eq] using hb)
    c owner hp
  rw [covered_unfold symb owner cs' arms he'] at hc
  have := (exact_cover_iff _ _).1 hc c ((member_iff _ _).1 hm)
  exact select_complete arms c (by omega)

open spec.patterns in
impl exhaustive_selection_proof: exhaustive_selection for (symb : Snoc Entry)
    (owner : Fren.Seq String) (arms : Snoc (ArmF Typing)) (constructor : Fren.Seq String) {
  symb := symb, owner := owner, arms := arms, constructor := constructor, holds? := true
} by
  intro symb owner arms constructor _
  simp only [exhaustive_selection.ensures, exhaustive_selection.ensure.output,
    exhaustive_selection.ensure.selects]
  refine ⟨trivial, ?_⟩
  intro h
  obtain ⟨f, hf⟩ := covered_selects symb h.1.1 owner arms constructor h.1.2
    (by simpa only [pattern_rule?, decide_eq_true_eq] using h.2)
  rw [hf]; rfl

open spec.patterns in
impl selection_typed_proof: selection_typed for (symb : Snoc Entry) (arms : Snoc (ArmF Typing))
    (owner : Fren.Seq String) (constructor : Fren.Seq String) (ctx : Snoc Ty) (ty : Ty)
    (found : ArmF Typing) {
  symb := symb, arms := arms, owner := owner, constructor := constructor, ctx := ctx, ty := ty,
  found := found, holds? := true
} by
  intro symb arms owner constructor ctx ty found _
  simp only [selection_typed.ensures, selection_typed.ensure.output, selection_typed.ensure.body,
    selection_typed.ensure.pattern]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    exact (arm_bodies_iff arms ctx ty).1 h.1 found (select_mem arms constructor found h.2)
  · intro h
    simpa only [pattern_rule?, decide_eq_true_eq] using
      (arm_patterns_iff symb arms owner).1 h.1 found (select_mem arms constructor found h.2)

open spec.patterns in
impl match_progress_proof: match_progress for (symb : Snoc Entry) (ctx : Snoc Ty)
    (scrutinee : Typing) (arms : Snoc (ArmF Typing)) (ty : Ty) (owner : Fren.Seq String)
    (constructor : Fren.Seq String) {
  symb := symb, ctx := ctx, scrutinee := scrutinee, arms := arms, ty := ty, owner := owner,
  constructor := constructor, holds? := true
} by
  intro symb ctx scrutinee arms ty owner constructor _
  simp only [match_progress.ensures, match_progress.ensure.output, match_progress.ensure.selected]
  refine ⟨trivial, ?_⟩
  intro h
  obtain ⟨⟨⟨hb, hm⟩, hs⟩, hp⟩ := h
  have hp' : entry symb constructor = some (.Constructor owner) := by
    simpa only [pattern_rule?, decide_eq_true_eq] using hp
  simp only [match_admitted?, match_rule?, hs, decide_eq_true_eq] at hm
  have hc : covered? _ symb owner arms = true := by
    first | exact hm.2 | simpa [covered?] using hm.2
  obtain ⟨f, hf⟩ := covered_selects symb hb owner arms constructor hc hp'
  have hbod := (arm_bodies_iff arms ctx ty).1 hm.1.1.2 f (select_mem arms constructor f hf)
  have e : Fren.Prelude.Option.some.x0 (some f) = f := rfl
  simp [selected_typed?, hf, e, hbod]

/-! ## Worked examples -/

open spec.patterns in
impl pattern_examples_proof: pattern_examples { holds? := true } by
  intro _
  simp only [pattern_examples.ensures, pattern_examples.ensure.output, pattern_examples.ensure.valid]
  refine ⟨trivial, ?_⟩
  decide

end Spec.Language.Patterns

set_option fren.requireEvidence "trusted" in
#fren_trace
