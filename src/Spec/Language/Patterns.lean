import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.Types

open Fren.Lang

#fren_md "Patterns.md"

#fren_check

namespace Spec.Language.Patterns

open spec.surface spec.names spec.types spec.patterns

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

/-! ## Lists -/

/-- Oldest first, the order of the source. -/
def toList {α : Type} : Snoc α → List α
  | .Empty => []
  | .Extend earlier last => toList earlier ++ [last]

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

theorem first_index_none_iff {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String) :
    first_index _ arms c = none ↔ occurrences _ arms c = 0 := by
  induction arms with
  | Empty => simp [first_index, occurrences]
  | Extend earlier last ih =>
    have hn := occurrences_nonneg earlier c
    simp only [first_index, occurrences]
    cases hs : first_index _ earlier c with
    | some j =>
      rw [hs] at ih
      have : occurrences _ earlier c ≠ 0 := fun h => by simp [h] at ih
      simp only [reduceCtorEq, false_iff]
      split <;> omega
    | none =>
      rw [hs] at ih
      have h0 : occurrences _ earlier c = 0 := ih.1 rfl
      simp only
      by_cases h : last.constructor = c <;> simp [h, h0]

theorem first_index_last {E : Type} [Inhabited E] (earlier : Snoc (ArmF E)) (last : ArmF E) :
    first_index _ (Snoc.Extend earlier last) last.constructor = some (length _ earlier) ↔
      occurrences _ earlier last.constructor = 0 := by
  have hn := occurrences_nonneg earlier last.constructor
  cases hs : first_index _ earlier last.constructor with
  | some j =>
    have hb := first_index_bound earlier last.constructor j hs
    have hne : occurrences _ earlier last.constructor ≠ 0 := fun h => by
      have := (first_index_none_iff earlier last.constructor).2 h
      rw [hs] at this; simp at this
    simp [first_index, hs]
    omega
  | none =>
    have h0 := (first_index_none_iff earlier last.constructor).1 hs
    simp [first_index, hs, h0]

theorem reachable_iff {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) :
    reachable? _ arms = true ↔ repeats _ arms = Snoc.Empty := by
  induction arms with
  | Empty => simp [reachable?, repeats]
  | Extend earlier last ih =>
    have hn := occurrences_nonneg earlier last.constructor
    have hl := first_index_last earlier last
    simp only [reachable?, repeats, decide_eq_true_eq]
    by_cases h : 0 < occurrences _ earlier last.constructor
    · have hne : ¬ occurrences _ earlier last.constructor = 0 := by omega
      simp only [if_pos h]
      constructor
      · rintro ⟨h1, _⟩; exact absurd (hl.1 h1) hne
      · intro hh; cases hh
    · have h0 : occurrences _ earlier last.constructor = 0 := by omega
      simp only [if_neg h]
      constructor
      · rintro ⟨_, h2⟩; exact ih.1 h2
      · intro h2; exact ⟨hl.2 h0, ih.2 h2⟩

theorem select_swap {E : Type} [Inhabited E] (earlier : Snoc (ArmF E)) (a b : ArmF E)
    (c : Fren.Seq String) (h : a.constructor ≠ b.constructor) :
    select _ (Snoc.Extend (Snoc.Extend earlier a) b) c =
      select _ (Snoc.Extend (Snoc.Extend earlier b) a) c := by
  simp only [select]
  cases hs : select _ earlier c with
  | some f => simp
  | none =>
    simp only
    by_cases ha : a.constructor = c <;> by_cases hb : b.constructor = c
    · exact absurd (ha.trans hb.symm) h
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
/-! ## Coverage and the inventory -/

theorem member_iff (cs : Snoc (Fren.Seq String)) (c : Fren.Seq String) :
    member? cs c = true ↔ c ∈ toList cs := by
  induction cs with
  | Empty => simp [member?, toList]
  | Extend earlier last ih =>
    simp only [member?, toList, List.mem_append, List.mem_singleton, ← ih,
      decide_eq_true_eq]
    constructor <;> rintro (h | h) <;> simp [h]

theorem exactly_once_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    exactly_once? _ cs arms = true ↔ ∀ c ∈ toList cs, occurrences _ arms c = 1 := by
  induction cs with
  | Empty => simp [exactly_once?, toList]
  | Extend earlier last ih =>
    simp only [exactly_once?, toList, decide_eq_true_eq, ih, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩ c (h | h)
      · exact h2 c h
      · subst h; exact h1
    · intro h; exact ⟨h _ (Or.inr rfl), fun c hc => h c (Or.inl hc)⟩

theorem each_covered_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    each_covered? _ cs arms = true ↔ ∀ c ∈ toList cs, 0 < occurrences _ arms c := by
  induction cs with
  | Empty => simp [each_covered?, toList]
  | Extend earlier last ih =>
    simp only [each_covered?, toList, decide_eq_true_eq, ih, List.mem_append,
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

theorem once_iff {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E))
    (listed : targets_listed? _ cs arms = true) :
    exactly_once? _ cs arms = true ↔
      each_covered? _ cs arms = true ∧ repeats _ arms = Snoc.Empty := by
  rw [exactly_once_iff, each_covered_iff, repeats_empty_iff]
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
    covered? _ symb owner arms = each_covered? _ cs arms := by
  simp only [covered?, h]
  simp

open spec.patterns in
impl arm_order_proof: arm_order for (earlier : Snoc (ArmF Typing)) (first second : ArmF Typing)
    (constructor : Fren.Seq String) {
  earlier := earlier, first := first, second := second, constructor := constructor,
  holds? := true
} by
  intro earlier first second constructor _
  simp only [arm_order.ensures, arm_order.ensure.output, arm_order.ensure.swap]
  refine ⟨trivial, ?_⟩
  intro h
  exact select_swap earlier first second constructor h

open spec.patterns in
impl reachability_proof: reachability for (arms : Snoc (ArmF Typing)) {
  arms := arms, holds? := true
} by
  intro arms _
  simp only [reachability.ensures, reachability.ensure.output, reachability.ensure.agrees]
  refine ⟨trivial, ?_⟩
  rw [← reachable_iff]
open spec.patterns in
impl coverage_characterized_proof: coverage_characterized for (symb : Snoc Entry)
    (owner : Fren.Seq String) (constructors : Snoc (Fren.Seq String))
    (arms : Snoc (ArmF Typing)) {
  symb := symb, owner := owner, constructors := constructors, arms := arms, holds? := true
} by
  intro symb owner constructors arms _
  simp only [coverage_characterized.ensures, coverage_characterized.ensure.output,
    coverage_characterized.ensure.listed, coverage_characterized.ensure.characterized,
    coverage_characterized.ensure.agrees, coverage_characterized.ensure.once]
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩
  · intro h; exact listed_of symb h.1.1 arms owner constructors h.1.2 h.2
  · intro h
    have h' : entry symb owner = some (.Enumeration constructors) := by
      simpa only [decide_eq_true_eq] using h
    rw [covered_unfold symb owner constructors arms h', each_covered_iff, inventory_selected_iff]
  · intro h
    have h' : entry symb owner = some (.Enumeration constructors) := by
      simpa only [decide_eq_true_eq] using h
    rw [covered_unfold symb owner constructors arms h', each_covered_iff, reachable_iff,
      uncovered_empty_iff]
  · intro h
    rw [covered_unfold symb owner constructors arms h.2, reachable_iff]
    exact (once_iff constructors arms h.1).symm

theorem covered_selects (symb : Snoc Entry) (hb : symb_ok? symb = true) (owner : Fren.Seq String)
    (arms : Snoc (ArmF Typing)) (c : Fren.Seq String)
    (hc : covered? _ symb owner arms = true) (hp : entry symb c = some (.Constructor owner)) :
    ∃ f, select _ arms c = some f := by
  obtain ⟨cs', he', hm⟩ := ctor_member symb symb (by simpa only [symb_ok?, decide_eq_true_eq] using hb)
    c owner hp
  rw [covered_unfold symb owner cs' arms he'] at hc
  exact select_complete arms c ((each_covered_iff _ _).1 hc c ((member_iff _ _).1 hm))

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
    simpa only [decide_eq_true_eq] using
      (arm_patterns_iff symb arms owner).1 h.1 found (select_mem arms constructor found h.2)

open spec.patterns in
impl admitted_selects_typed_proof: admitted_selects_typed for (symb : Snoc Entry) (ctx : Snoc Ty)
    (scrutinee : Typing) (arms : Snoc (ArmF Typing)) (ty : Ty) (owner : Fren.Seq String)
    (constructor : Fren.Seq String) {
  symb := symb, ctx := ctx, scrutinee := scrutinee, arms := arms, ty := ty, owner := owner,
  constructor := constructor, holds? := true
} by
  intro symb ctx scrutinee arms ty owner constructor _
  simp only [admitted_selects_typed.ensures, admitted_selects_typed.ensure.output,
    admitted_selects_typed.ensure.selected]
  refine ⟨trivial, ?_⟩
  intro h
  obtain ⟨⟨⟨hb, hm⟩, hs⟩, hp⟩ := h
  have hp' : entry symb constructor = some (.Constructor owner) := by
    simpa only [decide_eq_true_eq] using hp
  simp only [match_admitted?, match_rule?, hs, decide_eq_true_eq] at hm
  have hc : covered? _ symb owner arms = true := by
    first | exact hm.1.2 | simpa [covered?] using hm.1.2
  obtain ⟨f, hf⟩ := covered_selects symb hb owner arms constructor hc hp'
  have hbod := (arm_bodies_iff arms ctx ty).1 hm.1.1.1.2 f (select_mem arms constructor f hf)
  have e : Fren.Prelude.Option.some.x0 (some f) = f := rfl
  simp [selected_typed?, hf, e, hbod]

open spec.patterns in
impl empty_enumeration_proof: empty_enumeration for (symb : Snoc Entry) (ctx : Snoc Ty)
    (scrutinee : Typing) (arms : Snoc (ArmF Typing)) (ty : Ty) (owner : Fren.Seq String) {
  symb := symb, ctx := ctx, scrutinee := scrutinee, arms := arms, ty := ty, owner := owner,
  holds? := true
} by
  intro symb ctx scrutinee arms ty owner _
  simp only [empty_enumeration.ensures, empty_enumeration.ensure.output,
    empty_enumeration.ensure.unadmitted]
  refine ⟨trivial, ?_⟩
  rintro ⟨⟨hb, he⟩, hs⟩ hadm
  simp only [match_admitted?, match_rule?, hs, decide_eq_true_eq] at hadm
  obtain ⟨⟨⟨⟨⟨_, hne⟩, _⟩, hp⟩, _⟩, _⟩ := hadm
  cases arms with
  | Empty => exact (hne rfl).elim
  | Extend earlier last =>
    have h1 := (arm_patterns_iff symb _ owner).1 hp last (by simp [toList])
    obtain ⟨cs', he', hm⟩ := ctor_member symb symb
      (by simpa only [symb_ok?, decide_eq_true_eq] using hb) last.constructor owner h1
    rw [he] at he'
    have := ItemKind.Enumeration.inj (Option.some.inj he')
    subst this
    simp [member?, fren_spec] at hm

open spec.patterns in
impl table_admission_proof: table_admission for (symb : Snoc Entry) (earlier : Snoc Row) (row : Row)
    (scrutinee : Typing) (arms : Snoc (ArmF Typing)) {
  symb := symb, earlier := earlier, row := row, scrutinee := scrutinee, arms := arms,
  holds? := true
} by
  intro symb earlier row scrutinee arms _
  simp only [table_admission.ensures, table_admission.ensure.output, table_admission.ensure.newest,
    table_admission.ensure.rest]
  refine ⟨trivial, ?_, ?_⟩
  · rintro ⟨h, ha⟩
    simp only [rows_admitted?, decide_eq_true_eq, ha, layer_admitted?] at h
    simpa only [match_admitted?, match_rule?, decide_eq_true_eq] using h.2
  · intro h
    simp only [rows_admitted?, decide_eq_true_eq] at h
    exact h.1

open spec.patterns in
impl program_admission_proof: program_admission for (symb : Snoc Entry) (earlier : Snoc Decl)
    (item : Fren.Seq String) (body : Snoc Row) {
  symb := symb, earlier := earlier, item := item, body := body, holds? := true
} by
  intro symb earlier item body _
  simp only [program_admission.ensures, program_admission.ensure.output,
    program_admission.ensure.typed, program_admission.ensure.bodies]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    simp only [prog_admitted?, decide_eq_true_eq] at h
    simpa only [prog_ok?, decide_eq_true_eq] using h.1
  · intro h
    simp only [prog_admitted?, decls_admitted?, decl_admitted?, decide_eq_true_eq] at h
    exact h.2.1.2

open spec.patterns in
impl nested_examples_proof: nested_examples { holds? := true } by
  intro _
  simp only [nested_examples.ensures, nested_examples.ensure.output, nested_examples.ensure.valid]
  refine ⟨trivial, ?_⟩
  decide

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
