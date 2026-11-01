-- keep-sorted start
import FrenCore.Lint
import Reqs.Lint
-- keep-sorted end
open Fren.Lang

/-! # Pattern tests written out (`Reqs/Lint/Style/PatternTests`)

`manual_pattern_test`, proved of the functions that both front ends call:
how an operand is read from its shape (`readOperand`), and which runs of a
whole run of `or` or `and` are reported (`patternRuns`), for any number of
operands and alternatives. -/

namespace Fren.Impls.PatternTests

open Fren.Core

/-! ## Alternatives -/

/-- A string literal's text, from its value. -/
def quote (s : String) : String := "\"" ++ s ++ "\""

theorem quote_inj (s t : String) : quote s = quote t ↔ s = t := by
  constructor
  · intro h
    have h' := congrArg String.toList h
    simp only [quote, String.toList_append] at h'
    have : s.toList = t.toList := by simpa using h'
    exact String.ext this
  · rintro rfl; rfl

theorem isPrefixOf_single (c : Char) (l : List Char) : [c].isPrefixOf l = (l.head? == some c) := by
  cases l with
  | nil => rfl
  | cons h t =>
    simp only [List.isPrefixOf, List.head?_cons]
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq]
    simp [eq_comm (a := c)]

/-- A text has a character exactly where it has it in its list. -/
theorem contains_char (s : String) (c : Char) : Fren.Str.contains s (String.singleton c) = decide (c ∈ s.toList) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Fren.Str.contains, List.any_eq_true, List.mem_range, String.toList_singleton, isPrefixOf_single,
    beq_iff_eq, List.head?_drop]
  constructor
  · rintro ⟨i, _, h⟩; exact List.mem_of_getElem? h
  · intro h
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
    exact ⟨i, by have : s.toList.length = s.length := String.length_toList; omega, by simp [hi, e]⟩

theorem contains_quote (s : String) : Fren.Str.contains (quote s) "\\" = Fren.Str.contains s "\\" := by
  have h1 := contains_char (quote s) '\\'
  have h2 := contains_char s '\\'
  simp only [show String.singleton '\\' = "\\" from rfl] at h1 h2
  rw [h1, h2]
  simp [quote]

/-- A string literal's value, from its text. -/
def unquote (s : String) : String := String.ofList (s.toList.drop 1).dropLast

theorem unquote_quote (t : String) : unquote (quote t) = t := by
  simp [unquote, quote, String.toList_append]

/-- An alternative of the model as `manual_pattern_test` reads one, with a
string literal by its text. -/
def toPatAlt : lint.Alt → Fren.Core.PatAlt
  | .Integers lo hi => .ints lo hi
  | .Text s => .str (quote s)
  | .Variant c => .variant c

/-- The model's alternative that the lint reads as `a`. -/
def fromPatAlt : Fren.Core.PatAlt → lint.Alt
  | .ints lo hi => .Integers lo hi
  | .str s => .Text (unquote s)
  | .variant c => .Variant c

theorem from_to (a : lint.Alt) : fromPatAlt (toPatAlt a) = a := by
  cases a <;> simp [toPatAlt, fromPatAlt, unquote_quote]

theorem below_eq (h l : Option Int) : Fren.Core.boundBelow h l = lint.bound_below? h l := by
  cases h <;> cases l <;> simp [Fren.Core.boundBelow, lint.bound_below?, fren_spec]

theorem disjoint_eq (a b : lint.Alt) : (toPatAlt a).disjoint (toPatAlt b) = lint.alts_disjoint? a b := by
  rw [Bool.eq_iff_iff]
  cases a <;> cases b <;> simp only [toPatAlt, Fren.Core.PatAlt.disjoint, below_eq, contains_quote] <;>
    simp [lint.alts_disjoint?, fren_spec, quote_inj]

/-! ## Reading the operands -/

def toForm : lint.Literal → ValueForm
  | .Decimal k => .decimal k
  | .Quoted t => .quoted (quote t)
  | .Variant c => .variant c
  | .Truth b => .truth b
  | .Other => .other

theorem alt_eq (v : lint.Literal) (nat : Bool) : (toForm v).alt? nat = (lint.value_alt v nat).map toPatAlt := by
  cases v <;> simp only [toForm, ValueForm.alt?, lint.value_alt] <;> try rfl
  split <;> split <;> simp_all [toPatAlt]

/-- A side of a comparison of the model, as the lint reads one, with its
written form for its expression. -/
def toSide (s : lint.Side) : ComparisonSide String := { node := s.text, text := s.text, value := toForm s.value }

/-- An operand of the model, as the lint reads its shape, with its
expression's written form for the expression and no text for its
alternatives. -/
def toShape : lint.Shape → OperandShape String
  | .Comparison c => .comparison c.«equal?» c.«nat?» (toSide c.left) (toSide c.right)
  | .Test t => .test t.«negated?» t.scrutinee (t.alts.map fun q => q.toList.map fun a => (toPatAlt a, ""))
  | .Other => .other

/-- What the lint's decisions read of a reading: the expression, the
alternatives and whether it is an equation. -/
def view (p : PatternOperand String) : String × List PatAlt × Bool := (p.scrutinee, p.alts.map (·.1), p.equation)

/-- The same of a reading of the model. -/
def rview (r : lint.Reading) : String × List PatAlt × Bool := (r.scrutinee, r.alts.toList.map toPatAlt, r.«equation?»)

theorem read_eq (s : lint.Shape) (conj : Bool) :
    (readOperand conj (toShape s)).map view = (lint.reading s conj).map rview := by
  cases s with
  | Comparison c =>
    by_cases h : c.«equal?» = conj
    · simp [toShape, readOperand, lint.reading, h]
    · have h' : (c.«equal?» == conj) = false := by simpa using h
      simp only [toShape, readOperand, toSide, alt_eq, lint.reading, lint.comparison_reading, h',
        Bool.false_eq_true, ite_false]
      cases lint.value_alt c.left.value c.«nat?» <;> cases lint.value_alt c.right.value c.«nat?» <;>
        simp [view, rview, h]
  | Test t =>
    simp only [toShape, readOperand, lint.reading]
    by_cases h : t.«negated?» = conj
    · cases ha : t.alts <;> simp [h, view, rview, lint.test_reading, ha, Function.comp_def]
    · simp [h]
  | Other => simp [toShape, readOperand, lint.reading]

-- Both front ends read an operand with `patternOperand?`, which decides
-- with `readOperand` on the shape that `operandShape` reads.
impl read_operand: lint::read_operand for (s : lint.Shape) (conj : Bool) {
  shape := s,
  «conj?» := conj,
  «reads?» := (readOperand conj (toShape s)).isSome,
  «equation?» := ((readOperand conj (toShape s)).map (·.equation)).getD false,
  scrutinee := ((readOperand conj (toShape s)).map (·.scrutinee)).getD "",
  alts := Fren.Seq.ofList (((readOperand conj (toShape s)).map fun p => p.alts.map (fromPatAlt ·.1)).getD []),
} by
  intro s conj _
  have h := read_eq s conj
  unfold lint.read_operand.defs lint.read_operand.def.scrutinee lint.read_operand.def.alts
    lint.read_operand.ensures lint.read_operand.ensure.rule lint.read_operand.ensure.equation
  cases e : readOperand conj (toShape s) with
  | none =>
    cases e' : lint.reading s conj with
    | none => simp [fren_spec]; rfl
    | some r => rw [e, e'] at h; simp at h
  | some p =>
    cases e' : lint.reading s conj with
    | none => rw [e, e'] at h; simp at h
    | some r =>
      rw [e, e'] at h
      simp only [Option.map_some, Option.some.injEq, view, rview, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have ha : p.alts.map (fromPatAlt ·.1) = r.alts.toList := by
        have := congrArg (List.map fromPatAlt) h2
        simpa [List.map_map, Function.comp_def, from_to] using this
      simp [fren_spec, h1, h3, ha]

/-! ## Runs -/

/-- `L` has a longest run of operands that test the expression written `f`
from position `i` to position `j`. -/
def MaxRun (L : List (Option String)) (i j : Nat) : Prop :=
  ∃ f, i ≤ j ∧ (∀ p, i ≤ p → p ≤ j → L[p]? = some (some f))
    ∧ (i = 0 ∨ L[i - 1]? ≠ some (some f)) ∧ L[j + 1]? ≠ some (some f)

theorem runLength_spec (f : String) (rs : List (Option String)) :
    (∀ p, p < runLength f rs → rs[p]? = some (some f)) ∧ rs[runLength f rs]? ≠ some (some f) := by
  induction rs with
  | nil => simp [runLength]
  | cons r rs ih =>
    cases r with
    | none => simp [runLength]
    | some g =>
      simp only [runLength]
      split
      · rename_i h
        have hg : g = f := by simpa using h
        subst hg
        refine ⟨fun p hp => ?_, by simpa using ih.2⟩
        cases p with
        | zero => simp
        | succ p => simpa using ih.1 p (by omega)
      · rename_i h
        refine ⟨fun p hp => absurd hp (by omega), ?_⟩
        simp only [List.getElem?_cons_zero, ne_eq, Option.some.injEq]
        intro e; exact h (by simp [e])

theorem get_of_drop {L : List (Option String)} {m : Nat} {x rest} (e : L.drop m = x :: rest) (p : Nat) :
    L[m + p]? = (x :: rest)[p]? := by
  rw [← e, List.getElem?_drop]

theorem mem_runSpans (L : List (Option String)) (m : Nat)
    (hm : m = 0 ∨ ∀ f, L[m]? = some (some f) → L[m - 1]? ≠ some (some f)) (i j : Nat) :
    (i, j) ∈ runSpans m (L.drop m) ↔ m ≤ i ∧ MaxRun L i j := by
  match e : L.drop m with
  | [] =>
    simp only [runSpans, List.not_mem_nil, false_iff, not_and]
    intro hi ⟨f, hij, hall, _⟩
    have h1 := hall i (Nat.le_refl _) hij
    have : L.length ≤ m := by simpa using e
    rw [List.getElem?_eq_none (by omega)] at h1
    simp at h1
  | none :: rest =>
    have hL : L[m]? = some none := by simpa using get_of_drop e 0
    have hr : rest = L.drop (m + 1) := by
      rw [← List.drop_drop, e]; simp
    simp only [runSpans]
    rw [hr, mem_runSpans L (m + 1) (Or.inr fun f h => by simp [hL]) i j]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, ⟨f, hij, hall, hl, hr⟩⟩
      refine ⟨?_, ⟨f, hij, hall, hl, hr⟩⟩
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · omega
      · subst h; have := hall m (Nat.le_refl _) hij; simp [hL] at this
  | some f :: rest =>
    have hL : L[m]? = some (some f) := by simpa using get_of_drop e 0
    have hr : rest = L.drop (m + 1) := by
      rw [← List.drop_drop, e]; simp
    obtain ⟨hk, hstop⟩ := runLength_spec f rest
    generalize hkdef : runLength f rest = k at hk hstop
    have hrun : ∀ p, m ≤ p → p ≤ m + k → L[p]? = some (some f) := by
      intro p h1 h2
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · have := get_of_drop e (p - m)
        rw [show m + (p - m) = p by omega] at this
        rw [this]
        have := hk (p - m - 1) (by omega)
        rw [show p - m = (p - m - 1) + 1 by omega]
        simpa using this
      · subst h; exact hL
    have hend : L[m + k + 1]? ≠ some (some f) := by
      have := get_of_drop e (k + 1)
      rw [show m + (k + 1) = m + k + 1 by omega] at this
      rw [this]; simpa using hstop
    have hdrop : rest.drop k = L.drop (m + k + 1) := by
      rw [hr, List.drop_drop]; congr 1; omega
    simp only [runSpans, hkdef, List.mem_cons, Prod.mk.injEq]
    rw [hdrop, mem_runSpans L (m + k + 1) (Or.inr fun g hg => by
      rw [show m + k + 1 - 1 = m + k by omega, hrun (m + k) (by omega) (Nat.le_refl _)]
      intro hfg; simp at hfg; subst hfg; exact hend hg) i j]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨h1, h2⟩)
      · refine ⟨Nat.le_refl _, f, by omega, hrun, ?_, hend⟩
        rcases hm with h | h
        · exact Or.inl h
        · exact Or.inr (h f hL)
      · exact ⟨by omega, h2⟩
    · rintro ⟨h1, ⟨g, hij, hall, hl, hr'⟩⟩
      by_cases hi : i ≤ m + k
      · left
        have hg : g = f := by
          have := hall i (Nat.le_refl _) hij
          rw [hrun i h1 hi] at this; simpa using this.symm
        subst hg
        have him : i = m := by
          rcases Nat.lt_or_eq_of_le h1 with h | h
          · exfalso
            rcases hl with hl | hl
            · omega
            · exact hl (hrun (i - 1) (by omega) (by omega))
          · exact h.symm
        subst him
        refine ⟨rfl, ?_⟩
        by_cases hj : j < i + k
        · exact absurd (hrun (j + 1) (by omega) (by omega)) hr'
        · by_cases hj2 : j ≤ i + k
          · omega
          · exact absurd (hall (i + k + 1) (by omega) (by omega)) hend
      · right; exact ⟨by omega, ⟨g, hij, hall, hl, hr'⟩⟩
termination_by L.length - m
decreasing_by
  all_goals
    first
    | (have : L.length > m := by
        have := congrArg List.length e; simp at this; omega
       omega)

theorem mem_runsOf (vs : List (Option (String × List PatAlt × Bool))) (chain : Bool) (i j : Nat) :
    (i, j) ∈ runsOf vs chain ↔ MaxRun (vs.map (·.map (·.1))) i j ∧
      manualPatternTest (((vs.extract i (j + 1)).filterMap id).flatMap (·.2.1)) ((vs.extract i (j + 1)).filterMap id).length
        ((((vs.extract i (j + 1)).filterMap id).filter (·.2.2)).length) chain = true := by
  simp only [runsOf, List.mem_filter]
  have := mem_runSpans (vs.map (·.map (·.1))) 0 (Or.inl rfl) i j
  simp only [List.drop_zero, Nat.zero_le, true_and] at this
  rw [this]

theorem filterMap_some_of {β : Type} : ∀ (l : List (Option β)), (∀ x ∈ l, x ≠ none) → (l.filterMap id).map some = l
  | [], _ => rfl
  | none :: _, h => absurd rfl (h none (by simp))
  | some b :: l, h => by
    have ih := filterMap_some_of l (fun x hx => h x (by simp [hx]))
    simpa using ih

theorem pairwiseDisjoint_iff' (l : List PatAlt) :
    pairwiseDisjoint l = true ↔ l.Pairwise (fun a b => a.disjoint b = true) := by
  induction l with
  | nil => simp [pairwiseDisjoint]
  | cons a as ih => simp [pairwiseDisjoint, ih, List.pairwise_cons, List.all_eq_true]

/-- The alternatives of a run are disjoint two by two, in order, as
positions within each operand's alternatives. -/
theorem pairwise_flatMap_iff (w : List (String × List PatAlt × Bool)) :
    (w.flatMap (·.2.1)).Pairwise (fun a b => a.disjoint b = true) ↔
      ∀ p q k l (hp : p < w.length) (hq : q < w.length) (hk : k < w[p].2.1.length) (hl : l < w[q].2.1.length),
        p ≤ q → (p < q ∨ k < l) → w[p].2.1[k].disjoint w[q].2.1[l] = true := by
  rw [List.pairwise_flatMap, List.pairwise_iff_getElem]
  constructor
  · rintro ⟨hin, hx⟩ p q k l hp hq hk hl hpq hor
    rcases Nat.lt_or_eq_of_le hpq with h | h
    · exact hx p q hp hq h _ (List.getElem_mem hk) _ (List.getElem_mem hl)
    · subst h
      have hkl : k < l := by omega
      exact (List.pairwise_iff_getElem.mp (hin _ (List.getElem_mem hp))) k l hk hl hkl
  · intro h
    refine ⟨fun a ha => ?_, fun p q hp hq hpq x hx y hy => ?_⟩
    · obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem ha
      exact List.pairwise_iff_getElem.mpr fun k l hk hl hkl => h p p k l hp hp hk hl (Nat.le_refl _) (Or.inr hkl)
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hy
      exact h p q k l hp hq hk hl (Nat.le_of_lt hpq) (Or.inl hpq)

theorem fires_iff (w : List (String × List PatAlt × Bool)) (chain : Bool) :
    manualPatternTest (w.flatMap (·.2.1)) w.length (w.filter (·.2.2)).length chain = true ↔
      2 ≤ w.length ∧ (∃ q, ∃ hq : q < w.length, w[q].2.2 = true) ∧ chain = false ∧
      ∀ p q k l (hp : p < w.length) (hq : q < w.length) (hk : k < w[p].2.1.length) (hl : l < w[q].2.1.length),
        p ≤ q → (p < q ∨ k < l) → w[p].2.1[k].disjoint w[q].2.1[l] = true := by
  rw [← pairwise_flatMap_iff, ← pairwiseDisjoint_iff']
  simp only [manualPatternTest, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  have : 1 ≤ (w.filter (·.2.2)).length ↔ ∃ q, ∃ hq : q < w.length, w[q].2.2 = true := by
    constructor
    · intro h
      obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (by omega : 0 < (w.filter (·.2.2)).length)
      rw [List.mem_filter] at ha
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem ha.1
      exact ⟨q, hq, ha.2⟩
    · rintro ⟨q, hq, he⟩
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨List.getElem_mem hq, he⟩)
  rw [ge_iff_le, ge_iff_le, this]
  constructor
  · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩; exact ⟨a, b, c, d⟩
  · rintro ⟨a, b, c, d⟩; exact ⟨⟨⟨a, b⟩, c⟩, d⟩

/-! ### The model's runs -/

/-- What the model's operands test, as written. -/
def forms (l : List lint.Shape) (c : Bool) : List (Option String) := l.map fun x => (lint.reading x c).map (·.scrutinee)

section
variable (l : List lint.Shape) (c : Bool)


theorem reading_at_eq (i : Int) :
    lint.reading_at (Fren.Seq.ofList l) c i = if 0 ≤ i then l[i.toNat]?.bind (lint.reading · c) else none := by
  unfold lint.reading_at
  by_cases h : 0 ≤ i ∧ i < l.length
  · rw [if_pos (by simpa using h), if_pos h.1, Fren.Seq.nth_of_lt _ _ h.1 (by simpa using h.2),
      List.getElem?_eq_getElem (by omega)]
    simp
  · rw [if_neg (by simpa using h)]
    by_cases h0 : 0 ≤ i
    · rw [if_pos h0, List.getElem?_eq_none (by omega)]; simp
    · rw [if_neg h0]

theorem tests_iff (i : Int) (x : String) :
    lint.tests_at? (Fren.Seq.ofList l) c i x = true ↔ 0 ≤ i ∧ (forms l c)[i.toNat]? = some (some x) := by
  unfold lint.tests_at?
  rw [reading_at_eq]
  have hf : (forms l c)[i.toNat]? = l[i.toNat]?.map (fun y => (lint.reading y c).map (·.scrutinee)) := by
    simp [forms]
  rw [hf]
  by_cases h0 : 0 ≤ i
  · rw [if_pos h0]
    cases l[i.toNat]? with
    | none => simp [fren_spec, h0]
    | some y =>
      simp only [Option.bind_some, Option.map_some]
      generalize lint.reading y c = o
      cases o <;> simp [fren_spec, h0]
  · rw [if_neg h0]; simp [fren_spec, h0]

theorem longest_iff (s : lint.Span) :
    lint.longest_run? (Fren.Seq.ofList l) c s = true ↔
      0 ≤ s.first ∧ s.first ≤ s.last ∧ MaxRun (forms l c) s.first.toNat s.last.toNat := by
  have T := tests_iff l c
  simp only [decide_eq_true_eq] at T
  unfold lint.longest_run?
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨⟨hfl, hall⟩, hl⟩, hr⟩
    have h0 := ((T _ _).mp (hall s.first ⟨Int.le_refl _, hfl⟩)).1
    refine ⟨h0, hfl, x, by omega, fun p h1 h2 => ?_, ?_, ?_⟩
    · have := ((T _ _).mp (hall p ⟨by omega, by omega⟩)).2
      simpa using this
    · by_cases hz : s.first = 0
      · exact Or.inl (by omega)
      · refine Or.inr fun e => hl ((T _ _).mpr ⟨by omega, ?_⟩)
        rw [show (s.first - 1).toNat = s.first.toNat - 1 by omega]; exact e
    · intro e
      exact hr ((T _ _).mpr ⟨by omega, by rw [show (s.last + 1).toNat = s.last.toNat + 1 by omega]; exact e⟩)
  · rintro ⟨h0, hfl, x, _, hall, hl, hr⟩
    refine ⟨x, ⟨⟨hfl, fun p hp => (T _ _).mpr ⟨by omega, ?_⟩⟩, ?_⟩, ?_⟩
    · exact hall p.toNat (by omega) (by omega)
    · intro e
      obtain ⟨h1, e⟩ := (T _ _).mp e
      rcases hl with hl | hl
      · omega
      · exact hl (by rw [show s.first.toNat - 1 = (s.first - 1).toNat by omega]; exact e)
    · intro e
      obtain ⟨_, e⟩ := (T _ _).mp e
      exact hr (by rw [show s.last.toNat + 1 = (s.last + 1).toNat by omega]; exact e)

theorem alts_at_of (p : Nat) (x : lint.Shape) (r : lint.Reading) (hx : l[p]? = some x) (hr : lint.reading x c = some r) :
    lint.alts_at (Fren.Seq.ofList l) c p = r.alts := by
  unfold lint.alts_at
  rw [reading_at_eq, if_pos (by omega)]
  simp [hx, hr]

theorem equation_at_of (p : Nat) (x : lint.Shape) (r : lint.Reading) (hx : l[p]? = some x) (hr : lint.reading x c = some r) :
    lint.equation_at? (Fren.Seq.ofList l) c p = r.«equation?» := by
  unfold lint.equation_at?
  rw [reading_at_eq, if_pos (by omega)]
  simp [hx, hr]

end

/-- `decide`, with whatever instance a generated definition gives it. -/
theorem decide_true_iff {p : Prop} {inst : Decidable p} : @decide p inst = true ↔ p := @decide_eq_true_iff p inst

/-- The model's operands as the lint's decisions read them. -/
def views (l : List lint.Shape) (c : Bool) : List (Option (String × List PatAlt × Bool)) :=
  l.map fun x => (lint.reading x c).map rview

theorem views_forms (l : List lint.Shape) (c : Bool) : (views l c).map (·.map (·.1)) = forms l c := by
  simp [views, forms, rview, Function.comp_def]

/-- The operands of a longest run, as the lint's decisions read them,
each the reading of the model's operand at its position. -/
theorem run_readings (l : List lint.Shape) (c : Bool) (i j : Nat) (hm : MaxRun (forms l c) i j) :
    let w := ((views l c).extract i (j + 1)).filterMap id
    w.length = j + 1 - i ∧
      ∀ q (hq : q < w.length), ∃ x r, l[i + q]? = some x ∧ lint.reading x c = some r ∧ w[q] = rview r := by
  intro w
  obtain ⟨f, hij, hall, _, _⟩ := hm
  have hread : ∀ p, i ≤ p → p ≤ j → ∃ x r, l[p]? = some x ∧ lint.reading x c = some r := by
    intro p h1 h2
    have := hall p h1 h2
    simp only [forms, List.getElem?_map] at this
    cases hx : l[p]? with
    | none => simp [hx] at this
    | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at this
      cases hr : lint.reading x c with
      | none => simp [hr] at this
      | some r => exact ⟨x, r, rfl, hr⟩
  have hjl : j < l.length := by
    obtain ⟨x, _, hx, _⟩ := hread j hij (Nat.le_refl _)
    rcases Nat.lt_or_ge j l.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; simp at hx
  have hsub : ∀ q, q < j + 1 - i → ((views l c).extract i (j + 1))[q]? = (views l c)[i + q]? := by
    intro q hq
    rw [List.extract_eq_take_drop, List.getElem?_take_of_lt hq, List.getElem?_drop]
  have hsublen : ((views l c).extract i (j + 1)).length = j + 1 - i := by
    simp [List.extract_eq_take_drop, views]; omega
  have hsome : ∀ y ∈ (views l c).extract i (j + 1), y ≠ none := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
    have e := hsub q (by omega)
    rw [List.getElem?_eq_getElem hq] at e
    obtain ⟨x, r, hx, hr⟩ := hread (i + q) (by omega) (by omega)
    have hv : (views l c)[i + q]? = some (some (rview r)) := by simp [views, hx, hr]
    rw [hv, Option.some.injEq] at e
    rw [e]; simp
  have hmap := filterMap_some_of _ hsome
  have hwlen : w.length = j + 1 - i := by
    rw [← hsublen, ← hmap, List.length_map]
  refine ⟨hwlen, fun q hq => ?_⟩
  obtain ⟨x, r, hx, hr⟩ := hread (i + q) (by omega) (by omega)
  refine ⟨x, r, hx, hr, ?_⟩
  have e := hsub q (by omega)
  have hv : (views l c)[i + q]? = some (some (rview r)) := by simp [views, hx, hr]
  rw [← hmap, List.getElem?_map, List.getElem?_eq_getElem hq, hv] at e
  simpa using e

theorem fires_spec (l : List lint.Shape) (c : Bool) (cs : List lint.Shape) (s : lint.Span) (h0 : 0 ≤ s.first)
    (hfl : s.first ≤ s.last) (hm : MaxRun (forms l c) s.first.toNat s.last.toNat) :
    let w := ((views l c).extract s.first.toNat (s.last.toNat + 1)).filterMap id
    lint.run_fires? (Fren.Seq.ofList l) c (Fren.Seq.ofList cs) s = true ↔
      manualPatternTest (w.flatMap (·.2.1)) w.length (w.filter (·.2.2)).length
        (lint.membership_chain? (Fren.Seq.ofList cs) c) = true := by
  intro w
  obtain ⟨hwlen, hw⟩ := run_readings l c _ _ hm
  have hwlen' : w.length = s.last.toNat + 1 - s.first.toNat := hwlen
  replace hw : ∀ q (hq : q < w.length), ∃ x r, l[s.first.toNat + q]? = some x ∧ lint.reading x c = some r ∧
      w[q] = rview r := hw
  rw [fires_iff]
  unfold lint.run_fires?
  rw [decide_true_iff]
  -- Each position of the run, as an integer, is one of `w`'s.
  have hpos : ∀ p : Int, s.first ≤ p → p ≤ s.last → ∃ q, ∃ hq : q < w.length, p = ((s.first.toNat + q : Nat) : Int) :=
    fun p h1 h2 => ⟨(p - s.first).toNat, by omega, by omega⟩
  constructor
  · rintro ⟨⟨⟨hlt, hch⟩, ⟨p, ⟨h1, h2⟩, he⟩⟩, hdis⟩
    refine ⟨by omega, ?_, by simpa using hch, ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hpos p h1 h2
      obtain ⟨x, r, hx, hr, hwq⟩ := hw q hq
      rw [equation_at_of l c _ x r hx hr] at he
      exact ⟨q, hq, by rw [hwq]; exact he⟩
    · intro p q k k' hp hq hk hk' hpq hor
      obtain ⟨x, r, hx, hr, hwp⟩ := hw p hp
      obtain ⟨y, t, hy, ht, hwq⟩ := hw q hq
      have hk2 : k < r.alts.toList.length := by
        have := hk; simp only [hwp, rview, List.length_map] at this; exact this
      have hk2' : k' < t.alts.toList.length := by
        have := hk'; simp only [hwq, rview, List.length_map] at this; exact this
      have := hdis ((s.first.toNat + p : Nat) : Int) ((s.first.toNat + q : Nat) : Int) k k'
        ⟨⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by
          rw [alts_at_of l c _ x r hx hr]; simp; omega⟩, by rw [alts_at_of l c _ y t hy ht]; simp; omega⟩, by omega⟩
      rw [alts_at_of l c _ x r hx hr, alts_at_of l c _ y t hy ht, Fren.Seq.nth_of_lt _ _ (by omega) (by omega),
        Fren.Seq.nth_of_lt _ _ (by omega) (by omega), ← disjoint_eq] at this
      simp only [hwp, hwq, rview, List.getElem_map]
      simpa using this
  · rintro ⟨hlen, ⟨q, hq, he⟩, hch, hdis⟩
    refine ⟨⟨⟨by omega, by simp [hch]⟩, ?_⟩, ?_⟩
    · obtain ⟨x, r, hx, hr, hwq⟩ := hw q hq
      refine ⟨((s.first.toNat + q : Nat) : Int), ⟨by omega, by omega⟩, ?_⟩
      rw [equation_at_of l c _ x r hx hr]
      rw [hwq] at he; exact he
    · intro p p' k k' ⟨⟨⟨⟨⟨h1, _⟩, ⟨h2, h3⟩⟩, hk0, hk⟩, hk0', hk'⟩, hor⟩
      obtain ⟨q, hq, rfl⟩ := hpos p h1 (by omega)
      obtain ⟨q', hq', rfl⟩ := hpos p' (by omega) h3
      obtain ⟨x, r, hx, hr, hwp⟩ := hw q hq
      obtain ⟨y, t, hy, ht, hwq⟩ := hw q' hq'
      rw [alts_at_of l c _ x r hx hr] at hk ⊢
      rw [alts_at_of l c _ y t hy ht] at hk' ⊢
      simp only [Fren.Seq.len_eq] at hk hk'
      rw [Fren.Seq.nth_of_lt _ _ hk0 hk, Fren.Seq.nth_of_lt _ _ hk0' hk', ← disjoint_eq]
      have := hdis q q' k.toNat k'.toNat hq hq' (by simp [hwp, rview]; omega) (by simp [hwq, rview]; omega)
        (by omega) (by omega)
      simp only [hwp, hwq, rview, List.getElem_map] at this
      exact this

/-- The lint's reading of the membership chain is the model's. -/
theorem chainLeft_eq (c : Bool) (x : lint.Shape) :
    membershipChainShapes.chainLeft? id c (toShape x) =
      match x with
      | .Comparison k => if k.«equal?» != c then some k.left.text else none
      | _ => none := by
  cases x <;> simp [toShape, membershipChainShapes.chainLeft?, toSide]

theorem unwritten_eq (x : lint.Shape) : membershipChainShapes.unwrittenRight (toShape x) = lint.unwritten? x := by
  cases x with
  | Comparison k =>
    simp only [toShape, membershipChainShapes.unwrittenRight, toSide, lint.unwritten?]
    cases h : k.right.value <;> simp [toForm, fren_spec, h]
  | _ => simp [toShape, membershipChainShapes.unwrittenRight, lint.unwritten?]

theorem forall_nth {α : Type} [Inhabited α] (l : List α) (P : α → Prop) :
    (∀ i : Int, 0 ≤ i ∧ i < (Fren.Seq.ofList l).len → P ((Fren.Seq.ofList l).nth i)) ↔ ∀ x ∈ l, P x := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := h i ⟨by omega, by simp; omega⟩
    rwa [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)] at this
  · intro h i ⟨h0, h1⟩
    rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)]
    exact h _ (List.getElem_mem _)

theorem exists_nth {α : Type} [Inhabited α] (l : List α) (P : α → Prop) :
    (∃ i : Int, (0 ≤ i ∧ i < (Fren.Seq.ofList l).len) ∧ P ((Fren.Seq.ofList l).nth i)) ↔ ∃ x ∈ l, P x := by
  constructor
  · rintro ⟨i, ⟨h0, h1⟩, h⟩
    rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)] at h
    exact ⟨_, List.getElem_mem _, h⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨i, ⟨by omega, by simp; omega⟩, by rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)]; exact h⟩

/-- An operand of the chain has the chain's left operand, as the lint reads
it, exactly where the model's reads both. -/
theorem chain_left_iff (c : Bool) (x s0 : lint.Shape) :
    ((membershipChainShapes.chainLeft? id c (toShape x)).isSome = true ∧
        membershipChainShapes.chainLeft? id c (toShape x) = membershipChainShapes.chainLeft? id c (toShape s0)) ↔
      (lint.chain_equation? x c (lint.left_text s0) = true ∧ lint.chain_equation? s0 c (lint.left_text s0) = true) := by
  rw [chainLeft_eq, chainLeft_eq]
  cases x <;> cases s0 <;> simp [lint.chain_equation?, lint.left_text, fren_spec] <;> split <;> simp_all <;> exact and_comm

theorem chain_shapes_cons (c : Bool) (s0 : lint.Shape) (rest : List lint.Shape) :
    membershipChainShapes id c ((s0 :: rest).map toShape) = true ↔
      rest.length + 1 ≥ 3 ∧
        (∀ x ∈ s0 :: rest, (membershipChainShapes.chainLeft? id c (toShape x)).isSome = true ∧
          membershipChainShapes.chainLeft? id c (toShape x) = membershipChainShapes.chainLeft? id c (toShape s0)) ∧
        ∃ x ∈ s0 :: rest, membershipChainShapes.unwrittenRight (toShape x) = true := by
  simp [membershipChainShapes, List.all_eq_true, List.any_eq_true, and_assoc]

/-- The lint's reading of the membership chain is the model's. -/
theorem chain_eq (cs : List lint.Shape) (c : Bool) :
    membershipChainShapes id c (cs.map toShape) = lint.membership_chain? (Fren.Seq.ofList cs) c := by
  rw [Bool.eq_iff_iff]
  unfold lint.membership_chain?
  rw [decide_true_iff]
  cases cs with
  | nil => simp [membershipChainShapes]
  | cons s0 rest =>
    have h0 : (Fren.Seq.ofList (s0 :: rest)).nth 0 = s0 := by
      rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp)]; rfl
    have hlen : (Fren.Seq.ofList (s0 :: rest)).len = ((rest.length + 1 : Nat) : Int) := by simp
    rw [h0, forall_nth (s0 :: rest) (fun x => lint.chain_equation? x c (lint.left_text s0) = true),
      exists_nth (s0 :: rest) (fun x => lint.unwritten? x = true), chain_shapes_cons, hlen]
    have hu := unwritten_eq
    constructor
    · rintro ⟨hl, hall, x, hx, hw⟩
      rw [hu] at hw
      exact ⟨⟨by omega, fun y hy => ((chain_left_iff c y s0).mp (hall y hy)).1⟩, x, hx, hw⟩
    · rintro ⟨⟨hl, hall⟩, x, hx, hw⟩
      have h00 := hall s0 List.mem_cons_self
      refine ⟨by omega, fun y hy => (chain_left_iff c y s0).mpr ⟨hall y hy, h00⟩, x, hx, ?_⟩
      rw [hu]; exact hw

-- Both front ends report the runs that `patternRuns` gives, of the operands
-- that `patternOperand?` reads, in a chain that `membershipChainOf` reads
-- from the shapes of its operands, for every list of operands.
impl manual_pattern_test_runs: lint::manual_pattern_test_runs
    for (l cs : List lint.Shape) (c : Bool) (s : lint.Span) {
  operands := Fren.Seq.ofList l,
  chain := Fren.Seq.ofList cs,
  «conj?» := c,
  run := s,
  «reported?» := decide (0 ≤ s.first ∧ s.first ≤ s.last ∧
    (s.first.toNat, s.last.toNat) ∈ patternRuns id (l.map (readOperand c ∘ toShape))
      (membershipChainShapes id c (cs.map toShape))),
} by
  intro l cs c s _
  unfold lint.manual_pattern_test_runs.ensures lint.manual_pattern_test_runs.ensure.rule
  have hps : (l.map (readOperand c ∘ toShape)).map (·.map fun p => (id p.scrutinee, p.alts.map (·.1), p.equation)) =
      views l c := by
    simp only [views, List.map_map]
    congr 1; funext x
    exact read_eq x c
  rw [decide_eq_true_iff, patternRuns, hps, mem_runsOf, views_forms, longest_iff, chain_eq]
  constructor
  · rintro ⟨h0, hfl, hm, hf⟩
    exact ⟨⟨h0, hfl, hm⟩, (fires_spec l c cs s h0 hfl hm).mpr hf⟩
  · rintro ⟨⟨h0, hfl, hm⟩, hf⟩
    exact ⟨h0, hfl, hm, (fires_spec l c cs s h0 hfl hm).mp hf⟩

/-! ## The fix -/

/-- An operand holds exactly where one of its alternatives in the fix
matches. -/
theorem fix_alternatives_holds (t : lint.RunTest) (w : lang.Value) :
    (∃ k : Int, (0 ≤ k ∧ k < (lint.fix_alternatives t).len) ∧
      lang.matches_value? ((lint.fix_alternatives t).nth k) w = true) ↔ lint.test_holds? t w = true := by
  cases t with
  | Equals v =>
    simp only [lint.fix_alternatives, lint.test_holds?]
    constructor
    · rintro ⟨k, ⟨h0, h1⟩, hm⟩
      have hk : k = 0 := by simp at h1; omega
      subst hk; simpa [lang.matches_value?, fren_spec] using hm
    · intro h
      exact ⟨0, ⟨Int.le_refl _, by simp⟩, by simpa [lang.matches_value?, fren_spec] using h⟩
  | Is alts => simp [lint.fix_alternatives, lint.test_holds?, fren_spec]

/-- The fix holds exactly where the run does. -/
theorem fix_run_iff (tests : Fren.Seq lint.RunTest) (w : lang.Value) :
    (∃ i k : Int, ((0 ≤ i ∧ i < tests.len) ∧ 0 ≤ k ∧ k < (lint.fix_alternatives (tests.nth i)).len) ∧
      lang.matches_value? ((lint.fix_alternatives (tests.nth i)).nth k) w = true) ↔
      ∃ i : Int, (0 ≤ i ∧ i < tests.len) ∧ lint.test_holds? (tests.nth i) w = true := by
  constructor
  · rintro ⟨i, k, ⟨hi, hk⟩, hm⟩
    exact ⟨i, hi, (fix_alternatives_holds _ w).mp ⟨k, hk, hm⟩⟩
  · rintro ⟨i, hi, ht⟩
    obtain ⟨k, hk, hm⟩ := (fix_alternatives_holds _ w).mpr ht
    exact ⟨i, k, ⟨hi, hk⟩, hm⟩

-- Proved of the spec's own functions, for any number of tests and
-- alternatives.
impl manual_pattern_test_fix: lint::manual_pattern_test_fix for (tests : Fren.Seq lint.RunTest) (w : lang.Value) {
  tests := tests,
  w := w,
} by
  intro tests w _
  unfold lint.manual_pattern_test_fix.ensures lint.manual_pattern_test_fix.ensure.same_meaning
    lint.manual_pattern_test_fix.ensure.dual
  unfold lint.fix_holds? lint.run_holds?
  rw [decide_true_iff, decide_true_iff]
  have key := fix_run_iff tests w
  refine ⟨key, ?_⟩
  rw [key]
  simp only [not_exists, not_and]

/-! ## The fix of a run -/

/-- An equation's reading matches the value it writes. -/
theorem value_matches (v : lint.Literal) (nat : Bool) (a : lint.Alt) (h : lint.value_alt v nat = some a) :
    ∃ x, lint.literal_value v = some x ∧ lang.matches_value? (lint.alt_pattern a) x = true := by
  cases v with
  | Decimal k =>
    simp only [lint.value_alt] at h
    split at h
    · simp at h
    · cases h; exact ⟨.Integer k, rfl, by simp [lang.matches_value?, fren_spec]⟩
  | Quoted t =>
    simp only [lint.value_alt, Option.some.injEq] at h
    subst h
    refine ⟨.Text t, rfl, ?_⟩
    simp only [lint.alt_pattern]
    split <;> simp [lang.matches_value?, fren_spec]
  | Variant k =>
    simp only [lint.value_alt, Option.some.injEq] at h
    subst h
    exact ⟨.Constructed k .Nil, rfl, by simp [lang.matches_value?, fren_spec]⟩
  | Truth b => simp [lint.value_alt] at h
  | Other => simp [lint.value_alt] at h

/-- Disjoint alternatives' patterns match no value in common
(`lint::disjoint_alternatives::apart`), for every value. -/
theorem apart (a b : lint.Alt) (v : lang.Value) (h : lint.alts_disjoint? a b = true) :
    ¬(lang.matches_value? (lint.alt_pattern a) v = true ∧ lang.matches_value? (lint.alt_pattern b) v = true) := by
  cases a with
  | Integers l1 h1 =>
    cases b with
    | Integers l2 h2 =>
      cases l1 <;> cases h1 <;> cases l2 <;> cases h2 <;> cases v <;>
        simp_all [lint.alts_disjoint?, lint.bound_below?, lang.matches_value?, fren_spec] <;> omega
    | _ => simp [lint.alts_disjoint?] at h
  | Text s =>
    cases b with
    | Text t =>
      simp [lint.alts_disjoint?, fren_spec] at h
      simp only [lint.alt_pattern]
      split <;> split <;> cases v <;> simp_all [lang.matches_value?, fren_spec]
    | _ => simp [lint.alts_disjoint?] at h
  | Variant c =>
    cases b with
    | Variant d =>
      cases v <;> simp_all [lint.alts_disjoint?, lang.matches_value?, fren_spec]
      intro h1 h2; exact h (h1.trans h2.symm)
    | _ => simp [lint.alts_disjoint?] at h

/-- Each alternative of an operand's test in the fix matches no value that
the reading's pattern of the alternative at its position does not. -/
theorem cover (x : lint.Shape) (c : Bool) (r : lint.Reading) (hr : lint.reading x c = some r)
    (pats : Fren.Seq (lang.Pattern String)) (w : lang.Value)
    (hread : ∀ t, x = .Test t → pats.len = r.alts.len ∧ ∀ k : Int, (0 ≤ k ∧ k < pats.len) ∧
      lang.matches_value? (pats.nth k) w = true → lang.matches_value? (lint.alt_pattern (r.alts.nth k)) w = true) :
    (lint.fix_alternatives (lint.run_test x pats)).len = r.alts.len ∧
      ∀ k : Int, 0 ≤ k → k < r.alts.len → lang.matches_value? ((lint.fix_alternatives (lint.run_test x pats)).nth k) w = true →
        lang.matches_value? (lint.alt_pattern (r.alts.nth k)) w = true := by
  cases x with
  | Comparison k =>
    simp only [lint.reading] at hr
    split at hr
    · rename_i hc
      simp only [lint.comparison_reading] at hr
      simp only [lint.run_test, lint.equation_value]
      cases hl : lint.value_alt k.left.value k.«nat?» <;> cases hrt : lint.value_alt k.right.value k.«nat?» <;>
        simp only [hl, hrt] at hr <;> try simp at hr
      · obtain ⟨v, hv, hm⟩ := value_matches _ _ _ hrt
        cases hr
        simp only [hv]
        refine ⟨by simp [lint.fix_alternatives], fun k h0 h1 hk => ?_⟩
        have : k = 0 := by simp at h1; omega
        subst this
        simp [lint.fix_alternatives, lang.matches_value?, fren_spec] at hk
        subst hk; simpa using hm
      · obtain ⟨v, hv, hm⟩ := value_matches _ _ _ hl
        cases hr
        simp only [hv]
        refine ⟨by simp [lint.fix_alternatives], fun k h0 h1 hk => ?_⟩
        have : k = 0 := by simp at h1; omega
        subst this
        simp [lint.fix_alternatives, lang.matches_value?, fren_spec] at hk
        subst hk; simpa using hm
    · simp at hr
  | Test t =>
    obtain ⟨hlen, himp⟩ := hread t rfl
    simp only [lint.fix_alternatives]
    exact ⟨hlen, fun k h0 h1 hk => himp k ⟨⟨h0, by omega⟩, hk⟩⟩
  | Other => simp [lint.reading] at hr

/-- A read operand of the run, and its reading. -/
theorem read_at (l : List lint.Shape) (c : Bool) (p : Int) (h : lint.reading_at (Fren.Seq.ofList l) c p ≠ none) :
    ∃ y r, 0 ≤ p ∧ (Fren.Seq.ofList l).nth p = y ∧ lint.reading y c = some r ∧
      lint.alts_at (Fren.Seq.ofList l) c p = r.alts := by
  rw [reading_at_eq] at h
  by_cases h0 : 0 ≤ p
  · rw [if_pos h0] at h
    cases hy : l[p.toNat]? with
    | none => simp [hy] at h
    | some y =>
    cases hr : lint.reading y c with
    | none => simp [hy, hr] at h
    | some r =>
      have hlt : p.toNat < l.length := by
        rcases Nat.lt_or_ge p.toNat l.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hy; simp at hy
      refine ⟨y, r, h0, ?_, hr, ?_⟩
      · rw [Fren.Seq.nth_of_lt _ _ h0 (by simp; omega)]
        simp only [Fren.Seq.toList_ofList]
        have := List.getElem?_eq_getElem hlt
        rw [hy] at this
        exact (Option.some.inj this).symm
      · have := alts_at_of l c p.toNat y r hy hr
        rwa [show ((p.toNat : Nat) : Int) = p by omega] at this
  · rw [if_neg h0] at h; exact absurd rfl h

-- Proved of the spec's own functions, for any number of operands and
-- alternatives.
impl manual_pattern_test_refines: lint::manual_pattern_test_refines
    for (l cs : List lint.Shape) (c : Bool) (s : lint.Span) (ps : Fren.Seq (Fren.Seq (lang.Pattern String)))
      (ts : Fren.Seq lint.RunTest) (w : lang.Value) {
  operands := Fren.Seq.ofList l,
  chain := Fren.Seq.ofList cs,
  «conj?» := c,
  run := s,
  patterns := ps,
  tests := ts,
  w := w,
} by
  intro l cs c s ps ts w hyp
  unfold lint.manual_pattern_test_refines.ensures lint.manual_pattern_test_refines.ensure.covered
    lint.manual_pattern_test_refines.ensure.same_meaning lint.manual_pattern_test_refines.ensure.reachable
  unfold lint.manual_pattern_test_refines.assumes lint.manual_pattern_test_refines.assume.read
    lint.manual_pattern_test_refines.assume.operands_tests at hyp
  obtain ⟨hread, hlen, hts⟩ := hyp
  -- Where the run's operands are read: what the fix and the readings give
  -- at a position of the run.
  have at_ : (∀ i : Int, s.first ≤ i ∧ i ≤ s.last → lint.reading_at (Fren.Seq.ofList l) c i ≠ none) →
      ∀ q : Int, 0 ≤ q → q < ts.len → ∃ r : lint.Reading, lint.alts_at (Fren.Seq.ofList l) c (s.first + q) = r.alts ∧
      (lint.fix_alternatives (ts.nth q)).len = r.alts.len ∧
      ∀ m : Int, 0 ≤ m → m < r.alts.len → lang.matches_value? ((lint.fix_alternatives (ts.nth q)).nth m) w = true →
        lang.matches_value? (lint.alt_pattern (r.alts.nth m)) w = true := by
    intro hall q hq0 hq
    obtain ⟨y, r, _, hy, hr, ha⟩ := read_at l c (s.first + q) (by simpa using hall _ ⟨by omega, by omega⟩)
    refine ⟨r, ha, ?_⟩
    rw [hts q ⟨hq0, hq⟩, hy]
    refine cover y c r hr _ w fun t ht => ?_
    have := hread (s.first + q) ⟨⟨by omega, by omega⟩, by rw [hy, ht]; rfl⟩
    rw [ha] at this
    exact ⟨this.1, fun m hm => this.2 m hm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hall q ⟨hq0, hq⟩
    obtain ⟨r, har, hlr, himp⟩ := at_ hall q hq0 hq
    rw [har]
    exact ⟨hlr, fun m ⟨⟨hm0, _⟩, hm⟩ => himp m hm0 (by omega) hm⟩
  · unfold lint.fix_holds? lint.run_holds?
    rw [decide_true_iff, decide_true_iff]
    exact fix_run_iff ts w
  · unfold lint.run_fires?
    rintro ⟨hall, hfire⟩ i j k k' ⟨⟨⟨⟨⟨h0, _⟩, ⟨hij, hj⟩⟩, hk0, hk⟩, hk0', hk'⟩, hor⟩ ⟨hm, hm'⟩
    rw [decide_true_iff] at hfire
    obtain ⟨_, hdis⟩ := hfire
    obtain ⟨r, har, hlr, himp⟩ := at_ hall i h0 (by omega)
    obtain ⟨r', har', hlr', himp'⟩ := at_ hall j (by omega) hj
    have hd := hdis (s.first + i) (s.first + j) k k'
      ⟨⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨hk0, by rw [har]; omega⟩⟩, ⟨hk0', by rw [har']; omega⟩⟩,
        by omega⟩
    rw [har, har'] at hd
    exact apart _ _ w hd ⟨himp k hk0 (by omega) hm, himp' k' hk0' (by omega) hm'⟩

impl manual_pattern_test_reads: lint::manual_pattern_test_reads for (v : lint.Literal) (nat : Bool) {
  v := v,
  «nat?» := nat,
} by
  intro v nat _
  unfold lint.manual_pattern_test_reads.ensures lint.manual_pattern_test_reads.ensure.value_matches
  rintro ⟨h1, _⟩
  obtain ⟨x, hx, hm⟩ := value_matches v nat _ h1
  rw [hx]
  exact hm

impl manual_pattern_test_fix_alts: lint::manual_pattern_test_fix_alts for (l : List lint.Shape) (c : Bool) (s : lint.Span)
    (q : Int) {
  operands := Fren.Seq.ofList l,
  «conj?» := c,
  run := s,
  q := q,
  n_operands := ((runAlternatives (l.map (readOperand c ∘ toShape)) s.first.toNat s.last.toNat).length : Int),
  alts := Fren.Seq.ofList ((((runAlternatives (l.map (readOperand c ∘ toShape)) s.first.toNat s.last.toNat)[q.toNat]?).getD
    []).map (fromPatAlt ·.1)),
} by
  intro l c s q hyp
  unfold lint.manual_pattern_test_fix_alts.defs lint.manual_pattern_test_fix_alts.def.n_operands
    lint.manual_pattern_test_fix_alts.def.alts
  unfold lint.manual_pattern_test_fix_alts.assumes lint.manual_pattern_test_fix_alts.assume.read
    lint.manual_pattern_test_fix_alts.assume.position at hyp
  obtain ⟨⟨⟨h0, hfl⟩, hall⟩, hq0, hq⟩ := hyp
  generalize hL : l.map (readOperand c ∘ toShape) = L
  have hop : ∀ p : Nat, s.first.toNat ≤ p → p ≤ s.last.toNat → ∃ (op : PatternOperand String) (r : lint.Reading),
      L[p]? = some (some op) ∧
      lint.alts_at (Fren.Seq.ofList l) c p = r.alts ∧ op.alts.map (fromPatAlt ·.1) = r.alts.toList := by
    intro p h1 h2
    obtain ⟨y, r, _, hy, hr, ha⟩ := read_at l c p (by simpa using hall p ⟨by omega, by omega⟩)
    have hlt : p < l.length := by
      rcases Nat.lt_or_ge p l.length with hn | hn
      · exact hn
      · have hnone := hall p ⟨by omega, by omega⟩
        rw [reading_at_eq, if_pos (by omega), show (p : Int).toNat = p by omega, List.getElem?_eq_none hn] at hnone
        exact absurd rfl hnone
    have hly : l[p]? = some y := by
      rw [List.getElem?_eq_getElem hlt]
      rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)] at hy
      simpa using hy
    have h := read_eq y c
    rw [hr] at h
    cases e : readOperand c (toShape y) with
    | none => rw [e] at h; simp at h
    | some op =>
      rw [e] at h
      simp only [Option.map_some, Option.some.injEq, view, rview, Prod.mk.injEq] at h
      refine ⟨op, r, by simp [← hL, hly, e], by simpa using ha, ?_⟩
      have := congrArg (List.map fromPatAlt) h.2.1
      simpa [List.map_map, Function.comp_def, from_to] using this
  have hjl : s.last.toNat < L.length := by
    obtain ⟨op, _, h, _⟩ := hop s.last.toNat (by omega) (Nat.le_refl _)
    rcases Nat.lt_or_ge s.last.toNat L.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; simp at h
  -- The run's operands are all read, so none is dropped.
  have hsome : ∀ y ∈ L.extract s.first.toNat (s.last.toNat + 1), y ≠ none := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
    have hlen : (L.extract s.first.toNat (s.last.toNat + 1)).length = s.last.toNat + 1 - s.first.toNat := by
      simp [List.extract_eq_take_drop]; omega
    obtain ⟨op, _, h, _⟩ := hop (s.first.toNat + m) (by omega) (by omega)
    have e : (L.extract s.first.toNat (s.last.toNat + 1))[m]? = L[s.first.toNat + m]? := by
      rw [List.extract_eq_take_drop, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    rw [List.getElem?_eq_getElem hm, h] at e
    rw [Option.some.inj e]; simp
  have hmap := filterMap_some_of _ hsome
  have hlenx : (L.extract s.first.toNat (s.last.toNat + 1)).length = s.last.toNat + 1 - s.first.toNat := by
    simp [List.extract_eq_take_drop]; omega
  have hlenf : ((L.extract s.first.toNat (s.last.toNat + 1)).filterMap id).length = s.last.toNat + 1 - s.first.toNat := by
    have := congrArg List.length hmap
    rw [List.length_map] at this
    rw [this, hlenx]
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · simp only [runAlternatives, List.length_map]
    rw [hlenf]; omega
  · obtain ⟨op, r, h, ha, hr⟩ := hop (s.first.toNat + q.toNat) (by omega) (by omega)
    have e : ((L.extract s.first.toNat (s.last.toNat + 1)).filterMap id)[q.toNat]? = some op := by
      have e1 : (L.extract s.first.toNat (s.last.toNat + 1))[q.toNat]? = some (some op) := by
        rw [List.extract_eq_take_drop, List.getElem?_take_of_lt (by omega), List.getElem?_drop, h]
      rw [← hmap, List.getElem?_map] at e1
      cases e2 : ((L.extract s.first.toNat (s.last.toNat + 1)).filterMap id)[q.toNat]? with
      | none => rw [e2] at e1; simp at e1
      | some o => rw [e2] at e1; simp at e1; rw [e1]
    have hq' : ((s.first.toNat + q.toNat : Nat) : Int) = s.first + q := by omega
    rw [hq'] at ha
    simp only [runAlternatives, List.getElem?_map, e, Option.map_some, Option.getD_some]
    rw [hr, ha]; rfl

end Fren.Impls.PatternTests
