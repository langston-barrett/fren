-- keep-sorted start
import Fren.Impl
import FrenCore.Literate
import Reqs.Markdown
-- keep-sorted end
open Fren.Lang

/-! # Markdown specs (`Reqs/Markdown#code-blocks`)

The reader that both front ends, `fren fmt` and the tests read blocks with,
`Fren.Core.splitLine` and `Fren.Core.step`, bound to the requirements that
state it over a line's text. -/

namespace Fren.Impls

theorem md_at_past (s : String) (i : Int) (h : (s.length : Int) ≤ i) : Fren.Str.at s i = "" := by
  simp only [Fren.Str.at, Fren.Str.slice]
  rw [if_neg (by omega)]

theorem md_charRun_all (p : String → Bool) (s : String) :
    ∀ (n i : Nat), s.length - i = n → ∀ k : Nat, i ≤ k → k < i + Fren.Core.charRun p s i →
      p (Fren.Str.at s k) = true := by
  intro n
  induction n with
  | zero =>
    intro i hi k h1 h2
    rw [Fren.Core.charRun] at h2
    split at h2
    · rename_i hc; omega
    · omega
  | succ n ih =>
    intro i hi k h1 h2
    rw [Fren.Core.charRun] at h2
    split at h2
    · rename_i hc
      by_cases hk : k = i
      · subst hk; exact hc.2
      · exact ih (i + 1) (by omega) k (by omega) (by omega)
    · omega

theorem md_charRun_end (p : String → Bool) (s : String) (hp : p "" = false) :
    ∀ (n i : Nat), s.length - i = n → p (Fren.Str.at s ((i + Fren.Core.charRun p s i : Nat) : Int)) = false := by
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [Fren.Core.charRun]
    split
    · rename_i hc; omega
    · rw [md_at_past s _ (by omega)]; simpa using hp
  | succ n ih =>
    intro i hi
    rw [Fren.Core.charRun]
    split
    · have := ih (i + 1) (by omega)
      rw [show i + (Fren.Core.charRun p s (i + 1) + 1) = i + 1 + Fren.Core.charRun p s (i + 1) by omega]
      exact this
    · rename_i hc
      by_cases hl : i < s.length
      · simp only [Nat.add_zero]
        have : ¬ p (Fren.Str.at s i) = true := fun h => hc ⟨hl, h⟩
        simpa using this
      · simp only [Nat.add_zero]; rw [md_at_past s _ (by omega)]; simpa using hp

theorem md_charRun_all_int (p : String → Bool) (s : String) (i : Nat) (k : Int)
    (h1 : (i : Int) ≤ k) (h2 : k < (i : Int) + (Fren.Core.charRun p s i : Int)) : p (Fren.Str.at s k) = true := by
  have := md_charRun_all p s _ i rfl k.toNat (by omega) (by omega)
  rwa [show ((k.toNat : Nat) : Int) = k by omega] at this

theorem md_charRun_end' (p : String → Bool) (s : String) (hp : p "" = false) (i : Nat) :
    p (Fren.Str.at s ((i : Int) + (Fren.Core.charRun p s i : Int))) = false := by
  have := md_charRun_end p s hp _ i rfl
  simpa using this

theorem md_split_fields (line : String) :
    let P := Fren.Core.splitLine line
    P.indent = Fren.Core.charRun (· == " ") line 0 ∧
    P.marker = (if Fren.Str.at line P.indent = "`" ∨ Fren.Str.at line P.indent = "~" then Fren.Str.at line P.indent else "") ∧
    P.run = (if P.marker = "" then 0 else Fren.Core.charRun (· == P.marker) line P.indent) ∧
    P.lead = Fren.Core.charRun Fren.Core.isBlank line (P.indent + P.run) ∧
    P.info = Fren.Str.slice line ((P.indent : Int) + P.run + P.lead) ((line.length : Int) - P.indent - P.run - P.lead) ∧
    P.fence = (decide (P.indent ≤ 3) && decide (3 ≤ P.run) && (P.marker == "~" || !Fren.Str.contains P.info "`")) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

open Fren.Str in
theorem md_split_facts (line : String) :
    let P := Fren.Core.splitLine line
    ((P.marker = if Str.at line ↑P.indent = Str.lit "`" ∨ Str.at line ↑P.indent = Str.lit "~" then
          Str.at line ↑P.indent else Str.lit "") ∧
      P.info = Str.slice line (↑P.indent + ↑P.run + ↑P.lead) (Str.len line - ↑P.indent - ↑P.run - ↑P.lead)) ∧
    (∀ (k : Int), 0 ≤ k ∧ k < ↑P.indent → Str.at line k = Str.lit " ") ∧
    Str.at line ↑P.indent ≠ Str.lit " " ∧
    (∀ (k : Int), ↑P.indent ≤ k ∧ k < ↑P.indent + ↑P.run → Str.at line k = P.marker) ∧
    (P.marker = Str.lit "" ∨ Str.at line (↑P.indent + ↑P.run) ≠ P.marker) ∧
    (P.marker = Str.lit "" → (P.run : Int) = 0) ∧
    (∀ (k : Int), ↑P.indent + ↑P.run ≤ k ∧ k < ↑P.indent + ↑P.run + ↑P.lead →
      decide (Str.at line k = Str.lit " " ∨ Str.at line k = Str.lit "\t") = true) ∧
    ¬decide (Str.at line (↑P.indent + ↑P.run + ↑P.lead) = Str.lit " " ∨
      Str.at line (↑P.indent + ↑P.run + ↑P.lead) = Str.lit "\t") = true ∧
    (P.fence = true ↔ (↑P.indent ≤ (3 : Int) ∧ (3 : Int) ≤ ↑P.run) ∧
      (P.marker = Str.lit "~" ∨ ¬Str.contains P.info (Str.lit "`") = true)) := by
  dsimp only
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := md_split_fields line
  generalize Fren.Core.splitLine line = P at *
  simp only [Fren.Str.lit, Fren.Str.len]
  refine ⟨⟨h2, h5⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k ⟨k0, k1⟩
    have := md_charRun_all_int (· == " ") line 0 k (by omega) (by rw [← h1]; omega)
    simpa using this
  · have := md_charRun_end' (· == " ") line rfl 0
    rw [← h1] at this
    simpa using this
  · intro k ⟨k0, k1⟩
    by_cases hm : P.marker = ""
    · rw [if_pos hm] at h3; omega
    · rw [if_neg hm] at h3
      have := md_charRun_all_int (· == P.marker) line P.indent k k0 (by rw [← h3]; omega)
      simpa using this
  · by_cases hm : P.marker = ""
    · exact Or.inl hm
    · right
      rw [if_neg hm] at h3
      have := md_charRun_end' (· == P.marker) line (by simpa using Ne.symm hm) P.indent
      rw [← h3] at this
      simpa using this
  · intro hm; rw [if_pos hm] at h3; simp [h3]
  · intro k ⟨k0, k1⟩
    have := md_charRun_all_int Fren.Core.isBlank line (P.indent + P.run) k (by push_cast; omega)
      (by rw [← h4]; push_cast; omega)
    simpa [Fren.Core.isBlank] using this
  · have := md_charRun_end' Fren.Core.isBlank line rfl (P.indent + P.run)
    rw [← h4] at this
    push_cast at this
    simpa [Fren.Core.isBlank] using this
  · rw [h6]; simp; intro _; omega

/-- The specification's kind of block for the reader's. -/
def ofBlockKind : Fren.Core.BlockKind → markdown.BlockKind
  | .spec => .Spec
  | .exampleBlock => .Example
  | .looksLikeFren => .LooksLikeFren
  | .prose => .Prose

open Fren.Str in
theorem md_kind_eq (info : String) : ofBlockKind (Fren.Core.blockKind info) =
    if info = Str.lit "fren" then markdown.BlockKind.Spec
    else if info = Str.lit "fren example" then markdown.BlockKind.Example
    else if decide (((Str.startsWith info (Str.lit "fren ") = true ∨ Str.startsWith info (Str.lit "fren\t") = true) ∨
        Str.startsWith info (Str.lit "fren,") = true) ∨ Str.startsWith info (Str.lit "fren{") = true) = true then
      markdown.BlockKind.LooksLikeFren
    else markdown.BlockKind.Prose := by
  simp only [Fren.Core.blockKind, Fren.Core.frenInfo, Fren.Core.frenExampleInfo, Fren.Str.lit]
  split
  · rfl
  split
  · rfl
  simp only [Bool.or_eq_true]
  split <;> simp_all [ofBlockKind]

def ofOpening (o : Fren.Core.Opening) : markdown.Opening := { marker := o.marker, run := o.run, info := o.info }

open Fren.Str in
/-- What `split` gives from the runs that `splitLine` finds. -/
theorem md_split_outs (line : String) :
    let P := Fren.Core.splitLine line
    (P.marker = if Str.at line ↑P.indent = Str.lit "`" ∨ Str.at line ↑P.indent = Str.lit "~" then
          Str.at line ↑P.indent else Str.lit "") ∧
      P.info = Str.slice line (↑P.indent + ↑P.run + ↑P.lead) (Str.len line - ↑P.indent - ↑P.run - ↑P.lead) ∧
      P.fence = decide ((↑P.indent ≤ (3 : Int) ∧ (3 : Int) ≤ ↑P.run) ∧
        ((if Str.at line ↑P.indent = Str.lit "`" ∨ Str.at line ↑P.indent = Str.lit "~" then
            Str.at line ↑P.indent else Str.lit "") = Str.lit "~" ∨
          ¬Str.contains (Str.slice line (↑P.indent + ↑P.run + ↑P.lead)
            (Str.len line - ↑P.indent - ↑P.run - ↑P.lead)) (Str.lit "`") = true)) := by
  dsimp only
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := md_split_fields line
  generalize Fren.Core.splitLine line = P at *
  simp only [Fren.Str.lit, Fren.Str.len] at *
  rw [← h2, ← h5]
  refine ⟨rfl, rfl, ?_⟩
  rw [h6]
  clear h1 h3 h4 h2 h5 h6
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    Bool.not_eq_true]
  have e : (P.indent ≤ 3 ∧ 3 ≤ P.run) ↔ ((P.indent : Int) ≤ 3 ∧ (3 : Int) ≤ P.run) := by
    constructor <;> intro h <;> omega
  rw [e]

open Fren.Str in
/-- The runs that `splitLine` finds are those that `markdown::runs?` states. -/
theorem md_runs (line : String) :
    let P := Fren.Core.splitLine line
    (((((∀ (k : Int), 0 ≤ k ∧ k < ↑P.indent → Str.at line k = Str.lit " ") ∧
        Str.at line ↑P.indent ≠ Str.lit " ") ∧
      ∀ (k : Int), ↑P.indent ≤ k ∧ k < ↑P.indent + ↑P.run → Str.at line k = Str.at line ↑P.indent) ∧
      (if Str.at line ↑P.indent = Str.lit "`" ∨ Str.at line ↑P.indent = Str.lit "~" then
          Str.at line (↑P.indent + ↑P.run) ≠ Str.at line ↑P.indent
        else (P.run : Int) = 0)) ∧
      ∀ (k : Int), ↑P.indent + ↑P.run ≤ k ∧ k < ↑P.indent + ↑P.run + ↑P.lead →
        decide (Str.at line k = Str.lit " " ∨ Str.at line k = Str.lit "\t") = true) ∧
    ¬decide (Str.at line (↑P.indent + ↑P.run + ↑P.lead) = Str.lit " " ∨
      Str.at line (↑P.indent + ↑P.run + ↑P.lead) = Str.lit "\t") = true := by
  dsimp only
  obtain ⟨⟨hm, _⟩, ha, hb, hc, hd, he, hf, hg, _⟩ := md_split_facts line
  obtain ⟨_, h2, h3, _⟩ := md_split_fields line
  generalize Fren.Core.splitLine line = P at *
  simp only [Fren.Str.lit] at *
  by_cases m : P.marker = ""
  · have r0 : P.run = 0 := by rw [if_pos m] at h3; exact h3
    have nc : ¬(Fren.Str.at line ↑P.indent = "`" ∨ Fren.Str.at line ↑P.indent = "~") := by
      intro hc'
      rw [if_pos hc'] at h2
      rcases hc' with e | e <;> rw [e] at h2 <;> rw [h2] at m <;> exact absurd m (by decide)
    refine ⟨⟨⟨⟨⟨ha, hb⟩, ?_⟩, ?_⟩, hf⟩, hg⟩
    · intro k ⟨k0, k1⟩; omega
    · rw [if_neg nc]; simp [r0]
  · have hc' : (Fren.Str.at line ↑P.indent = "`" ∨ Fren.Str.at line ↑P.indent = "~") := by
      rcases Classical.em (Fren.Str.at line ↑P.indent = "`" ∨ Fren.Str.at line ↑P.indent = "~") with h | hn
      · exact h
      · rw [if_neg hn] at h2; exact absurd h2 m
    have hmk : P.marker = Fren.Str.at line ↑P.indent := by rw [if_pos hc'] at h2; exact h2
    refine ⟨⟨⟨⟨⟨ha, hb⟩, ?_⟩, ?_⟩, hf⟩, hg⟩
    · intro k hk; rw [← hmk]; exact hc k hk
    · rw [if_pos hc']
      rcases hd with h | h
      · exact absurd h m
      · rw [← hmk]; exact h

impl split: markdown::split for (line : String) {
  line := line,
  indent := (Fren.Core.splitLine line).indent,
  run := (Fren.Core.splitLine line).run,
  lead := (Fren.Core.splitLine line).lead,
  marker := (Fren.Core.splitLine line).marker,
  info := (Fren.Core.splitLine line).info,
  fence? := (Fren.Core.splitLine line).fence,
} by
  intro line _
  simp only [fren_spec]
  exact ⟨md_split_outs line, trivial⟩

impl step: markdown::step for (inside : Bool) (o : Fren.Core.Opening) (line : String) {
  inside? := inside,
  opening := ofOpening o,
  line := line,
  indent := (Fren.Core.splitLine line).indent,
  run := (Fren.Core.splitLine line).run,
  lead := (Fren.Core.splitLine line).lead,
  inside_after? := (Fren.Core.step inside o line).inside,
  opening_after := ofOpening (Fren.Core.step inside o line).opening,
  body? := (Fren.Core.step inside o line).body,
  opens? := (Fren.Core.step inside o line).opens,
  kept? := (Fren.Core.step inside o line).kept,
} by
  intro inside o line hA
  simp only [fren_spec]
  clear hA
  refine ⟨_, line, (Fren.Core.splitLine line).indent, (Fren.Core.splitLine line).run,
    (Fren.Core.splitLine line).lead, (Fren.Core.splitLine line).marker, (Fren.Core.splitLine line).info,
    (Fren.Core.splitLine line).fence, o.info, ofBlockKind (Fren.Core.blockKind o.info),
    ⟨?_, rfl⟩, ?_, ⟨⟨rfl, rfl, rfl, rfl⟩, md_split_outs line, ?_, trivial⟩, rfl, trivial, md_kind_eq o.info⟩
  · simp only [Fren.Core.step]
    cases inside <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split <;> simp_all [ofOpening]
  · simp only [Fren.Core.step, Fren.Core.closesBlock, ofOpening, Fren.Str.lit]
    cases inside <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split <;> simp_all
    all_goals (first | decide | omega | skip)
    all_goals (cases h : Fren.Core.blockKind o.info <;> simp_all [ofBlockKind])
  · simpa only [decide_eq_true_eq] using md_runs line

impl block_kind: markdown::block_kind for (info : String) {
  info := info,
  kind := ofBlockKind (Fren.Core.blockKind info),
} by
  intro info _
  simp only [fren_spec]
  exact md_kind_eq info

end Fren.Impls
