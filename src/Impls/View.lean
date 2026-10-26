-- keep-sorted start
import Impls.Check
import Reqs.View
-- keep-sorted end
open Fren.Lang

/-! # Reporting (`Reqs/View`) -/

namespace Fren.Impls

open Fren.Core (Severity Verdict CheckKind CheckResult summarySeverity)

instance : Fren.Finite Severity := ⟨[.error, .warning, .info], by intro x; cases x <;> simp⟩

def toLevel : Option Severity → view.Severity
  | none => .Silent
  | some .info => .Info
  | some .warning => .Warning
  | some .error => .Error

impl severity: view::severity for (k : CheckKind) (v : Verdict) {
  kind := toCheckKind k,
  verdict := toVerdict v,
  level := toLevel (Fren.Core.severity? k v),
}

impl summary: view::summary for (rs : Array CheckResult) {
  level := toLevel (some (summarySeverity rs)),
} by
  intro rs _
  simp [fren_spec, summarySeverity, toLevel]

def toBucket : Fren.Core.Bucket → view.Bucket
  | .passed => .Passed
  | .failed => .Failed
  | .inconclusive => .InconclusiveBucket
  | .redundant => .Redundant

-- `Fren.Core.summary` counts each result in its `bucketOf`.
impl counted: view::counted for (k : CheckKind) (v : Verdict) {
  kind := toCheckKind k,
  verdict := toVerdict v,
  bucket := toBucket (Fren.Core.bucketOf k v),
}

def toAdvice : Fren.Core.Advice → view.Advice
  | .raiseTimeout => .RaiseTimeout
  | .namesConstructs => .NamesConstructs

impl inconclusive_advice: view::inconclusive_advice for (d : Bool) {
  decidable? := d,
  advice := toAdvice (Fren.Core.inconclusiveAdvice d),
}

/-! ## Clash notes -/

theorem furtherWildcards_toList (k : Nat) :
    (Fren.Core.furtherWildcards k).toList = (List.replicate k [',', ' ', '_']).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Fren.Core.furtherWildcards, List.replicate_succ, String.join_cons, String.toList_append] at ih ⊢
    rw [ih]
    rfl

/-- Removing every `, _` from the `, _`s of `k` values leaves nothing, with
the fuel that `Str.replaceAll` gives. -/
theorem replaceAllAux_further (k fuel : Nat) (h : k < fuel) :
    Fren.Str.replaceAllAux fuel (List.replicate k [',', ' ', '_']).flatten [',', ' ', '_'] [] = [] := by
  induction k generalizing fuel with
  | zero =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | succ k ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append]
    rw [Fren.Str.replaceAllAux]
    simp only [List.isPrefixOf, BEq.rfl, Bool.and_true, if_true, List.nil_append, List.length_cons, List.length_nil]
    simpa using ih f (by omega)

/-- Removing every `, _` from `_` and the `, _`s of `k` values leaves `_`. -/
theorem replaceAll_wildcards (k : Nat) :
    Fren.Str.replaceAll ("_" ++ Fren.Core.furtherWildcards k) ", _" "" = "_" := by
  have hlen : (Fren.Core.furtherWildcards k).toList.length = 3 * k := by
    rw [furtherWildcards_toList]; simp [Nat.mul_comm]
  simp only [Fren.Str.replaceAll, show (", _" : String).isEmpty = false from rfl, Bool.false_eq_true, if_false]
  rw [show (", _" : String).toList = [',', ' ', '_'] from rfl, show ("" : String).toList = [] from rfl,
    String.toList_append, show ("_" : String).toList = ['_'] from rfl, List.singleton_append,
    String.length_append, show ("_" : String).length = 1 from rfl, ← String.length_toList, hlen]
  rw [show 1 + 3 * k + 1 = (3 * k + 1) + 1 by omega, Fren.Str.replaceAllAux, furtherWildcards_toList]
  simp only [List.isPrefixOf]
  rw [replaceAllAux_further _ _ (by omega)]
  rfl

-- For every arity, `Core.wildcards`: `_`, and `, _` for each further value.
impl wildcards: view::wildcards for (n : Nat) {
  arity := n,
  text := Fren.Core.wildcards n,
  shaped? := true,
} by
  intro n
  have hlen : (Fren.Core.furtherWildcards (n - 1)).length = 3 * (n - 1) := by
    rw [← String.length_toList, furtherWildcards_toList]
    simp [Nat.mul_comm]
  simp only [fren_spec, Fren.Str.lit]
  by_cases h : n = 0
  · subst h; simp [Fren.Core.wildcards]
  · have h' : ¬(n : Int) = 0 := by omega
    simp only [h', if_false, Fren.Core.wildcards, h]
    intro _
    refine ⟨?_, trivial⟩
    rw [eq_comm, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [Fren.Str.startsWith, show ("_" : String).toList = ['_'] from rfl]
    · simp only [Fren.Str.len, String.length_append, hlen, show ("_" : String).length = 1 from rfl]; omega
    · exact replaceAll_wildcards _

def toForced : Fren.Core.Forced → view.Forced
  | .value v => .Value v
  | .variant k => .Variant k.name k.arity

-- For every guarantee, output, what each side forces and others,
-- `Core.clashText`'s line, with the wildcards of `Core.wildcards`.
impl clash_text: view::clash_text for (g o r : String) (f f' : Fren.Core.Forced) (n : Int) {
  guarantee := g,
  output := o,
  forced := toForced f,
  blanks := f.blanks,
  others := r,
  count := n,
  other_forced := toForced f',
  other_blanks := f'.blanks,
  said := Fren.Core.forcedText o f,
  other_said := Fren.Core.forcedText o f',
  text := Fren.Core.clashLine g o f r f' n.toNat,
} by
  intro g o r f f' n h
  simp only [fren_spec, Fren.Core.clashLine, Fren.Str.lit] at *
  have ts : ∀ s : String, toString s = s := fun _ => rfl
  have hn : (n.toNat = 1) = (n = 1) := by apply propext; omega
  rcases f with v | ⟨c, a⟩ <;> rcases f' with v' | ⟨c', a'⟩ <;>
    simp only [toForced, view.Forced.Value.x0, view.Forced.Variant.x0, view.Forced.Variant.x1, Fren.Core.forcedText,
      Fren.Core.Variant.pattern, Fren.Core.Forced.blanks, ts, hn, reduceCtorEq, if_true, if_false, Int.natCast_eq_zero,
      String.append_assoc, and_true]
  all_goals (repeat' split) <;> first | (exfalso; omega) | simp only [String.append_empty, String.empty_append, String.append_assoc, and_self]

end Fren.Impls
