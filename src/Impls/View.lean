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

-- For every guarantee, output, values and others, `Core.clashText`'s line.
impl clash_text: view::clash_text for (g o v r w : String) (n : Int) {
  guarantee := g,
  output := o,
  value := v,
  others := r,
  count := n,
  other_value := w,
  text := Fren.Core.clashLine g o v r w n.toNat,
} by
  intro g o v r w n h
  simp only [fren_spec, Fren.Core.clashLine, Fren.Str.lit, toString] at *
  by_cases h1 : n = 1
  · subst h1; simp
  · have : n.toNat ≠ 1 := by omega
    simp [h1, this]

end Fren.Impls
