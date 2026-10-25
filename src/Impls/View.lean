-- keep-sorted start
import Impls.Check
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
  | .redundant => .RedundantBucket

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

-- `lake test` checks that every code is well formed and in its group.
tested view::code_group: "src/FrenTestMain.lean"

end Fren.Impls
