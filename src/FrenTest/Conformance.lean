-- keep-sorted start
import FrenTest.Messages
import FrenTest.Oracle
-- keep-sorted end

/-! # The decidable-core oracle

Failed checks and evidence downgrades are results of checking the generated
corpus, so exits 1 and 3 need their diagnostic; static errors and unexplained
exits fail. This differs from a subprocess used to measure coverage, whose
nonzero exit always fails (`Oracle.toolFailures`).
-/

namespace FrenTest.Conformance

/-- Only diagnostics explaining a normal checking exit may excuse it. -/
def exitAllowed (exit errors warnings : Nat) : Bool :=
  exit == 0 || (exit == 1 && errors > 0) || (exit == 3 && warnings > 0)

/-- Read the complete four-field summary, rejecting missing or malformed
counts rather than silently omitting them. -/
def counts? (out : String) : Option (Nat × Nat × Nat × Nat) := do
  let summary ← (out.splitOn "\n").find? (·.startsWith "fren: ")
  let [p, f, i, r] := (summary.drop 6).toString.splitOn ", " | none
  let count (s label : String) := (s.dropSuffix? label).bind (·.toString.toNat?)
  return (← count p " passed", ← count f " failed", ← count i " inconclusive", ← count r " redundant")

/-- The final verdict uses the actual output and status, retaining internal
errors before interpreting the summary. Only F0664 explains inconclusives. -/
def failures (out : String) (exit : Nat) : Array String := Id.run do
  let mut failures := Oracle.outputFailures out
  let diags := (out.splitOn "\n").filterMap Ui.header?
  let errors := diags.countP (·.1 == "error")
  let warnings := diags.countP (·.1 == "warning")
  unless exitAllowed exit errors warnings do
    failures := failures.push s!"conformance: unexpected exit {exit}"
  let some (p, f, i, r) := counts? out
    | return failures.push "conformance: missing or malformed summary"
  let resting := diags.countP fun (severity, code, _) => severity == "warning" && code == some "F0664"
  if i != resting || out.contains "could not check" then
    failures := failures.push "conformance: undecided checks"
  return Oracle.finish "conformance" (p + f + i + r) 1 failures

end FrenTest.Conformance
