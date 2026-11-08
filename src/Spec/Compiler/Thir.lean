import Fren.Impl
import Fren.Literate
import FrenHirToThir

open Fren.Lang

#fren_md "Thir.md"

#fren_check

namespace Spec.Compiler.Thir

/-- Same concrete successful-producer relation established by actual admission.
The public Resolved structure alone remains insufficient evidence. -/
def Admitted (input : FrenModule.Resolved) : Prop :=
  FrenHirToThir.Admitted input

/-- Nominal key equality uses the real canonical API, not a display string. -/
theorem nominal_key (a b : FrenBase.ItemId) : (a == b) = true ↔ a = b :=
  FrenBase.ItemId.beq_eq_true_iff a b

#check FrenHirToThir.check_retains
#check FrenHirToThir.erasure
#check FrenHirToThir.deterministic
#check FrenHirToThir.TypingSound

-- Focused accepted-resolver input and source anchor, not a typing verdict.
private def enumArithmetic :=
  "pub mod bad\n\npub enum Light { Red, Green }\n\n" ++
  "pub fn f(l: Light): Int := l + 1\n"

#guard match FrenParse.parseFile ⟨37⟩ enumArithmetic with
  | .ok doc => match FrenAstToHir.resolve doc with
    | .ok result =>
      let light := FrenBase.ItemId.named (FrenBase.ItemId.named .root "bad") "Light"
      result.references.any (fun r => r.role == .annotation && r.target == .item light) &&
      result.references.any (fun r => r.role == .expression && r.target == .local 0 &&
        r.written.anchor.text == "l" && r.context.map (·.text) == ["l"] &&
        r.written.anchor.span.file == ⟨37⟩ &&
        r.written.anchor.span.start == 71 && r.written.anchor.span.stop == 72)
    | .error _ => false
  | .error _ => false

-- Display collisions are possible in the base API: rendering is not a key.
private def dotted := FrenBase.ItemId.named .root "bad.Light"
private def nested := FrenBase.ItemId.named (FrenBase.ItemId.named .root "bad") "Light"
#guard dotted.render == nested.render
#guard dotted != nested
#guard FrenBase.ItemId.named nested "Red" !=
  FrenBase.ItemId.named (FrenBase.ItemId.named (FrenBase.ItemId.named .root "bad") "Signal") "Red"

end Spec.Compiler.Thir
