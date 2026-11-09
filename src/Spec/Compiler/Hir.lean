import Fren.Impl
import Fren.Literate
import FrenBase.Identity
import FrenParse

open Fren.Lang

#fren_md "Hir.md"

#fren_check

namespace Spec.Compiler.Hir

/-- This is a theorem about actual canonical paths, not their display text
or a copied path datatype. The full resolver has not been implemented. -/
theorem named_identity (p q : FrenBase.ItemId) (a b : String) :
    FrenBase.ItemId.named p a = FrenBase.ItemId.named q b ↔ p = q ∧ a = b := by
  simp [FrenBase.ItemId.named, FrenBase.ItemId.child_eq_child]

-- Trailing tests: actual parser input controls and actual ItemId primitives.
section

private def resolutionInputs : List (String × Nat) := [
  ("pub mod signals\npub fn use_next(l: Light): Light := next(l)\n" ++
    "expect forward(l: Light) { expect same: next(l) = next(l) }\n" ++
    "pub fn next(l: Light): Light := Light::Red\npub enum Light { Red, Green }", 5),
  ("pub mod signals\nfn f(x: Int, y: Int): Int := let x := x + y in x + y", 2),
  ("pub mod signals\nfn f(x: Int): Int := let fresh := fresh in fresh", 2),
  ("pub mod signals\nenum Light { Red, Green }\n" ++
    "fn f(l: Light): Light := if true then Light::Red else signals::Light::Red", 3),
  ("pub mod signals\nenum Light { Red }\nenum Signal { Red }", 3),
  ("pub mod signals\nfn f(x: Int): Int := Red", 2),
  ("pub mod signals\nenum Light { Red }\nfn Light(x: Int): Int := x", 3),
  ("pub mod signals\nfn f(x: Int, x: Int): Int := x", 2),
  ("pub mod signals\nenum Light { Red, Red }", 2),
  ("pub mod signals\nenum Light { Red, Green }\nfn f(l: Light): Int := " ++
    "match l { Light::Red => (let z := 1 in z), Light::Green => z }", 3),
  ("pub mod bad\npub fn f(x: Int): Int := y + 1", 2),
  ("pub mod bad\npub enum Light { Red, Green }\npub fn f(l: Light): Int := l + 1", 3)]

#eval show IO Unit from do
  for (source, count) in resolutionInputs do
    let .ok doc := FrenParse.parseFile ⟨37⟩ source
      | throw <| IO.userError "resolution input did not parse"
    let .declarations decls := doc.root
      | throw <| IO.userError "resolution input has wrong root"
    unless decls.size == count do throw <| IO.userError "declaration collection input count"
  IO.println "resolution contract: 12 parsed input controls; no resolver verdict claimed"

-- The negative name-resolution example already exposes a precise name occurrence.
#guard match FrenParse.parseFile ⟨37⟩ "pub mod bad\npub fn f(x: Int): Int := y + 1" with
  | .ok doc => match doc.root with
    | .declarations ds => match ds[1]? with
      | some (FrenAst.Decl.function _ _ _ _ _ _ _ (.binary (.name path) _ _ _)) =>
        path.head.text == "y" && path.head.span.file == ⟨37⟩ &&
          path.head.span.start == 37 && path.head.span.stop == 38
      | _ => false
    | _ => false
  | .error _ => false

private def light := FrenBase.ItemId.named (FrenBase.ItemId.named .root "signals") "Light"
private def signal := FrenBase.ItemId.named (FrenBase.ItemId.named .root "signals") "Signal"
#guard FrenBase.ItemId.named light "Red" != FrenBase.ItemId.named signal "Red"
#guard FrenBase.ItemId.named light "Red" != FrenBase.ItemId.named light "Green"

end
end Spec.Compiler.Hir
