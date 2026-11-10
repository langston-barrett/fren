module

public import FrenWalking
meta import FrenWalking

/-! The walking program's admitted boundary, against `FrenWalking.fromSource`
and `fromResolved`: rejected sources build no program, an edited resolver
table is refused, and the admitted program keeps the data that distinguishes
one source from another. -/

namespace FrenWalkingTests
open FrenWalking

private def source : String := "pub mod skeleton\n\n\
  pub enum Light { Red, Amber, Green }\n\
  pub fn next(l: Light): Light := match l { Light::Red => Light::Green, Light::Green => Light::Amber, Light::Amber => Light::Red, }\n\
  pub fn wait(l: Light, base: Int): Int := match l { Light::Red => (base) + 30, Light::Amber => base + 5, Light::Green => base, }\n\
  fn partial(x: Int): Int := x div 0\n\
  expect cycles(l: Light) { expect back: next(next(next(l))) = l }\n\
  expect waits(l: Light, base: Int) { assume bounded: base <= 100 expect at_most: wait(l, base) <= 130 }\n"

/-- Unresolved name, type error, recursion, missing match arm, syntax error. -/
private def rejected : Array String :=
  #["mod bad\nfn f(x: Int): Int := y + 1",
    "mod bad\nenum Light { Red, Green }\nfn f(l: Light): Int := l + 1",
    source ++ "\nfn loop(x: Int): Int := loop(x)",
    "mod bad\nenum Light { Red, Green }\nfn f(l: Light): Int := match l { Light::Red => 0 }",
    "mod bad\nfn f(x: Int): Int := ("]

private def boundary (n : Nat) : Bool := Id.run do
  let .ok p := fromSource ⟨n⟩ source | return false
  -- The admitted program is the checker's output for the retained source.
  if p.typed.resolved != p.input || p.input.document.emit != source then return false
  let .ok again := FrenHirToThir.checkWalking p.input | return false
  if again != p.typed then return false
  if rejected.any fun s => (fromSource ⟨n⟩ s).isOk then return false
  -- Admission re-runs the resolver: an edited table is refused.
  if (fromResolved {p.input with references := #[]}).isOk then return false
  -- Controls: each edit of the typed record, or of the source, is visible.
  if ({p.typed with bodies := #[]} : FrenModule.Typed) == p.typed then return false
  if ({p.typed with signatures := #[]} : FrenModule.Typed) == p.typed then return false
  if ({p.typed with resolved := {p.input with references := #[]}} : FrenModule.Typed) == p.typed then
    return false
  let edits := #[(n + 1, source),
    (n, source.replace "assume bounded:" "expect bounded:"),
    (n, source.replace "assume bounded: base <= 100 " ""),
    (n, source.replace "expect at_most: wait(l, base) <= 130" ""),
    (n, source.replace "(base)" "base"),
    (n, source.replace "Amber" "Yellow")]
  for (file, edited) in edits do
    let .ok q := fromSource ⟨file⟩ edited | return false
    if q.typed == p.typed then return false
  return true

#guard boundary 0
#guard boundary 7

end FrenWalkingTests
