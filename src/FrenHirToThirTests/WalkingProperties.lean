module

public import FrenHirToThirTests.Support
import Plausible

public section
namespace FrenHirToThirTests
open FrenAst FrenModule FrenHirToThir Plausible
open scoped Plausible.Decorations

private def tree : Nat → Nat → String
  | 0, n => if n % 2 == 0 then "x" else toString (n % 17)
  | depth + 1, n =>
    let a := tree depth (n / 3)
    let b := tree depth (n / 3 + 2)
    match n % 6 with
    | 0 => s!"({a} + {b})"
    | 1 => s!"(if false then {a} else {b})"
    | 2 => s!"(let x := {a} in {b})"
    | 3 => s!"(match E::A \{ E::B => {a}, E::A => {b} })"
    | 4 => s!"g({a})"
    | _ => s!"(match (match E::B \{ E::A => E::B, E::B => E::A }) \{ E::A => {a}, E::B => {b} })"

structure WalkingCounts where
  accepted : Nat := 0
  coverageRejected : Nat := 0
  cycleRejected : Nat := 0
  typingRejected : Nat := 0
  providerRejected : Nat := 0
  deriving Repr

/-- All samples must satisfy explicit premises. No filter/discard and no
second IR, alternate checker, or supplied graph decides expected results. -/
private def sample (n file : Nat) : Option WalkingCounts := do
  let good := tree (n % 3 + 1) n
  let pre := "mod m\nenum E { A, B }\nfn g(x: Int): Int := x\nfn f(x: Int): Int := "
  let mut recursion := ""
  let length := n % 4 + 1
  for i in [:length] do
    recursion := recursion ++ s!"\nfn r{i}(x: Int): Int := r{(i + 1) % length}(x)"
  let variants := #[(pre ++ good, 0),
    (pre ++ s!"match E::A \{ E::A => {good} }", 1),
    (pre ++ s!"match E::A \{ E::A => {good}, E::A => 0 }", 1),
    (pre ++ good ++ recursion, 2),
    (pre ++ s!"if true then {good} else false", 3)]
  let mut counts : WalkingCounts := {}
  for (source, expected) in variants do
    let .ok doc := FrenParse.parseFile ⟨file⟩ source | none
    let .ok r := FrenAstToHir.resolve doc | none
    let result := checkWalking r
    if !sameResult result (checkWalking r) then none else pure () -- actual determinism
    match result with
    | .ok t =>
      if expected != 0 || t.resolved != r || t.resolved.document.emit != source ||
          !sameResult (check r) (.ok t) || !(validateCoverage t).isOk || !(validateNonrecursive t).isOk then
        none else pure ()
      counts := {counts with accepted := counts.accepted + 1}
    | .error (.validation (.coverage _ owner missing repeated)) =>
      if expected != 1 || owner != key "E" || missing != #[(key "E").named "B"] ||
          repeated != (if source == (variants[1]!).1 then #[] else #[(key "E").named "A"]) ||
          !(check r).isOk then none else pure ()
      counts := {counts with coverageRejected := counts.coverageRejected + 1}
    | .error (.validation (.termination _ group .unguarded)) =>
      let expectedGroup := (List.range length).toArray.map (fun i => key s!"r{i}")
      if expected != 2 || group != expectedGroup || !(check r).isOk then none else pure ()
      counts := {counts with cycleRejected := counts.cycleRejected + 1}
    | .error (.typing _) =>
      if expected != 3 || (check r).isOk then none else pure ()
      counts := {counts with typingRejected := counts.typingRejected + 1}
    | _ => none
    let .error (.typing d) := checkWalking {r with references := #[]} | none
    if d.headline != "walking type error: incoherent resolved input" then none else pure ()
    counts := {counts with providerRejected := counts.providerRejected + 1}
  return counts

private def audit (n file : Nat) : Bool :=
  match sample n file with
  | none => false
  | some c => c.accepted == 1 && c.coverageRejected == 2 && c.cycleRejected == 1 &&
    c.typingRejected == 1 && c.providerRejected == 5

private def checkProperty (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 40, randomSeed := some 20261110}
  IO.println s!"actual walking static Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "walking validation Plausible failure")

def runWalkingProperties : IO Unit := do
  checkProperty <| ∀ (n file : Nat), audit n file = true
  let mut totals : WalkingCounts := {}
  for n in [:24] do
    let some c := sample n 93 | throw (IO.userError s!"walking census failed at {n}")
    totals := ⟨totals.accepted + c.accepted, totals.coverageRejected + c.coverageRejected,
      totals.cycleRejected + c.cycleRejected, totals.typingRejected + c.typingRejected,
      totals.providerRejected + c.providerRejected⟩
  require (totals.accepted == 24 && totals.coverageRejected == 48 && totals.cycleRejected == 24 &&
    totals.typingRejected == 24 && totals.providerRejected == 120) "vacuous walking census"
  IO.println s!"actual walking premise census: {repr totals}; discarded=0; finite evidence, no universal traversal soundness proof"

end FrenHirToThirTests
