import FrenCore.Induction

/-! Regression checks of the inputs that both front ends extract for
`lang::induction_candidate`, and of the refuted-model guard. -/

namespace FrenTest.InductionCandidates

open Fren.Core

private def listTy : Ty := .enum `G [.bool]

private def shapes (n : Lean.Name) : Option DataShape :=
  if n == `G then some { parts := #[#[], #[{ ty := .param 0 `A }, { ty := .enum `G [.param 0 `A] }]] }
  else if n == `Leaf then some { parts := #[#[], #[]] }
  else none

private def params : Array (Lean.Name × PTy) :=
  #[(`other, PTy.plain (.enum `Leaf [])), (`a, PTy.plain listTy), (`b, PTy.plain listTy)]

-- Instantiation must recognize G<Bool>'s child; a nonrecursive enum and
-- unused recursive parameters do not become candidates. Order follows
-- parameters, independently of the order in which applications were read.
#guard inductionCandidates shapes [.expect] false params #[`b, `a] == [1, 2]
#guard inductionCandidates shapes [.assume, .cover, .expect] false params #[`b] == [2]
#guard inductionCandidates shapes [.expect] false params #[] == []
#guard inductionCandidates shapes [.call, .expect] false params #[`a] == []
#guard inductionCandidates shapes [.expect] true params #[`a] == []

-- A restriction nested in an unused companion's element type excludes
-- every candidate. A subset payload in the enum itself does not.
private def restricted : PTy := { ty := .int, invariants := #[⟨`positive, `positive⟩] }
#guard inductionCandidates shapes [.expect] false
  (params.push (`unused, { ty := .seq .int, elems := #[restricted] })) #[`a] == []
#guard inductionCandidates (fun n => (shapes n).map fun d =>
    { d with parts := d.parts.push #[restricted] }) [.expect] false params #[`a] == [1]

-- Only a local variable written at the decreasing position is collected;
-- binders shadow it, and a derived argument is represented by none.
#guard inductionArgument? (some 1) #[none, some `a] #[`a] (fun _ => false) == some `a
#guard inductionArgument? (some 1) #[some `a, none] #[`a] (fun _ => false) == none
#guard inductionArgument? (some 0) #[some `a] #[`a] (· == `a) == none
#guard inductionArgument? (some 0) #[some `constant] #[`a] (fun _ => false) == none
#guard inductionArgument? none #[some `a] #[`a] (fun _ => false) == none
#guard inductionArgument? (some 2) #[some `a] #[`a] (fun _ => false) == none

-- Both representations of the internal error bar a passing induction;
-- ordinary solver unknowns and unconfirmed recursion models remain eligible.
#guard (Detail.refuted .goal #[]).modelRefuted
#guard (Detail.unknown refutedModelReason).modelRefuted
#guard !(Detail.unknown "timeout").modelRefuted
#guard inductionVerdict .inconclusive (Detail.refuted .goal #[]).modelRefuted [.pass] == .inconclusive
#guard inductionVerdict .inconclusive (Detail.unknown refutedModelReason).modelRefuted [.pass] == .inconclusive
#guard inductionVerdict .inconclusive false [.pass] == .pass

end FrenTest.InductionCandidates
