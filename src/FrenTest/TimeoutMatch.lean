-- keep-sorted start
import FrenTest.Messages
-- keep-sorted end

/-!
# Differences caused by solver timeouts

The shared and unshared paths of the binary must give the same output,
apart from the results of checks whose queries timed out
(`Reqs/dev/Testing`, "The binary's shared reading"). Match those checks
by their source position and question, including the subject, kind,
target, and row or arm numbers that the diagnostic names.
-/

namespace FrenTest.TimeoutMatch

/-- The blocks of a run's output: each diagnostic, from its line that
starts with a letter (`warning[F0608]: …`) to the next such line, and each
line of the summary. -/
def outputBlocks (out : String) : Array String := Id.run do
  let mut blocks : Array String := #[]
  for l in out.splitOn "\n" do
    let starts := l.toList.head?.any Char.isAlpha
    if starts || blocks.isEmpty then blocks := blocks.push l
    else blocks := blocks.modify (blocks.size - 1) (· ++ "\n" ++ l)
  return blocks

/-- Where a diagnostic block points (`--> FILE:LINE:COL`), if it does. -/
def blockSite (block : String) : Option String :=
  (block.splitOn "\n").findSome? fun l => match l.splitOn "--> " with
    | [_, site] => some site.trimAscii.toString
    | _ => none

/-- The question of a timed-out check, or of a decided result, phrased
as the undecided result phrases it. Only recognized results are matched;
internal errors and supplementary diagnostics never stand for a verdict.
Keep names, types, targets and row/arm numbers verbatim. -/
def question? (block : String) : Option String := do
  let (_, code?, text) ← Ui.header? ((block.splitOn "\n").head!.trimAscii.toString)
  let h := (text.splitOn ": ").head!
  let frame (pre post newPre newPost : String) : Option String := do
    let s ← h.dropPrefix? pre
    let s ← s.toString.dropSuffix? post
    return newPre ++ s.toString ++ newPost
  let replace (old new : String) : Option String := match h.splitOn old with
    | [a, b] => some (a ++ new ++ b)
    | _ => none
  match code? with
  | some "F0608" => do
    guard (text.endsWith ": the solver returned unknown (TIMEOUT)")
    (h.dropPrefix? "could not decide whether ").map (·.toString)
  | some "F0601" => frame "" " is not realizable" "" " is realizable"
  | some "F0603" => frame "expectation " " does not hold" "" " holds"
  | some "F0604" => replace " may not hold for call " " holds for call "
  | some "F0605" => frame "" " is vacuous" "" " is vacuous"
  | some "F0606" => frame "" " is redundant" "" " is redundant"
  | some "F0607" => frame "" " is not determined by the inputs" "" " is determined by the inputs"
  | some "F0611" => frame "an index of " " may be out of range" "an index of " " is in range"
  | some "F0615" => frame "cover goal " " cannot be met" "" " can be met"
  | some "F0618" => frame "a table in " " may have no row that holds" "some row of a table in " " holds"
  | some "F0619" => frame "" " may both hold" "" " are disjoint"
  | some "F0625" => frame "a `match` in " " may have no arm that is taken" "some arm of a `match` in " " is taken"
  | some "F0626" | some "F0638" => frame "" " is never taken" "" " can be taken"
  | some "F0627" => frame "" " is never the first that holds" "" " can be taken"
  | some "F0629" => replace " may not hold at this application in " " holds at an application in "
  | some "F0630" => frame "" " does not hold" "" " holds"
  | some "F0631" => frame "" " cannot all hold" "" " can hold"
  | some "F0632" => frame "the preconditions of " " are unsatisfiable" "the postconditions of " " can hold"
  | some "F0636" => frame "" " may both be taken" "" " are disjoint"
  | some "F0637" => frame "a table in " " may have no arm that is taken" "some arm of a table in " " is taken"
  | some "F0653" => frame "" " cannot all hold at some type" "" " can hold"
  | some "F0661" => do
    let rest ← h.dropPrefix? "the invariant of type "
    match rest.toString.splitOn " does not hold for a value in " with
    | [ty, subject] => return s!"a value in {subject} has the type {ty}"
    | _ =>
      let [ty, param] := rest.toString.splitOn " does not hold for parameter " | none
      let [param, call] := param.splitOn " in call " | none
      return s!"the parameter {param} has its type {ty} for call {call}"
  | none => frame "cover goal " " is met" "" " can be met"
  -- F0602 can mean realizability or vacuity under trait laws. Its
  -- headline does not tell those checks apart, so do not excuse it.
  | _ => none

/-- A check's rendered identity: its full file/line/column and question.
An absent position or an unrecognized result cannot match another check. -/
def blockCheck? (block : String) : Option (String × String) := do
  return (← blockSite block, ← question? block)

/-- This diagnostic, rather than text in a note, reports a solver timeout. -/
def timedOut (block : String) : Bool :=
  match Ui.header? ((block.splitOn "\n").head!.trimAscii.toString) with
  | some (_, some "F0608", text) => text.startsWith "could not decide whether "
      && text.endsWith ": the solver returned unknown (TIMEOUT)" && (blockCheck? block).isSome
  | _ => false

/-- `xs` without one occurrence of each of `ys`. -/
def removeEach (xs ys : Array String) : Array String :=
  ys.foldl (init := xs) fun acc y => match acc.idxOf? y with
    | some i => acc.eraseIdx! i
    | none => acc

/-- Whether outputs differ only in checks whose queries timed out. A
decided diagnostic must match one timeout of the other run, at the same
position and about the same question, at most once. A passing check can
be silent. Summary counts and explain hints are excused only when such
timeouts explain every diagnostic difference. -/
def onlyTimedOut (a b : String) : Bool := Id.run do
  let (xs, ys) := (outputBlocks a, outputBlocks b)
  let (xs, ys) := (removeEach xs ys, removeEach ys xs)
  let summary (block : String) :=
    block.startsWith "fren: " || block.startsWith "Some errors have" || block.startsWith "For more information"
  let explained (ds other : Array String) : Bool := Id.run do
    let mut timed := other.filter timedOut
    for d in ds do
      if summary d || timedOut d then continue
      let some key := blockCheck? d | return false
      let some i := timed.findIdx? (fun t => blockCheck? t == some key) | return false
      timed := timed.eraseIdx! i
    return true
  return (xs.any timedOut || ys.any timedOut) && explained xs ys && explained ys xs

end FrenTest.TimeoutMatch
