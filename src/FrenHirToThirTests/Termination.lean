module

public import FrenHirToThirTests.Support

public section
namespace FrenHirToThirTests
open FrenHirToThir.Termination

private abbrev Fn := Function String Unit

private def fn (item : String) (parameters : Nat) (body : Calls String)
    (unchecked := false) : Fn :=
  ⟨item, List.replicate parameters (), unchecked, body⟩

/-- A generated group of up to three functions `f0`, `f1`, `f2`, each with up
to two parameters and a body of calls drawn from the seed; `f3` is outside. -/
private def generatedCalls : Nat → Nat → Calls String
  | 0, n => if n % 3 == 0 then .leaf else
      .call s!"f{n % 4}" [if n % 5 == 0 then none else some (n % 3), some (n / 5 % 3)]
  | depth + 1, n =>
    match n % 3 with
    | 0 => .both (generatedCalls depth (n / 3)) (generatedCalls depth (n / 3 + 7))
    | 1 => .bind (if n % 2 == 0 then some (n / 3 % 2) else none) (generatedCalls depth (n / 3))
    | _ => generatedCalls depth (n / 3)

private def generatedGroup (n : Nat) : List Fn :=
  (List.range (n % 4)).map fun i =>
    fn s!"f{i}" ((n / 4 + i) % 3) (generatedCalls 3 (n / 12 + 31 * i)) (n % 11 == 0)

private def sizeCases : IO Unit := do
  require (parameterSizes [(), (), ()] 1 == [.unknown, .same, .unknown]) "parameter sizes"
  require (parameterSizes [()] 4 == [.unknown]) "decreasing parameter out of range"
  require (localSize [.same, .smaller] (some 1) == .smaller &&
    localSize [.same] (some 3) == .unknown && localSize [.smaller] none == .unknown) "local size"
  require (argumentGuarded [.same, .smaller] [some 0, some 1] 1 &&
    !argumentGuarded [.same, .smaller] [some 0, some 1] 0 &&
    !argumentGuarded [.smaller] [none] 0 && !argumentGuarded [.smaller] [some 0] 1)
    "guarded argument"

private def guardCases : IO Unit := do
  let choice := [("f", 0), ("g", 1)]
  require (chosen choice "g" == some 1 && chosen choice "h" == none &&
    chosen (choice ++ [("f", 2)]) "f" == some 2) "chosen parameter"
  -- A call is guarded when its argument at the callee's parameter is smaller.
  require (callsGuarded choice [.smaller] (.call "f" [some 0])) "smaller argument"
  require (!callsGuarded choice [.same] (.call "f" [some 0])) "the parameter itself"
  require (!callsGuarded choice [.smaller] (.call "g" [some 0])) "callee's own parameter"
  require (callsGuarded choice [.smaller] (.call "g" [none, some 0])) "mutual call"
  require (callsGuarded choice [.same] (.call "h" [some 0])) "call out of the group"
  -- A let gives its local the size of its value.
  require (callsGuarded choice [.smaller] (.bind (some 0) (.call "f" [some 1]))) "let of smaller"
  require (!callsGuarded choice [.smaller] (.bind none (.call "f" [some 1]))) "let of a form"
  require (!callsGuarded choice [.smaller]
    (.both (.call "f" [some 0]) (.call "f" [none]))) "every call is checked"

private def groupCases : IO Unit := do
  let call := Calls.call "f" [some 0]
  -- Each choice gives each function one of its parameters, in the group's order.
  require (choices [fn "f" 2 .leaf, fn "g" 1 .leaf] ==
    [[("f", 0), ("g", 0)], [("f", 1), ("g", 0)]]) "choices"
  require (choices ([] : List Fn) == [[]] && choices [fn "f" 2 .leaf, fn "g" 0 .leaf] == [])
    "choices of no function and of no parameter"
  -- A group whose bodies make no call of the group passes.
  require (groupPasses [fn "f" 1 (.call "h" [some 0]), fn "g" 2 .leaf]) "accepted group"
  require (!groupPasses [fn "f" 1 call]) "self call on the parameter itself"
  require (!groupPasses [fn "f" 1 (.call "g" [some 0]), fn "g" 1 call]) "mutual calls"
  require (!groupPasses [fn "f" 0 .leaf] && !structural [fn "f" 1 .leaf, fn "g" 0 .leaf])
    "no parameter to decrease on"
  -- The mark `unchecked` on any function of the group fails the whole group.
  require (!groupPasses [fn "f" 1 .leaf, fn "g" 1 .leaf (unchecked := true)] &&
    structural [fn "f" 1 .leaf, fn "g" 1 .leaf (unchecked := true)] &&
    optedOut [fn "f" 1 .leaf, fn "g" 1 .leaf (unchecked := true)] &&
    !optedOut [fn "f" 1 .leaf]) "opt-out of a group"
  require (passesAlone (fn "f" 0 .leaf) && !passesAlone (fn "f" 1 .leaf (unchecked := true)))
    "opt-out of a function in no group"

private def conditionCases : IO Unit := do
  let passes : String → Bool := fun item => item != "loop"
  let reached : String → List String
    | "top" => ["mid", "loop"]
    | "mid" => ["loop"]
    | "ok" => ["leaf"]
    | "loop" => ["loop"]
    | _ => []
  require (hereditary passes reached "ok" && hereditary passes reached "leaf") "hereditary pass"
  require (!hereditary passes reached "loop" && !hereditary passes reached "mid" &&
    !hereditary passes reached "top") "reaches a function that fails"
  require (conditionTerminating passes reached ["ok", "leaf"] &&
    conditionTerminating passes reached [] &&
    !conditionTerminating passes reached ["ok", "mid"]) "condition calls"

/-- The closed form that validation runs gives the verdict of the search, on
generated groups of each verdict. `structural_eq_now` proves it for all. -/
private def searchCases : IO Unit := do
  let mut passed := 0
  let mut failed := 0
  let mut optedOutCount := 0
  for n in [:3000] do
    let group := generatedGroup n
    require (structural group == structuralNow group &&
      groupPasses group == groupPassesNow group) s!"closed form differs at {n}"
    require ((choices group).length == (group.map (·.parameters.length)).foldl (· * ·) 1)
      s!"choice count at {n}"
    if optedOut group then optedOutCount := optedOutCount + 1
    if groupPasses group then passed := passed + 1 else failed := failed + 1
  require (passed > 100 && failed > 100 && optedOutCount > 100)
    s!"vacuous search census: {passed} {failed} {optedOutCount}"
  IO.println s!"termination search census: passed={passed}; failed={failed}; opted out={optedOutCount}"

def runTermination : IO Unit := do
  sizeCases
  guardCases
  groupCases
  conditionCases
  searchCases
  IO.println "termination: sizes, guards, groups, opt-out and conditions passed"

end FrenHirToThirTests
