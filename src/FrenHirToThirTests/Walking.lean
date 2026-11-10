module

public import FrenHirToThirTests.Support
public import FrenHirToThirTests.Termination

public section
namespace FrenHirToThirTests
open FrenAst FrenModule FrenHirToThir

private def accepts (source : String) : IO Typed := do
  let .ok t := checkWalkingSource ⟨47⟩ source
    | throw (IO.userError s!"walking rejected: {source}")
  require (t.resolved.document.emit == source && (validateCoverage t).isOk &&
    (validateNonrecursive t).isOk) "static erasure/validators"
  return t

private def fails (source : String) : IO WalkingFailure := do
  let t ← typed source -- Each negative here really passes actual typing.
  let .error (.validation d) := checkWalkingSource ⟨47⟩ source
    | throw (IO.userError s!"expected validation failure: {source}")
  require (sameResult (validateWalking t) (.error d)) "source/typed validation disagreement"
  return d

private def coverageCases : IO Unit := do
  let pre := "mod m\nenum E { A, B, C }\nfn f(e: E): Int := "
  let owner := key "E"
  let a := owner.named "A"
  let b := owner.named "B"
  let c := owner.named "C"
  let whole := "match e { E::A => 1, E::B => 2, E::C => 3 }"
  for arms in ["E::A => 1, E::B => 2, E::C => 3", "E::C => 3, E::A => 1, E::B => 2"] do
    let t ← accepts (pre ++ "match e { " ++ arms ++ " }")
    require (constructors t owner == #[a, b, c]) "declaration-ordered actual inventory"
  let missing ← fails (pre ++ "match e { E::B => 2 }")
  match missing with
  | .coverage span id absent duplicates =>
    require (id == owner && absent == #[a, c] && duplicates.isEmpty &&
      span.file == ⟨47⟩ && span.start == 44 && span.stop == 49) "missing oracle/keyword span"
  | _ => throw (IO.userError "wrong missing failure")
  -- Same case count as the enum, but one repeated ID and one absent ID.
  let duplicate ← fails (pre ++ "match e { E::A => 1, E::A => 2, E::C => 3 }")
  match duplicate with
  | .coverage span id absent duplicates =>
    require (id == owner && absent == #[b] && duplicates == #[a] &&
      span.file == ⟨47⟩ && span.start == 65 && span.stop == 66) "same-count duplicate oracle/span"
  | _ => throw (IO.userError "wrong duplicate failure")
  let extra ← fails (pre ++ "match e { E::A => 1, E::B => 2, E::C => 3, E::B => 4 }")
  match extra with
  | .coverage _ _ absent duplicates =>
    require (absent.isEmpty && duplicates == #[b]) "duplicate with no missing case"
  | _ => throw (IO.userError "wrong extra failure")
  for body in [
    "if true then 0 else match e { E::A => 0 }",
    "let x := match e { E::A => 0 } in 1",
    "1 + (match e { E::A => 0 })",
    "match e { E::A => 0, E::B => match e { E::A => 0 }, E::C => 0 }",
    "match (match e { E::A => e }) { E::A => 0, E::B => 1, E::C => 2 }"] do
    match ← fails (pre ++ body) with
    | .coverage _ id absent _ => require (id == owner && absent == #[b, c]) "nested coverage missed"
    | _ => throw (IO.userError "wrong nested failure")
  for kind in ["assume", "expect"] do
    discard <| fails ("mod m\nenum E { A, B, C }\nexpect q(e: E) { " ++ kind ++
      " p: (match e { E::A => 0 }) = 0 }")
  -- Coverage derives E's inventory even when F has identically spelled variants.
  discard <| accepts ("mod m\nenum E { A, B }\nenum F { A, B, C }\n" ++
    "fn f(e: E): Int := match e { E::B => 1, E::A => 0 }")
  let wrongOwner := "mod m\nenum E { A, B }\nenum F { A, B }\n" ++
    "fn f(e: E): Int := match e { E::A => 0, F::B => 1 }"
  let .error (.typing ownerDiagnostic) := checkWalkingSource ⟨47⟩ wrongOwner
    | throw (IO.userError "wrong-owner same-count match passed")
  require (ownerDiagnostic.code == some "F0304" &&
    ownerDiagnostic.headline == "type mismatch: expected `m::E`, found `m::F`") "wrong-owner typing facts"
  for arms in ["_ => 0", "e => 0"] do
    let source := "mod m\nenum E { A, B }\nenum F { A, B }\n" ++
      "fn f(e: E): Int := match e { " ++ arms ++ " }"
    require (!(checkWalkingSource ⟨47⟩ source).isOk) "wrong owner/unsupported pattern accepted"
  -- Call and binary expressions share their first token with a child; the
  -- scrutinee lookup must select the complete occurrence, not that child.
  discard <| accepts ("mod m\nenum E { A, B }\nfn id(e: E): E := e\n" ++
    "fn f(e: E): Int := match id(e) { E::A => 0, E::B => 1 }")
  let t ← accepts (pre ++ whole)
  require ((callEdges t).toOption == some #[]) "constructor/local references became calls"

private def cycleCases : IO Unit := do
  let self := "mod m\nfn f(x: Int): Int := f(x)"
  match ← fails self with
  | .termination span group .unguarded => require (group == #[key "f"] && span.file == ⟨47⟩ &&
      span.start == 27 && span.stop == 28) "self-recursion concrete group/span"
  | _ => throw (IO.userError "wrong self failure")
  let mutualSource := "mod m\nfn f(x: Int): Int := g(x)\nfn g(x: Int): Int := f(x)"
  match ← fails mutualSource with
  | .termination span group .unguarded => require (group == #[key "f", key "g"] &&
      span.start == 53 && span.stop == 54) "mutual concrete group/span"
  | _ => throw (IO.userError "wrong mutual failure")
  match ← fails ("mod m\nfn f(x: Int): Int := g(x)\nfn g(x: Int): Int := h(x)\n" ++
      "fn h(x: Int): Int := f(x)") with
  | .termination _ group .unguarded =>
    require (group == #[key "f", key "g", key "h"]) "long recursive group"
  | _ => throw (IO.userError "wrong long failure")
  -- A group is in declaration order whichever function the cycle was found from,
  -- and a function that only calls into it is not of it.
  match ← fails ("mod m\nfn top(x: Int): Int := g(x)\nfn g(x: Int): Int := f(x)\n" ++
      "fn f(x: Int): Int := g(x)") with
  | .termination _ group .unguarded => require (group == #[key "g", key "f"]) "group members"
  | _ => throw (IO.userError "wrong group failure")
  -- No source form calls a function of no parameters, so `noParameters` is tested on
  -- the deciding functions directly (`FrenHirToThirTests.Termination`).
  -- An argument that is the parameter itself, or a let of it, has the size `same`.
  for expr in ["f(y, x)", "let z := x in f(z, y)", "f((x), (y))", "f(x + 1, y)"] do
    match ← fails ("mod m\nfn f(x: Int, y: Int): Int := " ++ expr) with
    | .termination _ group .unguarded => require (group == #[key "f"]) "unguarded argument"
    | _ => throw (IO.userError s!"wrong failure: {expr}")
  for expr in ["if true then x else f(x)", "let y := f(x) in y", "(f(x))",
      "match E::A { E::A => x, E::B => f(x) }", "g(f(x))"] do
    match ← fails ("mod m\nenum E { A, B }\nfn g(x: Int): Int := x\nfn f(x: Int): Int := " ++ expr) with
    | .termination _ group .unguarded => require (group == #[key "f"]) "nested call's group"
    | _ => throw (IO.userError s!"wrong nested failure: {expr}")
  -- `cycleFrom` still gives the closed path, though validation reports the group.
  for (source, closed) in [(self, #[key "f", key "f"]), (mutualSource, #[key "f", key "g", key "f"])] do
    let t ← typed source
    let .ok edges := callEdges t | throw (IO.userError "cycle metadata")
    match cycleFrom t edges (key "f") with
    | some (.cycle span path) => require (path == closed && span.file == ⟨47⟩) "closed cycle path"
    | _ => throw (IO.userError "no cycle found")
  -- Every declaration is checked, including a disconnected unused cycle.
  discard <| fails "mod m\nfn main(x: Int): Int := x\nfn unused(x: Int): Int := unused(x)"
  let diamond := "mod m\nfn f(x: Int): Int := g(x) + h(x)\n" ++
    "fn g(x: Int): Int := k(x)\nfn h(x: Int): Int := k(x)\nfn k(x: Int): Int := x"
  discard <| fails "mod m\nfn f(f: Int): Int := m::f(f)"
  require (!(checkWalkingSource ⟨47⟩ "mod m\nfn f(x: Int): Int := (f)(x)").isOk)
    "unsupported parenthesized callee passed source grammar"
  let t ← accepts diamond
  let .ok edges := callEdges t | throw (IO.userError "diamond metadata")
  require (edges.map (fun e => (e.caller, e.callee)) ==
    #[(key "f", key "g"), (key "f", key "h"), (key "g", key "k"), (key "h", key "k")])
    "actual forward/diamond edge identities"
  for source in ["mod m\nfn f(f: Int): Int := f",
    "mod m\nfn f(x: Int): Int := let f := x in f",
    "mod m\nfn f(x: Int): Int := let g := x in m::g(g)\nfn g(x: Int): Int := x"] do
    discard <| accepts source
  require (!(checkWalkingSource ⟨47⟩ "mod m\nfn f(f: Int): Int := f(f)").isOk)
    "local shadowing became a callable edge"
  -- The actual resolver supports one module per input, no cross-module imports.
  -- Equal display names in separate modules must retain separate canonical IDs.
  for modName in ["m", "n"] do
    let t ← accepts (s!"mod {modName}\nfn f(x: Int): Int := g(x)\nfn g(x: Int): Int := x")
    let .ok edges := callEdges t | throw (IO.userError "module graph")
    let root := FrenBase.ItemId.root.named modName
    require (edges.map (·.callee) == #[root.named "g"]) "module nominal call identity"

/-- The written calls that validation reads of the body of `f`, by the production
`functionOf`, compared with a tree written by hand. -/
private def writtenCase (body : String) (expected : Termination.Calls FrenBase.ItemId) : IO Unit := do
  let t ← typed ("mod m\nenum E { A, B }\nfn g(x: Int): Int := x\n" ++
    "fn h(x: Int, y: Int): Int := x\nfn f(x: Int, y: Int): Int := " ++ body)
  let some typedBody := t.bodies.find? fun b => b.member.isNone && b.owner == key "f"
    | throw (IO.userError "no body of f")
  let span := (anchor typedBody.expression t.resolved.scope.name).span
  let .ok function := functionOf t span (key "f") | throw (IO.userError s!"no written calls: {body}")
  require (function.item == key "f" && function.parameters.length == 2 && !function.unchecked)
    "function read for the check"
  require (s!"{repr function.body}" == s!"{repr expected}")
    s!"written calls of {body}: {repr function.body}"

/-- Each form's written calls, with the level of each argument and let value that is a
local: `x` is at level 0, `y` at 1, and a let's local at the next level. -/
private def extractionCases : IO Unit := do
  let empty : Termination.Calls FrenBase.ItemId := .leaf
  -- A call has the calls of its arguments, folded from `leaf`, and then itself.
  let one := fun (argument call : Termination.Calls FrenBase.ItemId) => .both (.both empty argument) call
  let gx := one empty (.call (key "g") [some 0])
  writtenCase "x" empty
  writtenCase "g(y)" (one empty (.call (key "g") [some 1]))
  writtenCase "(g(x))" gx
  writtenCase "g((x))" gx
  writtenCase "g(x) + y" (.both gx empty)
  -- An argument that is not a local has no level; its own calls come first.
  writtenCase "h(g(x), y + 1)"
    (.both (.both (.both empty gx) (.both empty empty)) (.call (key "h") [none, none]))
  writtenCase "g(f(x, y))"
    (.both (.both empty (.both (.both (.both empty empty) empty) (.call (key "f") [some 0, some 1])))
      (.call (key "g") [none]))
  writtenCase "let z := y in g(z)"
    (.both empty (.bind (some 1) (one empty (.call (key "g") [some 2]))))
  -- A let of a call has no level, and a nested let's local is one level higher.
  writtenCase "let z := g(x) in let w := z in h(w, (x))"
    (.both gx (.bind none (.both empty (.bind (some 2)
      (.both (.both (.both empty empty) empty) (.call (key "h") [some 3, some 0]))))))
  -- A let with no call is recorded all the same.
  writtenCase "let z := x in z" (.both empty (.bind (some 0) empty))
  writtenCase "if true then g(x) else y" (.both empty (.both gx empty))
  writtenCase "match E::A { E::A => x, E::B => g(x) }" (.both empty (.both (.both empty empty) gx))
  -- A unary operator has its operand's calls, and a condition and a scrutinee theirs.
  writtenCase "-g(x)" gx
  let test : Termination.Calls FrenBase.ItemId := .both gx empty
  writtenCase "if g(x) = 0 then x else y" (.both test (.both empty empty))
  writtenCase "match (if g(x) = 0 then E::A else E::B) { E::A => x, E::B => y }"
    (.both (.both test (.both empty empty)) (.both (.both empty empty) empty))

private def boundaryCases : IO Unit := do
  let source ← IO.FS.readFile "test/FrenResolve/s1.fren"
  let t ← accepts source
  require (t.bodies.size == 6 && t.bodies.filterMap (fun b => b.member.map (·.label.text)) ==
    #["back", "bounded", "at_most", "never_red"] &&
    (t.bodies[5]?).map (·.type) == some .bool) "S1 false goal lost or judged"
  let r := t.resolved
  for edited in [{r with references := #[]}, {r with references := r.references.reverse},
      {r with scope := {r.scope with items := #[]}},
      {r with document := {r.document with source := source ++ "junk"}},
    {r with references := r.references ++ r.references},
    {r with references := r.references.map fun ref =>
      if ref.role == .pattern then {ref with target := .item (key "invented")} else ref}] do
    let .error (.typing d) := checkWalking edited | throw (IO.userError "forged input passed walking")
    require (d.headline == "walking type error: incoherent resolved input") "admission ordering"
  for (file, code, start, stop) in [("unknown", "F0201", 38, 39), ("enum-arithmetic", "F0304", 71, 72)] do
    let text ← IO.FS.readFile s!"test/FrenTypecheck/{file}.fren"
    let .error (.typing d) := checkWalkingSource ⟨47⟩ text | throw (IO.userError "old failure accepted")
    require (d.code == some code && d.span.start == start && d.span.stop == stop) "old diagnostic changed"

-- Native assertions use concrete independently written identities/spans/facts.
def runWalking : IO Unit := do
  coverageCases
  cycleCases
  extractionCases
  runTermination
  boundaryCases
  IO.println "walking static: coverage, actual call cycles, S1 goals and producer boundary passed"

end FrenHirToThirTests
