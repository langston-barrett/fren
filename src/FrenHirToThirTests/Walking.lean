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
    discard <| fails ("mod m\nenum E { A, B }\nfn g(x: Int): Int := x\nfn f(x: Int): Int := " ++ expr)
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
  runTermination
  boundaryCases
  IO.println "walking static: coverage, actual call cycles, S1 goals and producer boundary passed"

end FrenHirToThirTests
