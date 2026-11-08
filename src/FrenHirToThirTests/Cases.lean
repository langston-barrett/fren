module

public import FrenHirToThirTests.Support

public section
namespace FrenHirToThirTests
open FrenAst FrenModule FrenHirToThir FrenExpr

private def s1Checks (source : String) : IO Unit := do
  let t ← typed source
  let m := FrenBase.ItemId.root.named "skeleton"
  let light := m.named "Light"
  require (t.signatures.map (·.id) == #[m.named "next", m.named "wait"] &&
    t.signatures.map (·.result) == #[.enum light, .int]) "S1 signature identities/results"
  require (t.signatures.map (fun s => s.parameters.map (·.type)) ==
    #[#[.enum light], #[.enum light, .int]]) "S1 ordered signature types"
  require (t.bodies.map (·.owner) ==
    #[m.named "next", m.named "wait", m.named "cycles", m.named "waits", m.named "waits", m.named "wrong"])
    "S1 body owner order; no goals dropped"
  require (t.bodies.map (·.type) == #[.enum light, .int, .bool, .bool, .bool, .bool]) "S1 independent root types"
  require (t.bodies.filterMap (fun b => b.member.map fun member => (member.kind, member.label.text)) ==
    #[(.expect, "back"), (.assume, "bounded"), (.expect, "at_most"), (.expect, "never_red")])
    "S1 check kinds/labels including the false goal"
  require (t.bodies.map (fun b => b.occurrences.size) == #[5, 9, 9, 3, 6, 5]) "S1 complete occurrence census"
  let nextBody ← bodyAt t 0
  let backBody ← bodyAt t 2
  let wrongBody ← bodyAt t 5
  let nextNames := nameOccurrences nextBody
  require (nextNames.map (·.type) ==
    #[.value (.enum light), .value (.enum light), .value (.enum light), .value (.enum light)]) "S1 constructor value types"
  let backCalls := backBody.occurrences.filterMap fun o =>
    match o.type with | .callable s => some s.id | _ => none
  require (backCalls == #[m.named "next", m.named "next", m.named "next"]) "S1 call identities"
  let backLocals : Array (Nat × List FrenExpr.Ty) := (nameOccurrences backBody).filterMap fun o => do
    let .name p := o.expression | none
    let ref ← t.resolved.referenceAt p.head.slice
    let .local i := ref.target | none
    return (i, o.context.map Prod.snd)
  require (backLocals == #[(0, [.enum light]), (0, [.enum light])]) "S1 locals exact contexts"
  -- Written independently from the S1 source bytes; full path spans and
  -- callable/value types are distinct even where their anchors coincide.
  let nextSig ← signature t
  let some waitSig := t.signatures[1]? | throw (IO.userError "missing wait signature")
  let observed := t.bodies.flatMap fun b => (nameOccurrences b).filterMap fun o => do
    let .name p := o.expression | none
    let ref ← t.resolved.referenceAt p.head.slice
    let stop := (p.tokens.getLast?).getD p.head
    return (p.head.span.start, stop.span.stop, ref.target, o.type)
  let lightValue := ExpressionType.value (.enum light)
  let intValue := ExpressionType.value .int
  let nextCall := ExpressionType.callable nextSig
  let waitCall := ExpressionType.callable waitSig
  let expected : Array (Nat × Nat × Target × ExpressionType) := #[
    (94, 95, .local 0, lightValue), (116, 128, .item (light.named "Green"), lightValue),
    (150, 162, .item (light.named "Amber"), lightValue), (184, 194, .item (light.named "Red"), lightValue),
    (246, 247, .local 1, lightValue), (268, 272, .local 0, intValue),
    (299, 303, .local 0, intValue), (329, 333, .local 0, intValue),
    (381, 385, .item (m.named "next"), nextCall), (386, 390, .item (m.named "next"), nextCall),
    (391, 395, .item (m.named "next"), nextCall), (396, 397, .local 0, lightValue),
    (403, 404, .local 0, lightValue), (464, 468, .local 0, intValue),
    (496, 500, .item (m.named "wait"), waitCall), (501, 502, .local 1, lightValue),
    (504, 508, .local 0, intValue), (567, 571, .item (m.named "next"), nextCall),
    (572, 573, .local 0, lightValue), (578, 588, .item (light.named "Red"), lightValue)]
  require (observed == expected && t.resolved.references.all (·.written.anchor.span.file == ⟨47⟩))
    "S1 written type/identity/UTF-8 span oracle"
  require (observed != expected.set! 0 (94, 95, .local 1, lightValue) &&
    observed != expected.set! 0 (94, 95, .local 0, intValue) &&
    observed != expected.set! 3 (184, 194, .item ((m.named "Signal").named "Red"), lightValue) &&
    observed != expected.set! 0 (93, 95, .local 0, lightValue)) "wrong slot/type/owner/span expectations survived"
  require (localsRetained t) "S1 local retention"
  require (wrongBody.type != .int && backCalls != #[m.named "wait", m.named "next", m.named "next"])
    "wrong S1 type/target oracle survived"
  IO.println "S1: typed next:Light, wait:Int; retained four Bool check bodies including never_red; six total bodies"

def runCases : IO Unit := do
  s1Checks (← IO.FS.readFile "test/FrenResolve/s1.fren")
  let source ← IO.FS.readFile "test/FrenTypecheck/enum-arithmetic.fren"
  let d ← rejected source
  let some expectedSpan := FrenSource.Span.checked ⟨47⟩ 71 72 source.utf8ByteSize
    | throw (IO.userError "invalid pinned span")
  require (d == ⟨some "F0304", "type mismatch: expected `Int`, found `bad::Light`",
    expectedSpan⟩) "pinned F0304 data/span"
  IO.println s!"actual Fren2 F0304: {d.headline}; file=47, UTF-8 bytes [71,72)"
  let commentPrefix := "-- é😀\r\n"
  let u ← rejected (commentPrefix ++ source)
  require (u.span.start == 82 && u.span.stop == 83 && u.span.file == ⟨47⟩ &&
    u.headline == d.headline && u.code == d.code) "UTF-8 diagnostic operand span"
  let unknown ← IO.FS.readFile "test/FrenTypecheck/unknown.fren"
  let .error unknownDiag := checkSource ⟨47⟩ unknown | throw (IO.userError "unknown y accepted")
  require (unknownDiag.code == some "F0201" && unknownDiag.headline == "cannot find `y` in this scope") "unknown y must remain resolver error"

  let prelude := "mod m\nenum Light { Red, Green }\nenum Signal { Red, Green }\n"
  for body in ["if true then 1 else 2", "let x := 2 in x", "(1)", "-1 * 2 div 0 mod 0",
    "match Light::Red { Light::Red => 1 }", "match Light::Red { Light::Red => 1, Light::Red => 2 }"] do
    let t ← typed (prelude ++ "fn f(x: Int): Int := " ++ body)
    require ((t.bodies[0]?).map (·.type) == some .int) "valid expression root type"
  -- Type correctness deliberately admits partial/repeated matches and recursion.
  for decl in ["fn f(x: Int): Int := f(x)",
    "fn f(x: Int): Int := g(x)\nfn g(x: Int): Int := f(x)",
    "expect wrong() { expect false_claim: false }"] do discard <| typed (prelude ++ decl)

  for body in ["if 1 then 2 else 3", "if true then 1 else false",
    "if false then false else 1", "if true then 1 else (false + 1)",
    "let b? := 1 in b?", "match Light::Red {}", "match 1 { Light::Red => 1 }",
    "match Light::Red { Signal::Red => 1 }", "match Light::Red { Light::Red => 1, Light::Green => false }",
    "match Light::Red { Light::Red => 1, Light::Red => false }",
    "Light::Red = Signal::Red", "Light", "m", "g", "e",
    "x(1)", "Light(1)", "m(1)", "Light::Red(1)", "e(1)",
    "g(true)", "g(1, 2)", "h(1)", "h(1, 2, 3)", "h(true, 1)"] do
    discard <| rejected (prelude ++ "fn g(x: Int): Int := x\nfn h(x: Int, b?): Int := x\nexpect e() {}\nfn f(x: Int): Int := " ++ body)
  for decl in ["fn f(b?: Int): Int := b?", "fn f(x: Int): Bool := x",
    "expect e(x: Int) { assume q: x }", "expect e(x: Int) { expect q: x }"] do
    discard <| rejected (prelude ++ decl)

  let calls ← typed (prelude ++
    "fn f(x: Int): Light := g(true, x)\nfn g(b?: Bool, x: Int): Light := if b? then Light::Red else Light::Green")
  require (calls.signatures.map (·.result) == #[.enum (key "Light"), .enum (key "Light")]) "forward calls and nominal results"
  let shadow ← typed (prelude ++
    "fn f(x: Int, b?: Bool): Int := (let x := not b? in if x then (let x := 1 in x) else 2) + x")
  let names := nameOccurrences (← bodyAt shadow 0)
  require (names.map (·.type) == #[.value .bool, .value .bool, .value .int, .value .int]) "nearest shadow/sibling types"
  require (names.map (fun n => n.context.map Prod.snd) ==
    #[[.bool, .int], [.bool, .bool, .int], [.int, .bool, .bool, .int], [.bool, .int]]) "nearest shadow/sibling typed contexts"
  require (localsRetained shadow) "shadow local index/type law"
  let annotationScope ← typed "mod m\nenum Light { Red }\nfn f(Light: Int, l: Light): Light := l"
  let asig ← signature annotationScope
  require (asig.parameters.map (·.type) == #[.int, .enum (key "Light")] &&
    asig.result == .enum (key "Light") && annotationScope.resolved.references.all (fun r =>
      r.role != .annotation || r.context.isEmpty)) "annotations must ignore local parameter names"
  let valueBeforeBinder ← typed "mod m\nfn f(x: Int): Bool := let x := x = 1 in x"
  let uses := nameOccurrences (← bodyAt valueBeforeBinder 0)
  require (uses.map (·.type) == #[.value .int, .value .bool] &&
    uses.map (fun o => o.context.map Prod.snd) == #[[.int], [.bool, .int]])
    "let value/body old and new slot types"
  let explicit ← typed "mod m\nfn f(b?: Bool): Bool := let x? := b? in x?"
  let implicit ← typed "mod m\nfn f(b?): Bool := b?"
  require ((← parameter (← signature explicit)).written.annotation.isSome &&
    (← parameter (← signature implicit)).written.annotation.isNone) "annotation provenance lost"
  let lets ← typed "mod m\nfn f(x: Int, y: Bool): Int := let x := y in if x then 1 else (let z := 2 in z)"
  require (localsRetained lets) "let value typed before binder extension"
  -- Collection and resolution remain earlier boundaries, not typed holes.
  for (src, code) in [("fn f(x: Int, x: Int): Int := x", "F0213"),
    ("enum E { A }\nenum E { B }", "F0206"),
    ("fn f(x: Int): Int := (let y := x in y) + y", "F0201"),
    ("fn f(x: Int): Int := let y := y in x", "F0201")] do
    let .error err := checkSource ⟨47⟩ ("mod m\n" ++ src) | throw (IO.userError "earlier-stage invalid source accepted")
    require (err.code == some code) "earlier-stage error category changed"
  IO.println "typing cases: calls/annotations/scopes/all branches/patterns/empty match/diagnostics/stage boundaries passed"

end FrenHirToThirTests
