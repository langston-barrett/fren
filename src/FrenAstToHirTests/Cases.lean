module

public import FrenAstToHirTests.Support

public section
namespace FrenAstToHirTests
open FrenAst FrenModule FrenAstToHir FrenBase

private def moduleText := "pub mod walking\n"
private def enumLight := "enum Light { Red, Green }\n"
private def item (names : List String) : Target :=
  .item (names.foldl ItemId.named .root)

/-- Native acceptance tests: each source goes through the production parser
and resolver, with independently written targets and failure expectations. -/
def runCases : IO Unit := do
  let source ← IO.FS.readFile "test/FrenResolve/s1.fren"
  let doc ← parsed source
  let result ← resolved source
  require (audit doc result) "S1 occurrence/storage/span audit"
  let expected ← IO.FS.readFile "test/FrenResolve/s1.refs"
  let actual := "\n".intercalate (result.references.toList.map describe) ++ "\n"
  require (actual == expected) s!"S1 expected references/spans differ:\n{actual}"
  require (result.scope.items.toList.map (·.id.render) ==
    ["skeleton.Light", "skeleton.Light.Red", "skeleton.Light.Amber", "skeleton.Light.Green",
      "skeleton.next", "skeleton.wait", "skeleton.cycles", "skeleton.waits", "skeleton.wrong"])
    "complete ordered S1 item collection"
  require (result.references.size == 35) "S1 occurrence count"

  let declarations := [
    "fn use_next(l: Light): Light := next(l)\n",
    "expect forward(l: Light) { expect same: next(l) = next(l) }\n",
    "fn next(l: Light): Light := Light::Red\n", enumLight]
  let forward ← resolved (moduleText ++ "".intercalate declarations)
  let reversed ← resolved (moduleText ++ "".intercalate declarations.reverse)
  require (forward.scope.items.toList.all (fun it => reversed.scope.items.any (·.id == it.id)))
    "declaration permutation changed identities"
  require (targets forward == #[item ["walking", "next"], .local 0, item ["walking", "next"],
    .local 0, item ["walking", "next"], .local 0, item ["walking", "Light", "Red"]]) "forward targets"

  let shadow ← resolved (moduleText ++ "fn f(x: Int, y: Int): Int := let x := x + y in x + y")
  require (targets shadow == #[.local 1, .local 0, .local 0, .local 1]) "let value/body wrong-slot control"
  let renamed ← resolved (moduleText ++ "fn f(a: Int, b: Int): Int := let a := a + b in a + b")
  require (targets shadow == targets renamed) "capture-avoiding alpha control"
  let nested ← resolved (moduleText ++ "fn f(x: Int): Int := let x := x in let y := x in x + y")
  require (targets nested == #[.local 0, .local 0, .local 1, .local 0]) "nested nearest control"
  let refs := expressionRefs shadow
  require (refs[0]?.map (·.context.map (·.text)) == some ["y", "x"] &&
    refs[2]?.map (·.context.map (·.text)) == some ["x", "y", "x"]) "contextual slot identities"
  require (refs[2]?.map (·.written.anchor.span) != refs[3]?.map (·.written.anchor.span)) "distinct occurrences"

  let qualified ← resolved (moduleText ++ enumLight ++ "enum Signal { Red }\n" ++
    "fn f(Light: Light): walking::Light := walking::Light::Red\n" ++
    "fn g(x: Int): Light := if true then Light::Red else walking::Light::Red\n" ++
    "fn h(x: Int): Signal := Signal::Red")
  require (targets qualified == #[item ["walking", "Light", "Red"], item ["walking", "Light", "Red"],
    item ["walking", "Light", "Red"], item ["walking", "Signal", "Red"]]) "qualification and annotation scope"
  let implicit ← resolved (moduleText ++ "fn f(b?, c?: Int): Bool := b? and c?")
  require (implicit.references[0]?.map (·.written) ==
    (implicit.document.root.tokens.find? (·.text == "b?")).map Written.implicitBool) "implicit Bool metadata"
  require (implicit.references[1]?.map (·.target) == some .intType) "explicit suffix annotation retained"

  for (text, code, name) in [
    ("fn f(x: Int): Int := y + 1", "F0201", "`y`"),
    ("fn f(x: Int): Int := let fresh := fresh in fresh", "F0201", "`fresh`"),
    ("fn f(x: Int): Int := (let z := 1 in z) + z", "F0201", "`z`"),
    (enumLight ++ "fn f(l: Light): Int := match l { Light::Red => (let z := 1 in z), Light::Green => z }", "F0201", "`z`"),
    (enumLight ++ "fn f(l: Light): Light := Light::Blue", "F0203", "`Blue`"),
    (enumLight ++ "fn f(Light: Int): Light := Light::Red", "F0204", "no members"),
    ("fn Light(x: Int): Int := x\nfn f(x: Int): Int := Light::Red", "F0204", "no members"),
    (enumLight ++ "fn f(walking: Int): Int := walking::Light::Red", "F0204", "no members"),
    (enumLight ++ "fn f(l: Light): Int := Red", "F0201", "`Red`"),
    (enumLight ++ "fn f(x: Int): Light::Red := x", "F0210", "type"),
    ("fn f(x: Int): Int := match x { walking::f => x }", "F0210", "variant"),
    ("fn f(x: Int): Int := if true then (let z := 1 in z) else z", "F0201", "`z`"),
    ("fn f(x: Int): Int := f((let z := x in z), z)", "F0201", "`z`"),
    ("fn f(x: Int): Int := x\nfn g(x: Int): Int := z", "F0201", "`z`"),
    ("expect e(x: Int) { assume label: true expect q: label }", "F0201", "`label`"),
    (enumLight ++ "fn Light(x: Int): Int := x", "F0206", "`Light`"),
    ("fn Light(x: Int): Int := x\n" ++ enumLight, "F0206", "`Light`"),
    ("expect x() {}\nfn x(y: Int): Int := y", "F0206", "`x`"),
    ("fn f(x: Int, x: Int): Int := x", "F0213", "parameter `x`"),
    ("enum Light { Red, Red }", "F0213", "variant `Red`"),
    ("expect e(x: Int) { expect x: true }", "F0213", "label `x`"),
    ("expect e() { assume q: true expect q: true }", "F0213", "label `q`"),
    ("enum Bool { A }", "F0212", "built-in"), ("enum Int { A }", "F0212", "`Int`"),
    ("enum Light { Red, Int }", "F0212", "`Int`"), ("fn Bool(x: Int): Int := x", "F0212", "`Bool`"),
    ("fn f(Int: Bool): Bool := true", "F0212", "`Int`"), ("expect Int() {}", "F0212", "`Int`"),
    ("expect e(Bool: Int) {}", "F0212", "`Bool`"),
    ("expect e(x: Int) { expect Int: true }", "F0212", "`Int`"),
    ("expect e(x: Int) { assume Bool: true }", "F0212", "`Bool`"),
    ("fn f(x: Int): Int := let Int := x in x", "F0212", "`Int`"),
    ("fn f(x: Int): Int := let Bool := x in x", "F0212", "`Bool`"),
    ("expect e(x: Int) { expect q: let Int := x in true }", "F0212", "`Int`"),
    ("fn f(x: Int): Int := x + (let y := 1 in let Bool := y in y)", "F0212", "`Bool`") ] do
    discard <| failure (moduleText ++ text) code name
  -- `Bool` and `Int` are reserved type names (`syntax.name.reserved`), for modules too.
  discard <| failure "mod Bool\nfn f(x: Int): Int := x" "F0212" "`Bool`"

  -- Every item-kind pair shares the one module namespace.
  let sameNamed := ["enum repeated { A }", "fn repeated(x: Int): Int := x", "expect repeated() {}"]
  for first in sameNamed do
    for second in sameNamed do
      discard <| failure (moduleText ++ first ++ "\n" ++ second) "F0206" "`repeated`"
  for op in ["+", "-", "*", "div", "%", "=", "!=", "<", "<=", ">", ">=", "and", "or", "iff"] do
    let result ← resolved (moduleText ++ s!"fn f(x: Int, y: Int): Bool := x {op} y")
    require (targets result == #[.local 1, .local 0]) s!"binary traversal {op}"

  -- Readable ItemIds may collide. Production member lookup uses canonical
  -- identity, even for API-created paths outside parser identifier syntax.
  let token := result.scope.name
  let parent := ItemId.root.named "m"
  let flat := parent.named "A.B"
  let nested := (parent.named "A").named "B"
  require (flat.render == nested.render && flat != nested) "display collision fixture"
  let collisionScope : Scope := ⟨parent, token,
    #[⟨flat, {token with text := "A.B"}, .function⟩,
      ⟨nested, {token with text := "B"}, .constructor⟩]⟩
  require ((member collisionScope parent "A.B").map (·.id) == some flat &&
    (member collisionScope (parent.named "A") "B").map (·.id) == some nested)
    "render collision merged canonical identities"
  for ref in result.references do
    require (result.referenceAt ref.written.anchor.slice == some ref) "occurrence lookup"

  let unknownSource := "pub mod bad\npub fn f(x: Int): Int := y + 1"
  let unknown ← failure unknownSource "F0201" "cannot find `y` in this scope"
  require (unknown.span.file == ⟨47⟩ && unknown.span.start == 37 && unknown.span.stop == 38) "precise y span"
  let unicode ← failure ("-- é😀\r\n" ++ unknownSource) "F0201" "`y`"
  require (unicode.span.start == 48 && unicode.span.stop == 49) "UTF-8 byte span"
  let first ← failure (moduleText ++ "fn f(x: Int): Int := y + z") "F0201" "`y`"
  require (first.headline == "cannot find `y` in this scope") "source-order lookup failure"
  let duplicateFirst ← failure (moduleText ++ "fn f(x: Int): Int := missing\nenum E { A }\nenum E { B }") "F0206" "`E`"
  require (duplicateFirst.code == some "F0206") "collection must precede lookup"

  -- Deliberate typing/solver failures resolve. There is no type/evaluation
  -- verdict here: these tests prevent accidental resolution-stage rejection.
  for text in [enumLight ++ "fn f(l: Light): Int := l + 1",
    "fn f(x: Int): Int := x(x, true)", "fn f(x: Int): Int := f(x)",
    "fn f(x: Int): Int := g(x)\nfn g(x: Int): Int := f(x)",
    enumLight ++ "fn f(l: Light): Int := match l {}",
    "expect wrong() { expect false_claim: false }",
    enumLight ++ "fn f(x: Int): Int := Light", "fn f(x: Int): Int := walking",
    "expect e() {}\nfn f(x: Int): Int := e(x)",
    "fn f(b?: Int): Bool := not b?", "fn f(x: Int): Int := -x * 2 div 3 % 2"] do
    let doc ← parsed (moduleText ++ text)
    let result ← resolved (moduleText ++ text)
    require (audit doc result) "later-stage source rejected or corrupted"

  for source in ["", "enum E { A }", "mod a::b", "mod a\nmod b", "fn f(x: Int): Int := x"] do
    let doc ← parsed source
    let .error d := resolve doc | throw (IO.userError "unsupported module shape accepted")
    require (d.code.isNone) "invented unsupported-boundary code"
  let .ok expression := FrenParse.parseExpression ⟨47⟩ "x" | throw (IO.userError "expression parse")
  let .error _ := resolve expression | throw (IO.userError "expression root accepted")
  let doc ← parsed (moduleText ++ "fn f(x: Int): Int := x")
  for changed in [{doc with root := .declarations #[]}, {doc with source := doc.source ++ " junk"},
      {doc with entry := .context}, {doc with tape := #[]}] do
    let .error d := resolve changed | throw (IO.userError "edited/partial AST accepted")
    require (d.code.isNone) "malformed document has language lookup verdict"
  let deep := String.ofList (List.replicate 160 '(') ++ "x" ++ String.ofList (List.replicate 160 ')')
  let result ← resolved (moduleText ++ "fn f(x: Int): Int := " ++ deep)
  require (targets result == #[.local 0]) "syntax-derived traversal depth"
  IO.println "resolver cases: complete S1 targets/spans, forward/shadow/qualification/failure/stage/partial controls passed"

end FrenAstToHirTests
