module

meta import FrenParseTests.Adapter
meta import FrenProp

meta section
namespace FrenParseTests
open FrenAst FrenParse Plausible
open scoped Plausible.Decorations

private def shape (source : String) : Option String := do
  let doc ← (parseExpression ⟨1⟩ source).toOption
  let .expression body := doc.root | none
  return describe body

private def rejectedAt (entry : Entry) (source : String) (start stop : Nat) : Bool :=
  match parse entry ⟨1⟩ source with
  | .ok _ => false
  | .error failure => failure.diagnostic.span.file == ⟨1⟩ &&
      failure.diagnostic.span.start == start && failure.diagnostic.span.stop == stop &&
      failure.emit == source

-- Independent grammar oracles: token ownership and roundtripping alone cannot
-- distinguish the old, consistently wrong module/grouping/token-boundary trees.
#eval show IO Unit from do
  for gap in ["\n", "\r\n", " -- é😀\n", " -- é😀\r\n\t", "\n-- comment\n"] do
    for body in ["1", "(\n1)", "if true then 1 else 2", "let x := 1 in x"] do
      let source := "fn f(x: Int): Int := " ++ body ++ gap ++ "mod second\nfn g(x: Int): Int := 2"
      for entry in [Entry.file, Entry.context] do
        let .ok doc := parse entry ⟨1⟩ source | throw <| IO.userError "module boundary parse"
        let .declarations decls := doc.root | throw <| IO.userError "declarations root"
        unless decls.size == 3 && coherent doc && doc.emit == source do
          throw <| IO.userError s!"module swallowed after {repr body}, gap {repr gap}"
        let some moduleSyntax := decls[1]? | throw <| IO.userError "missing module"
        let Decl.moduleDecl none _ path := moduleSyntax | throw <| IO.userError "module order"
        unless path.head.text == "second" do throw <| IO.userError "module path"
      let expression := "1" ++ gap ++ "mod second"
      unless rejectedAt .expression expression (1 + gap.utf8ByteSize) (4 + gap.utf8ByteSize) do
        throw <| IO.userError "expression entry swallowed declaration"
  for source in ["x mod 2", "x mod\n2", "(x\n) mod 2", "x\rmod 2"] do
    unless shape source == some (if source.startsWith "(" then "(mod (paren x) 2)" else "(mod x 2)") do
      throw <| IO.userError s!"valid remainder {repr source}"
  let comparisons := ["=", "!=", "<", "<=", ">", ">="]
  for first in comparisons do
    for second in comparisons do
      let source := s!"a {first} b {second} c"
      let offset := (s!"a {first} b ").utf8ByteSize
      for entry in [Entry.expression, Entry.file, Entry.context] do
        let lead := if entry == .expression then "" else "fn f(x: Int): Bool := "
        unless rejectedAt entry (lead ++ source) (lead.utf8ByteSize + offset)
            (lead.utf8ByteSize + offset + second.utf8ByteSize) do
          throw <| IO.userError s!"unsupported comparison chain {source}"
      for source in [s!"(a {first} b) {second} c", s!"a {first} (b {second} c)"] do
        let .ok doc := parseExpression ⟨1⟩ source | throw <| IO.userError s!"explicit binary {source}"
        unless coherent doc && doc.emit == source do throw <| IO.userError "parenthesized binary coherence"
  unless rejectedAt .expression "a iff b iff c" 8 11 &&
      shape "(a iff b) iff c" == some "(iff (paren (iff a b)) c)" &&
      shape "a iff (b iff c)" == some "(iff a (paren (iff b c)))" do
    throw <| IO.userError "iff nonassociativity"
  for (source, offset) in [("x<-1", 1), ("-- é😀\r\nx<-1", 12)] do
    unless rejectedAt .expression source offset (offset + 2) do
      throw <| IO.userError "unsupported <- token anchoring"
  unless shape "x < -1" == some "(< x (- 1))" do throw <| IO.userError "spaced comparison/negation"
  IO.println "grammar regressions: 40 file/context module boundaries, 20 expression boundaries; 108 rejected comparison chains, 72 parenthesized positives; iff and <- controls passed"

private def check (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations)
    [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' {numInst := 500, maxSize := 40, randomSeed := some 100504}
  IO.println s!"grammar boundaries: 500 generated positive/negative pairs, zero discarded premises: {result}"
  match result with
  | .success _ => pure ()
  | _ => throw <| IO.userError "grammar boundary property"

#eval check <| ∀ (n : Nat) (crlf : Bool),
  let x := toString n
  let gap := if crlf then " -- é😀\r\n" else " -- é😀\n"
  let whole := s!"fn f(x: Int): Int := {x}" ++ gap ++ "mod second"
  (match parseFile ⟨1⟩ whole with
   | .ok doc => coherent doc && doc.emit == whole &&
       (match doc.root with | .declarations ds => ds.size == 2 | _ => false)
   | _ => false) = true ∧
  shape (x ++ " < -1") = some (s!"(< {n} (- 1))") ∧
  rejectedAt .expression (x ++ "<-1") x.utf8ByteSize (x.utf8ByteSize + 2) = true ∧
  rejectedAt .expression (x ++ " = 1 = 2") (x.utf8ByteSize + 5) (x.utf8ByteSize + 6) = true

end FrenParseTests

namespace FrenParseTests
open FrenAst FrenParse

-- A low-precedence prefix is not an implicit parenthesis. Each accepted
-- parenthesized counterpart remains syntax even when it is ill-typed.
#eval show IO Unit from do
  for operator in ["+", "-", "*", "div", "mod", "=", "!=", "<", "<=", ">", ">="] do
    let start := ("a " ++ operator ++ " ").utf8ByteSize
    let source := "a " ++ operator ++ " not b = c"
    unless rejectedAt .expression source start (start + 3) do
      throw <| IO.userError s!"bare not operand: {source}"
    let .ok doc := parseExpression ⟨1⟩ ("a " ++ operator ++ " (not b = c)")
      | throw <| IO.userError "parenthesized not operand"
    unless coherent doc do throw <| IO.userError "parenthesized not tree"
  for operator in ["+", "-", "*", "div", "mod", "=", "!=", "<", "<=", ">", ">=", "and", "or", "iff"] do
    let start := ("a " ++ operator ++ " ").utf8ByteSize
    let source := "a " ++ operator ++ " let x := true in x"
    for entry in [Entry.expression, Entry.file, Entry.context] do
      let lead := if entry == .expression then "" else "fn f(x: Int): Bool := "
      unless rejectedAt entry (lead ++ source) (lead.utf8ByteSize + start)
          (lead.utf8ByteSize + start + 3) do
        throw <| IO.userError s!"bare let operand: {source}"
    let .ok doc := parseExpression ⟨1⟩ ("a " ++ operator ++ " (let x := true in x)")
      | throw <| IO.userError "parenthesized let operand"
    unless coherent doc do throw <| IO.userError "parenthesized let tree"
  for (source, start, stop) in [("-not b", 1, 4), ("-let x := 1 in x", 1, 4),
      ("not let x := true in x", 4, 7), ("a < not b < c", 4, 7)] do
    unless rejectedAt .expression source start stop do throw <| IO.userError "unary prefix operand"
  for source in ["not not b", "-(not b)", "not (let x := true in x)",
      "a + if b then c else d", "match l { E::A => 1 } + 2", "y + 1", "l + 1"] do
    let .ok doc := parseExpression ⟨1⟩ source | throw <| IO.userError s!"valid prefix/atom {source}"
    unless coherent doc && doc.emit == source do throw <| IO.userError "valid operand tree"
  for word in ["proc", "forall", "exists", "use", "struct", "where", "with"] do
    unless rejectedAt .expression word 0 word.utf8ByteSize do
      throw <| IO.userError s!"unsupported reserved word became a name: {word}"
  for source in ["fn f(assume: Int): Int := assume", "fn assume(x: Int): Int := 1",
      "enum E { Int, Bool, assume }"] do
    let .ok doc := parseFile ⟨1⟩ source | throw <| IO.userError "contextual name grammar"
    unless coherent doc && doc.emit == source do throw <| IO.userError "contextual name tree"
  -- `true`, `false` and `not` are keywords: no declaration, binder, label,
  -- path segment or match pattern names one. Each rejection is anchored at
  -- the keyword itself.
  for word in ["true", "false", "not"] do
    for (entry, before, after) in [(Entry.file, "fn f(", ": Int): Int := 1"),
        (.file, "fn ", "(x: Int): Int := 1"),
        (.file, "enum E { A, ", " }"), (.file, "mod ", ""), (.file, "mod a::", ""),
        (.file, "expect ", "() {}"), (.file, "expect e() { expect ", ": x }"),
        (.file, "expect e(", ": Int) {}"), (.file, "fn f(x: Int): ", " := 1"),
        (.expression, "let ", " := 1 in 1"), (.expression, "E::", ""),
        (.expression, "match x { E::", " => 1 }"), (.expression, "match x { ", "::A => 1 }")] do
      let source := before ++ word ++ after
      unless rejectedAt entry source before.utf8ByteSize (before.utf8ByteSize + word.utf8ByteSize) do
        throw <| IO.userError s!"keyword became a name: {source}"
    -- With `?` the word is an identifier, as `if?` is.
    let .ok _ := parseFile ⟨1⟩ s!"fn f({word}?): Bool := {word}?" | throw <| IO.userError "question word"
  IO.println "prefix operand restrictions, explicit parentheses, atoms, reserved words and keywords as names passed"

end FrenParseTests

namespace FrenParseTests
open FrenAst FrenParse

private def typeName : Ty → String
  | .bool _ => "builtin Bool"
  | .int _ => "builtin Int"
  | .named p => "path " ++ "".intercalate (p.tokens.map (·.text))

#eval show IO Unit from do
  for entry in [Entry.file, Entry.context] do
    for ty in ["Bool", "Int", "E", "Int::T", "Bool::T", "A::Int", "Bool::Int::T"] do
      let source := s!"fn f(b?: {ty}): {ty} := b?"
      let .ok doc := parse entry ⟨1⟩ source | throw <| IO.userError s!"explicit suffix annotation: {source}"
      let .declarations decls := doc.root | throw <| IO.userError "declaration root"
      let some decl := decls[0]? | throw <| IO.userError "function missing"
      let .function _ _ _ params _ result _ _ := decl | throw <| IO.userError "function form"
      let some param := params.values[0]? | throw <| IO.userError "parameter missing"
      let some (_, annotation) := param.annotation | throw <| IO.userError "written annotation discarded"
      let expected := if ty == "Int" || ty == "Bool" then "builtin " ++ ty else "path " ++ ty
      unless typeName annotation == expected && typeName result == expected &&
          coherent doc && doc.emit == source do throw <| IO.userError "type path classification"
      let source := s!"expect e(b?: {ty}) \{ expect c: b? }"
      let .ok doc := parse entry ⟨1⟩ source | throw <| IO.userError "expectation annotation"
      let .declarations decls := doc.root | throw <| IO.userError "expectation root"
      let some decl := decls[0]? | throw <| IO.userError "expectation missing"
      let .expectation _ _ params _ _ _ := decl | throw <| IO.userError "expectation form"
      let some param := params.values[0]? | throw <| IO.userError "expectation parameter"
      let some (_, annotation) := param.annotation | throw <| IO.userError "expectation annotation lost"
      unless typeName annotation == expected && coherent doc && doc.emit == source do
        throw <| IO.userError "expectation type path classification"
    for source in ["fn f(b?:", "expect e(b?:", "fn f(x: Int::", "fn f(x: Bool::",
        "fn f(x: Int): Int::", "fn f(x: Int): Bool::", "expect e(x: Int::", "expect e(x: Bool::"] do
      unless rejectedAt entry source source.utf8ByteSize source.utf8ByteSize do
        throw <| IO.userError s!"type truncation: {source}"
    for source in ["fn f(b?): Bool := b?", "fn f(b: Bool): Bool := b?",
        "expect e(b?) { expect c: b? }", "expect e(b: Bool) { expect c: b? }"] do
      let .ok doc := parse entry ⟨1⟩ source | throw <| IO.userError "existing parameter form"
      unless coherent doc && doc.emit == source do throw <| IO.userError "existing parameter tree"
  IO.println "type grammar: 28 explicit suffix/path positives, 16 EOF truncations, 8 existing parameter positives passed"

end FrenParseTests

namespace FrenParseTests
open FrenAst FrenParse

private def requiredExpression (source : String) : IO Unit := do
  let .ok doc := parseExpression ⟨1⟩ source | throw <| IO.userError s!"required expression: {source}"
  unless coherent doc && doc.emit == source do throw <| IO.userError "required expression tree"

private def forbiddenExpression (source : String) : IO Unit := do
  for entry in [Entry.expression, Entry.file, Entry.context] do
    let lead := if entry == .expression then "" else "fn f(x: Int): Int := "
    let .error failure := parse entry ⟨1⟩ (lead ++ source)
      | throw <| IO.userError s!"unsupported expression category: {source}"
    unless failure.emit == lead ++ source do throw <| IO.userError "category failure ownership"

#eval show IO Unit from do
  -- Atom restriction: infix, either unary prefix and let cannot be a bare
  -- scrutinee, while parentheses and actual atoms preserve their written tree.
  for scrutinee in ["l + 1", "l = r", "-l", "not l", "let x := l in x"] do
    forbiddenExpression ("match " ++ scrutinee ++ " { E::A => 1 }")
    requiredExpression ("match (" ++ scrutinee ++ ") { E::A => 1 }")
  for scrutinee in ["l", "unknown(l)", "1", "true", "if b then l else r",
      "match l { E::A => l }"] do
    requiredExpression ("match " ++ scrutinee ++ " { E::A => 1 }")
  for source in ["let x := let y := 1 in y in x", "match l { E::A => let x := 1 in x }"] do
    forbiddenExpression source
  for source in ["let x := (let y := 1 in y) in x", "match l { E::A => (let x := 1 in x) }",
      "let x := 1 in let y := x in y", "let x := if b then 1 else 2 in x",
      "f(let x := 1 in x)", "if b then let x := 1 in x else 2"] do
    requiredExpression source
  for gap in [" ", "\t", "\n", "\r\n", " -- é😀\n", " -- é😀\r\n"] do
    forbiddenExpression ("f" ++ gap ++ "(x)")
    forbiddenExpression ("A::f" ++ gap ++ "(x)")
    for entry in [Entry.file, Entry.context] do
      for source in ["fn f" ++ gap ++ "(x: Int): Int := x",
          "expect e" ++ gap ++ "(x: Int) { expect c: true }"] do
        let .error failure := parse entry ⟨1⟩ source | throw <| IO.userError "spaced parameter opener"
        unless failure.emit == source do throw <| IO.userError "opener failure ownership"
  for source in ["1(x)", "true(x)", "(f)(x)", "f(x)(y)",
      "(if b then f else g)(x)", "match l { E::A => f }(x)"] do
    forbiddenExpression source
  for source in ["unknown(x)", "A::unknown(x)", "x(y)", "f(g(x), h(y))",
      "1 + (x)", "1 +\n(x)", "f((x))"] do
    requiredExpression source
  -- Independent source byte anchoring for separated and generic openers.
  unless rejectedAt .expression "f -- é😀\r\n(x)" 13 14 &&
      rejectedAt .expression "1(x)" 1 2 do throw <| IO.userError "call opener byte anchors"
  IO.println "atom scrutinees, iff definition/arm categories, adjacent named calls and parameter openers passed"

end FrenParseTests

namespace FrenParseTests
open FrenAst FrenParse

#eval show IO Unit from do
  for source in ["f()", "f( -- é😀\n)", "f(,)", "f(x,,)", "f(x y)"] do
    forbiddenExpression source
  for source in ["f(x,)", "f(x, y,)", "f(x, -- comment\r\n)"] do
    requiredExpression source
  for entry in [Entry.file, Entry.context] do
    for source in ["fn f(): Int := 1", "fn f( -- comment\n): Int := 1",
        "fn f(,): Int := 1", "fn f(x: Int,,): Int := x",
        "enum E {}", "enum E { -- é😀\n}", "enum E { , }", "expect e(,) {}",
        "fn f(l: E): Int := match l { , }"] do
      let .error failure := parse entry ⟨1⟩ source | throw <| IO.userError s!"required list element: {source}"
      unless failure.emit == source do throw <| IO.userError "list failure ownership"
    for source in ["expect e() {}", "expect e(x: Int,) { expect c: true }",
        "expect e(x: Int, -- é😀\n) {}", "enum E { A, }", "enum E { A, B, }",
        "fn f(l: E): Int := match l {}", "fn f(l: E): Int := match l { E::A => 1, }",
        "fn f(x: Int): Int := unknown(x)", "fn f(x: Int, y: Int): Int := x(y)",
        "fn f(x: Int,): Int := x", "fn f(a: Int, b: Int,): Int := a",
        "fn f(x: Int, -- comment\r\n): Int := x", "fn f(x: Int): Int := f(1, 2,)",
        "fn f(l: E): Int := match l { E::A => 1, E::B => 2, }"] do
      let .ok doc := parse entry ⟨1⟩ source | throw <| IO.userError s!"valid distinct list policy: {source}"
      unless coherent doc && doc.emit == source do throw <| IO.userError "valid list ownership"
  for source in ["f(x)", "f(x, y)", "f(g(x), h(y))"] do requiredExpression source
  IO.println "list policies: a trailing comma after any item; nonempty functions, applications and enums; empty expectations and matches passed"

end FrenParseTests
