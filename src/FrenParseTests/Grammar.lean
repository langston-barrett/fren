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
      let source := "fn f(): Int := " ++ body ++ gap ++ "mod second\nfn g(): Int := 2"
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
        let lead := if entry == .expression then "" else "fn f(): Bool := "
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
  let whole := s!"fn f(): Int := {x}" ++ gap ++ "mod second"
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
      let lead := if entry == .expression then "" else "fn f(): Bool := "
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
  for source in ["fn f(assume: Int): Int := assume", "fn assume(): Int := 1",
      "enum E { Int, Bool, not, assume, true, false }"] do
    let .ok doc := parseFile ⟨1⟩ source | throw <| IO.userError "contextual name grammar"
    unless coherent doc && doc.emit == source do throw <| IO.userError "contextual name tree"
  IO.println "prefix operand restrictions, explicit parentheses, atoms, and reserved/contextual names passed"

end FrenParseTests
