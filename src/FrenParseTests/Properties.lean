module

meta import FrenParseTests.Adapter
meta import FrenProp

meta section
namespace FrenParseTests
open FrenAst FrenParse Plausible
open scoped Plausible.Decorations

def accepted (result : Except Failure Document) : Bool :=
  match result with | .ok _ => true | .error _ => false

def generated (n : Nat) (choice : Bool) : String :=
  let v := n % 1000
  let body := if choice then
    s!"let x := {v} in if x <= 100 then x div 2 else -x"
    else s!"match l \{ E::A => f({v}), E::B => ({v} + 2) * 3, }"
  let depth := n % 20
  "-- é 😀\r\n" ++ String.ofList (List.replicate depth '(') ++ body ++
    String.ofList (List.replicate depth ')') ++ "\t-- eof"

private def check (label : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' {numInst := 500, maxSize := 40, randomSeed := some 100502}
  IO.println s!"{label}: 500 samples, seed 100502, no discarded premises: {result}"
  match result with
  | .success _ => pure ()
  | _ => throw <| IO.userError s!"parser property failed: {label}"

#eval check "1000 required accepted roots and 500 required malformed inputs" <|
  ∀ (n file : Nat) (choice : Bool),
  let text := generated n choice
  let full := "pub fn f(l: E): Int :=\n" ++ text
  let malformed := "pub fn f(l: E): Int := (" ++ text ++ "\n"
  accepted (parseExpression ⟨file⟩ text) = true ∧
  accepted (parseFile ⟨file⟩ full) = true ∧
  accepted (parseFile ⟨file⟩ malformed) = false ∧
  audit .expression ⟨file⟩ text = true ∧ audit .file ⟨file⟩ full = true ∧
  audit .file ⟨file⟩ malformed = true

#eval check "arbitrary text, success and failure ownership/bounds/complete-input" <|
  ∀ (text : String) (file : Nat) (expr : Bool),
  audit (if expr then .expression else .context) ⟨file⟩ text = true

#eval check "file and context share ordered declaration trees and diagnostics" <|
  ∀ (text : String) (file : Nat), entriesAgree text file = true

-- Independent expectations for producer classifications, not a copy of a
-- producer-supplied verdict. Both properties also have universal Lean proofs.
#eval check "ASCII whitespace and UTF-8 continuation primitives" <| ∀ (raw : Nat),
  let b := raw % 256
  spaceByte b = ([32, 9, 10, 13].contains b) ∧
  continuationByte b = (List.range 64 |>.map (· + 128) |>.contains b)

private def expectFailure (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' {numInst := 100, randomSeed := some 100503}
  IO.println s!"deliberately false {name}: {result}"
  match result with
  | .failure _ _ _ => pure ()
  | _ => throw <| IO.userError s!"false producer control survived: {name}"

#eval expectFailure "whitespace drops CR" <| ∀ (_ : Nat), spaceByte 13 = false
#eval expectFailure "bounds shifted into a continuation byte" <| ∀ (_ : Nat), boundary "aéz" 2 = true

-- These perturb the real producer output, not an unrelated toy model.
#eval show IO Unit from do
  let .ok doc := parseExpression ⟨1⟩ "1 + 2 * 3" | throw <| IO.userError "grouping parse"
  let .expression body := doc.root | throw <| IO.userError "expression root"
  unless describe body == "(+ 1 (* 2 3))" && describe body != "(* (+ 1 2) 3)" do
    throw <| IO.userError "precedence control"
  let .expression (.binary left plus op (.binary middle star multiply right)) := doc.root
    | throw <| IO.userError "binary structure"
  let changed : Document := {doc with root := .expression (.binary (.binary left plus op middle) star multiply right)}
  let .expression changedBody := changed.root | throw <| IO.userError "control root"
  unless describe changedBody != "(+ 1 (* 2 3))" do
    throw <| IO.userError "grouping control survived"
  let changed : Document := {doc with root := .expression left}
  unless !coherent changed && changed.emit != doc.emit do
    throw <| IO.userError "dropped node/emission control survived"

  let .integer token value := left | throw <| IO.userError "literal fixture"
  let some shifted := FrenSource.Span.checked ⟨1⟩ 0 0 doc.source.utf8ByteSize
    | throw <| IO.userError "span fixture"
  let rightTree := Expr.binary middle star multiply right
  let originalRoot := Expr.binary (.integer token value) plus op rightTree
  let alteredRoot := Expr.binary (.integer {token with span := shifted} value) plus op rightTree
  let original : Document := {doc with root := .expression originalRoot}
  let changed : Document := {doc with root := .expression alteredRoot}
  unless coherent original && original == doc && !coherent changed && changed.emit == doc.emit do
    throw <| IO.userError "isolated token span perturbation survived"

#eval show IO Unit from do
  -- Missing required syntax at EOF, byte coordinates after multibyte trivia,
  -- and invalid ingestion bytes are explicit, independent expectations.
  for (entry, text) in [(.expression, ""), (.expression, "-- é😀"),
      (.file, "pub fn f("), (.file, "pub enum E { A"),
      (.expression, "let x :="), (.expression, "match l { E::A =>")] do
    let .error failure := parse entry ⟨9⟩ text | throw <| IO.userError s!"accepted truncation {text}"
    let d := failure.diagnostic
    unless d.span.start == text.utf8ByteSize && d.span.stop == text.utf8ByteSize &&
        d.span.file == ⟨9⟩ && audit entry ⟨9⟩ text do
      throw <| IO.userError s!"EOF anchoring {repr d}"
  let .error failure := parseExpression ⟨9⟩ "-- é😀\r\n1 / 2" | throw <| IO.userError "accepted /"
  unless failure.diagnostic.span.start == 13 && failure.diagnostic.span.stop == 14 do
    throw <| IO.userError s!"UTF-8 slash location: {repr failure.diagnostic}"
  for bytes in [ByteArray.mk #[0xff], ByteArray.mk #[0xc3], ByteArray.mk #[0xc0, 0x80],
      ByteArray.mk #[0xed, 0xa0, 0x80]] do
    unless sameResult (decode bytes) (.error "invalid UTF-8") do throw <| IO.userError "invalid UTF-8 ingestion"
  for text in ["", "-- eof", "aéz", "-- 😀\r\npub mod m"] do
    unless sameResult (decode text.toUTF8) (.ok text) do throw <| IO.userError "valid ingestion"

#eval show IO Unit from do
  -- Every character-prefix of these fixtures exercises actual partial text.
  -- Some prefixes are complete programs, so both outcomes are audited.
  let mut good := 0
  let mut bad := 0
  for source in ["pub fn f(b?, x: Int): Int := let y := x + 1 in if b? then y else x",
      "pub enum E { A, B }\nexpect e(l: E) { expect c: match l { E::A => true, E::B => false } }"] do
    for n in [:source.length + 1] do
      let text := String.ofList (source.toList.take n)
      unless audit .file ⟨1⟩ text do throw <| IO.userError s!"prefix audit: {text}"
      if accepted (parseFile ⟨1⟩ text) then good := good + 1 else bad := bad + 1
  IO.println s!"partial-input premises: {good} accepted, {bad} rejected, 0 discarded"
  -- No arbitrary small recursion cap; depth derives from input tokens.
  let deep := String.ofList (List.replicate 120 '(') ++ "1" ++ String.ofList (List.replicate 120 ')')
  unless accepted (parseExpression ⟨1⟩ deep) && audit .expression ⟨1⟩ deep do
    throw <| IO.userError "token-derived recursion budget"

#eval show IO Unit from do
  let raw := "  -- é\r\npub enum E { B, A }\r\n"
  let .ok direct := parseContext ⟨7⟩ raw | throw <| IO.userError "context"
  let called ← IO.mkRef false
  let runner := contextRunner ⟨7⟩ fun context input => do
    called.set true
    return if context == direct && context.emit == raw && input == "case bytes\r\n😀" then
      .ok "same tree and bytes" else .error "adapter disagreement"
  unless sameResult (← runner.execute raw "case bytes\r\n😀") (.ok "same tree and bytes") && (← called.get) do
    throw <| IO.userError "typed adapter"
  called.set false
  let .error actual ← runner.execute "pub fn f(" "case" | throw <| IO.userError "context accepted"
  let .error direct := parseContext ⟨7⟩ "pub fn f(" | throw <| IO.userError "direct accepted"
  unless actual == direct.diagnostic.render && !(← called.get) do
    throw <| IO.userError "adapter failed context callback"

end FrenParseTests
