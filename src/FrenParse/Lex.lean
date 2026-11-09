module

public import FrenAst

public section
namespace FrenParse
open FrenAst

/-- Actual lexer primitive; the independent chapter uses natural byte values. -/
def spaceByte (byte : Nat) : Bool := byte == 32 || byte == 9 || byte == 10 || byte == 13

def continuationByte (byte : Nat) : Bool := 128 ≤ byte && byte < 192

--@ reference: parsing.primitive.space
theorem spaceByte_iff (byte : Nat) : spaceByte byte = true ↔
    byte = 32 ∨ byte = 9 ∨ byte = 10 ∨ byte = 13 := by simp [spaceByte, or_assoc]

--@ reference: parsing.primitive.continuation
theorem continuationByte_iff (byte : Nat) : continuationByte byte = true ↔
    128 ≤ byte ∧ byte < 192 := by simp [continuationByte]

structure Diagnostic where
  span : FrenSource.Span
  expected : String
  deriving Repr, BEq

def Diagnostic.render (diag : Diagnostic) : String :=
  s!"{diag.span.start}:{diag.span.stop}: expected {diag.expected}"

structure Lexed where
  file : FrenSource.FileId
  source : String
  tape : Array Slice
  tokens : Array Token
  eof : FrenSource.Span
  deriving Repr, BEq

/-- The reserved spellings (`Spec/Language/LexicalStructure#words-identifiers-and-keywords`),
reserved even when their constructs are outside this grammar. `true`, `false`
and `not` are keywords, so they are never names. The contextual word `assume`
and the built-in type names `Bool` and `Int` are identifiers, interpreted at
their grammar positions. -/
@[expose] def keywords : List String :=
  ["mod", "use", "pub", "ordered", "enum", "struct", "type", "fn", "const", "proc", "trait",
   "expect", "impl", "interp", "tested", "trusted", "iff", "and", "or", "union", "inter",
   "minus", "subset", "join", "div", "is", "in", "if", "then", "else", "match", "forall",
   "exists", "with", "let", "where", "table", "true", "false", "not"]

private def identStart (c : Char) : Bool := c.isAlpha && c.toNat < 128 || c == '_'
private def identRest (c : Char) : Bool := identStart c || c.isDigit

/-- Linear bounded scan. Every outer iteration owns at least one character;
lookahead only groups characters already present in the decoded input. -/
def tokenize (file : FrenSource.FileId) (source : String) : Lexed := Id.run do
  let chars := source.toList.toArray
  let mut tape := #[]
  let mut tokens := #[]
  let mut next := 0
  let mut offset := 0
  for i in [:chars.size] do
    if i < next then continue
    let c := chars[i]!
    let mut stop := i + 1
    let mut kind := LexicalKind.rejected
    if spaceByte c.toNat then
      kind := .trivia
    else if c == '-' && chars[i+1]? == some '-' then
      kind := .trivia
      stop := i + 2
      for j in [i+2:chars.size] do
        if chars[j]! == '\n' || (chars[j]! == '\r' && chars[j+1]? == some '\n') then break
        stop := j + 1
    else if identStart c then
      kind := .identifier
      for j in [i+1:chars.size] do
        if !identRest chars[j]! then break
        stop := j + 1
      if chars[stop]? == some '?' then stop := stop + 1
    else if c.isDigit then
      kind := .numeral
      for j in [i+1:chars.size] do
        if !chars[j]!.isDigit then break
        stop := j + 1
    else
      let pair := String.ofList [c, chars[i+1]?.getD '\x00']
      if pair == "<-" then
        -- Maximal punctuation ownership: this is unsupported, not `<` and `-`.
        kind := .rejected
        stop := i + 2
      else if ["<=", ">=", "!=", ":=", "=>", "::"].contains pair then
        kind := .punctuation
        stop := i + 2
      else if ['(', ')', '{', '}', ',', ':', '+', '-', '*', '=', '<', '>'].contains c then
        kind := .punctuation
    let text := String.ofList (chars.extract i stop).toList
    if kind == .identifier && keywords.contains text then kind := .keyword
    -- The offset is computed from decoded characters, never editor columns.
    let endOffset := offset + text.utf8ByteSize
    if let some span := FrenSource.Span.checked file offset endOffset source.utf8ByteSize then
      let index := tape.size
      tape := tape.push ⟨kind, text, span⟩
      if kind != .trivia then tokens := tokens.push ⟨index, text, span, kind⟩
    offset := endOffset
    next := stop
  -- EOF is an actual zero-width source boundary.
  let eof := (FrenSource.Span.checked file source.utf8ByteSize source.utf8ByteSize
    source.utf8ByteSize).get ((FrenSource.Span.checked_some_iff _ _ _ _).mpr ⟨by omega, by omega⟩)
  return ⟨file, source, tape, tokens, eof⟩

/-- Invalid UTF-8 is rejected before tokenization; no replacement decoding. -/
def decode (bytes : ByteArray) : Except String String :=
  match String.fromUTF8? bytes with
  | some text => .ok text
  | none => .error "invalid UTF-8"

/-- A boundary test connected to the actual source byte array. -/
def boundary (source : String) (offset : Nat) : Bool :=
  offset == 0 || offset == source.utf8ByteSize ||
    (offset < source.utf8ByteSize && !continuationByte (source.toUTF8[offset]!.toNat))

end FrenParse
