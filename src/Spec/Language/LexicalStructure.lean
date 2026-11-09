import Fren.Impl
import Fren.Literate
import FrenParse

open Fren.Lang

#fren_md "LexicalStructure.md"

#fren_check

namespace Spec.Language.LexicalStructure

open FrenAst

--@ reference: lexical.keyword.set
-- The lexer's own keyword table is `KEYWORDS`: the lexer classifies a word as
-- a keyword exactly when it is in `FrenParse.keywords` (`lexer_agrees` checks
-- that use of the table).
impl reserved: reserved for (word : String) {
  word := word, keyword? := FrenParse.keywords.contains word
} by
  intro word _
  simp [fren_spec, FrenParse.keywords]

def classes : List spec.lexical.Class := [.Whitespace, .Comment, .Word, .Numeral, .Punctuator]

/-- The kind of the actual lexer's slice for a piece of the chapter's class. -/
def kindOf (cls : spec.lexical.Class) (lexeme : String) : LexicalKind :=
  match cls with
  | .Whitespace | .Comment => .trivia
  | .Word => if FrenParse.keywords.contains lexeme then .keyword else .identifier
  | .Numeral => .numeral
  | .Punctuator => .punctuation

/-- The pieces that the chapter's rules give a source text, read off the rules
as written: at each position, `<-` is rejected text
(`lexical.piece.rejected`); otherwise the piece is the longest prefix that
`in_class?` puts in a class (`lexical.piece.longest`), less the CR of a line
ending at the end of a comment (`lexical.piece.comment-end`); and if no
prefix is in a class, the first character is rejected text. -/
def specPieces (source : String) : List (LexicalKind × String) :=
  go source.toList (source.length + 1)
where
  go (cs : List Char) : Nat → List (LexicalKind × String)
    | 0 => []
    | fuel + 1 =>
      if cs.isEmpty then [] else
      if cs.take 2 == ['<', '-'] then (.rejected, "<-") :: go (cs.drop 2) fuel else
      -- No class has a text with an LF but the whitespace "\n" itself, so no
      -- piece extends past the first LF.
      let bound := match cs.idxOf? '\n' with | some i => i + 1 | none => cs.length
      let longest := (List.range bound).reverse.findSome? fun i =>
        let p := String.ofList (cs.take (i + 1))
        (classes.find? (spec.lexical.«in_class?» · p)).map (i + 1, ·)
      match longest with
      | none => (.rejected, String.ofList (cs.take 1)) :: go (cs.drop 1) fuel
      | some (n, cls) =>
        let n := if cls == .Comment && cs[n - 1]? == some '\r' &&
            spec.lexical.«line_ending?» (String.ofList (cs.drop (n - 1))) then n - 1 else n
        let lexeme := String.ofList (cs.take n)
        (kindOf cls lexeme, lexeme) :: go (cs.drop n) fuel

/-- The actual lexer's slices of a source text, with their kinds. -/
def actualPieces (source : String) : List (LexicalKind × String) :=
  (FrenParse.tokenize ⟨0⟩ source).tape.toList.map fun piece => (piece.kind, piece.text)

/-- Every string of length at most `n` over `alphabet`. -/
def strings (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (strings alphabet n).flatMap fun s => alphabet.map fun c => s.push c

/-- Characters that start, continue or end each class, and some that start none. -/
def alphabet : List Char :=
  ['a', 'Z', '_', '7', '?', '-', '<', '>', '=', '!', ':', '(', '{', ',', '+', '*', '%', '/', '.',
   ' ', '\t', '\n', '\r', 'é']

/-- `count` seeded pseudo-random texts of 20 to 120 characters over `alphabet`
and some characters outside ASCII, from a linear congruential generator. -/
def randomTexts (count : Nat) : List String := Id.run do
  let chars := alphabet ++ ['t', 'r', 'u', 'e', 'n', 'o', 'd', 'i', 'v', '😀', 'ß']
  let mut seed : Nat := 20261109
  let mut out := []
  for _ in [:count] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let len := 20 + seed / 2 ^ 40 % 101
    let mut text := ""
    for _ in [:len] do
      seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      text := text.push (chars[seed / 2 ^ 33 % chars.length]!)
    out := text :: out
  return out

/-- Longer texts: keywords, contextual words, every punctuator, comments and
line endings in context, and text outside ASCII. -/
def corpus : List String :=
  ["pub fn next_step(x: Int): Int := x div 2 -- é😀\r\nmod m", "if? match? _ a?b x--1 x<-1 x < -1",
   "0x1F 1.5 007 123abc", "a<=b::=c!=d=>e:=f%g%%h", "-- only a comment", "--\r\r\n\r", "/- x -/",
   "assume not true false true? Bool Int", "forall exists proc use struct where with table",
   "é😀 x", "f(x)<=-1 -- note"]

--@ reference: lexical.source.line-ending
--@ reference: lexical.class.definition
--@ reference: lexical.piece.longest
--@ reference: lexical.piece.comment-end
--@ reference: lexical.piece.rejected
/-- The lexical rules (`lexical.piece.longest`, `lexical.piece.comment-end`,
`lexical.piece.rejected`, `lexical.source.line-ending`, `lexical.class.definition`):
the actual lexer gives exactly the chapter's pieces, with their kinds, its
slices have UTF-8 byte offsets without gaps, and no text with rejected text
parses. Bounded: every text of up to three characters over `alphabet` (24
characters), every text of four over ten of them, `corpus`, and 500 seeded
random texts of 20 to 120 characters. -/
def lexer_agrees : Bool :=
  let texts := strings alphabet 3 ++ strings ['a', '?', '-', '<', '=', '!', ':', '\r', '\n', '1'] 4 ++
    corpus ++ randomTexts 500
  texts.all fun s => actualPieces s == specPieces s &&
    FrenAst.ownsSource ⟨0⟩ s (FrenParse.tokenize ⟨0⟩ s).tape &&
    (!(actualPieces s).any (·.1 == .rejected) ||
      !(FrenParse.parseFile ⟨0⟩ s).toBool && !(FrenParse.parseExpression ⟨0⟩ s).toBool)

#guard lexer_agrees

--@ reference: lexical.source.encoding
/-- `lexical.source.encoding`: byte ingestion accepts exactly valid UTF-8, with
the characters it encodes, and rejects overlong forms, surrogates, stray
continuation bytes, truncated sequences and bytes that never occur in UTF-8.
Bounded: every sequence of up to two bytes, and the listed longer ones. -/
def encoding_agrees : Bool :=
  let bytes (l : List Nat) : ByteArray := ⟨l.toArray.map (·.toUInt8)⟩
  let valid : List (List Nat) := [[], [0x41], [0xC3, 0xA9], [0xE2, 0x82, 0xAC], [0xF0, 0x9F, 0x98, 0x80]]
  let invalid : List (List Nat) := [[0xFF], [0x80], [0xC0, 0x80], [0xED, 0xA0, 0x80], [0xE2, 0x82],
    [0xF8, 0x88, 0x80, 0x80, 0x80], [0xF4, 0x90, 0x80, 0x80]]
  let short := (List.range 256).flatMap fun a => [[a]] ++ (List.range 256).map fun b => [a, b]
  valid.all (fun l => (FrenParse.decode (bytes l)).toOption == String.fromUTF8? (bytes l) &&
      (FrenParse.decode (bytes l)).toBool) &&
  invalid.all (fun l => !(FrenParse.decode (bytes l)).toBool) &&
  short.all fun l => (FrenParse.decode (bytes l)).toOption == String.fromUTF8? (bytes l)

#guard encoding_agrees

--@ reference: lexical.numeral.value
/-- `lexical.numeral.value`: the parser gives each numeral its decimal value,
leading zeros included, beyond any fixed width. -/
def numerals_agree : Bool :=
  [("0", 0), ("007", 7), ("42", 42), ("18446744073709551616", 18446744073709551616),
   ("000000000000000000000000000001", 1)].all fun (text, value) =>
    match FrenParse.parseExpression ⟨0⟩ text with
    | .ok doc => match doc.root with
      | .expression (.integer _ v) => v == value
      | _ => false
    | .error _ => false

#guard numerals_agree

def chapterPath : System.FilePath := "src" / "Spec" / "Language" / "LexicalStructure.md"

/-- A piece in the notation of the chapter's `fren2 pieces` blocks: its kind
and its text, a space written as `U+0020`. Trivia is told apart by its text. -/
def pieceLine : LexicalKind × String → String
  | (.trivia, t) => if t.startsWith "--" then s!"comment {t}" else
      "whitespace " ++ " ".intercalate (t.toList.map fun c =>
        let h := (String.ofList (Nat.toDigits 16 c.toNat)).toUpper
        "U+" ++ String.ofList (List.replicate (4 - h.length) '0') ++ h)
  | (.identifier, t) => s!"identifier {t}"
  | (.keyword, t) => s!"keyword {t}"
  | (.numeral, t) => s!"numeral {t}"
  | (.punctuation, t) => s!"punctuator {t}"
  | (.rejected, t) => s!"rejected {t}"

--@ reference: lexical.piece.longest
--@ reference: lexical.piece.rejected
/-- Each `fren2 pieces` block's first line lexes into the pieces that its
other lines list, by the actual lexer and by the chapter's rules alike. -/
def pieces_agree (md : String) : Except String Unit := do
  for b in (Fren.Core.fencedBlocks md).toList do
    if b.info != "fren2 pieces" then continue
    let some text := b.body[0]? | throw s!"LexicalStructure.md:{b.line}: an empty `fren2 pieces` block"
    let expected := b.body.toList.drop 1
    unless (actualPieces text).map pieceLine == expected && (specPieces text).map pieceLine == expected do
      throw s!"LexicalStructure.md:{b.line}: `{text}` has the pieces {(actualPieces text).map pieceLine}"

open Lean in
/-- The `tested` and `lean` names of a chapter's status comments. -/
def statusNames (md : String) : List String :=
  (md.splitOn "\n").filterMap fun l =>
    match (l.trimAscii.toString.dropPrefix? "<!-- status: ").map (·.toString) with
    | some rest => match rest.splitOn " " with
      | [kind, name, "-->"] => if kind == "tested" || kind == "lean" then some name else none
      | _ => none
    | none => none

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let md ← IO.FS.readFile chapterPath
  if let .error e := pieces_agree md then throwError e
  for name in statusNames md do
    unless (← getEnv).contains name.toName do throwError s!"the status names `{name}`, which does not exist"

end Spec.Language.LexicalStructure
