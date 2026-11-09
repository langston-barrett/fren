import Fren.Impl
import Fren.Literate
import FrenParse

open Fren.Lang

#fren_md "LexicalStructure.md"

#fren_check

namespace Spec.Language.LexicalStructure

open FrenAst

/-- The kind of the actual lexer's slice for a piece of the chapter's class. -/
def kindOf (cls : spec.lexical.Class) (lexeme : String) : LexicalKind :=
  match cls with
  | .Whitespace | .Comment => .trivia
  | .Word => if spec.lexical.«keyword?» lexeme then .keyword else .identifier
  | .Numeral => .numeral
  | .Punctuator => .punctuation
  | .Rejected => .rejected

/-- The pieces that the chapter's rules give a source text: each piece's class
is `element_class` of the text from its start, and its lexeme the shortest
nonempty prefix after which `element_ends?` holds (`lexical.element.longest`).
This is the chapter's definition run as written, not a second lexer. -/
def specPieces (source : String) : List (LexicalKind × String) :=
  go source.toList (source.length + 1)
where
  go (cs : List Char) : Nat → List (LexicalKind × String)
    | 0 => []
    | fuel + 1 =>
      if cs.isEmpty then [] else
      let cls := spec.lexical.element_class (String.ofList cs)
      match ((List.range cs.length).map (· + 1)).find? (fun n =>
          spec.lexical.«element_ends?» cls (String.ofList (cs.take n)) (String.ofList (cs.drop n))) with
      | some n =>
        let lexeme := String.ofList (cs.take n)
        (kindOf cls lexeme, lexeme) :: go (cs.drop n) fuel
      -- No piece ends: the rules define none, which no lexer output equals.
      | none => [(.rejected, "")]

/-- The actual lexer's slices of a source text, with their kinds. -/
def actualPieces (source : String) : List (LexicalKind × String) :=
  (FrenParse.tokenize ⟨0⟩ source).tape.toList.map fun piece => (piece.kind, piece.text)

/-- Every string of length at most `n` over `alphabet`. -/
def strings (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (strings alphabet n).flatMap fun s => alphabet.map fun c => s.push c

/-- Characters that start, continue or end each class, and some that start none. -/
def alphabet : List Char :=
  ['a', 'Z', '_', '7', '?', '-', '<', '>', '=', '!', ':', '(', '{', ',', '+', '*', '/', '.',
   ' ', '\t', '\n', '\r', 'é']

/-- Longer texts: keywords, contextual words, every punctuator, comments and
line endings in context, and text outside ASCII. -/
def corpus : List String :=
  ["pub fn next_step(x: Int): Int := x div 2 -- é😀\r\nmod m", "if? match? _ a?b x--1 x<-1 x < -1",
   "0x1F 1.5 007 123abc", "a<=b::=c!=d=>e:=f", "-- only a comment", "--\r\r\n\r", "/- x -/",
   "assume not true false Bool Int", "forall exists proc use struct where with table",
   "é😀 x", "f(x)<=-1 -- note"]

--@ reference: lexical.source.characters
--@ reference: lexical.source.line-ending
--@ reference: lexical.element.partition
--@ reference: lexical.element.class
--@ reference: lexical.element.longest
--@ reference: lexical.element.rejected
--@ reference: lexical.comment.extent
--@ reference: lexical.word.shape
--@ reference: lexical.punctuator.longest
/-- `lexical.element.partition`, `lexical.element.class`, `lexical.element.longest`
and the rules of each class: the actual lexer gives exactly the chapter's
pieces, with their kinds, for every text of up to three characters over
`alphabet`, every text of four over a smaller one, and `corpus`. -/
def lexer_agrees : Bool :=
  let texts := strings alphabet 3 ++ strings ['a', '?', '-', '<', '=', '!', ':', '\r', '\n', '1'] 4 ++ corpus
  texts.all (fun s => actualPieces s == specPieces s &&
    -- Positions are UTF-8 byte offsets of the source text, with no gaps.
    FrenAst.ownsSource ⟨0⟩ s (FrenParse.tokenize ⟨0⟩ s).tape) &&
  -- The chapter's worked example.
  actualPieces "f(x)<=-1 -- note" ==
    [(.identifier, "f"), (.punctuation, "("), (.identifier, "x"), (.punctuation, ")"),
     (.punctuation, "<="), (.punctuation, "-"), (.numeral, "1"), (.trivia, " "), (.trivia, "-- note")] &&
  actualPieces "x<-1" == [(.identifier, "x"), (.rejected, "<-"), (.numeral, "1")]

#guard lexer_agrees

open Lean in
/-- The actual lexer's reserved spellings. The lexer keeps its table private,
so this reads that very constant from the environment, not a copy of it. -/
unsafe def lexerKeywords : CoreM (List String) := do
  let name := Name.mkNum (`_private ++ `FrenParse.Lex) 0 ++ `FrenParse.keywords
  ofExcept <| (← getEnv).evalConst (List String) (← getOptions) name

--@ reference: lexical.keyword.set
/-- `lexical.keyword.set`: the lexer's reserved spellings `lexer` are exactly
`KEYWORDS`, and each of them, and each near miss, lexes as one word that is a
keyword exactly when `keyword?` says so. -/
def keywords_agree (lexer : List String) : Bool :=
  decide (spec.lexical.KEYWORDS = Fren.FinSet.ofList lexer) &&
  (["if?", "match?", "Mod", "MOD", "mod_", "_mod", "letx", "assume", "not", "true", "false",
    "Bool", "Int", "when", "require", "ensure", "self", "_"] ++ lexer).all fun w =>
    match (FrenParse.tokenize ⟨0⟩ w).tokens.toList with
    | [t] => t.text == w && (t.kind == .keyword) == spec.lexical.«keyword?» w
    | _ => false

open Lean in
#eval show CoreM Unit from do
  let lexer ← unsafe lexerKeywords
  unless lexer.length == 37 && keywords_agree lexer do
    throwError "the lexer's keywords differ from `KEYWORDS`: {lexer}"

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

end Spec.Language.LexicalStructure

