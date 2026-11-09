import Fren
import FrenParse
import FrenAstToHir
import Spec.Language.Syntax

/-!
# The syntax chapters' checks

The checks of [Lexical structure](../Spec/Language/LexicalStructure.md) and
[Syntax](../Spec/Language/Syntax.md) that run the actual lexer and parser on
many inputs. They are compiled into `fren_test`, whose `syntaxChapters` job
runs them, so that the chapters' own modules build in seconds. Each check
reads the chapter's Markdown as it is written.
-/

namespace FrenTest.SpecChapters.Syntax

open Fren.Generated FrenAst

/-! ## Lexical structure -/
def classes : List spec.lexical.Class := [.Whitespace, .Comment, .Word, .Numeral, .Punctuator]

/-- The kind of the actual lexer's slice for a piece of the chapter's class. -/
def kindOf (cls : spec.lexical.Class) (lexeme : String) : LexicalKind :=
  match cls with
  | .Whitespace | .Comment => .trivia
  | .Word => if FrenParse.keywords.contains lexeme then .keyword else .identifier
  | .Numeral => .numeral
  | .Punctuator => .punctuation

/-- Every next piece that the chapter's `next_piece?` admits at the start of
`remaining`: each class or none, with each length up to the end of the text. -/
def nextPieces (remaining : String) : List (Option spec.lexical.Class × Nat) :=
  (none :: classes.map some).flatMap fun kind =>
    (List.range remaining.length).filterMap fun i =>
      if spec.lexical.«next_piece?» remaining kind (Int.ofNat (i + 1)) then some (kind, i + 1) else none

/-- `lexical.piece.division` at one position: no text of a class at the start
of `remaining` is longer than the piece of `n` characters there, but a comment
up to the CR of a line ending. -/
def noLonger (remaining : String) (n : Nat) : Bool :=
  (List.range (remaining.length - n)).all fun k =>
    let m := n + 1 + k
    let longer := String.ofList (remaining.toList.take m)
    !spec.lexical.«classed?» longer ||
      (k == 0 && spec.lexical.«in_class?» .Comment longer &&
        spec.lexical.«line_ending?» (String.ofList ((remaining.toList.drop n).take 2)))

/-- The pieces that the chapter gives a source text (`lexical.piece.division`):
the piece that `next_piece?` gives at position 0, then at each piece's end.
`none` when some position has no next piece or more than one, or has a longer
text of a class than the division allows. -/
def specPieces (source : String) : Option (List (LexicalKind × String)) :=
  go source.toList (source.length + 1)
where
  go (cs : List Char) : Nat → Option (List (LexicalKind × String))
    | 0 => none
    | fuel + 1 =>
      if cs.isEmpty then some [] else
      let remaining := String.ofList cs
      match nextPieces remaining with
      | [(kind, n)] =>
        let lexeme := String.ofList (cs.take n)
        if noLonger remaining n then
          (go (cs.drop n) fuel).map (((kind.map (kindOf · lexeme)).getD .rejected, lexeme) :: ·)
        else none
      | _ => none

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

-- fren-covers: spec::lexical::division
-- fren-covers: spec::parsing::lexer_agreement
--@ reference: lexical.source.line-ending
--@ reference: lexical.class.definition
--@ reference: lexical.piece.longest
--@ reference: lexical.piece.next
--@ reference: lexical.piece.comment-end
--@ reference: lexical.piece.rejected
--@ reference: lexical.piece.division
/-- The lexical rules (`lexical.piece.next`, `lexical.piece.division`,
`lexical.source.line-ending`, `lexical.class.definition`): the start of a
text, and each position where one of its pieces ends, has exactly one next
piece by the chapter's `next_piece?`, among every class and length, with no
longer text of a class than the division allows; the actual lexer gives exactly
those pieces, with their kinds; its slices have UTF-8 byte offsets without
gaps; and no text with rejected text parses. Positions inside a piece are
checked only as the starts of other texts: the exhaustive texts include each
of their own suffixes, the corpus and the random texts do not.
Bounded: every text of up to three characters over `alphabet` (24 characters),
every text of up to four over ten of them, `corpus`, and 500 seeded random
texts of 20 to 120 characters. -/
def lexer_agrees : Bool :=
  let texts := strings alphabet 3 ++ strings ['a', '?', '-', '<', '=', '!', ':', '\r', '\n', '1'] 4 ++
    corpus ++ randomTexts 500
  texts.all fun s => specPieces s == some (actualPieces s) &&
    FrenAst.ownsSource ⟨0⟩ s (FrenParse.tokenize ⟨0⟩ s).tape &&
    (!(actualPieces s).any (·.1 == .rejected) ||
      !(FrenParse.parseFile ⟨0⟩ s).toBool && !(FrenParse.parseExpression ⟨0⟩ s).toBool)


-- fren-covers: spec::parsing::decoding
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


-- fren-covers: spec::parsing::numerals
--@ reference: lexical.numeral.value
/-- `lexical.numeral.value`: the parser gives each numeral its decimal value,
leading zeros included, beyond any fixed width. Bounded: the listed numerals,
which include 2^64, 2^128 + 1 and 10^40, and 200 seeded random numerals of 1 to
80 digits, whose value is summed from their digits. -/
def numerals_agree : Bool :=
  let listed := [("0", 0), ("007", 7), ("42", 42), ("18446744073709551616", 18446744073709551616),
    ("340282366920938463463374607431768211457", 2 ^ 128 + 1),
    ("10000000000000000000000000000000000000000", 10 ^ 40),
    ("000000000000000000000000000001", 1)]
  let random := Id.run do
    let mut seed : Nat := 20261110
    let mut out := []
    for _ in [:200] do
      seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      let len := 1 + seed / 2 ^ 40 % 80
      let mut digits : List Nat := []
      for _ in [:len] do
        seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
        digits := seed / 2 ^ 33 % 10 :: digits
      out := (String.ofList (digits.map fun d => Char.ofNat (48 + d)),
        digits.foldl (fun value d => value * 10 + d) 0) :: out
    return out
  (listed ++ random).all fun (text, value) =>
    match FrenParse.parseExpression ⟨0⟩ text with
    | .ok doc => match doc.root with
      | .expression (.integer _ v) => v == value
      | _ => false
    | .error _ => false



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

-- fren-covers: spec::lexical::division
-- fren-covers: spec::parsing::lexer_agreement
--@ reference: lexical.piece.next
--@ reference: lexical.piece.comment-end
--@ reference: lexical.piece.rejected
/-- Each `fren2 pieces` block's first line, with `\r` and `\n` read as CR and
LF, lexes into the pieces that its other lines list, by the actual lexer and
by the chapter's `next_piece?` alike. -/
def pieces_agree (md : String) : Except String Unit := do
  for b in (Fren.Core.fencedBlocks md).toList do
    if b.info != "fren2 pieces" then continue
    let some line := b.body[0]? | throw s!"LexicalStructure.md:{b.line}: an empty `fren2 pieces` block"
    let text := (line.replace "\\r" "\r").replace "\\n" "\n"
    let expected := b.body.toList.drop 1
    unless (actualPieces text).map pieceLine == expected &&
        (specPieces text).map (·.map pieceLine) == some expected do
      throw s!"LexicalStructure.md:{b.line}: `{text}` has the pieces {(actualPieces text).map pieceLine}"

/-! ## Syntax -/
open FrenAst

abbrev SUnary := spec.surface.UnaryOp
abbrev SBinary := spec.surface.BinaryOp
abbrev Category := spec.surface.Category

/-! The chapter's checks run the actual parser, `FrenParse.parse`, against the
chapter as written: its `grammar` blocks, read from the Markdown and run as a
parsing expression grammar; its abstract syntax and printing functions; and
its example blocks. Every check takes the chapter's text, so that the
mutation control below can run it on altered chapters. -/

/-! ## The chapter's text -/

def chapterPath : System.FilePath := "src" / "Spec" / "Language" / "Syntax.md"

/-- The bodies of the chapter's blocks with info string `info`, each with the
line of its fence. -/
def blocks (md info : String) : List (Nat × String) :=
  (Fren.Core.fencedBlocks md).toList.filterMap fun b =>
    if b.info == info then some (b.line, "\n".intercalate b.body.toList) else none

/-! ## The grammar, as data read from the chapter

A parsing expression, with an identity for each node that a choice or a
repetition makes, so that example coverage can name it. -/
inductive G where
  | term (spelling : String)
  | nt (name : String)
  | seq (parts : List G)
  | alt (id : String) (options : List G)
  | opt (id : String) (g : G)
  | star (id : String) (g : G)
  | plus (id : String) (g : G)
  | neg (g : G)
  deriving Inhabited, Repr, BEq

/-- The terminals that are classes of tokens, not spellings. -/
def classTerminals : List String := ["Identifier", "QuestionIdentifier", "Numeral", "TouchingOpen"]

/-- The lexemes of grammar notation: names, quoted strings, and `( ) | ? * + !`;
anything else is an error. -/
def notationTokens (text : String) : Except String (List String) := do
  let mut out := []
  let mut cs := text.toList
  for _ in [:text.length + 1] do
    match cs with
    | [] => break
    | c :: rest =>
      if c == ' ' || c == '\n' then cs := rest
      else if c == '"' then
        let body := rest.takeWhile (· != '"')
        if body.length == rest.length || body.isEmpty then
          throw s!"an unterminated or empty quoted terminal in `{text.trimAscii}`"
        out := out ++ [String.ofList ('"' :: body)]
        cs := (rest.drop body.length).drop 1
      else if c.isAlpha then
        let name := cs.takeWhile Char.isAlphanum
        out := out ++ [String.ofList name]
        cs := cs.drop name.length
      else if "()|?*+!".contains c then
        out := out ++ [String.singleton c]
        cs := rest
      else throw s!"the character `{c}` in `{text.trimAscii}` is no grammar notation"
  return out

/-- A recursive-descent reader of grammar notation, which numbers the nodes of
rule `rule` as it reads them. -/
structure Reader where
  rule : String
  next : Nat := 0

abbrev ReadM := StateT Reader (Except String)

def fresh : ReadM String := do
  let r ← get
  set { r with next := r.next + 1 }
  return s!"{r.rule}.{r.next}"

mutual
partial def readAlt (ts : List String) : ReadM (G × List String) := do
  let id ← fresh
  let (first, ts) ← readSeq ts
  let mut options := [first]
  let mut ts := ts
  repeat
    match ts with
    | "|" :: rest =>
      let (s, rest) ← readSeq rest
      options := options ++ [s]
      ts := rest
    | _ => break
  return (if options.length == 1 then first else .alt id options, ts)

partial def readSeq (ts : List String) : ReadM (G × List String) := do
  let mut parts := []
  let mut ts := ts
  repeat
    match ts with
    | [] | "|" :: _ | ")" :: _ => break
    | _ =>
      let (i, rest) ← readItem ts
      parts := parts ++ [i]
      ts := rest
  if parts.isEmpty then throw "an empty alternative"
  return (if parts.length == 1 then parts.head! else .seq parts, ts)

partial def readItem (ts : List String) : ReadM (G × List String) := do
  match ts with
  | "!" :: rest => let (i, rest) ← readItem rest; return (.neg i, rest)
  | _ =>
    let (a, ts) ← readAtom ts
    let mut g := a
    let mut ts := ts
    repeat
      match ts with
      | "?" :: rest => g := .opt (← fresh) g; ts := rest
      | "*" :: rest => g := .star (← fresh) g; ts := rest
      | "+" :: rest => g := .plus (← fresh) g; ts := rest
      | _ => break
    return (g, ts)

partial def readAtom (ts : List String) : ReadM (G × List String) := do
  match ts with
  | "(" :: rest =>
    let (g, rest) ← readAlt rest
    match rest with
    | ")" :: rest => return (g, rest)
    | _ => throw "a group without its `)`"
  | t :: rest =>
    if t.startsWith "\"" then return (.term (t.drop 1).toString, rest)
    else if t.front.isUpper then return (.nt t, rest)
    else throw s!"`{t}` is neither a quoted terminal nor a nonterminal"
  | [] => throw "an alternative that ends early"
end

/-- The nonterminals that a grammar names. -/
partial def G.names : G → List String
  | .term _ => []
  | .nt n => [n]
  | .seq gs | .alt _ gs => gs.flatMap G.names
  | .opt _ g | .star _ g | .plus _ g | .neg g => g.names

/-- The rules of the chapter's `grammar` blocks: a line that contains `::=`
starts a rule, and the lines after it continue it. Malformed notation, a rule
defined twice, a nonterminal that no rule defines, and a rule that `File` and
`ExpressionEntry` do not reach are errors. -/
def grammarOf (md : String) : Except String (List (String × G)) := do
  let mut raw : List (String × String) := []
  for (_, body) in blocks md "grammar" do
    for line in body.splitOn "\n" do
      match line.splitOn "::=" with
      | [lhs, rhs] => raw := raw ++ [(lhs.trimAscii.toString, rhs)]
      | [_] => match raw.getLast? with
        | some (n, rhs) => raw := raw.dropLast ++ [(n, rhs ++ " " ++ line)]
        | none => throw s!"`{line}` continues no rule"
      | _ => throw s!"`{line}` has more than one `::=`"
  let mut rules := []
  for (n, rhs) in raw do
    unless n.toList.all Char.isAlphanum && n.front.isUpper do throw s!"`{n}` is no nonterminal"
    if rules.any (·.1 == n) then throw s!"`{n}` is defined twice"
    let (g, rest) ← ((readAlt (← notationTokens rhs)).run' { rule := n })
    unless rest.isEmpty do throw s!"`{n}` has unread notation {rest}"
    rules := rules ++ [(n, g)]
  for (n, g) in rules do
    for m in g.names do
      unless classTerminals.contains m || rules.any (·.1 == m) do
        throw s!"`{n}` names `{m}`, which no rule defines"
  -- Every rule is reachable from the start nonterminals.
  let mut reached := ["File", "ExpressionEntry"]
  for _ in [:rules.length + 1] do
    reached := (reached ++ reached.flatMap fun r => ((rules.lookup r).map G.names).getD []).eraseDups
  for (n, _) in rules do
    unless reached.contains n do throw s!"`{n}` is unreachable from `File` and `ExpressionEntry`"
  for start in ["File", "ExpressionEntry"] do
    unless rules.any (·.1 == start) do throw s!"no rule defines `{start}`"
  return rules

/-! ## Running the grammar on the lexer's tokens -/

/-- A token, with whether trivia comes before it. -/
structure Tok where
  text : String
  kind : LexicalKind
  touching : Bool

def toks (source : String) : Array Tok :=
  let lexed := FrenParse.tokenize ⟨0⟩ source
  lexed.tokens.mapIdx fun i t =>
    let touching := match (if i == 0 then none else lexed.tokens[i - 1]?) with
      | some previous => previous.slice + 1 == t.slice
      | none => false
    { text := t.text, kind := t.kind, touching }

def terminal (spelling : String) (t : Tok) : Bool :=
  match spelling with
  | "Identifier" => t.kind == .identifier
  | "QuestionIdentifier" => t.kind == .identifier && t.text.endsWith "?"
  | "Numeral" => t.kind == .numeral
  | "TouchingOpen" => t.text == "(" && t.touching
  | _ => false

/-- Match `g` at token `i`: the position after the match and the choices and
repetitions that it used, or `none` if it does not match. -/
partial def run (rules : List (String × G)) (ts : Array Tok) (g : G) (i : Nat) :
    Option (Nat × List String) :=
  match g with
  | .term s => match ts[i]? with
    | some t => if t.text == s && t.kind != .rejected then some (i + 1, []) else none
    | none => none
  | .nt n =>
    if classTerminals.contains n then
      match ts[i]? with
      | some t => if terminal n t then some (i + 1, []) else none
      | none => none
    else (rules.lookup n).bind (run rules ts · i)
  | .seq parts => parts.foldlM (init := (i, [])) fun (j, used) p =>
      (run rules ts p j).map fun (k, more) => (k, used ++ more)
  | .alt id options =>
    options.zipIdx.findSome? fun (o, k) => (run rules ts o i).map fun (j, used) => (j, s!"{id}/{k}" :: used)
  | .opt id g => some <| match run rules ts g i with
    | some (j, used) => (j, id :: used)
    | none => (i, [])
  | .star id g =>
    let rec loop (j : Nat) (used : List String) (fuel : Nat) : Nat × List String :=
      match fuel with
      | 0 => (j, used)
      | fuel + 1 => match run rules ts g j with
        | some (k, more) => if k == j then (j, used) else loop k (used ++ id :: more) fuel
        | none => (j, used)
    some (loop i [] (ts.size + 1))
  | .plus id g => (run rules ts g i).bind fun (j, used) =>
      (run rules ts (.star id g) j).map fun (k, more) => (k, id :: used ++ more)
  | .neg g => if (run rules ts g i).isSome then none else some (i, [])

/-- `run` without the record of choices, for speed. -/
partial def matchAt (rules : List (String × G)) (ts : Array Tok) (g : G) (i : Nat) : Option Nat :=
  match g with
  | .term s => match ts[i]? with
    | some t => if t.text == s && t.kind != .rejected then some (i + 1) else none
    | none => none
  | .nt n =>
    if classTerminals.contains n then
      match ts[i]? with
      | some t => if terminal n t then some (i + 1) else none
      | none => none
    else (rules.lookup n).bind (matchAt rules ts · i)
  | .seq parts => parts.foldlM (init := i) fun j p => matchAt rules ts p j
  | .alt _ options => options.findSome? (matchAt rules ts · i)
  | .opt _ g => some ((matchAt rules ts g i).getD i)
  | .star _ g =>
    let rec loop (j : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => j
      | fuel + 1 => match matchAt rules ts g j with
        | some k => if k == j then j else loop k fuel
        | none => j
    some (loop i (ts.size + 1))
  | .plus id g => (matchAt rules ts g i).bind (matchAt rules ts (.star id g) ·)
  | .neg g => if (matchAt rules ts g i).isSome then none else some i

def grammarAccepts (rules : List (String × G)) (start source : String) : Bool :=
  let ts := toks source
  matchAt rules ts (.nt start) 0 == some ts.size

def parserAccepts (entry : Entry) (source : String) : Bool :=
  (FrenParse.parse entry ⟨0⟩ source).toBool

/-! ## Inputs -/

def lcg (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Every sequence of at most `n` of `pieces`, joined by spaces. -/
def sequences (pieces : List String) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (sequences pieces n).flatMap fun s =>
      pieces.map fun p => if s.isEmpty then p else s ++ " " ++ p

/-- `count` seeded pseudo-random sequences of 5 to 14 of `pieces`. -/
def randomSequences (pieces : List String) (count seed : Nat) : List String := Id.run do
  let mut seed := seed
  let mut out := []
  for _ in [:count] do
    seed := lcg seed
    let len := 5 + seed / 2 ^ 40 % 10
    let mut text := ""
    for _ in [:len] do
      seed := lcg seed
      text := text ++ " " ++ pieces[seed / 2 ^ 33 % pieces.length]!
    out := text :: out
  return out

def expressionPieces : List String :=
  ["x", "1", "true", "not", "-", "+", "*", "%", "<", "=", "and", "iff", "(", ")", "f(", ",", "if",
   "then", "else", "let", ":=", "in", "match", "{", "}", "E::A", "=>", "::", "\n%", "mod"]

def smallExpressionPieces : List String :=
  ["x", "not", "-", "<", "(", ")", "f(", "if"]

def declarationPieces : List String :=
  ["pub", "fn f(x: Int): Int :=", "fn f(", "x", "b?", ":", "Int", ")", "): Int :=", "mod m", "mod",
   "::", "%", "enum E {", "A", ",", "}", "expect e(", "expect e() {", "{", "expect c:", "assume",
   "a:", ":=", "let"]

/-- The texts near `text`: each with one token dropped, each with one token
written twice, and each with one matched pair of parentheses dropped. -/
def nearTexts (text : String) (pairsOnly : Bool := false) : List String :=
  let pieces := (FrenParse.tokenize ⟨0⟩ text).tape.toList.map (·.text)
  let tokenAt := pieces.zipIdx.filter fun (p, _) =>
    !(p.all fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r') && !p.startsWith "--"
  let without (ks : List Nat) := String.join (pieces.zipIdx.filterMap fun (p, k) => if ks.contains k then none else some p)
  let doubled (k : Nat) := String.join (pieces.zipIdx.map fun (p, j) => if j == k then p ++ " " ++ p else p)
  -- Matched parentheses, by a stack of the open ones.
  let pairs := Id.run do
    let mut stack : List Nat := []
    let mut out : List (Nat × Nat) := []
    for (p, k) in pieces.zipIdx do
      if p == "(" then stack := k :: stack
      else if p == ")" then
        match stack with
        | o :: rest => out := (o, k) :: out; stack := rest
        | [] => pure ()
    return out
  if pairsOnly then pairs.map fun (o, c) => without [o, c] else
  (tokenAt.map fun (_, k) => without [k]) ++ (tokenAt.map fun (_, k) => doubled k) ++
    pairs.map fun (o, c) => without [o, c]

/-! ## Abstract syntax -/

/-- An expression tree: the fixed point of the chapter's `ExprF`, one
constructor for each of its constructors. -/
inductive Tree where
  | boolean (b : Bool)
  | integer (n : Nat)
  | name (path : List String)
  | call (path : List String) (args : List Tree)
  | unary (op : SUnary) (e : Tree)
  | binary (op : SBinary) (l r : Tree)
  | ifE (c t e : Tree)
  | letE (x : String) (v b : Tree)
  | matchE (s : Tree) (arms : List (List String × Tree))
  deriving Inhabited

def unaryOps : List SUnary := [.Neg, .Not]
def binaryOps : List SBinary :=
  [.Add, .Sub, .Mul, .Div, .Mod, .Eq, .Ne, .Lt, .Le, .Gt, .Ge, .And, .Or, .Iff]

theorem all_binary (op : SBinary) : op ∈ binaryOps := by cases op <;> simp [binaryOps]
theorem all_unary (op : SUnary) : op ∈ unaryOps := by cases op <;> simp [unaryOps]

def pathOf (p : Path) : List String := p.tokens.filter (·.text != "::") |>.map (·.text)

def unaryOf : FrenAst.UnaryOp → SUnary
  | .neg => .Neg | .not => .Not

def binaryOf (op : FrenAst.BinaryOp) : SBinary :=
  match op with
  | .add => .Add | .sub => .Sub | .mul => .Mul | .div => .Div | .mod => .Mod | .eq => .Eq
  | .ne => .Ne | .lt => .Lt | .le => .Le | .gt => .Gt | .ge => .Ge | .and => .And | .or => .Or
  | .iff => .Iff

def spellBinary (op : SBinary) : String := spec.surface.binary_spelling op
def spellUnary (op : SUnary) : String := spec.surface.unary_spelling op

/-- `syntax.tree.productions`: the tree of each expression production. An
operator node has the operator whose spelling (`unary_spelling`,
`binary_spelling`) was written; with any other spelling the result is the
empty name, which is no tree of the chapter. -/
partial def abstract : Expr → Tree
  | .name path => .name (pathOf path)
  | .bool _ b => .boolean b
  | .integer _ n => .integer n
  | .paren _ body _ => abstract body
  | .unary token op body =>
    if spellUnary (unaryOf op) == token.text then .unary (unaryOf op) (abstract body) else .name []
  | .binary l token op r =>
    if spellBinary (binaryOf op) == token.text then .binary (binaryOf op) (abstract l) (abstract r)
    else .name []
  | .call (.name path) _ args _ _ => .call (pathOf path) (args.toList.map abstract)
  | .call _ _ args _ _ => .call [] (args.toList.map abstract)
  | .ifE _ c _ t _ e => .ifE (abstract c) (abstract t) (abstract e)
  | .letE _ x _ v _ b => .letE x.text (abstract v) (abstract b)
  | .matchE _ s _ arms _ => .matchE (abstract s) (arms.toList.map fun a => (pathOf a.1, abstract a.2.2.1))

def unaryName : SUnary → String | .Neg => "Neg" | .Not => "Not"
def binaryName : SBinary → String
  | .Add => "Add" | .Sub => "Sub" | .Mul => "Mul" | .Div => "Div" | .Mod => "Mod" | .Eq => "Eq"
  | .Ne => "Ne" | .Lt => "Lt" | .Le => "Le" | .Gt => "Gt" | .Ge => "Ge" | .And => "And"
  | .Or => "Or" | .Iff => "Iff"

/-- A tree's top node, as the chapter's `ExprF` over its subtrees. -/
def Tree.layer : Tree → spec.surface.ExprF Tree
  | .boolean b => .Boolean b
  | .integer n => .Integer n
  | .name p => .Name (Fren.Seq.ofList p)
  | .call p args => .Call (Fren.Seq.ofList p) (Fren.Seq.ofList args)
  | .unary op e => .Unary op e
  | .binary op l r => .Binary op l r
  | .ifE c t e => .If c t e
  | .letE x v b => .Let x v b
  | .matchE s arms => .Match s (Fren.Seq.ofList (arms.map fun (p, b) => .mk! (Fren.Seq.ofList p) b))

/-- A tree from its top node: `Tree` is the fixed point of `ExprF`. -/
def Tree.ofLayer : spec.surface.ExprF Tree → Tree
  | .Boolean b => .boolean b
  | .Integer n => .integer n
  | .Name p => .name p.toList
  | .Call p args => .call p.toList args.toList
  | .Unary op e => .unary op e
  | .Binary op l r => .binary op l r
  | .If c t e => .ifE c t e
  | .Let x v b => .letE x v b
  | .Match s arms => .matchE s (arms.toList.map fun a => (a.variant.toList, a.body))

theorem Tree.ofLayer_layer (t : Tree) : Tree.ofLayer t.layer = t := by
  cases t <;> simp [Tree.layer, Tree.ofLayer, Fren.Seq.ofList, Fren.Seq.toList, Function.comp_def]

/-- `ExprF` maps over its subexpressions. -/
def mapLayer (f : α → β) : spec.surface.ExprF α → spec.surface.ExprF β
  | .Boolean b => .Boolean b
  | .Integer n => .Integer n
  | .Name p => .Name p
  | .Call p args => .Call p (Fren.Seq.ofList (args.toList.map f))
  | .Unary op e => .Unary op (f e)
  | .Binary op l r => .Binary op (f l) (f r)
  | .If c t e => .If (f c) (f t) (f e)
  | .Let x v b => .Let x (f v) (f b)
  | .Match s arms => .Match (f s) (Fren.Seq.ofList (arms.toList.map fun a => .mk! a.variant (f a.body)))

def pathText (p : Fren.Seq String) : String := "::".intercalate p.toList

/-- One `ExprF` node, whose subtrees are already written, in the chapter's
`fren2 trees` notation: the constructor's name and its fields. -/
def layerSexp : spec.surface.ExprF String → String
  | .Boolean b => s!"(Boolean {b})"
  | .Integer n => s!"(Integer {n})"
  | .Name p => s!"(Name {pathText p})"
  | .Call p args => s!"(Call {pathText p}" ++ String.join (args.toList.map (" " ++ ·)) ++ ")"
  | .Unary op e => s!"(Unary {unaryName op} {e})"
  | .Binary op l r => s!"(Binary {binaryName op} {l} {r})"
  | .If c t e => s!"(If {c} {t} {e})"
  | .Let x v b => s!"(Let {x} {v} {b})"
  | .Match s arms => s!"(Match {s}" ++
      String.join (arms.toList.map fun a => s!" (Arm {pathText a.variant} {a.body})") ++ ")"

partial def Tree.sexp (t : Tree) : String := layerSexp (mapLayer Tree.sexp t.layer)

/-- The tree of a type: the chapter's `type_name` of its written path
(`syntax.tree.productions`). -/
def typeTree : Ty → spec.surface.TypeName
  | .bool token | .int token => spec.surface.type_name (Fren.Seq.ofList [token.text])
  | .named p => spec.surface.type_name (Fren.Seq.ofList (pathOf p))

def typeSexp : spec.surface.TypeName → String
  | .Boolean => "Boolean"
  | .Integer => "Integer"
  | .Named p => s!"(Named {pathText p})"

def paramTree (p : Parameter) : spec.surface.Parameter :=
  ⟨p.name.text, p.annotation.map (typeTree ·.2)⟩

def paramSexp (p : spec.surface.Parameter) : String :=
  match p.annotation with
  | some t => s!"(Parameter {p.name} {typeSexp t})"
  | none => s!"(Parameter {p.name})"

/-- The tree of a declaration (`syntax.tree.productions`), as the chapter's
`DeclarationF` over expression trees. -/
def declTree : Decl → spec.surface.DeclarationF Tree
  | .moduleDecl v _ p => .Module ⟨v.isSome, Fren.Seq.ofList (pathOf p)⟩
  | .enumDecl v _ n _ vs _ _ => .Enumeration ⟨v.isSome, n.text, Fren.Seq.ofList (vs.toList.map (·.text))⟩
  | .function v _ n ps _ r _ b =>
    .Function (.mk! v.isSome n.text (Fren.Seq.ofList (ps.values.toList.map paramTree)) (typeTree r) (abstract b))
  | .expectation _ n ps _ ms _ =>
    .Expectation (.mk! n.text (Fren.Seq.ofList (ps.values.toList.map paramTree))
      (Fren.Seq.ofList (ms.toList.map fun m =>
        .mk! (if m.kind == .assume then .Assume else .Expect) m.label.text (abstract m.body))))

/-- A `DeclarationF` node in the `fren2 trees` notation, read off its fields. -/
def declSexp : spec.surface.DeclarationF Tree → String
  | .Module d => s!"(Module {if d.public? then "pub " else ""}{pathText d.path})"
  | .Enumeration d =>
    s!"(Enumeration {if d.public? then "pub " else ""}{d.name}" ++ String.join (d.variants.toList.map (" " ++ ·)) ++ ")"
  | .Function d =>
    s!"(Function {if d.public? then "pub " else ""}{d.name}" ++
      String.join (d.parameters.toList.map (" " ++ paramSexp ·)) ++ s!" {typeSexp d.result} {d.body.sexp})"
  | .Expectation d =>
    s!"(Expectation {d.name}" ++ String.join (d.parameters.toList.map (" " ++ paramSexp ·)) ++
      String.join (d.members.toList.map fun m =>
        s!" (Member {match m.kind with | .Assume => "Assume" | .Expect => "Expect"} {m.label} {m.body.sexp})") ++ ")"

def exprSexp? (source : String) : Option String :=
  match FrenParse.parseExpression ⟨0⟩ source with
  | .ok { root := .expression e, .. } => some (abstract e).sexp
  | _ => none

def fileSexp? (source : String) : Option String :=
  match FrenParse.parseFile ⟨0⟩ source with
  | .ok { root := .declarations ds, .. } => some ("(File" ++ String.join (ds.toList.map fun d => " " ++ declSexp (declTree d)) ++ ")")
  | _ => none

/-- The subexpressions of a node, in the order of `ExprF`. -/
def layerChildren : spec.surface.ExprF α → List α
  | .Boolean _ | .Integer _ | .Name _ => []
  | .Call _ args => args.toList
  | .Unary _ e => [e]
  | .Binary _ l r => [l, r]
  | .If c t e => [c, t, e]
  | .Let _ v b => [v, b]
  | .Match s arms => s :: arms.toList.map (·.body)

/-- `syntax.tree.well-formed`: the chapter's `node_well_formed?` holds of
every node of the tree, with its subexpressions elided. -/
partial def Tree.wellFormed (t : Tree) : Bool :=
  spec.surface.«node_well_formed?» (mapLayer (fun _ => .Elided) t.layer) &&
    (layerChildren t.layer).all Tree.wellFormed

/-- `DeclarationF` maps over its expressions. -/
def mapDecl (f : α → β) : spec.surface.DeclarationF α → spec.surface.DeclarationF β
  | .Module d => .Module d
  | .Enumeration d => .Enumeration d
  | .Function d => .Function (.mk! d.public? d.name d.parameters d.result (f d.body))
  | .Expectation d =>
    .Expectation (.mk! d.name d.parameters
      (Fren.Seq.ofList (d.members.toList.map fun m => .mk! m.kind m.label (f m.body))))

/-- The expressions of a declaration. -/
def declBodies : spec.surface.DeclarationF α → List α
  | .Module _ | .Enumeration _ => []
  | .Function d => [d.body]
  | .Expectation d => d.members.toList.map (·.body)

/-- `syntax.tree.well-formed`: the chapter's `declaration_well_formed?` holds
of the declaration, and each of its expressions is well formed. -/
def declWellFormed (d : spec.surface.DeclarationF Tree) : Bool :=
  spec.surface.«declaration_well_formed?» (mapDecl (fun _ => .Elided) d) &&
    (declBodies d).all Tree.wellFormed

/-- Whether each declaration of a file is well formed (`syntax.tree.well-formed`). -/
def fileTrees? (source : String) : Option (List Bool) :=
  match FrenParse.parseFile ⟨0⟩ source with
  | .ok { root := .declarations ds, .. } => some (ds.toList.map fun d => declWellFormed (declTree d))
  | _ => none

def tree? (source : String) : Option Tree :=
  match FrenParse.parseExpression ⟨0⟩ source with
  | .ok { root := .expression e, .. } => some (abstract e)
  | _ => none

/-! ## Printing -/

/-- A printed subtree: its tokens, each with whether it touches the token
before it, and its `shape` by the chapter. -/
structure Printed where
  tokens : List (String × Bool)
  shape : spec.surface.Shape

instance : Inhabited Printed := ⟨⟨[], ⟨.Primary, false⟩⟩⟩

/-- A token after a space. -/
def word (text : String) : String × Bool := (text, false)

def pathTokens (p : Fren.Seq String) : List (String × Bool) :=
  (p.toList.map word).intersperse (word "::")

/-- The tokens of a node, given its printed subtrees
(`syntax.property.print-parse`): the node's tokens in the order of its
production, with a subtree in parentheses exactly where the chapter's `fits?`
says that its `shape` does not fit its `place`. With `full`, the text instead
has what the trees do not distinguish: every subtree in parentheses, a
trailing comma in every list and a leading zero on every numeral. -/
def layerTokens (full : Bool) (node : spec.surface.ExprF Printed) : List (String × Bool) :=
  let child (k : Nat) (c : Printed) : List (String × Bool) :=
    if !full && spec.surface.«fits?» c.shape (spec.surface.place Printed node (Int.ofNat k)) then c.tokens
    else word "(" :: c.tokens ++ [word ")"]
  let list (items : List (List (String × Bool))) : List (String × Bool) :=
    (items.intersperse [word ","]).flatten ++ (if full && !items.isEmpty then [word ","] else [])
  match node with
  | .Boolean b => [word (toString b)]
  | .Integer n => [word ((if full then "0" else "") ++ toString n)]
  | .Name p => pathTokens p
  | .Call p args =>
    pathTokens p ++ [("(", true)] ++ list (args.toList.zipIdx.map fun (a, k) => child k a) ++ [word ")"]
  | .Unary op e => word (spellUnary op) :: child 0 e
  | .Binary op l r => child 0 l ++ [word (spellBinary op)] ++ child 1 r
  | .If c t e => word "if" :: child 0 c ++ [word "then"] ++ child 1 t ++ [word "else"] ++ child 2 e
  | .Let x v b => [word "let", word x, word ":="] ++ child 0 v ++ [word "in"] ++ child 1 b
  | .Match s arms =>
    word "match" :: child 0 s ++ [word "{"] ++
      list (arms.toList.zipIdx.map fun (a, k) => pathTokens a.variant ++ [word "=>"] ++ child (k + 1) a.body) ++
      [word "}"]

/-- A tree printed: each node's tokens by `layerTokens`, and its shape by the
chapter's `shape` of its subtrees' shapes. -/
partial def Tree.printWith (full : Bool) (t : Tree) : Printed :=
  let node := mapLayer (Tree.printWith full) t.layer
  ⟨layerTokens full node, spec.surface.shape (mapLayer (·.shape) node)⟩

/-- The text of `syntax.property.print-parse`. -/
def Tree.print (t : Tree) : Printed := t.printWith false

/-- One space between each two consecutive tokens, but none before a token
that touches. -/
def Printed.text (p : Printed) : String :=
  String.join (p.tokens.zipIdx.map fun ((t, touching), k) => (if k == 0 || touching then "" else " ") ++ t)

/-- The tokens of an accepted expression that its tree keeps: all but each
pair of parentheses that is not a call's, each trailing comma, and the leading
zeros of numerals. A call's `(` is the one after an identifier. -/
def keptTokens (source : String) : List String := Id.run do
  let ts := toks source
  let mut calls : List Bool := []
  let mut out : Array String := #[]
  for (t, i) in ts.toList.zipIdx do
    if t.text == "(" then
      let call := i > 0 && ts[i - 1]?.any (·.kind == .identifier)
      calls := call :: calls
      if call then out := out.push t.text
    else if t.text == ")" then
      match calls with
      | call :: rest =>
        calls := rest
        if call then out := out.push t.text
      | [] => out := out.push t.text
    else if t.text == "," && (ts[i + 1]?.any fun next => next.text == ")" || next.text == "}") then
      pure ()
    else if t.kind == .numeral then out := out.push (toString t.text.toNat!)
    else out := out.push t.text
  return out.toList

/-- A seeded pseudo-random well-formed tree of at most `depth` levels. -/
partial def randomTree (seed : Nat) : Nat → Tree × Nat
  | 0 => let s := lcg seed
    (match s / 2 ^ 33 % 4 with
      | 0 => .name ["x"] | 1 => .integer (s / 2 ^ 40 % 100) | 2 => .boolean (s / 2 ^ 41 % 2 == 0)
      | _ => .name ["E", "A"], s)
  | depth + 1 =>
    let s := lcg seed
    let pick := s / 2 ^ 33 % 12
    if pick < 2 then randomTree s 0 else
    let (a, s) := randomTree s depth
    let (b, s) := randomTree s depth
    let (c, s) := randomTree s depth
    match pick with
    | 2 => (.unary (unaryOps[s / 2 ^ 35 % 2]!) a, s)
    | 3 | 4 | 5 | 6 => (.binary (binaryOps[s / 2 ^ 35 % 14]!) a b, s)
    | 7 => (.ifE a b c, s)
    | 8 => (.letE "v" a b, s)
    | 9 => (.call ["f"] [a, b], s)
    | 10 => (.matchE a [(["E", "A"], b), (["E", "B"], c)], s)
    | _ => (.call ["g"] [a], s)

def randomTrees (count depth seed : Nat) : List Tree := Id.run do
  let mut seed := seed
  let mut out := []
  for _ in [:count] do
    let (t, s) := randomTree seed depth
    seed := s
    out := t :: out
  return out

/-- A seeded pseudo-random file of declarations, printed, with every list
policy, `pub`, paths and member forms; one parameter in twenty has neither
a type nor a `?`, which no file may have. -/
def randomFile (seed : Nat) : String × Nat := Id.run do
  let mut s := seed
  let mut out := ""
  let pick (s : Nat) (n : Nat) : Nat := s / 2 ^ 33 % n
  s := lcg s
  for _ in [:1 + pick s 3] do
    s := lcg s
    let vis := if pick s 2 == 0 then "pub " else ""
    s := lcg s
    let trailing := if pick s 2 == 0 then "," else ""
    s := lcg s
    let params := Id.run do
      let mut ps := []
      let mut s := s
      for _ in [:1 + pick s 3] do
        s := lcg s
        ps := ps ++ [match pick s 20 with
          | 0 => "y" | 1 | 2 | 3 => "b?" | 4 | 5 => "b?: Bool" | 6 => "e: E::T" | _ => "x: Int"]
      return ", ".intercalate ps
    s := lcg s
    let (body, s') := randomTree s 3
    s := s'
    let body := body.print.text
    let (other, s'') := randomTree s 2
    s := lcg s''
    let other := other.print.text
    let expectParams := if pick s 3 == 0 then "" else params ++ trailing
    out := out ++ match pick s 4 with
      | 0 => s!"{vis}mod {if pick s 3 == 0 then "a::b" else "m"}\n"
      | 1 => s!"{vis}enum E \{ A, B{trailing} }\n"
      | 2 => s!"{vis}fn f({params}{trailing}): Int := {body}\n"
      | _ => s!"expect e({expectParams}) \{ assume a: {other} expect c: {body} }\n"
  return (out, s)

def randomFiles (count seed : Nat) : List String := Id.run do
  let mut seed := seed
  let mut out := []
  for _ in [:count] do
    let (f, s) := randomFile seed
    seed := s
    out := f :: out
  return out

/-! ## The checks -/

/-- For each pair of binary operators, an `if` whose `else` branch ends in the
first and is the left operand of the second, and the same at the start of an
`else`: dropping their parentheses makes the operators meet where an `else`
branch ends. -/
def elseTrees : List Tree :=
  let (x, y, z) := (Tree.name ["x"], Tree.name ["y"], Tree.name ["z"])
  binaryOps.flatMap fun a => binaryOps.map fun b =>
    .binary b (.ifE x y (.binary a x y)) (.binary b y z)

/-- Inputs for `grammar_agrees`, as (start nonterminal, text). Bounded: as
an `ExpressionEntry`, every sequence of up to three of `expressionPieces` (30),
every sequence of up to five of `smallExpressionPieces` (8), 1000 random
sequences of 5 to 14 of them, 500 printed random trees and the texts near
them; as a `File`, every sequence of up to three of `declarationPieces` (25),
1000 random sequences, 200 printed random files and the texts near them, and
the chapter's `fren2` and `fren2 rejected` blocks. -/
def grammarInputs (md : String) : List (String × String) :=
  let exprs := (randomTrees 500 4 4049 ++ elseTrees).map (·.print.text)
  let files := randomFiles 200 77
  -- Texts near valid ones first: they find a wrong rule soonest.
  ((exprs ++ exprs.flatMap nearTexts).map ("ExpressionEntry", ·)) ++
  ((files ++ files.flatMap nearTexts ++ ((blocks md "fren2") ++ (blocks md "fren2 rejected")).map (·.2)).map ("File", ·)) ++
  ((sequences expressionPieces 3 ++ sequences smallExpressionPieces 5 ++
      randomSequences expressionPieces 1000 7).map ("ExpressionEntry", ·)) ++
  ((sequences declarationPieces 3 ++ randomSequences declarationPieces 1000 11).map ("File", ·))

-- fren-covers: spec::parsing::grammar_acceptance
--@ reference: syntax.notation.trivia-sensitive
--@ reference: syntax.file.syntax
--@ reference: syntax.declaration.syntax
--@ reference: syntax.declaration.lists
--@ reference: syntax.expression.syntax
--@ reference: parsing.grammar.acceptance
/-- The chapter's grammar, read strictly and run as written, accepts exactly
what the parser accepts, on `grammarInputs`. -/
def grammar_agrees (md : String) (inputs : List (String × String)) : Except String Unit := do
  let rules ← grammarOf md
  for (start, text) in inputs do
    let entry := if start == "File" then Entry.file else .expression
    if grammarAccepts rules start text != parserAccepts entry text then
      throw s!"the grammar and the parser disagree on {start} {repr text}"

/-- The choices and repetitions of the grammar, but those of `ExpressionEntry`
and those under a `!`. -/
partial def G.choices : G → List String
  | .term _ | .nt _ | .neg _ => []
  | .seq gs => gs.flatMap G.choices
  | .alt id gs => (List.range gs.length).map (s!"{id}/{·}") ++ gs.flatMap G.choices
  | .opt id g | .star id g | .plus id g => id :: g.choices

/-- The chapter's `fren2` blocks use every choice and repetition of the
grammar: each alternative of each `|`, and each `?`, `*` and `+` at least once. -/
def examples_cover (md : String) : Except String Unit := do
  let rules ← grammarOf md
  let used := (blocks md "fren2").flatMap fun (_, body) =>
    match run rules (toks body) (.nt "File") 0 with
    | some (_, used) => used
    | none => []
  let missing := (rules.filter (·.1 != "ExpressionEntry")).flatMap (·.2.choices) |>.filter fun c => !(used.contains c)
  unless missing.isEmpty do throw s!"the `fren2` examples use no match of {missing}"

/-- `syntax.expression.terminals`: the grammar's punctuators are exactly
`PUNCTUATORS`, its keywords exactly `GRAMMAR_KEYWORDS`, and its other words
exactly `CONTEXTUAL`. -/
partial def G.terminals : G → List String
  | .term s => [s]
  | .nt _ => []
  | .seq gs | .alt _ gs => gs.flatMap G.terminals
  | .opt _ g | .star _ g | .plus _ g | .neg g => g.terminals

-- fren-covers: spec::surface::grammar_terminals
--@ reference: syntax.expression.terminals
def terminals_agree (md : String) : Except String Unit := do
  let rules ← grammarOf md
  let ts := (rules.flatMap fun (_, g) => g.terminals).eraseDups
  let isWord (t : String) := t.toList.all Char.isAlpha
  let words := ts.filter isWord
  unless decide (spec.lexical.PUNCTUATORS = Fren.FinSet.ofList (ts.filter fun t => !(isWord t))) do
    throw "the grammar's punctuators are not `PUNCTUATORS`"
  unless decide (spec.surface.GRAMMAR_KEYWORDS = Fren.FinSet.ofList (words.filter FrenParse.keywords.contains)) do
    throw "the grammar's keywords are not `GRAMMAR_KEYWORDS`"
  unless decide (spec.surface.CONTEXTUAL = Fren.FinSet.ofList (words.filter fun w => !(FrenParse.keywords.contains w))) do
    throw "the grammar's other words are not `CONTEXTUAL`"

-- fren-covers: spec::parsing::operators
--@ reference: syntax.tree.operators
/-- `syntax.tree.operators`: the parser reads each binary spelling as that
operator and nothing else as a binary operator, among every text of up to
three of the characters `(){},:=<>!+-*%/.?&|`, which includes each punctuator,
the lexer's keywords, `x`, `1` and `assume`; orders the binary operators'
precedences as the chapter's categories rank them; and reads each unary
spelling before an operand as that unary operator. -/
def operators_agree : Bool :=
  let prec (op : SBinary) : Option Nat := (FrenParse.binaryOperator (spellBinary op)).map (·.2)
  let rank (op : SBinary) : Int := spec.surface.rank (spec.surface.binary_category op)
  binaryOps.all (fun op => match FrenParse.binaryOperator (spellBinary op) with
    | some (ast, _) => binaryOf ast == op
    | none => false) &&
  binaryOps.all (fun a => binaryOps.all fun b =>
    match prec a, prec b with
    | some p, some q => (p < q) == (rank a < rank b)
    | _, _ => false) &&
  (strings "(){},:=<>!+-*%/.?&|".toList 3 ++ FrenParse.keywords ++ ["x", "1", "assume"]).all
    (fun s => (FrenParse.binaryOperator s).isSome == (binaryOps.map spellBinary).contains s) &&
  unaryOps.all fun op => exprSexp? (spellUnary op ++ " x") == some s!"(Unary {unaryName op} (Name x))"


-- fren-covers: spec::parsing::expression_trees, spec::surface::print_parse
--@ reference: syntax.property.print-parse
--@ reference: parsing.grammar.trees
/-- `syntax.property.print-parse`: the text of a well-formed tree has exactly
the tokens written, by the actual lexer, and parses back to the tree; dropping
any pair of its parentheses gives a text that is rejected or has another
tree; the text with every subtree in parentheses, trailing commas and leading
zeros has the same tree; conversely, the text of the tree of an accepted
expression has that expression's tokens, apart from pairs of parentheses,
trailing commas and leading zeros; and ill-formed trees do not come back.
Bounded: 1000 seeded random trees of depth at most 5, every pair of binary
operators and every unary operator around binary operands, and seven
ill-formed trees; the converse on those trees' texts in full parentheses and
on the texts near those of 300 more random trees of depth at most 4. -/
def roundtrip_agrees : Bool := Id.run do
  let x := Tree.name ["x"]
  let y := Tree.name ["y"]
  let z := Tree.name ["z"]
  let mut trees := randomTrees 1000 5 2026
  for a in binaryOps do
    for b in binaryOps do
      trees := .binary a (.binary b x y) z :: .binary a x (.binary b y z) :: trees
    for u in unaryOps do
      trees := .unary u (.binary a x y) :: .binary a (.unary u x) y :: .binary a x (.unary u y) :: trees
  let illFormed : List Tree := [.call ["f"] [], .name [], .call [] [x],
    .matchE x [(["A"], y)], .letE "true" x y, .name ["E", "not"], .binary .Add (.name ["if"]) x]
  let same (t : Tree) (text : String) := (tree? text).map (·.sexp) == some t.sexp
  let separated (p : Printed) := (toks p.text).toList.map (·.text) == p.tokens.map (·.1)
  let converse (text : String) := match tree? text with
    | some t => keptTokens t.print.text == keptTokens text
    | none => true
  let direct := trees.all fun t =>
    let printed := t.print
    let text := printed.text
    let full := (t.printWith true).text
    t.wellFormed && separated printed && same t text &&
      -- Dropping a matched pair of parentheses; calls' parentheses included.
      (nearTexts text true).all (fun near => near == text || !same t near) &&
      same t full && converse full
  let near := (randomTrees 300 4 2027).all fun t => (nearTexts t.print.text).all converse
  return direct && near && illFormed.all fun t => !t.wellFormed && !same t t.print.text


/-- A declaration tree printed: its tokens, with each expression printed as
`syntax.property.print-parse` says, and a trailing comma when `trailing`. -/
def declPrint (trailing : Bool) : spec.surface.DeclarationF Tree → String
  | .Module d => s!"{if d.public? then "pub " else ""}mod {pathText d.path}"
  | .Enumeration d =>
    s!"{if d.public? then "pub " else ""}enum {d.name} \{ " ++ ", ".intercalate d.variants.toList ++
      (if trailing then "," else "") ++ " }"
  | .Function d =>
    s!"{if d.public? then "pub " else ""}fn {d.name}(" ++ ", ".intercalate (d.parameters.toList.map paramText) ++
      (if trailing then "," else "") ++ s!"): {typeText d.result} := {d.body.print.text}"
  | .Expectation d =>
    s!"expect {d.name}(" ++ ", ".intercalate (d.parameters.toList.map paramText) ++
      (if trailing && !d.parameters.toList.isEmpty then "," else "") ++ ") { " ++
      " ".intercalate (d.members.toList.map fun m =>
        s!"{match m.kind with | .Assume => "assume" | .Expect => "expect"} {m.label}: {m.body.print.text}") ++ " }"
where
  typeText : spec.surface.TypeName → String
    | .Boolean => "Bool" | .Integer => "Int" | .Named p => pathText p
  paramText (p : spec.surface.Parameter) : String :=
    p.name ++ ((p.annotation.map fun t => ": " ++ typeText t).getD "")

/-- A seeded pseudo-random declaration tree, with random visibility, names,
paths, parameters, types and members. -/
def randomDecl (seed : Nat) : spec.surface.DeclarationF Tree × Nat := Id.run do
  let mut s := lcg seed
  let pick (s n : Nat) : Nat := s / 2 ^ 33 % n
  let names := ["a", "b", "c?", "next_step", "Bool", "Int", "T"]
  let name (s : Nat) := names[pick s 4]!
  let isPub := pick s 2 == 0
  s := lcg s
  let path := Fren.Seq.ofList ((List.range (1 + pick s 3)).map fun i => names[(pick s 7 + i) % 7]!)
  s := lcg s
  let types : List spec.surface.TypeName := [.Boolean, .Integer, .Named (Fren.Seq.ofList ["E"]),
    .Named (Fren.Seq.ofList ["Int", "T"])]
  let params := (List.range (1 + pick s 3)).map fun i =>
    let n := names[(pick s 5 + i) % 4]!
    let t := types[(pick s 11 + i) % 4]!
    (⟨n, if n.endsWith "?" && (pick s 13 + i) % 2 == 0 then none else some t⟩ : spec.surface.Parameter)
  s := lcg s
  let (body, s') := randomTree s 3
  let (other, s'') := randomTree s' 2
  s := lcg s''
  let decl : spec.surface.DeclarationF Tree := match pick s 4 with
    | 0 => .Module ⟨isPub, path⟩
    | 1 => .Enumeration ⟨isPub, name s, Fren.Seq.ofList (names.take (1 + pick s 3))⟩
    | 2 => .Function (.mk! isPub (name s) (Fren.Seq.ofList params) (types[pick s 4]!) body)
    | _ => .Expectation (.mk! (name s) (Fren.Seq.ofList (if pick s 3 == 0 then [] else params))
        (Fren.Seq.ofList [.mk! .Assume "a" other, .mk! .Expect "c" body]))
  return (decl, s)

-- fren-covers: spec::parsing::declaration_trees
--@ reference: syntax.tree.productions
--@ reference: parsing.grammar.declaration-trees
/-- `parsing.grammar.declaration-trees`: a generated declaration tree is
well formed and, printed and parsed, gives back that tree, field for field.
The trees are generated independently of the parser. Bounded: 1000 seeded
random files of one to three declarations, with and without trailing commas,
and eight ill-formed declaration trees, which the chapter's
`declaration_well_formed?` must refuse. -/
def declarations_agree : Bool := Id.run do
  let x := Tree.name ["x"]
  let p : spec.surface.Parameter := ⟨"x", some .Integer⟩
  let illFormed : List (spec.surface.DeclarationF Tree) := [
    .Module ⟨false, Fren.Seq.ofList []⟩,
    .Enumeration ⟨false, "E", Fren.Seq.ofList []⟩,
    .Enumeration ⟨false, "if", Fren.Seq.ofList ["A"]⟩,
    .Function (.mk! false "f" (Fren.Seq.ofList []) .Integer x),
    .Function (.mk! false "f" (Fren.Seq.ofList [⟨"y", none⟩]) .Integer x),
    .Function (.mk! false "f" (Fren.Seq.ofList [p]) (.Named (Fren.Seq.ofList ["Bool"])) x),
    .Function (.mk! false "f" (Fren.Seq.ofList [p]) .Integer (.call ["g"] [])),
    .Expectation (.mk! "e" (Fren.Seq.ofList []) (Fren.Seq.ofList [.mk! .Expect "then" x]))]
  if illFormed.any declWellFormed then return false
  let mut seed := 9091
  for _ in [:1000] do
    let mut decls := []
    for _ in [:1 + seed / 2 ^ 33 % 3] do
      let (d, s) := randomDecl seed
      seed := s
      decls := decls ++ [d]
    unless decls.all declWellFormed do return false
    let trailing := seed % 2 == 0
    let text := "\n".intercalate (decls.map (declPrint trailing))
    let expected := "(File" ++ String.join (decls.map fun d => " " ++ declSexp d) ++ ")"
    if fileSexp? text != some expected then return false
  return true


-- fren-covers: spec::surface::accepted_trees_well_formed
--@ reference: syntax.path.syntax
--@ reference: syntax.tree.productions
--@ reference: syntax.tree.well-formed
/-- `syntax.tree.productions` and `syntax.tree.well-formed`: each line of the
chapter's `fren2 trees` blocks has the tree it states, and the tree of every
expression and file that the parser accepts among `inputs` is well formed.
`check` passes the first 80000 of `grammarInputs`. -/
def trees_agree (md : String) (inputs : List (String × String)) : Except String Unit := do
  for (line, body) in blocks md "fren2 trees" do
    for l in body.splitOn "\n" do
      let [text, expected] := l.splitOn " -- " | throw s!"Syntax.md:{line}: `{l}` is not `text -- tree`"
      let actual := if expected.startsWith "(File" then fileSexp? text else exprSexp? text
      unless actual == some expected do
        throw s!"Syntax.md:{line}: the tree of `{text}` is {actual}"
  for (start, text) in inputs do
    if start == "ExpressionEntry" then
      if let some t := tree? text then
        unless t.wellFormed do throw s!"the tree of {repr text} is not well formed"
    else if let some ds := fileTrees? text then
      unless ds.all id do throw s!"a declaration of {repr text} is not well formed"

-- fren-covers: spec::surface::extent
--@ reference: syntax.property.extent
/-- `syntax.property.extent`: each line `lhs -- rhs` of a `fren2 groups`
block has the same tree on both sides. -/
def groups_agree (md : String) : Except String Unit := do
  for (line, body) in blocks md "fren2 groups" do
    for l in body.splitOn "\n" do
      let [lhs, rhs] := l.splitOn " -- " | throw s!"Syntax.md:{line}: `{l}` is not `lhs -- rhs`"
      unless (exprSexp? lhs).isSome && exprSexp? lhs == exprSexp? rhs do
        throw s!"Syntax.md:{line}: `{lhs}` does not group as `{rhs}`"

/-- The line of a byte offset, from 1. -/
def lineOf (text : String) (offset : Nat) : Nat :=
  ((String.fromUTF8! (text.toUTF8.extract 0 offset)).toList.filter (· == '\n')).length + 1

/-- Each `fren2` block is accepted, and each `fren2 rejected` block is
rejected, with the diagnostic that its `--~ error:` annotation states on the
annotated line; the sentence before the block names the rule it breaks. -/
def examples_agree (md : String) : Except String Unit := do
  for (line, body) in blocks md "fren2" do
    unless parserAccepts .file body do throw s!"Syntax.md:{line}: the parser rejects a `fren2` block"
  let ids := ((md.splitOn "\n").filter (·.startsWith "r[")).map fun l => ((l.drop 2).takeWhile (· != ']')).toString
  let lines := (md.splitOn "\n").toArray
  for (line, body) in blocks md "fren2 rejected" do
    let before := ((lines.extract 0 (line - 1)).toList.reverse.dropWhile (·.trimAscii.isEmpty)
      |>.takeWhile (!·.trimAscii.isEmpty)).getLast?
    unless before.any fun b => ids.any fun id => b.startsWith s!"`{id}`:" do
      throw s!"Syntax.md:{line}: no sentence before the rejected block names the rule it breaks"
    let some (k, note) := (body.splitOn "\n").zipIdx.findSome? (fun (l, k) =>
        match l.splitOn "--~ error: " with | [_, msg] => some (k + 1, msg) | _ => none)
      | throw s!"Syntax.md:{line}: a rejected block has no `--~ error:` annotation"
    match FrenParse.parseFile ⟨0⟩ body with
    | .ok _ => throw s!"Syntax.md:{line}: the parser accepts a rejected block"
    | .error f =>
      unless lineOf body f.diagnostic.span.start == k && "expected " ++ f.diagnostic.expected == note do
        throw s!"Syntax.md:{line}: the parser says {f.diagnostic.render} on line {lineOf body f.diagnostic.span.start}"

-- fren-covers: spec::surface::reserved_names
/-- Each `fren2 unresolved` block parses, and name resolution rejects it with
the message that its `--~ error:` annotation states on the annotated line;
the sentence before the block names the rule it breaks. -/
def unresolved_agree (md : String) : Except String Unit := do
  let ids := ((md.splitOn "\n").filter (·.startsWith "r[")).map fun l => ((l.drop 2).takeWhile (· != ']')).toString
  let lines := (md.splitOn "\n").toArray
  let blocksFound := blocks md "fren2 unresolved"
  if blocksFound.isEmpty then throw "no `fren2 unresolved` block"
  for (line, body) in blocksFound do
    let before := ((lines.extract 0 (line - 1)).toList.reverse.dropWhile (·.trimAscii.isEmpty)
      |>.takeWhile (fun l => !l.trimAscii.isEmpty)).getLast?
    unless before.any fun b => ids.any fun id => b.startsWith s!"`{id}`:" do
      throw s!"Syntax.md:{line}: no sentence before the unresolved block names the rule it breaks"
    let some (k, note) := (body.splitOn "\n").zipIdx.findSome? (fun (l, k) =>
        match l.splitOn "--~ error: " with | [_, msg] => some (k + 1, msg) | _ => none)
      | throw s!"Syntax.md:{line}: an unresolved block has no `--~ error:` annotation"
    match FrenParse.parseFile ⟨0⟩ body with
    | .error f => throw s!"Syntax.md:{line}: the parser rejects an unresolved block: {f.diagnostic.render}"
    | .ok doc => match FrenAstToHir.resolve doc with
      | .ok _ => throw s!"Syntax.md:{line}: name resolution accepts an unresolved block"
      | .error d =>
        unless lineOf body d.span.start == k && d.headline == note do
          throw s!"Syntax.md:{line}: name resolution says `{d.headline}` on line {lineOf body d.span.start}"

/-! ## Mutation control

Each of these changes to the chapter's grammar makes it wrong, and the checks
above must notice: the grammar check, the coverage check or the strict reader
fails on each. -/
def mutants : List (String × String × String) := [
  ("fn-no-trailing-comma", "Parameter (\",\" Parameter)* \",\"? \")\"\n", "Parameter (\",\" Parameter)* \")\"\n"),
  ("call-no-trailing-comma", "Expression (\",\" Expression)* \",\"? \")\"", "Expression (\",\" Expression)* \")\""),
  ("call-empty", "Path TouchingOpen Expression (\",\" Expression)* \",\"? \")\"", "Path TouchingOpen (Expression (\",\" Expression)* \",\"?)? \")\""),
  ("scrutinee-negation", "\"match\" Primary", "\"match\" Negation"),
  ("arm-expression", "Arm         ::= QualifiedPath \"=>\" Iff", "Arm         ::= QualifiedPath \"=>\" Expression"),
  ("arm-unqualified", "Arm         ::= QualifiedPath \"=>\" Iff", "Arm         ::= Path \"=>\" Iff"),
  ("no-compare-lookahead", "Sum (CompareOp Sum)? !CompareOp", "Sum (CompareOp Sum)?"),
  ("no-iff-lookahead", "Or (\"iff\" Or)? !\"iff\"", "Or (\"iff\" Or)?"),
  ("let-definition-expression", "\"let\" Identifier \":=\" Iff \"in\"", "\"let\" Identifier \":=\" Expression \"in\""),
  ("not-once", "Not         ::= \"not\" Not | Comparison", "Not         ::= \"not\" Comparison | Comparison"),
  ("negation-once", "Negation    ::= \"-\" Negation | Primary", "Negation    ::= \"-\" Primary | Primary"),
  ("expect-params-nonempty", "TouchingOpen (Parameter (\",\" Parameter)* \",\"?)? \")\"", "TouchingOpen Parameter (\",\" Parameter)* \",\"? \")\""),
  ("expect-params-no-trailing", "TouchingOpen (Parameter (\",\" Parameter)* \",\"?)? \")\"", "TouchingOpen (Parameter (\",\" Parameter)*)? \")\""),
  ("module-identifier", "\"pub\"? \"mod\" Path", "\"pub\"? \"mod\" Identifier"),
  ("typo", "| Primary\nPrimary", "| Primry\nPrimary"),
  ("unbalanced", "((\"+\" | \"-\") Product)*", "((\"+\" | \"-\") Product*"),
  ("else-optional", "\"then\" Expression \"else\" Expression", "\"then\" Expression (\"else\" Expression)?"),
  ("path-before-call", "Numeral | Call | Path |", "Numeral | Path | Call |"),
  ("member-iff", "Identifier \":\" Expression\n", "Identifier \":\" Iff\n"),
  ("pub-expect", "ExpectationDeclaration ::= \"expect\"", "ExpectationDeclaration ::= \"pub\"? \"expect\""),
  ("question-first", "Parameter              ::= Identifier \":\" Type | QuestionIdentifier", "Parameter              ::= QuestionIdentifier | Identifier \":\" Type"),
  ("question-any", "Parameter              ::= Identifier \":\" Type | QuestionIdentifier", "Parameter              ::= Identifier \":\" Type | Identifier"),
  ("sum-once", "Sum         ::= Product ((\"+\" | \"-\") Product)*", "Sum         ::= Product ((\"+\" | \"-\") Product)?"),
  ("or-once", "Or          ::= And (\"or\" And)*", "Or          ::= And (\"or\" And)?"),
  ("not-dropped", "Not         ::= \"not\" Not | Comparison", "Not         ::= Comparison"),
  ("ge-dropped", "\"<=\" | \">\" | \">=\"", "\"<=\" | \">\""),
  ("type-identifier", "Type          ::= Path", "Type          ::= Identifier"),
  ("enum-empty", "\"{\" Identifier (\",\" Identifier)* \",\"? \"}\"", "\"{\" (Identifier (\",\" Identifier)* \",\"?)? \"}\""),
  ("paren-iff", "| \"(\" Expression \")\" |", "| \"(\" Iff \")\" |"),
  ("remainder-dropped", "(\"*\" | \"div\" | \"%\")", "(\"*\" | \"div\")"),
  ("duplicate-rule", "CompareOp   ::=", "Sum         ::= Product\nCompareOp   ::="),
  ("unread-group", "((\"+\" | \"-\") Product)*", "((\"+\" | \"-\" Product)*"),
  ("stray-character", "Negation    ::= \"-\" Negation", "Negation    ::= \"-\" Negation ;"),
  ("unreachable-rule", "QualifiedPath ::=", "Unused        ::= Path\nQualifiedPath ::=")]

/-- Inputs for the mutation control: the chapter's blocks first, then texts
near printed trees and files, then every sequence of up to three pieces. -/
def mutantInputs (md : String) : List (String × String) :=
  let exprs := (elseTrees ++ randomTrees 200 4 4049).map (·.print.text)
  let files := randomFiles 100 77
  (((blocks md "fren2") ++ (blocks md "fren2 rejected")).map ("File", ·.2)) ++
  ((exprs ++ exprs.flatMap nearTexts).map ("ExpressionEntry", ·)) ++
  ((files ++ files.flatMap nearTexts).map ("File", ·)) ++
  ((sequences expressionPieces 3).map ("ExpressionEntry", ·)) ++
  ((sequences declarationPieces 3).map ("File", ·))

-- fren-covers: spec::parsing::grammar_acceptance
/-- Every mutant breaks a check; a mutant whose text is not found is an error. -/
def mutants_caught (md : String) (inputs : List (String × String)) : Except String Unit := do
  for (name, old, new) in mutants do
    unless (md.splitOn old).length == 2 do throw s!"the mutant `{name}` finds no `{old}` in the chapter"
    let m := md.replace old new
    let caught := (examples_cover m).toBool == false || (grammar_agrees m inputs).toBool == false
    unless caught do throw s!"no check catches the mutant `{name}`"

/-! ## Status names

Each `tested` or `lean` status of the chapter names a declaration that exists. -/
/-- Every check of both chapters, by name, with its failures. -/
def check : IO (Array String) := do
  let lexical ← IO.FS.readFile ("src" / "Spec" / "Language" / "LexicalStructure.md")
  let md ← IO.FS.readFile chapterPath
  let inputs := grammarInputs md
  let mut out := #[]
  for (name, ok) in [("lexer_agrees", lexer_agrees), ("encoding_agrees", encoding_agrees),
      ("numerals_agree", numerals_agree), ("operators_agree", operators_agree),
      ("roundtrip_agrees", roundtrip_agrees), ("declarations_agree", declarations_agree)] do
    unless ok do out := out.push s!"{name} failed"
  for (name, result) in [("pieces_agree", pieces_agree lexical),
      ("grammar_agrees", grammar_agrees md inputs), ("terminals_agree", terminals_agree md),
      ("trees_agree", trees_agree md (inputs.take 80000)), ("groups_agree", groups_agree md),
      ("examples_agree", examples_agree md), ("examples_cover", examples_cover md),
      ("unresolved_agree", unresolved_agree md),
      ("mutants_caught", mutants_caught md (mutantInputs md))] do
    if let .error e := result then out := out.push s!"{name}: {e}"
  return out

end FrenTest.SpecChapters.Syntax
