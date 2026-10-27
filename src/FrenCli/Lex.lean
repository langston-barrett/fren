-- keep-sorted start
import FrenCore.Lexical
import FrenCore.Syntax
import Std.Data.HashMap
import Std.Data.HashSet
-- keep-sorted end

/-!
# Lexer for `.fren` files

Mirrors Lean's lexing of Fren specs: `--` and nested `/- -/` comments,
identifiers that may end in `?`, then `!`, and the tokens of `Fren.Lang`.
-/

namespace FrenCli

/-- A source range, as character offsets. -/
structure Span where
  start : Nat
  stop : Nat
  deriving Inhabited, Repr, BEq, Hashable

def Span.to (a b : Span) : Span := { start := a.start, stop := b.stop }

inductive Tok where
  | ident (s : String)
  /-- An integer literal, as written, and its value. -/
  | num (s : String) (value : Nat)
  /-- A string literal, unescaped. -/
  | str (s : String)
  /-- A reserved word or a symbol. -/
  | kw (s : String)
  | eof
  deriving Inhabited, Repr, BEq

def Tok.describe : Tok → String
  | .ident s => s!"identifier `{s}`"
  | .num s _ => s!"number `{s}`"
  | .str _ => "string literal"
  | .kw s => if s.all Char.isAlpha then s!"keyword `{s}`" else s!"`{s}`"
  | .eof => "end of file"

structure Token where
  tok : Tok
  span : Span
  /-- A line ends between the previous token and this one: a membership's
  `in` and a remainder's `mod` cannot start a line
  (`Reqs/Lang/Lexical#keywords`). -/
  nlBefore : Bool := false
  deriving Inhabited

/-- The reserved words (`Fren.Core.reservedWords`): `lang::reserved_word`. -/
def reserved : List String := Fren.Core.reservedWords

/-- The punctuators (`Reqs/Lang/Lexical#punctuators`), longest first.
Includes tokens Fren doesn't use but Lean lexes (`==`, `&&`, `||`, `<-`), so
that errors name them as Lean's do. `.` is only the one after `)` or `}` that
reads a field; after a name, it is part of the name. -/
def punctuators : List String :=
  ["::*", "::{", "..=", "::", "..", "==", "=>", "&&", "||", "|", "!=", "<=", "<-", "->", ">=", ":=", "{", "}", "(", ")", "[", "]", ",", ":", ".", "*", "=", "<", ">", "++", "+", "-"]

def lexCommands : List String := ["#fren_check", "#fren_trace"]

structure LexError where
  span : Span
  msg : Fren.Core.Msg
  deriving Inhabited

def unterminatedString : Fren.Core.Msg :=
  { code? := some "F0103", headline := "unterminated string literal", label? := some "string starts here"
    notes := #["note: a string literal ends with `\"` on the same line"] }

/-- The value of a hexadecimal digit, `[0-9a-fA-F]`. -/
def hexValue? (d : Char) : Option Nat :=
  if '0' ≤ d && d ≤ '9' then some (d.toNat - '0'.toNat)
  else if 'a' ≤ d && d ≤ 'f' then some (d.toNat - 'a'.toNat + 10)
  else if 'A' ≤ d && d ≤ 'F' then some (d.toNat - 'A'.toNat + 10)
  else none

/-- The escape sequence whose `\` is just before `i`: the character it
stands for, and its length with the `\` (`lang::escape_sequence`). -/
def escapeAt (src : Array Char) (i : Nat) : Option (Char × Nat) :=
  let hex (k : Nat) : Option Nat := (List.range k).foldlM (init := 0) fun acc j => do
    return acc * 16 + (← hexValue? (← src[i + 1 + j]?))
  match src[i]? with
  | some 'n' => some ('\n', 2)
  | some 't' => some ('\t', 2)
  | some 'r' => some ('\r', 2)
  | some '\\' => some ('\\', 2)
  | some '"' => some ('"', 2)
  | some '\'' => some ('\'', 2)
  | some 'x' => (hex 2).map (Char.ofNat ·, 4)
  | some 'u' => (hex 4).map (Char.ofNat ·, 6)
  | _ => none

/-- Whether `s` is in `src` at `i`. -/
def occursAt (src : Array Char) (i : Nat) (s : String) : Bool :=
  -- The first character first, which rules out most of `punctuators`
  -- without reading the rest.
  s.isEmpty || (src[i]? == some s.front && (s.foldl (fun (ok, k) c => (ok && src[k]? == some c, k + 1)) (true, i)).1)

/-- The punctuator at `i`: the longest, by maximal munch, since
`punctuators` is longest first (`lang::punctuator_end`). -/
def punctuatorAt (src : Array Char) (i : Nat) : Option String := do
  (punctuatorsByFirst[← src[i]?]?.getD []).find? (occursAt src i)
where
  /-- `punctuators` by their first character, each list in the same order,
  so that the first of them that occurs is the first of `punctuators` that
  does: one that does not start with `src[i]` cannot occur at `i`. -/
  punctuatorsByFirst : Std.HashMap Char (List String) :=
    punctuators.foldr (init := {}) fun p m => m.alter p.front fun ps? => some (p :: ps?.getD [])

/-- `reserved`, as a set, which an identifier is looked up in. -/
def reservedSet : Std.HashSet String := .ofList reserved

/-- Where the block comment that starts at `start` ends, after its closer,
counting the comments nested in it; `none` if it does not. -/
def blockCommentEnd (src : Array Char) (start : Nat) : Option Nat := Id.run do
  let mut i := start
  let mut depth := 0
  repeat
    if i ≥ src.size then return none
    if occursAt src i "/-" then depth := depth + 1; i := i + 2
    else if occursAt src i "-/" then
      depth := depth - 1; i := i + 2
      if depth == 0 then break
    else i := i + 1
  return some i

/-- The token that starts with `c`, at `i`, which neither whitespace nor a
comment starts, and where it ends; or the error there. -/
def tokenAt (src : Array Char) (i : Nat) (c : Char) : Except LexError (Token × Nat) := Id.run do
  let n := src.size
  let at? (i : Nat) : Option Char := src[i]?
  let startsWith := occursAt src
  -- `String.ofList (src.extract a b).toList`, without the list.
  let text (a b : Nat) : String := src.foldl (·.push ·) "" a b
  let mut i := i
  if c == 'r' && (at? (i + 1) == some '"' || at? (i + 1) == some '#') then
    -- A raw literal, `r"..."` or `r#"..."#`, with as many `#`s closing it.
    let start := i
    i := i + 1
    let mut hashes := 0
    while at? i == some '#' do hashes := hashes + 1; i := i + 1
    if at? i != some '"' then
      return .error { span := ⟨start, i⟩, msg := unterminatedString }
    i := i + 1
    let close := "\"" ++ String.ofList (List.replicate hashes '#')
    let bodyStart := i
    while i < n && !startsWith i close do
      if src[i]! == '\n' then return .error { span := ⟨start, i⟩, msg := unterminatedString }
      i := i + 1
    if i ≥ n then return .error { span := ⟨start, i⟩, msg := unterminatedString }
    return .ok ({ tok := .str (text bodyStart i), span := ⟨start, i + close.length⟩ }, i + close.length)
  else if Fren.Core.isLeanIdStart c then
    let start := i
    if Fren.Core.isIdStart c then i := Fren.Core.identEnd src i
    -- Where Lean would read further, as it does all of an identifier that
    -- Fren's rule does not start, the two front ends would differ.
    let lean := Fren.Core.leanIdentEnd src start
    if lean > i then
      let lexeme := String.ofList (src.extract start lean).toList
      -- An unclosed `«` runs to the end of the input: mark only its line.
      let stop := ((src.extract start lean).findIdx? (· == '\n')).map (start + ·) |>.getD lean
      return .error { span := ⟨start, stop⟩, msg := Fren.Core.leanIdentifierMsg lexeme (src[lean]? == some '=') }
    let s := text start i
    return .ok ({ tok := if reservedSet.contains s then .kw s else .ident s, span := ⟨start, i⟩ }, i)
  else if c == '"' then
    -- Lean's escapes (`Lang/Lexical.md`).
    let start := i
    i := i + 1
    let mut s := ""
    repeat
      match at? i with
      | none | some '\n' => return .error { span := ⟨start, i⟩, msg := unterminatedString }
      | some '"' => i := i + 1; break
      | some '\\' =>
        let some (ch, k) := escapeAt src (i + 1)
          | return .error { span := ⟨i, i + 2⟩, msg := {
              code? := some "F0115", headline := "unknown escape in a string literal", label? := some "not an escape"
              notes := #["note: the escapes are `\\\\`, `\\\"`, `\\'`, `\\n`, `\\t`, `\\r`, `\\xHH` and `\\uHHHH`",
                "help: for a literal `\\`, write `\\\\`, or use a raw literal, `r\"...\"`"] } }
        s := s.push ch
        i := i + k
      | some ch => s := s.push ch; i := i + 1
    return .ok ({ tok := .str s, span := ⟨start, i⟩ }, i)
  else if Fren.Core.isDecimalDigit c then
    let start := i
    i := Fren.Core.integerEnd src i
    let s := text start i
    -- Both halves of the rule: well formed, and Lean decodes it.
    let some v := if Fren.Core.integerLiteral s then Fren.Core.integerValue? s else none
      | return .error { span := ⟨start, i⟩, msg := Fren.Core.malformedIntegerMsg s }
    return .ok ({ tok := .num s v, span := ⟨start, i⟩ }, i)
  else
    match lexCommands.find? (startsWith i) <|> punctuatorAt src i with
    | some s => return .ok ({ tok := .kw s, span := ⟨i, i + s.length⟩ }, i + s.length)
    | none =>
      if startsWith i "//" then
        return .error { span := ⟨i, i + 2⟩, msg := {
          code? := some "F0101", headline := "unexpected characters `//`", label? := some "not a comment in Fren"
          fixes := #[{ msg := "comments start with `--`", replacement := "--" }] } }
      if c == '!' || c == '/' || c == '%' then
        let spaceBefore := i == 0 || src[i - 1]!.isWhitespace
        let spaceAfter := (src[i + 1]?.map Char.isWhitespace).getD true
        return .error { span := ⟨i, i + 1⟩, msg := Fren.Core.foreignOpMsg c.toString spaceBefore spaceAfter }
      let msg : Fren.Core.Msg :=
        { code? := some "F0101", headline := s!"unexpected character `{c}`", label? := some "not part of Fren's syntax" }
      let msg := match c with
        | '#' => { msg with fixes := #[{ msg := "comments start with `--`", replacement := "--" }] }
        | '&' => { msg with fixes := #[{ msg := "use `and`", replacement := "and" }] }
        | ';' => { msg with notes := #["note: Fren has no statement separators"], fixes := #[{ msg := "remove it", replacement := "" }] }
        | _ => msg
      return .error { span := ⟨i, i + 1⟩, msg }

/-- The tokens of `src` from `i` on, after `toks`, and the spans of its
comments, after `comments`: a tail-recursive loop, which the compiler makes
a loop without allocating a closure for each step. -/
partial def lexFrom (src : Array Char) (i : Nat) (toks : Array Token) (comments : Array Span) :
    Except LexError (Array Token × Array Span) :=
  if h : i < src.size then
    let c := src[i]
    if c.isWhitespace then lexFrom src (i + 1) toks comments
    -- `startsWith i "--"` and `startsWith i "/-"`, from `c`.
    else if c == '-' && src[i + 1]? == some '-' then
      let stop := lineEnd i
      lexFrom src stop toks (comments.push ⟨i, stop⟩)
    else if c == '/' && src[i + 1]? == some '-' then
      match blockCommentEnd src i with
      | some stop => lexFrom src stop toks (comments.push ⟨i, stop⟩)
      | none => .error { span := ⟨i, i + 2⟩, msg := {
          code? := some "F0102", headline := "unterminated block comment", label? := some "comment starts here"
          notes := #["note: block comments nest, so each `/-` needs its own `-/`"] } }
    else match tokenAt src i c with
      | .ok (t, stop) => lexFrom src stop (toks.push t) comments
      | .error e => .error e
  else .ok (toks, comments)
where
  /-- Where the line of `i` ends, at its `\n` or the end of `src`. -/
  lineEnd (i : Nat) : Nat := if i < src.size && src[i]! != '\n' then lineEnd (i + 1) else i

/-- The tokens of `src`, and the spans of its comments. -/
def lexWithComments (src : Array Char) : Except LexError (Array Token × Array Span) := do
  let (toks, comments) ← lexFrom src 0 #[] #[]
  let toks := toks.push { tok := .eof, span := ⟨src.size, src.size⟩ }
  -- Whether a line ends between a token and the one before it, read in
  -- place: `src.any` over the range is `contains` of its `extract`.
  let marked := toks.mapIdx fun k t =>
    let prev := if k == 0 then 0 else toks[k - 1]!.span.stop
    { t with nlBefore := src.any (· == '\n') prev t.span.start }
  return (marked, comments)

def lex (src : Array Char) : Except LexError (Array Token) := (·.1) <$> lexWithComments src

end FrenCli
