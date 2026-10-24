-- keep-sorted start
import FrenCore.Syntax
-- keep-sorted end

/-!
# Lexer for `.fren` files

Mirrors Lean's lexing of Fren specs: `--` and nested `/- -/` comments,
identifiers that may end in `?`, and the tokens of `Fren.Lang`.
-/

namespace FrenCli

/-- A source range, as character offsets. -/
structure Span where
  start : Nat
  stop : Nat
  deriving Inhabited, Repr, BEq

def Span.to (a b : Span) : Span := { start := a.start, stop := b.stop }

inductive Tok where
  | ident (s : String)
  | num (s : String)
  /-- A string literal, unescaped. -/
  | str (s : String)
  /-- A reserved word or a symbol. -/
  | kw (s : String)
  | eof
  deriving Inhabited, Repr, BEq

def Tok.describe : Tok → String
  | .ident s => s!"identifier `{s}`"
  | .num s => s!"number `{s}`"
  | .str _ => "string literal"
  | .kw s => if s.all Char.isAlpha then s!"keyword `{s}`" else s!"`{s}`"
  | .eof => "end of file"

structure Token where
  tok : Tok
  span : Span
  /-- A line ends between the previous token and this one: a membership's
  `in` cannot start a line (`Reqs/Lang/Lexical#keywords`). -/
  nlBefore : Bool := false
  deriving Inhabited

/-- Reserved where `Fren.Lang` is open (plus Lean's `in`, `if`, `then`,
`else`, `match` and `forall`): `lang::reserved_word`. Other Fren keywords
(`when`, `out`, `req`, ...) are contextual and lexed as identifiers. -/
def reserved : List String :=
  ["mod", "use", "pub", "enum", "struct", "type", "fn", "const", "comp", "expect", "impl", "interp", "tested", "trusted", "iff", "and", "or", "union", "inter", "minus", "subset", "join", "in", "if", "then", "else", "match", "forall"]

/-- The punctuators (`Reqs/Lang/Lexical#punctuators`), longest first.
Includes tokens Fren doesn't use but Lean lexes (`==`, `&&`, `||`), so that
errors name them as Lean's do. `.` is only the one after `)` or `}` that
reads a field; after a name, it is part of the name. -/
def punctuators : List String :=
  ["::*", "::{", "::", "==", "=>", "&&", "||", "|", "!=", "<=", ">=", ":=", "{", "}", "(", ")", "[", "]", ",", ":", ".", "*", "=", "<", ">", "++", "+", "-"]

def lexCommands : List String := ["#fren_check", "#fren_trace"]

structure LexError where
  span : Span
  msg : Fren.Core.Msg

def unterminatedString : Fren.Core.Msg :=
  { code? := some "F0103", headline := "unterminated string literal", label? := some "string starts here"
    notes := #["note: a string literal ends with `\"` on the same line"] }

/-- `[A-Za-z_]`: starts an identifier (`lang::identifier`). -/
def isIdStart (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'

/-- `[A-Za-z0-9_']`: continues an identifier. -/
def isIdRest (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '\''

/-- How many characters at `i` continue an identifier whose last character
is `last`, or `0` where it ends (`lang::identifier_end`): a character of an
identifier, a final `?`, or a `.` and the start of another component. -/
def identExtends (src : Array Char) (last : Char) (i : Nat) : Nat :=
  if last == '?' then 0 else
  match src[i]? with
  | some c =>
    if isIdRest c || c == '?' then 1
    else if c == '.' && (src[i + 1]?).any isIdStart then 2
    else 0
  | none => 0

/-- Where the identifier that starts at `i` ends: like Lean, `a.b` is one
identifier, of two components (`lang::identifier`). -/
def identEnd (src : Array Char) (i : Nat) : Nat := go src[i]! (i + 1)
where
  go (last : Char) (j : Nat) : Nat :=
    if h : j < src.size then
      match identExtends src last j with
      | 0 => j
      | k + 1 => go src[j + k]! (j + k + 1)
    else j
  termination_by src.size - j

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
  s.toList.zipIdx.all fun (c, k) => src[i + k]? == some c

/-- The punctuator at `i`: the longest, by maximal munch, since
`punctuators` is longest first (`lang::punctuator_end`). -/
def punctuatorAt (src : Array Char) (i : Nat) : Option String :=
  punctuators.find? (occursAt src i)

/-- The tokens of `src`, and the spans of its comments. -/
def lexWithComments (src : Array Char) : Except LexError (Array Token × Array Span) := Id.run do
  let n := src.size
  let at? (i : Nat) : Option Char := src[i]?
  let startsWith := occursAt src
  let mut toks : Array Token := #[]
  let mut comments := #[]
  let mut i := 0
  while i < n do
    let c := src[i]!
    if c.isWhitespace then
      i := i + 1
    else if startsWith i "--" then
      let start := i
      while i < n && src[i]! != '\n' do i := i + 1
      comments := comments.push ⟨start, i⟩
    else if startsWith i "/-" then
      let start := i
      let mut depth := 0
      repeat
        if i ≥ n then return .error { span := ⟨start, start + 2⟩, msg := {
          code? := some "F0102", headline := "unterminated block comment", label? := some "comment starts here"
          notes := #["note: block comments nest, so each `/-` needs its own `-/`"] } }
        if startsWith i "/-" then depth := depth + 1; i := i + 2
        else if startsWith i "-/" then
          depth := depth - 1; i := i + 2
          if depth == 0 then break
        else i := i + 1
      comments := comments.push ⟨start, i⟩
    else if c == 'r' && (at? (i + 1) == some '"' || at? (i + 1) == some '#') then
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
      toks := toks.push { tok := .str (String.ofList (src.extract bodyStart i).toList), span := ⟨start, i + close.length⟩ }
      i := i + close.length
    else if isIdStart c then
      let start := i
      i := identEnd src i
      let s := String.ofList (src.extract start i).toList
      toks := toks.push { tok := if reserved.contains s then .kw s else .ident s, span := ⟨start, i⟩ }
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
      toks := toks.push { tok := .str s, span := ⟨start, i⟩ }
    else if c.isDigit then
      let start := i
      while i < n && src[i]!.isDigit do i := i + 1
      toks := toks.push { tok := .num (String.ofList (src.extract start i).toList), span := ⟨start, i⟩ }
    else
      match lexCommands.find? (startsWith i) <|> punctuatorAt src i with
      | some s =>
        toks := toks.push { tok := .kw s, span := ⟨i, i + s.length⟩ }
        i := i + s.length
      | none =>
        if startsWith i "//" then
          return .error { span := ⟨i, i + 2⟩, msg := {
            code? := some "F0101", headline := "unexpected characters `//`", label? := some "not a comment in Fren"
            fixes := #[{ msg := "comments start with `--`", replacement := "--" }] } }
        if c == '!' || c == '/' || c == '%' then
          return .error { span := ⟨i, i + 1⟩, msg := Fren.Core.foreignOpMsg c.toString }
        let msg : Fren.Core.Msg :=
          { code? := some "F0101", headline := s!"unexpected character `{c}`", label? := some "not part of Fren's syntax" }
        let msg := match c with
          | '#' => { msg with fixes := #[{ msg := "comments start with `--`", replacement := "--" }] }
          | '&' => { msg with fixes := #[{ msg := "use `and`", replacement := "and" }] }
          | ';' => { msg with notes := #["note: Fren has no statement separators"], fixes := #[{ msg := "remove it", replacement := "" }] }
          | _ => msg
        return .error { span := ⟨i, i + 1⟩, msg }
  toks := toks.push { tok := .eof, span := ⟨n, n⟩ }
  let marked := toks.mapIdx fun k t =>
    let prev := if k == 0 then 0 else toks[k - 1]!.span.stop
    { t with nlBefore := (src.extract prev t.span.start).contains '\n' }
  return .ok (marked, comments)

def lex (src : Array Char) : Except LexError (Array Token) := (·.1) <$> lexWithComments src

end FrenCli
