-- keep-sorted start
import FrenCore.Lint.Model
import FrenCore.Lint.Text
-- keep-sorted end

/-!
# String literal lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Raw string literals -/

/-- The `#`s around the raw string literal written `t`, `r#"..."#`, and its
body; `none` if `t` is not a raw literal. -/
def rawParts? (t : String) : Option (Nat × List Char) := do
  let 'r' :: cs := t.toList | none
  let hashes := (cs.takeWhile (· == '#')).length
  let '"' :: rest := cs.drop hashes | none
  guard (rest.length ≥ hashes + 1)
  return (hashes, rest.take (rest.length - hashes - 1))

/-- The longest run of `#` directly after a `"` in `body`, or `-1` if it has
no `"`. -/
def longestHashRun : List Char → Int
  | [] => -1
  | '"' :: rest => max (rest.takeWhile (· == '#')).length (longestHashRun rest)
  | _ :: rest => longestHashRun rest

/-- Whether `needless_raw_string_hashes` fires on a raw literal with
`hashes` `#`s, whose body's longest run of `#` after a `"` is `longest`,
and the fewest `#`s it needs: one more than that run, so that no `"` in
the body is followed by as many (`lint::needless_raw_string_hashes`). -/
def needlessRawHashes (hashes : Nat) (longest : Int) : Bool × Int := (hashes > longest + 1, longest + 1)

/-- The raw literal written `t`, with the fewest `#`s it needs, if
`needless_raw_string_hashes` fires on it. -/
def fewerHashes? (t : String) : Option String := do
  let (hashes, body) ← rawParts? t
  let (fires, fewest) := needlessRawHashes hashes (longestHashRun body)
  guard fires
  let hs := String.ofList (List.replicate fewest.toNat '#')
  return s!"r{hs}\"{String.ofList body}\"{hs}"

/-- A raw literal with more `#`s than it needs, as the text of its fix. -/
def needlessRawHashesMsg (fixed : String) : Msg :=
  { code? := some Lint.needlessRawStringHashes.code, headline := "this raw string literal has more `#`s than it needs"
    label? := some "fewer `#`s would do"
    notes := #["note: a raw literal needs one `#` more than the longest run of `#` after a `\"` in it, and none without a `\"`"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-! ## Invisible characters -/

/-- Whether `invisible_characters` reports the character whose code point is
`n`, in a comment if `comment`, or else in a string literal: a
bidirectional control or U+FEFF anywhere, and a zero-width or invisible
character in a literal (`lint::invisible_character`). -/
def invisibleCode (comment : Bool) (n : Nat) : Bool :=
  (0x202A ≤ n && n ≤ 0x202E) || (0x2066 ≤ n && n ≤ 0x2069) || n == 0xFEFF
    || (!comment && (n == 0x00AD || n == 0x200B || n == 0x2060))

/-- `U+XXXX`, the code point of `c`. -/
def codePoint (c : Char) : String :=
  let h := (String.ofList (Nat.toDigits 16 c.toNat)).toUpper
  "U+" ++ String.ofList (List.replicate (4 - min 4 h.length) '0') ++ h

/-- The name of a character that `invisible_characters` reports. -/
def invisibleName (c : Char) : String :=
  match c.toNat with
  | 0x00AD => "soft hyphen"
  | 0x200B => "zero width space"
  | 0x2060 => "word joiner"
  | 0x202A => "left-to-right embedding"
  | 0x202B => "right-to-left embedding"
  | 0x202C => "pop directional formatting"
  | 0x202D => "left-to-right override"
  | 0x202E => "right-to-left override"
  | 0x2066 => "left-to-right isolate"
  | 0x2067 => "right-to-left isolate"
  | 0x2068 => "first strong isolate"
  | 0x2069 => "pop directional isolate"
  | _ => "zero width no-break space"

/-- The escape of `c` in a string literal, `\uXXXX`. -/
def unicodeEscape (c : Char) : String := "\\u" ++ (codePoint c).drop 2

/-- The text between the quotes of the raw string literal written `t`,
`r"..."` or `r#"..."#`, or `none` if it is not raw. -/
def rawBody? (t : String) : Option String :=
  if t.startsWith "r" then
    -- The body is between the first `"` and the last.
    some ((t.drop 1).toString.dropWhile (· == '#') |>.toString.drop 1 |>.toString.dropEndWhile (· == '#')
      |>.toString.dropEnd 1 |>.toString)
  else none

/-- The string literal written `t`, with each character for which `esc`
holds written as an escape. A raw literal, which has no escapes, becomes an
ordinary one, with `\\` and `\"` for its `\` and `"`. -/
def escapedLiteral (esc : Char → Bool) (t : String) : String :=
  let escape (c : Char) := if esc c then unicodeEscape c else c.toString
  match rawBody? t with
  | some cs =>
    "\"" ++ String.join (cs.toList.map fun c => if c == '\\' then "\\\\" else if c == '"' then "\\\"" else escape c)
      ++ "\""
  | none => String.join (t.toList.map escape)

/-- `invisible_characters` on a comment, if `comment`, or a string literal,
written `t`: the characters it reports, and `t` with each removed from a
comment or written as an escape in a literal. A raw literal, which has no
escapes, becomes an ordinary one. `none` if it reports none. -/
def invisibleFix? (comment : Bool) (t : String) : Option (Array Char × String) := do
  let found := t.toList.toArray.filter (invisibleCode comment ·.toNat)
  guard !found.isEmpty
  if comment then return (found, String.ofList (t.toList.filter (!invisibleCode comment ·.toNat)))
  return (found, escapedLiteral (invisibleCode false ·.toNat) t)

/-- A comment, if `comment`, or a string literal, with the characters
`found`, whose fix is `fixed`. -/
def invisibleMsg (comment : Bool) (found : Array Char) (fixed : String) : Msg :=
  let distinct := found.foldl (init := #[]) fun acc c => if acc.contains c then acc else acc.push c
  let names := distinct.map fun c => s!"`{codePoint c}` ({invisibleName c})"
  let what := if comment then "comment" else "string literal"
  let headline := if distinct.size == 1 then s!"this {what} contains an invisible character, {names[0]!}"
    else s!"this {what} contains invisible characters: {", ".intercalate names.toList}"
  let control := distinct.any (invisibleCode true ·.toNat)
  let notes := if control then #["note: a bidirectional control can make the text read differently from what it means"]
    else #["note: it cannot be seen, so it is probably not meant"]
  let msg := if comment then (if found.size == 1 then "remove it" else "remove them")
    else if found.size == 1 then "write it as an escape" else "write them as escapes"
  { code? := some Lint.invisibleCharacters.code, headline, label? := some (if control then "may not read as it is written" else "contains what cannot be seen")
    notes, fixes := #[{ msg, replacement := fixed }] }

/-! ## Restricted literals -/

/-- Whether `needless_raw_strings` fires on a string literal, if it is
`raw`, from whether its contents have a `\` or a `"`
(`lint::needless_raw_strings`). -/
def needlessRawStrings (raw backslash quote : Bool) : Bool := raw && !backslash && !quote

/-- A raw string literal that needs no escapes, whose fix is `fixed`. -/
def needlessRawMsg (fixed : String) : Msg :=
  { code? := some Lint.needlessRawStrings.code, headline := "this raw string literal needs no escapes"
    label? := some "has no `\\` and no `\"`"
    notes := #["note: an ordinary literal of the same characters has the same value"]
    fixes := #[{ msg := "write it as an ordinary literal", replacement := fixed }] }

/-- Whether `non_ascii_literal` reports the character whose code point is
`n`, and whether an escape can write it (`lint::non_ascii_literal`). -/
def nonAscii (n : Nat) : Bool × Bool := (n ≥ 0x80, n ≤ 0xFFFF)

/-- A string literal with the non-ASCII characters `found`, whose fix, if
an escape can write each, is `fixed?`. -/
def nonAsciiMsg (found : Array Char) (fixed? : Option String) : Msg :=
  let distinct := found.foldl (init := #[]) fun acc c => if acc.contains c then acc else acc.push c
  let names := distinct.map fun c => s!"`{codePoint c}`"
  let headline := if distinct.size == 1 then s!"this string literal contains a non-ASCII character, {names[0]!}"
    else s!"this string literal contains non-ASCII characters: {", ".intercalate names.toList}"
  let beyond := distinct.filter fun c => !(nonAscii c.toNat).2
  let notes := if beyond.isEmpty then #[] else
    #[s!"note: {proseList (beyond.map codePoint)} {if beyond.size == 1 then "is" else "are"} beyond `U+FFFF`, which `\\uHHHH` cannot write, so this has no fix"]
  let msg := if found.size == 1 then "write it as an escape" else "write them as escapes"
  { code? := some Lint.nonAsciiLiteral.code, headline, label? := some "not ASCII", notes
    fixes := fixed?.toArray.map fun replacement => { msg, replacement } }

/-- The lints of the `restriction` group on the string literal written
`t`: `needless_raw_strings` and `non_ascii_literal`. -/
def literalMsgs (t : String) : Array (Lint × Msg) :=
  let raw := match rawBody? t with
    | some body =>
      if needlessRawStrings true (body.contains '\\') (body.contains '"') then
        #[(.needlessRawStrings, needlessRawMsg ("\"" ++ body ++ "\""))]
      else #[]
    | none => #[]
  let reported (c : Char) := (nonAscii c.toNat).1
  let found := t.toList.toArray.filter reported
  let fixed? := if found.all fun c => (nonAscii c.toNat).2 then some (escapedLiteral reported t) else none
  raw ++ if found.isEmpty then #[] else #[(.nonAsciiLiteral, nonAsciiMsg found fixed?)]

end Fren.Core
