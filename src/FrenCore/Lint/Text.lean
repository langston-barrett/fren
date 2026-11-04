/-!
# Text comparison for lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

namespace Fren.Core

/-! ## Texts -/

/-- Whether `c` can be in an identifier's component (`Reqs/Lang/Lexical#identifiers`). -/
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '?' || c == '\''

/-- The characters `cs[start:stop]` without the comments outside their
string literals: line comments, and block comments, which nest. Each
comment becomes a space. With `limit? := some n`, it stops once it has `n`
characters from the first that is not whitespace, a prefix of the whole
result, which is all that a caller reading the first lexeme needs. -/
def withoutCommentsIn (cs : Array Char) (start stop : Nat) (limit? : Option Nat := none) : Array Char := Id.run do
  let stop := min stop cs.size
  let mut out : Array Char := #[]
  let mut i := start
  -- The first character of `out` that is not whitespace, once there is one,
  -- and how far `out` has been scanned for it.
  let mut first? : Option Nat := none
  let mut scanned := 0
  -- In a string literal: the number of `#` that end it, if raw.
  let mut str? : Option (Option Nat) := none
  while i < stop do
    if let some limit := limit? then
      while first?.isNone && scanned < out.size do
        if !out[scanned]!.isWhitespace then first? := some scanned
        scanned := scanned + 1
      if let some f := first? then
        if out.size - f ≥ limit then break
    let c := cs[i]!
    match str? with
    | some raw? =>
      out := out.push c
      match raw? with
      | none =>
        if c == '\\' && i + 1 < stop then out := out.push cs[i + 1]!; i := i + 1
        else if c == '"' then str? := none
      | some n =>
        if c == '"' && (List.range n).all (fun k => i + 1 + k < stop && cs[i + 1 + k]! == '#') then
          for _ in [0:n] do out := out.push '#'
          i := i + n
          str? := none
      i := i + 1
    | none =>
      if c == '-' && i + 1 < stop && cs[i + 1]! == '-' then
        while i < stop && cs[i]! != '\n' do i := i + 1
        out := out.push ' '
      else if c == '/' && i + 1 < stop && cs[i + 1]! == '-' then
        let mut depth := 1
        i := i + 2
        while i < stop && depth > 0 do
          if cs[i]! == '/' && i + 1 < stop && cs[i + 1]! == '-' then depth := depth + 1; i := i + 2
          else if cs[i]! == '-' && i + 1 < stop && cs[i + 1]! == '/' then depth := depth - 1; i := i + 2
          else i := i + 1
        out := out.push ' '
      else if c == '"' then
        -- A raw literal is `r`, some `#`, then `"`.
        let mut hashes := 0
        while hashes < i - start && cs[i - 1 - hashes]! == '#' do hashes := hashes + 1
        let raw := i - start ≥ hashes + 1 && cs[i - hashes - 1]! == 'r'
        str? := some (if raw then some hashes else none)
        out := out.push c
        i := i + 1
      else
        out := out.push c
        i := i + 1
  return out

/-- `s` without the comments outside its string literals (`withoutCommentsIn`). -/
def withoutComments (s : String) : String :=
  let cs := s.toList.toArray
  String.ofList (withoutCommentsIn cs 0 cs.size).toList

/-- Whether `s` has a comment outside its string literals. -/
def hasComment (s : String) : Bool := withoutComments s != s

/-- The text `s` as the lints compare it, so that two texts are *written the
same* (`Reqs/Lint#written-the-same`) if these agree: without comments or
whitespace, but for one space between two characters of names, numbers or
keywords, and with string literals, raw ones too, as they are. A text
without whitespace, string literals or the start of a comment is its own
form, and is returned as it is. -/
def writtenForm (s : String) : String := Id.run do
  let plain := (s.foldl (init := (true, ' ')) fun (ok, prev) c =>
    (ok && !c.isWhitespace && c != '"' && !(c == '-' && (prev == '-' || prev == '/')), c)).1
  if plain then return s
  let cs := (withoutComments s).toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let mut space := false
  while i < cs.size do
    let c := cs[i]!
    if c.isWhitespace then
      space := true
      i := i + 1
      continue
    if space && out.back?.any isWordChar && isWordChar c then out := out.push ' '
    space := false
    out := out.push c
    i := i + 1
    if c == '"' then
      -- A raw literal is `r`, some `#`, then `"`, and has no escapes.
      let mut hashes := 0
      while hashes + 1 < out.size && out[out.size - 2 - hashes]! == '#' do hashes := hashes + 1
      let raw := out.size ≥ hashes + 2 && out[out.size - hashes - 2]! == 'r'
      let closes (k : Nat) : Bool :=
        cs[k]! == '"' && (!raw || (List.range hashes).all fun h => cs[k + 1 + h]? == some '#')
      while i < cs.size && !closes i do
        if !raw && cs[i]! == '\\' && i + 1 < cs.size then
          out := out.push cs[i]!
          i := i + 1
        out := out.push cs[i]!
        i := i + 1
      let stop := min cs.size (i + 1 + (if raw then hashes else 0))
      out := out ++ cs.extract i stop
      i := stop
  return String.ofList out.toList

/-- Whether `cs` has, anywhere, the two characters that start a line
comment, or the two that start a block comment: without them,
`withoutComments` leaves a text as it is. -/
def mayHaveComments : List Char → Bool
  | '-' :: '-' :: _ | '/' :: '-' :: _ => true
  | _ :: rest => mayHaveComments rest
  | [] => false

/-- Whether `a` and `b` have the same characters other than whitespace. -/
def sameNonWhitespace : List Char → List Char → Bool
  | c :: a, b => if c.isWhitespace then sameNonWhitespace a b else
    match b.dropWhile Char.isWhitespace with
    | d :: b => c == d && sameNonWhitespace a b
    | [] => false
  | [], b => b.all Char.isWhitespace

/-- Whether `a` and `b` are written the same: whether their `writtenForm`s
agree. Most pairs that a lint compares differ, and are told apart without
computing those forms: `writtenForm` keeps every character of its text but
comments and whitespace, so two texts without comments that have different
characters other than whitespace have different forms. -/
def writtenSame (a b : String) : Bool :=
  let (as, bs) := (a.toList, b.toList)
  if !mayHaveComments as && !mayHaveComments bs && !sameNonWhitespace as bs then false
  else writtenForm a == writtenForm b

/-- Whether two expressions see the same binders of pattern tests, `sa` and
`sb`, as sets (`lint::Scoped`). -/
def sameScope (sa sb : List String) : Bool := sa.all (sb.contains ·) && sb.all (sa.contains ·)

/-- Whether two expressions are written the same in the same scope: their
texts `a` and `b` are written the same, and they see the same binders of
pattern tests, `sa` and `sb` (`lint::Scoped`). -/
def writtenSameIn (a b : String) (sa sb : List String) : Bool := writtenSame a b && sameScope sa sb

/-- `ts` as a list in prose: `` `a` ``, `` `a` and `b` ``, `` `a`, `b` and `c` ``. -/
def proseList (ts : Array String) : String :=
  let qs := ts.map (s!"`{·}`")
  match qs.back? with
  | none => ""
  | some last => if qs.size == 1 then last else s!"{", ".intercalate qs.pop.toList} and {last}"

end Fren.Core
