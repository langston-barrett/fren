module

public import Std

public section
namespace Fren.TextTests

/-- Byte offsets delimit only the replaceable result, never the surrounding text. -/
structure Case where
  name : String
  context : String
  input : String
  expected : Option String
  start : Nat
  stop : Nat
  eol : String
  insertionPrefix : String := ""
  finalEol : Bool := true
  deriving Repr, Inhabited

private structure Line where
  text : String
  start : Nat
  stop : Nat
  eol : String
  deriving Inhabited

private def lines (text : String) : Array Line := Id.run do
  let mut out := #[]
  let mut pos := 0
  let parts := text.splitOn "\n"
  for i in [:parts.length] do
    let raw := parts[i]!
    let hasLF := i + 1 < parts.length
    if !hasLF && raw.isEmpty then break
    let cr := hasLF && raw.endsWith "\r"
    let eol := if cr then "\r\n" else if hasLF then "\n" else ""
    let stop := pos + raw.utf8ByteSize + if hasLF then 1 else 0
    out := out.push ⟨if cr then (raw.dropEnd 1).toString else raw, pos, stop, eol⟩
    pos := stop
  return out

private def suffix (text marker : String) : String := (text.drop marker.length).toString
private def payload (text marker : String) : String :=
  let s := suffix text marker
  if s.startsWith " " then (s.drop 1).toString else s
private def reserved (s : String) : Bool :=
  ["-- case:", "-- context:", "-- result:", "--  "].any (fun marker => s.startsWith marker)
private def trivia (s : String) : Bool := s.trimAscii.toString.isEmpty || s.startsWith "--"
private def slice (bytes : ByteArray) (a b : Nat) : String :=
  String.fromUTF8! (bytes.extract a b)

/-- Column-zero marker lines are reserved, including inside multiline input. There
is no escape syntax. Context is the exact suffix of its marker (spaces included). -/
def parse (text : String) : Except String (Array Case) := do
  let ls := lines text
  let bytes := text.toUTF8
  let mut starts := #[]
  for i in [:ls.size] do
    if ls[i]!.text.startsWith "-- case:" then starts := starts.push i
  let first := starts[0]?.getD ls.size
  for i in [:first] do
    if reserved ls[i]!.text || !trivia ls[i]!.text then
      throw s!"line {i+1}: expected -- case:"
  let mut out := #[]
  let mut names : Array String := #[]
  for k in [:starts.size] do
    let a := starts[k]!
    let b := starts[k+1]?.getD ls.size
    let name := (suffix ls[a]!.text "-- case:").trimAscii.toString
    if name.isEmpty || names.contains name then throw s!"line {a+1}: empty or duplicate case name '{name}'"
    names := names.push name
    let mut i := a + 1
    let mut context := ""
    if i < b && ls[i]!.text.startsWith "-- context:" then
      context := suffix ls[i]!.text "-- context:"
      i := i + 1
    let inputStart := if i < b then ls[i]!.start else ls[a]!.stop
    let mut r := i
    while r < b && !ls[r]!.text.startsWith "-- result:" do
      if reserved ls[r]!.text then throw s!"line {r+1}: misplaced reserved marker"
      r := r + 1
    if r == i then throw s!"case {name}: input needs at least one line"
    let inputStop := if r < b then ls[r]!.start else if b < ls.size then ls[b]!.start else bytes.size
    -- The final physical EOL separates input from the result marker. Exclude it
    -- uniformly, including missing results, so blessing an EOF case without LF
    -- cannot change the callback's input on the next check.
    let rawInput := slice bytes inputStart inputStop
    let input := if rawInput.endsWith "\r\n" then (rawInput.dropEnd 2).toString
      else if rawInput.endsWith "\n" then (rawInput.dropEnd 1).toString else rawInput
    let eol := if ls[a]!.eol.isEmpty then "\n" else ls[a]!.eol
    if r == b then
      out := out.push {
        name := name, context := context, input := input, expected := none, start := inputStop,
        stop := inputStop, eol := eol, insertionPrefix := (if rawInput.endsWith "\n" then "" else eol),
        finalEol := b < ls.size || text.endsWith "\n" }
    else
      let mut result := payload ls[r]!.text "-- result:"
      let mut j := r + 1
      while j < b && ls[j]!.text.startsWith "--  " do
        result := result ++ "\n" ++ suffix ls[j]!.text "--  "
        j := j + 1
      for t in [j:b] do
        if reserved ls[t]!.text || !trivia ls[t]!.text then
          throw s!"line {t+1}: only blank lines and comments may follow a result"
      out := out.push {
        name := name, context := context, input := input, expected := some result,
        start := ls[r]!.start, stop := ls[j-1]!.stop,
        eol := if ls[r]!.eol.isEmpty then eol else ls[r]!.eol,
        finalEol := !ls[j-1]!.eol.isEmpty }
  return out

def render (result : Except String String) : String :=
  match result with
  | .ok s => s
  | .error m => "error: " ++ m

/-- Exact comparison: only physical CRLF in result markers is decoded to LF. -/
def agrees (c : Case) (actual : String) : Bool := c.expected == some actual

def replacement (c : Case) (actual : String) : ByteArray :=
  let parts := actual.splitOn "\n"
  -- An actual CR immediately before a result newline needs a separate physical
  -- CRLF terminator, otherwise decoding LF/CRLF would consume that actual CR.
  let eol := if parts.any (·.endsWith "\r") then "\r\n" else c.eol
  (c.insertionPrefix ++ "-- result: " ++ parts.head! ++
    String.join ((parts.drop 1).map (eol ++ "--  " ++ ·)) ++
    (if c.finalEol then eol else "")).toUTF8

/-- Edits must be in source order and refer to disjoint parsed result spans. -/
def rewrite (original : ByteArray) (edits : Array (Case × String)) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut pos := 0
  for (c, actual) in edits do
    out := out ++ original.extract pos c.start ++ replacement c actual
    pos := c.stop
  return out ++ original.extract pos original.size
end Fren.TextTests
