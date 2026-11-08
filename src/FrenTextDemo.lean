module

public import FrenTextTests

public section
namespace Fren.TextDemo

/-- Demonstration syntax only: an optional natural-number initial sum. This is
not Fren binding syntax; the real shared Context parser is still a prerequisite. -/
def parseContext (raw : String) : Except String Nat :=
  let text := raw.trimAscii.toString
  if text.isEmpty then .ok 0
  else match text.toNat? with
    | some n => .ok n
    | none => .error s!"demo context must be a natural number, received:{raw}"

/-- Sum actual multiline natural-number input using the parsed initial sum. -/
def evaluate (initial : Nat) (input : String) : IO (Except String String) := do
  let mut total := initial
  for line in input.trimAscii.toString.splitOn "\n" do
    let text := line.trimAscii.toString
    match text.toNat? with
    | some n => total := total + n
    | none => return .error s!"invalid natural number\n{text}"
  return .ok (toString total)

@[fren_text_tests "test/FrenTextDemo"]
def run : Fren.TextTests.Runner := Fren.TextTests.Runner.of parseContext evaluate
/-- A deliberately byte-sensitive development callback. Empty context is parsed
as Unit; internal physical line endings are observable in the input's size. -/
def byteCount (_ : Unit) (input : String) : IO (Except String String) :=
  pure (.ok (toString input.utf8ByteSize))

@[fren_text_tests "test/FrenTextBytes"]
def bytes : Fren.TextTests.Runner := .of
  (fun raw => if raw.isEmpty then .ok () else .error "byte demo requires empty context") byteCount

end Fren.TextDemo
