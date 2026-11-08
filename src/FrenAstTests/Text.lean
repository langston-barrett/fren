module

public import FrenAst
public import FrenTextTests

public section
namespace FrenAstTests
open FrenAst

/-- Construct an independent character-sized partition, not a parser. -/
def characterTape (file : FrenSource.FileId) (source : String) : Array Slice := Id.run do
  let mut offset := 0
  let mut tape := #[]
  for c in source.toList do
    let spelling := String.singleton c
    let stop := offset + spelling.utf8ByteSize
    if let some span := FrenSource.Span.checked file offset stop source.utf8ByteSize then
      tape := tape.push ⟨.trivia, spelling, span⟩
    offset := stop
  return tape

@[fren_text_tests "test/FrenAst"]
def astRunner : Fren.TextTests.Runner := .of
  (fun raw => if raw.trimAscii.toString.isEmpty then .ok () else .error "AST emitter tests have no context")
  fun _ input => do
    let tape := characterTape ⟨3⟩ input
    let doc : Document := ⟨⟨3⟩, "deliberately different source storage", tape, .file, .declarations #[]⟩
    if doc.emit != input || !ownsSource ⟨3⟩ input tape then return .error "emission/ownership"
    return .ok s!"{tape.size} characters; {input.utf8ByteSize} bytes"

end FrenAstTests
