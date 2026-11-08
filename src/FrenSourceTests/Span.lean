module

public import FrenSource
public meta import FrenSource

namespace FrenSourceTests
open FrenSource

private def body : FileId := ⟨1⟩
private def host : FileId := ⟨2⟩
private def exampleSpan := Span.checked body 1 3 4

#guard "aéz".utf8ByteSize == 4
#guard "é".utf8ByteSize == 2
#guard (Span.checked body 2 2 4).isSome -- Byte bounds do not imply character boundaries.
#guard exampleSpan.map (·.start) == some 1
#guard exampleSpan.map (·.stop) == some 3
#guard (exampleSpan.bind fun s => s.offset 4 host 100 104).map (fun s => (s.file, s.start, s.stop)) == some (host, 101, 103)
#guard Span.checked body 4 4 4 |>.isSome
#guard (Span.checked body 3 1 4).isNone
#guard (Span.checked body 0 5 4).isNone
#guard Span.checked body 1 3 4 != Span.checked host 1 3 4
#guard (exampleSpan.bind fun s => s.offset 4 host 100 103).isNone
#guard (exampleSpan.bind fun s => s.offset 2 host 100 104).isNone

/-- Deterministic smoke check, callable by a future test driver. -/
public def run : IO Unit := do
  unless (exampleSpan.bind fun s => s.offset 4 host 100 104).map (fun s => (s.file, s.start, s.stop)) == some (host, 101, 103) &&
      (Span.checked body 3 1 4).isNone && (Span.checked body 4 4 4).isSome do
    throw <| IO.userError "source span smoke check failed"
end FrenSourceTests
