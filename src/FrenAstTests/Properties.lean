module

meta import FrenAstTests.Text
meta import FrenProp

meta section
namespace FrenAstTests
open FrenAst Plausible
open scoped Plausible.Decorations

private def check (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations)
    [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' {numInst := 400, maxSize := 40, randomSeed := some 100501}
  IO.println s!"AST lexical reconstruction: 400 arbitrary strings, no premises discarded: {result}"
  match result with
  | .success _ => pure ()
  | _ => throw <| IO.userError "AST property failed"

#eval check <| ∀ (source : String) (file : Nat),
  let tape := characterTape ⟨file⟩ source
  emitTape tape == source ∧ ownsSource ⟨file⟩ source tape = true ∧
  ({file := ⟨file⟩, source := "not used", tape, entry := .file,
    root := .declarations #[]} : Document).emit == source

-- A broken emitter and altered partition must actually fail the audit.
#eval show IO Unit from do
  let tape := characterTape ⟨4⟩ "é\r\n"
  unless emitTape (tape.extract 1 tape.size) != "é\r\n" &&
      !ownsSource ⟨5⟩ "é\r\n" tape && !ownsSource ⟨4⟩ "é\r\n!" tape do
    throw <| IO.userError "AST perturbed ownership control survived"

end FrenAstTests
