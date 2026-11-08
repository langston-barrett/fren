module

public import FrenTextTests.Format

public section
namespace Fren.TextTests

/-- Development-only adapter. `Context` is an honest parsed type supplied by the
library; the shared Fren Context adapter awaits FrenParse/FrenAst. -/
structure Runner where
  execute : String → String → IO (Except String String)

/-- Parse context exactly once and pass its typed value to the real callback.
Parsing failures use the same error rendering as callback failures. -/
def Runner.of {Context : Type} (parseContext : String → Except String Context)
    (run : Context → String → IO (Except String String)) : Runner := ⟨fun raw input => do
  match parseContext raw with
  | .error m => return .error m
  | .ok context => run context input⟩

instance : Inhabited Runner := ⟨Runner.of (fun _ => .ok ()) (fun _ _ => pure (.ok ""))⟩

structure Registered where
  directory : String
  runner : Runner
  deriving Inhabited

/-- Only flat test/<Library> directories can be registered. -/
def validDirectory (path : String) : Bool :=
  match path.splitOn "/" with
  | ["test", lib] => !lib.isEmpty && lib.toList.all (fun c => c.isAlphanum || c == '_')
  | _ => false

structure Options where
  filter : String := ""
  bless : Bool := false

structure Summary where
  selected : Nat := 0
  failed : Nat := 0
  changed : Nat := 0
  diagnostics : Array String := #[]
  deriving Repr

private def plain (path : System.FilePath) (kind : IO.FS.FileType) : IO Unit := do
  unless (← path.symlinkMetadata).type == kind do
    throw <| IO.userError s!"{path}: expected regular file/directory; symlinks are unsupported"

/-- Resolve only registered paths below the current project. Reject symlinks at
all traversed components. Files are sorted, and all are parsed before callbacks
or writes, so malformed unselected cases cannot be blessed accidentally. -/
def runDirectory (registered : Registered) (options : Options := {}) : IO Summary := do
  unless validDirectory registered.directory do
    throw <| IO.userError s!"invalid test directory: {registered.directory}"
  plain "test" .dir
  let dir : System.FilePath := registered.directory
  plain dir .dir
  let paths := ((← dir.readDir).map (·.path)).filter (·.extension == some "fren")
    |>.qsort (fun a b => a.toString < b.toString)
  let mut files := #[]
  for path in paths do
    plain path .file
    let bytes ← IO.FS.readBinFile path
    let some text := String.fromUTF8? bytes | throw <| IO.userError s!"{path}: invalid UTF-8"
    let cases ← match parse text with
      | .ok cs => pure cs
      | .error m => throw <| IO.userError s!"{path}: {m}"
    files := files.push (path, bytes, cases)
  let mut summary : Summary := {}
  for (path, bytes, cases) in files do
    let mut edits := #[]
    for c in cases do
      unless options.filter.isEmpty || (c.name.splitOn options.filter).length > 1 do continue
      summary := { summary with selected := summary.selected + 1 }
      let result ← registered.runner.execute c.context c.input
      let actual := render result
      unless agrees c actual do
        if options.bless then
          edits := edits.push (c, actual)
          summary := { summary with changed := summary.changed + 1 }
        else
          summary := { summary with
            failed := summary.failed + 1,
            diagnostics := summary.diagnostics.push
              s!"{path}: {c.name}\n- expected: {c.expected.getD "<missing result>"}\n+ actual: {actual}" }
    unless edits.isEmpty do
      -- Best-effort recheck: reject an edit already visible before this write.
      plain "test" .dir
      plain dir .dir
      plain path .file
      unless (← IO.FS.readBinFile path) == bytes do
        throw <| IO.userError s!"{path}: changed while tests ran"
      IO.FS.writeBinFile path (rewrite bytes edits)
  return summary

/-- All selected libraries run even when one fails. 0 success, 1 mismatch or
malformed file/callback exception, 2 invalid CLI or no matching cases. -/
def cli (runners : Array Registered) (args : List String) : IO UInt32 := do
  let mut lib : Option String := none
  let mut options : Options := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--lib" :: value :: tail =>
      if lib.isSome then return 2
      lib := some value
      rest := tail
    | "--filter" :: value :: tail =>
      options := { options with filter := value }
      rest := tail
    | "--bless" :: tail =>
      options := { options with bless := true }
      rest := tail
    | _ =>
      IO.eprintln "usage: fren2_test --lib Library [--filter name] [--bless]"
      return 2
  let some library := lib | return 2
  let selected := runners.filter (·.directory == "test/" ++ library)
  if selected.size != 1 then
    IO.eprintln s!"unknown or ambiguous text-test library: {library}"
    return 2
  try
    let s ← runDirectory selected[0]! options
    for d in s.diagnostics do IO.eprintln d
    IO.println s!"{s.selected} cases, {s.failed} failed, {s.changed} blessed"
    return if s.failed > 0 then 1 else if s.selected == 0 then 2 else 0
  catch e =>
    IO.eprintln e.toString
    return 1
end Fren.TextTests
