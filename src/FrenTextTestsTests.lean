module

import FrenTextTests

open Fren.TextTests

-- The adapter receives the exact context suffix and the exact multiline input,
-- including CRLF, Unicode, blank lines, and a final line without LF.
#eval show IO Unit from do
  let source := "-- case: raw\r\n-- context:  x: Seq<Int> = [1, 2]  \r\nα\r\n\r\nβ"
  let .ok cases := parse source | throw <| IO.userError "parse failed"
  unless cases.size == 1 do throw <| IO.userError "case count"
  let c := cases[0]!
  unless c.context == "  x: Seq<Int> = [1, 2]  " && c.input == "α\r\n\r\nβ" do
    throw <| IO.userError "raw text changed"
  let observed ← IO.mkRef false
  let runner := Runner.of (fun raw => if raw == c.context then .ok (7 : Nat) else .error "context changed")
    (fun n input => do
      observed.set true
      return if n == 7 && input == c.input then .ok "actual\noutput\n" else .error "input changed")
  let actual := render (← runner.execute c.context c.input)
  unless actual == "actual\noutput\n" && (← observed.get) do throw <| IO.userError "callback not run"
  let changed := rewrite source.toUTF8 #[(c, actual)]
  let .ok parsed := parse (String.fromUTF8! changed) | throw <| IO.userError "reparse failed"
  unless agrees parsed[0]! actual do throw <| IO.userError "multiline result did not roundtrip"

-- Result encoding must represent empty strings, trailing LF, CRLF content and
-- both physical newline styles without losing callback text or EOF status.
#eval show IO Unit from do
  for source in ["-- case: c\n1\n-- result: old", "-- case: c\r\n1\r\n-- result: old\r\n",
      "-- case: c\n1", "-- case: c\n1\n"] do
    let .ok cases := parse source | throw <| IO.userError "parse failed"
    for actual in ["", "x", "x\n", "x\n\n", "x\r\ny\r", "λ\n-- case: inside result"] do
      let bytes := rewrite source.toUTF8 #[(cases[0]!, actual)]
      let .ok again := parse (String.fromUTF8! bytes) | throw <| IO.userError "reparse failed"
      unless agrees again[0]! actual && again[0]!.input == cases[0]!.input do
        throw <| IO.userError s!"result/input roundtrip failed: {repr actual}"

/-- error: expected test/<Library> -/
#guard_msgs in
@[fren_text_tests "test/../outside"]
def invalidPath : Runner := default

/-- error: registered declaration must have type Fren.TextTests.Runner -/
#guard_msgs in
@[fren_text_tests "test/WrongType"]
def invalidType : Nat := 0

@[fren_text_tests "test/Duplicate"]
def duplicateOne : Runner := default
@[fren_text_tests "test/Duplicate"]
def duplicateTwo : Runner := default

/-- error: duplicate text-test directory: test/Duplicate -/
#guard_msgs in
fren_test_runners duplicateRegistry

-- Each invocation owns its temporary project and restores the process cwd.
private def withFixture (test : System.FilePath → IO Unit) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let previous ← IO.currentDir
    try
      IO.Process.setCurrentDir root
      IO.FS.createDirAll "test/Owned"
      test "test/Owned/cases.fren"
    finally
      IO.Process.setCurrentDir previous

-- Parse -> real typed callback -> IO bless -> reparse -> callback/check. Original
-- bytes outside the insertion AND original callback input must both survive.
#eval withFixture fun path => do
  let samples := [("1\r", "1\r"), ("\r", "\r"), ("1\r\r", "1\r\r"), ("1", "1"),
    ("1\n2", "1\n2"), ("1\r\n2\r", "1\r\n2\r"), ("1\n", "1"),
    ("1\r\n", "1"), ("\n", ""), ("\r\n", "")]
  for headerEol in ["\n", "\r\n"] do
    for contextEol in ["\n", "\r\n"] do
      for (raw, expectedInput) in samples do
        let source := "-- preamble ü\r\n-- case: c" ++ headerEol ++
          "-- context: 7 " ++ contextEol ++ raw
        let original := source.toUTF8
        IO.FS.writeBinFile path original
        let .ok before := parse source | throw <| IO.userError "initial parse failed"
        let c := before[0]!
        unless c.input == expectedInput do throw <| IO.userError "initial input differs"
        let observed ← IO.mkRef (#[] : Array String)
        let runner := Runner.of (fun raw => if raw == " 7 " then .ok (7 : Nat) else .error "context changed")
          (fun n input => do
            observed.modify (·.push input)
            return .ok (toString (n + input.utf8ByteSize)))
        let blessed ← runDirectory ⟨"test/Owned", runner⟩ { bless := true }
        let changed ← IO.FS.readBinFile path
        let actual := toString (7 + expectedInput.utf8ByteSize)
        unless blessed.selected == 1 && blessed.changed == 1 && blessed.failed == 0 &&
            c.start == original.size && c.stop == original.size &&
            changed == original ++ replacement c actual do
          throw <| IO.userError "blessing changed bytes outside its EOF insertion"
        let .ok after := parse (String.fromUTF8! changed) | throw <| IO.userError "reparse failed"
        let d := after[0]!
        unless after.size == before.size && d.name == c.name && d.context == c.context &&
            d.input == c.input && agrees d actual do
          throw <| IO.userError s!"input/result law failed for {repr source}"
        let checked ← runDirectory ⟨"test/Owned", runner⟩
        unless checked.failed == 0 && checked.changed == 0 && checked.selected == 1 &&
            (← observed.get) == #[expectedInput, expectedInput] &&
            (← IO.FS.readBinFile path) == changed do
          throw <| IO.userError "next callback/check changed input or disagreed with blessed result"
  IO.println "40 input-preserving IO bless/recheck cases passed"

-- Deterministic edit after the runner reads the source, before its write guard.
#eval withFixture fun path => do
  let original := "-- case: changing\n1\n-- result: wrong\n".toUTF8
  let callbackBytes := "-- callback owns ü\r\n-- case: changed\r\n9\r\n-- result: keep exactly".toUTF8
  IO.FS.writeBinFile path original
  let observed ← IO.mkRef false
  let runner := Runner.of (fun (_ : String) => .ok ()) (fun _ input => do
    unless input == "1" do throw <| IO.userError "callback input differs"
    observed.set true
    IO.FS.writeBinFile path callbackBytes
    return .ok "1")
  let error ← try
    let _ ← runDirectory ⟨"test/Owned", runner⟩ { bless := true }
    pure none
  catch e => pure (some e.toString)
  unless (← observed.get) && ((error.getD "").splitOn "changed while tests ran").length > 1 &&
      (← IO.FS.readBinFile path) == callbackBytes do
    throw <| IO.userError s!"changed-file guard failed: {error}"
  IO.println "changed-file guard rejected blessing and preserved exact callback bytes"
