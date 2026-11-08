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
