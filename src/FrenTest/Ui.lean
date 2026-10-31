-- keep-sorted start
import FrenCore.Str
-- keep-sorted end

/-!
# ui tests

Expectations written as comments in `test/ui/**/*.fren` and
`examples/**/*.fren`, in the style of rustc's
ui tests, checked against the messages of either front end:

- `--~ SEV: TEXT` expects a message of severity `SEV` (`error`, `warning` or
  `info`) on this line whose text contains `TEXT`. `--~^ ...` refers to the
  line above (`--~^^` two above, and so on).
- `--~[hosted] ...` and `--~[cli] ...` apply to one front end only, for
  messages that legitimately differ (mostly parse and type errors, which the
  Lean front end gets from Lean).
- `--~$ ...` expects a message with no line: in the Lean front end, one at
  the `#fren_check` that the test adds after the source, such as an error
  that stops the whole check.
- `--~? ...` (`--~^? ...`, and so on) allows such a message without
  expecting it, for a message that either front end may give in one of
  several places, such as a note at whichever requirement of a conflict its
  solver's model picks (`cli::agreement`).
- Every message must be expected: unexpected messages fail the test.
- `--@ summary: N passed, M failed, K inconclusive` expects the checks'
  summary; `--@ exit: N` the binary's exit code; `--@ only: cli` (or
  `hosted`) restricts the file to one front end.
-/

namespace FrenTest.Ui

structure Diagnostic where
  line : Nat
  /-- `error`, `warning` or `info`. -/
  severity : String
  text : String
  /-- The error code, such as `F0105`, where the front end shows it. -/
  code? : Option String := none
  deriving Inhabited, Repr

structure Expectation where
  line : Nat
  severity : String
  text : String
  frontEnd? : Option String
  /-- Written `--~?`: such a message is allowed, not expected. -/
  optional : Bool := false
  /-- Where the annotation itself is, for error messages. -/
  at_ : Nat
  deriving Inhabited

structure Spec where
  expectations : Array Expectation := #[]
  summary? : Option String := none
  exit? : Option Nat := none
  only? : Option String := none
  deriving Inhabited

def severities : List String := ["error", "warning", "info"]

/-- Parses the annotations in a ui test's source. -/
def parse (src : String) : Except String Spec := do
  let mut spec : Spec := {}
  for line in src.splitOn "\n", i in [1:src.length + 2] do
    if let some rest := (line.splitOn "--@ ")[1]? then
      match rest.splitOn ": " with
      | ["summary", v] => spec := { spec with summary? := some v.trimAscii.toString }
      | ["exit", v] => spec := { spec with exit? := v.trimAscii.toString.toNat? }
      | ["only", v] => spec := { spec with only? := some v.trimAscii.toString }
      | _ => throw s!"line {i}: unknown directive `--@ {rest}`"
    let some ann := (line.splitOn "--~")[1]? | continue
    let atEnd := ann.startsWith "$"
    let ann := if atEnd then (ann.drop 1).toString else ann
    let carets := (ann.takeWhile (· == '^')).toString.length
    let ann := (ann.drop carets).toString
    let optional := ann.startsWith "?"
    let ann := if optional then (ann.drop 1).toString else ann
    let (frontEnd?, ann) :=
      if ann.startsWith "[" then
        match ann.drop 1 |>.toString.splitOn "]" with
        | fe :: rest => (some fe, "]".intercalate rest)
        | [] => (none, ann)
      else (none, ann)
    let ann := ann.trimAscii.toString
    let some (sev, text) := severities.findSome? fun s =>
        (ann.dropPrefix? (s ++ ": ")).map (s, ·.toString)
      | throw s!"line {i}: annotation must start with `error: `, `warning: ` or `info: `"
    if carets ≥ i then throw s!"line {i}: `^` points above the first line"
    let e : Expectation :=
      { line := if atEnd then 0 else i - carets, severity := sev, text := text.trimAscii.toString, frontEnd? := frontEnd?, optional, at_ := i }
    spec := { spec with expectations := spec.expectations.push e }
  return spec

/-- Whether the expectation `e` applies to `frontEnd`: it is for both front
ends, or for that one. -/
def Expectation.applies (frontEnd : String) (e : Expectation) : Bool := e.frontEnd?.all (· == frontEnd)

/-- Whether the message `d` meets the expectation `e`, for `frontEnd`: `e`
applies to it, and `d` is on `e`'s line, of its severity, and its text
contains `e`'s. -/
def meets (frontEnd : String) (e : Expectation) (d : Diagnostic) : Bool :=
  e.applies frontEnd && d.line == e.line && d.severity == e.severity && Fren.Str.contains d.text e.text

/-- Whether the expectation `e` may go without a message, for `frontEnd`:
it is written `--~?`, or it is for the other front end. -/
def mayLack (frontEnd : String) (e : Expectation) : Bool := e.optional || !e.applies frontEnd

/-- Whether each of the expectations `es` can be given a message of `ds`
that meets it, a different one for each, or none if it may lack one, so
that each message of `ds` is given to one (`testing::met?`). A search over
every way of giving them, so that one expectation that two messages meet
cannot take the message that only it and another meet: messages on
different lines never meet the same expectation, so it branches only
between those on one line. -/
def assignable (frontEnd : String) : List Expectation → List Diagnostic → Bool
  | [], ds => ds.isEmpty
  | e :: es, ds =>
    (List.range ds.length).any (fun i => meets frontEnd e ds[i]! && assignable frontEnd es (ds.eraseIdx i))
      || (mayLack frontEnd e && assignable frontEnd es ds)

/-- A description of each discrepancy between the messages `diags` and
the expectations `es`, for `frontEnd`, found by giving each expectation the
first message left that meets it: those that it then expects but finds no
message for, and the messages left. -/
def unmatched (frontEnd : String) (es : Array Expectation) (diags : Array Diagnostic) : Array String := Id.run do
  let mut failures := #[]
  let mut left := diags
  -- The expected messages first, then those only allowed.
  for e in es.filter (!·.optional) ++ es.filter (·.optional) do
    unless e.applies frontEnd do continue
    match left.findIdx? (meets frontEnd e) with
    | some idx => left := left.eraseIdx! idx
    | none =>
      if e.optional then continue
      let here := diags.filter (·.line == e.line) |>.map fun d => s!"\n    got {d.severity}: {d.text}"
      failures := failures.push s!"line {e.line}: expected {e.severity}: {e.text} (annotation on line {e.at_}){String.join here.toList}"
  for d in left do
    failures := failures.push s!"line {d.line}: unexpected {d.severity}: {d.text}"
  return failures

/-- The discrepancies between `frontEnd`'s messages `diags` and the
expectations `es`: none if `assignable`, and otherwise those that
`unmatched` finds, or, if it finds none, as it may where an expectation
took a message that another needed, one that says so. -/
def messageFailures (frontEnd : String) (es : Array Expectation) (diags : Array Diagnostic) : Array String :=
  if assignable frontEnd es.toList diags.toList then #[] else
    let failures := unmatched frontEnd es diags
    if failures.isEmpty then #["the messages cannot each be given an expectation that they meet, a different one for each"] else failures

/-- The discrepancy between the summary that `--@ summary:` expects,
`want?`, and `got?`. -/
def summaryFailures (want? got? : Option String) : Array String :=
  match want? with
  | some s => if got? != some s then #[s!"expected summary `{s}`, got `{got?.getD "(none)"}`"] else #[]
  | none => #[]

/-- The discrepancy between the exit code that `--@ exit:` expects,
`want?`, and `got?`, the binary's; Lean has none. -/
def exitFailures (want? got? : Option Nat) : Array String :=
  match want?, got? with
  | some e, some got => if e != got then #[s!"expected exit code {e}, got {got}"] else #[]
  | _, _ => #[]

/-- Checks `frontEnd`'s messages, summary and exit code against `spec`;
returns a description of each discrepancy (`testing::ui_file`). -/
def check (frontEnd : String) (spec : Spec) (diags : Array Diagnostic)
    (summary? : Option String) (exit? : Option Nat) : Array String :=
  messageFailures frontEnd spec.expectations diags ++ summaryFailures spec.summary? summary?
    ++ exitFailures spec.exit? exit?

end FrenTest.Ui
