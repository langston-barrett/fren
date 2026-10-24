/-!
# ui tests

Expectations written as comments in `test/ui/**/*.fren`, in the style of rustc's
ui tests, checked against the messages of either front end:

- `--~ SEV: TEXT` expects a message of severity `SEV` (`error`, `warning` or
  `info`) on this line whose text contains `TEXT`. `--~^ ...` refers to the
  line above (`--~^^` two above, and so on).
- `--~[hosted] ...` and `--~[cli] ...` apply to one front end only, for
  messages that legitimately differ (mostly parse and type errors, which the
  Lean front end gets from Lean).
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
  deriving Inhabited, Repr

structure Expectation where
  line : Nat
  severity : String
  text : String
  frontEnd? : Option String
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
    let carets := (ann.takeWhile (· == '^')).toString.length
    let ann := (ann.drop carets).toString
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
      { line := i - carets, severity := sev, text := text.trimAscii.toString, frontEnd? := frontEnd?, at_ := i }
    spec := { spec with expectations := spec.expectations.push e }
  return spec

/-- Checks `frontEnd`'s messages, summary and exit code against `spec`;
returns a description of each discrepancy. -/
def check (frontEnd : String) (spec : Spec) (diags : Array Diagnostic)
    (summary? : Option String) (exit? : Option Nat) : Array String := Id.run do
  let mut failures := #[]
  let mut unmatched := diags
  for e in spec.expectations do
    if e.frontEnd?.any (· != frontEnd) then continue
    match unmatched.findIdx? fun d => d.line == e.line && d.severity == e.severity && (d.text.splitOn e.text).length > 1 with
    | some idx => unmatched := unmatched.eraseIdx! idx
    | none =>
      let here := diags.filter (·.line == e.line) |>.map fun d => s!"\n    got {d.severity}: {d.text}"
      failures := failures.push s!"line {e.line}: expected {e.severity}: {e.text} (annotation on line {e.at_}){String.join here.toList}"
  for d in unmatched do
    failures := failures.push s!"line {d.line}: unexpected {d.severity}: {d.text}"
  if let some s := spec.summary? then
    if summary? != some s then
      failures := failures.push s!"expected summary `{s}`, got `{summary?.getD "(none)"}`"
  if let (some e, some got) := (spec.exit?, exit?) then
    if e != got then failures := failures.push s!"expected exit code {e}, got {got}"
  return failures

end FrenTest.Ui
