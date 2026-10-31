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
  /-- Its column, counted in characters from 0 at the start of the line;
  0 where it has no line. The ui tests do not compare it; the front-end
  fuzzer does (`FrenTest.Frontends.compare`). -/
  col : Nat := 0
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
that each message of `ds` is given to one (`testing::met?`), by a search
over every way of giving them. It takes time exponential in the number of
expectations that share messages, multiplied across lines, so `met`
decides this with a matching instead, and falls back on this search only
should the matching's answer fail its check. -/
def assignable (frontEnd : String) : List Expectation → List Diagnostic → Bool
  | [], ds => ds.isEmpty
  | e :: es, ds =>
    (List.range ds.length).any (fun i => meets frontEnd e ds[i]! && assignable frontEnd es (ds.eraseIdx i))
      || (mayLack frontEnd e && assignable frontEnd es ds)

/-- Whether `a` gives each expectation of `es` the position of a message of
`ds` that meets it, or -1 where it may lack one, a different message for
each, and every message to one. -/
def checkAssigns (frontEnd : String) (es : List Expectation) (ds : List Diagnostic) (a : List Int) : Bool :=
  a.length == es.length
    && (List.range es.length).all (fun i =>
      match es[i]?, a[i]? with
      | some e, some x =>
        if x = -1 then mayLack frontEnd e
        else decide (0 ≤ x) && match ds[x.toNat]? with
          | some d => meets frontEnd e d
          | none => false
      | _, _ => true)
    && (List.range a.length).all (fun i => (List.range a.length).all fun j =>
      !decide (i < j) || a[i]?.getD (-1) == -1 || a[i]?.getD (-1) != a[j]?.getD (-1))
    && (List.range ds.length).all (fun m => decide ((m : Int) ∈ a))

/-- Whether the expectation at `i` of `es` and the message at `m` of `ds`
are there, and the message meets the expectation. -/
def meetsAt (frontEnd : String) (es : List Expectation) (ds : List Diagnostic) (i m : Nat) : Bool :=
  match es[i]?, ds[m]? with
  | some e, some d => meets frontEnd e d
  | _, _ => false

/-- Whether the expectations of `es` at the positions `ys`, each of which
must have a message, are met by fewer messages of `ds` than there are of
them, so that they cannot each be given a different one. -/
def refutesExpected (frontEnd : String) (es : List Expectation) (ds : List Diagnostic) (ys : List Nat) : Bool :=
  decide ys.Nodup
    && ys.all (fun y => match es[y]? with
      | some e => !mayLack frontEnd e
      | none => false)
    && decide (((List.range ds.length).filter fun m => ys.any (meetsAt frontEnd es ds · m)).length < ys.length)

/-- Whether the messages of `ds` at the positions `xs` meet fewer
expectations of `es` than there are of them, so that they cannot each be
given a different one. -/
def refutesGiven (frontEnd : String) (es : List Expectation) (ds : List Diagnostic) (xs : List Nat) : Bool :=
  decide xs.Nodup && xs.all (· < ds.length)
    && decide (((List.range es.length).filter fun i => xs.any (meetsAt frontEnd es ds i)).length < xs.length)

/-- What `solve` finds: a way to give the expectations messages, if
`lacking` and `unexpected` are empty, and otherwise, for each expectation
that it could give no message, and each message that it could give no
expectation, the positions of a set of expectations, or of messages, that
`refutesExpected`, or `refutesGiven`, shows cannot be given, with the one
that it could not give at its head. -/
structure Solution where
  /-- For each expectation, the position of its message, or -1. -/
  assignment : List Int
  lacking : List (List Nat) := []
  unexpected : List (List Nat) := []
  deriving Inhabited

/-- The state of `solve`'s search for an alternating path. -/
structure Search where
  /-- The message given to each expectation. -/
  ofE : Array (Option Nat)
  /-- The expectation given each message. -/
  ofD : Array (Option Nat)
  seenE : Array Bool
  seenD : Array Bool

/-- Gives each message an expectation that it meets, by augmenting
paths (Kuhn's algorithm): from the message `d`, an expectation that it
meets that has no message, or whose message can be given another. -/
partial def giveMessage (meetsD : Array (Array Nat)) (d : Nat) : StateM Search Bool := do
  modify fun s => { s with seenD := s.seenD.set! d true }
  for e in meetsD[d]! do
    if (← get).seenE[e]! then continue
    modify fun s => { s with seenE := s.seenE.set! e true }
    let free ← match (← get).ofE[e]! with
      | none => pure true
      | some d' => giveMessage meetsD d'
    if free then
      modify fun s => { s with ofE := s.ofE.set! e (some d), ofD := s.ofD.set! d (some e) }
      return true
  return false

/-- Gives the expectation `e`, which must have one, a message that meets
it: one that has no expectation, or whose expectation may lack one, or
whose expectation can be given another. -/
partial def giveExpectation (meetsE : Array (Array Nat)) (mayLackE : Array Bool) (e : Nat) :
    StateM Search Bool := do
  modify fun s => { s with seenE := s.seenE.set! e true }
  for d in meetsE[e]! do
    if (← get).seenD[d]! then continue
    modify fun s => { s with seenD := s.seenD.set! d true }
    let free ← match (← get).ofD[d]! with
      | none => pure true
      | some e' =>
        if mayLackE[e']! then
          modify fun s => { s with ofE := s.ofE.set! e' none }
          pure true
        else if (← get).seenE[e']! then pure false
        else giveExpectation meetsE mayLackE e'
    if free then
      modify fun s => { s with ofE := s.ofE.set! e (some d), ofD := s.ofD.set! d (some e) }
      return true
  return false

/-- The positions marked in `seen`. -/
def marked (seen : Array Bool) : List Nat := (List.range seen.size).filter (seen[·]!)

/-- Gives the expectations `es` the messages `ds`, in time polynomial in
their numbers: first each message an expectation that it meets, then
each expectation that must have a message and has none one, without
taking any message's away. When a search from a message fails, the
messages it reached meet only the expectations it reached, each of which
has one of the other messages; when one from an expectation fails, the
expectations it reached, which must each have a message, are met only by
the messages it reached, each of which another of them has. Either is a
set of which `refutesGiven`, or `refutesExpected`, holds. -/
def solve (frontEnd : String) (es : List Expectation) (ds : List Diagnostic) : Solution := Id.run do
  let esA := es.toArray
  let dsA := ds.toArray
  let meetsD := dsA.map fun d => (List.range esA.size).filter (fun i => meets frontEnd esA[i]! d) |>.toArray
  let meetsE := esA.map fun e => (List.range dsA.size).filter (fun m => meets frontEnd e dsA[m]!) |>.toArray
  let mayLackE := esA.map (mayLack frontEnd)
  let none' : Search :=
    { ofE := .replicate esA.size none, ofD := .replicate dsA.size none,
      seenE := .replicate esA.size false, seenD := .replicate dsA.size false }
  let mut s := none'
  let mut unexpected := #[]
  for d in [0:dsA.size] do
    let (ok, s') := giveMessage meetsD d |>.run { s with seenE := none'.seenE, seenD := none'.seenD }
    s := s'
    unless ok do unexpected := unexpected.push (d :: (marked s.seenD).filter (· != d))
  let mut lacking := #[]
  for e in [0:esA.size] do
    if mayLackE[e]! || s.ofE[e]!.isSome then continue
    let (ok, s') := giveExpectation meetsE mayLackE e |>.run { s with seenE := none'.seenE, seenD := none'.seenD }
    s := s'
    unless ok do lacking := lacking.push (e :: (marked s.seenE).filter (· != e))
  return { assignment := s.ofE.toList.map fun o => (o.map (fun m : Nat => (m : Int))).getD (-1),
           lacking := lacking.toList, unexpected := unexpected.toList }

/-- Whether the expectations `es` can be given the messages `ds`, as
`assignable` says, decided by `solve`: its way of giving them, or its
sets that cannot be given, checked. Should neither pass its check, which
`solve` being right rules out, though that is tested and not proved, it
falls back on `assignable`'s search. -/
def met (frontEnd : String) (es : List Expectation) (ds : List Diagnostic) : Bool :=
  let sol := solve frontEnd es ds
  if sol.lacking.isEmpty && sol.unexpected.isEmpty then
    checkAssigns frontEnd es ds sol.assignment || assignable frontEnd es ds
  else if sol.lacking.any (refutesExpected frontEnd es ds) || sol.unexpected.any (refutesGiven frontEnd es ds) then false
  else assignable frontEnd es ds

/-- A description of each expectation and message that `solve` could not
give, for `frontEnd`: those that it expects but finds no message for, and
the messages left. -/
def unmatched (frontEnd : String) (es : Array Expectation) (diags : Array Diagnostic) : Array String :=
  let sol := solve frontEnd es.toList diags.toList
  let missing := sol.lacking.filterMap (·.head?) |>.filterMap (es[·]?) |>.map fun e =>
    let here := diags.filter (·.line == e.line) |>.map fun d => s!"\n    got {d.severity}: {d.text}"
    s!"line {e.line}: expected {e.severity}: {e.text} (annotation on line {e.at_}){String.join here.toList}"
  let left := sol.unexpected.filterMap (·.head?) |>.filterMap (diags[·]?) |>.map fun d =>
    s!"line {d.line}: unexpected {d.severity}: {d.text}"
  (missing ++ left).toArray

/-- The discrepancies between `frontEnd`'s messages `diags` and the
expectations `es`: none if they are `met`, and otherwise those that
`unmatched` finds, or, should `solve` find none where `met` falls back on
`assignable`'s search, which `solve` being right rules out, one that says
so. -/
def messageFailures (frontEnd : String) (es : Array Expectation) (diags : Array Diagnostic) : Array String :=
  if met frontEnd es.toList diags.toList then #[] else
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
