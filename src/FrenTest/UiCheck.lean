-- keep-sorted start
import FrenTest.Ui
-- keep-sorted end

/-!
How a ui test's annotations are read (`FrenTest.Ui.parse`), and checked
against a front end's messages (`FrenTest.Ui.check`, `testing::ui_file`,
which `Impls.Testing` proves for any messages and expectations).
-/

open FrenTest.Ui

def parsed (src : String) : Array (Nat × String × String × Option String × Bool) :=
  match parse src with
  | .ok s => s.expectations.map fun e => (e.line, e.severity, e.text, e.frontEnd?, e.optional)
  | .error _ => #[]

-- `--~` expects a message on its line, `--~^` on the line above, `--~^^`
-- two above, `--~$` one with no line (0), `--~?` allows one, and `[cli]`
-- or `[hosted]` restricts it to one front end.
#guard parsed "a --~ error: x\nb\nc --~^ warning: y\nd --~^^? info: z\n--~$ error: stop\n--~[hosted] error: lean\n--~^?[cli] error: both" ==
  #[(1, "error", "x", none, false), (2, "warning", "y", none, false), (2, "info", "z", none, true),
    (0, "error", "stop", none, false), (6, "error", "lean", some "hosted", false), (6, "error", "both", some "cli", true)]

-- `--@` gives the summary, the exit code and the front ends.
#guard match parse "--@ summary: 1 passed, 0 failed, 0 inconclusive\n--@ exit: 3\n--@ only: cli" with
  | .ok s => s.summary? == some "1 passed, 0 failed, 0 inconclusive" && s.exit? == some 3 && s.only? == some "cli"
  | .error _ => false

-- A caret above the first line, an unknown severity or directive is an error.
#guard (parse "--~^ error: x" matches .error _)
#guard (parse "--~ note: x" matches .error _)
#guard (parse "--@ other: x" matches .error _)

def ex (line : Nat) (text : String) (optional := false) (frontEnd? : Option String := none) : Expectation :=
  { line, severity := "error", text, frontEnd?, optional, at_ := line }

def msg (line : Nat) (text : String) : Diagnostic := { line, severity := "error", text }

def passes (es : Array Expectation) (ds : Array Diagnostic) (fe := "cli") : Bool :=
  (check fe { expectations := es } ds none none).isEmpty

-- Each message is expected, and each expectation met once, by a message
-- on its line of its severity, whose text contains its own.
#guard passes #[ex 1 "x"] #[msg 1 "an x here"]
#guard !passes #[ex 1 "x"] #[msg 2 "x"]
#guard !passes #[ex 1 "x"] #[{ msg 1 "x" with severity := "warning" }]
#guard !passes #[ex 1 "x"] #[msg 1 "y"]
#guard !passes #[ex 1 "x"] #[]
#guard !passes #[] #[msg 1 "x"]
#guard !passes #[ex 1 "x"] #[msg 1 "x", msg 1 "x"]
#guard passes #[ex 1 "x", ex 1 "x"] #[msg 1 "x", msg 1 "x"]
#guard !passes #[ex 1 "x", ex 1 "x"] #[msg 1 "x"]
-- Every text contains the empty one.
#guard passes #[ex 1 ""] #[msg 1 "x"]
-- `--~?` allows a message, once, and does not expect one.
#guard passes #[ex 1 "x" true] #[]
#guard passes #[ex 1 "x" true] #[msg 1 "x"]
#guard !passes #[ex 1 "x" true] #[msg 1 "x", msg 1 "x"]
-- An expectation for the other front end is not met, and expects nothing.
#guard passes #[ex 1 "x" (frontEnd? := some "hosted")] #[]
#guard !passes #[ex 1 "x" (frontEnd? := some "hosted")] #[msg 1 "x"]
#guard passes #[ex 1 "x" (frontEnd? := some "hosted")] #[msg 1 "x"] "hosted"

-- An expectation that two messages meet must not take the one that only
-- another expectation is met by: `x` is in both messages, and `xy` in one.
-- Giving each expectation the first message that meets it fails here.
#guard passes #[ex 1 "x", ex 1 "xy"] #[msg 1 "xy", msg 1 "x"]
#guard passes #[ex 1 "x" true, ex 1 "xy"] #[msg 1 "xy"]
#guard !passes #[ex 1 "x", ex 1 "xy"] #[msg 1 "xy", msg 1 "y"]
#guard (check "cli" { expectations := #[ex 1 "x", ex 1 "xy"] } #[msg 1 "xy", msg 1 "y"] none none).size == 2

-- The summary and exit code, where expected.
#guard (check "cli" { summary? := some "s" } #[] (some "s") (some 0)).isEmpty
#guard !(check "cli" { summary? := some "s" } #[] (some "t") none).isEmpty
#guard !(check "cli" { summary? := some "s" } #[] none none).isEmpty
#guard !(check "cli" { exit? := some 1 } #[] none (some 0)).isEmpty
#guard (check "hosted" { exit? := some 1 } #[] none none).isEmpty

-- `solve` gives the messages by matching, in polynomial time, so a file
-- with many expectations that the same messages meet fails, or passes,
-- at once: a search over every way of giving them would try all 11! here.
#guard !passes (.replicate 10 (ex 1 "x")) (.replicate 11 (msg 1 "x"))
#guard !passes (.replicate 11 (ex 1 "x")) (.replicate 10 (msg 1 "x"))
#guard passes (.replicate 40 (ex 1 "x") ++ .replicate 40 (ex 1 "x" true)) (.replicate 60 (msg 1 "x"))

/-- Whether `met` decides by `solve`'s answer, which passes its check,
without falling back on `assignable`'s search; and every set that `solve`
reports cannot be given, for the failures that `unmatched` describes. -/
def decided (es : List Expectation) (ds : List Diagnostic) : Bool :=
  let sol := solve "cli" es ds
  (if sol.lacking.isEmpty && sol.unexpected.isEmpty then checkAssigns "cli" es ds sol.assignment else true)
    && sol.lacking.all (refutesExpected "cli" es ds) && sol.unexpected.all (refutesGiven "cli" es ds)

/-- The lists of `n` elements of `xs`. -/
def listsOf (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (listsOf xs n).flatMap fun l => xs.map (· :: l)

/-- The lists of up to `n` elements of `xs`. -/
def upTo (xs : List α) (n : Nat) : List (List α) := (List.range (n + 1)).flatMap (listsOf xs)

-- On every file of one line with up to three expectations, each `x`, `xy`
-- or `y`, expected or allowed, and up to four messages, `x`, `xy` or `y`.
#guard (upTo [ex 1 "x", ex 1 "xy", ex 1 "y", ex 1 "x" true, ex 1 "xy" true, ex 1 "y" true] 3).all fun es =>
  (upTo [msg 1 "x", msg 1 "xy", msg 1 "y"] 4).all (decided es)
