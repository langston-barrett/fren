-- keep-sorted start
import FrenTest.Frontends
import FrenTest.Messages
-- keep-sorted end

/-!
# Comparing the front ends' reports

Regression tests for `FrenTest.Frontends.compare`, which
`fren_fuzz_frontends` relies on: each spec here, with the reports that the
front ends gave or could give on it, must be reported as differing (or as
agreeing), so that a normalization never hides a real difference.
-/

namespace FrenTest.FrontendsCompare

open FrenTest.Ui (Diagnostic)
open FrenTest.Frontends

def err (line : Nat) (text : String) (code? : Option String := none) : Diagnostic :=
  { line, severity := "error", text, code? }

def warn (line : Nat) (text : String) (code? : Option String := none) : Diagnostic :=
  { line, severity := "warning", text, code? }

def none0 : String := "0 passed, 0 failed, 0 inconclusive, 0 redundant"

def note (line : Nat) (text : String) : Diagnostic := { line, severity := "info", text }

def differs (text : String) (cli hosted : Report) : Bool := !(compare text cli hosted).1.isEmpty

def agrees (text : String) (cli hosted : Report) : Bool := (compare text cli hosted).1.isEmpty

/-! ## Lean rejects what the binary accepts -/

-- #97 in a constant, an item without checks.
def constant : String := "pub const K: Int := {(1, 2)}.range.card\n"

-- No exit code, so that only the messages can tell the reports apart.
#guard differs constant { diags := #[], summary? := none0 }
  { diags := #[err 1 "`Rel(Int, Int)` has no method `range.card`"], summary? := none0 }

-- One of Lean's own errors with no error of the binary on its line.
#guard differs constant { diags := #[], summary? := none0 }
  { diags := #[err 1 "unknown identifier 'K'"], summary? := none0 }

-- ... nor a static error: a check that fails in the binary is not one
-- that Lean rejects (#97 in an expectation).
def expectation : String := "expect e: {(1, 2)}.range.card = 2
"

def expectationDiff : Array String :=
  (compare expectation { diags := #[err 1 "expectation `e` does not hold" "F0603"], summary? := none0 }
    { diags := #[err 1 "Type mismatch\n  x\nhas type Bool"], summary? := none0 }).1

-- Both errors are reported, each as only one front end's.
#guard expectationDiff.any (·.startsWith "line 1: only fren reports error[F0603]")
#guard expectationDiff.any (·.startsWith "line 1: only Lean reports error: Type mismatch")

-- Only a parse error of Lean's stands for an error of the binary on the
-- same line: a type error must be worded as the binary's.
#guard agrees constant { diags := #[err 1 "expected an expression, found keyword `with`" "F0102"], exit? := some 2 }
  { diags := #[err 1 "unexpected token 'with'; expected term"] }
#guard !agrees constant { diags := #[err 1 "type mismatch: expected `Int`, found `Bool`" "F0304"], exit? := some 2 }
  { diags := #[err 1 "Type mismatch\n  x\nhas type Bool"] }

-- Both report the lints of an item with a static error (`Reqs/View`), and
-- each of Lean's errors on other lines of it is compared.
def item : String := "comp c {\n    in x: Int\n    pub out y: Int\n    ensure q: y = x * x\n    ensure r: y = K\n}\n"

#guard differs item { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307"], exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", warn 2 "unused variable `x`"] }

#guard agrees item { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307", warn 2 "unused variable `x`" "F0710"], exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", warn 2 "unused variable `x`"] }

#guard differs item { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307"], exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", err 5 "unknown identifier 'K'"] }

-- Both report a static error per constraint (`Reqs/View#how-many-are-reported`),
-- so an error of Lean's in another constraint of an item that the binary
-- rejects is compared like any other.
#guard differs item { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307"], exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", err 5 "cannot find `K` in this scope"] }
#guard agrees item
  { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307", err 5 "cannot find `K` in this scope" "F0201"],
    exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", err 5 "cannot find `K` in this scope"] }

-- A static error stops both front ends' checks: a result, or a summary,
-- of Lean's after one is a difference.
#guard differs item { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307"], exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", err 1 "`c` is not realizable"] }

#guard differs item { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307"], exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported"], summary? := none0 }

/-! ## The binary cannot parse what Lean accepts -/

def parse : String := "comp c {\n    in x: Int\n    ensure q: x = 1\n}\n\ncomp d {\n    in y: Int\n    ensure q: y = 1\n}\n"

-- Lean's only error is a failed check in another item.
#guard differs parse { diags := #[err 3 "expected an expression, found keyword `expect`" "F0104"], exit? := some 2 }
  { diags := #[err 7 "`d` is not realizable"] }

-- Lean's other errors in the item, before the binary's parse error: Lean
-- parsed the whole item, the line that the binary rejects included.
def parseLate : String := "comp c {\n    in x: Int\n    expect x0: x = 1\n    ensure q: x =\n}\n"

#guard differs parseLate { diags := #[err 4 "expected an expression, found `}`" "F0104"], exit? := some 2 }
  { diags := #[err 3 "expectation `c::x0` does not hold"] }

#guard differs parseLate { diags := #[err 4 "expected an expression, found `}`" "F0104"], exit? := some 2 }
  { diags := #[err 2 "cannot find `Int2` in this scope"] }

-- Lean's parse error two lines before the binary's: the binary parsed
-- that line, so this is a difference of its own.
def parseEarly : String := "comp c {\n    in x: Int\n    expect e: {(1, 2)}.range.card = 1\n    ensure q: x =\n}\n"

#guard differs parseEarly { diags := #[err 5 "expected an expression, found `}`" "F0104"], exit? := some 2 }
  { diags := #[err 3 "unexpected token '.'; expected fren_expr"] }

-- The same, across a blank line and a comment, which the binary skips.
def parseGap : String := "comp c {\n    ensure q: x =\n\n    -- a comment\n    expect e: x = 1\n}\n"

#guard agrees parseGap { diags := #[err 5 "expected an expression, found keyword `expect`" "F0104"], exit? := some 2 }
  { diags := #[err 2 "unexpected token 'expect'; expected fren_expr"] }

#guard !isLeanParseError (err 2 "expected a function, but `f` is a variable")
#guard isLeanParseError (err 2 "expected 'out'")

-- Lean's own parse error, on the line before the binary's, in its item.
#guard agrees parse { diags := #[err 3 "expected an expression, found keyword `expect`" "F0104"], exit? := some 2 }
  { diags := #[err 2 "unexpected token 'expect'; expected fren_expr", err 7 "`d` is vacuous: its condition can never hold"] }

/-! ## Summaries and exit codes -/

def checked : String := "comp c {\n    in x: Int\n    pub out y?\n    ensure q: y? iff x = 1\n}\n"

-- A summary that differs with no undecided check to explain it.
#guard differs checked { diags := #[], summary? := "2 passed, 0 failed, 0 inconclusive, 0 redundant", exit? := some 0 }
  { diags := #[], summary? := "1 passed, 0 failed, 0 inconclusive, 1 redundant" }

#guard !(compare checked { diags := #[], summary? := "2 passed, 0 failed, 0 inconclusive, 0 redundant", exit? := some 0 }
  { diags := #[], summary? := "1 passed, 0 failed, 0 inconclusive, 1 redundant" }).2

-- ... but an undecided check, on one side, is a matter of time.
#guard (compare checked
  { diags := #[warn 4 "could not decide whether `c::q` is redundant: the solver returned unknown (TIMEOUT)" "F0608"],
    summary? := "1 passed, 0 failed, 1 inconclusive, 0 redundant", exit? := some 3 }
  { diags := #[], summary? := "2 passed, 0 failed, 0 inconclusive, 0 redundant" }).2

-- An exit code that disagrees with Lean's messages.
#guard differs checked { diags := #[], summary? := none0, exit? := some 1 } { diags := #[], summary? := none0 }
#guard differs checked { diags := #[], summary? := none0, exit? := some 3 } { diags := #[], summary? := none0 }
#guard agrees checked { diags := #[warn 2 "unused variable `x`" "F0710"], summary? := none0, exit? := some 3 }
  { diags := #[warn 2 "unused variable `x`"], summary? := none0 }
#guard differs checked { diags := #[warn 2 "unused variable `x`" "F0710"], summary? := none0, exit? := some 0 }
  { diags := #[warn 2 "unused variable `x`"], summary? := none0 }

/-! ## Messages without a location -/

#guard (FrenTest.Ui.cliDiagnostics "a.fren" "error: internal error: oops\n  = note: this is a bug in Fren\n"
  (keepUnlocated := true)).1.size == 1

#guard (FrenTest.Ui.cliDiagnostics "a.fren" "error: internal error: oops\n").1.isEmpty

-- Each front end's line when a static error stops it, which has no
-- location: both must say it, or neither.
def stopped : Array Diagnostic :=
  #[err 4 "nonlinear arithmetic is not supported" "F0307", err 0 "could not check due to previous errors"]

#guard agrees item { diags := stopped, exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", err 0 "could not check due to previous errors"] }

#guard differs item { diags := stopped, exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported"] }

#guard differs item { diags := #[err 4 "nonlinear arithmetic is not supported" "F0307"], exit? := some 2 }
  { diags := #[err 4 "nonlinear arithmetic is not supported", err 0 "could not check due to previous errors"] }

-- ... even after a parse error, where nothing else is compared.
#guard differs parse { diags := #[err 3 "expected an expression, found keyword `expect`" "F0104", err 0 "could not check due to previous errors"], exit? := some 2 }
  { diags := #[err 2 "unexpected token 'expect'; expected fren_expr"] }

#guard differs checked { diags := #[err 0 "internal error: oops"], summary? := none0, exit? := some 2 }
  { diags := #[], summary? := none0 }

/-! ## Normalized headlines -/

-- Values are masked. A realizability failure's input and requirements are
-- in its note, not its first line.
#guard normHead "`c::x` is not determined by the inputs: for the input a = 1, it can be 1 or 2"
  == normHead "`c::x` is not determined by the inputs: for the input a = 2, it can be 3 or 4"

/-- A realizability failure of `c`, as the binary's text has it (a `=`
note's lines, its later lines indented under its text) or Lean's (after a
blank line). -/
def unrealizable (input : Array String) (core : String) (hosted : Bool := false) : String :=
  let note := if input.isEmpty then s!"note: no outputs satisfy {core}"
    else "note: for the input\n" ++ String.join (input.toList.map (s!"          {·}\n")) ++ s!"      no outputs satisfy {core}"
  s!"`c` is not realizable{if hosted then "\n\n" else "\n"}{note}\nhelp: weaken one of them"

#guard conflictInput? (unrealizable #["x = 1", "y = 2"] "`q`") == some "x = 1\ny = 2"
#guard conflictInput? (unrealizable #["x = 1"] "`q`" (hosted := true)) == some "x = 1"
#guard conflictCore? (unrealizable #["x = 1"] "`q` and `r`") == some "no outputs satisfy `q` and `r`"
#guard conflictInput? (unrealizable #[] "`q`") == some ""
#guard conflictCore? (unrealizable #[] "`q`") == some "no outputs satisfy `q`"
#guard conflictInput? "`c::x` is not determined by the inputs" == none
#guard isConflictNote (note 4 "`q0` forces x = 1, but `q1` forces x = 2")
#guard !isConflictNote (note 4 "cover goal `c::g` is met")

/-! ## Realizability failures (#99) -/

def conflict : String :=
  "comp c {\n    in s: String\n    inst w: d { b? := s != \"\" }\n    ensure q0: w.b?\n    ensure q1: not w.b?\n}\n"

-- Different inputs, so different requirements and notes, each minimal for
-- its input: they agree.
#guard agrees conflict
  { diags := #[err 1 (unrealizable #["s = \"\""] "`q0`") "F0601",
      note 4 "`q0` forces w.b? = true, but `q1` forces w.b? = false"], summary? := none0, exit? := some 1 }
  { diags := #[err 1 (unrealizable #["s = \"A\""] "`q1`" (hosted := true))], summary? := none0 }

-- The same input, but different requirements: they differ, even if some
-- undecided check could explain the rest.
#guard differs conflict
  { diags := #[err 1 (unrealizable #["s = \"A\""] "`q0`") "F0601"], summary? := none0, exit? := some 1 }
  { diags := #[err 1 (unrealizable #["s = \"A\""] "`q1`" (hosted := true))], summary? := none0 }
#guard !(compare conflict
  { diags := #[err 1 (unrealizable #["s = \"A\""] "`q0`") "F0601"], summary? := none0, exit? := some 1 }
  { diags := #[err 1 (unrealizable #["s = \"A\""] "`q1`" (hosted := true))], summary? := none0 }).2
-- The same input and requirements: they agree.
#guard agrees conflict
  { diags := #[err 1 (unrealizable #["s = \"A\""] "`q0` and `q1`") "F0601"], summary? := none0, exit? := some 1 }
  { diags := #[err 1 (unrealizable #["s = \"A\""] "`q0` and `q1`" (hosted := true))], summary? := none0 }
-- " when " elsewhere is text, not values.
#guard normHead "`p` holds when a" != normHead "`p` holds when b"

#guard isCheckResult (err 3 "expectation `c::x` does not hold")
#guard !isCheckResult (err 3 "expectation `c::x` does not hold here, but is a lint")
#guard isCheckResult (err 3 "a table in `c::r` may have no row that holds")
#guard isCheckResult (err 3 "rows 1 and 2 of a table in `c::r` may both hold")
#guard isCheckResult (err 3 "could not decide whether rows 1 and 2 of a table in `c::r` are disjoint: timeout")
#guard !isCheckResult (err 3 "rows 1 and 2 of a table in `c::r` may both hold, but is a lint")

end FrenTest.FrontendsCompare
