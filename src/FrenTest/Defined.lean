-- keep-sorted start
import Fren.Impl
-- keep-sorted end
open Fren.Lang

-- Defined functions in Lean: each is a definition, which `impl` proofs
-- unfold, and which needs no interpretation.
mod defined_test

type Key
fn double(n: Int): Int := 2 * n
-- Only `#check`ed, below.
set_option fren.lint.dead_code "allow" in
fn same?(a: Key, b: Key) := a = b

comp doubler {
    in x: Int
    pub out y: Int

    ensure r: y = double(x)
}

/-- info: defined_test.double : Int → Int -/
#guard_msgs in #check @defined_test.double

/-- info: defined_test.same? : (Key : Type) → Key → Key → Bool -/
#guard_msgs in #check @defined_test.same?

def dbl (n : Int) : Int := n + n

impl dbl_doubler: doubler for (n : Int) { x := n, y := dbl n } by
  intro n _
  simp [fren_spec, dbl]
  omega

/--
error: expected an abstract type or an uninterpreted function, but `defined_test::double` is a function
-/
#guard_msgs in interp double := fun (n : Int) => n
