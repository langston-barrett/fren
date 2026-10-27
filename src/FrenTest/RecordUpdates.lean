-- keep-sorted start
import Fren.Impl
-- keep-sorted end

-- Lean-only behaviour of record updates: `{ r with x := e }` generates the
-- record's constructor applied to `e` and to the other fields read from `r`,
-- which is what Lean's own `{ r with x := e }` means.

open Fren.Lang

mod record_update_test

pub struct Point { x: Int, y: Int }

proc moves(p: Point, n: Int): (q: Point) {
  ensure r: q = { p with x := n }
  ensure s: q = { { p with y := 0 } with x := n }
}

/--
info: @[reducible] def Fren.Generated.record_update_test.moves.ensure.r : record_update_test.Point →
  Int → record_update_test.Point → Prop :=
fun p n q => q = { x := n, y := p.y }
-/
#guard_msgs in
#print record_update_test.moves.ensure.r

-- Lean's record update means the same.
example (p : record_update_test.Point) (n : Int) (q : record_update_test.Point) :
    record_update_test.moves.ensure.r p n q ↔ q = { p with x := n } := Iff.rfl

-- An updated value that is not a name is bound once, so that nested updates
-- grow linearly.
/--
info: @[reducible] def Fren.Generated.record_update_test.moves.ensure.s : record_update_test.Point →
  Int → record_update_test.Point → Prop :=
fun p n q =>
  q =
    let r := { x := p.x, y := 0 };
    { x := n, y := r.y }
-/
#guard_msgs in
#print record_update_test.moves.ensure.s

-- The solver proves an `impl` of a component with a bound update: the
-- `let` is reduced away before lean-smt, which does not translate it.
proc resets(p: Point): (q: Point) {
  ensure r: q = { { p with y := 0 } with x := 1 }
}

#guard_msgs in
impl reset_impl: resets for (p : record_update_test.Point) { p := p, q := ⟨1, 0⟩ }
