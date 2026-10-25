-- keep-sorted start
import Fren
-- keep-sorted end

-- Lean-only behaviour of record updates: `{ r with x := e }` generates the
-- record's constructor applied to `e` and to the other fields read from `r`,
-- which is what Lean's own `{ r with x := e }` means.

open Fren.Lang

mod record_update_test

pub struct Point { x: Int, y: Int }

comp moves {
  in p: Point
  in n: Int
  pub out q: Point

  req r: q = { p with x := n }
  req s: q = { { p with y := 0 } with x := n }
}

/--
info: @[reducible] def record_update_test.moves.req.r : record_update_test.Point → Int → record_update_test.Point → Prop :=
fun p n q => q = { x := n, y := p.y }
-/
#guard_msgs in
#print record_update_test.moves.req.r

-- Lean's record update means the same.
example (p : record_update_test.Point) (n : Int) (q : record_update_test.Point) :
    record_update_test.moves.req.r p n q ↔ q = { p with x := n } := Iff.rfl

-- An updated value that is not a name is bound once, so that nested updates
-- grow linearly.
/--
info: @[reducible] def record_update_test.moves.req.s : record_update_test.Point → Int → record_update_test.Point → Prop :=
fun p n q =>
  q =
    let r := { x := p.x, y := 0 };
    { x := n, y := r.y }
-/
#guard_msgs in
#print record_update_test.moves.req.s
