-- keep-sorted start
import Fren.Impl
-- keep-sorted end

-- Lean-only behaviour of tables: a table generates `if`s over its rows'
-- conditions, and without a `_` row, where no row holds, an index out of
-- range of the empty sequence, `Fren.Seq.nth ∅ 0`, which is what the solver
-- sees: one unspecified value of each type.

open Fren.Lang

mod table_test

comp sign {
  in x: Int
  pub out s: Int

  ensure r: s = table { x > 0 => 1, x < 0 => -1, x = 0 => 0 }
  ensure w: s = table { x > 0 => 1, x < 0 => -1, _ => 0 }
}

/--
info: @[reducible] def table_test.sign.ensure.r : Int → Int → Prop :=
fun x s => s = if x > 0 then 1 else if x < 0 then -1 else if x = 0 then 0 else ∅.nth 0
-/
#guard_msgs in
#print table_test.sign.ensure.r

/--
info: @[reducible] def table_test.sign.ensure.w : Int → Int → Prop :=
fun x s => s = if x > 0 then 1 else if x < 0 then -1 else 0
-/
#guard_msgs in
#print table_test.sign.ensure.w

-- The solver proves an `impl` of a component with a table.
#guard_msgs in
impl sign_impl: sign for (x : Int) { x := x, s := if x > 0 then 1 else if x < 0 then -1 else 0 }

-- Two tables of one type that have no `_` row are the same value where
-- neither has a row that holds, for the solver and in Lean alike: `r`
-- holds of every `x`, so the solver proves the `impl`, and so does Lean,
-- whose definition the `impl`'s axiom is about.
comp coincide {
  in x: Int

  ensure r: x > 0 or table { x > 0 => 1 } = table { x > 0 => 2 }
}

#guard_msgs in
impl coincide_impl: coincide for (x : Int) { x := x }

example (x : Int) : table_test.coincide.ensure.r x := by
  by_cases h : x > 0 <;> simp [table_test.coincide.ensure.r, h]

-- Where no row holds, a table's value is unknown to the solver, so this
-- implementation is not proved: the solver cannot show that it is the
-- implementation's value.
comp incomplete {
  in x: Int
  pub out s: Int

  ensure r: s = table { x > 0 => 1 }
}

/--
warning: could not prove that `incomplete_impl` implements `table_test::incomplete`

note: `decide` does not apply, and the solver does not see the definitions of the implementation
help: write a proof after `by`
-/
#guard_msgs in
impl incomplete_impl: incomplete for (x : Int) { x := x, s := 1 }
