-- keep-sorted start
import Fren.Elab
-- keep-sorted end
open Fren.Lang

-- A quantifier's Lean definition is its expansion (`Reqs/Generated#components`):
-- the body at each value, conjoined by `∧`, or by `∨` for `exists`, as a
-- balanced tree, with no `∀`, `∃` or `Fintype` left.
mod quant

enum Method { Len, Card, Rev }

struct Pair { a?, b? }

proc c(x: Method): (all_other?, some_pair?, nested?) {
  ensure all_other: all_other? iff (forall (m: Method), m != x)
  ensure some_pair: some_pair? iff (exists (p: Pair), p.a? and not p.b?)
  ensure nested: nested? iff (forall (a? b?: Bool), a? or b?)
}

/--
info: @[reducible] def Fren.Generated.quant.c.ensure.all_other : quant.Method → Bool → Bool → Bool → Prop :=
fun x all_other? some_pair? nested? =>
  all_other? = true ↔ quant.Method.Len ≠ x ∧ quant.Method.Card ≠ x ∧ quant.Method.Rev ≠ x
-/
#guard_msgs in
#print quant.c.ensure.all_other

-- A record's values are every combination of its fields', the last field
-- fastest, and `Bool`'s are `true` then `false`.
/--
info: @[reducible] def Fren.Generated.quant.c.ensure.some_pair : quant.Method → Bool → Bool → Bool → Prop :=
fun x all_other? some_pair? nested? =>
  some_pair? = true ↔
    ({ a? := true, b? := true }.a? = true ∧ ¬{ a? := true, b? := true }.b? = true ∨
        { a? := true, b? := false }.a? = true ∧ ¬{ a? := true, b? := false }.b? = true) ∨
      { a? := false, b? := true }.a? = true ∧ ¬{ a? := false, b? := true }.b? = true ∨
        { a? := false, b? := false }.a? = true ∧ ¬{ a? := false, b? := false }.b? = true
-/
#guard_msgs in
#print quant.c.ensure.some_pair

-- Two bound names: every combination, the last fastest, in one balanced tree.
/--
info: @[reducible] def Fren.Generated.quant.c.ensure.nested : quant.Method → Bool → Bool → Bool → Prop :=
fun x all_other? some_pair? nested? =>
  nested? = true ↔
    ((true = true ∨ true = true) ∧ (true = true ∨ false = true)) ∧
      (false = true ∨ true = true) ∧ (false = true ∨ false = true)
-/
#guard_msgs in
#print quant.c.ensure.nested

-- An erased, unused binder keeps the body's computable decision and its
-- simplification rule, including in a conditional and a Boolean local.
set_option fren.lint.unused_variables "allow"
set_option fren.lint.undecidable "allow"

pub fn unused_if(a: Int): Int := if (forall (u: Int), a = -1) then 1 else 0
set_option fren.lint.redundant_bool_type "allow" in
pub fn unused_bool(a: Int): Int := let b?: Bool := (forall (u: Int), a = -1) in if b? then 1 else 0

#guard_msgs in
#eval show IO Unit from do
  unless quant.unused_if (-1) == 1 && quant.unused_if 0 == 0 do
    throw (IO.userError "an unused quantifier's if did not compile or compute")
  unless quant.unused_bool (-1) == 1 && quant.unused_bool 0 == 0 do
    throw (IO.userError "an unused quantifier's Boolean local did not compile or compute")

example (a : Int) : Fren.unusedQuantifier Int (a = -1) ↔ a = -1 := by
  simp [fren_spec]
