-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang

-- A quantifier's Lean definition is its expansion (`Reqs/Generated#components`):
-- the body at each value, conjoined by `∧`, or by `∨` for `exists`, as a
-- balanced tree, with no `∀`, `∃` or `Fintype` left.
mod quant

enum Method { Len, Card, Rev }

struct Pair { a?, b? }

comp c {
  in x: Method
  pub out all_other?
  pub out some_pair?
  pub out nested?

  ensure all_other: all_other? iff (forall (m: Method), m != x)
  ensure some_pair: some_pair? iff (exists (p: Pair), p.a? and not p.b?)
  ensure nested: nested? iff (forall (a? b?: Bool), a? or b?)
}

/--
info: @[reducible] def quant.c.ensure.all_other : quant.Method → Bool → Bool → Bool → Prop :=
fun x all_other? some_pair? nested? =>
  all_other? = true ↔ quant.Method.Len ≠ x ∧ quant.Method.Card ≠ x ∧ quant.Method.Rev ≠ x
-/
#guard_msgs in
#print quant.c.ensure.all_other

-- A record's values are every combination of its fields', the last field
-- fastest, and `Bool`'s are `true` then `false`.
/--
info: @[reducible] def quant.c.ensure.some_pair : quant.Method → Bool → Bool → Bool → Prop :=
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
info: @[reducible] def quant.c.ensure.nested : quant.Method → Bool → Bool → Bool → Prop :=
fun x all_other? some_pair? nested? =>
  nested? = true ↔
    ((true = true ∨ true = true) ∧ (true = true ∨ false = true)) ∧
      (false = true ∨ true = true) ∧ (false = true ∨ false = true)
-/
#guard_msgs in
#print quant.c.ensure.nested
