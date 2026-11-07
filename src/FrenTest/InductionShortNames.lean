-- keep-sorted start
import Fren.Elab.GlobalExpectations
import Fren.View
-- keep-sorted end
open Fren.Lang

mod short_names

-- fren-covers: lang::induction_candidate, lang::induction_verdict

-- A template's temporary procedure name is not the global expectation's
-- identity. Different claims at the same reference position need distinct
-- induction functions, as happens across files of one module.
set_option fren.lint.undecidable "allow"
set_option fren.lint.assertions_on_constants "allow"
set_option fren.lint.duplicate_constraint "allow"

pub enum L { Nil, Cons(Int, L) }
pub fn len(l: L): Int := match l { L::Nil => 0, L::Cons(_, t) => 1 + len(t) }

open Lean Elab Command Fren in
run_cmd do
  let ref ← getRef
  for text in #["expect short_a: forall (a: L), len(a) >= 0",
      "expect short_b: forall (a: L), len(a) > -1"] do
    elabCommand (← parseAt `command text ref)

/-- info: fren: 1 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check short_a

/-- info: fren: 1 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check short_b
