-- keep-sorted start
import Fren.Elab.GlobalBlocks
import Fren.View
-- keep-sorted end
open Fren.Lang

-- Each attempt at induction has Lean's heartbeat limit to itself, and an
-- attempt that reaches it does not pass, so the claim keeps its own check's
-- verdict and message; the item's check does not fail
-- (`lang::induction_verdict`).
-- `len_append::adds` passes by induction on `a` at the default limit. At
-- 160 thousand heartbeats, its own check finishes and the attempt reaches
-- the limit, which failed the whole item's check, as a limit reached, until
-- the attempt was caught (#750); it did so from 130 to 200 thousand.
-- Heartbeat counts move with Lean and lean-smt: if an upgrade
-- makes this test fail, pick a limit again at which the claim's own check
-- finishes and the attempt does not.
pub enum L { Nil, Cons(Int, L) }

pub fn len(l: L): Int := match l {
    L::Nil => 0,
    L::Cons(_, r) => 1 + len(r),
}

pub fn append(a: L, b: L): L := match a {
    L::Nil => b,
    L::Cons(h, t) => L::Cons(h, append(t, b)),
}

expect len_append(a: L, b: L) { expect adds: len(append(a, b)) = len(a) + len(b) }

/--
warning: could not decide whether `len_append::adds` holds

note: this check fails under the contracts of `append`, `len`
note: evaluation of the recursive definitions does not confirm the counterexample: it refutes it, or cannot evaluate it
help: strengthen those functions' contracts
---
info: fren: 1 passed, 0 failed, 1 inconclusive, 0 redundant
-/
#guard_msgs in
set_option maxHeartbeats 160 in
#fren_check

/-- info: fren: 2 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check

-- The functions generated for induction are apart from the defined ones,
-- which every check reads, so they never weigh on the checks of other
-- items: 165 of them, from `Reqs/Lang`, made each query of every later
-- item cost more, and `lint::print_parens_refines` reached the limit
-- (#750). One for each candidate, `a` and `b`.
open Lean Elab Command Fren in
/-- info: defined: [append, len], generated: 2 -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let s := frenExt.getState (← getEnv)
  logInfo m!"defined: {s.defined.toList.map (·.1)}, generated: {s.inductionFns.size}"
