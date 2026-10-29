-- keep-sorted start
import Fren.View
-- keep-sorted end

/-! Reflected recursive contracts unfold implicit subset predicates just as
explicit preconditions. The executable predicate uses a Lean match; its solver
form uses constructor tests. Sending the executable form to SMT used to make
this real contract violation inconclusive with an unsupported lambda. -/
open Fren.Lang

enum RecursiveSubsetTree { Zero, Succ(RecursiveSubsetTree) }
type RecursiveSubsetSuccessor = value: RecursiveSubsetTree where invariant:
    value is RecursiveSubsetTree::Succ(_)
pub fn recursive_subset_bad(t: RecursiveSubsetSuccessor): (r: Int) {
    out r := match t {
        RecursiveSubsetTree::Zero => 1,
        RecursiveSubsetTree::Succ(a) =>
            if a is RecursiveSubsetTree::Succ(_) then recursive_subset_bad(a) else 1,
    }
    ensure zero: r = 0
}

/--
error: the postcondition `zero` of `recursive_subset_bad` does not hold

counterexample: t = RecursiveSubsetTree::Succ(RecursiveSubsetTree::Zero)
help: correct the body or the postcondition, or add a precondition that rules this case out
---
info: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check
