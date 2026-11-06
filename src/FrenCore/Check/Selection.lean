-- keep-sorted start
import FrenCore.Check.Types
-- keep-sorted end

/-!
# Selecting checks for an item

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type}

/-- A split predicate member is reported at its definition. A whole
predicate, including a cover goal, stays at its written check's label
(`check::predicate_check_site`). Leading wrappers do not change the site. -/
def predicateCheckAtMember (memberPath : String) (cover : Bool) : Bool :=
  !cover && memberPath != ""

/-- The checks of a global expectation (`check::applies`), as a `Comp`:
those of a procedure, but for redundancy and determinism, since it
constrains nothing; with no outputs, its realizability is that its
assumptions are satisfiable (`Reqs/Lang/Global#meaning`). -/
def globalKinds : Array CheckKind :=
  #[.realizable, .inst, .expect, .cover, .vacuity, .definedness, .completeness, .disjointness, .precondition,
    .reachability]

/-- The checks of the tables, `match`es and applications in the body and contract of
a function or the value of a constant, and of a defined function's
postconditions (`check::applies`), as a `Comp` whose path is its module,
with its parameters as inputs and its preconditions as assumptions. -/
def bodyKinds : Array CheckKind := #[.definedness, .completeness, .disjointness, .precondition, .postcondition, .reachability]

/-- The checks of the contract of an uninterpreted function with
postconditions (`check::applies`), as a `Comp` whose path is its module,
with its parameters as inputs, its value as its one `out`, its
preconditions as assumptions and its postconditions, of its value, as
guarantees: whether they can hold together, and the tables and
applications in its clauses. -/
def contractKinds : Array CheckKind := #[.realizable, .completeness, .disjointness, .precondition, .reachability]

/-- The checks run on a global expectation if `global`, else on a procedure
(`check::applies`). -/
def kindsFor (global : Bool) : Array CheckKind :=
  if global then globalKinds else CheckKind.all

/-- What the checks run on (`check::CheckedItem`). -/
inductive CheckedItem where
  | component
  | global
  /-- A global expectation in the short form, `expect n: e`, which has no
  assumptions to satisfy. -/
  | shortGlobal
  /-- The body and contract of a function, or the value of a constant. -/
  | body
  /-- The contract of an uninterpreted function with postconditions. -/
  | contract
  deriving Inhabited, DecidableEq, Repr

/-- What an item of a front end is (`check::CheckedItem`): a function's
body or contract (`body`), the contract where it has its value as an output
(`output`); a global expectation (`global`), in the short form where
`short`; otherwise a procedure. Both front ends decide it with this. -/
def CheckedItem.of (body output global short : Bool) : CheckedItem :=
  if body then (if output then .contract else .body)
  else if global then (if short then .shortGlobal else .global) else .component

/-- The checks run on an item (`check::applies`). -/
def CheckedItem.kinds : CheckedItem → Array CheckKind
  | .component => kindsFor false
  | .global => kindsFor true
  | .shortGlobal => (kindsFor true).filter (· != .realizable)
  | .body => bodyKinds
  | .contract => contractKinds

/-- The kinds of check that both front ends run on a procedure of `kinds`:
on the procedure that checks a subset type's inhabitation (`subset`), only
its realizability, and on the one that checks that its invariants are
defined (`subsetInvariant`), only the checks of its clauses
(`Reqs/Lang/SubsetTypes`). -/
def kindsRun (subset subsetInvariant : Bool) (kinds : Array CheckKind) : Array CheckKind :=
  if subset then #[.realizable]
  else if subsetInvariant then #[.definedness, .completeness, .disjointness, .precondition] else kinds

/-- The checks reported of the contract of a generic function without a
body (`lang::generic_contract`), from its check at its type parameters'
sorts, `atSorts`, and, where that does not pass, its check at each instance
that the spec applies, `instances`, which `fren` and the hosted front end
run only then: the opaque check if it passes or the spec applies no
instance, and otherwise each instance's. -/
def genericContract {α : Type} (verdict : α → Verdict) (atSorts : α) (instances : Array α) : Array α :=
  match verdict atSorts with
  | .pass => #[atSorts]
  | _ => if instances.isEmpty then #[atSorts] else instances

end Fren.Core
