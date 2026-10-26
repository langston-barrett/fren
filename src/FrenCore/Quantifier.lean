-- keep-sorted start
import FrenCore.Diagnostic
import Lean.Data.NameMap
-- keep-sorted end

/-!
# Quantifiers (`Reqs/Lang/Quantifiers`)

The rules of quantifiers over finite types, which both front ends expand
while elaborating: which types a quantifier ranges over, how many instances
it may have, and what a binder of a global expectation ranges over.
-/

open Lean

namespace Fren.Core

/-- The kind of a type, as `lang::quantified_type` sees it. -/
inductive QuantifiedKind where
  | bool
  | enum
  | record
  /-- `Int`, `Nat`, `String`, an abstract type, or a set, relation or
  sequence type. -/
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a quantifier ranges over a type of kind `k`, from whether it is
a recursive enumeration and whether a quantifier ranges over the types of
all of its payloads or fields (`lang::quantified_type`). -/
def quantifiedTypeAccepted (k : QuantifiedKind) (recursive parts : Bool) : Bool :=
  match k with
  | .bool => true
  | .enum => parts && !recursive
  | .record => parts
  | .other => false

/-- The most instances a quantifier may have (`lang::MAX_INSTANCES`). -/
def maxInstances : Nat := 256

/-- Whether a quantifier of `n` instances is accepted (`lang::quantifier_size`). -/
def quantifierSizeAccepted (n : Nat) : Bool := n ≤ maxInstances

/-- What a binder's type names (`lang::BinderTarget`). -/
inductive BinderTarget where
  /-- A type that a quantifier ranges over. -/
  | listedType
  | otherType
  | component
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a binder is accepted, and whether it ranges over a component's
behaviours, from what its type names and whether it is in a global
expectation's leading `forall` (`lang::quantifier_binder`). -/
def quantifierBinder (target : BinderTarget) (global : Bool) : Bool × Bool :=
  match target with
  | .listedType => (true, false)
  | .otherType => (false, false)
  | .component => (global, true)

/-- The number of instances of a quantifier whose bound names have types of
`sizes` values each. -/
def instanceCount (sizes : Array Nat) : Nat := sizes.foldl (· * ·) 1

/-- A quantifier over `ty`, which it does not range over (`F0355`);
`collection` if `ty` is or contains a set, relation or sequence type. -/
def quantifiedTypeMsg (ty : String) (collection : Bool) : Msg :=
  { code? := some "F0355", headline := s!"a quantifier cannot range over `{ty}`"
    label? := some "not a type whose values can be listed"
    notes := #["note: a quantifier ranges over `Bool`, an enum or record whose payloads and fields it ranges over, or a pattern type whose base type it ranges over or whose integer ranges are bounded",
      if collection then "help: to quantify over the members of a set `s`, quantify over their type: `forall (x: T), when x in s, ...`"
      else "help: state it of a variable of that type instead, which the checks hold for every value of"] }

/-- A quantifier of `n` instances, more than `maxInstances` (`F0356`),
counting those of the quantifiers around it if `nested`. -/
def quantifierSizeMsg (n : Nat) (nested : Bool := false) : Msg :=
  { code? := some "F0356"
    headline := if nested then s!"with the quantifiers around it, this quantifier has {n} instances, more than {maxInstances}"
      else s!"this quantifier has {n} instances, more than {maxInstances}"
    label? := some s!"{n} instances"
    notes := #[s!"note: a quantifier is expanded into one instance for each combination of the values of its bound names, at most {maxInstances}",
      "help: quantify over a smaller type, or state it of a variable of that type instead"] }

/-- A binder of a quantifier in an expression whose type names the
component `c`. -/
def quantifiedComponentMsg (c : String) : Msg :=
  { code? := some "F0210", headline := s!"expected a type, but `{c}` is a component"
    label? := some "not a type"
    notes := #["note: a quantifier in an expression ranges over the values of a type",
      "help: only a global expectation's leading `forall` ranges over the behaviours of a component"] }

/-- A name bound twice by one quantifier. -/
def dupBoundMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"`{n}` is bound multiple times in this quantifier", label? := some "bound again here" }

end Fren.Core
