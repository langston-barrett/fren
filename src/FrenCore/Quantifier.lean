-- keep-sorted start
import FrenCore.Diagnostic
import Lean.Data.NameMap
-- keep-sorted end

/-!
# Quantifiers (`Reqs/Lang/Quantifiers`)

The rules of quantifiers, which both front ends follow: which types are
listed, so that a quantifier over them is expanded while elaborating, how
many instances it may have, what a binder of a global expectation ranges
over, and the guards that bound an unbounded quantifier, which set
`fmf-bound` and which the evaluator enumerates.
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

/-- Whether a type of kind `k` is listed, so that a quantifier over it is
expanded, from whether it is a recursive enumeration and whether all of
its constituents, the types of its payloads or fields, are listed: one
layer of the closure that `lang::quantified_type` states. -/
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
  /-- A type, listed or not. -/
  | typeName
  | component
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a binder is accepted, and whether it is one of the form that
global expectations were written in before (`F0416`), from what its type
names and whether it is in a global expectation's leading `forall`
(`lang::quantifier_binder`). -/
def quantifierBinder (target : BinderTarget) (global : Bool) : Bool × Bool :=
  match target with
  | .typeName => (true, false)
  | .component => (false, global)

/-- The number of instances of a quantifier whose bound names have types of
`sizes` values each. -/
def instanceCount (sizes : Array Nat) : Nat := sizes.foldl (· * ·) 1

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
procedure `c`. -/
def quantifiedComponentMsg (c : String) : Msg :=
  { code? := some "F0210", headline := s!"expected a type, but `{c}` is a procedure"
    label? := some "not a type"
    notes := #["note: a quantifier in an expression ranges over the values of a type",
      "help: to relate behaviours of a procedure, call it in a global expectation, as in `expect n(x: T) { call a := p(x) ... }`"] }

/-- A name bound twice by one quantifier. -/
def dupBoundMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"`{n}` is bound multiple times in this quantifier", label? := some "bound again here" }

/-! ## Guards (`Reqs/Lang/Quantifiers#guards`) -/

/-- An operand of a conjunct of a guard, seen from a bound name `x`
(`lang::GuardOperand`). -/
inductive GuardOperand where
  /-- `x` itself, written alone. -/
  | name
  /-- An expression that names neither `x` nor a bound name declared after
  it. -/
  | free
  /-- Any other expression. -/
  | later
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The relation of a conjunct of a guard (`lang::GuardRelation`). -/
inductive GuardRelation where
  | lt
  | le
  | gt
  | ge
  | mem
  /-- Anything else, whose operands are then irrelevant. -/
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The relation `op`, as written, of a comparison or a membership. -/
def GuardRelation.ofOp : String → GuardRelation
  | "<" => .lt
  | "<=" => .le
  | ">" => .gt
  | ">=" => .ge
  | "in" => .mem
  | _ => .other

/-- What a conjunct of a guard gives a bound name (`lang::Bound`). -/
inductive GuardBound where
  | members
  | lower
  | upper
  | none
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The bound that a conjunct `left relation right` gives a bound name,
from its operands seen from the name, and whether it is strict
(`lang::guard_bound`). -/
def guardBound (left : GuardOperand) (relation : GuardRelation) (right : GuardOperand) : GuardBound × Bool :=
  let strict := relation == .lt || relation == .gt
  let bound := match left, relation, right with
    | .name, .mem, .free => .members
    | .name, .gt, .free | .name, .ge, .free | .free, .lt, .name | .free, .le, .name => .lower
    | .name, .lt, .free | .name, .le, .free | .free, .gt, .name | .free, .ge, .name => .upper
    | _, _, _ => .none
  (bound, strict)

/-- A bound name's domain, from the bounds of its guard's conjuncts, naming
the conjuncts by position (`lang::Domain`). -/
inductive GuardDomain where
  /-- The members of the conjunct `x in e` at `k`. -/
  | members (k : Nat)
  /-- From the lower bound at `lo` to the upper bound at `hi`. -/
  | range (lo hi : Nat)
  /-- From 0 to the upper bound at `hi`. -/
  | fromZero (hi : Nat)
  | unbounded
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The domain of a bound name whose guard's conjuncts give `bounds`, in
order, where `nat` says that it is a `Nat` (`lang::guard_domain`), with
`members`, `lower` and `upper` the bounds as `bounds` names them: its
members, by the first conjunct that gives them; else the range from the
first lower bound to the first upper bound, or from 0 for a `Nat` without
a lower bound; else none. -/
def guardDomainBy [BEq β] (members lower upper : β) (bounds : List β) (nat : Bool) : GuardDomain :=
  match bounds.idxOf? members with
  | some k => .members k
  | none => match bounds.idxOf? lower, bounds.idxOf? upper with
    | some lo, some hi => .range lo hi
    | none, some hi => if nat then .fromZero hi else .unbounded
    | _, none => .unbounded

/-- `guardDomainBy` of the bounds as both front ends name them. -/
def guardDomain (bounds : List GuardBound) (nat : Bool) : GuardDomain :=
  guardDomainBy .members .lower .upper bounds nat

/-- A conjunct of a quantifier's guard, as written: its left operand, its
relation and its right operand, or `none` for one that is no comparison or
membership. -/
abbrev GuardConjunct (α : Type) := Option (α × GuardRelation × α)

/-- What a front end sees of a node of a guard, from its syntax, with the
parentheses around it removed. -/
inductive GuardNode (α : Type) where
  /-- `a and b`. -/
  | conj (a b : α)
  /-- A comparison or membership, chained or not: its operands, and the
  operator between each two. -/
  | compare (operands : Array α) (ops : Array String)
  | other

/-- The conjuncts of the guard `e` (`Reqs/Lang/Quantifiers#guards`): split
at the `and`s at its top, a chained comparison into its comparisons, each
a comparison or membership, or `none`, read by `view`. -/
partial def splitConjuncts (view : α → GuardNode α) (e : α) : Array (GuardConjunct α) :=
  match view e with
  | .conj a b => splitConjuncts view a ++ splitConjuncts view b
  | .compare xs ops => ops.zipIdx.map fun (op, i) =>
    let r := GuardRelation.ofOp op
    match r, xs[i]?, xs[i + 1]? with
    | .other, _, _ => none
    | _, some a, some b => some (a, r, b)
    | _, _, _ => none
  | .other => #[none]

/-- The conjuncts of the guard of a quantifier, a `forall` if `all`, whose
body is `body`: the conditions of the `when`s at the top of a `forall`'s
body, which `when?` reads, and an `exists`'s body. Both front ends read
guards with it. -/
partial def guardConjunctsBy (view : α → GuardNode α) (when? : α → Option (α × α)) (all : Bool) (body : α) :
    Array (GuardConjunct α) :=
  if all then
    match when? body with
    | some (c, d) => splitConjuncts view c ++ guardConjunctsBy view when? all d
    | none => #[]
  else splitConjuncts view body

/-- What the operand `e` of a conjunct is, seen from the bound name at
position `k` (`lang::guard_operand`): that name, if `alone e` is its
position, an expression that names it or a later one, by `names e`, or
another. -/
def guardOperandOf (alone : α → Option Nat) (names : α → List Nat) (k : Nat) (e : α) : GuardOperand :=
  if alone e == some k then .name else if (names e).any (· ≥ k) then .later else .free

/-- The bound that the conjunct `c` gives the bound name at position `k`,
and the expression that it reads, with whether it is strict
(`lang::conjunct_bound`). -/
def conjunctBound (alone : α → Option Nat) (names : α → List Nat) (k : Nat) (c : GuardConjunct α) :
    GuardBound × Option (α × Bool) :=
  match c with
  | some (a, r, b) =>
    let side := guardOperandOf alone names k
    let (bd, strict) := guardBound (side a) r (side b)
    -- The expression that the bound reads: the side that is not the name.
    (bd, if bd == GuardBound.none then none else some (if side a == GuardOperand.name then b else a, strict))
  | none => (.none, none)

/-- The domain of the bound name of position `k` among a quantifier's
bound names, from its guard's `conjuncts`, where `alone e` is the position
of the bound name that `e` is, written alone, and `names e` the positions
of the quantifier's bound names that `e` names (`lang::guard_domain`);
with the expressions that its bounds read, as the domain names them. -/
def boundDomain (alone : α → Option Nat) (names : α → List Nat) (conjuncts : Array (GuardConjunct α)) (k : Nat)
    (nat : Bool) : GuardDomain × Array (Option (α × Bool)) :=
  let bounds := conjuncts.map (conjunctBound alone names k)
  (guardDomain (bounds.map (·.1)).toList nat, bounds.map (·.2))

/-- A quantifier whose bound name cannot be enumerated, in what a check
of `what`, written as it is shown, by testing evaluates (`F0639`). -/
def untestableMsg (what : String) : Msg :=
  { code? := some "F0639", headline := s!"this quantifier cannot be evaluated, so {what} cannot be tested"
    label? := some "a bound name without a domain"
    notes := #["note: testing enumerates a bound name of a type that is not listed over its domain: the members in `x in s`, or the integers between a lower and an upper bound, as in `0 <= i < n`, in the guard",
      "help: guard the bound name, as in `forall (x: T), when x in s, ...` or `exists (i: Int), 0 <= i < q.len and ...`, or check it with the solver"] }

end Fren.Core
