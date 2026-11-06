-- keep-sorted start
import FrenCore.Check.Backend
import FrenCore.Check.Component
-- keep-sorted end

/-!
# Check hypotheses and output substitution

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- Whether a check replaces defined outputs by their definitions, rather
than assuming the equations `D` (`check::definitions`): only
realizability, whose `∃` must not range over them. -/
def CheckKind.substitutes (k : CheckKind) : Bool := k == .realizable

/-- The definitions, as equations, for the hypotheses of a check of kind `k`. -/
def Comp.defEqs (c : Comp F) (k : CheckKind) : Array (Name × F) :=
  if k.substitutes then #[] else c.defs.map fun (n, eq, _) => (n, eq)

/-- `f`, with the defined outputs replaced by their definitions for a check
of kind `k`. -/
def Comp.subst (c : Comp F) (b : Backend m F V) (k : CheckKind) (f : F) : F :=
  if k.substitutes && !c.defs.isEmpty then b.subst (c.defs.map fun (n, _, e) => (n, e)) f else f

/-- `hs`, each with the defined outputs replaced by their definitions, for
realizability. -/
def Comp.substHyps (c : Comp F) (b : Backend m F V) (hs : Array (Name × F)) : Array (Name × F) :=
  hs.map fun (n, f) => (n, c.subst b .realizable f)

/-- Whether the queries of a check of kind `k` have a trait's laws among
their hypotheses (`check::query_hypotheses`): every check's but
realizability's, both of whose queries ask of the item's own assumptions
and calls alone. -/
def CheckKind.queryHasLaws (k : CheckKind) : Bool := k != .realizable

/-- What a check's queries have among their hypotheses
(`check::query_hypotheses`): the item's trait's laws, its assumptions, and
of each call, its bindings and the called procedure's behaviour, with the
called procedure's assumptions or only what follows from them. -/
structure HypParts where
  laws : Bool
  /-- Each call's procedure's assumptions as hypotheses, not only as the
  premise of its guarantees. -/
  callAssumptions : Bool
  deriving Inhabited, DecidableEq, Repr

/-- What the queries of a check of kind `k` have among their hypotheses,
or, `lawful`, those of an item's vacuity under its trait's laws
(`check::query_hypotheses`): every check's queries have the laws but
realizability's, and each call's procedure's assumptions; the vacuity
under the laws has the laws, and of a call only what its procedure
guarantees where its assumptions hold, which the call checks apart
(`checkInst`), as the item's realizability does not ask them either. -/
def hypParts (k : CheckKind) (lawful : Bool) : HypParts :=
  if lawful then { laws := true, callAssumptions := false }
  else { laws := k.queryHasLaws, callAssumptions := true }

/-- The item as the queries of a check of kind `k` see it: without its
trait's laws where `hypParts` leaves them out. -/
def Comp.forKind (c : Comp F) (k : CheckKind) : Comp F :=
  if (hypParts k false).laws then c else { c with laws := #[] }

/-- The laws, the assumptions, then what each call contributes (`I`). -/
def Comp.hyps (c : Comp F) (b : Backend m F V) (upTo : Nat := c.insts.size) : Array (Name × F) :=
  c.laws ++ c.assumes ++ (c.insts.extract 0 upTo).map fun i => (i.name, b.conj #[i.bindings, i.behaviour])

/-- The outputs whose values a clash note may give: the public ones that
are not defined, since realizability replaces those by their definitions. -/
def Comp.clashOutputs (c : Comp F) : Array Name :=
  (c.vars.filter fun v => v.role == .output && v.isPub && !c.defs.any (·.1 == v.name)).map (·.name)

/-- Whether the values of a realizability conflict's clash notes would
depend on an interpretation (`check::clash_notes`), as a cover goal's
witness would (`coverInterpreted`): whether some variable's type is
abstract, or some formula of the notes' queries, a guarantee or a
definition substituted into one, uses an abstract type or an
uninterpreted function, as `interprets` says of a formula. -/
def Comp.realizableInterpreted (c : Comp F) (interprets : F → Bool) : Bool :=
  c.typesInterpreted || (c.defs.map (·.2.1) ++ c.reqs.map (·.2)).any interprets

/-- The SAT shortcut is only a fresh-output declaration carrier, never a
procedure whose inputs, definitions, assumptions or calls need the ordinary
universal-completion protocol. Interpretation freedom is checked separately. -/
def Comp.fixedInhabitation (c : Comp F) (interprets : F → Bool := fun _ => false) : Bool :=
  c.inhabitation && !c.realizableInterpreted interprets && c.defs.isEmpty &&
    c.laws.isEmpty && c.assumes.isEmpty && c.insts.isEmpty && c.vars.all (·.role == .output)

end Fren.Core
