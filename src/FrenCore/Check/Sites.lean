-- keep-sorted start
import FrenCore.Check.Hypotheses
import FrenCore.Check.Query
-- keep-sorted end

/-!
# Definedness, cases and postconditions

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- The hypotheses of an index's place, for `definedness`. -/
def Comp.siteHyps (c : Comp F) (b : Backend m F V) (site : IndexSite F) : Array (Name × F) :=
  let own (name : Name) := name == site.prop || (site.excludeSelf &&
    (name.toString (escape := false)).startsWith (site.prop.toString (escape := false) ++ "."))
  match site.place with
  | .assume => c.assumes.filter (!own ·.1)
  | .binding k => c.hyps b k
  | .prop => c.hyps b ++ (if site.excludeSelf then c.reqs.filter (!own ·.1) else c.reqs)
  | .body => c.assumes

/-- `definedness`: the index is in range wherever it is evaluated, given the
hypotheses of its place (`check::definedness`): for an assumption, the
other assumptions; for a binding, the assumptions and earlier calls;
otherwise the assumptions, calls and requirements. -/
def checkDefinedness (c : Comp F) (site : IndexSite F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .definedness, comp := c.path, prop? := some site.prop, index? := some site.k, verdict, detail
      subsetTy? := site.subsetTy? }
  let hyps := c.defEqs .definedness ++ c.siteHyps b site
  let q ← b.query hyps site.goal true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b hyps site.goal model vals verdict (.counterexample vals)
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- The questions about the rows of `c`'s tables that the checks of kind
`k` answer. -/
def Comp.tablesOf (c : Comp F) (k : CheckKind) : Array (TableSite F) := c.tables.filter (·.goal.kind == k)

/-- Whether reachability asks under a hypothesis, from whether it is one
of definedness's at the case and whether it is the constraint, definition
or binding that the case is in (`check::reach_hypothesis`). -/
def reachUses (definedness enclosing : Bool) : Bool := definedness && !enclosing

/-- The hypotheses of the checks of kind `kind` that leave out the
constraint, definition or binding that a case is in, reachability and
disjointness (`check::reach_hypothesis`): those of its place for
`definedness`, the definitions among them, but that one. -/
def Comp.caseHyps (c : Comp F) (b : Backend m F V) (kind : CheckKind) (site : IndexSite F) : Array (Name × F) :=
  (c.defEqs kind ++ c.siteHyps b site).filter fun h => reachUses true (h.1 == site.prop)

/-- The hypotheses of a case's reachability: those of its place for
`definedness`, the definitions among them, but the constraint, definition
or binding that it is in, which may rule out the behaviours that take the
case only because the case is written in it, as in `ensure r: match k { A
if ok? => true, _ => false }`, or in the definition of `y` beside `ensure
q: y = 1` (`check::reachability`). A binding's own call is never
among them. -/
def Comp.reachHyps (c : Comp F) (b : Backend m F V) (site : IndexSite F) : Array (Name × F) :=
  c.caseHyps b .reachability site

/-- The hypotheses of a question about the cases of a table or a `match`
but reachability: those of its place, as for `definedness`, but for
disjointness, which leaves out the constraint, definition or binding that
the table is in, as reachability does (`Comp.caseHyps`): it holds only
where the table has the value it needs, so it would hide two rows that
overlap where it does not (`check::disjointness`). -/
def Comp.tableHyps (c : Comp F) (b : Backend m F V) (t : TableSite F) : Array (Name × F) :=
  if t.goal.kind == .disjointness then c.caseHyps b .disjointness t.site
  else c.defEqs t.goal.kind ++ c.siteHyps b t.site

/-- `completeness` or `disjointness`: what the question about the cases of
a table or a `match` asks holds wherever it is evaluated, given the
hypotheses of its place (`Comp.tableHyps`) (`check::completeness`,
`check::disjointness`). -/
def checkTable (c : Comp F) (t : TableSite F) : m CheckResult := do
  let kind := t.goal.kind
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind, comp := c.path, prop? := some t.site.prop, site? := some t.site.k, rows? := t.goal.rows?,
      target? := t.goal.target?, goal? := some t.goal, verdict, detail }
  let q ← b.query (c.tableHyps b t) t.site.goal true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b (c.tableHyps b t) t.site.goal model vals verdict (.counterexample vals)
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `postcondition`: the postcondition `p` of a defined function, named
after the function and the clause, follows from its preconditions, its
parameters free (`check::postcondition`); for a structural recursion, by
simultaneous Hoare induction with facts at actual applications. -/
def checkPostcondition (c : Comp F) (p : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .postcondition, comp := c.path, prop? := some p.1, target? := c.fn?.map (·, Name.mkSimple p.1.getString!),
      verdict, detail }
  let q ← b.query (c.assumes) p.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b c.assumes p.2 model vals verdict (.counterexample vals)
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `reachability`: the case of a table or a `match` that the question is
about can be taken somewhere it is evaluated, given the hypotheses of its
place but the constraint it is in (`Comp.reachHyps`): its goal, that the
case is not taken there, cannot be proved, as for `vacuity`
(`check::reachability`). -/
def checkReach (c : Comp F) (t : TableSite F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .reachability, comp := c.path, prop? := some t.site.prop, site? := some t.site.k, goal? := some t.goal
      verdict, detail }
  let q ← b.query (c.reachHyps b t.site) t.site.goal false
  match vacuityVerdict q.answer with
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | verdict => return result verdict

end Fren.Core
