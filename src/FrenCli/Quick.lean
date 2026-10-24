-- keep-sorted start
import FrenCli.Confirm
import FrenCli.Search
-- keep-sorted end

/-!
# Testing specs on random behaviours (`Reqs/Eval#fren-quickcheck`)

Each test chooses an interpretation, an admissible input, behaviours of
the instances and outputs, by the search of `FrenCli.Search`, and reports
what it refutes as the checks would (`eval::test_verdict`). Every
counterexample has been evaluated, so it is genuine (`eval::sound`).
-/

open Lean

namespace FrenCli.Eval

open Fren.Core (CheckResult CheckKind Assignment)

/-- What testing one check found. -/
structure Tally where
  tests : Nat := 0
  /-- The first counterexample. -/
  refuted? : Option Fren.Core.Detail := none

def Tally.reach (t : Tally) : Tally := { t with tests := t.tests + 1 }

def Tally.refute (t : Tally) (d : Fren.Core.Detail) : Tally :=
  if t.refuted?.isSome then t else { t with refuted? := some d }

def Spec.shown (sp : Spec) (vars : Array Var) (env : Env) (keep : Var → Bool) : Assignment :=
  vars.filterMap fun v => if keep v then env[v.name]?.map (v.name, ·.show sp) else none

/-- The variables of `vars` to choose, in `order`, other than those in `env`. -/
def remaining (order : Array (Name × VTy)) (env : Env) : Array (Name × VTy) := order.filter (!env.contains ·.1)

/-- An admissible input, with behaviours of the instances: the instance
assumptions that a test refutes, and the instance whose behaviour was not
found, if any. -/
structure Admitted where
  env : Env
  /-- Counterexamples to instance assumptions: the instance, the
  instantiated comp, its assumption, and the shown values. -/
  instFails : Array (Name × Name × Name × Assignment) := #[]
  /-- The instances reached, by index, for counting. -/
  reached : Nat := 0
  complete : Bool := false

/-- Searches for an admissible input, then for each instance in turn
confirms its assumptions on its inputs and searches for its behaviour. -/
def Spec.admit (sp : Spec) (w : World) (c : Comp) : R (Option Admitted) := do
  let I := w.interp sp
  let assumes := atomsOf .anonymous (c.ofKind .assume)
  let inputs := c.vars.filter (·.role == .input) |>.map fun v => (v.name, v.ty)
  let some env ← ({ vars := inputs, atoms := assumes, ints := intsOf (sp.meaning c) : Problem }.solve sp w I {})
    | return none
  let vars := sp.flatVars c
  let mut env := env
  let mut out : Admitted := { env }
  for i in c.insts, k in [0:c.insts.size] do
    let some d := sp.comp? i.comp | return none
    let ins := d.vars.filter (·.role == .input) |>.map fun v => (i.name ++ v.name, v.ty)
    let binds := bindingAtoms .anonymous i
    let some env' ← ({ vars := ins, atoms := binds, ints := intsOf binds : Problem }.solve sp w I env) | return some out
    env := env'
    out := { out with env, reached := k + 1 }
    -- Inputs and the earlier instances' public outputs (`checkInst`).
    let later := (c.insts.extract k).map (·.name)
    let shown := sp.shown vars env fun v => v.role.isUniversal && v.isPub && !later.contains v.name.getRoot
    let mut failed := false
    for a in d.ofKind .assume do
      if ({ label := a.name, pfx := i.name, e := a.e } : Atom).eval I env.look == some false then
        out := { out with instFails := out.instFails.push (i.name, d.path, a.name, shown) }
        failed := true
    if failed then return some out
    let atoms := sp.instAtoms .anonymous i
    let some env' ← ({ vars := remaining (sp.order d i.name) env, atoms, ints := intsOf atoms : Problem }.solve sp w I env)
      | return some out
    env := env'
    out := { out with env }
  return some { out with complete := true }

structure Report where
  results : Array CheckResult := #[]
  /-- Inputs for which no outputs were found (`F0609`). -/
  noOutputs? : Option Assignment := none
  /-- No test found an admissible behaviour (`F0610`). -/
  untested : Bool := false

def verdictOf (kind : CheckKind) (t : Tally) : Fren.Core.Verdict :=
  match t.refuted? with
  | some _ => if kind == .realizable then .inconclusive else .fail
  | none => if t.tests > 0 then .pass else .inconclusive

/-- Tests the comp `c` (`eval::test_verdict`). -/
def Spec.quickComp (sp : Spec) (c : Comp) (tests : Nat) : R Report := do
  let vars := sp.flatVars c
  let expects := c.ofKind .expect
  let dets := c.vars.filter (·.isDet)
  let instAssumes := c.insts.flatMap fun i =>
    ((sp.comp? i.comp).map fun d => (d.ofKind .assume).map fun a => (i.name, d.path, a.name)).getD #[]
  let mut realizable : Tally := {}
  let mut expT : Array Tally := expects.map fun _ => {}
  let mut detT : Array Tally := dets.map fun _ => {}
  let mut instT : Array Tally := instAssumes.map fun _ => {}
  let mut noOutputs? := none
  let mut behaviours := 0
  -- The definitions, so that the search computes defined outputs.
  let reqs := c.defAtoms ++ atomsOf .anonymous (c.ofKind .req)
  let all := sp.meaning c
  let ints := intsOf all
  for _ in [0:tests] do
    let w ← World.random sp
    let I := w.interp sp
    let some adm ← sp.admit w c | continue
    for (x, k) in instAssumes.zipIdx do
      let reached := (c.insts.findIdx? (·.name == x.1)).any (· < adm.reached)
      if reached then instT := instT.modify k Tally.reach
      if let some (_, _, _, shown) := adm.instFails.find? fun (w, _, a, _) => w == x.1 && a == x.2.2 then
        instT := instT.modify k (·.refute (.counterexample shown))
    unless adm.complete do continue
    realizable := realizable.reach
    let outs := c.vars.filter (·.role == .output) |>.map fun v => (v.name, v.ty)
    let some env ← ({ vars := outs, atoms := reqs, ints : Problem }.solve sp w I adm.env)
      | let input := sp.shown vars adm.env fun v => v.role.isUniversal && v.isPub
        if noOutputs?.isNone then noOutputs? := some input
        realizable := realizable.refute (.conflict input #[])
        continue
    behaviours := behaviours + 1
    for e in expects, k in [0:expects.size] do
      expT := expT.modify k Tally.reach
      if ({ label := e.name, pfx := .anonymous, e := e.e } : Atom).eval I env.look == some false then
        expT := expT.modify k (·.refute (.counterexample (sp.shown vars env (·.isPub))))
    -- A second behaviour on the same input, differing on the `det out`.
    let inputs : Env := c.vars.foldl (init := {}) fun acc v =>
      if v.role == .input then (env[v.name]?.map (acc.insert v.name ·)).getD acc else acc
    for x in dets, k in [0:dets.size] do
      detT := detT.modify k Tally.reach
      let some v₁ := env[x.name]? | continue
      let differs : Atom := { label := x.name, pfx := .anonymous, e := .bin .ne (.var x.name) (.lit v₁) }
      let atoms := all.push differs
      if let some env₂ ← ({ vars := remaining (sp.order c) inputs, atoms, ints : Problem }.solve sp w I inputs) then
        let some v₂ := env₂[x.name]? | continue
        let input := sp.shown vars env fun v => v.role == .input && v.isPub
        detT := detT.modify k (·.refute (.nondeterministic input (v₁.show sp) (v₂.show sp)))
  let result (kind : CheckKind) (prop? : Option Name) (t : Tally) (target? : Option (Name × Name) := none) : CheckResult :=
    let verdict := verdictOf kind t
    { kind, comp := c.path, prop?, target?, verdict
      detail := match verdict with
        | .fail => t.refuted?.getD .none
        | .inconclusive => .unknown "testing found no outputs, or no test reached it"
        | .pass => .none }
  let results := #[result .realizable none realizable]
    ++ (instAssumes.zip instT).map (fun ((w, d, a), t) => result .inst (some w) t (some (d, a)))
    ++ (expects.zip expT).map (fun (e, t) => result .expect (some e.name) t)
    ++ (dets.zip detT).map (fun (x, t) => result .determinism (some x.name) t)
  return { results, noOutputs?, untested := behaviours == 0 && noOutputs?.isNone }

/-- Tests the global expectation `g`. -/
def Spec.quickGlobal (sp : Spec) (g : Comp) (tests : Nat) : R Report := do
  let vars := sp.flatVars g
  let some body := g.constraints[0]? | return {}
  let mut t : Tally := {}
  for _ in [0:tests] do
    let w ← World.random sp
    let I := w.interp sp
    let mut env? : Option Env := some {}
    for i in g.insts do
      let some env := env? | break
      let some d := sp.comp? i.comp | env? := none; break
      let atoms := sp.meaning d i.name
      env? ← ({ vars := sp.order d i.name, atoms, ints := intsOf atoms : Problem }.solve sp w I env)
    let some env := env? | continue
    t := t.reach
    if ({ label := body.name, pfx := .anonymous, e := body.e } : Atom).eval I env.look == some false then
      t := t.refute (.counterexample (sp.shown vars env (·.isPub)))
  let verdict := verdictOf .expect t
  return { results := #[{ kind := .expect, comp := g.path, prop? := some body.name, verdict
                          detail := match verdict with
                            | .fail => t.refuted?.getD .none
                            | _ => .none }]
           untested := t.tests == 0 }

/-! ## `fren eval` -/

/-- `eval::Status`. -/
inductive Status where
  | Inadmissible
  | Violates
  | Meets
  deriving BEq, Repr

/-- The value of each constraint and instance of `c` in `env`, and the
behaviour's status (`eval::status`), `none` if unknown. -/
structure Evaluation where
  lines : Array (String × Option Bool)
  status? : Option Status
  expectFalse : Bool

def Spec.evaluate (sp : Spec) (I : Interp) (c : Comp) (env : Env) : Evaluation := Id.run do
  let one (k : PropKind) := (c.ofKind k).map fun p =>
    (p, ({ label := p.name, pfx := .anonymous, e := p.e } : Atom).eval I env.look)
  let kw : PropKind → String
    | .assume => "assume" | .req => "req" | .expect => "expect"
  let as := one .assume
  let rs := one .req
  let es := one .expect
  let is := c.insts.map fun i => (i, allHold I env.look (sp.instAtoms .anonymous i))
  let conj (xs : Array (Option Bool)) : Option Bool :=
    if xs.any (· == some false) then some false else if xs.all (· == some true) then some true else none
  let adm := conj ((as.map (·.2)) ++ (is.map (·.2)))
  let met := conj (rs.map (·.2))
  let status? := match adm, met with
    | some false, _ => some .Inadmissible
    | some true, some false => some .Violates
    | some true, some true => some .Meets
    | _, _ => none
  let lines := (as ++ rs ++ es).map (fun (p, v) => (s!"{kw p.kind} {p.name}", v))
    ++ is.map fun (i, v) => (s!"inst {i.name}", v)
  return { lines, status?, expectFalse := es.any (·.2 == some false) }

end FrenCli.Eval
