-- keep-sorted start
import FrenCli.Confirm
import FrenCli.Search
import FrenCli.Verdicts
-- keep-sorted end

/-!
# Testing specs on random behaviours (`Reqs/Eval#fren-quickcheck`)

Each test chooses an interpretation, an admissible input, behaviours of
the calls and outputs, by the search of `FrenCli.Search`, and reports
what it refutes as the checks would (`eval::test_verdict`). Every
counterexample has been evaluated, so it is genuine (`eval::sound`).
-/

open Lean

namespace FrenCli.Eval

open Fren.Core (CheckResult CheckKind Assignment)

/-- What testing one check found. -/
structure Tally where
  /-- The tests that reached the check (`eval::reaches`). -/
  tests : Nat := 0
  /-- The tests that found what the check is about, in which its trigger,
  if it has one, was not false, but in which the trigger or the check had
  no value (`eval::unreached`). -/
  valueless : Nat := 0
  /-- Those of `valueless` in which the trigger had no value
  (`eval::unreached`). -/
  unknownTrigger : Nat := 0
  /-- The tests that found what the check is about in which the check as a
  whole, its trigger included, had a value (`eval::unreached_warning`). -/
  valued : Nat := 0
  /-- The first counterexample. -/
  refuted? : Option Fren.Core.Detail := none
  /-- For realizability: the counterexample is an input for which the
  search saw every output (`Spec.noOutputsExist`). -/
  exhausted : Bool := false

def Tally.reach (t : Tally) : Tally := { t with tests := t.tests + 1 }

def Tally.refute (t : Tally) (d : Fren.Core.Detail) : Tally :=
  if t.refuted?.isSome then t else { t with refuted? := some d }

/-- `t`, refuted by an input for which the search saw every output, which
takes the place of an earlier input without outputs that it did not. -/
def Tally.refuteExhausted (t : Tally) (d : Fren.Core.Detail) : Tally :=
  if t.exhausted then t else { t with refuted? := some d, exhausted := true }

def Spec.shown (sp : Spec) (vars : Array Var) (env : Env) (keep : Var → Bool) : Assignment :=
  vars.filterMap fun v => if keep v then env[v.name]?.map (v.name, ·.showAs sp v.ty) else none

/-- The variables of `vars` to choose, in `order`, other than those in `env`. -/
def remaining (order : Array (Name × VTy)) (env : Env) : Array (Name × VTy) := order.filter (!env.contains ·.1)

/-- An admissible input, with behaviours of the calls: the call
assumptions that a test refutes, and the call whose behaviour was not
found, if any. -/
structure Admitted where
  env : Env
  /-- Counterexamples to call assumptions: the call, the
  called procedure, its assumption, and the shown values. -/
  instFails : Array (Name × Name × Name × Assignment) := #[]
  /-- The value of each call assumption on its call's inputs, by call and
  assumption, `none` where it has none, as where an index is out of range
  or evaluation runs out of fuel (`outOfFuel`): such an assumption the
  test neither refutes nor reaches (`eval::reaches`). -/
  instValues : Array ((Name × Name) × Option Bool) := #[]
  /-- The calls reached, by index, for counting. -/
  reached : Nat := 0
  complete : Bool := false

/-- `e` with each variable that a definition gives from the inputs
(`Comp.earlyDefs`) replaced by its definition, through the definitions
of others, so that admission evaluates an assumption that reads one with
it computed, and, where it has no value, as strong Kleene logic has the
assumption (`Reqs/Eval#searching-for-behaviours`). An `e` that reads none
is unchanged. -/
def Comp.inlineEarly (c : Comp) (e : Ex) : Ex := Id.run do
  let early := c.earlyDefs
  let defs := c.defs.filter (early.contains ·.1)
  let mut e := e
  -- Each round removes one level: definitions read only earlier ones.
  for _ in [0:defs.size] do
    unless e.vars.any early.contains do break
    e := e.substVars fun n => ((defs.find? (·.1 == n)).map (·.2)).getD (.var n)
  return e

/-- The constraints that `Spec.admit` searches with, for `c`: its
assumptions, the definitions of its defined variables that the inputs give,
and each call's arguments and meaning, compiled for searches whose
interpretations' shapes are `shapes` (`Atom.compiled`). -/
structure AdmitAtoms where
  assumes : Array Atom
  early : Array Atom
  binds : Array (Array Atom)
  insts : Array (Array Atom)
  /-- Each call's procedure's assumptions, by name, each with the
  definitions that it reads in their place (`Comp.inlineEarly`), as they
  are evaluated on the call's inputs. -/
  callAssumes : Array (Array (Name × Ex))

def Spec.admitAtoms (sp : Spec) (c : Comp) (shapes : Name → Option Fren.Core.DataShape) : AdmitAtoms :=
  let early := c.earlyDefs
  { assumes := (atomsOf .anonymous (c.ofKind .assume)).map fun a => ({ a with e := c.inlineEarly a.e } : Atom).compiled shapes
    early := (c.defAtoms.filter (early.contains ·.label)).map (·.compiled shapes)
    binds := c.insts.map fun i => (bindingAtoms .anonymous i).map (·.compiled shapes)
    insts := c.insts.map fun i => (sp.instAtoms .anonymous i).map (·.compiled shapes)
    callAssumes := c.insts.map fun i =>
      ((sp.comp? i.comp).map fun d => (d.ofKind .assume).map fun a => (a.name, d.inlineEarly a.e)).getD #[] }

/-- Searches for an admissible input, then for each call in turn
confirms its assumptions on its inputs and searches for its behaviour.
`ints` and `strs` are the integers and strings to try (`intsOf`,
`stringsOf`); `shapes?` is as for `World.interp`, and `pre` is
`sp.admitAtoms c`, for the shapes of `w.interp sp shapes?`. `fixedPools`
is `sp.fixedPools strs` of the types of the variables
(`Problem.fixedPools`). -/
def Spec.admit (sp : Spec) (w : World) (c : Comp) (ints : Array Int) (strs : Array String)
    (shapes? : Option (Std.HashMap Name Fren.Core.DataShape)) (pre : AdmitAtoms)
    (fixedPools : Std.HashMap VTy (Thunk (Array Val)) := {}) : R (Option Admitted) := do
  let I := w.interp sp shapes?
  let inputs := c.vars.filter (·.role == .input) |>.map fun v => (v.name, v.ty)
  let some env ← ({ vars := inputs, atoms := pre.assumes, ints, strs, fixedPools : Problem }.solve sp w I {})
    | return none
  -- The defined outputs that the inputs give, which bindings may read
  -- (`Reqs/Eval#searching-for-behaviours`).
  let early := c.earlyDefs
  -- If they have no value, the outputs' search reports it, as before.
  let env := (← ({ vars := early.filterMap fun n => (c.vars.find? (·.name == n)).map fun v => (v.name, v.ty)
                   atoms := pre.early, ints, strs, fixedPools : Problem }.solve sp w I env)).getD env
  let vars := sp.flatVars c
  let mut env := env
  let mut out : Admitted := { env }
  for i in c.insts, k in [0:c.insts.size] do
    let some d := sp.comp? i.comp | return none
    let ins := d.vars.filter (·.role == .input) |>.map fun v => (i.name ++ v.name, v.ty)
    let binds := pre.binds[k]!
    let some env' ← ({ vars := ins, atoms := binds, ints := intsOf binds, strs, fixedPools : Problem }.solve sp w I env) | return some out
    env := env'
    out := { out with env, reached := k + 1 }
    -- Inputs and the earlier calls' public outputs (`checkInst`).
    let later := (c.insts.extract k).map (·.name)
    let shown := sp.shown vars env fun v => v.role.isUniversal && v.isPub && !later.contains v.name.getRoot
    let mut failed := false
    -- With the called procedure's definitions that they read in their
    -- place, as for its own admission (`Comp.inlineEarly`).
    for (a, e) in pre.callAssumes[k]! do
      let value := ({ label := a, pfx := i.name, e } : Atom).eval I env.look
      out := { out with instValues := out.instValues.push ((i.name, a), value) }
      if value == some false then
        out := { out with instFails := out.instFails.push (i.name, d.path, a, shown) }
        failed := true
    if failed then return some out
    let atoms := pre.insts[k]!
    let some env' ← ({ vars := remaining (sp.order d i.name) env, atoms, ints := intsOf atoms, strs, fixedPools : Problem }.solve sp w I env)
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
  /-- The checks with a trigger that no test reached, though some found
  what they are about, because the trigger was false in all of them
  (`F0612`, `eval::unreached`). What a test finds is an admissible
  behaviour for an expectation, and the call's inputs for a call
  assumption. Beside the procedure's `F0610` (`untested`), none is shown
  (`eval::unreached_warning`). -/
  untriggered : Array CheckResult := #[]
  /-- The checks that no test reached, though some found what they are
  about, as for `untriggered`, in which their triggers, if any, were not
  false, and in some of which the trigger held, because the check had no
  value in any of those (`F0617` at the check, `eval::unreached`). Beside
  the procedure's `F0610`, only call assumptions that had no value as a
  whole in any test are (`eval::unreached_warning`), since they explain
  it. -/
  valueless : Array CheckResult := #[]
  /-- The checks that no test reached, as for `valueless`, because their
  triggers had no value in every test in which they were not false
  (`F0617` at the trigger, `eval::unreached`). -/
  triggerValueless : Array CheckResult := #[]
  /-- The cover goals for which no test found a witness, though some found
  behaviours that meet the procedure (`F0616`). -/
  unwitnessed : Array CheckResult := #[]

def verdictOf (kind : CheckKind) (t : Tally) : Fren.Core.Verdict := testVerdict kind t.refuted?.isSome t.tests t.exhausted

/-- Every value of `ty`, where it has finitely many, all of which a search
tries (`smallValues`): `Bool`, an abstract type, with the world's number
of values, and an enumeration whose variants have no fields. -/
def finiteValues? (sp : Spec) (w : World) : VTy → Option (Array Val)
  | .bool => some #[.bool false, .bool true]
  | .abstract s => some ((Array.range (w.size s)).map (.abs s))
  | .data p _ => do
    let d ← sp.data.find? p
    if d.isRecord || d.ctors.isEmpty || !d.ctors.all (·.fields.isEmpty) then none
    some ((Array.range d.ctors.size).map fun i => .ctor p i #[])
  | _ => none

/-- Whether `c` has no outputs for the input and behaviours of the calls in
`env`, under `I`, decided only where the search sees every output
(`eval::outputs_seen`): each output is defined, or of a type of
`finiteValues?`, with at most `limit` assignments of the others, and each
assignment, with the defined outputs from their definitions, makes one of
`reqs`, its definitions and guarantees, `false`. If so, those that are
`false`, one for each assignment, preferring those already found. -/
def Spec.noOutputsExist (sp : Spec) (w : World) (I : Interp) (c : Comp) (reqs : Array Atom) (env : Env)
    (limit : Nat := 4096) : Option (Array Name) := Id.run do
  let free := c.vars.filter fun v => v.role == .output && !c.defs.any (·.1 == v.name)
  let domains := free.map fun v => (v.name, finiteValues? sp w v.ty)
  let sizes := domains.map (·.2.map (·.size))
  let count := sizes.foldl (· * ·.getD 0) 1
  let mut assignments : Array Assigned := #[]
  let mut core : Array Nat := #[]
  if sizes.all (·.isSome) && count ≤ limit then
    for k in [0:count] do
      -- The `k`th assignment of the outputs without definitions.
      let mut env := env
      let mut j := k
      for (x, vs?) in domains do
        let vs := vs?.getD #[]
        env := env.insert x vs[j % vs.size]!
        j := j / vs.size
      -- The defined outputs, from their definitions, which may read one
      -- another: one round for each.
      for _ in c.defs do
        for (d, e) in c.defs do
          unless env.contains d do
            if let some v := e.eval I env.look then env := env.insert d v
      let values := reqs.map (·.eval I env.look)
      let falsified := values.zipIdx.filterMap fun (v, i) => if v == some false then some i else none
      assignments := assignments.push <|
        if !c.defs.all (env.contains ·.1) then .Undefined
        else if !falsified.isEmpty then .Ruled
        else if values.all (·.isSome) then .Satisfied
        else .Undefined
      if let some i := falsified[0]? then
        unless falsified.any core.contains do core := core.push i
  if !outputsSeen sizes count assignments limit then return none
  return some ((core.qsort (· < ·)).map (reqs[·]!.label))

/-- The value in `env` of the trigger `trigger?` of a check, `some true`
if it has none: a test must find it `true` to reach the check
(`eval::reaches`). -/
def triggerValue (I : Interp) (pfx : Name) (trigger? : Option Ex) (env : Env) : Option Bool :=
  match trigger? with
  | some t => ({ label := .anonymous, pfx, e := t } : Atom).eval I env.look
  | none => some true

/-- `t`, after a test that found what its check is about, in which the
check's trigger, if it has one (`hasTrigger`), has the value `trigger`,
and the check the value `value`. The test reaches the check only where
the trigger holds and the check has a value (`eval::reaches`). One in
which the trigger is not false but either has no value, as where an index
is out of range, a function has no value that the evaluator knows, or
evaluation runs out of fuel (`outOfFuel`), refutes nothing and reaches
nothing, and is counted apart (`Tally.valueless`) for the warning
(`eval::unreached`). Where the value is `false`, it refutes the check, by
`cex`. -/
def Tally.test (t : Tally) (hasTrigger : Bool) (trigger value : Option Bool) (cex : Unit → Fren.Core.Detail) : Tally :=
  let t := if value.isSome then { t with valued := t.valued + 1 } else t
  if reached true hasTrigger trigger value then
    if value == some false then t.reach.refute (cex ()) else t.reach
  else if counted true hasTrigger trigger then
    { t with valueless := t.valueless + 1
             unknownTrigger := t.unknownTrigger + if triggerUnknown true hasTrigger trigger then 1 else 0 }
  else t

/-- The warning shown at the check of `t` (`eval::unreached_warning`),
where `found` tests found what it is about, `untested` if the procedure
has `F0610`, and `callAssumption` if the check is a call assumption. -/
def Tally.warning (t : Tally) (found : Nat) (untested callAssumption : Bool) : UnreachedWarning :=
  unreachedWarning found (t.tests + t.valueless) t.unknownTrigger t.tests t.valued untested callAssumption

/-- Tests the procedure `c` (`eval::test_verdict`). -/
def Spec.quickComp (sp : Spec) (c : Comp) (tests : Nat) : R Report := do
  let vars := sp.flatVars c
  let expects := c.ofKind .expect
  let covers := c.ofKind .cover
  let dets := c.vars.filter (·.isDet)
  let instAssumes := c.insts.flatMap fun i =>
    ((sp.comp? i.comp).map fun d => (d.ofKind .assume).map fun a => (i.name, d.path, a.name, (d.inlineEarly a.e).trigger?)).getD #[]
  let mut realizable : Tally := {}
  let mut expT : Array Tally := expects.map fun _ => {}
  -- Each cover goal's first witness: the tests that found one reach it.
  let mut covT : Array Tally := covers.map fun _ => {}
  let mut covW : Array (Option Assignment) := covers.map fun _ => none
  let mut detT : Array Tally := dets.map fun _ => {}
  let mut instT : Array Tally := instAssumes.map fun _ => {}
  -- The tests that reached each call, whether or not the trigger held.
  let mut instFound : Array Nat := instAssumes.map fun _ => 0
  let mut noOutputs? := none
  let mut behaviours := 0
  -- The definitions, so that the search computes defined outputs.
  let reqs := c.defAtoms ++ atomsOf .anonymous (c.ofKind .ensure)
  let all := sp.meaning c
  -- The literals of the whole procedure, its expectations and cover goals too.
  let lits := all ++ atomsOf .anonymous expects ++ atomsOf .anonymous covers
  let ints := intsOf lits
  let strs ← stringsOf lits
  let sp := sp.withMatchMemo lits strs
  let shapes := sp.shapeMap
  -- The structural recursions too.
  let sp := sp.withCompiledRecs fun p => shapes[p]?
  -- The constraints of the searches, each compiled once, with the shapes
  -- of every interpretation below (`World.interp`).
  let compiled := Atom.compiled fun p => shapes[p]?
  let pre := sp.admitAtoms c fun p => shapes[p]?
  let reqs := reqs.map compiled
  let all := all.map compiled
  let negations := expects.map fun e => compiled { label := e.name, pfx := .anonymous, e := .not e.e }
  let triggers := expects.map fun e => e.e.trigger?.map fun t => compiled { label := e.name, pfx := .anonymous, e := t }
  let goals := covers.map fun g => compiled { label := g.name, pfx := .anonymous, e := g.e }
  -- The problems searched at every test, each prepared once
  -- (`Problem.prepare`), with the shapes of every interpretation below.
  -- The pools of the variables' types that are the same at every test
  -- (`Spec.fixedPools`), computed once for all of the searches.
  let fixedPools := sp.fixedPools strs ((sp.order c).map (·.2))
  let prepared (p : Problem) : Problem :=
    { p with prepared? := some (Thunk.mk fun _ => p.prepare fun q => shapes[q]?), fixedPools }
  let outs := c.vars.filter (·.role == .output) |>.map fun v => (v.name, v.ty)
  let outputsP := prepared { vars := outs, atoms := reqs, ints, strs }
  let negationsP := negations.map fun n => prepared { vars := sp.order c, atoms := all.push n, ints, strs }
  let triggersP := triggers.map (·.map fun t => prepared { vars := sp.order c, atoms := all.push t, ints, strs })
  let goalsP := goals.map fun g => prepared { vars := sp.order c, atoms := all.push g, ints, strs }
  -- For each `det` variable, the search for a second behaviour on a test's
  -- input that differs on it, prepared once: the first behaviour's value
  -- is given as a variable of its own, `first`, which no other variable
  -- is, since no identifier has `[`.
  let inputNames := c.vars.filter (·.role == .input) |>.map (·.name)
  let first (x : Name) : Name := x.str "[first]"
  let detsP := dets.map fun x =>
    let differs : Atom := { label := x.name, pfx := .anonymous, e := .bin .ne (.var x.name) (.var (first x.name)) }
    prepared { vars := (sp.order c).filter (!inputNames.contains ·.1), atoms := all.push differs, ints, strs }
  for _ in [0:tests] do
    let w ← World.random sp
    let I := w.interp sp (some shapes)
    let some adm ← sp.admit w c ints strs (some shapes) pre fixedPools | continue
    for (x, k) in instAssumes.zipIdx do
      let callReached := (c.insts.findIdx? (·.name == x.1)).any (· < adm.reached)
      if callReached then instFound := instFound.modify k (· + 1)
      -- Whether its value on the call's inputs, from admission, is known:
      -- the counterexample, where it is `false`, is admission's, below.
      if callReached then
        let known := ((adm.instValues.find? (·.1 == (x.1, x.2.2.1))).bind (·.2)).map fun _ => true
        instT := instT.modify k (·.test x.2.2.2.isSome (triggerValue I x.1 x.2.2.2 adm.env) known fun _ => .none)
      if let some (_, _, _, shown) := adm.instFails.find? fun (w, _, a, _) => w == x.1 && a == x.2.2.1 then
        instT := instT.modify k (·.refute (.counterexample shown))
    unless adm.complete do continue
    realizable := realizable.reach
    let some env ← (outputsP.solve sp w I adm.env)
      | let input := sp.shown vars adm.env fun v => v.role.isUniversal && v.isPub
        if noOutputs?.isNone then noOutputs? := some input
        -- Where the search saw every output, the input is a genuine
        -- counterexample (`eval::test_verdict`).
        realizable := match sp.noOutputsExist w I c reqs adm.env with
          | some core => realizable.refuteExhausted (.conflict input core)
          | none => realizable.refute (.conflict input #[])
        continue
    behaviours := behaviours + 1
    for e in expects, k in [0:expects.size] do
      -- A counterexample, searched for directly (`Reqs/Eval#fren-quickcheck`).
      if (expT[k]?.bind (·.refuted?)).isNone then
        if let some cex ← (negationsP[k]!.solve sp w I {}) then
          expT := expT.modify k fun t => (t.reach).refute (.counterexample (sp.shown vars cex (·.isPub)))
          continue
      let trigger? := e.e.trigger?
      -- A behaviour in which the trigger holds, searched for from a new
      -- input if this one's does not. It need only meet the procedure,
      -- which is what an expectation is about, so call assumptions are
      -- hypotheses there, as in the solver's query, not obligations.
      let held := triggerValue I .anonymous trigger? env
      let env? ← if held == some true then pure (some env) else
        -- Once refuted, an expectation needs no more searching.
        let some t := triggersP[k]! | pure none
        if (expT[k]?.bind (·.refuted?)).isSome then pure none else
        t.solve sp w I {}
      -- Where none was found, a trigger without a value in this behaviour
      -- is counted apart from a false one (`eval::unreached`).
      let some envE := env?
        | expT := expT.modify k (·.test true held none fun _ => .none)
          continue
      -- The trigger holds in `envE`, as above, or by the search.
      let value := ({ label := e.name, pfx := .anonymous, e := e.e } : Atom).eval I envE.look
      expT := expT.modify k (·.test trigger?.isSome (some true) value fun _ => .counterexample (sp.shown vars envE (·.isPub)))
    -- A witness of each cover goal that has none yet: this behaviour, or
    -- one searched for from a new input (`Reqs/Eval#fren-quickcheck`).
    for goal in goals, k in [0:goals.size] do
      if (covW[k]?.join).isSome then continue
      let env? ← if goal.eval I env.look == some true then pure (some env) else
        goalsP[k]!.solve sp w I {}
      let some envG := env? | continue
      covT := covT.modify k Tally.reach
      covW := covW.set! k (some (sp.shown vars envG (·.isPub)))
    -- A second behaviour on the same input, differing on the `det` variable.
    let inputs : Env := c.vars.foldl (init := {}) fun acc v =>
      if v.role == .input then (env[v.name]?.map (acc.insert v.name ·)).getD acc else acc
    for x in dets, k in [0:dets.size] do
      detT := detT.modify k Tally.reach
      let some v₁ := env[x.name]? | continue
      -- Admission gives every input a value, since it searches for them
      -- all (`Spec.admit`), so the prepared search (`detsP`) applies: its
      -- variables are then `remaining`'s, and its `first` has the value
      -- that `.lit v₁` would.
      let env₂? ← detsP[k]!.solve sp w I (inputs.insert (first x.name) v₁)
      if let some env₂ := env₂? then
        let some v₂ := env₂[x.name]? | continue
        let input := sp.shown vars env fun v => v.role == .input && v.isPub
        detT := detT.modify k (·.refute (.nondeterministic input (v₁.showAs sp x.ty) (v₂.showAs sp x.ty)))
  -- Each result shows a behaviour only where its verdict allows it
  -- (`view::report_shows`): a counterexample where it fails, and a
  -- witness where a cover goal passes, added below.
  let result (kind : CheckKind) (prop? : Option Name) (t : Tally) (target? : Option (Name × Name) := none) : CheckResult :=
    let verdict := verdictOf kind t
    Fren.Core.CheckResult.sealShown
      { kind, comp := c.path, prop?, target?, verdict
        detail := match verdict with
          | .fail => t.refuted?.getD .none
          | .inconclusive => .unknown "testing found no outputs, or no test reached it"
          | .pass => .none }
  let results := #[result .realizable none realizable]
    ++ (instAssumes.zip instT).map (fun ((w, d, a, _), t) => result .inst (some w) t (some (d, a)))
    ++ (expects.zip expT).map (fun (e, t) => result .expect (some e.name) t)
    ++ ((covers.zip covT).zip covW).map (fun ((g, t), w?) =>
      let r := result .cover (some g.name) t
      match r.verdict, w? with
      | .pass, some w => Fren.Core.CheckResult.sealShown { r with detail := .witness w }
      | _, _ => r)
    ++ (dets.zip detT).map (fun (x, t) => result .determinism (some x.name) t)
  let untested := behaviours == 0 && noOutputs?.isNone
  -- The warning shown at each call assumption and expectation that no
  -- test reached (`eval::unreached_warning`), from why none did
  -- (`eval::unreached`): from the tests that found its call's inputs, or
  -- behaviours, those in which its trigger held, and those in which it had
  -- a value.
  let unreached :=
    ((instAssumes.zip (instT.zip instFound)).map fun ((w, d, a, _), (t, found)) =>
      (t.warning found untested true, result .inst (some w) t (some (d, a))))
    ++ (expects.zip expT).map fun (e, t) =>
      (t.warning behaviours untested false, result .expect (some e.name) t)
  let untriggered := unreached.filterMap fun (shown, r) => if shown == .Untriggered then some r else none
  let valueless := unreached.filterMap fun (shown, r) => if shown == .Valueless then some r else none
  let triggerValueless := unreached.filterMap fun (shown, r) => if shown == .TriggerValueless then some r else none
  let unwitnessed := if untested || behaviours == 0 then #[] else
    (covers.zip covT).filterMap fun (g, t) => if t.tests == 0 then some (result .cover (some g.name) t) else none
  return { results, noOutputs?, untested, untriggered, valueless, triggerValueless, unwitnessed }

/-- Tests the global expectation `g`. -/
def Spec.quickGlobal (sp : Spec) (g : Comp) (tests : Nat) : R Report := do
  let vars := sp.flatVars g
  let some body := g.constraints[0]? | return {}
  let trigger := body.e.trigger?
  let ds := g.insts.filterMap fun i => (sp.comp? i.comp).map (i, ·)
  -- A binder whose procedure is unknown leaves it untested.
  if ds.size != g.insts.size then
    return { results := #[{ kind := .expect, comp := g.path, prop? := some body.name, verdict := .inconclusive, detail := .none }]
             untested := true }
  let order := ds.flatMap fun (i, d) => sp.order d i.name
  let meaning := ds.flatMap fun (i, d) => sp.meaning d i.name
  -- The literals of the body too, as of a procedure's expectations.
  let lits := meaning.push { label := body.name, pfx := .anonymous, e := body.e }
  let strs ← stringsOf lits
  let ints := intsOf lits
  let sp := sp.withMatchMemo lits strs
  let shapes := sp.shapeMap
  let sp := sp.withCompiledRecs fun p => shapes[p]?
  -- Compiled once, as in `Spec.quickComp`.
  let compiled := Atom.compiled fun p => shapes[p]?
  let meaning := meaning.map compiled
  let withTrigger := match trigger with
    | some t => meaning.push (compiled { label := body.name, pfx := .anonymous, e := t })
    | none => meaning
  let negated := meaning.push (compiled { label := body.name, pfx := .anonymous, e := .not body.e })
  -- The searches, each prepared once (`Problem.prepare`), as in
  -- `Spec.quickComp`.
  let fixedPools := sp.fixedPools strs (order.map (·.2))
  let prepared (atoms : Array Atom) : Problem :=
    let p : Problem := { vars := order, atoms, ints, strs, fixedPools }
    { p with prepared? := some (Thunk.mk fun _ => p.prepare fun q => shapes[q]?) }
  let withTriggerP := prepared withTrigger
  let meaningP := prepared meaning
  let negatedP := prepared negated
  -- The budget that each binder had when they were chosen in turn.
  let budget := 4000 * max 1 ds.size
  let mut t : Tally := {}
  let mut found := false
  for _ in [0:tests] do
    let w ← World.random sp
    let I := w.interp sp (some shapes)
    -- The binders' behaviours, chosen together, so that the body's
    -- trigger can be among the constraints (`eval::reaches`).
    let some env ← (withTriggerP.solve sp w I {} budget)
      | -- Whether any behaviours were found, to tell `F0610` from `F0612`.
        if trigger.isSome && !found then
          found := (← (meaningP.solve sp w I {} budget)).isSome
        continue
    found := true
    -- A counterexample, searched for directly (`Reqs/Eval#fren-quickcheck`).
    if t.refuted?.isNone then
      if let some cex ← (negatedP.solve sp w I {} budget) then
        t := (t.reach).refute (.counterexample (sp.shown vars cex (·.isPub)))
        continue
    let value := ({ label := body.name, pfx := .anonymous, e := body.e } : Atom).eval I env.look
    t := t.test trigger.isSome (triggerValue I .anonymous trigger env) value fun _ => .counterexample (sp.shown vars env (·.isPub))
  -- Where behaviours were found but the trigger never held in them, the
  -- trigger is told apart from one that was false in all of them by
  -- whether it had no value in some behaviour (`eval::unreached`). Only
  -- then, after the tests, so that they do not depend on it.
  if let some tr := trigger then
    if found && t.tests == 0 && t.valueless == 0 then
      for _ in [0:tests] do
        let w ← World.random sp
        let I := w.interp sp (some shapes)
        let some env ← (meaningP.solve sp w I {} budget) | continue
        let held := triggerValue I .anonymous (some tr) env
        if held.isNone then
          t := t.test true held none fun _ => .none
          break
  let verdict := verdictOf .expect t
  let r : CheckResult := { kind := .expect, comp := g.path, prop? := some body.name, verdict
                           detail := match verdict with
                             | .fail => t.refuted?.getD .none
                             | _ => .none }
  -- Every test that found behaviours with the trigger holding counts in
  -- `t`; one that found them only without it counts as found.
  let shown := t.warning (if found then max 1 (t.tests + t.valueless) else 0) (!found) false
  return { results := #[r], untested := !found
           untriggered := if shown == .Untriggered then #[r] else #[]
           valueless := if shown == .Valueless then #[r] else #[]
           triggerValueless := if shown == .TriggerValueless then #[r] else #[] }

/-! ## `fren eval` -/

/-- The value of each constraint and call of `c` in `env`, and the
behaviour's status (`eval::status`), `none` if unknown. -/
structure Evaluation where
  lines : Array (String × Option Bool)
  status? : Option Status
  expectFalse : Bool

def Spec.evaluate (sp : Spec) (I : Interp) (c : Comp) (env : Env) : Evaluation := Id.run do
  let one (k : PropKind) := (c.ofKind k).map fun p =>
    (p, ({ label := p.name, pfx := .anonymous, e := p.e } : Atom).eval I env.look)
  let kw : PropKind → String
    | .assume => "assume" | .ensure => "ensure" | .expect => "expect" | .cover => "cover"
  let as := one .assume
  let rs := one .ensure
  let es := one .expect
  let gs := one .cover
  let is := c.insts.map fun i => (i, allHold I env.look (sp.instAtoms .anonymous i))
  let conj (xs : Array (Option Bool)) : Option Bool :=
    if xs.any (· == some false) then some false else if xs.all (· == some true) then some true else none
  let adm := conj ((as.map (·.2)) ++ (is.map (·.2)))
  let met := conj (rs.map (·.2))
  let status? := match adm, met with
    | some false, _ => some (statusOf false true true)
    | some true, some r => some (statusOf true true r)
    | _, _ => none
  -- What a variable's type brings is named after the variable.
  let lines := (as ++ rs ++ es ++ gs).map (fun (p, v) =>
      (if p.typed?.isSome then s!"type {p.name.getPrefix}" else s!"{kw p.kind} {p.name}", v))
    ++ is.map fun (i, v) => (s!"inst {i.name}", v)
  return { lines, status?, expectFalse := es.any (·.2 == some false) }

end FrenCli.Eval
