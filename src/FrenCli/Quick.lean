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
  tests : Nat := 0
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
  /-- The calls reached, by index, for counting. -/
  reached : Nat := 0
  complete : Bool := false

/-- The constraints that `Spec.admit` searches with, for `c`: its
assumptions, the definitions of its defined variables that the inputs give,
and each call's arguments and meaning, compiled for searches whose
interpretations' shapes are `shapes` (`Atom.compiled`). -/
structure AdmitAtoms where
  assumes : Array Atom
  early : Array Atom
  binds : Array (Array Atom)
  insts : Array (Array Atom)

def Spec.admitAtoms (sp : Spec) (c : Comp) (shapes : Name → Option Fren.Core.DataShape) : AdmitAtoms :=
  let early := c.earlyDefs
  { assumes := (atomsOf .anonymous (c.ofKind .assume)).map (·.compiled shapes)
    early := (c.defAtoms.filter (early.contains ·.label)).map (·.compiled shapes)
    binds := c.insts.map fun i => (bindingAtoms .anonymous i).map (·.compiled shapes)
    insts := c.insts.map fun i => (sp.instAtoms .anonymous i).map (·.compiled shapes) }

/-- Searches for an admissible input, then for each call in turn
confirms its assumptions on its inputs and searches for its behaviour.
`ints` and `strs` are the integers and strings to try (`intsOf`,
`stringsOf`); `shapes?` is as for `World.interp`, and `pre` is
`sp.admitAtoms c`, for the shapes of `w.interp sp shapes?`. -/
def Spec.admit (sp : Spec) (w : World) (c : Comp) (ints : Array Int) (strs : Array String)
    (shapes? : Option (Std.HashMap Name Fren.Core.DataShape)) (pre : AdmitAtoms) : R (Option Admitted) := do
  let I := w.interp sp shapes?
  let inputs := c.vars.filter (·.role == .input) |>.map fun v => (v.name, v.ty)
  let some env ← ({ vars := inputs, atoms := pre.assumes, ints, strs : Problem }.solve sp w I {})
    | return none
  -- The defined outputs that the inputs give, which bindings may read
  -- (`Reqs/Eval#searching-for-behaviours`).
  let early := c.earlyDefs
  -- If they have no value, the outputs' search reports it, as before.
  let env := (← ({ vars := (c.vars.filter (early.contains ·.name)).map fun v => (v.name, v.ty)
                   atoms := pre.early, ints, strs : Problem }.solve sp w I env)).getD env
  let vars := sp.flatVars c
  let mut env := env
  let mut out : Admitted := { env }
  for i in c.insts, k in [0:c.insts.size] do
    let some d := sp.comp? i.comp | return none
    let ins := d.vars.filter (·.role == .input) |>.map fun v => (i.name ++ v.name, v.ty)
    let binds := pre.binds[k]!
    let some env' ← ({ vars := ins, atoms := binds, ints := intsOf binds, strs : Problem }.solve sp w I env) | return some out
    env := env'
    out := { out with env, reached := k + 1 }
    -- Inputs and the earlier calls' public outputs (`checkInst`).
    let later := (c.insts.extract k).map (·.name)
    let shown := sp.shown vars env fun v => v.role.isUniversal && v.isPub && !later.contains v.name.getRoot
    let mut failed := false
    for a in d.ofKind .assume do
      if ({ label := a.name, pfx := i.name, e := a.e } : Atom).eval I env.look == some false then
        out := { out with instFails := out.instFails.push (i.name, d.path, a.name, shown) }
        failed := true
    if failed then return some out
    let atoms := pre.insts[k]!
    let some env' ← ({ vars := remaining (sp.order d i.name) env, atoms, ints := intsOf atoms, strs : Problem }.solve sp w I env)
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
  admissible behaviours (`F0612`). -/
  untriggered : Array CheckResult := #[]
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
`env`, under `I`: whether every assignment of its outputs makes one of
`reqs`, its definitions and guarantees, `false`, and if so, those that
are, one for each assignment, preferring those already found. This is
decided only where the search sees every output (`eval::test_verdict`):
each output is defined, with a definition that has a value, or is of a
type of `finiteValues?`, with at most `limit` assignments of them in all,
and in each assignment some constraint is `false`. Otherwise it is
`none`. -/
def Spec.noOutputsExist (sp : Spec) (w : World) (I : Interp) (c : Comp) (reqs : Array Atom) (env : Env)
    (limit : Nat := 4096) : Option (Array Name) := Id.run do
  let free := c.vars.filter fun v => v.role == .output && !c.defs.any (·.1 == v.name)
  let mut domains : Array (Name × Array Val) := #[]
  for v in free do
    let some vs := finiteValues? sp w v.ty | return none
    domains := domains.push (v.name, vs)
  let total := domains.foldl (· * ·.2.size) 1
  if total > limit then return none
  let mut core : Array Nat := #[]
  for k in [0:total] do
    -- The `k`th assignment of the outputs without definitions.
    let mut env := env
    let mut j := k
    for (x, vs) in domains do
      env := env.insert x vs[j % vs.size]!
      j := j / vs.size
    -- The defined outputs, from their definitions, which may read one
    -- another: one round for each.
    for _ in c.defs do
      for (d, e) in c.defs do
        unless env.contains d do
          if let some v := e.eval I env.look then env := env.insert d v
    unless c.defs.all (env.contains ·.1) do return none
    let falsified := (reqs.map (·.eval I env.look)).zipIdx.filterMap fun (v, i) => if v == some false then some i else none
    if falsified.isEmpty then return none
    unless falsified.any core.contains do core := core.push falsified[0]!
  return some ((core.qsort (· < ·)).map (reqs[·]!.label))

/-- Whether a test that found what a check is about, in `env`, reaches it:
whether the check's trigger, if any, holds there (`eval::reaches`). -/
def reaches (I : Interp) (pfx : Name) (trigger? : Option Ex) (env : Env) : Bool :=
  reached true trigger?.isSome (trigger?.any fun t => ({ label := .anonymous, pfx, e := t } : Atom).eval I env.look == some true)

/-- Tests the procedure `c` (`eval::test_verdict`). -/
def Spec.quickComp (sp : Spec) (c : Comp) (tests : Nat) : R Report := do
  let vars := sp.flatVars c
  let expects := c.ofKind .expect
  let covers := c.ofKind .cover
  let dets := c.vars.filter (·.isDet)
  let instAssumes := c.insts.flatMap fun i =>
    ((sp.comp? i.comp).map fun d => (d.ofKind .assume).map fun a => (i.name, d.path, a.name, a.e.trigger?)).getD #[]
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
  -- The constraints of the searches, each compiled once, with the shapes
  -- of every interpretation below (`World.interp`).
  let compiled := Atom.compiled fun p => shapes[p]?
  let pre := sp.admitAtoms c fun p => shapes[p]?
  let reqs := reqs.map compiled
  let all := all.map compiled
  let negations := expects.map fun e => compiled { label := e.name, pfx := .anonymous, e := .not e.e }
  let triggers := expects.map fun e => e.e.trigger?.map fun t => compiled { label := e.name, pfx := .anonymous, e := t }
  let goals := covers.map fun g => compiled { label := g.name, pfx := .anonymous, e := g.e }
  for _ in [0:tests] do
    let w ← World.random sp
    let I := w.interp sp (some shapes)
    let some adm ← sp.admit w c ints strs (some shapes) pre | continue
    for (x, k) in instAssumes.zipIdx do
      let reached := (c.insts.findIdx? (·.name == x.1)).any (· < adm.reached)
      if reached then instFound := instFound.modify k (· + 1)
      if reached && reaches I x.1 x.2.2.2 adm.env then instT := instT.modify k Tally.reach
      if let some (_, _, _, shown) := adm.instFails.find? fun (w, _, a, _) => w == x.1 && a == x.2.2.1 then
        instT := instT.modify k (·.refute (.counterexample shown))
    unless adm.complete do continue
    realizable := realizable.reach
    let outs := c.vars.filter (·.role == .output) |>.map fun v => (v.name, v.ty)
    let some env ← ({ vars := outs, atoms := reqs, ints, strs : Problem }.solve sp w I adm.env)
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
        let atoms := all.push negations[k]!
        if let some cex ← ({ vars := sp.order c, atoms, ints, strs : Problem }.solve sp w I {}) then
          expT := expT.modify k fun t => (t.reach).refute (.counterexample (sp.shown vars cex (·.isPub)))
          continue
      let trigger? := e.e.trigger?
      -- A behaviour in which the trigger holds, searched for from a new
      -- input if this one's does not. It need only meet the procedure,
      -- which is what an expectation is about, so call assumptions are
      -- hypotheses there, as in the solver's query, not obligations.
      let env? ← if reaches I .anonymous trigger? env then pure (some env) else
        -- Once refuted, an expectation needs no more searching.
        let some t := triggers[k]! | pure none
        if (expT[k]?.bind (·.refuted?)).isSome then pure none else
        let atoms := all.push t
        ({ vars := sp.order c, atoms, ints, strs : Problem }.solve sp w I {})
      let some envE := env? | continue
      expT := expT.modify k Tally.reach
      if ({ label := e.name, pfx := .anonymous, e := e.e } : Atom).eval I envE.look == some false then
        expT := expT.modify k (·.refute (.counterexample (sp.shown vars envE (·.isPub))))
    -- A witness of each cover goal that has none yet: this behaviour, or
    -- one searched for from a new input (`Reqs/Eval#fren-quickcheck`).
    for goal in goals, k in [0:goals.size] do
      if (covW[k]?.join).isSome then continue
      let env? ← if goal.eval I env.look == some true then pure (some env) else
        ({ vars := sp.order c, atoms := all.push goal, ints, strs : Problem }.solve sp w I {})
      let some envG := env? | continue
      covT := covT.modify k Tally.reach
      covW := covW.set! k (some (sp.shown vars envG (·.isPub)))
    -- A second behaviour on the same input, differing on the `det` variable.
    let inputs : Env := c.vars.foldl (init := {}) fun acc v =>
      if v.role == .input then (env[v.name]?.map (acc.insert v.name ·)).getD acc else acc
    for x in dets, k in [0:dets.size] do
      detT := detT.modify k Tally.reach
      let some v₁ := env[x.name]? | continue
      let differs : Atom := { label := x.name, pfx := .anonymous, e := .bin .ne (.var x.name) (.lit v₁) }
      let atoms := all.push differs
      if let some env₂ ← ({ vars := remaining (sp.order c) inputs, atoms, ints, strs : Problem }.solve sp w I inputs) then
        let some v₂ := env₂[x.name]? | continue
        let input := sp.shown vars env fun v => v.role == .input && v.isPub
        detT := detT.modify k (·.refute (.nondeterministic input (v₁.showAs sp x.ty) (v₂.showAs sp x.ty)))
  let result (kind : CheckKind) (prop? : Option Name) (t : Tally) (target? : Option (Name × Name) := none) : CheckResult :=
    let verdict := verdictOf kind t
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
      | .pass, some w => { r with detail := .witness w }
      | _, _ => r)
    ++ (dets.zip detT).map (fun (x, t) => result .determinism (some x.name) t)
  let untested := behaviours == 0 && noOutputs?.isNone
  -- Admissible behaviours were found, but none in which the trigger held.
  -- Not beside `F0610`, which already says that nothing was tested.
  let untriggered := if untested then #[] else
    ((instAssumes.zip (instT.zip instFound)).filterMap fun ((w, d, a, t?), (t, found)) =>
      if t?.isSome && t.tests == 0 && found > 0 then some (result .inst (some w) t (some (d, a))) else none)
    ++ (expects.zip expT).filterMap fun (e, t) =>
      if e.e.trigger?.isSome && t.tests == 0 && behaviours > 0 then some (result .expect (some e.name) t) else none
  let unwitnessed := if untested || behaviours == 0 then #[] else
    (covers.zip covT).filterMap fun (g, t) => if t.tests == 0 then some (result .cover (some g.name) t) else none
  return { results, noOutputs?, untested, untriggered, unwitnessed }

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
  -- Compiled once, as in `Spec.quickComp`.
  let compiled := Atom.compiled fun p => shapes[p]?
  let meaning := meaning.map compiled
  let withTrigger := match trigger with
    | some t => meaning.push (compiled { label := body.name, pfx := .anonymous, e := t })
    | none => meaning
  let negated := meaning.push (compiled { label := body.name, pfx := .anonymous, e := .not body.e })
  let mut t : Tally := {}
  let mut found := false
  for _ in [0:tests] do
    let w ← World.random sp
    let I := w.interp sp (some shapes)
    -- The binders' behaviours, chosen together, so that the body's
    -- trigger can be among the constraints (`eval::reaches`).
    let atoms := withTrigger
    -- The budget that each binder had when they were chosen in turn.
    let budget := 4000 * max 1 ds.size
    let some env ← ({ vars := order, atoms, ints, strs : Problem }.solve sp w I {} budget)
      | -- Whether any behaviours were found, to tell `F0610` from `F0612`.
        if trigger.isSome && !found then
          found := (← ({ vars := order, atoms := meaning, ints, strs : Problem }.solve sp w I {} budget)).isSome
        continue
    found := true
    -- A counterexample, searched for directly (`Reqs/Eval#fren-quickcheck`).
    if t.refuted?.isNone then
      if let some cex ← ({ vars := order, atoms := negated, ints, strs : Problem }.solve sp w I {} budget) then
        t := (t.reach).refute (.counterexample (sp.shown vars cex (·.isPub)))
        continue
    unless reaches I .anonymous trigger env do continue
    t := t.reach
    if ({ label := body.name, pfx := .anonymous, e := body.e } : Atom).eval I env.look == some false then
      t := t.refute (.counterexample (sp.shown vars env (·.isPub)))
  let verdict := verdictOf .expect t
  let r : CheckResult := { kind := .expect, comp := g.path, prop? := some body.name, verdict
                           detail := match verdict with
                             | .fail => t.refuted?.getD .none
                             | _ => .none }
  return { results := #[r], untested := !found
           untriggered := if found && t.tests == 0 then #[r] else #[] }

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
