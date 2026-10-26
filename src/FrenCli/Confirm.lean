-- keep-sorted start
import FrenCli.Search
import FrenCli.Smt
import FrenCli.Verdicts
-- keep-sorted end

/-!
# Confirming models (`Reqs/Eval#confirming-models`)

Each formula given to the solver is paired with what it means to the
evaluator (`Fm`), by the same operations of the check algorithms
(`Fren.Core.Backend`), so that each `sat` answer's model can be evaluated:
every hypothesis must be `true` in it, and the goal `false`. The pairing is
by name, from the elaborator's comp (`toCore`) and the evaluator's
(`Eval.Comp`), so the solver's side is exactly what `fren check` asks.
-/

open Lean

namespace FrenCli

open Eval

/-- What a formula means to the evaluator. -/
inductive Fm where
  /-- The conjunction of constraints. -/
  | atoms (as : Array Atom)
  | falsity
  | not (f : Fm)
  | conj (fs : Array Fm)
  /-- `∃ outputs, f`, over the comp's `out`s. -/
  | exOutputs (outs : Array (Name × VTy)) (f : Fm)
  /-- `x = v`, for a value as the solver writes it. -/
  | pin (x : Name) (v : String)
  /-- `f` over the second copy of the variables that `copied` names. -/
  | primed (copied : Array Name) (f : Fm)
  /-- `x = x'`. -/
  | same (x : Name)
  /-- `d = e`, the definition of the defined output `d`. -/
  | defn (d : Name) (e : Ex)
  /-- `f` with the defined outputs replaced by their definitions, in order:
  their values are computed rather than read from the model. -/
  | defined (ds : Array (Name × Ex)) (f : Fm)
  /-- A formula the evaluator does not know the meaning of, such as an
  index's guard and bounds: its value is never known. -/
  | unknown
  deriving Inhabited

/-- The constraint that a goal is about, for attributing a refuted model
to the check that asked it. -/
partial def Fm.subject? : Fm → Option Name
  | .atoms as => as[0]?.map (·.label)
  | .not f | .primed _ f => f.subject?
  | .same x => some x
  | _ => none

partial def Fm.flatAtoms? : Fm → Option (Array Atom)
  | .atoms as => some as
  | .defn d e => some #[{ label := d, pfx := .anonymous, e := .bin .eq (.var d) e }]
  -- Under `∃ outputs`, the equations let the search compute them.
  | .defined ds f =>
    let eqs := ds.map fun (d, e) => ({ label := d, pfx := .anonymous, e := .bin .eq (.var d) e } : Atom)
    (eqs ++ ·) <$> f.flatAtoms?
  | .conj fs => fs.foldlM (fun acc f => (acc ++ ·) <$> f.flatAtoms?) #[]
  | _ => none

/-! ## The solver's values -/

inductive SExp where
  | atom (s : String)
  | list (xs : Array SExp)
  deriving Inhabited, BEq

/-- Reads an S-expression; `|...|` is one atom, without its bars. -/
partial def parseSExps (cs : Array Char) : Array SExp := Id.run do
  let mut stack : Array (Array SExp) := #[#[]]
  let mut i := 0
  let mut tok := ""
  let push (stack : Array (Array SExp)) (tok : String) : Array (Array SExp) :=
    if tok.isEmpty then stack else stack.modify (stack.size - 1) (·.push (.atom tok))
  while h : i < cs.size do
    let c := cs[i]
    if c == '|' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '|' do
        tok := tok.push cs[j]!
        j := j + 1
      i := j + 1
    else if c == '"' then
      -- A string literal, kept with its quotes; `""` is a `"`.
      tok := tok.push c
      let mut j := i + 1
      while j < cs.size && !(cs[j]! == '"' && cs[j + 1]? != some '"') do
        if cs[j]! == '"' then tok := tok.push '"'; j := j + 1
        tok := tok.push cs[j]!
        j := j + 1
      tok := tok.push '"'
      i := j + 1
    else if c == '(' then
      stack := push stack tok
      tok := ""
      stack := stack.push #[]
      i := i + 1
    else if c == ')' then
      stack := push stack tok
      tok := ""
      if stack.size > 1 then
        let top := stack.back!
        stack := stack.pop
        stack := stack.modify (stack.size - 1) (·.push (.list top))
      i := i + 1
    else if c.isWhitespace then
      stack := push stack tok
      tok := ""
      i := i + 1
    else
      tok := tok.push c
      i := i + 1
  stack := push stack tok
  return stack[0]!

def parseSExp? (s : String) : Option SExp := (parseSExps s.toList.toArray)[0]?

/-- What the solver's symbols mean: constructors, testers' constructors and
selectors, by their SMT-LIB names (`Reqs/Cli#solver-queries`). -/
structure Symbols where
  ctors : Std.HashMap String (Name × Nat) := {}
  /-- Field `k` of constructor `idx` of the datatype. -/
  selectors : Std.HashMap String (Name × Nat × Nat) := {}
  /-- `::a::T` for the abstract type `a::T`. -/
  sorts : Std.HashMap String Name := {}

def Symbols.of (sp : Spec) : Symbols := Id.run do
  -- Each map in its own variable, so that inserting does not copy it.
  let mut ctors := {}
  let mut selectors := {}
  let mut sorts := {}
  for (p, d) in sp.data do
    let shown := Fren.Core.showPath p
    for c in d.ctors, idx in [0:d.ctors.size] do
      -- A record's constructor is `R{}` (`recordCtorSym`), which no field can be.
      let ctor := if d.isRecord then s!"{shown}\{}" else s!"{shown}::{c.name}"
      ctors := ctors.insert ctor (p, idx)
      for (f, _) in c.fields, k in [0:c.fields.size] do
        let sel := if d.isRecord then s!"{shown}::{f}" else s!"{shown}::{c.name}::{k}"
        selectors := selectors.insert sel (p, idx, k)
  for p in sp.sorts do sorts := sorts.insert s!"::{Fren.Core.showPath p}" p
  return { ctors, selectors, sorts }

/-- `@::a::T_3`, a value of an abstract type, as `T#3`. -/
def Symbols.abstract? (sy : Symbols) (a : String) : Option Val := do
  guard (a.startsWith "@")
  let body := (a.drop 1).toString
  let digits := (body.toList.reverse.takeWhile Char.isDigit).reverse
  guard !digits.isEmpty
  let sort := ((body.dropEnd digits.length).dropEndWhile (· == '_')).toString
  let p ← sy.sorts[sort]?
  return .abs p (String.ofList digits).toNat!

/-- The value of a ground term, or of a function's body with its
parameters `env`. -/
partial def Symbols.eval (sy : Symbols) (env : List (String × Val)) : SExp → Option Val
  | .atom "true" => some (.bool true)
  | .atom "false" => some (.bool false)
  | .atom a =>
    if let some v := env.lookup a then some v
    else if a == "set.empty" then some (.set #[])
    else if a == "seq.empty" then some (.seq #[])
    else if let some s := Fren.Core.parseSmtString? a then some (.str s)
    else if let some n := a.toNat? then some (.int n)
    else if let some (p, idx) := sy.ctors[a]? then some (.ctor p idx #[])
    else sy.abstract? a
  | .list #[.atom "as", e, _] => sy.eval env e
  | .list #[.atom "-", e] => match sy.eval env e with
    | some (.int x) => some (.int (-x))
    | _ => none
  | .list #[.list #[.atom "_", .atom "is", .atom c], e] => do
    let (p, idx) ← sy.ctors[c]?
    let .ctor q i _ ← sy.eval env e | none
    guard (p == q)
    return .bool (i == idx)
  | .list #[.atom "ite", c, a, b] => do
    let .bool c ← sy.eval env c | none
    sy.eval env (if c then a else b)
  | .list xs => do
    let .atom f := xs[0]? |>.getD (.atom "") | none
    let args ← (xs.extract 1).mapM (sy.eval env)
    match f, args with
    | "not", #[.bool a] => return .bool !a
    | "and", _ => return .bool (args.all (· == .bool true))
    | "or", _ => return .bool (args.any (· == .bool true))
    | "=>", #[.bool a, .bool b] => return .bool (!a || b)
    | "=", #[a, b] => return .bool (a == b)
    | "distinct", #[a, b] => return .bool (a != b)
    | "-", #[.int a, .int b] => return .int (a - b)
    | "+", _ => return .int (← args.foldlM (fun acc v => match v with | .int x => some (acc + x) | _ => none) 0)
    | "*", _ => return .int (← args.foldlM (fun acc v => match v with | .int x => some (acc * x) | _ => none) 1)
    | "div", #[.int a, .int b] => return .int (Int.ediv a b)
    | "mod", #[.int a, .int b] => return .int (Int.emod a b)
    | "<", #[.int a, .int b] => return .bool (a < b)
    | "<=", #[.int a, .int b] => return .bool (a ≤ b)
    | ">", #[.int a, .int b] => return .bool (a > b)
    | ">=", #[.int a, .int b] => return .bool (a ≥ b)
    -- Sets are of 1-tuples (`Reqs/Cli`).
    | "tuple", #[v] => return v
    | "tuple", #[a, b] => return .pair a b
    | "seq.unit", #[v] => return .seq #[v]
    | "seq.++", _ => .seq <$> args.foldlM (fun acc v => match v with | .seq es => some (acc ++ es) | _ => none) #[]
    | "set.singleton", #[v] => return .set #[v]
    | "set.union", #[.set a, .set b] => return Val.setOf (a ++ b)
    | "set.insert", _ =>
      let .set rest ← args.back? | none
      return Val.setOf (args.pop ++ rest)
    | _, _ =>
      if let some (p, idx) := sy.ctors[f]? then return .ctor p idx args
      if let some (p, idx, k) := sy.selectors[f]? then
        let #[.ctor q i vs] := args | none
        guard (p == q && i == idx)
        return ← vs[k]?
      none

/-- A model: its variables' values, and the interpretation of the
functions whose values it gives (as `::f`, a `lambda`). -/
def readModel (sp : Spec) (sy : Symbols) (model : Array (Name × String)) : Env × Interp := Id.run do
  let mut env : Env := {}
  let mut funs : Std.HashMap Name (Array String × SExp) := {}
  for (n, s) in model do
    let some e := parseSExp? s | continue
    if let some f := n.toString.dropPrefix? "::" then
      let some (p, _) := sp.funs.toList.find? fun (p, _) => Fren.Core.showPath p == f.toString | continue
      if let .list #[.atom "lambda", .list params, body] := e then
        let names := params.filterMap fun | .list #[.atom x, _] => some x | _ => none
        funs := funs.insert p (names, body)
      continue
    if let some v := sy.eval [] e then env := env.insert n v
  let fn (f : Name) (args : Array Val) : Option Val := do
    let (ps, body) ← funs[f]?
    sy.eval (ps.toList.zip args.toList) body
  let interp : Interp := { fn, shapes := sp.shapes.find? }
  return (env, interp)

/-! ## Evaluating formulas in a model -/

/-- How many values of each abstract type a model mentions. -/
def sizesOf (env : Env) : NameMap Nat :=
  env.fold (init := {}) fun m _ v => match v with
    | .abs s k => m.insert s (max (k + 1) ((m.find? s).getD 1))
    | _ => m

partial def Fm.eval (sp : Spec) (sy : Symbols) (I : Interp) (env : Env) (tys : Name → Option VTy) : Fm → Option Bool
  | .atoms as => allHold I env.look as
  | .falsity => some false
  | .unknown => none
  | .not f => (f.eval sp sy I env tys).map (!·)
  | .conj fs => fs.foldl (init := some true) fun acc f =>
    match acc, f.eval sp sy I env tys with
    | some false, _ | _, some false => some false
    | some true, some true => some true
    | _, _ => none
  | .pin x v => do
    let v ← parseSExp? v >>= sy.eval []
    return env[x]? == some v
  | .same x => do return (← env[x]?) == (← env[Fren.Core.primed x]?)
  | .defn d e => do return (← env[d]?) == (← e.eval I env.look)
  | .defined ds f =>
    let env := ds.foldl (init := env) fun env (d, e) =>
      match e.eval I env.look with
      | some v => env.insert d v
      | none => env.erase d
    f.eval sp sy I env tys
  | .primed copied f =>
    let env' := copied.foldl (init := env) fun e x =>
      match env[Fren.Core.primed x]? with
      | some v => e.insert x v
      | none => e.erase x
    f.eval sp sy I env' tys
  | .exOutputs outs f => do
    -- Outputs that make `f` true refute "no outputs exist"; not finding
    -- any decides nothing.
    let atoms ← f.flatAtoms?
    let env := outs.foldl (fun e (x, _) => e.erase x) env
    let p : Problem := { vars := outs, atoms, ints := intsOf atoms ++ (env.fold (init := #[]) fun acc _ v =>
      match v with | .int i => acc ++ #[i - 1, i, i + 1] | _ => acc), strs := (stringsOf atoms).run' ⟨1⟩ }
    let w : World := { seed := 0, sizes := sizesOf env }
    match (p.solve sp w I env 20000).run' ⟨1⟩ with
    | some _ => some true
    | none => none

/-! ## The paired backend -/

/-- A model that does not confirm its answer. -/
structure Refutation where
  kind : Fren.Core.CheckKind
  /-- The constraint that the query's goal is about, if any. -/
  subject? : Option Name
  /-- The hypothesis that is false, or `none` if the goal is true. -/
  hyp? : Option Name
  model : Array (Name × String)
  deriving Inhabited

/-- `b`, with each formula paired with its meaning, and each model
evaluated; refuted models are recorded in `log`. `sy` is `Symbols.of sp`,
which the caller builds once for the spec. -/
def confirming (sp : Spec) (sy : Symbols) (ec : Comp) (kind : Fren.Core.CheckKind) (log : IO.Ref (Array Refutation))
    (b : Fren.Core.Backend IO String String) : Fren.Core.Backend IO (String × Fm) String :=
  let vars := sp.flatVars ec
  let outs := vars.filter (·.role == .output) |>.map fun v => (v.name, v.ty)
  let copied := vars.filter (fun v => (Fren.Core.Symbol.ofRole v.role).copied) |>.map (·.name)
  let tys (n : Name) := (vars.find? (·.name == n)).map (·.ty)
  { query := fun hyps goal wantModel => do
      let o ← b.query (hyps.map fun (n, f) => (n, f.1)) goal.1 true
      if let .sat model := o then
        let (env, I) := readModel sp sy model
        let vals := hyps.map fun (n, f) => (n, f.2.eval sp sy I env tys)
        let bad := vals.find? (·.2 == some false)
        let g := goal.2.eval sp sy I env tys
        -- Only a refuted model is reported (`eval::confirm`).
        if confirmation bad.isSome (g == some true) (vals.all (·.2.isSome) && g.isSome) == .Refuted then
          let hyp? := bad.map (·.1)
          log.modify (·.push { kind, subject? := goal.2.subject?, hyp?, model })
        return if wantModel then o else .sat #[]
      return o
    falseF := (b.falseF, .falsity)
    notF := fun f => (b.notF f.1, .not f.2)
    conj := fun fs => (b.conj (fs.map (·.1)), .conj (fs.map (·.2)))
    existsOutputs := fun f => do return (← b.existsOutputs f.1, .exOutputs outs f.2)
    pin := fun n v => do return (← b.pin n v).map (·, .pin n v)
    render := b.render
    prime := fun f => (b.prime f.1, .primed copied f.2)
    samePrimed := fun n => (b.samePrimed n, .same n)
    -- `R[d := e]` means `d = e ∧ R`, under `∃ outputs`.
    subst := fun ds f =>
      (b.subst (ds.map fun (d, e) => (d, e.1)) f.1,
        .defined (ds.filterMap fun (_, _, fm) => match fm with | .defn d e => some (d, e) | _ => none) f.2) }

/-- `core`, the elaborator's comp, with each formula paired with the
meaning of the constraint of `ec` of the same name. Each index's
definedness is paired by its position, one of `positions`, in order, the
`n`th of the item's indexes at a position with the `n`th goal there, and
each question about a table's rows likewise by where it is reported, one
of `tablePositions`, and the question. -/
def pairCore (sp : Spec) (ec : Comp) (core : Fren.Core.Comp String) (positions : Array Nat)
    (tablePositions : Array Nat := #[]) : Fren.Core.Comp (String × Fm) :=
  -- The expressions an index or a table can be in: the constraint, the
  -- definition, the instance's bindings or the body that it names, or, in
  -- a refinement, the binding of the variable that it names.
  let exsOf (n : Name) : Array Ex :=
    (ec.constraints.filter (·.name == n)).map (·.e)
      ++ (ec.defs.filter (·.1 == n)).map (·.2)
      ++ (ec.insts.filter (·.name == n)).flatMap (·.bindings.map (·.2))
      ++ (ec.bindings.filter (·.1 == n)).map (·.2)
      ++ (ec.body?.filter (·.1 == n)).toArray.map (·.2)
  let atomOf (n : Name) : Fm :=
    match ec.constraints.find? (·.name == n) with
    | some p => .atoms #[{ label := n, pfx := .anonymous, e := p.e }]
    | none => .atoms #[]
  let props (ps : Array (Name × String)) := ps.map fun (n, s) => (n, (s, atomOf n))
  let trigger (n : Name) : Fm :=
    match (ec.constraints.find? (·.name == n)).bind (·.e.trigger?) with
    | some t => .atoms #[{ label := n, pfx := .anonymous, e := t }]
    | none => .atoms #[]
  let defn (d : Name) : Fm := match ec.defs.find? (·.1 == d) with
    | some (_, e) => .defn d e
    | none => .atoms #[]
  { path := core.path, vars := core.vars
    defs := core.defs.map fun (d, eq, e) => (d, (eq, defn d), (e, defn d))
    assumes := props core.assumes, expects := props core.expects
    -- An uninterpreted function's postconditions, of its value, which the
    -- evaluator's comp of its contract does not have: undecided.
    reqs := if core.fn?.isSome then core.reqs.map fun (n, s) => (n, (s, .unknown)) else props core.reqs
    posts := props core.posts, fn? := core.fn?
    covers := props core.covers
    triggers := core.triggers.map fun (n, s) => (n, (s, trigger n))
    indexes := core.indexes.mapIdx fun j x =>
      -- The `n`th index at a position is the `n`th goal there: a name of a
      -- `let` or `where` repeats its definition's indexes where it is
      -- mentioned.
      -- A pattern type's obligation, which the evaluator does not know
      -- of, is not confirmed.
      let goal? := if x.patTy?.isSome then none else positions[j]?.bind fun pos =>
        let n := ((positions.extract 0 j).zip (core.indexes.extract 0 j)).filter (fun (p, y) =>
          p == pos && y.prop == x.prop && y.patTy?.isNone) |>.size
        (((exsOf x.prop).flatMap (·.indexGoals)).filter (·.1 == pos))[n]?
      { x with goal := (x.goal, match goal? with
        | some (_, g) => .atoms #[{ label := .num x.prop x.k, pfx := .anonymous, e := g }]
        | none => .unknown) }
    tables := core.tables.mapIdx fun j t =>
      let atom (g : Ex) : Atom := { label := .num t.site.prop t.site.k, pfx := .anonymous, e := g }
      let at? (pos : Nat) := ((exsOf t.site.prop).flatMap (·.tableGoals)).filter fun (p, q, _) => p == pos && q == t.goal
      -- A reachability question is the conjunction of its case's goals at
      -- every mention of a `let` or `where` name (`Fren.Core.mergeReach`).
      if t.goal matches .reachability .. then
        let gs := ((tablePositions[j]?.map at?).getD #[]).map (·.2.2)
        { t with site := { t.site with goal := (t.site.goal, if gs.isEmpty then .unknown else .atoms (gs.map atom)) } }
      else
      -- Likewise the `n`th question at a position.
      let goal? := tablePositions[j]?.bind fun pos =>
        let n := ((tablePositions.extract 0 j).zip (core.tables.extract 0 j)).filter (fun (p, y) =>
          p == pos && y.site.prop == t.site.prop && y.goal == t.goal) |>.size
        (at? pos)[n]?
      { t with site := { t.site with goal := (t.site.goal, match goal? with
        | some (_, _, g) => .atoms #[atom g]
        | none => .unknown) } }
    insts := core.insts.map fun i =>
      let ei? := ec.insts.find? (·.name == i.name)
      let d? := ei?.bind (sp.comp? ·.comp)
      { name := i.name, comp := i.comp
        bindings := (i.bindings, .atoms ((ei?.map (bindingAtoms .anonymous)).getD #[]))
        behaviour := (i.behaviour, .atoms ((d?.map (sp.meaning · i.name (typedInputs := false))).getD #[]))
        -- An input's type's obligation, which the evaluator does not
        -- know of, is not confirmed.
        assumes := i.assumes.map fun (a, s) =>
          let e? := d?.bind fun d => (d.constraints.find? (·.name == a)).map (·.e)
          (a, (s, match e? with
            | some e => .atoms #[{ label := i.name ++ a, pfx := i.name, e }]
            | none => if i.typed.any (·.1 == a) then .unknown else .atoms #[]))
        typed := i.typed } }

/-- Whether a refutation is about result `r`. -/
def Refutation.about (x : Refutation) (r : Fren.Core.CheckResult) : Bool :=
  x.kind == r.kind && match x.subject? with
    | none => true
    | some s => match r.kind, r.prop?, r.target? with
      | .inst, some w, some (_, a) => s == w ++ a
      | .definedness, some p, _ => s == .num p (r.index?.getD 0)
      | .completeness, some p, _ | .disjointness, some p, _ | .precondition, some p, _ | .reachability, some p, _ =>
        s == .num p (r.site?.getD 0)
      | _, some p, _ => s == p
      | _, none, _ => true

def kindName : Fren.Core.CheckKind → String
  | .realizable => "realizability" | .inst => "instance" | .expect => "expectation" | .cover => "cover"
  | .vacuity => "vacuity" | .redundancy => "redundancy" | .determinism => "determinism"
  | .definedness => "definedness" | .completeness => "completeness" | .disjointness => "disjointness"
  | .precondition => "precondition" | .postcondition => "postcondition"
  | .reachability => "reachability"

def Refutation.msg (x : Refutation) (r : Fren.Core.CheckResult) : Fren.Core.Msg :=
  let subject := Fren.Core.showComp (r.comp ++ (r.prop?.getD .anonymous))
  let what := match x.hyp? with
    | some h => s!"makes its hypothesis `{h}` false"
    | none => "makes its goal true"
  { code? := none
    headline := s!"internal error: the solver's model for the {kindName r.kind} check of `{subject}` {what}"
    notes := #[s!"note: the model: {Fren.Core.showAssignment (x.model.map fun (n, v) => (n, v))}",
      "note: this is a bug in Fren's translation of the spec, or in the solver",
      "note: so this check is inconclusive" ] }

/-- The results, with each one that a refuted model is about made
inconclusive (`eval::confirmed_verdict`), and the internal errors. -/
def applyRefutations (results : Array Fren.Core.CheckResult) (log : Array Refutation) :
    Array Fren.Core.CheckResult × Array (Fren.Core.CheckResult × Fren.Core.Msg) := Id.run do
  let mut out := #[]
  let mut errs := #[]
  for r in results do
    match log.find? (·.about r) with
    | some x =>
      out := out.push { r with verdict := confirmedVerdict r.verdict .Refuted, detail := .unknown "the solver's model was refuted" }
      errs := errs.push (r, x.msg r)
    | none => out := out.push r
  return (out, errs)

/-- The evaluator's reading of files that the elaborator accepted. -/
def specStateOf (files : Array (String × Array Char)) : Except String LState := do
  let items ← files.mapM fun (_, chars) =>
    match lex chars with
    | .error e => throw e.msg.headline
    | .ok toks => match parse toks with
      | .error e => throw e.msg.headline
      | .ok items => pure items
  lowerAll items

def specOf (files : Array (String × Array Char)) : Except String Spec := (·.spec) <$> specStateOf files

/-- The evaluator's comp for the elaborator's, matched by path, for a
global expectation by its module and name, or for the body of a function
or the value of a constant (`body`) by its module and the item. -/
def Eval.Spec.counterpart? (sp : Spec) (c : CComp) (global : Bool) (body : Bool := false) : Option Comp :=
  if body then sp.bodies.find? fun b => b.path == c.path && (b.body?.map (·.1)) == c.bodyOf?
  else if global then sp.globals.find? fun g => g.path == c.path && g.constraints.map (·.name) == c.props.map (·.name)
  else sp.comp? c.path

end FrenCli
