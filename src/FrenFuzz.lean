-- keep-sorted start
import FrenCli.Run
-- keep-sorted end

/-!
# Differential fuzzing (`Reqs/dev/Testing`)

`lake exe fren_fuzz [--count N] [--seed N] [--out DIR]` generates random
specs, checks each with `fren check`'s pipeline (cvc5, with its models
confirmed), and compares every result with one computed by brute force
from the evaluator (`FrenCli.Eval`), from the definitions of
`Reqs/Check`.

The specs stay in a fragment where brute force is exact: `Bool`s,
enumerations without payloads, `Int`s that constraints named `range_*`
bound to `0..2`, an abstract type and a function from it to `Bool`, with
instances, `det out`s and global expectations. Every query's hypotheses
then bound every `Int` that matters, except the comparison sets of the
`range_*` constraints' own redundancy, which are not compared. Abstract
types need as many values as the variables of that type, and the
function's interpretations are enumerated over them.

Inputs may also be sets, relations and sequences of one element type, the
enumeration or `Bool`, which has finitely many values, so that brute force
enumerates every set and relation; `range_*` constraints bound sequences
to two elements. Each index is guarded, before or after it, so that the
evaluator knows every constraint's value, as the solver does whatever the
interpretation of an index out of range.
-/

open Lean FrenCli FrenCli.Eval

namespace FrenFuzz

open Fren.Core (CheckKind Verdict CheckResult)

/-! ## Generating specs -/

inductive GTy where
  | bool | int | enum | abs
  /-- Of the spec's element type. -/
  | set | rel | seq
  deriving BEq, Inhabited

structure GVar where
  name : String
  ty : GTy
  isIn : Bool
  isPub : Bool := true
  isDet : Bool := false
  deriving Inhabited

structure GInst where
  name : String
  comp : Nat
  bindings : Array (String × String)
  deriving Inhabited

structure GComp where
  name : String
  vars : Array GVar
  inst? : Option GInst := none
  assumes : Array (String × String) := #[]
  reqs : Array (String × String) := #[]
  expects : Array (String × String) := #[]
  deriving Inhabited

def pick (xs : Array α) [Inhabited α] : R α := do return xs[← below xs.size]!

def chance (pct : Nat) : R Bool := do return (← below 100) < pct

/-- The element type of sets, relations and sequences: the enumeration
if there is one, else `Bool`. -/
def elemTy (useEnum : Bool) : GTy := if useEnum then .enum else .bool

def tyName (elem : GTy) (t : GTy) : String :=
  let base : GTy → String
    | .int => "Int" | .enum => "E" | .abs => "T" | _ => "Bool"
  match t with
  | .set => s!"Set({base elem})"
  | .rel => s!"Rel({base elem}, {base elem})"
  | .seq => s!"Seq({base elem})"
  | t => base t

/-- A variable in scope: its text, type, and whether it may be a
function's argument. -/
structure Scope where
  vars : Array (String × GTy × Bool)
  nVariants : Nat
  hasFn : Bool
  elem : GTy := .bool
  /-- No `card`: the spec has a relation, and the solver does not combine
  counting with relational operators (`Reqs/Lang/Decidability#relations`). -/
  noCard : Bool := false

def Scope.of (sc : Scope) (t : GTy) : Array String := sc.vars.filterMap fun (n, t', _) => if t' == t then some n else none

def intTerm (sc : Scope) : R String := do
  let ns := sc.of .int
  if ns.isEmpty then return toString (← below 3)
  match ← below 5 with
  | 0 => return s!"({← pick ns} + {← pick ns})"
  | 1 => return s!"({← pick ns} - 1)"
  | 2 => return s!"2 * {← pick ns}"
  | 3 => return toString (← below 4)
  | _ => pick ns

/-- A value of the element type. -/
def elemTerm (sc : Scope) : R String := do
  let vs := sc.of sc.elem
  if vs.isEmpty || (← chance 50) then
    if sc.elem == .enum then return s!"E::V{← below sc.nVariants}"
    return ← pick #["true", "false"]
  pick vs

/-- A set: a variable, or a literal of zero to two elements. -/
def setTerm (sc : Scope) : R String := do
  let vs := sc.of .set
  if !vs.isEmpty && (← chance 60) then return ← pick vs
  match ← below 3 with
  | 0 => return "{}"
  | 1 => return s!"\{{← elemTerm sc}}"
  | _ => return s!"\{{← elemTerm sc}, {← elemTerm sc}}"

/-- A relation: a variable, a literal, or a relational operator on one. -/
def relTerm (sc : Scope) : R String := do
  let vs := sc.of .rel
  let pair : R String := do return s!"({← elemTerm sc}, {← elemTerm sc})"
  if vs.isEmpty || (← chance 20) then
    if ← chance 30 then return "{}"
    return s!"\{{← pair}}"
  let r ← pick vs
  match ← below 6 with
  | 0 => return s!"{r}.inverse"
  | 1 => return s!"{r}.closure"
  | 2 => return s!"({r} join {← pick vs})"
  | _ => return r

/-- A sequence: a variable, or a literal of zero to two elements. -/
def seqTerm (sc : Scope) : R String := do
  let vs := sc.of .seq
  if !vs.isEmpty && (← chance 70) then return ← pick vs
  match ← below 3 with
  | 0 => return "[]"
  | 1 => return s!"[{← elemTerm sc}]"
  | _ => return s!"[{← elemTerm sc}, {← elemTerm sc}]"

/-- A constraint on sets, relations or sequences. -/
def collectionAtom (sc : Scope) (t : GTy) : R String := do
  match t with
  | .set =>
    let s ← pick (sc.of .set)
    match ← below 6 with
    | 0 => return s!"{← elemTerm sc} in {s}"
    | 1 => return s!"{s} subset {← setTerm sc}"
    | 2 => return s!"{s} {← pick #["=", "!="]} {← setTerm sc}"
    | 3 => return s!"{← elemTerm sc} in ({s} {← pick #["union", "inter", "minus"]} {← setTerm sc})"
    | _ =>
      if sc.noCard then return s!"{← elemTerm sc} in {s}"
      return s!"{s}.card {← pick #["=", "<=", ">="]} {← below 3}"
  | .rel =>
    let r ← pick (sc.of .rel)
    match ← below 6 with
    | 0 => return s!"{← elemTerm sc} in {r}.{← pick #["domain", "range"]}"
    | 1 => return s!"{r}.image(\{{← elemTerm sc}}) subset {← setTerm sc}"
    | 2 => return s!"{r} {← pick #["=", "subset"]} {← relTerm sc}"
    | _ => return s!"({← elemTerm sc}, {← elemTerm sc}) in {← relTerm sc}"
  | _ =>
    let q ← pick (sc.of .seq)
    let k ← below 2
    match ← below 8 with
    | 0 => return s!"{q}.len {← pick #["=", "<", ">="]} {← below 3}"
    | 1 => return s!"{q} {← pick #["=", "!="]} {← seqTerm sc}"
    | 2 => return s!"{q}.{← pick #["starts_with?", "ends_with?"]}([{← elemTerm sc}])"
    | 3 => return s!"{q}.update({k}, {← elemTerm sc}) = {← seqTerm sc}"
    -- Guarded indexes, whose definedness holds, and a bound after the
    -- index, whose definedness fails.
    | 4 => return s!"({k} < {q}.len and {q}[{k}] = {← elemTerm sc})"
    | 5 => return s!"({q}.len <= {k} or {q}[{k}] != {← elemTerm sc})"
    | 6 => return s!"({q}[{k}] = {← elemTerm sc} and {k} < {q}.len)"
    | _ => return s!"(when {q}.len > {k}, {q}[{k}] = {← elemTerm sc})"

partial def genBool (sc : Scope) (depth : Nat) : R String := do
  let atom : R String := do
    let mut kinds := #[0]
    unless (sc.of .bool).isEmpty do kinds := kinds ++ #[1, 1, 1]
    unless (sc.of .int).isEmpty do kinds := kinds ++ #[2, 2]
    unless (sc.of .enum).isEmpty do kinds := kinds ++ #[3, 3]
    unless (sc.of .abs).isEmpty do kinds := kinds.push 4
    let args := sc.vars.filterMap fun (n, t, a) => if t == .abs && a then some n else none
    if sc.hasFn && !args.isEmpty then kinds := kinds ++ #[5, 5]
    unless (sc.of .set).isEmpty do kinds := kinds ++ #[6, 6]
    unless (sc.of .rel).isEmpty do kinds := kinds ++ #[7, 7]
    unless (sc.of .seq).isEmpty do kinds := kinds ++ #[8, 8]
    match ← pick kinds with
    | 1 => pick (sc.of .bool)
    | 2 => return s!"{← intTerm sc} {← pick #["=", "!=", "<", "<=", ">", ">="]} {← intTerm sc}"
    | 3 =>
      let es := sc.of .enum
      let rhs ← if ← chance 60 then pure s!"E::V{← below sc.nVariants}" else pick es
      return s!"{← pick es} {← pick #["=", "!="]} {rhs}"
    | 4 => let ts := sc.of .abs; return s!"{← pick ts} {← pick #["=", "!="]} {← pick ts}"
    | 5 => return s!"p?({← pick args})"
    | 6 => collectionAtom sc .set
    | 7 => collectionAtom sc .rel
    | 8 => collectionAtom sc .seq
    | _ => pick #["true", "false"]
  if depth == 0 then return ← atom
  match ← below 7 with
  | 0 => return s!"({← genBool sc (depth - 1)} and {← genBool sc (depth - 1)})"
  | 1 => return s!"({← genBool sc (depth - 1)} or {← genBool sc (depth - 1)})"
  | 2 => return s!"not ({← genBool sc (depth - 1)})"
  | 3 => return s!"({← genBool sc (depth - 1)} iff {← genBool sc (depth - 1)})"
  | 4 => return s!"(if {← genBool sc (depth - 1)} then {← genBool sc (depth - 1)} else {← genBool sc (depth - 1)})"
  | _ => atom

/-- A constraint, often with a trigger. -/
def genConstraint (sc : Scope) (trig : Scope) : R String := do
  match ← below 10 with
  | 0 | 1 | 2 | 3 | 4 => return s!"when {← genBool trig 1}, {← genBool sc 1}"
  | 5 => return s!"unless {← genBool trig 1}, {← genBool sc 1}"
  | 6 => return s!"when {← genBool trig 0}, when {← genBool trig 0}, {← genBool sc 1}"
  | _ => genBool sc 2

def varName (t : GTy) (isIn : Bool) (k : Nat) : String :=
  match t, isIn with
  | .bool, true => s!"a{k}?" | .bool, false => s!"b{k}?"
  | .int, true => s!"n{k}" | .int, false => s!"k{k}"
  | .enum, true => s!"m{k}" | .enum, false => s!"e{k}"
  | .abs, _ => s!"t{k}"
  | .set, _ => s!"s{k}" | .rel, _ => s!"rel{k}" | .seq, _ => s!"q{k}"

def genComp (idx : Nat) (prev : Array GComp) (useEnum useAbs : Bool) (nVariants : Nat) (collections : Array GTy) :
    R GComp := do
  let tys := #[GTy.bool, .bool, .int] ++ (if useEnum then #[GTy.enum] else #[]) ++ (if useAbs then #[GTy.abs] else #[])
    ++ collections
  let outTys := #[GTy.bool, .int] ++ (if useEnum then #[GTy.enum] else #[])
  let mut vars : Array GVar := #[]
  for k in [0:(← below 3) + 1] do
    let t ← pick tys
    -- At most one of each collection, whose domains are large.
    if collections.contains t && vars.any (·.ty == t) then continue
    vars := vars.push { name := varName t true k, ty := t, isIn := true }
  for k in [0:(← below 2) + 1] do
    let t ← pick outTys
    vars := vars.push { name := varName t false k, ty := t, isIn := false, isPub := ← chance 80, isDet := ← chance 40 }
  -- An instance of an earlier comp, with every input bound.
  let mut inst? := none
  if !prev.isEmpty && (← chance 60) then
    let ci ← below prev.size
    let d := prev[ci]!
    for v in d.vars do
      if v.isIn && v.ty == .abs && !vars.any (fun u => u.isIn && u.ty == .abs) then
        vars := vars.push { name := varName .abs true 9, ty := .abs, isIn := true }
    let insc : Scope := { vars := vars.filter (·.isIn) |>.map (fun v => (v.name, v.ty, true)), nVariants, hasFn := useAbs
                          elem := elemTy useEnum, noCard := collections.contains .rel }
    let mut bs := #[]
    for v in d.vars do
      unless v.isIn do continue
      let e ← match v.ty with
        | .bool => genBool insc 1
        | .int => if (insc.of .int).isEmpty || (← chance 30) then (toString <$> below 3) else pick (insc.of .int)
        | .enum => if (insc.of .enum).isEmpty || (← chance 30) then pure s!"E::V{← below nVariants}" else pick (insc.of .enum)
        | .abs => pick (insc.of .abs)
        | .set => setTerm insc
        | .rel => relTerm insc
        | .seq => seqTerm insc
      bs := bs.push (v.name, e)
    inst? := some { name := "w", comp := ci, bindings := bs }
  let own := vars.map fun v => (v.name, v.ty, v.isIn)
  let instVars := match inst? with
    | some i => prev[i.comp]!.vars.filter (fun v => v.isIn || v.isPub) |>.map fun v => (s!"w.{v.name}", v.ty, true)
    | none => #[]
  let elem := elemTy useEnum
  let noCard := collections.contains .rel
  let inputs : Scope := { vars := own.filter (·.2.2), nVariants, hasFn := useAbs, elem, noCard }
  let all : Scope := { vars := own ++ instVars, nVariants, hasFn := useAbs, elem, noCard }
  let mut assumes := #[]
  let mut reqs := #[]
  for v in vars do
    if v.ty == .int then
      if v.isIn then assumes := assumes.push (s!"range_{v.name}", s!"0 <= {v.name} and {v.name} <= 2")
      else reqs := reqs.push (s!"range_{v.name}", s!"0 <= {v.name} and {v.name} <= 2")
    if v.ty == .seq then assumes := assumes.push (s!"range_{v.name}", s!"{v.name}.len <= 2")
  for k in [0:← below 2] do assumes := assumes.push (s!"as{k}", ← genBool inputs 1)
  for k in [0:(← below 3) + 1] do reqs := reqs.push (s!"r{k}", ← genConstraint all all)
  let mut expects := #[]
  for k in [0:← below 3] do expects := expects.push (s!"x{k}", ← genConstraint all all)
  return { name := s!"c{idx}", vars, inst?, assumes, reqs, expects }

structure GSpec where
  text : String

def genSpec : R GSpec := do
  let useEnum ← chance 60
  let useAbs ← chance 35
  let nVariants := (← below 2) + 2
  let mut collections := #[]
  for t in #[GTy.set, .rel, .seq] do
    -- A relation over three values has 512 values, too many to evaluate
    -- `closure` and `join` on for every behaviour.
    if t == .rel && useEnum && nVariants > 2 then continue
    if ← chance 40 then collections := collections.push t
  let mut out := "mod fz\n\n"
  if useEnum then
    out := out ++ s!"pub enum E \{ {", ".intercalate ((List.range nVariants).map (s!"V{·}"))} }\n"
  if useAbs then out := out ++ "pub type T\npub fn p?(T)\n"
  let mut comps : Array GComp := #[]
  for i in [0:(← below 2) + 1] do
    comps := comps.push (← genComp i comps useEnum useAbs nVariants collections)
  for c in comps do
    out := out ++ s!"\npub comp {c.name} \{\n"
    for v in c.vars do
      let ty := if v.ty == .bool then "" else s!": {tyName (elemTy useEnum) v.ty}"
      let mods := if v.isIn then "in" else s!"{if v.isPub then "pub " else ""}{if v.isDet then "det " else ""}out"
      out := out ++ s!"    {mods} {v.name}{ty}\n"
    if let some i := c.inst? then
      let bs := ", ".intercalate (i.bindings.toList.map fun (x, e) => s!"{x} := {e}")
      out := out ++ s!"    inst {i.name}: {comps[i.comp]!.name} \{ {bs} }\n"
    for (n, e) in c.assumes do out := out ++ s!"    assume {n}: {e}\n"
    for (n, e) in c.reqs do out := out ++ s!"    req {n}: {e}\n"
    for (n, e) in c.expects do out := out ++ s!"    expect {n}: {e}\n"
    out := out ++ "}\n"
  -- A global expectation over two behaviours of one comp.
  if ← chance 40 then
    let c ← pick comps
    let shown := c.vars.filter (fun v => v.isIn || v.isPub)
    let sc : Scope := { vars := shown.flatMap (fun v => #[(s!"x.{v.name}", v.ty, v.isIn), (s!"y.{v.name}", v.ty, v.isIn)])
                        nVariants, hasFn := useAbs, elem := elemTy useEnum, noCard := collections.contains .rel }
    let ins := shown.filter (·.isIn)
    let same := " and ".intercalate (ins.toList.map fun v => s!"x.{v.name} = y.{v.name}")
    let body ← if (← chance 50) && !ins.isEmpty then
        let o := shown.filter (!·.isIn)
        if o.isEmpty then pure s!"when {same}, {← genBool sc 1}"
        else do let v ← pick o; pure s!"when {same}, x.{v.name} = y.{v.name}"
      else genConstraint sc sc
    out := out ++ s!"\nexpect g: forall (x y: {c.name}), {body}\n"
  return { text := out }

/-! ## Brute force -/

/-- Every subset of `xs`. -/
def subsets (xs : Array Val) : Array Val :=
  (xs.foldl (fun acc x => acc ++ acc.map (·.push x)) #[#[]]).map Val.setOf

partial def domain (sp : Spec) (size : Nat) : VTy → Array Val
  | .bool => #[.bool false, .bool true]
  | .int => #[.int 0, .int 1, .int 2]
  -- The generator emits no strings.
  | .string => #[]
  | .set t => subsets (domain sp size t)
  | .rel a b => subsets ((domain sp size a).flatMap fun x => (domain sp size b).map (.pair x ·))
  -- Up to two elements, as the `range_*` constraints bound them.
  | .seq t =>
    let xs := domain sp size t
    #[.seq #[]] ++ xs.map (.seq #[·]) ++ xs.flatMap fun x => xs.map fun y => .seq #[x, y]
  | .abstract s => (Array.range size).map (.abs s)
  | .data p => match sp.data.find? p with
    | some d => (Array.range d.ctors.size).map (.ctor p · #[])
    | none => #[]

/-- Every interpretation of the functions, whose parameters are abstract
types of `size` values. -/
def interps (sp : Spec) (size : Nat) : Array Interp := Id.run do
  let fs := sp.funs.toList.toArray
  let mut tables : Array (Std.HashMap (Name × Array Val) Val) := #[{}]
  for (f, ps, r) in fs do
    let mut points : Array (Array Val) := #[#[]]
    for t in ps do points := points.flatMap fun pre => (domain sp size t).map pre.push
    for pt in points do
      tables := tables.flatMap fun tb => (domain sp size r).map fun v => tb.insert (f, pt) v
  return tables.map fun tb => { fn := fun f args => tb[(f, args)]? }

/-- Every assignment of `vars` that makes `atoms` true. -/
partial def models (sp : Spec) (size : Nat) (I : Interp) (vars : Array (Name × VTy)) (atoms : Array Atom)
    (env : Env := {}) : Array Env :=
  let rec go (i : Nat) (env : Env) : Array Env :=
    if atoms.any (·.eval I env.look == some false) then #[]
    else if h : i < vars.size then
      let (x, t) := vars[i]
      if env.contains x then go (i + 1) env
      else (domain sp size t).flatMap fun v => go (i + 1) (env.insert x v)
    else if allHold I env.look atoms == some true then #[env] else #[]
  go 0 env

def holds (I : Interp) (env : Env) (a : Atom) : Bool := a.eval I env.look == some true

/-- How many assignments and interpretations brute force tries, at most. -/
def space (sp : Spec) (c : Comp) : Nat :=
  let flat := sp.flatVars c
  let size := max 1 (flat.filter (·.ty matches .abstract _)).size
  -- Evaluating an assignment costs about as much as its collections have
  -- members.
  let members (t : VTy) : Nat := match t with
    | .set e => (domain sp size e).size
    | .rel a b => (domain sp size a).size * (domain sp size b).size
    | .seq _ => 2
    | _ => 0
  (interps sp size).size * flat.foldl (fun n v => n * (domain sp size v.ty).size) 1
    * (1 + flat.foldl (fun n v => n + members v.ty) 0)

def maxSpace : Nat := 3000000

structure Oracle where
  /-- The verdict of each result that brute force decides, by key. -/
  verdicts : Array ((CheckKind × Option Name × Option (Name × Name)) × Verdict) := #[]
  /-- Results that the checks must not report: redundancy that is not asked. -/
  notAsked : Array Name := #[]

def isRange (n : Name) : Bool := n.toString.startsWith "range_"

def oracle (sp : Spec) (c : Comp) : Oracle := Id.run do
  let flat := sp.flatVars c
  let size := max 1 (flat.filter (·.ty matches .abstract _)).size
  let Is := interps sp size
  let order := sp.order c
  let ownIns := c.vars.filter (·.role == .input) |>.map fun v => (v.name, v.ty)
  let atom (p : Constraint) (e := p.e) : Atom := { label := p.name, pfx := .anonymous, e }
  let as := c.ofKind .assume
  let rs := c.ofKind .req
  let es := c.ofKind .expect
  let A := as.map (atom ·)
  let R := rs.map (atom ·)
  let Iw := sp.insts c
  let full := A ++ Iw ++ R
  let mut out : Oracle := {}
  let put (o : Oracle) (k : CheckKind) (p : Option Name) (v : Verdict) (t : Option (Name × Name) := none) :=
    { o with verdicts := o.verdicts.push ((k, p, t), v) }
  let pass (b : Bool) : Verdict := if b then .pass else .fail
  let MF := Is.map fun I => (I, models sp size I order full)
  let constraintsWithTrig := (c.constraints.filter (·.kind != .assume)).filterMap fun p => p.e.trigger?.map (p, ·)
  -- Definedness, of each index by its position: in every model of `ms`,
  -- its goal holds.
  let defined (o : Oracle) (p : Name) (e : Ex) (ms : Array (Interp × Array Env)) : Oracle :=
    e.indexGoals.foldl (init := o) fun o (pos, g) =>
      put o .definedness (some (.num p pos)) (pass (ms.all fun (I, ms) =>
        ms.all (holds I · { label := p, pfx := .anonymous, e := g })))
  if c.isGlobal then
    let MG := Is.map fun I => (I, models sp size I order (sp.insts c))
    for e in es do out := put out .expect (some e.name) (pass (MG.all fun (I, ms) => ms.all (holds I · (atom e))))
    for e in es do out := defined out e.name e.e MG
    for (p, t) in constraintsWithTrig do
      out := put out .vacuity (some p.name) (pass (MG.any fun (I, ms) => ms.any (holds I · (atom p t))))
    return out
  -- Realizability.
  let assumeSat := Is.any fun I => !(models sp size I ownIns A).isEmpty
  let realizable := assumeSat && Is.all fun I =>
    let noOut := order.filter fun (x, _) => !(c.vars.any fun v => v.role == .output && v.name == x)
    let ms := (MF.find? (fun _ => true)).map (·.2) |>.getD #[]
    let _ := ms
    let full := (models sp size I order full)
    (models sp size I noOut (A ++ Iw)).all fun m =>
      full.any fun f => noOut.all fun (x, _) => f[x]? == m[x]?
  out := put out .realizable none (pass realizable)
  -- Instance assumptions.
  for i in c.insts, k in [0:c.insts.size] do
    let some d := sp.comp? i.comp | continue
    let before := (c.insts.extract 0 k).flatMap fun j => (sp.comp? j.comp).map (sp.order · j.name) |>.getD #[]
    let ins := d.vars.filter (·.role == .input) |>.map fun v => (i.name ++ v.name, v.ty)
    let vars := ownIns ++ before ++ ins
    let hyps := A ++ sp.insts c k ++ bindingAtoms .anonymous i
    for a in d.ofKind .assume do
      let goal : Atom := { label := a.name, pfx := i.name, e := a.e }
      let ok := Is.all fun I => (models sp size I vars hyps).all (holds I · goal)
      out := put out .inst (some i.name) (pass ok) (some (d.path, a.name))
    let ms := Is.map fun I => (I, models sp size I (ownIns ++ before) (A ++ sp.insts c k))
    for (_, e) in i.bindings do out := defined out i.name e ms
  for a in as, k in [0:as.size] do
    let others := (A.extract 0 k) ++ A.extract (k + 1)
    out := defined out a.name a.e (Is.map fun I => (I, models sp size I ownIns others))
  for p in rs ++ es do out := defined out p.name p.e MF
  for e in es do
    out := put out .expect (some e.name) (pass (MF.all fun (I, ms) => ms.all (holds I · (atom e))))
  let mut vacuous : Array Name := #[]
  for (p, t) in constraintsWithTrig do
    let ok := MF.any fun (I, ms) => ms.any (holds I · (atom p t))
    unless ok do vacuous := vacuous.push p.name
    out := put out .vacuity (some p.name) (pass ok)
  -- Redundancy, but not of `range_*` constraints.
  for a in as, k in [0:as.size] do
    if !assumeSat then out := { out with notAsked := out.notAsked.push a.name }; continue
    if isRange a.name then continue
    let others := (A.extract 0 k) ++ A.extract (k + 1)
    let ok := Is.any fun I => (models sp size I ownIns others).any (!holds I · (atom a))
    out := put out .redundancy (some a.name) (pass ok)
  let consistent := MF.any fun (_, ms) => !ms.isEmpty
  for r in rs, k in [0:rs.size] do
    if !consistent || vacuous.contains r.name then out := { out with notAsked := out.notAsked.push r.name }; continue
    if isRange r.name then continue
    let others := A ++ Iw ++ (R.extract 0 k) ++ R.extract (k + 1)
    let ok := Is.any fun I => (models sp size I order others).any (!holds I · (atom r))
    out := put out .redundancy (some r.name) (pass ok)
  -- Determinism.
  for x in c.vars.filter (·.isDet) do
    let ok := MF.all fun (_, ms) => ms.all fun m₁ => ms.all fun m₂ =>
      !(ownIns.all fun (n, _) => m₁[n]? == m₂[n]?) || m₁[x.name]? == m₂[x.name]?
    out := put out .determinism (some x.name) (pass ok)
  return out

/-! ## Details -/

/-- The atoms named `names` among the hypotheses of `c`: assumptions,
requirements and instances. -/
def named (sp : Spec) (c : Comp) (names : Array Name) : Array Atom :=
  (c.constraints.filter (fun p => p.kind != .expect && names.contains p.name)).map
    (fun p => { label := p.name, pfx := .anonymous, e := p.e })
  ++ (c.insts.filter (names.contains ·.name)).flatMap (sp.instAtoms .anonymous)

/-- The values `shown` as an environment. Abstract values keep their
pattern of equalities: the `k`th distinct one shown is value `k`. -/
def pinned (st : LState) (c : Comp) (vars : Array Var) (shown : Fren.Core.Assignment) : Option Env := do
  let module := if c.isGlobal then c.path else c.path.getPrefix
  let mut env : Env := {}
  let mut abstracts : Array String := #[]
  for (n, text) in shown do
    let v ← vars.find? (·.name == n)
    if let .abstract s := v.ty then
      let k := (abstracts.idxOf? text).getD abstracts.size
      if k == abstracts.size then abstracts := abstracts.push text
      env := env.insert n (.abs s k)
    else
      match parseValue st module v.ty text with
      | .ok val => env := env.insert n val
      | .error _ => none
  return env

/-- What is wrong with the details of a failing result, by brute force. -/
def checkDetail (st : LState) (c : Comp) (r : CheckResult) : Option String := Id.run do
  let sp := st.spec
  let flat := sp.flatVars c
  let size := max 1 (flat.filter (·.ty matches .abstract _)).size
  let Is := interps sp size
  let order := sp.order c
  let some_ (atoms : Array Atom) (env : Env := {}) := Is.any fun I => !(models sp size I order atoms env).isEmpty
  let prop? := r.prop?.bind fun n => c.constraints.find? (·.name == n)
  let atomOf (p : Constraint) (e := p.e) : Atom := { label := p.name, pfx := .anonymous, e }
  match r.detail with
  | .vacuousAssumptions core =>
    if some_ (named sp c core) then return some s!"the assumptions {core} are satisfiable"
  | .conflict input core =>
    -- Under the model's interpretation, which is not shown: wrong only if
    -- outputs satisfy the core under every interpretation.
    let some env := pinned st c flat input | return some s!"cannot read the input {input}"
    let context := sp.meaning c |>.filter fun a => !(c.ofKind .req).any (·.name == a.label)
    if Is.all fun I => !(models sp size I order (context ++ named sp c core) env).isEmpty then
      return some s!"on the input {input}, outputs satisfy {core}"
  | .vacuous core =>
    let some p := prop? | return none
    let some t := p.e.trigger? | return none
    if some_ (named sp c core |>.push (atomOf p t)) then return some s!"{core} do not rule out the trigger"
  | .redundant core =>
    let some p := prop? | return none
    if some_ (named sp c core |>.push (atomOf p (.not p.e))) then return some s!"{p.name} does not follow from {core}"
  | .counterexample shown =>
    let some env := pinned st c flat shown | return some s!"cannot read the counterexample {shown}"
    if r.kind == .expect then
      let some p := prop? | return none
      let hyps := if c.isGlobal then sp.insts c else sp.meaning c
      unless some_ (hyps.push (atomOf p (.not p.e))) env do
        return some s!"the counterexample {shown} is not a behaviour in which it is false"
  | .nondeterministic input v₁ v₂ =>
    let some env := pinned st c flat input | return some s!"cannot read the input {input}"
    let some x := r.prop? | return none
    let some v := flat.find? (·.name == x) | return none
    let (.ok a, .ok b) := (parseValue st c.path.getPrefix v.ty v₁, parseValue st c.path.getPrefix v.ty v₂)
      | return none
    if a == b then return some s!"the two values {v₁} and {v₂} are equal"
    let has (I : Interp) (val : Val) :=
      !(models sp size I order (sp.meaning c |>.push { label := x, pfx := .anonymous, e := .bin .eq (.var x) (.lit val) }) env).isEmpty
    unless Is.any fun I => has I a && has I b do return some s!"on the input {input}, {x} cannot be both {v₁} and {v₂}"
  | _ => pure ()
  return none

/-! ## Comparing -/

structure Finding where
  what : String

def keyOf (r : CheckResult) : CheckKind × Option Name × Option (Name × Name) := (r.kind, r.prop?, r.target?)

def showKey (k : CheckKind × Option Name × Option (Name × Name)) : String :=
  let (kind, p, t) := k
  s!"{kindName kind}{(p.map (s!" {·}")).getD ""}{(t.map fun (d, a) => s!" ({d}::{a})").getD ""}"

/-- Checks one spec, and returns what differs from brute force. -/
def runOne (dir : System.FilePath) (text : String) (timeout : Nat) :
    IO (Array String × Nat × Nat × Nat) := do
  let path := dir / "current.fren"
  IO.FS.writeFile path text
  let lints := Fren.Core.Lint.all.map (.lint ·, Fren.Core.LintLevel.allow)
  let some (files, st) ← elaborate {} #[path.toString] lints | return (#["cannot read the spec"], 0, 0, 0)
  let errors := st.diags.filter (·.severity == .error)
  unless errors.isEmpty do return (#[s!"generator: static error: {(errors[0]?.map (·.msg.headline)).getD ""}"], 0, 0, 0)
  let lst ← match specStateOf files with
    | .ok s => pure s
    | .error e => return (#[s!"the evaluator cannot read the spec: {e}"], 0, 0, 0)
  let sp := lst.spec
  let mut found := #[]
  let mut compared := 0
  let mut inconclusive := 0
  let mut skipped := 0
  let prelude := Prelude.ofDecls st.prelude
  for (c, global) in st.comps.map (·, false) ++ st.globals.map (·, true) do
    let some ec := sp.counterpart? c global | found := found.push s!"no counterpart of {c.path}"; continue
    let log ← IO.mkRef #[]
    let bk := backend prelude st.datatypes c timeout none (st.usesStrings || st.usesSeqs) (st.usesSets || st.usesSeqs)
      st.usesProjection
    let results ← Fren.Core.checkComp (fun k => confirming sp ec k log (bk k)) (pairCore sp ec (toCore c) (c.indexes.map (·.2.2.1.start)))
      (Fren.Core.kindsFor global)
    -- A definedness result, by its index's position, as brute force keys it.
    let keyOf (r : CheckResult) :=
      if r.kind != .definedness then keyOf r else
      let pos? := r.prop?.bind fun p => (c.indexes.filter (·.1 == p))[r.index?.getD 0]?.map (·.2.2.1.start)
      (r.kind, r.prop?.map fun p => Name.num p (pos?.getD 0), r.target?)
    for x in ← log.get do
      found := found.push s!"{c.path}: refuted model ({kindName x.kind} {x.subject?}, hypothesis {x.hyp?}): {x.model}"
    if space sp ec > maxSpace then skipped := skipped + 1; continue
    let o := oracle sp ec
    for r in results do
      if r.kind == .redundancy && o.notAsked.contains (r.prop?.getD .anonymous) then
        found := found.push s!"{c.path}: {showKey (keyOf r)} was checked, but brute force says it is not asked"
      if r.verdict == .inconclusive then inconclusive := inconclusive + 1; continue
      match o.verdicts.find? (·.1 == keyOf r) with
      | some (_, v) =>
        compared := compared + 1
        if v != r.verdict then
          found := found.push s!"{c.path}: {showKey (keyOf r)}: fren says {repr r.verdict}, brute force says {repr v}"
      | none =>
        let ignored := r.kind == .redundancy && (r.prop?.any isRange || o.notAsked.contains (r.prop?.getD .anonymous))
        unless ignored do found := found.push s!"{c.path}: {showKey (keyOf r)}: no such check by brute force"
      if r.verdict == .fail then
        if let some why := checkDetail lst ec r then
          found := found.push s!"{c.path}: {showKey (keyOf r)}: wrong details: {why}"
    for (k, _) in o.verdicts do
      unless results.any (keyOf · == k) do
        found := found.push s!"{c.path}: {showKey k}: brute force checks it, but fren does not"
  return (found, compared, inconclusive, skipped)

def usage : String := "usage: fren_fuzz [--count N] [--seed N] [--out DIR] [--timeout SECONDS]"

def main (args : List String) : IO UInt32 := do
  let rec parse : List String → Nat × Nat × String × Nat → Option (Nat × Nat × String × Nat)
    | [], a => some a
    | "--count" :: n :: rest, (_, s, d, t) => n.toNat?.bind fun n => parse rest (n, s, d, t)
    | "--seed" :: n :: rest, (c, _, d, t) => n.toNat?.bind fun n => parse rest (c, n, d, t)
    | "--out" :: d :: rest, (c, s, _, t) => parse rest (c, s, d, t)
    | "--timeout" :: n :: rest, (c, s, d, _) => n.toNat?.bind fun n => parse rest (c, s, d, n)
    | _, _ => none
  let some (count, seed, dir, timeout) := parse args (100, 0, ".lake/fuzz", 10) | IO.eprintln usage; return 2
  IO.FS.createDirAll dir
  let mut bad := 0
  let mut compared := 0
  let mut inconclusive := 0
  let mut skipped := 0
  for i in [0:count] do
    let s := seed + i
    let g := genSpec.run' ⟨mix s.toUInt64 0x5eed⟩
    let start ← IO.monoMsNow
    let (found, n, u, k) ← runOne dir g.text timeout
    let elapsed := (← IO.monoMsNow) - start
    if elapsed > 5000 then IO.eprintln s!"seed {s}: slow, {elapsed / 1000}s"
    skipped := skipped + k
    compared := compared + n
    inconclusive := inconclusive + u
    unless found.isEmpty do
      bad := bad + 1
      let file : System.FilePath := dir / s!"seed{s}.fren"
      let header := String.join (found.toList.map fun f => s!"-- {f.replace "\n" " "}\n")
      IO.FS.writeFile file (s!"-- fren_fuzz --seed {s}\n" ++ header ++ g.text)
      IO.eprintln s!"seed {s}: {found.size} difference(s), written to {file}"
      for f in found.extract 0 3 do IO.eprintln s!"  {f}"
  IO.eprintln s!"fren_fuzz: {count} specs, {compared} results compared, {inconclusive} inconclusive, \
    {skipped} components too large for brute force, {bad} with differences"
  return if bad == 0 then 0 else 1

end FrenFuzz

def main (args : List String) : IO UInt32 := FrenFuzz.main args
