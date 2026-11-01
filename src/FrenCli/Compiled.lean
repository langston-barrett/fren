-- keep-sorted start
import FrenCli.Eval
-- keep-sorted end

/-!
# Compiled expressions

An expression compiled once to a closure, which a search runs at each
candidate instead of evaluating the expression (`Ex.eval`). Compiling
chooses each node's case, and its operands' closures, once, so that a run
does not match on the expression again.

The closure is the evaluator's meaning: `Ex.toRun_eq` proves that running
it gives what `Ex.eval` gives, at every fuel and in every context.
-/

open Lean

namespace FrenCli.Eval

/-- What `Ex.eval` reads besides the expression: the interpretation, the
variables' values, the bindings and the shared expressions. -/
structure Ctx where
  I : Interp
  look : Look
  locals : List (Name × Val) := []
  slots : Array (Option Val) := #[]
  frame : Array Binding := #[]
  memos : Array (Thunk (Option Val)) := #[]
  deriving Inhabited

/-- `e`'s value in `c`, with `fuel`. -/
@[inline] def Ctx.eval (c : Ctx) (fuel : Nat) (e : Ex) : Option Val :=
  e.eval c.I c.look c.locals c.slots c.frame c.memos fuel

/-- A compiled expression: its value at each fuel, in each context, and
whether it was compiled, rather than left to the evaluator. It is a
structure of two fields, which the compiler keeps as an object, rather than
as the closure itself: where a closure returns a `Run`, the compiler would
otherwise take the `Run`'s arguments as its own, so that the closure would
compile again at each run. -/
structure Run where
  run : Nat → Ctx → Option Val
  compiled : Bool := true

instance : Inhabited Run := ⟨{ run := fun _ _ => none }⟩

/-- A closure that spends a unit of fuel, as `Ex.eval` does at each call,
then runs `f` with the rest. -/
@[inline] def step (f : Nat → Ctx → Option Val) : Run where
  run n c := match n with
    | 0 => outOfFuel ()
    | n + 1 => f n c

/-- The structural recursions' bodies, compiled at one depth of calls:
each body by its index in `Compiled.bodies`, compiled when first run. -/
abbrev Level := Array (Thunk Run)

/-- `fr` with the bindings of `p`'s binders when it matches `v`, the
first innermost, as `Ex.eval` pushes `p.matchVal v`'s, or `none` if it
does not match. -/
partial def Pat.matchPush : Pat → Val → Array Binding → Option (Array Binding)
  | .wild, _, fr => some fr
  | .bind n, v, fr => some (fr.push (n, some v))
  | .bool b, .bool b', fr => if b == b' then some fr else none
  | .int lo hi, .int i, fr => if lo.all (· ≤ i) && hi.all (i ≤ ·) then some fr else none
  | .str s, .str s', fr => if s == s' then some fr else none
  | .ctor idx ps, .ctor _ idx' vs, fr =>
    if idx != idx' || ps.size != vs.size then none
    else (List.range ps.size).foldrM (init := fr) fun k fr => ps[k]!.matchPush vs[k]! fr
  | .alts ps, v, fr => ps.findSome? (·.matchPush v fr)
  | _, _, _ => none

namespace Run

/-! Each case's closure is made by a function of its own, which is not
inlined, from its parts already compiled: so the compiler cannot move the
compiling of a part into the closure, where it would be done again at
each run. -/

@[noinline] def lit (v : Val) : Run := step fun _ _ => some v

@[noinline] def var (x : Name) : Run := step fun _ c => c.look x

@[noinline] def slot (i : Nat) : Run := step fun _ c => if h : i < c.slots.size then c.slots[i] else none

@[noinline] def bound (x : Name) : Run := step fun _ c => match c.frame.findRev? (·.1 == x) with
  | some (_, v) => v
  | none => c.locals.lookup x

@[noinline] def boundAt (i : Nat) : Run :=
  step fun _ c => if i < c.frame.size then c.frame[c.frame.size - 1 - i]!.2 else none

@[noinline] def shared (i : Nat) : Run :=
  step fun _ c => if i < c.memos.size then c.memos[c.memos.size - 1 - i]!.get else none

@[noinline] def known (v : Option Val) : Run := step fun _ _ => v

@[noinline] def memo (ls : Array Run) (ca : Run) : Run := step fun n c =>
  let ms := ls.foldr (init := c.memos) fun x ms => ms.push (Thunk.mk fun _ => x.run n c)
  ca.run n { c with memos := ms }

@[noinline] def not (ca : Run) : Run := step fun n c => notV (ca.run n c)

@[noinline] def neg (ca : Run) : Run := step fun n c => match ca.run n c with
  | some (.int x) => some (.int (-x))
  | _ => none

@[noinline] def memberLit (ca : Run) (ces : Array Run) : Run := step fun n c => do
  let x ← ca.run n c
  boolV ((← ces.mapM (·.run n c)).contains x)

@[noinline] def and (ca cb : Run) : Run := step fun n c => match ca.run n c with
  | some (.bool false) => some (.bool false)
  | x => kleeneAnd x (cb.run n c)

@[noinline] def or (ca cb : Run) : Run := step fun n c => match ca.run n c with
  | some (.bool true) => some (.bool true)
  | x => kleeneOr x (cb.run n c)

@[noinline] def bin (op : Op) (a b : Ex) (ca cb : Run) : Run := step fun n c =>
  match Ex.countOfOne? c.I.defined c.I.definedCount op a b with
  | some (cd, conds) =>
    (cd.holds? (conds.map fun (x, inDef) =>
      match if inDef then x.eval c.I c.look [] #[] #[] #[] n else c.eval n x with
      | some (.bool b) => some b
      | _ => none)).map .bool
  | none => binV op (ca.run n c) (cb.run n c)

@[noinline] def «when» (negated : Bool) (ca cb : Run) : Run := step fun n c =>
  let x := ca.run n c
  match notV (if negated then notV x else x) with
  | some (.bool true) => some (.bool true)
  | x => kleeneOr x (cb.run n c)

@[noinline] def ite (cp ca cb : Run) : Run := step fun n c => match cp.run n c with
  | some (.bool true) => ca.run n c
  | some (.bool false) => cb.run n c
  | _ =>
    let x := ca.run n c
    if x.isSome && x == cb.run n c then x else none

/-- An application of the structural recursion whose body is `next`'s
`i`th, with the parameters `ps`. -/
@[noinline] def call (next : Thunk Level) (i : Nat) (ps : Array Name) (cargs : Array Run) : Run := step fun n c => do
  let vs ← cargs.mapM (·.run n c)
  match next.get[i]? with
  | some body => body.get.run n { I := c.I, look := c.look, locals := ps.toList.zip vs.toList }
  | none => none

@[noinline] def app (f : Name) (cargs : Array Run) : Run := step fun n c => do
  let vs ← cargs.mapM (·.run n c)
  c.I.fn f vs

@[noinline] def pre (ca : Run) : Run := step fun n c => ca.run n c

@[noinline] def cardinality (cd : Fren.Core.Cardinality) (cargs : Array Run) : Run := step fun n c =>
  let vs := cargs.toList.map fun a => match a.run n c with
    | some (.bool b) => some b
    | _ => none
  (cd.holds? vs).map .bool

@[noinline] def method (m : Fren.Core.Method) (cr : Run) (cargs : Array Run) : Run := step fun n c => do
  let r ← cr.run n c
  let vs ← cargs.mapM (·.run n c)
  r.method m vs

@[noinline] def «matches» (cr : Run) (p : String) (re : Fren.Core.Re) : Run := step fun n c => do
  let .str s ← cr.run n c | none
  match c.I.matchMemo p s with
  | some b => boolV b
  | none => boolV (re.matches s)

@[noinline] def pair (ca cb : Run) : Run := step fun n c => do return .pair (← ca.run n c) (← cb.run n c)

@[noinline] def seqLit (ces : Array Run) : Run := step fun n c => do return .seq (← ces.mapM (·.run n c))

@[noinline] def index (cq ci : Run) (u : Name) : Run := step fun n c => do
  let .seq es ← cq.run n c | none
  let .int j ← ci.run n c | none
  if 0 ≤ j && j < es.size then es[j.toNat]? else c.I.outOfRange u

@[noinline] def ctor (ty : Name) (idx : Nat) (cargs : Array Run) : Run :=
  step fun n c => do return .ctor ty idx (← cargs.mapM (·.run n c))

@[noinline] def setLit (ces : Array Run) : Run := step fun n c => do return Val.setOf (← ces.mapM (·.run n c))

@[noinline] def card (cs : Run) : Run := step fun n c => do
  let .set ms ← cs.run n c | none
  return .int ms.size

@[noinline] def field (ca : Run) (idx : Nat) : Run := step fun n c => match ca.run n c with
  | some (.ctor _ _ vs) => vs[idx]?
  | _ => none

@[noinline] def update (ca : Run) (cfs : Array (Nat × Run)) : Run := step fun n c => do
  let .ctor ty idx vs ← ca.run n c | none
  let mut vs := vs
  for (j, x) in cfs do vs := vs.set! j (← x.run n c)
  return .ctor ty idx vs

@[noinline] def table (crows : Array (Option Run × Run)) (unspec? : Option Name) : Run := step fun n c => do
  let taken? ← firstCaseIn crows fun (p?, v) => match p? with
    | none => some (some v)
    | some p => match p.run n c with
      | some (.bool true) => some (some v)
      | some (.bool false) => some none
      | _ => none
  match taken? with
  | some v => v.run n c
  | none => c.I.fn (← unspec?) #[]

@[noinline] def const (ca : Run) : Run := step fun n c => ca.run n { I := c.I, look := fun _ => none }

@[noinline] def typed (t : Fren.Core.PTy) (ca : Run) : Run :=
  step fun n c => do return .bool (← Ex.eval.typeV c.I n t (← ca.run n c))

@[noinline] def «match» (cs : Run) (carms : Array (Pat × Option Run × Run)) (unspec? : Option Name) : Run :=
  step fun n c => do
    let v ← cs.run n c
    let taken? ← firstCaseIn carms fun (p, g?, body) => match p.matchPush v c.frame with
      | none => some none
      | some fr =>
        let c' := { c with frame := fr }
        match g? with
        | none => some (some (c', body))
        | some g => match g.run n c' with
          | some (.bool true) => some (some (c', body))
          | some (.bool false) => some none
          | _ => none
    match taken? with
    | some (c', body) => body.run n c'
    | none => c.I.fn (← unspec?) #[]

@[noinline] def range (clo chi : Run) : Run := step fun n c => do
  let .int a ← clo.run n c | none
  let .int b ← chi.run n c | none
  if b - a > Fren.Core.Enumeration.maxEnumerated then none
  return .seq ((Array.range (b - a).toNat).map fun (j : Nat) => Val.int (a + j))

/-- `e`, evaluated. -/
@[noinline] def evaluated (e : Ex) : Run := { run := fun n c => c.eval n e, compiled := false }

end Run

/-- `e` compiled, `k` deep, below which it is evaluated. `R` gives each
structural recursion's index among the bodies and its parameters, and
`next` the bodies compiled for the calls that `e` makes. -/
def Ex.toRun (R : Name → Option (Nat × Array Name)) (next : Thunk Level) : Nat → Ex → Run
  | 0, e => .evaluated e
  | k + 1, e =>
    let go := Ex.toRun R next k
    match e with
    | .lit v => .lit v
    | .var x => .var x
    | .slot i => .slot i
    | .bound x => .bound x
    | .boundAt i => .boundAt i
    | .shared i => .shared i
    | .known v => .known v
    | .memo lets a => .memo (lets.map go) (go a)
    | .not a => .not (go a)
    | .neg a => .neg (go a)
    | .bin .member a (.setLit es) => .memberLit (go a) (es.map go)
    | .bin .and a b => .and (go a) (go b)
    | .bin .or a b => .or (go a) (go b)
    | .bin op a b => .bin op a b (go a) (go b)
    | .when negated a b => .when negated (go a) (go b)
    | .ite p a b => .ite (go p) (go a) (go b)
    | .app f args => match R f with
      | some (i, ps) => .call next i ps (args.map go)
      | none => .app f (args.map go)
    | .pre _ _ _ a => .pre (go a)
    | .cardinality cd args => .cardinality cd (args.map go)
    | .method m recv args => .method m (go recv) (args.map go)
    | .matches recv p re => .matches (go recv) p re
    | .pair a b => .pair (go a) (go b)
    | .seqLit es => .seqLit (es.map go)
    | .index q i _ u => .index (go q) (go i) u
    | .ctor ty idx args => .ctor ty idx (args.map go)
    | .setLit es => .setLit (es.map go)
    | .card s => .card (go s)
    | .field a idx => .field (go a) idx
    | .update a fs => .update (go a) (fs.map fun (j, x) => (j, go x))
    | .table _ rows unspec? => .table (rows.map fun (_, p?, v) => (p?.map go, go v)) unspec?
    | .const _ a => .const (go a)
    | .typed t _ a => .typed t (go a)
    | .match s arms _ _ unspec? _ => .match (go s) (arms.map fun (p, g?, b) => (p, g?.map go, go b)) unspec?
    | .range lo hi => .range (go lo) (go hi)
    | e => .evaluated e

/-- How deep `Ex.toRun` compiles: deeper than any expression. -/
def compileDepth : Nat := 1 <<< 20

/-- The structural recursions of a spec, to compile: their bodies, and,
for each, its index among them and its parameters. -/
structure Recursions where
  bodies : Array Ex := #[]
  index : NameMap (Nat × Array Name) := {}
  deriving Inhabited

def Recursions.of (recDefs : NameMap (Array Name × Ex)) : Recursions :=
  recDefs.foldl (init := {}) fun c f (ps, b) =>
    { bodies := c.bodies.push b, index := c.index.insert f (c.bodies.size, ps) }

/-- The bodies, compiled at each depth of calls, `d` deep, below which they
are evaluated. Each depth's are shared by the calls at that depth, and
each body is compiled when it is first run. -/
def Recursions.level (rs : Recursions) : Nat → Level
  | 0 => rs.bodies.map fun b => Thunk.pure (.evaluated b)
  | d + 1 =>
    let next := Thunk.mk fun _ => rs.level d
    rs.bodies.map fun b => Thunk.mk fun _ => b.toRun rs.index.find? next compileDepth

/-- A spec's structural recursions, with their bodies compiled for the
calls at each depth, built once, so that the closures that call them share
them. -/
structure Compiled where
  recursions : Recursions
  top : Thunk Level

def Compiled.of (recDefs : NameMap (Array Name × Ex)) : Compiled :=
  let rs := Recursions.of recDefs
  { recursions := rs, top := Thunk.mk fun _ => rs.level compileDepth }

/-- `e`, compiled, for an interpretation whose structural recursions are
`cs`'s. -/
def Compiled.run (cs : Compiled) (e : Ex) : Run :=
  e.toRun cs.recursions.index.find? cs.top compileDepth

end FrenCli.Eval
