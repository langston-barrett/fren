-- keep-sorted start
import Fren.Seq
import FrenCli.Parse
import FrenCore.Names
import FrenCore.Regex
-- keep-sorted end

/-!
# The evaluator (`Reqs/Eval`)

The meaning of a spec on one behaviour: an interpretation and a value for
each variable. It is computed from the parsed items, with its own types and
its own reading of each expression, and shares only name resolution
(`Fren.Core.Table`) with the elaborator, so that it is an independent
statement of what a spec means, against which the formulas given to the
solver are confirmed (`FrenCli.Confirm`).

Evaluation is three-valued: a variable without a value, or a function
application that the interpretation does not give, is unknown (`none`),
and `and`, `or` and `when` are decided when one operand decides them, as
the search for behaviours (`FrenCli.Search`) needs.
-/

open Lean

namespace FrenCli.Eval

open Fren.Core (Table Resolved Role showPath)

inductive VTy where
  | bool
  | int
  | string
  | set (elem : VTy)
  | rel (a b : VTy)
  | seq (elem : VTy)
  /-- An enumeration or a record. -/
  | data (path : Name)
  | abstract (path : Name)
  deriving Inhabited, BEq, Hashable, Repr

inductive Val where
  | bool (b : Bool)
  | int (i : Int)
  | str (s : String)
  /-- A set, its members in the order of `Val.setOf`, without repeats. -/
  | set (members : Array Val)
  /-- A pair, a member of a relation. -/
  | pair (a b : Val)
  /-- A sequence, its elements in order. -/
  | seq (elems : Array Val)
  /-- Constructor `idx` of the enumeration or record `ty`, with its payload
  or fields. A record has one constructor. -/
  | ctor (ty : Name) (idx : Nat) (args : Array Val)
  /-- Value `k` of the abstract type `sort`. -/
  | abs (sort : Name) (k : Nat)
  deriving Inhabited, BEq, Hashable, Repr

structure Ctor where
  name : Name
  /-- A record's fields, with their names; a variant's payload, with
  anonymous names. -/
  fields : Array (Name × VTy)
  deriving Inhabited

structure DataDef where
  path : Name
  isRecord : Bool
  ctors : Array Ctor
  deriving Inhabited

inductive Op where
  | and | or | iff | eq | ne | lt | le | gt | ge | add | sub | mul | concat
  | member | union | inter | minus | subset | join
  deriving Inhabited, BEq, Repr

def Op.ofString? : String → Option Op
  | "and" => some .and | "or" => some .or | "iff" => some .iff
  | "=" => some .eq | "!=" => some .ne
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "++" => some .concat
  | "in" => some .member | "union" => some .union | "inter" => some .inter | "minus" => some .minus
  | "subset" => some .subset | "join" => some .join
  | _ => none

/-- A `match` arm's pattern: `_`, a variant with a name for each value
of its payload (`_` for one that is ignored), or the variants of an
or-pattern, which binds nothing. -/
inductive Pat where
  | wild
  | ctor (idx : Nat) (binders : Array Name)
  | alts (idxs : Array Nat)
  deriving Inhabited

/-- A resolved expression. -/
inductive Ex where
  | lit (v : Val)
  /-- A variable of the comp, such as `x` or `w.x`. -/
  | var (n : Name)
  /-- A binder of an enclosing `match` arm. -/
  | bound (n : Name)
  | not (a : Ex)
  | neg (a : Ex)
  | bin (op : Op) (a b : Ex)
  | when (negated : Bool) (c d : Ex)
  | ite (c a b : Ex)
  | app (f : Name) (args : Array Ex)
  | ctor (ty : Name) (idx : Nat) (args : Array Ex)
  /-- Field `idx` of a record. -/
  | field (e : Ex) (idx : Nat)
  | «match» (e : Ex) (arms : Array (Pat × Ex))
  /-- A method of a `String` (`Reqs/Lang/Expressions#methods`). -/
  | method (m : Fren.Core.Method) (recv : Ex) (args : Array Ex)
  /-- `{a, b}`. -/
  | setLit (elems : Array Ex)
  /-- `(a, b)`, in a relation literal or on the left of `in`. -/
  | pair (a b : Ex)
  /-- `[a, b]`. -/
  | seqLit (elems : Array Ex)
  /-- `q[i]`, at the source position `pos`, which pairs it with its
  definedness check (`Ex.indexGoals`). -/
  | index (q i : Ex) (pos : Nat)
  /-- `s.card`. -/
  | card (s : Ex)
  deriving Inhabited

structure Var where
  name : Name
  ty : VTy
  role : Role
  /-- Shown in counterexamples. -/
  isPub : Bool
  isDet : Bool := false
  deriving Inhabited

structure Constraint where
  kind : PropKind
  name : Name
  e : Ex
  deriving Inhabited

structure Inst where
  name : Name
  comp : Name
  /-- Each input of `comp`, with the expression bound to it; empty for a
  binder of a global expectation. -/
  bindings : Array (Name × Ex)
  deriving Inhabited

/-- A comp, or a global expectation: a comp whose path is its module, with
an instance per binder and the expectation as its only constraint. -/
structure Comp where
  path : Name
  /-- Its own variables, in declaration order. -/
  vars : Array Var
  constraints : Array Constraint
  insts : Array Inst
  isGlobal : Bool := false
  /-- Each defined output, with its definition. -/
  defs : Array (Name × Ex) := #[]
  deriving Inhabited

structure Spec where
  data : NameMap DataDef := {}
  /-- The abstract types, in order. -/
  sorts : Array Name := #[]
  funs : NameMap (Array VTy × VTy) := {}
  /-- Each defined function's parameters, as binders of its body, the
  body, and its result type. -/
  defs : NameMap (Array Name × Ex × VTy) := {}
  consts : NameMap (Val × VTy) := {}
  comps : Array Comp := #[]
  globals : Array Comp := #[]
  deriving Inhabited

def Spec.comp? (sp : Spec) (path : Name) : Option Comp := sp.comps.find? (·.path == path)

/-- Every variable of `c`: its own, then each instance's, named `w.x`, in
the order the elaborator gives them. -/
partial def Spec.flatVars (sp : Spec) (c : Comp) : Array Var := Id.run do
  let mut vs := c.vars
  for i in c.insts do
    let some d := sp.comp? i.comp | continue
    for v in sp.flatVars d do
      let role := Role.ofInst v.role v.isPub
      -- A binder's inputs are shown too.
      let isPub := if c.isGlobal then role != .instHidden else role == .instOutput
      vs := vs.push { name := i.name ++ v.name, ty := v.ty, role, isPub }
  return vs

/-! ## Evaluation -/

/-- What the abstract types and functions mean, as far as it is known. -/
structure Interp where
  fn : Name → Array Val → Option Val := fun _ _ => none

instance : Inhabited Interp := ⟨{}⟩

/-- The value of each variable, as far as it is known. -/
abbrev Look := Name → Option Val

def kleeneAnd : Option Val → Option Val → Option Val
  | some (.bool false), _ | _, some (.bool false) => some (.bool false)
  | some (.bool true), some (.bool true) => some (.bool true)
  | _, _ => none

def kleeneOr : Option Val → Option Val → Option Val
  | some (.bool true), _ | _, some (.bool true) => some (.bool true)
  | some (.bool false), some (.bool false) => some (.bool false)
  | _, _ => none

def notV : Option Val → Option Val
  | some (.bool b) => some (.bool !b)
  | _ => none

def intOp (f : Int → Int → Val) : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => some (f x y)
  | _, _ => none

/-- A set of `vs`: sorted by how they print, so that equal sets are equal
values. -/
def Val.setOf (vs : Array Val) : Val :=
  .set ((vs.toList.eraseDups.toArray.qsort fun a b => reprStr a < reprStr b))

def setOp (f : Array Val → Array Val → Val) : Option Val → Option Val → Option Val
  | some (.set a), some (.set b) => some (f a b)
  | _, _ => none

/-- An ordering, of `Int`s or of `String`s. -/
def ordV (f : Ordering → Bool) : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => some (.bool (f (compare x y)))
  | some (.str x), some (.str y) => some (.bool (f (compare x.toList y.toList)))
  | _, _ => none

/-- The pairs `(a, c)` for each `(a, b)` in `r` and `(b, c)` in `q`. -/
def joinPairs (r q : Array Val) : Array Val :=
  r.flatMap fun | .pair a b => q.filterMap (fun | .pair b' c => if b == b' then some (Val.pair a c) else none | _ => none)
                | _ => #[]

/-- The transitive closure of `r`: join with `r` until nothing is new,
which takes at most as many rounds as `r` has pairs' members squared. -/
def closurePairs (r : Array Val) : Array Val := Id.run do
  let mut s := r
  for _ in [0:r.size * r.size + 1] do
    let next := (s ++ joinPairs s r).toList.eraseDups.toArray
    if next.size == s.size then return s
    s := next
  return s

def binV : Op → Option Val → Option Val → Option Val
  | .and => kleeneAnd
  | .or => kleeneOr
  | .iff | .eq => fun x y => do return .bool ((← x) == (← y))
  | .ne => fun x y => do return .bool ((← x) != (← y))
  | .lt => ordV (· == .lt)
  | .le => ordV (· != .gt)
  | .gt => ordV (· == .gt)
  | .ge => ordV (· != .lt)
  | .concat => fun
    | some (.str x), some (.str y) => some (.str (x ++ y))
    | some (.seq x), some (.seq y) => some (.seq (x ++ y))
    | _, _ => none
  | .member => fun
    | some x, some (.set s) => some (.bool (s.contains x))
    | some x, some (.seq q) => some (.bool (q.contains x))
    | _, _ => none
  | .union => setOp fun a b => Val.setOf (a ++ b)
  | .inter => setOp fun a b => Val.setOf (a.filter b.contains)
  | .minus => setOp fun a b => Val.setOf (a.filter (!b.contains ·))
  | .subset => setOp fun a b => .bool (a.all b.contains)
  | .join => setOp fun a b => Val.setOf (joinPairs a b)
  | .add => intOp fun x y => .int (x + y)
  | .sub => intOp fun x y => .int (x - y)
  | .mul => intOp fun x y => .int (x * y)

partial def Ex.eval (I : Interp) (look : Look) (locals : List (Name × Val) := []) : Ex → Option Val
  | .lit v => some v
  | .var n => look n
  | .bound n => locals.lookup n
  | .not a => notV (a.eval I look locals)
  | .neg a => match a.eval I look locals with
    | some (.int x) => some (.int (-x))
    | _ => none
  | .bin op a b => binV op (a.eval I look locals) (b.eval I look locals)
  | .when negated c d =>
    let c := c.eval I look locals
    kleeneOr (notV (if negated then notV c else c)) (d.eval I look locals)
  | .ite c a b => match c.eval I look locals with
    | some (.bool true) => a.eval I look locals
    | some (.bool false) => b.eval I look locals
    | _ =>
      let x := a.eval I look locals
      if x.isSome && x == b.eval I look locals then x else none
  | .app f args => do I.fn f (← args.mapM (·.eval I look locals))
  | .method m recv args => do
    let r ← recv.eval I look locals
    let args ← args.mapM (·.eval I look locals)
    -- A relation's methods.
    if let .set ps := r then
      let fsts := ps.filterMap fun | .pair a _ => some a | _ => none
      let snds := ps.filterMap fun | .pair _ b => some b | _ => none
      return ← match m, (args[0]? : Option Val) with
        | .card, _ => some (.int ps.size)
        | .inverse, _ => some (Val.setOf (ps.filterMap fun | .pair a b => some (.pair b a) | _ => none))
        | .closure, _ => some (Val.setOf (closurePairs ps))
        | .domain, _ => some (Val.setOf fsts)
        | .range, _ => some (Val.setOf snds)
        | .image, some (.set s) =>
          some (Val.setOf (ps.filterMap fun | .pair a b => if s.contains a then some b else none | _ => none))
        | _, _ => none
    -- A sequence's methods, by `Fren.Seq`, over the elements' numbers in
    -- a table of the distinct values involved, which have decidable equality.
    if let .seq es := r then
      let table := (es ++ args.flatMap fun | .seq a => a | v => #[v]).toList.eraseDups.toArray
      let num (v : Val) : Nat := (table.findIdx? (· == v)).getD 0
      let q := Fren.Seq.ofList (es.toList.map num)
      let back (q : Fren.Seq Nat) : Val := .seq (q.toList.toArray.map (table[·]!))
      let seq (k : Nat) : Fren.Seq Nat := match args[k]? with
        | some (Val.seq a) => Fren.Seq.ofList (a.toList.map num)
        | _ => ∅
      let int (k : Nat) := match args[k]? with | some (Val.int i) => i | _ => 0
      return ← match m with
        | .len => some (.int (Fren.Seq.len q))
        | .startsWith => some (.bool (Fren.Seq.startsWith q (seq 0)))
        | .endsWith => some (.bool (Fren.Seq.endsWith q (seq 0)))
        | .contains => some (.bool (Fren.Seq.contains q (seq 0)))
        | .at => some (back (Fren.Seq.at q (int 0)))
        | .slice => some (back (Fren.Seq.slice q (int 0) (int 1)))
        | .indexOf => some (.int (Fren.Seq.indexOf q (seq 0) (int 1)))
        | .replace => some (back (Fren.Seq.replace q (seq 0) (seq 1)))
        | .update => do some (back (Fren.Seq.update q (int 0) (num (← args[1]?))))
        | .rev => some (back (Fren.Seq.rev q))
        | _ => none
    let .str s := r | none
    let str (k : Nat) := match args[k]? with | some (Val.str a) => a | _ => ""
    let int (k : Nat) := match args[k]? with | some (Val.int i) => i | _ => 0
    return match m with
      | .len => .int (Fren.Str.len s)
      | .startsWith => .bool (Fren.Str.startsWith s (str 0))
      | .endsWith => .bool (Fren.Str.endsWith s (str 0))
      | .contains => .bool (Fren.Str.contains s (str 0))
      | .matches => .bool (Fren.Str.matches s (str 0))
      | .at => .str (Fren.Str.at s (int 0))
      | .slice => .str (Fren.Str.slice s (int 0) (int 1))
      | .indexOf => .int (Fren.Str.indexOf s (str 0) (int 1))
      | .replace => .str (Fren.Str.replace s (str 0) (str 1))
      | .replaceAll => .str (Fren.Str.replaceAll s (str 0) (str 1))
      | _ => .int 0
  | .pair a b => do return .pair (← a.eval I look locals) (← b.eval I look locals)
  | .seqLit es => do return .seq (← es.mapM (·.eval I look locals))
  -- Out of range, an index is part of the interpretation, which is unknown.
  | .index q i _ => do
    let .seq es ← q.eval I look locals | none
    let .int k ← i.eval I look locals | none
    if 0 ≤ k && k < es.size then es[k.toNat]? else none
  | .ctor ty idx args => do return .ctor ty idx (← args.mapM (·.eval I look locals))
  | .setLit es => do return Val.setOf (← es.mapM (·.eval I look locals))
  | .card s => do
    let .set ms ← s.eval I look locals | none
    return .int ms.size
  | .field e idx => match e.eval I look locals with
    | some (.ctor _ _ vs) => vs[idx]?
    | _ => none
  | .match e arms => do
    let .ctor _ idx vs ← e.eval I look locals | none
    let some (p, body) := arms.find? fun
        | (.wild, _) => true
        | (.ctor i _, _) => i == idx
        | (.alts is, _) => is.contains idx
      | none
    match p with
    | .wild | .alts _ => body.eval I look locals
    | .ctor _ bs =>
      let new := (bs.zip vs).toList.filter (·.1 != `_)
      body.eval I look (new ++ locals)

/-- The trigger of a constraint (`Reqs/Lang/Components#triggers`): the
conditions of its top-level `when`/`unless` chain, conjoined. -/
def Ex.trigger? : Ex → Option Ex
  | .when negated c d =>
    let c := if negated then .not c else c
    match d.trigger? with
    | none => some c
    | some t => some (.bin .and c t)
  | _ => none

/-- The indexes in `e`, each with its position and its definedness: that
its position is in range wherever the conditions before it hold
(`check::definedness`). The conditions are read left to right, as the
elaborator reads them, through `when`, `unless`, `if`, `and`, `or` and the
arms of `match`; `wrap` puts a definedness under those around `e`. -/
partial def Ex.indexGoals (e : Ex) (wrap : Ex → Ex := id) : Array (Nat × Ex) :=
  let go (e : Ex) (w : Ex → Ex := wrap) := e.indexGoals w
  match e with
  | .lit _ | .var _ | .bound _ => #[]
  | .not a | .neg a | .field a _ | .card a => go a
  | .when negated c d => go c ++ go d (fun g => wrap (.when negated c g))
  | .ite c a b => go c ++ go a (fun g => wrap (.when false c g)) ++ go b (fun g => wrap (.when true c g))
  | .bin .and a b => go a ++ go b (fun g => wrap (.when false a g))
  | .bin .or a b => go a ++ go b (fun g => wrap (.when true a g))
  | .bin _ a b | .pair a b => go a ++ go b
  | .app _ args | .ctor _ _ args | .setLit args | .seqLit args => args.flatMap (go ·)
  | .method _ r args => go r ++ args.flatMap (go ·)
  | .index q i pos =>
    let bounds := Ex.bin .and (.bin .le (.lit (.int 0)) i) (.bin .lt i (.method .len q #[]))
    go q ++ go i ++ #[(pos, wrap bounds)]
  -- An arm's indexes are guarded by its pattern and the earlier ones not
  -- matching: the same `match`, true in every other arm.
  | .match s arms =>
    let arm (j : Nat) (g : Ex) : Ex :=
      .match s (arms.mapIdx fun j' (p, _) => (p, if j' == j then g else Ex.lit (.bool true)))
    go s ++ (List.range arms.size).toArray.flatMap fun j => go arms[j]!.2 (fun g => wrap (arm j g))

/-- A constraint of a comp nested at `pfx`, such as `w.v` for instance `v`
of instance `w`: `e` over the variables `pfx.x`. -/
structure Atom where
  /-- Where it comes from, such as `w.r` for requirement `r` of `w`'s comp,
  or `w.x` for `w`'s binding of `x`. -/
  label : Name
  pfx : Name
  e : Ex
  deriving Inhabited

def Atom.eval (a : Atom) (I : Interp) (look : Look) : Option Bool :=
  match a.e.eval I (fun n => look (a.pfx ++ n)) with
  | some (.bool b) => some b
  | _ => none

/-- Kleene conjunction: `false` if one is, `true` if all are. -/
def allHold (I : Interp) (look : Look) (atoms : Array Atom) : Option Bool := Id.run do
  let mut known := true
  for a in atoms do
    match a.eval I look with
    | some false => return some false
    | some true => pure ()
    | none => known := false
  return if known then some true else none

def Comp.ofKind (c : Comp) (k : PropKind) : Array Constraint := c.constraints.filter (·.kind == k)

def atomsOf (pfx : Name) (cs : Array Constraint) : Array Atom :=
  cs.map fun p => { label := pfx ++ p.name, pfx, e := p.e }

/-- The definitions of a comp nested at `pfx`, as equations, each labelled
with its output. -/
def Comp.defAtoms (c : Comp) (pfx : Name := .anonymous) : Array Atom :=
  c.defs.map fun (d, e) => { label := pfx ++ d, pfx, e := .bin .eq (.var d) e }

/-- The bindings of instance `i` of a comp nested at `pfx`, as equations. -/
def bindingAtoms (pfx : Name) (i : Inst) : Array Atom :=
  i.bindings.map fun (x, e) => { label := pfx ++ i.name ++ x, pfx, e := .bin .eq (.var (i.name ++ x)) e }

mutual
/-- What instance `i` of a comp nested at `pfx` contributes, `I_w`: its
bindings, and the meaning of its comp. -/
partial def Spec.instAtoms (sp : Spec) (pfx : Name) (i : Inst) : Array Atom :=
  match sp.comp? i.comp with
  | some d => bindingAtoms pfx i ++ sp.meaning d (pfx ++ i.name)
  | none => #[]

/-- Everything a comp nested at `pfx` says of its variables: its
assumptions, requirements and instances (`Reqs/Lang/Components#meaning`). -/
partial def Spec.meaning (sp : Spec) (c : Comp) (pfx : Name := .anonymous) : Array Atom :=
  c.defAtoms pfx ++ atomsOf pfx (c.ofKind .assume) ++ atomsOf pfx (c.ofKind .req) ++ c.insts.flatMap (sp.instAtoms pfx)
end

/-- `I`, of the instances before `upTo`. -/
def Spec.insts (sp : Spec) (c : Comp) (upTo : Nat := c.insts.size) : Array Atom :=
  (c.insts.extract 0 upTo).flatMap (sp.instAtoms .anonymous)

/-! ## Values, as Fren shows them (`Reqs/View#check-results`) -/

partial def Val.show (sp : Spec) : Val → String
  | .bool b => toString b
  | .int i => toString i
  | .str s => s.quote
  | .set ms => "{" ++ ", ".intercalate ((ms.map (·.show sp)).toList.mergeSort (· < ·)) ++ "}"
  | .pair a b => s!"({a.show sp}, {b.show sp})"
  | .seq es => "[" ++ ", ".intercalate (es.toList.map (·.show sp)) ++ "]"
  | .abs s k => s!"{s.getString!}#{k}"
  | .ctor ty idx args =>
    let short := ty.getString!
    match sp.data.find? ty with
    | some d =>
      match d.ctors[idx]? with
      | none => s!"{short}::?"
      | some c =>
      if d.isRecord then
        let fs := (c.fields.zip args).toList.map fun ((f, _), v) => s!"{f} := {v.show sp}"
        s!"{short} \{ {", ".intercalate fs} }"
      else if args.isEmpty then s!"{short}::{c.name}"
      else s!"{short}::{c.name}({", ".intercalate (args.toList.map (·.show sp))})"
    | none => s!"{short}::?"

/-! ## Lowering parsed items -/

structure LState where
  table : Table := {}
  module : Name := .anonymous
  /-- The scope that paths resolve in: the module, or the component being
  lowered, if it has `use`s. -/
  scope : Name := .anonymous
  spec : Spec := {}

abbrev L := StateT LState (Except String)

def liftE (x : Except Fren.Core.Error α) : L α :=
  match x with
  | .ok a => pure a
  | .error e => throw e.msg.headline

def segNames (segs : Array Ident) : Array Name := segs.map (Name.mkSimple ·.name)

def resolve (segs : Array Ident) : L Resolved := do
  let st ← get
  liftE (st.table.resolvePath st.scope (segNames segs))

/-- `a.b` as a `Name`. -/
def dotted (parts : List String) : Name := parts.foldl Name.mkStr .anonymous

partial def lowerTy (segs : Array Ident) : L VTy := do
  if segs.size == 1 && segs[0]!.name == "Bool" then return .bool
  if segs.size == 1 && segs[0]!.name == "Int" then return .int
  if segs.size == 1 && segs[0]!.name == "String" then return .string
  if segs[0]!.name == Parser.setSeg then return .set (← lowerTy (segs.extract 1))
  if segs[0]!.name == Parser.relSeg then
    let (a, b) := Parser.splitRel (segs.extract 1)
    return .rel (← lowerTy a) (← lowerTy b)
  if segs[0]!.name == Parser.seqSeg then return .seq (← lowerTy (segs.extract 1))
  match ← resolve segs with
  | .item { kind := .enumItem, path, .. } | .item { kind := .recordItem, path, .. } => return .data path
  | .item { kind := .typeItem, path, .. } => return .abstract path
  | r => throw s!"`{showPath r.path}` is not a type"

def dataDef (path : Name) : L DataDef := do
  let some d := (← get).spec.data.find? path | throw s!"unknown datatype `{showPath path}`"
  return d

structure Cx where
  /-- Every variable of the comp (`Spec.flatVars`). -/
  vars : Array Var := #[]
  /-- The binders of the enclosing `match` arms, innermost first. -/
  binders : List (Name × VTy) := []

/-- The type of the method `m` of a receiver of type `t`. -/
def methodTy (m : Fren.Core.Method) (t : VTy) : VTy :=
  match m.result, t with
  | .bool, _ => .bool
  | .int, _ => .int
  | .string, _ => .string
  | .elem, .seq e => e
  | _, .seq _ => t
  | _, .rel a b => match m with
    | .inverse => .rel b a
    | .closure => t
    | .domain => .set a
    | _ => .set b
  | _, _ => .bool

/-- Reads the fields `fs` of `e`, of type `ty`. -/
def readFields (e : Ex) (ty : VTy) (fs : List String) : L (Ex × VTy) := do
  let mut e := e
  let mut ty := ty
  for f in fs do
    if let .set _ := ty then
      unless f == "card" do throw s!"unknown method `{f}`"
      e := .card e
      ty := .int
      continue
    if ty matches .rel .. | .seq _ then
      let some m := Fren.Core.Method.ofName? f | throw s!"unknown method `{f}`"
      e := .method m e #[]
      ty := methodTy m ty
      continue
    -- A method of a `String`, without arguments.
    if ty == .string then
      let some m := Fren.Core.Method.ofName? f | throw s!"unknown method `{f}`"
      e := .method m e #[]
      ty := methodTy m ty
      continue
    let .data p := ty | throw s!"`.{f}` reads a field of a value that is not a record"
    let d ← dataDef p
    let some c := d.ctors[0]? | throw s!"`{showPath p}` has no constructor"
    let some idx := c.fields.findIdx? (·.1 == Name.mkSimple f) | throw s!"`{showPath p}` has no field `{f}`"
    e := .field e idx
    ty := c.fields[idx]!.2
  return (e, ty)

def evalClosed (e : Ex) : Option Val := e.eval {} fun _ => none

/-- `e` with each binder, and each mention of one, renamed by `f`. -/
partial def Ex.renameBound (f : Name → Name) : Ex → Ex
  | .lit v => .lit v
  | .var n => .var n
  | .bound n => .bound (f n)
  | .not a => .not (a.renameBound f)
  | .neg a => .neg (a.renameBound f)
  | .bin op a b => .bin op (a.renameBound f) (b.renameBound f)
  | .when negated c d => .when negated (c.renameBound f) (d.renameBound f)
  | .ite c a b => .ite (c.renameBound f) (a.renameBound f) (b.renameBound f)
  | .app g args => .app g (args.map (·.renameBound f))
  | .method m r args => .method m (r.renameBound f) (args.map (·.renameBound f))
  | .setLit es => .setLit (es.map (·.renameBound f))
  | .pair a b => .pair (a.renameBound f) (b.renameBound f)
  | .seqLit es => .seqLit (es.map (·.renameBound f))
  | .index q i pos => .index (q.renameBound f) (i.renameBound f) pos
  | .card e => .card (e.renameBound f)
  | .ctor ty idx args => .ctor ty idx (args.map (·.renameBound f))
  | .field e idx => .field (e.renameBound f) idx
  | .match e arms => .match (e.renameBound f) <| arms.map fun
    | (.wild, b) => (.wild, b.renameBound f)
    | (.alts is, b) => (.alts is, b.renameBound f)
    | (.ctor i bs, b) => (.ctor i (bs.map fun x => if x == `_ then x else f x), b.renameBound f)

/-- `e` with the binders of `σ` that are free in it replaced by their
expressions. -/
partial def Ex.subst (σ : List (Name × Ex)) : Ex → Ex
  | .lit v => .lit v
  | .var n => .var n
  | .bound n => (σ.lookup n).getD (.bound n)
  | .not a => .not (a.subst σ)
  | .neg a => .neg (a.subst σ)
  | .bin op a b => .bin op (a.subst σ) (b.subst σ)
  | .when negated c d => .when negated (c.subst σ) (d.subst σ)
  | .ite c a b => .ite (c.subst σ) (a.subst σ) (b.subst σ)
  | .app g args => .app g (args.map (·.subst σ))
  | .method m r args => .method m (r.subst σ) (args.map (·.subst σ))
  | .setLit es => .setLit (es.map (·.subst σ))
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .seqLit es => .seqLit (es.map (·.subst σ))
  | .index q i pos => .index (q.subst σ) (i.subst σ) pos
  | .card e => .card (e.subst σ)
  | .ctor ty idx args => .ctor ty idx (args.map (·.subst σ))
  | .field e idx => .field (e.subst σ) idx
  | .match e arms => .match (e.subst σ) <| arms.map fun
    | (.wild, b) => (.wild, b.subst σ)
    | (.alts is, b) => (.alts is, b.subst σ)
    -- An arm's binders shadow those of `σ`.
    | (.ctor i bs, b) => (.ctor i bs, b.subst (σ.filter (!bs.contains ·.1)))

mutual
partial def lowerExpr (cx : Cx) : Expr → L (Ex × VTy)
  | .when _ negated c d => do
    return (.when negated (← lowerExpr cx c).1 (← lowerExpr cx d).1, .bool)
  | .ite _ c a b => do
    let (a, t) ← lowerExpr cx a
    return (.ite (← lowerExpr cx c).1 a (← lowerExpr cx b).1, t)
  | .bin _ op a b => do
    let some o := Op.ofString? op | throw s!"unknown operator `{op}`"
    let (x, ta) ← lowerExpr cx a
    let (y, tb) ← lowerExpr cx b
    let t := match o, ta, tb with
      | .add, _, _ | .sub, _, _ | .mul, _, _ => VTy.int
      | .concat, _, _ => ta
      | .union, _, _ | .inter, _, _ | .minus, _, _ => ta
      | .join, .rel a _, .rel _ c => .rel a c
      | _, _, _ => .bool
    return (.bin o x y, t)
  | .not _ a => do return (.not (← lowerExpr cx a).1, .bool)
  | .neg _ a => do return (.neg (← lowerExpr cx a).1, .int)
  | .num _ d => return (.lit (.int d.toNat!), .int)
  | .str _ v => return (.lit (.str v), .string)
  | .set _ es => do
    let es ← es.mapM (lowerExpr cx)
    -- `{}` is typed by where it is written, which the evaluator does not need.
    let t : VTy := match (es[0]? : Option (Ex × VTy)) with
      | some (_, .rel a b) => .rel a b
      | some (_, t) => .set t
      | none => .set .bool
    return (.setLit (es.map (·.1)), t)
  | .seq _ es => do
    let es ← es.mapM (lowerExpr cx)
    return (.seqLit (es.map (·.1)), .seq ((es[0]?.map (·.2)).getD .bool))
  | .index span q i => do
    let (x, tq) ← lowerExpr cx q
    let (y, _) ← lowerExpr cx i
    return (.index x y span.start, match tq with | .seq t => t | _ => .bool)
  | .pair _ a b => do
    let (x, ta) ← lowerExpr cx a
    let (y, tb) ← lowerExpr cx b
    -- A pair's type is the relation it is a member of.
    return (.pair x y, .rel ta tb)
  | .method _ recv m args => do
    let (r, t) ← lowerExpr cx recv
    let some method := Fren.Core.Method.ofName? m.name | throw s!"unknown method `{m.name}`"
    let args ← args.mapM fun a => (·.1) <$> lowerExpr cx a
    return (.method method r args, methodTy method t)
  | .bool _ b => return (.lit (.bool b), .bool)
  | .path _ segs => do
    if segs.size == 1 then
      let parts := segs[0]!.name.splitOn "."
      -- A binder shadows the comp's variables; otherwise the longest
      -- prefix that is a variable, then fields.
      if let some (_, ty) := cx.binders.find? (·.1 == Name.mkSimple parts.head!) then
        return ← readFields (.bound (Name.mkSimple parts.head!)) ty parts.tail
      for k in (List.range parts.length).reverse do
        let n := dotted (parts.take (k + 1))
        if let some v := cx.vars.find? (·.name == n) then
          return ← readFields (.var n) v.ty (parts.drop (k + 1))
      if parts.length > 1 then throw s!"`{segs[0]!.name}` names no variable"
    match ← resolve segs with
    | .variant en idx => do
      let d ← dataDef en.path
      unless d.ctors[idx]!.fields.isEmpty do throw s!"`{showPath en.path}::{en.variants[idx]!}` needs a payload"
      return (.lit (.ctor en.path idx #[]), .data en.path)
    | .item { kind := .constItem, path, .. } =>
      let some (v, t) := (← get).spec.consts.find? path | throw s!"unknown constant `{showPath path}`"
      return (.lit v, t)
    | r => throw s!"`{showPath r.path}` is not a value"
  | .app _ segs args => do
    let args ← args.mapM fun a => (·.1) <$> lowerExpr cx a
    match ← resolve segs with
    | .item { kind := .fnItem, path, .. } =>
      -- A defined function's body, with its parameters standing for the
      -- arguments.
      if let some (ps, body, r) := (← get).spec.defs.find? path then
        return (body.subst (ps.zip args).toList, r)
      let some (_, r) := (← get).spec.funs.find? path | throw s!"unknown function `{showPath path}`"
      return (.app path args, r)
    | .variant en idx => return (.ctor en.path idx args, .data en.path)
    | r => throw s!"`{showPath r.path}` is not a function or a variant"
  | .record span ty fields => do
    let path ← match ← resolve ty with
      | .item { kind := .recordItem, path, .. } => pure path
      | r => throw s!"`{showPath r.path}` is not a record"
    let d ← dataDef path
    let some c := d.ctors[0]? | throw s!"`{showPath path}` has no constructor"
    let mut vals := #[]
    for (f, _) in c.fields do
      let some (x, e?) := fields.find? (fun (x, _) => Name.mkSimple x.name == f) | throw s!"no value for field `{f}`"
      vals := vals.push (← lowerExpr cx (e?.getD (.path span #[x]))).1
    return (.ctor path 0 vals, .data path)
  | .field _ e f => do
    let (x, t) ← lowerExpr cx e
    readFields x t [f.name]
  | .match _ scrutinee arms => do
    let (s, t) ← lowerExpr cx scrutinee
    let .data path := t | throw "the scrutinee of `match` is not an enumeration"
    let d ← dataDef path
    let mut out := #[]
    let mut ty := VTy.bool
    for (p, body) in arms do
      let (pat, bound) ← match p with
        | .wild _ => pure (Pat.wild, [])
        | .variant _ segs binders? => do
          let .variant en idx ← resolve segs | throw "a pattern names no variant"
          unless en.path == path do throw s!"the pattern's variant is not of `{showPath path}`"
          let bs := (binders?.getD #[]).map (Name.mkSimple ·.name)
          let tys := d.ctors[idx]!.fields.map (·.2)
          pure (Pat.ctor idx bs, (bs.zip tys).toList.filter (·.1 != `_))
        | .or _ alts => do
          let idxs ← alts.mapM fun
            | .variant _ segs _ => do
              let .variant en idx ← resolve segs | throw "a pattern names no variant"
              unless en.path == path do throw s!"the pattern's variant is not of `{showPath path}`"
              pure idx
            | _ => throw "a nested or-pattern"
          pure (Pat.alts idxs, [])
      let (b, t) ← lowerExpr { cx with binders := bound.reverse ++ cx.binders } body
      ty := t
      out := out.push (pat, b)
    return (.match s out, ty)
end

def varTy (ty? : Option (Array Ident)) : L VTy := do
  match ty? with
  | some t => lowerTy t
  | none => return .bool

/-- Imports `segs` into the current module, or into the component `scope`. -/
def declareUseIn (segs : Array Ident) (glob : Bool) (scope : Option Name) : L Unit := do
  let st ← get
  let u ← liftE (st.table.declareUse st.module (segNames segs) glob (scope.getD st.module))
  modify fun s => { s with table := s.table.addUse u, scope := scope.getD s.scope }

def lowerComp (isPub : Bool) (name : Ident) (members : Array Member) : L Unit := do
  let path := (← get).module ++ Name.mkSimple name.name
  for m in members do
    match m with
    | .use _ segs glob => declareUseIn segs glob (some path)
    | .useGroup _ pre paths => for p in paths do declareUseIn (pre ++ p) false (some path)
    | _ => pure ()
  let st ← get
  let mut vars := #[]
  for m in members do
    let .var isIn isPub isDet x ty? _ := m | continue
    vars := vars.push { name := Name.mkSimple x.name, ty := ← varTy ty?, role := if isIn then .input else .output, isPub, isDet }
  let mut pending := #[]
  for m in members do
    let .inst x p bs := m | continue
    let cpath ← match ← resolve p with
      | .item { kind := .compItem, path, .. } => pure path
      | r => throw s!"`{showPath r.path}` is not a component"
    pending := pending.push (Name.mkSimple x.name, cpath, bs)
  let shell : Comp := { path, vars, constraints := #[], insts := pending.map fun (w, c, _) => { name := w, comp := c, bindings := #[] } }
  let cx : Cx := { vars := st.spec.flatVars shell }
  let mut insts := #[]
  for (w, cpath, bs) in pending do
    let mut bindings := #[]
    for (b, e?) in bs do
      bindings := bindings.push (Name.mkSimple b.name, (← lowerExpr cx (e?.getD (.path b.span #[b]))).1)
    insts := insts.push { name := w, comp := cpath, bindings }
  let mut constraints := #[]
  for m in members do
    let .prop kind x e := m | continue
    constraints := constraints.push { kind, name := Name.mkSimple x.name, e := (← lowerExpr cx e).1 }
  let mut defs := #[]
  for m in members do
    let .var _ _ _ x _ (some e) := m | continue
    defs := defs.push (Name.mkSimple x.name, (← lowerExpr cx e).1)
  let c : Comp := { path, vars, constraints, insts, defs }
  modify fun s => { s with
    table := s.table.addItem { kind := .compItem, path, isPub, owner := s.module }
    scope := s.module
    spec.comps := s.spec.comps.push c }

def lowerGlobal (name : Ident) (binders : Array (Array Ident × Array Ident)) (body : Expr) : L Unit := do
  let mut insts := #[]
  for (xs, p) in binders do
    let cpath ← match ← resolve p with
      | .item { kind := .compItem, path, .. } => pure path
      | r => throw s!"`{showPath r.path}` is not a component"
    for x in xs do insts := insts.push { name := Name.mkSimple x.name, comp := cpath, bindings := #[] }
  let st ← get
  let shell : Comp := { path := st.module, vars := #[], constraints := #[], insts, isGlobal := true }
  let n := Name.mkSimple name.name
  let e := (← lowerExpr { vars := st.spec.flatVars shell } body).1
  modify fun s => { s with
    table := s.table.addItem { kind := .expectItem, path := s.module ++ n, isPub := false, owner := s.module }
    spec.globals := s.spec.globals.push { shell with constraints := #[{ kind := .expect, name := n, e }] } }

partial def lowerItem : Item → L Unit
  | .mod isPub segs => do
    let (path, new) ← liftE ((← get).table.declareModule (segNames segs) isPub)
    modify fun s => { s with table := new.foldl (·.addItem ·) s.table, module := path, scope := path }
  | .use _ segs glob => declareUse segs glob
  | .useGroup _ pre paths => do for p in paths do declareUse (pre ++ p) false
  | .enum isPub name variants => do
    let st ← get
    let path := st.module ++ Name.mkSimple name.name
    let vs := variants.map (Name.mkSimple ·.1.name)
    -- Declared first: a payload may have the enumeration's own type.
    modify fun s => { s with table := (s.table.addItem { kind := .enumItem, path, isPub, owner := s.module }).addEnum { path, variants := vs } }
    let mut ctors := #[]
    for (v, payload?) in variants do
      let tys ← (payload?.getD #[]).mapM lowerTy
      ctors := ctors.push { name := Name.mkSimple v.name, fields := tys.map (.anonymous, ·) }
    modify fun s => { s with spec.data := s.spec.data.insert path { path, isRecord := false, ctors } }
  | .record isPub name fields => do
    let st ← get
    let path := st.module ++ Name.mkSimple name.name
    let mut fs := #[]
    for (f, ty?) in fields do fs := fs.push (Name.mkSimple f.name, ← varTy ty?)
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      spec.data := s.spec.data.insert path { path, isRecord := true, ctors := #[{ name := `mk, fields := fs }] } }
  | .abstractType isPub name => do
    let path := (← get).module ++ Name.mkSimple name.name
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
      spec.sorts := s.spec.sorts.push path }
  | .function isPub name params result body => do
    let path := (← get).module ++ Name.mkSimple name.name
    let r ← varTy result
    match body with
    | none =>
      let ps ← params.mapM (lowerTy ·.1)
      modify fun s => { s with spec.funs := s.spec.funs.insert path (ps, r) }
    | some body =>
      let ps ← params.mapM fun (p, ty?) => return (Name.mkSimple p[0]!.name, ← varTy ty?)
      let (b, _) ← lowerExpr { binders := ps.toList.reverse } body
      -- Binders named after the function, so that substituting arguments
      -- never captures a binder of theirs: theirs are a comp's or another
      -- function's.
      let b := b.renameBound (path ++ ·)
      modify fun s => { s with spec.defs := s.spec.defs.insert path (ps.map (path ++ ·.1), b, r) }
    modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
  | .const isPub name ty value => do
    let path := (← get).module ++ Name.mkSimple name.name
    let t ← lowerTy ty
    let (e, _) ← lowerExpr {} value
    let some v := evalClosed e | throw s!"the value of `{showPath path}` cannot be evaluated"
    modify fun s => { s with
      table := s.table.addItem { kind := .constItem, path, isPub, owner := s.module }
      spec.consts := s.spec.consts.insert path (v, t) }
  | .comp isPub name members => lowerComp isPub name members
  | .global name binders body => lowerGlobal name binders body
  | .claim .. | .check _ => pure ()
  | .lintSetting _ _ _ _ _ body? => do if let some b := body? then lowerItem b
where
  declareUse (segs : Array Ident) (glob : Bool) : L Unit := declareUseIn segs glob none

/-- The spec of the files' items, which the elaborator accepted, with the
names it declares. -/
def lowerAll (files : Array (Array Item)) : Except String LState := do
  let mut st : LState := {}
  for items in files do
    st := { st with module := .anonymous, scope := .anonymous }
    for item in items do
      st := (← (lowerItem item).run st).2
  return st

def lowerFiles (files : Array (Array Item)) : Except String Spec := (·.spec) <$> lowerAll files

def VTy.show : VTy → String
  | .bool => "Bool"
  | .int => "Int"
  | .string => "String"
  | .set t => s!"Set({t.show})"
  | .rel a b => s!"Rel({a.show}, {b.show})"
  | .seq t => s!"Seq({t.show})"
  | .data p | .abstract p => showPath p

/-- A value written as Fren shows values (`Reqs/Eval#values`), of type
`ty`, read in module `module`. -/
def parseValue (st : LState) (module : Name) (ty : VTy) (text : String) : Except String Val := do
  let text := text.trimAscii.toString
  if let .abstract s := ty then
    let pre := s!"{s.getString!}#"
    let some k := (text.dropPrefix? pre).bind (·.toString.toNat?)
      | throw s!"`{text}` is not a value of `{showPath s}`, which are written `{pre}0`, `{pre}1`, ..."
    return .abs s k
  let toks ← match lex text.toList.toArray with
    | .ok toks => pure toks
    | .error e => throw e.msg.headline
  let (e, ps) ← match (Parser.expr).run { toks } with
    | .ok r => pure r
    | .error e => throw e.msg.headline
  unless ps.toks[ps.pos]?.any (·.tok == .eof) do throw s!"`{text}` is not a value"
  let ((ex, t), _) ← (lowerExpr {} e).run { st with module }
  let a (t : VTy) := if "AEIOU".contains t.show.front then "an" else "a"
  -- `{}` and `[]` have the type they are read at.
  let empty := match ex, ty with
    | .setLit #[], .set _ | .setLit #[], .rel .. | .seqLit #[], .seq _ => true
    | _, _ => false
  unless t == ty || empty do throw s!"`{text}` is {a t} `{t.show}`, not {a ty} `{ty.show}`"
  let some v := evalClosed ex | throw s!"`{text}` is not a value"
  return v

end FrenCli.Eval
