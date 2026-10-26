-- keep-sorted start
import Fren.Seq
import FrenCli.Parse
import FrenCore.Names
import FrenCore.Patterns
import FrenCore.Regex
import FrenCore.Table
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

Evaluation is monotone, which the search relies on: giving more variables
values never changes a value that is already known. Every case keeps it:
an operator is known only when the operands it needs are, an `if` whose
condition is unknown is known only when both branches agree, and the
interpretation is fixed.
-/

open Lean

namespace FrenCli.Eval

open Fren.Core (Table Resolved Role showPath)

inductive VTy where
  | bool
  | int
  /-- An `Int` that is at least 0. -/
  | nat
  | string
  | set (elem : VTy)
  | rel (a b : VTy)
  | seq (elem : VTy)
  /-- An enumeration or a record. -/
  | data (path : Name)
  | abstract (path : Name)
  /-- A newtype, whose values are its underlying type's, `under`
  (`Reqs/Lang/Items#newtypes`): only how they are shown differs. -/
  | newtype (path : Name) (under : VTy)
  deriving Inhabited, BEq, Hashable, Repr

/-- `t`, as an element type: a `Nat` is widened to an `Int`. -/
def VTy.widen : VTy → VTy
  | .nat => .int
  | t => t

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
  | and | or | iff | eq | ne | lt | le | gt | ge | add | sub | mul | div | mod | concat
  | member | union | inter | minus | subset | join
  deriving Inhabited, BEq, Repr

def Op.ofString? : String → Option Op
  | "and" => some .and | "or" => some .or | "iff" => some .iff
  | "=" => some .eq | "!=" => some .ne
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "++" => some .concat
  | "div" => some .div | "mod" => some .mod
  | "in" => some .member | "union" => some .union | "inter" => some .inter | "minus" => some .minus
  | "subset" => some .subset | "join" => some .join
  | _ => none

/-- A pattern (`Reqs/Lang/Patterns`), resolved: `_`, a binder, a literal,
the integers from `lo` to `hi` (`none` unbounded; a literal or a range), a
variant with a pattern for each value of its payload, or an or-pattern. -/
inductive Pat where
  | wild
  | bind (n : Name)
  | bool (b : Bool)
  | int (lo hi : Option Int)
  | str (s : String)
  | ctor (idx : Nat) (args : Array Pat)
  | alts (ps : Array Pat)
  deriving Inhabited

/-- The values that `p` binds when it matches `v`, or `none` if it does not
match. -/
partial def Pat.matchVal : Pat → Val → Option (List (Name × Val))
  | .wild, _ => some []
  | .bind n, v => some [(n, v)]
  | .bool b, .bool b' => if b == b' then some [] else none
  | .int lo hi, .int i => if lo.all (· ≤ i) && hi.all (i ≤ ·) then some [] else none
  | .str s, .str s' => if s == s' then some [] else none
  | .ctor idx ps, .ctor _ idx' vs =>
    if idx != idx' || ps.size != vs.size then none
    else (ps.zip vs).foldlM (init := []) fun acc (p, v) => return acc ++ (← p.matchVal v)
  | .alts ps, v => ps.findSome? (·.matchVal v)
  | _, _ => none

/-- `p` as the static rules see it (`Fren.Core.Pat`). -/
partial def Pat.core : Pat → Fren.Core.Pat
  | .wild => .wild
  | .bind _ => .wild true
  | .bool b => .bool b
  | .int lo hi => .int lo hi
  | .str s => .str s
  | .ctor idx ps => .ctor idx (ps.map Pat.core)
  | .alts ps => .or (ps.map Pat.core)

/-- The type of a value that patterns match, as they see it. -/
def VTy.patTy : VTy → Fren.Core.PatTy
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .data p => .enum p
  | _ => .other

/-- The names that `p` binds. -/
partial def Pat.binders : Pat → Array Name
  | .bind n => #[n]
  | .ctor _ ps | .alts ps => ps.flatMap Pat.binders
  | _ => #[]

/-- `p` with each binder renamed by `f`. -/
partial def Pat.rename (f : Name → Name) : Pat → Pat
  | .bind n => .bind (f n)
  | .ctor idx ps => .ctor idx (ps.map (·.rename f))
  | .alts ps => .alts (ps.map (·.rename f))
  | p => p

/-- A resolved expression. -/
inductive Ex where
  | lit (v : Val)
  /-- A variable of the comp, such as `x` or `w.x`. -/
  | var (n : Name)
  /-- A variable of a search, by its index in the search's environment
  (`Problem.solve`), which reads it without looking up its name. -/
  | slot (k : Nat)
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
  /-- `e`, a record, with each field `idx` of `fields` given a new value: a
  record update. -/
  | update (e : Ex) (fields : Array (Nat × Ex))
  /-- A `match` on `e`, whose `match` is at the source position `pos`:
  each arm's pattern, its guard, if it has one, and its body, and the
  position of each arm's pattern, which pair it with the checks of its arms
  (`Ex.tableGoals`). Where its arms without guards are not exhaustive, and
  no arm is taken, its value is the interpretation's of the function
  `unspec?` without parameters (`unspecifiedFn`), as a table's is. -/
  | «match» (e : Ex) (arms : Array (Pat × Option Ex × Ex)) (pos : Nat) (armPos : Array Nat) (unspec? : Option Name)
  /-- A method of a `String` (`Reqs/Lang/Expressions#methods`). -/
  | method (m : Fren.Core.Method) (recv : Ex) (args : Array Ex)
  /-- `recv.matches?(p)` for a literal `p`, with its pattern `re`, parsed
  once rather than at each evaluation. -/
  | «matches» (recv : Ex) (p : String) (re : Fren.Core.Re)
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
  /-- `exactly_one?(a, b)` or `at_most_one?(a, b)`
  (`Reqs/Lang/Expressions#cardinality`). -/
  | cardinality (c : Fren.Core.Cardinality) (args : Array Ex)
  /-- `forall`, or `exists` if not `all`, over the bound names `names`:
  its body at each of `insts`, the values of the names in each instance
  (`Reqs/Lang/Quantifiers#meaning`). -/
  | quant (all : Bool) (names : Array Name) (insts : Array (Array Val)) (body : Ex)
  /-- A table, whose `table` is at the source position `pos`: each row's
  position, its condition, `none` for `_`, and its value. The positions
  pair it with the checks of its rows (`Ex.tableGoals`). Without a `_` row,
  where no row holds, its value is the interpretation's of the function
  `unspec?` without parameters (`unspecifiedFn`). -/
  | table (pos : Nat) (rows : Array (Nat × Option Ex × Ex)) (unspec? : Option Name)
  /-- The constant `path`, whose value is unknown, as its expression `e`,
  which is the constant's own: what the checks ask of its indexes and
  tables is asked of the constant, not of where it is mentioned. -/
  | const (path : Name) (e : Ex)
  /-- `e`, an application, at the source position `pos`, of the function
  `f`, with each of `f`'s preconditions at its arguments: its value is
  `e`'s, and the positions pair the preconditions with their checks
  (`Ex.tableGoals`, `check::precondition`). -/
  | pre (pos : Nat) (f : Name) (goals : Array (Name × Ex)) (e : Ex)
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
  /-- A refinement's bindings, each bound variable of the abstract
  component with the expression it is bound to, which reads the concrete
  component's variables. The definedness of their indexes is checked. -/
  bindings : Array (Name × Ex) := #[]
  /-- For the body of a defined function or the value of a constant, as a
  comp for the checks of its tables, the function or constant, and its body
  or value, over the parameters as its inputs. -/
  body? : Option (Name × Ex) := none
  deriving Inhabited

structure Spec where
  data : NameMap DataDef := {}
  /-- The newtypes, each with its underlying type. -/
  newtypes : NameMap VTy := {}
  /-- The abstract types, in order. -/
  sorts : Array Name := #[]
  funs : NameMap (Array VTy × VTy) := {}
  /-- Each uninterpreted function with postconditions: its parameters, as
  binders of its clauses, its preconditions and its postconditions, which
  a random interpretation meets (`Reqs/Eval#searching-for-behaviours`). -/
  contracts : NameMap (Array Name × Array Ex × Array Ex) := {}
  /-- Each function with preconditions: its parameters, as binders of its
  preconditions, named after the function as a defined function's are,
  and each precondition with its name, which each application states of
  its arguments (`Ex.pre`). -/
  pres : NameMap (Array Name × Array (Name × Ex)) := {}
  /-- Each defined function's parameters, as binders of its body, the
  body, and its result type. -/
  defs : NameMap (Array Name × Ex × VTy) := {}
  /-- Each constant's value, as a literal, or as its expression where the
  value is unknown: an index out of range, or a table where no row holds. -/
  consts : NameMap (Ex × VTy) := {}
  comps : Array Comp := #[]
  globals : Array Comp := #[]
  /-- For each pattern `p` and string `s`, whether `s` matches `p`, as a
  thunk, so that it is matched once however often a search asks
  (`Spec.withMatchMemo`). -/
  matchMemo : Std.HashMap String (Std.HashMap String (Thunk Bool)) := {}
  /-- The bodies of defined functions and values of constants that have
  tables, each as a comp (`Comp.body?`). -/
  bodies : Array Comp := #[]
  deriving Inhabited

def Spec.comp? (sp : Spec) (path : Name) : Option Comp := sp.comps.find? (·.path == path)

/-- Every value of `t`, a type that a quantifier ranges over
(`lang::quantified_type`), in the order of a quantifier's instances
(`Reqs/Lang/Quantifiers#meaning`). The elaborator has rejected any other
type, such as a recursive enumeration. -/
partial def Spec.values (sp : Spec) : VTy → Array Val
  | .bool => #[.bool true, .bool false]
  | .data p => match sp.data.find? p with
    | some d => (d.ctors.mapIdx fun idx c =>
        (c.fields.foldl (fun acc (_, t) => acc.flatMap fun pre => (sp.values t).map pre.push) #[#[]]).map (.ctor p idx ·)).flatten
    | none => #[]
  | _ => #[]

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
  /-- Whether the string `s` matches the pattern `p`, if it is known
  without matching it: `Fren.Core.Re.matches` of `p`'s parse, remembered
  (`Spec.withMatchMemo`). It is not part of the meaning. -/
  matchMemo : String → String → Option Bool := fun _ _ => none

instance : Inhabited Interp := ⟨{}⟩

/-- The value of each variable, as far as it is known. -/
abbrev Look := Name → Option Val

/-- `some (.bool b)`, without allocating it: each of the two values is a
closed term, which the compiler allocates once. -/
@[inline] def boolV (b : Bool) : Option Val := if b then some (.bool true) else some (.bool false)

def kleeneAnd : Option Val → Option Val → Option Val
  | some (.bool false), _ | _, some (.bool false) => some (.bool false)
  | some (.bool true), some (.bool true) => some (.bool true)
  | _, _ => none

def kleeneOr : Option Val → Option Val → Option Val
  | some (.bool true), _ | _, some (.bool true) => some (.bool true)
  | some (.bool false), some (.bool false) => some (.bool false)
  | _, _ => none

def notV : Option Val → Option Val
  | some (.bool b) => boolV !b
  | _ => none

@[inline] def intOp (f : Int → Int → Val) : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => some (f x y)
  | _, _ => none

/-- Whether `n` has a numeric component. -/
def nameHasNum : Name → Bool
  | .anonymous => false
  | .num .. => true
  | .str p _ => nameHasNum p

/-- `n` as `reprArg n` prints it. A string component after only string
components prints as a backquote and `Name.toString n`, which escapes
exactly as `Name.reprPrec` does (both are `toStringWithToken n true
(fun _ => false)`); any other name is printed by `Name.reprPrec` itself,
whose output has no line breaks. -/
def nameReprArg (n : Name) : String :=
  match n with
  | .str p _ => if nameHasNum p then (reprArg n).pretty else "`" ++ n.toString
  | _ => (reprArg n).pretty

/-- `v` printed as its derived `Repr` prints it, appended to `out`, in
argument position if `arg`, but on one line: with each of the
pretty-printer's line breaks as a space. Each constructor of `Val` has
arguments, so in argument position it is parenthesized. -/
partial def Val.reprFlat (out : String) (arg : Bool) (v : Val) : String :=
  let out := if arg then out.push '(' else out
  let out := match v with
    | .bool b => out ++ "FrenCli.Eval.Val.bool " ++ (if b then "true" else "false")
    | .int i => out ++ "FrenCli.Eval.Val.int " ++ (if i < 0 then "(" ++ i.repr ++ ")" else i.repr)
    | .str s => out ++ "FrenCli.Eval.Val.str " ++ s.quote
    | .set ms => elems (out ++ "FrenCli.Eval.Val.set ") ms
    | .pair a b => (b.reprFlat ((a.reprFlat (out ++ "FrenCli.Eval.Val.pair ") true).push ' ') true)
    | .seq es => elems (out ++ "FrenCli.Eval.Val.seq ") es
    | .ctor ty idx args =>
      elems (out ++ "FrenCli.Eval.Val.ctor " ++ nameReprArg ty ++ " " ++ idx.repr ++ " ") args
    | .abs sort k => out ++ "FrenCli.Eval.Val.abs " ++ nameReprArg sort ++ " " ++ k.repr
  if arg then out.push ')' else out
where
  /-- An array, as `Array.repr` prints it on one line. -/
  elems (out : String) (vs : Array Val) : String :=
    if vs.isEmpty then out ++ "#[]" else
      (vs.foldl (init := (out ++ "#[", true)) fun (out, first) v =>
        (Val.reprFlat (if first then out else out ++ ", ") false v, false)).1.push ']'

/-- `reprStr v`, the key by which `Val.setOf` orders a set's members,
computed without the pretty-printer when it can be. `reprStr` lays out
`repr v` in 120 columns, and its line breaks are only those of groups and
fills that do not fit. When the whole text fits on one line, every group
fits, so `reprStr v` is that line, which is `Val.reprFlat`. Its length in
bytes bounds its length in characters, so a text of at most 100 bytes
fits. A longer one is printed by `reprStr` itself. Either way the key is
`reprStr v`, so the order of members is unchanged. -/
def Val.setKey (v : Val) : String :=
  let flat := v.reprFlat "" false
  if flat.utf8ByteSize ≤ 100 then flat else reprStr v

/-- A set of `vs`: sorted by how they print (`Val.setKey`), so that equal
sets are equal values. Each member is printed once, not at each
comparison. -/
def Val.setOf (vs : Array Val) : Val :=
  let ms := vs.toList.eraseDups.toArray
  if ms.size ≤ 1 then .set ms else
    .set ((ms.map fun v => (v.setKey, v)).qsort (·.1 < ·.1) |>.map (·.2))

@[inline] def setOp (f : Array Val → Array Val → Val) : Option Val → Option Val → Option Val
  | some (.set a), some (.set b) => some (f a b)
  | _, _ => none

/-- An ordering, of `Int`s, of `String`s, or of the variants of an ordered
enumeration, by their positions. -/
@[inline] def ordV (f : Ordering → Bool) : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => boolV (f (compare x y))
  | some (.str x), some (.str y) => boolV (f (compare x.toList y.toList))
  | some (.ctor t i _), some (.ctor u j _) => if t == u then boolV (f (compare i j)) else none
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

/-- The value of `op` on `x` and `y`. It takes both operands, rather than
returning a function of them, so that evaluating an operator calls no
closure. -/
def binV (op : Op) (x y : Option Val) : Option Val :=
  match op with
  | .and => kleeneAnd x y
  | .or => kleeneOr x y
  | .iff | .eq => match x, y with
    | some x, some y => boolV (x == y)
    | _, _ => none
  | .ne => match x, y with
    | some x, some y => boolV (x != y)
    | _, _ => none
  | .lt => ordV (· == .lt) x y
  | .le => ordV (· != .gt) x y
  | .gt => ordV (· == .gt) x y
  | .ge => ordV (· != .lt) x y
  | .concat => match x, y with
    | some (.str x), some (.str y) => some (.str (x ++ y))
    | some (.seq x), some (.seq y) => some (.seq (x ++ y))
    | _, _ => none
  | .member => match x, y with
    | some x, some (.set s) => boolV (s.contains x)
    | some x, some (.seq q) => boolV (q.contains x)
    | _, _ => none
  | .union => setOp (fun a b => Val.setOf (a ++ b)) x y
  | .inter => setOp (fun a b => Val.setOf (a.filter b.contains)) x y
  | .minus => setOp (fun a b => Val.setOf (a.filter (!b.contains ·))) x y
  | .subset => setOp (fun a b => .bool (a.all b.contains)) x y
  | .join => setOp (fun a b => Val.setOf (joinPairs a b)) x y
  | .add => intOp (fun x y => .int (x + y)) x y
  | .sub => intOp (fun x y => .int (x - y)) x y
  | .mul => intOp (fun x y => .int (x * y)) x y
  -- Euclidean, as SMT-LIB's; the divisor is never `0`.
  | .div => intOp (fun x y => .int (Int.ediv x y)) x y
  | .mod => intOp (fun x y => .int (Int.emod x y)) x y

/-- The value of an expression, as far as it is known: each variable as
`look` gives it, each binder of a `match` arm as `locals` does, and each
`slot k` as `slots[k]` does. -/
partial def Ex.eval (I : Interp) (look : Look) (locals : List (Name × Val) := []) (slots : Array (Option Val) := #[]) :
    Ex → Option Val
  | .lit v => some v
  | .var n => look n
  | .slot k => if h : k < slots.size then slots[k] else none
  | .bound n => locals.lookup n
  | .not a => notV (a.eval I look locals slots)
  | .neg a => match a.eval I look locals slots with
    | some (.int x) => some (.int (-x))
    | _ => none
  -- Membership in a set literal, without building the set, which does
  -- not change which values are members.
  | .bin .member a (.setLit es) => do
    let x ← a.eval I look locals slots
    boolV ((← es.mapM (·.eval I look locals slots)).contains x)
  -- `and`, `or` and `when` evaluate their second operand only when the
  -- first does not decide them, which gives the same value: `kleeneAnd`
  -- is `false` whatever its second operand when its first is `false`, and
  -- `kleeneOr` likewise `true`. Evaluation has no other effect.
  | .bin .and a b => match a.eval I look locals slots with
    | some (.bool false) => some (.bool false)
    | x => kleeneAnd x (b.eval I look locals slots)
  | .bin .or a b => match a.eval I look locals slots with
    | some (.bool true) => some (.bool true)
    | x => kleeneOr x (b.eval I look locals slots)
  | .bin op a b => binV op (a.eval I look locals slots) (b.eval I look locals slots)
  | .when negated c d =>
    let c := c.eval I look locals slots
    match notV (if negated then notV c else c) with
    | some (.bool true) => some (.bool true)
    | x => kleeneOr x (d.eval I look locals slots)
  | .ite c a b => match c.eval I look locals slots with
    | some (.bool true) => a.eval I look locals slots
    | some (.bool false) => b.eval I look locals slots
    | _ =>
      let x := a.eval I look locals slots
      if x.isSome && x == b.eval I look locals slots then x else none
  | .app f args => do I.fn f (← args.mapM (·.eval I look locals slots))
  | .pre _ _ _ e => e.eval I look locals slots
  -- Known once the unknown arguments cannot change it: with two `true`,
  -- whatever the rest are.
  | .cardinality c args =>
    let vs := args.map (·.eval I look locals slots)
    let trues := (vs.filter (· == some (.bool true))).size
    let unknown := (vs.filter fun v => !(v matches some (.bool _))).size
    if unknown == 0 || trues ≥ 2 then some (.bool (c.holds trues))
    else if c == .atMostOne && trues + unknown ≤ 1 then some (.bool true)
    else none
  | .method m recv args => do
    let r ← recv.eval I look locals slots
    let args ← args.mapM (·.eval I look locals slots)
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
      -- A length needs no table: it is the number of elements, which the
      -- numbering keeps.
      if let .len := m then return .int es.size
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
    -- An `Int`'s methods.
    if let .int x := r then
      return ← match m, (args[0]? : Option Val) with
        | .abs, _ => some (.int (if x < 0 then -x else x))
        | .min, some (.int y) => some (.int (if x ≤ y then x else y))
        | .max, some (.int y) => some (.int (if x ≥ y then x else y))
        | _, _ => none
    -- An ordered enumeration's methods, by the variants' positions.
    if let .ctor t i _ := r then
      return ← match m, (args[0]? : Option Val) with
        | .min, some y@(.ctor u j _) => if t == u then some (if i ≤ j then r else y) else none
        | .max, some y@(.ctor u j _) => if t == u then some (if i ≥ j then r else y) else none
        | _, _ => none
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
  | .matches recv p re => do
    let .str s ← recv.eval I look locals slots | none
    -- `re` is `p`'s parse, so a remembered answer is `re`'s.
    match I.matchMemo p s with
    | some b => boolV b
    | none => boolV (re.matches s)
  | .pair a b => do return .pair (← a.eval I look locals slots) (← b.eval I look locals slots)
  | .seqLit es => do return .seq (← es.mapM (·.eval I look locals slots))
  -- Out of range, an index is part of the interpretation, which is unknown.
  | .index q i _ => do
    let .seq es ← q.eval I look locals slots | none
    let .int k ← i.eval I look locals slots | none
    if 0 ≤ k && k < es.size then es[k.toNat]? else none
  | .ctor ty idx args => do return .ctor ty idx (← args.mapM (·.eval I look locals slots))
  | .setLit es => do return Val.setOf (← es.mapM (·.eval I look locals slots))
  | .card s => do
    let .set ms ← s.eval I look locals slots | none
    return .int ms.size
  | .field e idx => match e.eval I look locals slots with
    | some (.ctor _ _ vs) => vs[idx]?
    | _ => none
  | .update e fs => do
    let .ctor ty idx vs ← e.eval I look locals slots | none
    let mut vs := vs
    for (k, x) in fs do vs := vs.set! k (← x.eval I look locals slots)
    return .ctor ty idx vs
  -- The first row whose condition holds; where none does, the
  -- interpretation's unspecified value of its type.
  | .table _ rows unspec? => do
    for (_, c?, v) in rows do
      match c? with
      | none => return ← v.eval I look locals slots
      | some c =>
        let .bool b ← c.eval I look locals slots | none
        if b then return ← v.eval I look locals slots
    I.fn (← unspec?) #[]
  -- A closed expression, which neither variables nor binders reach.
  | .const _ e => e.eval I (fun _ => none)
  -- The first arm whose pattern matches and whose guard holds; where none
  -- is taken, the interpretation's unspecified value of its type.
  | .match e arms _ _ unspec? => do
    let v ← e.eval I look locals slots
    for (p, g?, body) in arms do
      let some new := p.matchVal v | continue
      if let some g := g? then
        let .bool b ← g.eval I look (new ++ locals) slots | none
        unless b do continue
      return ← body.eval I look (new ++ locals) slots
    I.fn (← unspec?) #[]
  -- The conjunction or disjunction of its instances, decided when one
  -- instance decides it.
  | .quant all names insts body =>
    insts.foldl (init := some (.bool all)) fun acc vals =>
      let v := body.eval I look ((names.zip vals).toList ++ locals) slots
      if all then kleeneAnd acc v else kleeneOr acc v

/-- The trigger of a constraint (`Reqs/Lang/Components#triggers`): the
conditions of its top-level `when`/`unless` chain, conjoined. -/
def Ex.trigger? : Ex → Option Ex
  | .when negated c d =>
    let c := if negated then .not c else c
    match d.trigger? with
    | none => some c
    | some t => some (.bin .and c t)
  | _ => none

/-- The indexes, tables and `match`es in `e`, as the questions that the
checks ask of them, each with its position, the question about a table's
rows or a `match`'s arms (`none` for an index's definedness), and its
formula: that it holds wherever the conditions before it hold
(`check::definedness`, `check::completeness`, `check::disjointness`,
`check::reachability`). An index's position is its own, and a table's or
a `match`'s question is at its `table` or `match` for completeness, at
the later row for disjointness, and at the row's condition or `_`, or the
arm's pattern, for reachability. The conditions are read left to right, as the
elaborator reads them, through `when`, `unless`, `if`, `and`, `or`, the
arms of `match` and the rows of tables; `wrap` puts a formula under those
around `e`. -/
partial def Ex.siteGoals (e : Ex) (wrap : Ex → Ex := id) : Array (Nat × Option Fren.Core.TableGoal × Ex) :=
  let go (e : Ex) (w : Ex → Ex := wrap) := e.siteGoals w
  match e with
  | .lit _ | .var _ | .slot _ | .bound _ => #[]
  | .not a | .neg a | .field a _ | .card a => go a
  | .update a fs => go a ++ fs.flatMap (go ·.2)
  | .when negated c d => go c ++ go d (fun g => wrap (.when negated c g))
  | .ite c a b => go c ++ go a (fun g => wrap (.when false c g)) ++ go b (fun g => wrap (.when true c g))
  | .bin .and a b => go a ++ go b (fun g => wrap (.when false a g))
  | .bin .or a b => go a ++ go b (fun g => wrap (.when true a g))
  | .bin _ a b | .pair a b => go a ++ go b
  | .app _ args | .cardinality _ args | .ctor _ _ args | .setLit args | .seqLit args => args.flatMap (go ·)
  | .method _ r args => go r ++ args.flatMap (go ·)
  -- Its arguments' questions, then its preconditions', as the elaborator
  -- records them.
  | .pre pos f goals e => go e ++ goals.map fun (p, g) => (pos, some (.precondition f p), wrap g)
  | .matches r _ _ => go r
  | .index q i pos =>
    let bounds := Ex.bin .and (.bin .le (.lit (.int 0)) i) (.bin .lt i (.method .len q #[]))
    go q ++ go i ++ #[(pos, none, wrap bounds)]
  -- An arm's guard is guarded by its pattern's matching where no earlier
  -- arm is taken, and its body by its being the first arm taken: the same
  -- `match`, with `g` in that arm and true in every other and where no arm
  -- is taken. Then the `match`'s own questions.
  | .match s arms pos armPos unspec? =>
    let tt := Ex.lit (.bool true)
    let others (j : Nat) := (arms.extract 0 j).map fun (p, g?, _) => (p, g?, tt)
    let inGuard (j : Nat) (g : Ex) : Ex := .match s (others j ++ #[(arms[j]!.1, none, g), (.wild, none, tt)]) pos armPos none
    let inBody (j : Nat) (g : Ex) : Ex :=
      .match s (others j ++ #[(arms[j]!.1, arms[j]!.2.1, g), (.wild, none, tt)]) pos armPos none
    let inArms := (List.range arms.size).toArray.flatMap fun j =>
      (match arms[j]!.2.1 with | some c => go c (fun g => wrap (inGuard j g)) | none => #[]) ++
        go arms[j]!.2.2 (fun g => wrap (inBody j g))
    -- Where each arm is taken, if no earlier one is: its pattern matches and
    -- its guard holds; `none` for `_` or a binder without a guard.
    let taken := arms.map fun (p, g?, _) => match p, g? with
      | .wild, none | .bind _, none => none
      | _, _ => some (Ex.match s #[(p, none, g?.getD tt), (.wild, none, .lit (.bool false))] pos #[] none)
    let guarded := arms.map (·.2.1.isSome)
    let orF (cs : Array Ex) : Ex := if cs.isEmpty then .lit (.bool false) else cs.pop.foldr (fun c acc => .bin .or c acc) cs.back!
    -- Completeness is asked exactly where no arm may be taken.
    let goals := Fren.Core.splitGoals .match orF (.bin .and) .not tt taken guarded (unspec?.isSome)
    go s ++ inArms ++ goals.map fun (g, f) =>
      ((match g with | .reachability _ j => armPos[j]! | _ => pos), some g, wrap f)
  -- In every instance, whatever the quantifier: the instances do not guard
  -- each other.
  | .quant _ names insts body => go body (fun g => wrap (.quant true names insts g))
  -- A row's condition is guarded by the earlier rows' not holding, and its
  -- value by its own holding too; then the table's own questions.
  -- A constant's indexes and tables are the constant's.
  | .const .. => #[]
  | .table pos rows _ =>
    let unlessAll (cs : Array Ex) (g : Ex) : Ex := cs.foldr (fun c g => .when true c g) g
    let (inRows, _) := rows.foldl (init := ((#[] : Array (Nat × Option Fren.Core.TableGoal × Ex)), (#[] : Array Ex)))
      fun (acc, before) (_, c?, v) =>
        let inC := match c? with
          | some c => go c (fun g => wrap (unlessAll before g))
          | none => #[]
        let inV := go v (fun g => wrap (unlessAll before (match c? with | some c => .when false c g | none => g)))
        (acc ++ inC ++ inV, before ++ c?.toArray)
    let conds := rows.filterMap (·.2.1)
    let starts := rows.filterMap fun (p, c?, _) => c?.map fun _ => p
    let orF (cs : Array Ex) : Ex := if cs.isEmpty then .lit (.bool false) else cs.pop.foldr (fun c acc => .bin .or c acc) cs.back!
    let wild := (rows.back?.map (·.2.1.isNone)).getD false
    -- That a condition's indexes are in range where it evaluates them.
    let defined := conds.map fun c =>
      Fren.Core.allOf? (.bin .and) (c.siteGoals.filterMap fun (_, g?, f) => if g?.isNone then some f else none)
    inRows ++ (Fren.Core.tableGoals orF (.bin .and) .not (.lit (.bool true)) conds defined wild).map fun (g, f) =>
      ((match g with
        | .disjointness _ j => starts[j]!
        | .reachability _ j => rows[j]!.1
        | _ => pos), some g, wrap f)

/-- The indexes in `e`, each with its position and its definedness: that
its position is in range wherever the conditions before it hold
(`check::definedness`), read as `Ex.siteGoals` reads them. -/
def Ex.indexGoals (e : Ex) : Array (Nat × Ex) :=
  e.siteGoals.filterMap fun (pos, g?, f) => if g?.isNone then some (pos, f) else none

/-- The questions about the rows of the tables in `e`, each with where it
is reported and its formula, read as `Ex.siteGoals` reads them. -/
def Ex.tableGoals (e : Ex) : Array (Nat × Fren.Core.TableGoal × Ex) :=
  e.siteGoals.filterMap fun (pos, g?, f) => g?.map (pos, ·, f)

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
  c.defAtoms pfx ++ atomsOf pfx (c.ofKind .assume) ++ atomsOf pfx (c.ofKind .ensure) ++ c.insts.flatMap (sp.instAtoms pfx)
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

/-- `v`, of type `ty`, shown with its newtypes, which its value does not
record: `5` of the newtype `Ms` is `Ms(5)`. -/
partial def Val.showAs (sp : Spec) (ty : VTy) (v : Val) : String :=
  match ty, v with
  | .newtype p u, _ => s!"{p.getString!}({v.showAs sp u})"
  | .set t, .set ms => "{" ++ ", ".intercalate ((ms.map (·.showAs sp t)).toList.mergeSort (· < ·)) ++ "}"
  | .rel a b, .set ms =>
    let pair : Val → String
      | .pair x y => s!"({x.showAs sp a}, {y.showAs sp b})"
      | m => m.show sp
    "{" ++ ", ".intercalate ((ms.map pair).toList.mergeSort (· < ·)) ++ "}"
  | .seq t, .seq es => "[" ++ ", ".intercalate (es.toList.map (·.showAs sp t)) ++ "]"
  | .data p, .ctor _ idx args =>
    match (sp.data.find? p).bind (·.ctors[idx]?), sp.data.find? p with
    | some c, some d =>
      let shown := (c.fields.zip args).map fun ((_, t), a) => a.showAs sp t
      if d.isRecord then
        let fs := (c.fields.zip shown).toList.map fun ((f, _), a) => s!"{f} := {a}"
        s!"{p.getString!} \{ {", ".intercalate fs} }"
      else if args.isEmpty then s!"{p.getString!}::{c.name}"
      else s!"{p.getString!}::{c.name}({", ".intercalate shown.toList})"
    | _, _ => v.show sp
  | _, _ => v.show sp

/-! ## Lowering parsed items -/

structure LState where
  table : Table := {}
  module : Name := .anonymous
  /-- The scope that paths resolve in: the module, or the component being
  lowered, if it has `use`s. -/
  scope : Name := .anonymous
  spec : Spec := {}
  /-- The binders of `match` arms lowered so far, which number their names. -/
  fresh : Nat := 0

abbrev L := StateT LState (Except String)

def liftE (x : Except Fren.Core.Error α) : L α :=
  match x with
  | .ok a => pure a
  | .error e => throw e.msg.get.headline

def segNames (segs : Array Ident) : Array Name := segs.map (Name.mkSimple ·.name)

/-- The name that `x` declares: `x!` declares `x`. -/
def declName (x : Ident) : Name := (Fren.Core.declaredName (Name.mkSimple x.name)).1

def resolve (segs : Array Ident) : L Resolved := do
  let st ← get
  liftE (st.table.resolvePath st.scope (segNames segs))

/-- `a.b` as a `Name`. -/
def dotted (parts : List String) : Name := parts.foldl Name.mkStr .anonymous

partial def lowerTy (segs : Array Ident) : L VTy := do
  if segs.size == 1 && segs[0]!.name == "Bool" then return .bool
  if segs.size == 1 && segs[0]!.name == "Int" then return .int
  if segs.size == 1 && segs[0]!.name == "Nat" then return .nat
  if segs.size == 1 && segs[0]!.name == "String" then return .string
  if segs[0]!.name == Parser.setSeg then return .set (← lowerTy (segs.extract 1))
  if segs[0]!.name == Parser.relSeg then
    let (a, b) := Parser.splitRel (segs.extract 1)
    return .rel (← lowerTy a) (← lowerTy b)
  if segs[0]!.name == Parser.seqSeg then return .seq (← lowerTy (segs.extract 1))
  match ← resolve segs with
  | .item { kind := .recordItem, path, .. } =>
    if let some u := (← get).spec.newtypes.find? path then return .newtype path u
    return .data path
  | .item { kind := .enumItem, path, .. } => return .data path
  | .item { kind := .typeItem, path, .. } => return .abstract path
  | r => throw s!"`{showPath r.path}` is not a type"

def dataDef (path : Name) : L DataDef := do
  let some d := (← get).spec.data.find? path | throw s!"unknown datatype `{showPath path}`"
  return d

structure Cx where
  /-- Every variable of the comp (`Spec.flatVars`). -/
  vars : Array Var := #[]
  /-- The binders of the enclosing `match` arms, innermost first, each with
  its type and the name it is bound by in `Ex`, made unique so that a
  definition put under another arm is never captured. -/
  binders : List (Name × VTy × Name) := []
  /-- The names of the enclosing `let`s and `where` clauses, innermost
  first, each with its definition, which a mention of it stands for
  (`Reqs/Lang/Let#meaning`), and its type. A name is never also a binder. -/
  lets : List (Name × Ex × VTy) := []

/-- The type of the method `m` of a receiver of type `t`. -/
def methodTy (m : Fren.Core.Method) (t : VTy) : VTy :=
  match m.result, t with
  | .bool, _ => .bool
  -- `min` and `max`, the only methods of an ordered enumeration.
  | _, .data _ => t
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
    -- A newtype's field `0`, its value, which is the newtype's.
    if let .newtype _ u := ty then
      unless f == "0" do throw s!"a newtype has no field `{f}`"
      ty := u
      continue
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
    -- A method of a `String` or an `Int`, without arguments.
    if ty == .string || ty == .int || ty == .nat then
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
  | .slot k => .slot k
  | .bound n => .bound (f n)
  | .not a => .not (a.renameBound f)
  | .neg a => .neg (a.renameBound f)
  | .bin op a b => .bin op (a.renameBound f) (b.renameBound f)
  | .when negated c d => .when negated (c.renameBound f) (d.renameBound f)
  | .ite c a b => .ite (c.renameBound f) (a.renameBound f) (b.renameBound f)
  | .app g args => .app g (args.map (·.renameBound f))
  | .pre pos g gs e => .pre pos g (gs.map fun (p, x) => (p, x.renameBound f)) (e.renameBound f)
  | .cardinality c args => .cardinality c (args.map (·.renameBound f))
  | .method m r args => .method m (r.renameBound f) (args.map (·.renameBound f))
  | .matches r p re => .matches (r.renameBound f) p re
  | .setLit es => .setLit (es.map (·.renameBound f))
  | .pair a b => .pair (a.renameBound f) (b.renameBound f)
  | .seqLit es => .seqLit (es.map (·.renameBound f))
  | .index q i pos => .index (q.renameBound f) (i.renameBound f) pos
  | .card e => .card (e.renameBound f)
  | .ctor ty idx args => .ctor ty idx (args.map (·.renameBound f))
  | .field e idx => .field (e.renameBound f) idx
  | .update e fs => .update (e.renameBound f) (fs.map fun (k, x) => (k, x.renameBound f))
  | .table pos rows u => .table pos (rows.map fun (p, c?, v) => (p, c?.map (·.renameBound f), v.renameBound f)) u
  | .const p e => .const p e
  | .match e arms pos ps u =>
    .match (e.renameBound f) (arms.map fun (p, g?, b) => (p.rename f, g?.map (·.renameBound f), b.renameBound f)) pos ps u
  | .quant all ns insts b => .quant all (ns.map f) insts (b.renameBound f)

/-- `e` with each variable renamed by `f`. -/
partial def Ex.renameVars (f : Name → Name) : Ex → Ex
  | .lit v => .lit v
  | .var n => .var (f n)
  | .slot k => .slot k
  | .bound n => .bound n
  | .not a => .not (a.renameVars f)
  | .neg a => .neg (a.renameVars f)
  | .bin op a b => .bin op (a.renameVars f) (b.renameVars f)
  | .when negated c d => .when negated (c.renameVars f) (d.renameVars f)
  | .ite c a b => .ite (c.renameVars f) (a.renameVars f) (b.renameVars f)
  | .app g args => .app g (args.map (·.renameVars f))
  | .pre pos g gs e => .pre pos g (gs.map fun (p, x) => (p, x.renameVars f)) (e.renameVars f)
  | .cardinality c args => .cardinality c (args.map (·.renameVars f))
  | .method m r args => .method m (r.renameVars f) (args.map (·.renameVars f))
  | .matches r p re => .matches (r.renameVars f) p re
  | .setLit es => .setLit (es.map (·.renameVars f))
  | .pair a b => .pair (a.renameVars f) (b.renameVars f)
  | .seqLit es => .seqLit (es.map (·.renameVars f))
  | .index q i pos => .index (q.renameVars f) (i.renameVars f) pos
  | .card e => .card (e.renameVars f)
  | .ctor ty idx args => .ctor ty idx (args.map (·.renameVars f))
  | .field e idx => .field (e.renameVars f) idx
  | .update e fs => .update (e.renameVars f) (fs.map fun (k, x) => (k, x.renameVars f))
  | .match e arms pos ps u => .match (e.renameVars f) (arms.map fun (p, g?, b) => (p, g?.map (·.renameVars f), b.renameVars f)) pos ps u
  | .quant all ns insts b => .quant all ns insts (b.renameVars f)
  | .table pos rows u => .table pos (rows.map fun (p, c?, v) => (p, c?.map (·.renameVars f), v.renameVars f)) u
  | .const p e => .const p e

/-- `e` with each variable `n` replaced by `f n`. -/
partial def Ex.substVars (f : Name → Ex) : Ex → Ex
  | .lit v => .lit v
  | .var n => f n
  | .slot k => .slot k
  | .bound n => .bound n
  | .not a => .not (a.substVars f)
  | .neg a => .neg (a.substVars f)
  | .bin op a b => .bin op (a.substVars f) (b.substVars f)
  | .when negated c d => .when negated (c.substVars f) (d.substVars f)
  | .ite c a b => .ite (c.substVars f) (a.substVars f) (b.substVars f)
  | .app g args => .app g (args.map (·.substVars f))
  | .pre pos g gs e => .pre pos g (gs.map fun (p, x) => (p, x.substVars f)) (e.substVars f)
  | .cardinality c args => .cardinality c (args.map (·.substVars f))
  | .method m r args => .method m (r.substVars f) (args.map (·.substVars f))
  | .matches r p re => .matches (r.substVars f) p re
  | .setLit es => .setLit (es.map (·.substVars f))
  | .pair a b => .pair (a.substVars f) (b.substVars f)
  | .seqLit es => .seqLit (es.map (·.substVars f))
  | .index q i pos => .index (q.substVars f) (i.substVars f) pos
  | .card e => .card (e.substVars f)
  | .ctor ty idx args => .ctor ty idx (args.map (·.substVars f))
  | .field e idx => .field (e.substVars f) idx
  | .update e fs => .update (e.substVars f) (fs.map fun (k, x) => (k, x.substVars f))
  | .match e arms pos ps u => .match (e.substVars f) (arms.map fun (p, g?, b) => (p, g?.map (·.substVars f), b.substVars f)) pos ps u
  | .quant all ns insts b => .quant all ns insts (b.substVars f)
  | .table pos rows u => .table pos (rows.map fun (p, c?, v) => (p, c?.map (·.substVars f), v.substVars f)) u
  | .const p e => .const p e

/-- The comp that checks that `c` refines `a` (`Reqs/Lang/Refinement`): its
inputs are `c`'s, its assumptions `a`'s, it has an instance `w` of `c` and
`a`'s instances, and its expectations are `a`'s requirements and
definitions, with each variable of `a` read as its binding in `bindings`,
over `c`'s variables, or else as `c`'s of the same name, and `c`'s outputs
read from `w`'s. -/
def Comp.refinement (path w : Name) (c a : Comp) (bindings : Array (Name × Ex) := #[]) : Comp :=
  let outs := (a.vars.filter (·.role == .output)).map (·.name)
  let ownC (e : Ex) := e.renameVars fun n => if c.vars.any (fun v => v.name == n && v.role != .input) then w ++ n else n
  let ren (e : Ex) := e.substVars fun n => match bindings.find? (·.1 == n) with
    | some (_, b) => ownC b
    | none => .var (if outs.contains n then w ++ n else n)
  let inputs := c.vars.filter (·.role == .input)
  { path
    vars := inputs
    constraints := (a.constraints.filter (·.kind == .assume)).map (fun p => { p with e := ren p.e })
      ++ (a.constraints.filter (·.kind == .ensure)).map (fun p => { p with kind := .expect, e := ren p.e })
      ++ a.defs.map fun (d, e) => { kind := .expect, name := d, e := .bin .eq (ren (.var d)) (ren e) }
    insts := #[{ name := w, comp := c.path, bindings := inputs.map fun v => (v.name, .var v.name) }]
      ++ a.insts.map fun i => { i with bindings := i.bindings.map fun (x, e) => (x, ren e) }
    bindings := bindings.map fun (x, b) => (x, ownC b) }

/-- `e` with the binders of `σ` that are free in it replaced by their
expressions. -/
partial def Ex.subst (σ : List (Name × Ex)) : Ex → Ex
  | .lit v => .lit v
  | .var n => .var n
  | .slot k => .slot k
  | .bound n => (σ.lookup n).getD (.bound n)
  | .not a => .not (a.subst σ)
  | .neg a => .neg (a.subst σ)
  | .bin op a b => .bin op (a.subst σ) (b.subst σ)
  | .when negated c d => .when negated (c.subst σ) (d.subst σ)
  | .ite c a b => .ite (c.subst σ) (a.subst σ) (b.subst σ)
  | .app g args => .app g (args.map (·.subst σ))
  | .pre pos g gs e => .pre pos g (gs.map fun (p, x) => (p, x.subst σ)) (e.subst σ)
  | .cardinality c args => .cardinality c (args.map (·.subst σ))
  | .method m r args => .method m (r.subst σ) (args.map (·.subst σ))
  | .matches r p re => .matches (r.subst σ) p re
  | .setLit es => .setLit (es.map (·.subst σ))
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .seqLit es => .seqLit (es.map (·.subst σ))
  | .index q i pos => .index (q.subst σ) (i.subst σ) pos
  | .card e => .card (e.subst σ)
  | .ctor ty idx args => .ctor ty idx (args.map (·.subst σ))
  | .field e idx => .field (e.subst σ) idx
  | .update e fs => .update (e.subst σ) (fs.map fun (k, x) => (k, x.subst σ))
  | .table pos rows u => .table pos (rows.map fun (p, c?, v) => (p, c?.map (·.subst σ), v.subst σ)) u
  | .const p e => .const p e
  -- An arm's binders shadow those of `σ`.
  | .match e arms pos ps u =>
    .match (e.subst σ) (arms.map fun (p, g?, b) =>
      let σ' := σ.filter (!p.binders.contains ·.1)
      (p, g?.map (·.subst σ'), b.subst σ')) pos ps u
  -- So do a quantifier's bound names.
  | .quant all ns insts b => .quant all ns insts (b.subst (σ.filter (!ns.contains ·.1)))

/-- The value of a bound of a range pattern. -/
def boundValue : Bound → L Int
  | .num _ v => return v
  | .path _ segs => do
    let .item { kind := .constItem, path, .. } ← resolve segs | throw "a range's bound is not a constant"
    let some (.lit (.int v), _) := (← get).spec.consts.find? path | throw s!"`{showPath path}` is not an integer"
    return v

/-- Lowers the pattern `p` of a value of type `t`: the pattern, and its
binders with their types. An identifier of one segment, not applied, is a
variant if it resolves to one, as the elaborator decides with the
variables that shadow items: it has accepted the spec, so a variable never
shadows a variant that a pattern names without `!` (`lang::pattern_name`). -/
partial def lowerPattern (t : VTy) (p : Pattern) : L (Pat × List (Name × VTy × Name)) := do
  match p with
  | .wild _ => return (.wild, [])
  | .str _ v => return (.str v, [])
  | .num _ v => return (.int v v, [])
  | .range _ lo hi inclusive =>
    let (l, h) := Fren.Core.rangeInterval (← lo.mapM boundValue) (← hi.mapM boundValue) inclusive
    return (.int l h, [])
  | .variant _ segs args? =>
    if segs.size == 1 && args?.isNone then
      let (n, bang) := Fren.Core.declaredName (Name.mkSimple segs[0]!.name)
      let st ← get
      let variant := st.table.resolvePath st.scope #[Name.mkSimple segs[0]!.name] matches .ok (.variant ..)
      match Fren.Core.patternName (n == `true || n == `false) bang variant with
      | .boolLiteral => return (.bool (n == `true), [])
      | .binder =>
        -- Named apart, so that a definition put under it is never captured.
        let k := (← get).fresh
        modify fun s => { s with fresh := s.fresh + 1 }
        return (.bind (Name.mkNum n k), [(n, t, Name.mkNum n k)])
      | .variant => pure ()
    let .variant en idx ← resolve segs | throw "a pattern names no variant"
    let .data path := t | throw "a variant matches a value that is not an enumeration"
    unless en.path == path do throw s!"the pattern's variant is not of `{showPath path}`"
    let d ← dataDef path
    let tys := d.ctors[idx]!.fields.map (·.2)
    let mut ps := #[]
    let mut bound := []
    for a in args?.getD #[], ta in tys do
      let (q, qb) ← lowerPattern ta a
      ps := ps.push q
      bound := bound ++ qb
    return (.ctor idx ps, bound)
  | .or _ alts => do
    let ps ← alts.mapM fun a => return (← lowerPattern t a).1
    return (.alts ps, [])

/-- The function without parameters that an interpretation gives the
unspecified value of the type `t` by, where no row of a table holds: not a
Fren name, so it is no item's. -/
def unspecifiedFn (t : VTy) : Name := .str .anonymous s!"[][0] : {reprStr t}"

/-- Whether `e` reads an index or a table without a `_` row, whose value
may be unknown without an interpretation. -/
partial def Ex.readsUnspecified : Ex → Bool
  | .index .. | .table _ _ (some _) | .const .. => true
  | .table _ rows none => rows.any fun (_, c?, v) => c?.any (·.readsUnspecified) || v.readsUnspecified
  | .lit _ | .var _ | .slot _ | .bound _ => false
  | .not a | .neg a | .field a _ | .card a | .matches a _ _ | .quant _ _ _ a | .pre _ _ _ a => a.readsUnspecified
  | .bin _ a b | .when _ a b | .pair a b => a.readsUnspecified || b.readsUnspecified
  | .ite c a b => c.readsUnspecified || a.readsUnspecified || b.readsUnspecified
  | .app _ args | .ctor _ _ args | .setLit args | .seqLit args | .cardinality _ args => args.any (·.readsUnspecified)
  | .method _ r args => r.readsUnspecified || args.any (·.readsUnspecified)
  | .update e fs => e.readsUnspecified || fs.any (·.2.readsUnspecified)
  | .match e arms _ _ u => u.isSome || e.readsUnspecified || arms.any fun (_, g?, b) =>
    g?.any (·.readsUnspecified) || b.readsUnspecified

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
      -- Of a newtype, the newtype, which `+` and `-` are erased through.
      | .add, .newtype .., _ | .sub, .newtype .., _ => ta
      | .add, _, _ | .sub, _, _ | .mul, _, _ | .div, _, _ | .mod, _, _ => VTy.int
      | .concat, _, _ => ta
      | .union, _, _ | .inter, _, _ | .minus, _, _ => ta
      | .join, .rel a _, .rel _ c => .rel a c
      | _, _, _ => .bool
    return (.bin o x y, t)
  -- `a < b <= c` is `a < b and b <= c`, with the same `b` in both: an
  -- index in `b` has its goal first where it is unguarded.
  | .chain _ es ops => do
    let xs ← es.mapM fun e => (·.1) <$> lowerExpr cx e
    let links ← (ops.zip (xs.zip (xs.extract 1))).mapM fun ((op, _), x, y) => do
      let some o := Op.ofString? op | throw s!"unknown operator `{op}`"
      return Ex.bin o x y
    return ((links.extract 1).foldl (.bin .and) links[0]!, .bool)
  | .not _ a => do return (.not (← lowerExpr cx a).1, .bool)
  | .neg _ a => do return (.neg (← lowerExpr cx a).1, .int)
  | .num _ v => return (.lit (.int v), .int)
  | .str _ v => return (.lit (.str v), .string)
  | .set _ es => do
    let es ← es.mapM (lowerExpr cx)
    -- `{}` is typed by where it is written, which the evaluator does not need.
    let t : VTy := match (es[0]? : Option (Ex × VTy)) with
      | some (_, .rel a b) => .rel a b
      | some (_, t) => .set t.widen
      | none => .set .bool
    return (.setLit (es.map (·.1)), t)
  | .seq _ es => do
    let es ← es.mapM (lowerExpr cx)
    return (.seqLit (es.map (·.1)), .seq ((es[0]?.map (·.2.widen)).getD .bool))
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
    if let (.matches, #[Ex.lit (.str p)]) := (method, args) then
      if let .ok re := Fren.Core.parseRe p then return (.matches r p re, methodTy method t)
    return (.method method r args, methodTy method t)
  | .bool _ b => return (.lit (.bool b), .bool)
  | .path _ segs => do
    if segs.size == 1 then
      let parts := segs[0]!.name.splitOn "."
      -- A binder shadows the comp's variables; otherwise the longest
      -- prefix that is a variable, then fields.
      if let some (_, ty, x) := cx.binders.find? (·.1 == Name.mkSimple parts.head!) then
        return ← readFields (.bound x) ty parts.tail
      if let some (_, d, ty) := cx.lets.find? (·.1 == Name.mkSimple parts.head!) then
        return ← readFields d ty parts.tail
      for k in (List.range parts.length).reverse do
        let n := dotted (parts.take (k + 1))
        if let some v := cx.vars.find? (·.name == n) then
          return ← readFields (.var n) v.ty (parts.drop (k + 1))
      if parts.length > 1 then
        -- A constant, then the fields read from its value, or the methods
        -- without arguments applied to it. The spec has been checked, so
        -- the root is not an instance and nothing shadows it here.
        let st ← get
        let .ok (.item { kind := .constItem, path, .. }) := st.table.resolvePath st.scope #[Name.mkSimple parts.head!]
          | throw s!"`{segs[0]!.name}` names no variable"
        let some (v, t) := st.spec.consts.find? path | throw s!"unknown constant `{showPath path}`"
        return ← readFields v t parts.tail
    match ← resolve segs with
    | .variant en idx => do
      let d ← dataDef en.path
      unless d.ctors[idx]!.fields.isEmpty do throw s!"`{showPath en.path}::{en.variants[idx]!}` needs a payload"
      return (.lit (.ctor en.path idx #[]), .data en.path)
    | .item { kind := .constItem, path, .. } =>
      let some (v, t) := (← get).spec.consts.find? path | throw s!"unknown constant `{showPath path}`"
      return (v, t)
    | r => throw s!"`{showPath r.path}` is not a value"
  | .app _ segs args => do
    let args ← args.mapM fun a => (·.1) <$> lowerExpr cx a
    -- The spec has been checked, so no variable shadows a built-in
    -- function here.
    if let some c := (if segs.size == 1 then Fren.Core.builtinFunction? (.mkSimple segs[0]!.name) else none) then
      return (.cardinality c args, .bool)
    match ← resolve segs with
    | .item { kind := .fnItem, path, .. } =>
      -- With its preconditions at its arguments, if it has any.
      let withPres (x : Ex) : L Ex := do
        let some (ps, pres) := (← get).spec.pres.find? path | return x
        let σ := (ps.zip args).toList
        return .pre segs[0]!.span.start path (pres.map fun (n, g) => (n, g.subst σ)) x
      -- A defined function's body, with its parameters standing for the
      -- arguments.
      if let some (ps, body, r) := (← get).spec.defs.find? path then
        return (← withPres (body.subst (ps.zip args).toList), r)
      let some (_, r) := (← get).spec.funs.find? path | throw s!"unknown function `{showPath path}`"
      return (← withPres (.app path args), r)
    | .variant en idx => return (.ctor en.path idx args, .data en.path)
    -- A newtype, erased to its value.
    | .item { kind := .recordItem, path, .. } => do
      let some u := (← get).spec.newtypes.find? path | throw s!"`{showPath path}` is not a newtype"
      let some a := args[0]? | throw s!"`{showPath path}` needs a value"
      return (a, .newtype path u)
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
  | .update _ base fields => do
    let (r, t) ← lowerExpr cx base
    let .data path := t | throw "an updated value is not a record"
    let d ← dataDef path
    let some c := d.ctors[0]? | throw s!"`{showPath path}` has no constructor"
    -- In the order of the record's fields, as the elaborator reads them.
    let mut vals := #[]
    for (f, _) in c.fields, k in [0:c.fields.size] do
      let some (x, e?) := fields.find? (fun (x, _) => Name.mkSimple x.name == f) | continue
      vals := vals.push (k, (← lowerExpr cx (e?.getD (.path x.span #[x]))).1)
    return (.update r vals, .data path)
  | .field _ e f => do
    let (x, t) ← lowerExpr cx e
    readFields x t [f.name]
  | .match span scrutinee arms => do
    let (s, t) ← lowerExpr cx scrutinee
    let mut out := #[]
    let mut ty := VTy.bool
    for (p, guard?, body) in arms do
      let (pat, bound) ← lowerPattern t p
      let acx := { cx with binders := bound.reverse ++ cx.binders, lets := cx.lets.filter fun (n, _) => !bound.any (·.1 == n) }
      let g? ← guard?.mapM fun g => return (← lowerExpr acx g).1
      let (b, t) ← lowerExpr acx body
      ty := t
      out := out.push (pat, g?, b)
    -- Whether some arm may not be taken, as the elaborator decides it
    -- (`Fren.Core.checkMatch`), which has accepted the spec.
    let st ← get
    let sigs : Fren.Core.Sigs := fun p =>
      ((st.spec.data.find? p).map fun d => d.ctors.map fun c => (c.name, c.fields.map (·.2.patTy))).getD #[]
    let unguardedExhaustive := match Fren.Core.checkMatch sigs t.patTy (out.map (·.1.core)) (out.map (·.2.1.isSome)) with
      | .ok u => u
      | .error _ => true
    let armPos := arms.map (·.1.span.start)
    if unguardedExhaustive then return (.match s out span.start armPos none, ty)
    -- The function of the interpretation for its type's unspecified value.
    let u := unspecifiedFn ty
    modify fun s => { s with spec.funs := s.spec.funs.insert u (#[], ty) }
    return (.match s out span.start armPos (some u), ty)
  | .table span rows => do
    let mut out := #[]
    let mut ty := VTy.bool
    for (start, c?, v) in rows do
      let (x, t) ← lowerExpr cx v
      ty := t
      -- Where the row's question is reported: its condition.
      out := out.push (((c?.map (·.span.start)).getD start.start), ← c?.mapM fun c => return (← lowerExpr cx c).1, x)
    let wild := rows.back?.any (·.2.1.isNone)
    if wild then return (.table span.start out none, ty)
    -- The function of the interpretation for its type's unspecified value.
    let u := unspecifiedFn ty
    modify fun s => { s with spec.funs := s.spec.funs.insert u (#[], ty) }
    return (.table span.start out (some u), ty)
  -- `e is P` is `match e { P => true, _ => false }`.
  | .is _ scrutinee p => do
    let (s, t) ← lowerExpr cx scrutinee
    let (pat, _) ← lowerPattern t p
    return (.match s #[(pat, none, .lit (.bool true)), (.wild, none, .lit (.bool false))] 0 #[] none, .bool)
  | .«let» _ defs body _ => do
    -- Each name stands for its definition, which sees the earlier names.
    let mut cx := cx
    for (x, _, d) in defs do
      let (e, t) ← lowerExpr cx d
      let n := declName x
      cx := { cx with lets := (n, e, t) :: cx.lets, binders := cx.binders.filter (·.1 != n) }
    lowerExpr cx body
  | .quant _ all bs body => do
    -- Each bound name with its type and a name made unique, as a
    -- pattern's binder's is.
    let mut bound := #[]
    for b in bs do
      let t ← lowerTy b.ty
      for x in b.names do
        let k := (← get).fresh
        modify fun s => { s with fresh := s.fresh + 1 }
        bound := bound.push (declName x, t, Name.mkNum (declName x) k)
    let sp := (← get).spec
    -- Every combination of the names' values, the last fastest.
    let insts := bound.foldl (fun acc (_, t, _) => acc.flatMap fun pre => (sp.values t).map pre.push) #[#[]]
    -- A bound name hides a name of an enclosing `let` or `where`.
    let names := bound.map (·.1)
    let (b, _) ← lowerExpr { cx with binders := bound.toList.reverse ++ cx.binders,
                                     lets := cx.lets.filter (!names.contains ·.1) } body
    return (.quant all (bound.map (·.2.2)) insts b, .bool)
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
    vars := vars.push { name := declName x, ty := ← varTy ty?, role := if isIn then .input else .output, isPub, isDet }
  let mut pending := #[]
  for m in members do
    let .inst x p bs := m | continue
    let cpath ← match ← resolve p with
      | .item { kind := .compItem, path, .. } => pure path
      | r => throw s!"`{showPath r.path}` is not a component"
    pending := pending.push (declName x, cpath, bs)
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
    defs := defs.push (declName x, (← lowerExpr cx e).1)
  let c : Comp := { path, vars, constraints, insts, defs }
  modify fun s => { s with
    table := s.table.addItem { kind := .compItem, path, isPub, owner := s.module }
    scope := s.module
    spec.comps := s.spec.comps.push c }

/-- Records the body or value `e` of the function or constant `n`, over the
inputs `vars`, as a comp for the checks of its tables and of the
applications in it and in the function's contract (`Spec.bodies`). Each is
recorded, since an application's question is the elaborator's alone. -/
def noteBody (n : Name) (vars : Array Var) (e : Ex) (constraints : Array Constraint := #[]) : L Unit := do
  modify fun s => { s with
    spec.bodies := s.spec.bodies.push { path := s.module, vars, constraints, insts := #[], body? := some (n, e) } }

/-- The clauses of the contract of the function `n` at `path`, whose
parameters are `ps`: records them for the function's applications, and,
for an uninterpreted function with postconditions, for a random
interpretation, which meets them. Gives them over the parameters as the
inputs `vars`, as the constraints of the function's body, named after the
function and the clause: the preconditions, and the postconditions if the
function is `defined` (`Reqs/Eval#confirming-models`). -/
def lowerContract (path n : Name) (defined : Bool) (ps : Array (Name × VTy)) (vars : Array Var)
    (clauses : Array (Bool × Ident × Expr)) : L (Array Constraint) := do
  let cx : Cx := { binders := ps.toList.reverse.map fun (x, t) => (x, t, x) }
  let mut pres := #[]
  let mut posts := #[]
  let mut constraints := #[]
  for (post, x, e) in clauses do
    let cn := Name.mkSimple x.name
    let bound := (← lowerExpr cx e).1
    if post then posts := posts.push bound else pres := pres.push (cn, bound)
    if defined || !post then
      let c := (← lowerExpr { vars } e).1
      constraints := constraints.push { kind := (if post then .ensure else .assume), name := n ++ cn, e := c }
  unless pres.isEmpty do
    let entry := (ps.map (path ++ ·.1), pres.map fun (cn, g) => (cn, g.renameBound (path ++ ·)))
    modify fun s => { s with spec.pres := s.spec.pres.insert path entry }
  unless defined || posts.isEmpty do
    modify fun s => { s with spec.contracts := s.spec.contracts.insert path (ps.map (·.1), pres.map (·.2), posts) }
  return constraints

/-- The path of the component that `segs` names. -/
def resolveComp (segs : Array Ident) : L Name := do
  match ← resolve segs with
  | .item { kind := .compItem, path, .. } => pure path
  | r => throw s!"`{showPath r.path}` is not a component"

def lowerGlobal (name : Ident) (binders : Array Binder) (body : Expr) : L Unit := do
  let mut insts := #[]
  -- The binders over values, a quantifier around the body (`lang::quantifier_binder`).
  let mut values := #[]
  for b in binders do
    let st ← get
    match st.table.resolvePath st.scope (segNames b.ty) with
    | .ok (.item { kind := .compItem, path, .. }) =>
      for x in b.names do insts := insts.push { name := declName x, comp := path, bindings := #[] }
    | _ => values := values.push b
  let st ← get
  let shell : Comp := { path := st.module, vars := #[], constraints := #[], insts, isGlobal := true }
  let n := Name.mkSimple name.name
  let body := if values.isEmpty then body else .quant body.span true values body
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
  | .enum isPub name variants _ => do
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
  | .newtype isPub name fields => do
    let path := (← get).module ++ Name.mkSimple name.name
    let some ty := fields[0]? | throw s!"`{showPath path}` has no field"
    let u ← lowerTy ty
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      spec.newtypes := s.spec.newtypes.insert path u }
  | .abstractType isPub name => do
    let path := (← get).module ++ Name.mkSimple name.name
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
      spec.sorts := s.spec.sorts.push path }
  | .function isPub name params result body clauses _ => do
    let path := (← get).module ++ Name.mkSimple name.name
    let r ← varTy result
    let contract := !clauses.isEmpty
    match body with
    | none =>
      if !contract then
        let ps ← params.mapM (lowerTy ·.1)
        modify fun s => { s with spec.funs := s.spec.funs.insert path (ps, r) }
      else
        let ps ← params.mapM fun (p, ty?) => return (declName p[0]!, ← varTy ty?)
        modify fun s => { s with
          spec.funs := s.spec.funs.insert path (ps.map (·.2), r)
          table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
        -- Over the parameters as inputs, for the checks of its clauses.
        let vars := ps.map fun (x, t) => ({ name := x, ty := t, role := .input, isPub := true } : Var)
        let cs ← lowerContract path (Name.mkSimple name.name) false ps vars clauses
        noteBody (Name.mkSimple name.name) vars (.lit (.bool true)) cs
    | some body =>
      let ps ← params.mapM fun (p, ty?) => return (declName p[0]!, ← varTy ty?)
      let (b, _) ← lowerExpr { binders := ps.toList.reverse.map fun (n, t) => (n, t, n) } body
      -- Binders named after the function, so that substituting arguments
      -- never captures a binder of theirs: theirs are a comp's or another
      -- function's.
      let b := b.renameBound (path ++ ·)
      modify fun s => { s with spec.defs := s.spec.defs.insert path (ps.map (path ++ ·.1), b, r) }
      -- Over the parameters as inputs, for the checks of its tables, and
      -- its contract's, once it can be applied.
      let vars := ps.map fun (x, t) => ({ name := x, ty := t, role := .input, isPub := true } : Var)
      let e := (← lowerExpr { vars } body).1
      modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
      let cs ← lowerContract path (Name.mkSimple name.name) true ps vars clauses
      noteBody (Name.mkSimple name.name) vars e cs
    modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
  | .const isPub name ty value => do
    let path := (← get).module ++ Name.mkSimple name.name
    let t ← lowerTy ty
    let (e, _) ← lowerExpr {} value
    noteBody (Name.mkSimple name.name) #[] e
    -- Unknown where it reads an index out of range or a table where no
    -- row holds, which only an interpretation gives a value: then it is
    -- the constant, kept as its expression, wherever it is mentioned.
    let v ← match evalClosed e with
      | some v => pure (Ex.lit v)
      | none =>
        unless e.readsUnspecified do throw s!"the value of `{showPath path}` cannot be evaluated"
        pure (.const path e)
    modify fun s => { s with
      table := s.table.addItem { kind := .constItem, path, isPub, owner := s.module }
      spec.consts := s.spec.consts.insert path (v, t) }
  | .comp isPub name members .. => lowerComp isPub name members
  | .global name binders body => lowerGlobal name binders body
  | .refine name concrete abstract bs => do
    let comp (segs : Array Ident) : L Comp := do
      let some c := (← get).spec.comp? (← resolveComp segs) | throw s!"unknown component `{segNames segs}`"
      return c
    let c ← comp concrete
    let a ← comp abstract
    let path := (← get).module ++ Name.mkSimple name.name
    -- The bindings, over `c`'s own variables.
    let bindings ← bs.mapM fun (b, e?) => do
      return (Name.mkSimple b.name, (← lowerExpr { vars := c.vars } (e?.getD (.path b.span #[b]))).1)
    -- As the elaborator builds it (`Reqs/Lang/Refinement`).
    modify fun s => { s with
      table := s.table.addItem { kind := .expectItem, path, isPub := false, owner := s.module }
      spec.comps := s.spec.comps.push (Comp.refinement path (Name.mkSimple c.path.getString!) c a bindings) }
  | .claim .. | .check _ => pure ()
  | .lintSetting _ _ _ _ _ body? => do if let some b := body? then lowerItem b
where
  declareUse (segs : Array Ident) (glob : Bool) : L Unit := declareUseIn segs glob none

/-- The state after the files' items, from the state `st` of the files
before them. Each file starts at the root module. -/
def lowerFrom (st : LState) (files : Array (Array Item)) : Except String LState := do
  let mut st := st
  for items in files do
    st := { st with module := .anonymous, scope := .anonymous }
    for item in items do
      st := (← (lowerItem item).run st).2
  return st

/-- The spec of the files' items, which the elaborator accepted, with the
names it declares. Lowering files one after another is lowering them
together: `lowerFrom st (a ++ b)` is `lowerFrom st a >>= (lowerFrom · b)`,
which `fren mutate` relies on to lower only the files from a mutant's. -/
def lowerAll (files : Array (Array Item)) : Except String LState := lowerFrom {} files

def lowerFiles (files : Array (Array Item)) : Except String Spec := (·.spec) <$> lowerAll files

def VTy.show : VTy → String
  | .bool => "Bool"
  | .int => "Int"
  | .nat => "Nat"
  | .string => "String"
  | .set t => s!"Set({t.show})"
  | .rel a b => s!"Rel({a.show}, {b.show})"
  | .seq t => s!"Seq({t.show})"
  | .data p | .abstract p | .newtype p _ => showPath p

/-- Whether `e` is a `Nat` where one is expected (`lang::literal_type`,
`lang::operator_type`): a literal, a `Nat` constant, or `+`, `*` or a
conditional of those. -/
partial def natTyped (e : Expr) : L Bool := do
  match e with
  | .num .. => return true
  | .bin _ "+" a b | .bin _ "*" a b => return (← natTyped a) && (← natTyped b)
  | .ite _ _ a b => return (← natTyped a) && (← natTyped b)
  | .path .. => return (← lowerExpr {} e).2 == .nat
  | _ => return false

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
  let (((ex, t), nat), _) ← (do return (← lowerExpr {} e, ← natTyped e)).run { st with module }
  -- Typed as at a binding of the type (`lang::widening`): a `Nat` is read
  -- as an `Int`, and a literal as a `Nat`.
  let t := if nat && ty == .nat then .nat else if t == .nat && ty == .int then .int else t
  let a (t : VTy) := if "AEIOU".contains t.show.front then "an" else "a"
  -- `{}` and `[]` have the type they are read at.
  let empty := match ex, ty with
    | .setLit #[], .set _ | .setLit #[], .rel .. | .seqLit #[], .seq _ => true
    | _, _ => false
  unless t == ty || empty do throw s!"`{text}` is {a t} `{t.show}`, not {a ty} `{ty.show}`"
  let some v := evalClosed ex | throw s!"`{text}` is not a value"
  return v

end FrenCli.Eval
