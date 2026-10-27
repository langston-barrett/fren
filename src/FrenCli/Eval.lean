-- keep-sorted start
import Fren.Seq
import FrenCli.Guard
import FrenCli.Parse
import FrenCore.Names
import FrenCore.PatternTypes
import FrenCore.Patterns
import FrenCore.Regex
import FrenCore.Table
import FrenCore.TypeFacts
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
  /-- An enumeration or a record, with its type arguments if it is generic,
  or none if a construction's are not known here. -/
  | data (path : Name) (args : List VTy)
  | abstract (path : Name)
  /-- A newtype, whose values are its underlying type's, `under`
  (`Reqs/Lang/Items#newtypes`): only how they are shown differs. -/
  | newtype (path : Name) (under : VTy)
  /-- The `k`th type parameter, within a generic type's declaration. -/
  | param (k : Nat)
  deriving Inhabited, BEq, Hashable, Repr

/-- `t`, with the `k`th of `args` for each type parameter `k`
(`lang::instantiation`). A parameter without one stays. -/
partial def VTy.subst (args : List VTy) : VTy → VTy
  | .param k => args[k]?.getD (.param k)
  | .set t => .set (t.subst args)
  | .rel a b => .rel (a.subst args) (b.subst args)
  | .seq t => .seq (t.subst args)
  | .data p as => .data p (as.map (·.subst args))
  | t => t

/-- What matching the type `found` against `decl` gives the abstract types
of `decl` that a generic function's type parameters are
(`Fren.Core.typeParamName?`): each with its argument. -/
partial def VTy.matchAbstract (decl found : VTy) : List (Name × VTy) :=
  match decl, found with
  | .abstract p, f => if (Fren.Core.typeParamName? p).isSome then [(p, f)] else []
  | .set d, .set f | .seq d, .seq f => d.matchAbstract f
  | .rel a b, .rel c d => a.matchAbstract c ++ b.matchAbstract d
  | .data _ ds, .data _ fs => (ds.zip fs).flatMap fun (d, f) => d.matchAbstract f
  | _, _ => []

/-- `t`, with each abstract type of `σ` its argument. -/
partial def VTy.substAbstract (σ : List (Name × VTy)) : VTy → VTy
  | .abstract p => (σ.lookup p).getD (.abstract p)
  | .set t => .set (t.substAbstract σ)
  | .rel a b => .rel (a.substAbstract σ) (b.substAbstract σ)
  | .seq t => .seq (t.substAbstract σ)
  | .data p as => .data p (as.map (·.substAbstract σ))
  | t => t

/-- What matching the type `f` of an argument against the declared type `d`
gives the type parameter `k`, as `Fren.Core.matchParam` matches them. -/
partial def VTy.matchParam (k : Nat) : VTy → VTy → Option VTy
  | .param j, f => if j == k then some f else none
  | .set d, .set f | .seq d, .seq f => d.matchParam k f
  | .rel a b, .rel c e => a.matchParam k c <|> b.matchParam k e
  | .data p ds, .data q fs => if p == q then (ds.zip fs).findSome? fun (d, f) => d.matchParam k f else none
  | _, _ => none

/-- `t`, with the type parameter `k` for each abstract type that is the
`k`th type parameter of the generic function at `fn`
(`Fren.Core.typeParamPath`), as `Fren.Core.Ty.asParams` has it. -/
partial def VTy.asParams (fn : Name) (tps : Array Name) : VTy → VTy
  | .abstract p => match (List.range tps.size).find? fun k => Fren.Core.typeParamPath fn k tps[k]! == p with
    | some k => .param k
    | none => .abstract p
  | .set t => .set (t.asParams fn tps)
  | .rel a b => .rel (a.asParams fn tps) (b.asParams fn tps)
  | .seq t => .seq (t.asParams fn tps)
  | .data p as => .data p (as.map (·.asParams fn tps))
  | t => t

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

/-- The type of a construction of the variant or record `idx` of `d` from
values of the types `tys`: with the type arguments that matching them
against the declared types gives (`VTy.matchParam`), as the elaborator
infers them from values that synthesize their types, or with none if
some type parameter has none. -/
def DataDef.constructed (d : DataDef) (idx : Nat) (tys : Array VTy) : VTy :=
  let rec params : VTy → Nat
    | .param k => k + 1
    | .set t | .seq t => params t
    | .rel a b => max (params a) (params b)
    | .data _ as => as.foldl (fun n a => max n (params a)) 0
    | _ => 0
  let n := d.ctors.foldl (fun n c => c.fields.foldl (fun n (_, t) => max n (params t)) n) 0
  let fields := ((d.ctors[idx]?.map (·.fields)).getD #[]).map (·.2)
  match (List.range n).mapM fun k => (fields.zip tys).findSome? fun (f, t) => f.matchParam k t with
  | some args => .data d.path (args.map VTy.widen)
  | none => .data d.path []

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
partial def VTy.patTy : VTy → Fren.Core.PatTy
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .data p as => .enum p (as.map VTy.patTy)
  | .param k => .param k
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
  /-- A variable of the procedure, such as `x` or `w.x`. -/
  | var (n : Name)
  /-- A variable of a search, by its index in the search's environment
  (`Problem.solve`), which reads it without looking up its name. -/
  | slot (k : Nat)
  /-- A binder of an enclosing `match` arm or quantifier, by its name. -/
  | bound (n : Name)
  /-- A binder of an enclosing `match` arm or quantifier, by its position:
  the `k`th binding from the innermost, as `Ex.compile` resolves `.bound`.
  It reads the binding without looking up its name. -/
  | boundAt (k : Nat)
  /-- The `k`th of the expressions shared by the innermost enclosing
  `memo` (`Ex.compile`). -/
  | shared (k : Nat)
  /-- `e`, in which `.shared` reads the value of each of `lets`, which is
  evaluated once, when it is first read (`Ex.compile`). -/
  | memo (lets : Array Ex) (e : Ex)
  /-- A value known before evaluation, which it is, with nothing to
  allocate (`Ex.compile`). -/
  | known (v : Option Val)
  /-- `q`, a quantifier, in whose body `.shared` reads the value of each
  of `lets[k]`, which reads only the bound names before the `k`th, each
  evaluated once for each of their values, when first read
  (`Ex.compile`). -/
  | lifted (lets : Array (Array Ex)) (q : Ex)
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
    (pairs? : Option (Array (Nat × Nat)))
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
  /-- `forall`, or `exists` if not `all`, written at the source position
  `pos` of the file `file`, over the bound names `names`, each with its domain, which lists the
  values that it takes given those of the names before it, as a sequence or
  a set, or `none` if it has none, and its declared type, whose values those
  are: its body at each combination of their values
  (`Reqs/Eval#quantifiers`). A bound name of a listed type has every value
  of its type as its domain (`Reqs/Lang/Quantifiers#meaning`). -/
  | quant (file pos : Nat) (all : Bool) (names : Array Name) (doms : Array (Option Ex)) (tys : Array Fren.Core.PTy)
      (body : Ex)
  /-- The integers from `lo` up to `hi`, but not `hi`, as a sequence, if
  there are at most `maxEnumerated` of them (`Reqs/Eval#quantifiers`). -/
  | range (lo hi : Ex)
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
  /-- That `e` is a value of the declared type `t`: what its pattern
  types, and those within it, say of it (`Reqs/Lang/Types#meaning`). -/
  | typed (t : Fren.Core.PTy) (ints : Array Int) (e : Ex)
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
  /-- For what a variable's type brings, rather than a constraint of the
  spec: that type, as written (`Reqs/Lang/Procedures#pattern-types`). -/
  typed? : Option String := none
  deriving Inhabited

structure Inst where
  name : Name
  comp : Name
  /-- Each parameter of `comp`, with its argument; empty for a
  binder of a global expectation. -/
  bindings : Array (Name × Ex)
  deriving Inhabited

/-- A procedure, or a global expectation: a procedure whose path is its module, with
a call per binder and the expectation as its only constraint. -/
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
  procedure with the expression it is bound to, which reads the concrete
  procedure's variables. The definedness of their indexes is checked. -/
  bindings : Array (Name × Ex) := #[]
  /-- For the body of a defined function or the value of a constant, as a
  procedure for the checks of its tables, the function or constant, and its body
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
  tables, each as a procedure (`Comp.body?`). -/
  bodies : Array Comp := #[]
  /-- The fields of each record and newtype, and the payloads of each
  enumeration, as declared (`Fren.Core.DataShape`). -/
  shapes : NameMap Fren.Core.DataShape := {}
  /-- The result type of each uninterpreted function, as declared. -/
  results : NameMap Fren.Core.PTy := {}
  /-- Each generic function without a body, in declaration order: its type
  parameters, and its parameters' and result's types, which mention them as
  `VTy.param` (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
  Each instance that an application uses is a function of its own in
  `funs`, named after the function and its type arguments, as the solver
  names it (`Fren.Core.instanceText`). -/
  generics : Array (Name × Array Name × Array VTy × VTy) := #[]
  /-- The generic function of each such instance, whose `results` and
  `contracts` are the instance's. -/
  instanceOf : NameMap Name := {}
  deriving Inhabited

def Spec.comp? (sp : Spec) (path : Name) : Option Comp := sp.comps.find? (·.path == path)

/-- Every value of `t`, a type that a quantifier ranges over
(`lang::quantified_type`), in the order of a quantifier's instances
(`Reqs/Lang/Quantifiers#meaning`). The elaborator has rejected any other
type, such as a recursive enumeration. -/
partial def Spec.values (sp : Spec) : VTy → Array Val
  | .bool => #[.bool true, .bool false]
  | .data p args => match sp.data.find? p with
    | some d => (d.ctors.mapIdx fun idx c =>
        (c.fields.foldl (fun acc (_, t) => acc.flatMap fun pre => (sp.values (t.subst args)).map pre.push) #[#[]]).map (.ctor p idx ·)).flatten
    | none => #[]
  -- A newtype's values are its underlying type's, as `Spec.ofPVal` has them.
  | .newtype _ u => sp.values u
  | _ => #[]

/-- Every variable of `c`: its own, then each call's, named `w.x`, in
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
  /-- The parts of each record, newtype and enumeration, as declared, for
  `Ex.typed` (`Spec.shapes`). -/
  shapes : Name → Option Fren.Core.DataShape := fun _ => none

instance : Inhabited Interp := ⟨{}⟩

/-- The value of each variable, as far as it is known. -/
abbrev Look := Name → Option Val

/-- The most values that the evaluator enumerates of a range
(`eval::MAX_ENUMERATED`). -/
def maxEnumerated : Int := 1024

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
fills that do not fit. A group is laid out on one line when that line has
no newline and is at most 120 characters long (`Std.Format.pushGroup`).
When the whole text fits, every group within it does, so `reprStr v` is
that line, which is `Val.reprFlat`. Its length in bytes bounds its length
in characters, so a text of at most 100 bytes is short enough, and so is
one of at most 120 characters. Any other text, or one with a newline, is
printed by `reprStr` itself. Either way the key is `reprStr v`, so the
order of members is unchanged. -/
def Val.setKey (v : Val) : String :=
  let flat := v.reprFlat "" false
  if flat.utf8ByteSize ≤ 100 || (flat.length ≤ 120 && !flat.contains '\n') then flat else reprStr v

/-- A set of `vs`: sorted by how they print (`Val.setKey`), so that equal
sets are equal values. Each member is printed once, not at each
comparison. -/
def Val.setOf (vs : Array Val) : Val :=
  -- Without repeats already.
  if vs.size ≤ 1 then .set vs else
  let ms := vs.toList.eraseDups.toArray
  if ms.size ≤ 1 then .set ms else
    .set ((ms.map fun v => (v.setKey, v)).qsort (·.1 < ·.1) |>.map (·.2))

/-- `Val.setOf` of the values of `kvs`, each with its key (`Val.setKey`),
computed when first needed, so that values that are members of many sets
are printed once: the same members, without repeats, the first of each
kept, and sorted by the same keys in the same way. -/
def Val.setOfKeyed (kvs : Array (Thunk String × Val)) : Val :=
  let ms := kvs.foldl (init := #[]) fun (ms : Array (Thunk String × Val)) kv =>
    if ms.any (·.2 == kv.2) then ms else ms.push kv
  if ms.size ≤ 1 then .set (ms.map (·.2)) else
    .set ((ms.map fun (k, v) => (k.get, v)).qsort (·.1 < ·.1) |>.map (·.2))

@[inline] def setOp (f : Array Val → Array Val → Val) : Option Val → Option Val → Option Val
  | some (.set a), some (.set b) => some (f a b)
  | _, _ => none

/-- How two values of one ordered type compare
(`Reqs/Lang/Items#ordered-declarations`): `Int`s and `String`s by their own
orders, and values of an ordered enumeration or record by their
constructors' positions, then by their payloads or fields, in order,
lexicographically. A newtype's value is its underlying type's. -/
partial def cmpV : Val → Val → Option Ordering
  | .int x, .int y => some (compare x y)
  | .str x, .str y => some (compare x.toList y.toList)
  | .ctor t i xs, .ctor u j ys => do
    unless t == u && xs.size == ys.size do none
    if i != j then return compare i j
    -- Lexicographically, by the payloads or fields in order
    -- (`Fren.Core.lexCompare`).
    return Fren.Core.lexCompare (← (xs.zip ys).toList.mapM fun (x, y) => cmpV x y)
  | _, _ => none

/-- An ordering, of values of an ordered type (`cmpV`). -/
@[inline] def ordV (f : Ordering → Bool) : Option Val → Option Val → Option Val
  | some x, some y => (cmpV x y).bind (boolV ∘ f)
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

/-- Whether the pattern `p` matches the value `v`. -/
partial def patHolds : Fren.Core.Pat → Val → Bool
  | .wild _, _ => true
  | .bool b, .bool c => b == c
  | .int lo hi, .int i => Fren.Core.intervalHolds lo hi i
  | .str s, .str t => s == t
  | .ctor i ps, .ctor _ j vs => i == j && ps.size == vs.size && (ps.zip vs).all fun (p, w) => patHolds p w
  | .or ps, v => ps.any (patHolds · v)
  | _, _ => false

/-- Whether `v` is a value of the declared type `t`, where `shapes` gives
the records', newtypes' and enumerations' parts: it matches the pattern
of `t`, and so does each of its fields, payloads and elements, however
deep, and each `Nat` within it is at least 0. A value is finite, so this
reads all of it, a recursive enumeration's too, which the solver states
only of what a query reads (`Fren.Core.PTy.cons`). -/
partial def typeHolds (shapes : Name → Option Fren.Core.DataShape) (t : Fren.Core.PTy) (v : Val) : Bool :=
  t.pat?.all (patHolds · v) && match t.ty, v with
    | .nat, .int i => 0 ≤ i
    | .set _, .set ms | .seq _, .seq ms => (t.elems[0]?).all fun e => ms.all (typeHolds shapes e)
    | .rel .., .set ms => ms.all fun
      | .pair a b => (t.elems[0]?).all (typeHolds shapes · a) && (t.elems[1]?).all (typeHolds shapes · b)
      | _ => true
    -- A newtype's value is its underlying type's.
    | .newtype p _, v => ((shapes p).bind (·.parts[0]?) |>.bind (·[0]?)).all (typeHolds shapes · v)
    -- Without a payload there is nothing to check, nor to look up.
    | .record p _, .ctor _ idx args | .enum p _, .ctor _ idx args => args.isEmpty ||
      ((shapes p).bind (·.inst t.parts |>.parts[idx]?)).all fun ts => (ts.zip args).all fun (u, w) => typeHolds shapes u w
    | _, _ => true

/-- `Fren.Core.firstCase xs.toList take`, the case of `xs` that is taken,
read from the array, from case `i` (`firstCaseIn_eq`): `take` of each
case in turn, until one is taken or whether one is is unknown. -/
@[specialize] def firstCaseIn (xs : Array α) (take : α → Option (Option β)) (i : Nat := 0) : Option (Option β) :=
  if h : i < xs.size then
    match take xs[i] with
    | none => none
    | some none => firstCaseIn xs take (i + 1)
    | some (some r) => some (some r)
  else some none
termination_by xs.size - i

theorem firstCaseIn_eq (xs : Array α) (take : α → Option (Option β)) (i : Nat) :
    firstCaseIn xs take i = Fren.Core.firstCase (xs.toList.drop i) take := by
  induction i using firstCaseIn.induct xs take with
  | case1 i h hn =>
    rw [firstCaseIn, dif_pos h, List.drop_eq_getElem_cons (by simpa using h)]
    simp [Fren.Core.firstCase, hn]
  | case2 i h hn ih =>
    rw [firstCaseIn, dif_pos h, List.drop_eq_getElem_cons (by simpa using h)]
    simp [Fren.Core.firstCase, hn, ih]
  | case3 i h r hn =>
    rw [firstCaseIn, dif_pos h, List.drop_eq_getElem_cons (by simpa using h)]
    simp [Fren.Core.firstCase, hn]
  | case4 i h =>
    rw [firstCaseIn, dif_neg h, List.drop_eq_nil_of_le (by simpa using h)]
    rfl

/-- A binding of a binder of a `match` arm or a quantifier, in the frame
that `Ex.eval` keeps of them, the innermost last. -/
abbrev Binding := Name × Option Val

/-- The value of an expression, as far as it is known: each variable as
`look` gives it, each binder of an enclosing `match` arm or quantifier as
its binding in `frame` does, the innermost first, and else as `locals`
does, and each `slot k` as `slots[k]` does. `memos` is the shared
expressions of the enclosing `memo`s, the innermost last. Its arguments
are borrowed (`@&`), so that a call, at each node, neither counts nor
uncounts a reference to them.

Looked up by its name, a binder has the value of its innermost binding,
which is what it had when each binding was put in front of `locals`: a
quantifier binds each of its names in turn, and a `match` arm the binders
of its pattern, the first innermost, as `new ++ locals` puts them. -/
partial def Ex.eval (I : @& Interp) (look : @& Look) (locals : @& List (Name × Val) := [])
    (slots : @& Array (Option Val) := #[]) (frame : @& Array Binding := #[])
    (memos : @& Array (Thunk (Option Val)) := #[]) (e : @& Ex) : Option Val :=
  match e with
  | .lit v => some v
  | .var n => look n
  | .slot k => if h : k < slots.size then slots[k] else none
  | .bound n => match frame.findRev? (·.1 == n) with
    | some (_, v) => v
    | none => locals.lookup n
  | .boundAt k => if k < frame.size then frame[frame.size - 1 - k]!.2 else none
  | .shared k => if k < memos.size then memos[memos.size - 1 - k]!.get else none
  | .known v => v
  | .memo lets e =>
    -- The first of `lets` innermost, as `.shared 0`.
    let ms := lets.foldr (init := memos) fun x ms => ms.push (Thunk.mk fun _ => x.eval I look locals slots frame memos)
    e.eval I look locals slots frame ms
  | .not a => notV (a.eval I look locals slots frame memos)
  | .neg a => match a.eval I look locals slots frame memos with
    | some (.int x) => some (.int (-x))
    | _ => none
  -- Membership in a set literal, without building the set, which does
  -- not change which values are members.
  | .bin .member a (.setLit es) => do
    let x ← a.eval I look locals slots frame memos
    boolV ((← es.mapM (·.eval I look locals slots frame memos)).contains x)
  -- `and`, `or` and `when` evaluate their second operand only when the
  -- first does not decide them, which gives the same value: `kleeneAnd`
  -- is `false` whatever its second operand when its first is `false`, and
  -- `kleeneOr` likewise `true`. Evaluation has no other effect.
  | .bin .and a b => match a.eval I look locals slots frame memos with
    | some (.bool false) => some (.bool false)
    | x => kleeneAnd x (b.eval I look locals slots frame memos)
  | .bin .or a b => match a.eval I look locals slots frame memos with
    | some (.bool true) => some (.bool true)
    | x => kleeneOr x (b.eval I look locals slots frame memos)
  | .bin op a b => binV op (a.eval I look locals slots frame memos) (b.eval I look locals slots frame memos)
  | .when negated c d =>
    let c := c.eval I look locals slots frame memos
    match notV (if negated then notV c else c) with
    | some (.bool true) => some (.bool true)
    | x => kleeneOr x (d.eval I look locals slots frame memos)
  | .ite c a b => match c.eval I look locals slots frame memos with
    | some (.bool true) => a.eval I look locals slots frame memos
    | some (.bool false) => b.eval I look locals slots frame memos
    | _ =>
      let x := a.eval I look locals slots frame memos
      if x.isSome && x == b.eval I look locals slots frame memos then x else none
  | .app f args => do I.fn f (← args.mapM (·.eval I look locals slots frame memos))
  | .pre _ _ _ e => e.eval I look locals slots frame memos
  -- Known once the unknown arguments cannot change it: with two `true`,
  -- whatever the rest are.
  | .cardinality c args =>
    let vs := args.map (·.eval I look locals slots frame memos)
    let trues := (vs.filter (· == some (.bool true))).size
    let unknown := (vs.filter fun v => !(v matches some (.bool _))).size
    if unknown == 0 || trues ≥ 2 then some (.bool (c.holds trues))
    else if c == .atMostOne && trues + unknown ≤ 1 then some (.bool true)
    else none
  | .method m recv args => do
    let r ← recv.eval I look locals slots frame memos
    let args ← args.mapM (·.eval I look locals slots frame memos)
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
    -- `min` and `max` of an ordered enumeration's, record's or `String`'s
    -- value, by their order (`cmpV`).
    if r matches .ctor .. || m == .min || m == .max then
      return ← match m, (args[0]? : Option Val) with
        | .min, some y => (cmpV r y).map fun c => if c != .gt then r else y
        | .max, some y => (cmpV r y).map fun c => if c != .lt then r else y
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
    let .str s ← recv.eval I look locals slots frame memos | none
    -- `re` is `p`'s parse, so a remembered answer is `re`'s.
    match I.matchMemo p s with
    | some b => boolV b
    | none => boolV (re.matches s)
  | .pair a b => do return .pair (← a.eval I look locals slots frame memos) (← b.eval I look locals slots frame memos)
  | .seqLit es => do return .seq (← es.mapM (·.eval I look locals slots frame memos))
  -- Out of range, an index is part of the interpretation, which is unknown.
  | .index q i _ => do
    let .seq es ← q.eval I look locals slots frame memos | none
    let .int k ← i.eval I look locals slots frame memos | none
    if 0 ≤ k && k < es.size then es[k.toNat]? else none
  | .ctor ty idx args => do return .ctor ty idx (← args.mapM (·.eval I look locals slots frame memos))
  | .setLit es => do return Val.setOf (← es.mapM (·.eval I look locals slots frame memos))
  | .card s => do
    let .set ms ← s.eval I look locals slots frame memos | none
    return .int ms.size
  | .field e idx => match e.eval I look locals slots frame memos with
    | some (.ctor _ _ vs) => vs[idx]?
    | _ => none
  | .update e fs => do
    let .ctor ty idx vs ← e.eval I look locals slots frame memos | none
    let mut vs := vs
    for (k, x) in fs do vs := vs.set! k (← x.eval I look locals slots frame memos)
    return .ctor ty idx vs
  -- The first row whose condition holds; where none does, the
  -- interpretation's unspecified value of its type.
  -- As the arms `_ if C => v` and `_ => v` (`Fren.Core.firstCase`).
  | .table _ rows unspec? => do
    let taken? ← firstCaseIn rows fun (_, c?, v) => match c? with
      | none => some (some v)
      | some c => match c.eval I look locals slots frame memos with
        | some (.bool true) => some (some v)
        | some (.bool false) => some none
        | _ => none
    match taken? with
    | some v => v.eval I look locals slots frame memos
    | none => I.fn (← unspec?) #[]
  -- A closed expression, which neither variables nor binders reach.
  | .const _ e => e.eval I (fun _ => none)
  | .typed t _ e => return .bool (typeHolds I.shapes t (← e.eval I look locals slots frame memos))
  -- The first arm whose pattern matches and whose guard holds; where none
  -- is taken, the interpretation's unspecified value of its type.
  -- The first arm that is taken: whose pattern matches and whose guard
  -- holds (`Fren.Core.firstCase`, `lang::guarded_match`).
  | .match e arms _ _ unspec? _ => do
    let v ← e.eval I look locals slots frame memos
    let taken? ← firstCaseIn arms fun (p, g?, body) => match p.matchVal v with
      | none => some none
      | some new =>
        -- The binders in the frame, the first innermost.
        let fr := new.foldr (init := frame) fun (n, v) fr => fr.push (n, some v)
        match g? with
        | none => some (some (fr, body))
        | some g => match g.eval I look locals slots fr memos with
          | some (.bool true) => some (some (fr, body))
          | some (.bool false) => some none
          | _ => none
    match taken? with
    | some (fr, body) => body.eval I look locals slots fr memos
    | none => I.fn (← unspec?) #[]
  | .range lo hi => do
    let .int a ← lo.eval I look locals slots frame memos | none
    let .int b ← hi.eval I look locals slots frame memos | none
    if b - a > maxEnumerated then none
    return .seq ((Array.range (b - a).toNat).map fun (k : Nat) => Val.int (a + k))
  -- The conjunction or disjunction of its instances, decided when one
  -- instance decides it: the body at each combination of the values of its
  -- bound names' domains, of their types.
  | .quant _ _ all names doms tys body => quantV I look locals slots all names doms tys body #[] 0 frame memos
  | .lifted lets q => match q with
    | .quant _ _ all names doms tys body => quantV I look locals slots all names doms tys body lets 0 frame memos
    | q => q.eval I look locals slots frame memos
where
  /-- A quantifier's value, from its `k`th bound name, with those before it
  in `frame`: the conjunction or disjunction of the instances at each of
  the `k`th's values, of its type, given which the next are bound, and
  `lets[k]` shared from where the `k`th is bound (`.lifted`). -/
  quantV (I : @& Interp) (look : @& Look) (locals : @& List (Name × Val)) (slots : @& Array (Option Val))
      (all : Bool) (names : @& Array Name) (doms : @& Array (Option Ex)) (tys : @& Array Fren.Core.PTy) (body : @& Ex)
      (lets : @& Array (Array Ex)) (k : Nat) (frame : Array Binding) (memos : Array (Thunk (Option Val))) :
      Option Val :=
    let memos := match lets[k]? with
      | some ls => ls.foldl (init := memos) fun ms x => ms.push (Thunk.mk fun _ => x.eval I look locals slots frame memos)
      | none => memos
    if h : k < names.size then
      match doms[k]?.bind id |>.bind (·.eval I look locals slots frame memos) with
      | some (.seq vs) | some (.set vs) => Id.run do
        -- Once an instance decides it, the rest would leave it as it is,
        -- so they are not looked at.
        let mut acc : Option Val := some (.bool all)
        for v in vs do
          if (match acc with | some (.bool b) => b != all | _ => false) then break
          if tys[k]?.all (typeHolds I.shapes · v) then
            let x := quantV I look locals slots all names doms tys body lets (k + 1) (frame.push (names[k], some v)) memos
            acc := if all then kleeneAnd acc x else kleeneOr acc x
        return acc
      | _ => none
    else body.eval I look locals slots frame memos

/-- The expressions directly within `e`. -/
def Ex.children : Ex → Array Ex
  | .lit _ | .var _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => #[]
  | .memo lets e => lets.push e
  | .lifted lets q => lets.flatten.push q
  | .not a | .neg a | .field a _ | .card a | .matches a _ _ | .const _ a | .typed _ _ a => #[a]
  | .bin _ a b | .when _ a b | .pair a b | .index a b _ | .range a b => #[a, b]
  | .ite c a b => #[c, a, b]
  | .app _ args | .cardinality _ args | .ctor _ _ args | .setLit args | .seqLit args => args
  | .method _ r args => #[r] ++ args
  | .update e fs => #[e] ++ fs.map (·.2)
  | .match e arms .. => arms.foldl (init := #[e]) fun acc (_, g?, b) => acc ++ g?.toArray ++ #[b]
  | .quant _ _ _ _ ds _ b => (ds.filterMap id).push b
  | .table _ rows _ => rows.flatMap fun (_, c?, v) => c?.toArray.push v
  | .pre _ _ gs e => (gs.map (·.2)).push e

/-- Whether `e` has an unbounded quantifier: one with a bound name whose
domain is not its type's listed values. -/
partial def Ex.unbounded (e : Ex) : Bool :=
  match e with
  | .quant _ _ _ _ ds _ b => ds.any (fun | some (.lit _) => false | _ => true) || b.unbounded
  | _ => e.children.any (·.unbounded)

/-- Where `e` has a quantifier with a bound name without a domain, which the
evaluator cannot evaluate (`Reqs/Eval#quantifiers`): its file and position. -/
partial def Ex.undomained? (e : Ex) : Option (Nat × Nat) :=
  match e with
  | .quant file pos _ _ ds _ _ => if ds.any Option.isNone then some (file, pos) else e.children.findSome? (·.undomained?)
  | _ => e.children.findSome? (·.undomained?)

/-- Where what testing `c` evaluates has a quantifier that the evaluator
cannot evaluate (`Reqs/Eval#quantifiers`): its constraints, definitions and
bindings, its calls' bindings and procedures, and so the bodies of the
defined functions and values of the constants that they apply, which are
part of them. -/
partial def Spec.untestable? (sp : Spec) (c : Comp) (seen : List Name := []) : Option (Nat × Nat) :=
  c.constraints.findSome? (·.e.undomained?)
    <|> c.defs.findSome? (·.2.undomained?)
    <|> c.bindings.findSome? (·.2.undomained?)
    <|> c.insts.findSome? fun i => i.bindings.findSome? (·.2.undomained?)
      <|> if seen.contains i.comp then none else (sp.comp? i.comp).bind (sp.untestable? · (i.comp :: seen))

/-- The position of the `match` that a `when` whose condition's pattern
test binds names is lowered to, `match x { P => D, _ => true }`
(`lowerExpr`): no `match` is written there, since it has no arms'
positions, and `Ex.trigger?` reads it as a `when`, which the `is` of a
test (at position 0) and an `if` are not. -/
def whenPos : Nat := 1

/-- The trigger of a constraint (`Reqs/Lang/Procedures#triggers`): the
conditions of its top-level `when`/`unless` chain, conjoined. -/
partial def Ex.trigger? : Ex → Option Ex
  | .when negated c d =>
    let c := if negated then .not c else c
    match d.trigger? with
    | none => some c
    | some t => some (.bin .and c t)
  -- A `when` whose condition's pattern test binds names, as `lowerExpr`
  -- gives it: `match x { P => D, _ => true }`, without the positions of a
  -- written `match`. Its trigger is that `P` matches, and `D`'s, with the
  -- names bound.
  | .match s #[(p, none, d), (.wild, none, .lit (.bool true))] 1 #[] none none =>
    some (.match s #[(p, none, d.trigger?.getD (.lit (.bool true))), (.wild, none, .lit (.bool false))] 0 #[] none none)
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
  | .lit _ | .var _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => #[]
  -- Only evaluation reads what `Ex.compile` gives.
  | .memo _ e | .lifted _ e => go e
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
  | .match s arms pos armPos unspec? pairs? =>
    let tt := Ex.lit (.bool true)
    let others (j : Nat) := (arms.extract 0 j).map fun (p, g?, _) => (p, g?, tt)
    let inGuard (j : Nat) (g : Ex) : Ex := .match s (others j ++ #[(arms[j]!.1, none, g), (.wild, none, tt)]) pos armPos none none
    let inBody (j : Nat) (g : Ex) : Ex :=
      .match s (others j ++ #[(arms[j]!.1, arms[j]!.2.1, g), (.wild, none, tt)]) pos armPos none none
    let inArms := (List.range arms.size).toArray.flatMap fun j =>
      (match arms[j]!.2.1 with | some c => go c (fun g => wrap (inGuard j g)) | none => #[]) ++
        go arms[j]!.2.2 (fun g => wrap (inBody j g))
    -- Where each arm is taken, if no earlier one is: its pattern matches and
    -- its guard holds; `none` for `_` or a binder without a guard.
    let taken := arms.map fun (p, g?, _) => match p, g? with
      | .wild, none | .bind _, none => none
      | _, _ => some (Ex.match s #[(p, none, g?.getD tt), (.wild, none, .lit (.bool false))] pos #[] none none)
    let guarded := arms.map (·.2.1.isSome)
    let orF (cs : Array Ex) : Ex := if cs.isEmpty then .lit (.bool false) else cs.pop.foldr (fun c acc => .bin .or c acc) cs.back!
    -- Completeness is asked exactly where no arm may be taken.
    let split := Fren.Core.splitGoals (if pairs?.isSome then .tableMatch else .match) orF (.bin .and) .not tt taken
      guarded (unspec?.isSome)
    -- Of a table over a scrutinee, the disjointness of the pairs of its
    -- arms that `Fren.Core.tableArmPair` asks about, between completeness
    -- and reachability, as `Fren.Core.tableMatchGoals` orders them. That
    -- the indexes in an arm's guard are in range reads its binders, so it
    -- is put within the arm's own `match`, beside the guard.
    let pairGoals := match pairs? with
      | none => #[]
      | some pairs =>
        let both : Array (Option Ex) := arms.map fun (p, g?, _) =>
          let d := g?.bind fun g =>
            Fren.Core.allOf? (.bin .and) (g.siteGoals.filterMap fun (_, q?, f) => if q?.isNone then some f else none)
          some (Ex.match s #[(p, none, Fren.Core.allOf? (.bin .and) (d.toArray ++ g?.toArray) |>.getD tt),
            (.wild, none, .lit (.bool false))] pos #[] none none)
        Fren.Core.disjointGoals .tableMatch (.bin .and) .not tt both #[] pairs
    let goals := split.filter (·.1 matches .completeness _) ++ pairGoals ++ split.filter (·.1 matches .reachability ..)
    go s ++ inArms ++ goals.map fun (g, f) =>
      ((match g with | .reachability _ j | .disjointness _ _ j => armPos[j]! | _ => pos), some g, wrap f)
  -- In every instance, whatever the quantifier: the instances do not guard
  -- each other.
  | .quant file pos _ names doms tys body => go body (fun g => wrap (.quant file pos true names doms tys g))
  | .range lo hi => go lo ++ go hi
  -- A row's condition is guarded by the earlier rows' not holding, and its
  -- value by its own holding too; then the table's own questions.
  -- A constant's indexes and tables are the constant's.
  | .const .. => #[]
  | .typed _ _ a => go a
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
        | .disjointness _ _ j => starts[j]!
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

/-! ## Compiling constraints

A search evaluates its constraints many times, so it evaluates them as
`Ex.compile` gives them, with the same values (`Ex.eval`), compiled once
for each constraint of the spec (`Spec.withRuns`). -/

/-- Whether two arrays have the same elements, by `same`. -/
@[inline] def sameAll (same : α → α → Bool) (xs ys : Array α) : Bool :=
  xs.size == ys.size && (xs.zip ys).all fun (x, y) => same x y

/-- Whether two options are both `none`, or the same, by `same`. -/
@[inline] def sameOpt (same : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some x, some y => same x y
  | _, _ => false

/-- Whether two patterns are the same. -/
partial def Pat.same : Pat → Pat → Bool
  | .wild, .wild => true
  | .bind n, .bind m => n == m
  | .bool b, .bool c => b == c
  | .int lo hi, .int lo' hi' => lo == lo' && hi == hi'
  | .str s, .str t => s == t
  | .ctor i ps, .ctor j qs => i == j && sameAll Pat.same ps qs
  | .alts ps, .alts qs => sameAll Pat.same ps qs
  | _, _ => false

/-- Whether two patterns of pattern types are the same. -/
partial def corePatSame : Fren.Core.Pat → Fren.Core.Pat → Bool
  | .wild b, .wild c => b == c
  | .bool b, .bool c => b == c
  | .int lo hi, .int lo' hi' => lo == lo' && hi == hi'
  | .str s, .str t => s == t
  | .ctor i ps, .ctor j qs => i == j && sameAll corePatSame ps qs
  | .or ps, .or qs => sameAll corePatSame ps qs
  | _, _ => false

/-- Whether two declared types are the same. -/
partial def ptySame (t u : Fren.Core.PTy) : Bool :=
  t.ty == u.ty && sameOpt corePatSame t.pat? u.pat? && sameAll ptySame t.elems u.elems && t.text == u.text

/-- Whether two expressions are the same, and so have the same value
wherever both are evaluated in the same environment. -/
partial def Ex.same : Ex → Ex → Bool
  | .lit v, .lit w => v == w
  | .var n, .var m | .bound n, .bound m => n == m
  | .slot k, .slot j | .boundAt k, .boundAt j | .shared k, .shared j => k == j
  | .known v, .known w => v == w
  | .not a, .not b | .neg a, .neg b | .card a, .card b => a.same b
  | .bin o a b, .bin o' a' b' => o == o' && a.same a' && b.same b'
  | .when n c d, .when n' c' d' => n == n' && c.same c' && d.same d'
  | .ite c a b, .ite c' a' b' => c.same c' && a.same a' && b.same b'
  | .app f as, .app g bs => f == g && sameAll Ex.same as bs
  | .ctor t i as, .ctor u j bs => t == u && i == j && sameAll Ex.same as bs
  | .field e i, .field f j => i == j && e.same f
  | .update e fs, .update f gs => e.same f && sameAll (fun (k, x) (j, y) => k == j && x.same y) fs gs
  | .match e arms pos ps u pairs?, .match e' arms' pos' ps' u' pairs?' =>
    pos == pos' && ps == ps' && u == u' && pairs? == pairs?' && e.same e'
      && sameAll (fun (p, g?, b) (p', g?', b') => p.same p' && sameOpt Ex.same g? g?' && b.same b') arms arms'
  | .method m r as, .method m' r' bs => m == m' && r.same r' && sameAll Ex.same as bs
  | .matches r p re, .matches r' p' re' => p == p' && re == re' && r.same r'
  | .setLit as, .setLit bs | .seqLit as, .seqLit bs => sameAll Ex.same as bs
  | .pair a b, .pair a' b' | .range a b, .range a' b' => a.same a' && b.same b'
  | .index q i pos, .index q' i' pos' => pos == pos' && q.same q' && i.same i'
  | .cardinality c as, .cardinality c' bs => c == c' && sameAll Ex.same as bs
  | .quant file pos all ns ds ts b, .quant file' pos' all' ns' ds' ts' b' =>
    file == file' && pos == pos' && all == all' && ns == ns' && sameAll (sameOpt Ex.same) ds ds'
      && sameAll ptySame ts ts' && b.same b'
  | .table pos rows u, .table pos' rows' u' =>
    pos == pos' && u == u' && sameAll (fun (p, c?, v) (p', c?', v') => p == p' && sameOpt Ex.same c? c?' && v.same v') rows rows'
  | .const p e, .const p' e' => p == p' && e.same e'
  | .pre pos f gs e, .pre pos' f' gs' e' =>
    pos == pos' && f == f' && sameAll (fun (n, g) (n', g') => n == n' && g.same g') gs gs' && e.same e'
  | .typed t is e, .typed t' is' e' => ptySame t t' && is == is' && e.same e'
  | .memo ls e, .memo ls' e' => sameAll Ex.same ls ls' && e.same e'
  | .lifted ls e, .lifted ls' e' => sameAll (sameAll Ex.same) ls ls' && e.same e'
  | _, _ => false

/-- Whether evaluating `e` may cost more than reading a few values and
comparing them: it builds a value, looks one up in a set or a sequence,
applies a function or method, or has a quantifier, a table, a `match` or a
constant. -/
partial def Ex.costly (e : Ex) : Bool :=
  match e with
  | .lit _ | .var _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => false
  | .not _ | .neg _ | .field .. | .card _ | .when .. | .ite .. | .index .. => e.children.any (·.costly)
  | .bin op .. =>
    !(op matches .and | .or | .iff | .eq | .ne | .lt | .le | .gt | .ge | .add | .sub | .mul | .div | .mod)
      || e.children.any (·.costly)
  | _ => true

/-- Whether `e` binds names or starts a scope of its own (a quantifier, a
`match`, a table's shared expressions or a constant), within which an
expression may not mean what it means outside. -/
def Ex.scoped : Ex → Bool
  | .quant .. | .match .. | .table .. | .const .. | .memo .. | .lifted .. => true
  | _ => false

/-- The costly expressions in `e` (`Ex.costly`), outside its scopes
(`Ex.scoped`), outermost first. -/
partial def Ex.costlyParts (e : Ex) : Array Ex :=
  if !e.costly then #[]
  else if e.scoped then #[e]
  else e.children.foldl (init := #[e]) fun acc c => acc ++ c.costlyParts

/-- `e` with each costly expression, outermost first and outside scopes,
that `pick` picks replaced by `.shared k`, reading the `k`th of the
shared expressions `lets`, which it extends. -/
partial def Ex.share (pick : Ex → Bool) (lets : Array Ex) (e : Ex) : Ex × Array Ex :=
  if !e.costly then (e, lets) else
  if pick e then
    match lets.findIdx? (·.same e) with
    | some k => (.shared k, lets)
    | none => (.shared lets.size, lets.push e)
  else if e.scoped then (e, lets) else
  match e with
  | .not a => let (a, l) := a.share pick lets; (.not a, l)
  | .neg a => let (a, l) := a.share pick lets; (.neg a, l)
  | .card a => let (a, l) := a.share pick lets; (.card a, l)
  | .field a i => let (a, l) := a.share pick lets; (.field a i, l)
  | .matches a p re => let (a, l) := a.share pick lets; (.matches a p re, l)
  | .typed t is a => let (a, l) := a.share pick lets; (.typed t is a, l)
  | .bin op a b => let (a, l) := a.share pick lets; let (b, l) := b.share pick l; (.bin op a b, l)
  | .when n c d => let (c, l) := c.share pick lets; let (d, l) := d.share pick l; (.when n c d, l)
  | .ite c a b =>
    let (c, l) := c.share pick lets; let (a, l) := a.share pick l; let (b, l) := b.share pick l; (.ite c a b, l)
  | .app f args => let (args, l) := all args lets; (.app f args, l)
  | .ctor t i args => let (args, l) := all args lets; (.ctor t i args, l)
  | .setLit args => let (args, l) := all args lets; (.setLit args, l)
  | .seqLit args => let (args, l) := all args lets; (.seqLit args, l)
  | .cardinality c args => let (args, l) := all args lets; (.cardinality c args, l)
  | .method m r args => let (r, l) := r.share pick lets; let (args, l) := all args l; (.method m r args, l)
  | .pair a b => let (a, l) := a.share pick lets; let (b, l) := b.share pick l; (.pair a b, l)
  | .range a b => let (a, l) := a.share pick lets; let (b, l) := b.share pick l; (.range a b, l)
  | .index q i pos => let (q, l) := q.share pick lets; let (i, l) := i.share pick l; (.index q i pos, l)
  | .update a fs =>
    let (a, l) := a.share pick lets
    let (fs, l) := fs.foldl (init := (#[], l)) fun (acc, l) (k, x) => let (x, l) := x.share pick l; (acc.push (k, x), l)
    (.update a fs, l)
  | .pre pos f gs a =>
    let (gs, l) := gs.foldl (init := (#[], lets)) fun (acc, l) (n, g) => let (g, l) := g.share pick l; (acc.push (n, g), l)
    let (a, l) := a.share pick l
    (.pre pos f gs a, l)
  | e => (e, lets)
where
  all (es : Array Ex) (lets : Array Ex) : Array Ex × Array Ex :=
    es.foldl (init := (#[], lets)) fun (acc, l) x => let (x, l) := x.share pick l; (acc.push x, l)

/-- Whether an or-pattern within `p` binds a name, so that the names that
`p` binds when it matches (`Pat.matchVal`) may not be `Pat.binders p`. -/
partial def Pat.altsBind : Pat → Bool
  | .alts ps => ps.any (!·.binders.isEmpty)
  | .ctor _ ps => ps.any Pat.altsBind
  | _ => false

/-- The binders that `e` reads and does not bind, by name, before
`Ex.compile`. Those of the arms of a pattern whose or-pattern binds names,
which it may not bind, count as read. -/
partial def Ex.freeBound (e : Ex) : Array Name :=
  match e with
  | .bound n => #[n]
  -- Evaluated on its own, where no binder has a value.
  | .const .. => #[]
  | .quant _ _ _ ns ds _ b =>
    (ds.mapIdx fun k d? => (d?.map fun d => d.freeBound.filter (!(ns.extract 0 k).contains ·)).getD #[]).flatten
      ++ b.freeBound.filter (!ns.contains ·)
  | .match s arms .. =>
    s.freeBound ++ arms.flatMap fun (p, g?, b) =>
      let reads := (g?.map (·.freeBound)).getD #[] ++ b.freeBound
      if p.altsBind then reads else reads.filter (!p.binders.contains ·)
  | e => e.children.flatMap (·.freeBound)

/-- `e` with each `.shared k` read as `.shared (f k)`, outside scopes
(`Ex.scoped`), within which `Ex.share` puts none. -/
partial def Ex.renumberShared (f : Nat → Nat) (e : Ex) : Ex :=
  let go := Ex.renumberShared f
  match e with
  | .shared k => .shared (f k)
  | .not a => .not (go a)
  | .neg a => .neg (go a)
  | .card a => .card (go a)
  | .field a i => .field (go a) i
  | .matches a p re => .matches (go a) p re
  | .typed t is a => .typed t is (go a)
  | .bin op a b => .bin op (go a) (go b)
  | .when n c d => .when n (go c) (go d)
  | .ite c a b => .ite (go c) (go a) (go b)
  | .app f' args => .app f' (args.map go)
  | .ctor t i args => .ctor t i (args.map go)
  | .setLit args => .setLit (args.map go)
  | .seqLit args => .seqLit (args.map go)
  | .cardinality c args => .cardinality c (args.map go)
  | .method m r args => .method m (go r) (args.map go)
  | .pair a b => .pair (go a) (go b)
  | .range a b => .range (go a) (go b)
  | .index q i pos => .index (go q) (go i) pos
  | .update a fs => .update (go a) (fs.map fun (k, x) => (k, go x))
  | .pre pos f' gs a => .pre pos f' (gs.map fun (n, g) => (n, go g)) (go a)
  | e => e

/-- `e`, evaluated by `Ex.eval` in less time, to the same value under any
interpretation whose records', newtypes' and enumerations' parts are
`shapes`, as every search's are, the spec's (`World.interp`,
`readModel`), from an empty frame and no shared expressions:
- Each binder that `scope` names, the innermost first, is read by its
  position (`.boundAt`), as the frame has it: a quantifier binds its names
  in turn, and a `match` arm the binders of its pattern, the first
  innermost. With `scope` `none`, such as within an arm whose or-pattern
  binds names, binders are read by name, as everywhere else.
- A quantifier's domain that is a literal, a listed type's values, keeps
  only the values of its declared type, which are those that `Ex.eval`
  instantiates, so that it does not check them at each evaluation.
- The costly expressions that a table's rows share, such as an argument
  of a defined function that its body reads in each row, are each
  evaluated once, when first read (`.memo`, `Ex.share`).
- The costly expressions in a quantifier's body that do not read its last
  bound name are evaluated once for each value of the names that they
  read, when first read, rather than at each instance (`.lifted`).
- An expression whose parts are all known is known, but for one that
  reads the interpretation's functions: its value, which needs no
  environment, is computed once (`.known`). -/
partial def Ex.compile (shapes : Name → Option Fren.Core.DataShape) (scope : Option (List Name)) (e : Ex) : Ex :=
  match e with
  | .bound n => match scope.bind (·.idxOf? n) with
    | some k => .boundAt k
    | none => .bound n
  | .lit v => .known (some v)
  | .var _ | .slot _ | .boundAt _ | .shared _ | .known _ => e
  | e => fold (compound e)
where
  /-- An expression all of whose parts are known is too, unless it applies
  a function, or is a constant or a table or `match` without a value
  where nothing holds, whose values are the interpretation's: its value,
  whatever the environment, under any interpretation with `shapes`. -/
  fold (e : Ex) : Ex :=
    let readsFns := e matches .app .. | .const .. | .table _ _ (some _) | .match _ _ _ _ (some _) _
    if !readsFns && e.children.all (· matches .known _) then .known (e.eval { shapes } fun _ => none) else e
  /-- `e`, an expression with parts, with its parts compiled. -/
  compound (e : Ex) : Ex :=
  let go (x : Ex) := x.compile shapes scope
  match e with
  | .not a => .not (go a)
  | .neg a => .neg (go a)
  | .card a => .card (go a)
  | .field a i => .field (go a) i
  | .matches a p re => .matches (go a) p re
  | .typed t is a => .typed t is (go a)
  | .bin op a b => .bin op (go a) (go b)
  | .when n c d => .when n (go c) (go d)
  | .ite c a b => .ite (go c) (go a) (go b)
  | .app f args => .app f (args.map go)
  | .ctor t i args => .ctor t i (args.map go)
  | .setLit args => .setLit (args.map go)
  | .seqLit args => .seqLit (args.map go)
  | .cardinality c args => .cardinality c (args.map go)
  | .method m r args => .method m (go r) (args.map go)
  | .pair a b => .pair (go a) (go b)
  | .range a b => .range (go a) (go b)
  | .index q i pos => .index (go q) (go i) pos
  | .update a fs => .update (go a) (fs.map fun (k, x) => (k, go x))
  | .pre pos f gs a => .pre pos f (gs.map fun (n, g) => (n, go g)) (go a)
  -- Evaluated on its own, from an empty frame.
  | .const p a => .const p (a.compile shapes (some []))
  | .memo lets a => .memo (lets.map go) (go a)
  | .match s arms pos ps u pairs? =>
    .match (go s) (arms.map fun (p, g?, b) =>
      let inner := if p.altsBind then none else scope.map (p.binders.toList ++ ·)
      (p, g?.map (·.compile shapes inner), b.compile shapes inner)) pos ps u pairs?
  | .quant file pos all ns ds ts b =>
    -- The `k`th domain is evaluated with the names before it bound.
    let ds := ds.mapIdx fun k d? => d?.map fun d =>
      match d with
      | .lit (.seq vs) => .lit (.seq (vs.filter fun v => ts[k]?.all (typeHolds shapes · v)))
      | .lit (.set vs) => .lit (.set (vs.filter fun v => ts[k]?.all (typeHolds shapes · v)))
      | d => d.compile shapes (scope.map ((ns.extract 0 k).toList.reverse ++ ·))
    let listed (d? : Option Ex) : Bool := d? matches some (.lit (.seq _)) | some (.lit (.set _))
    -- A literal domain's values are of their type already: a `Bool`, with
    -- no pattern, holds of any value (`typeHolds`).
    let ts := if ds.all listed then #[] else ts.mapIdx fun k t => if listed ds[k]! then { ty := .bool } else t
    -- The position after the last of the bound names that `x` reads: the
    -- first at which its value is known.
    let level (x : Ex) : Nat := x.freeBound.foldl (init := 0) fun l n =>
      (ns.zipIdx.foldl (init := l) fun l (m, i) => if m == n then max l (i + 1) else l)
    let (b, found) := b.share (fun x => level x < ns.size) #[]
    let inner := scope.map (ns.toList.reverse ++ ·)
    if found.isEmpty then .quant file pos all ns ds ts (b.compile shapes inner) else
    -- Pushed level by level, each level's in order, so that the body reads
    -- the `p`th pushed as the `found.size - 1 - p`th from the last.
    let levels := (List.range ns.size).toArray.map fun j => (found.zipIdx.filter (level ·.1 == j)).map (·.2)
    let pushed := levels.flatten
    let b := b.renumberShared fun k => found.size - 1 - (pushed.idxOf? k).getD 0
    let lets := levels.mapIdx fun j ks => ks.map fun k => found[k]!.compile shapes (scope.map ((ns.extract 0 j).toList.reverse ++ ·))
    .lifted lets (.quant file pos all ns ds ts (b.compile shapes inner))
  | .table pos rows u =>
    let parts := rows.flatMap fun (_, c?, v) => (c?.map (·.costlyParts)).getD #[] ++ v.costlyParts
    -- Those that occur more than once.
    let twice := Id.run do
      let mut seen : Array Ex := #[]
      let mut twice : Array Ex := #[]
      for x in parts do
        if seen.any (·.same x) then
          unless twice.any (·.same x) do twice := twice.push x
        else seen := seen.push x
      return twice
    if twice.isEmpty then .table pos (rows.map fun (p, c?, v) => (p, c?.map go, go v)) u else
    let (rows, lets) := rows.foldl (init := (#[], #[])) fun (acc, lets) (p, c?, v) =>
      let (c?, lets) := match c? with
        | some c => let (c, l) := c.share (fun x => twice.any (·.same x)) lets; (some c, l)
        | none => (none, lets)
      let (v, lets) := v.share (fun x => twice.any (·.same x)) lets
      (acc.push (p, c?, v), lets)
    .memo (lets.map go) (.table pos (rows.map fun (p, c?, v) => (p, c?.map go, go v)) u)
  | e => e

/-- A constraint of a procedure nested at `pfx`, such as `w.v` for call `v`
of call `w`: `e` over the variables `pfx.x`. -/
structure Atom where
  /-- Where it comes from, such as `w.r` for requirement `r` of `w`'s procedure,
  or `w.x` for `w`'s binding of `x`. -/
  label : Name
  pfx : Name
  e : Ex
  /-- `e` as a search evaluates it (`Ex.compile`), if it is compiled
  already, for searches whose interpretations have the shapes that it was
  compiled with (`Atom.compiled`); else each search compiles it. -/
  run? : Option (Thunk Ex) := none
  deriving Inhabited

/-- `a`, compiled for searches whose interpretations' shapes are
`shapes`, when a search first needs it (`Ex.compile`), so that the
searches that share it compile it once. -/
def Atom.compiled (shapes : Name → Option Fren.Core.DataShape) (a : Atom) : Atom :=
  { a with run? := some (Thunk.mk fun _ => a.e.compile shapes (some [])) }

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

/-- The definitions of a procedure nested at `pfx`, as equations, each labelled
with its output. -/
def Comp.defAtoms (c : Comp) (pfx : Name := .anonymous) : Array Atom :=
  c.defs.map fun (d, e) => { label := pfx ++ d, pfx, e := .bin .eq (.var d) e }

/-- The bindings of call `i` of a procedure nested at `pfx`, as equations. -/
def bindingAtoms (pfx : Name) (i : Inst) : Array Atom :=
  i.bindings.map fun (x, e) => { label := pfx ++ i.name ++ x, pfx, e := .bin .eq (.var (i.name ++ x)) e }

mutual
/-- What call `i` of a procedure nested at `pfx` contributes, `I_w`: its
bindings, and the meaning of its comp. -/
partial def Spec.instAtoms (sp : Spec) (pfx : Name) (i : Inst) : Array Atom :=
  match sp.comp? i.comp with
  -- What its inputs' types bring is its assumption, which the call
  -- check asks of the bindings, rather than part of its behaviour.
  | some d => bindingAtoms pfx i ++ sp.meaning d (pfx ++ i.name) (typedInputs := false)
  | none => #[]

/-- Everything a procedure nested at `pfx` says of its variables: its
assumptions, requirements and calls (`Reqs/Lang/Procedures#meaning`). -/
partial def Spec.meaning (sp : Spec) (c : Comp) (pfx : Name := .anonymous) (typedInputs : Bool := true) : Array Atom :=
  c.defAtoms pfx ++ atomsOf pfx ((c.ofKind .assume).filter fun a => typedInputs || a.typed?.isNone)
    ++ atomsOf pfx (c.ofKind .ensure) ++ c.insts.flatMap (sp.instAtoms pfx)
end

/-- `I`, of the calls before `upTo`. -/
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
  | .data p targs, .ctor _ idx args =>
    match (sp.data.find? p).bind (·.ctors[idx]?), sp.data.find? p with
    | some c, some d =>
      let shown := (c.fields.zip args).map fun ((_, t), a) => a.showAs sp (t.subst targs)
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
  /-- The scope that paths resolve in: the module, or the procedure being
  lowered, if it has `use`s. -/
  scope : Name := .anonymous
  spec : Spec := {}
  /-- The binders of `match` arms lowered so far, which number their names. -/
  fresh : Nat := 0
  /-- The file being lowered, by its position among the files. -/
  file : Nat := 0
  /-- The type aliases, each with the type it names, without its patterns,
  and as declared. -/
  aliases : NameMap VTy := {}
  declaredAliases : NameMap Fren.Core.PTy := {}
  /-- The type parameters of the generic type being declared. -/
  typeParams : Array Name := #[]
  /-- The generic function being lowered, with its type parameters, which
  are abstract types within it (`Reqs/Lang/GenericFunctions`). -/
  fnTypeParams : Option (Name × Array Name) := none
  /-- The higher-order functions: each parameter's type, or a function
  parameter's parameters' and result's types (`Reqs/Lang/HigherOrder`). -/
  hofs : NameMap (Array (VTy ⊕ (Array VTy × VTy))) := {}

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
  -- A pattern type has its base type's values, to the evaluator.
  let segs := (splitPatternType segs).1
  -- An instance of a generic type, `G<A, B>`.
  if let some i := segs.findIdx? (·.name == Parser.argsOpen) then
    if i > 0 && segs[0]!.name != Parser.setSeg && segs[0]!.name != Parser.seqSeg && segs[0]!.name != Parser.relSeg then
      let args ← (Parser.splitArgs (segs.extract (i + 1) (segs.size - 1))).mapM lowerTy
      return match ← resolve (segs.extract 0 i) with
        | .item { path, .. } => .data path args.toList
        | r => .data r.path args.toList
  if let some k := (← get).typeParams.idxOf? (Name.mkSimple segs[0]!.name) then
    if segs.size == 1 then return .param k
  if let some (fn, ps) := (← get).fnTypeParams then
    if let some k := ps.idxOf? (Name.mkSimple segs[0]!.name) then
      if segs.size == 1 then return .abstract (Fren.Core.typeParamPath fn k ps[k]!)
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
    return .data path []
  | .item { kind := .enumItem, path, .. } => return .data path []
  | .item { kind := .typeItem, path, .. } =>
    if let some t := (← get).aliases.find? path then return t
    return .abstract path
  | r => throw s!"`{showPath r.path}` is not a type"

def dataDef (path : Name) : L DataDef := do
  let some d := (← get).spec.data.find? path | throw s!"unknown datatype `{showPath path}`"
  return d

structure Cx where
  /-- Every variable of the procedure (`Spec.flatVars`). -/
  vars : Array Var := #[]
  /-- The binders of the enclosing `match` arms, innermost first, each with
  its type and the name it is bound by in `Ex`, made unique so that a
  definition put under another arm is never captured. -/
  binders : List (Name × VTy × Name) := []
  /-- The names of the enclosing `let`s and `where` clauses, innermost
  first, each with its definition, which a mention of it stands for
  (`Reqs/Lang/Let#meaning`), and its type. A name is never also a binder. -/
  lets : List (Name × Ex × VTy) := []
  /-- In a higher-order function, its function parameters, each with the
  name of the uninterpreted function that it is applied as
  (`Reqs/Lang/HigherOrder#function-parameters`). -/
  fnParams : List (Name × Name) := []

/-- The type of the method `m` of a receiver of type `t`. -/
def methodTy (m : Fren.Core.Method) (t : VTy) : VTy :=
  match m.result, t with
  | .bool, _ => .bool
  -- `min` and `max`, the only methods of an ordered enumeration.
  | _, .data .. => t
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
    let .data p targs := ty | throw s!"`.{f}` reads a field of a value that is not a record"
    let d ← dataDef p
    let some c := d.ctors[0]? | throw s!"`{showPath p}` has no constructor"
    let some idx := c.fields.findIdx? (·.1 == Name.mkSimple f) | throw s!"`{showPath p}` has no field `{f}`"
    e := .field e idx
    ty := c.fields[idx]!.2.subst targs
  return (e, ty)

def evalClosed (e : Ex) : Option Val := e.eval {} fun _ => none

/-- `e` with each binder, and each mention of one, renamed by `f`. -/
partial def Ex.renameBound (f : Name → Name) : Ex → Ex
  | .lit v => .lit v
  | .var n => .var n
  | .slot k => .slot k
  | .boundAt k => .boundAt k
  | .shared k => .shared k
  | .known v => .known v
  | .lifted lets q => .lifted (lets.map (·.map (·.renameBound f))) (q.renameBound f)
  | .memo lets e => .memo (lets.map (·.renameBound f)) (e.renameBound f)
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
  | .typed t is a => .typed t is (a.renameBound f)
  | .match e arms pos ps u t =>
    .match (e.renameBound f) (arms.map fun (p, g?, b) => (p.rename f, g?.map (·.renameBound f), b.renameBound f)) pos ps u t
  | .quant file pos all ns ds ts b => .quant file pos all (ns.map f) (ds.map (·.map (·.renameBound f))) ts (b.renameBound f)
  | .range lo hi => .range (lo.renameBound f) (hi.renameBound f)

/-- `e` with each variable renamed by `f`. -/
partial def Ex.renameVars (f : Name → Name) : Ex → Ex
  | .lit v => .lit v
  | .var n => .var (f n)
  | .slot k => .slot k
  | .boundAt k => .boundAt k
  | .shared k => .shared k
  | .known v => .known v
  | .lifted lets q => .lifted (lets.map (·.map (·.renameVars f))) (q.renameVars f)
  | .memo lets e => .memo (lets.map (·.renameVars f)) (e.renameVars f)
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
  | .match e arms pos ps u t => .match (e.renameVars f) (arms.map fun (p, g?, b) => (p, g?.map (·.renameVars f), b.renameVars f)) pos ps u t
  | .quant file pos all ns ds ts b => .quant file pos all ns (ds.map (·.map (·.renameVars f))) ts (b.renameVars f)
  | .range lo hi => .range (lo.renameVars f) (hi.renameVars f)
  | .table pos rows u => .table pos (rows.map fun (p, c?, v) => (p, c?.map (·.renameVars f), v.renameVars f)) u
  | .const p e => .const p e
  | .typed t is a => .typed t is (a.renameVars f)

/-- `e` with each variable `n` replaced by `f n`. -/
partial def Ex.substVars (f : Name → Ex) : Ex → Ex
  | .lit v => .lit v
  | .var n => f n
  | .slot k => .slot k
  | .boundAt k => .boundAt k
  | .shared k => .shared k
  | .known v => .known v
  | .lifted lets q => .lifted (lets.map (·.map (·.substVars f))) (q.substVars f)
  | .memo lets e => .memo (lets.map (·.substVars f)) (e.substVars f)
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
  | .match e arms pos ps u t => .match (e.substVars f) (arms.map fun (p, g?, b) => (p, g?.map (·.substVars f), b.substVars f)) pos ps u t
  | .quant file pos all ns ds ts b => .quant file pos all ns (ds.map (·.map (·.substVars f))) ts (b.substVars f)
  | .range lo hi => .range (lo.substVars f) (hi.substVars f)
  | .table pos rows u => .table pos (rows.map fun (p, c?, v) => (p, c?.map (·.substVars f), v.substVars f)) u
  | .const p e => .const p e
  | .typed t is a => .typed t is (a.substVars f)

/-- The procedure that checks that `c` refines `a` (`Reqs/Lang/Refinement`): its
parameters are `c`'s, its assumptions `a`'s, it has a call `w` of `c` and
`a`'s calls, and its expectations are `a`'s requirements and
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
  | .boundAt k => .boundAt k
  | .shared k => .shared k
  | .known v => .known v
  | .lifted lets q => .lifted (lets.map (·.map (·.subst σ))) (q.subst σ)
  | .memo lets e => .memo (lets.map (·.subst σ)) (e.subst σ)
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
  | .typed t is a => .typed t is (a.subst σ)
  -- An arm's binders shadow those of `σ`.
  | .match e arms pos ps u t =>
    .match (e.subst σ) (arms.map fun (p, g?, b) =>
      let σ' := σ.filter (!p.binders.contains ·.1)
      (p, g?.map (·.subst σ'), b.subst σ')) pos ps u t
  -- So do a quantifier's bound names.
  | .quant file pos all ns ds ts b =>
    let σ' := σ.filter (!ns.contains ·.1)
    .quant file pos all ns (ds.map (·.map (·.subst σ'))) ts (b.subst σ')
  | .range lo hi => .range (lo.subst σ) (hi.subst σ)

/-- `e` with each application of a function of `σ` replaced by its
closure's body, with the closure's parameters standing for the arguments
(`Reqs/Lang/HigherOrder#meaning`): the closure's names are unique, and
those of the body it is unfolded into made unique, so that none captures
another. -/
partial def Ex.substFns (σ : List (Name × Array Name × Ex)) : Ex → Ex
  | .app g args =>
    let args := args.map (·.substFns σ)
    match σ.lookup g with
    | some (ps, b) => b.subst (ps.zip args).toList
    | none => .app g args
  | .lit v => .lit v
  | .var n => .var n
  | .slot k => .slot k
  | .boundAt k => .boundAt k
  | .shared k => .shared k
  | .known v => .known v
  | .lifted lets q => .lifted (lets.map (·.map (·.substFns σ))) (q.substFns σ)
  | .memo lets e => .memo (lets.map (·.substFns σ)) (e.substFns σ)
  | .bound n => .bound n
  | .not a => .not (a.substFns σ)
  | .neg a => .neg (a.substFns σ)
  | .bin op a b => .bin op (a.substFns σ) (b.substFns σ)
  | .when negated c d => .when negated (c.substFns σ) (d.substFns σ)
  | .ite c a b => .ite (c.substFns σ) (a.substFns σ) (b.substFns σ)
  | .pre pos g gs e => .pre pos g (gs.map fun (p, x) => (p, x.substFns σ)) (e.substFns σ)
  | .cardinality c args => .cardinality c (args.map (·.substFns σ))
  | .method m r args => .method m (r.substFns σ) (args.map (·.substFns σ))
  | .matches r p re => .matches (r.substFns σ) p re
  | .setLit es => .setLit (es.map (·.substFns σ))
  | .pair a b => .pair (a.substFns σ) (b.substFns σ)
  | .seqLit es => .seqLit (es.map (·.substFns σ))
  | .index q i pos => .index (q.substFns σ) (i.substFns σ) pos
  | .card e => .card (e.substFns σ)
  | .ctor ty idx args => .ctor ty idx (args.map (·.substFns σ))
  | .field e idx => .field (e.substFns σ) idx
  | .update e fs => .update (e.substFns σ) (fs.map fun (k, x) => (k, x.substFns σ))
  | .table pos rows u => .table pos (rows.map fun (p, c?, v) => (p, c?.map (·.substFns σ), v.substFns σ)) u
  | .const p e => .const p e
  | .typed t is a => .typed t is (a.substFns σ)
  | .match e arms pos ps u t => .match (e.substFns σ) (arms.map fun (p, g?, b) => (p, g?.map (·.substFns σ), b.substFns σ)) pos ps u t
  | .quant file pos all ns ds ts b => .quant file pos all ns (ds.map (·.map (·.substFns σ))) ts (b.substFns σ)
  | .range lo hi => .range (lo.substFns σ) (hi.substFns σ)

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
      let variant := st.table.namesVariant? st.scope n
      match Fren.Core.patternName (n == `true || n == `false) bang variant with
      | .boolLiteral => return (.bool (n == `true), [])
      | .binder =>
        -- Named apart, so that a definition put under it is never captured.
        let k := (← get).fresh
        modify fun s => { s with fresh := s.fresh + 1 }
        return (.bind (Name.mkNum n k), [(n, t, Name.mkNum n k)])
      | .variant => pure ()
    let .variant en idx ← resolve segs | throw "a pattern names no variant"
    let .data path targs := t | throw "a variant matches a value that is not an enumeration"
    unless en.path == path do throw s!"the pattern's variant is not of `{showPath path}`"
    let d ← dataDef path
    let tys := d.ctors[idx]!.fields.map (·.2.subst targs)
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
  | .typed _ _ a => a.readsUnspecified
  | .table _ rows none => rows.any fun (_, c?, v) => c?.any (·.readsUnspecified) || v.readsUnspecified
  | .lit _ | .var _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => false
  | .memo lets a => a.readsUnspecified || lets.any (·.readsUnspecified)
  | .lifted lets a => a.readsUnspecified || lets.any (·.any (·.readsUnspecified))
  | .not a | .neg a | .field a _ | .card a | .matches a _ _ | .pre _ _ _ a => a.readsUnspecified
  | .quant _ _ _ _ ds _ a => a.readsUnspecified || ds.any (·.any (·.readsUnspecified))
  | .range lo hi => lo.readsUnspecified || hi.readsUnspecified
  | .bin _ a b | .when _ a b | .pair a b => a.readsUnspecified || b.readsUnspecified
  | .ite c a b => c.readsUnspecified || a.readsUnspecified || b.readsUnspecified
  | .app _ args | .ctor _ _ args | .setLit args | .seqLit args | .cardinality _ args => args.any (·.readsUnspecified)
  | .method _ r args => r.readsUnspecified || args.any (·.readsUnspecified)
  | .update e fs => e.readsUnspecified || fs.any (·.2.readsUnspecified)
  | .match e arms _ _ u _ => u.isSome || e.readsUnspecified || arms.any fun (_, g?, b) =>
    g?.any (·.readsUnspecified) || b.readsUnspecified

/-- `t` as both front ends see it (`Fren.Core.Ty`). -/
partial def VTy.core (sp : Spec) : VTy → Fren.Core.Ty
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .set t => .set (t.core sp)
  | .rel a b => .rel (a.core sp) (b.core sp)
  | .seq t => .seq (t.core sp)
  | .data p as =>
    let as := as.map (·.core sp)
    if (sp.data.find? p).any (·.isRecord) then .record p as else .enum p as
  | .abstract p => .abstract p
  | .newtype p u => .newtype p (u.core sp)
  | .param k => .param k .anonymous

/-- The declared type written `segs`, with the patterns of the pattern
types within it, as the elaborator's `elabPTy` has it. -/
partial def lowerPTy (segs : Array Ident) : L Fren.Core.PTy := do
  let (base, seg?) := splitPatternType segs
  let t ← lowerBasePTy base
  let some seg := seg? | return t
  let some p := seg.pattern? | throw "a pattern type's pattern"
  let vt ← lowerTy base
  let (q, _) ← lowerPattern vt p
  return { t with pat? := some q.core }
where
  lowerBasePTy (segs : Array Ident) : L Fren.Core.PTy := do
    if segs[0]!.name == Parser.setSeg || segs[0]!.name == Parser.seqSeg then
      let e ← lowerPTy (segs.extract 1)
      let sp := (← get).spec
      return { ty := (← lowerTy segs).core sp, elems := #[e] }
    if segs[0]!.name == Parser.relSeg then
      let (a, b) := Parser.splitRel (segs.extract 1)
      let sp := (← get).spec
      return { ty := (← lowerTy segs).core sp, elems := #[← lowerPTy a, ← lowerPTy b] }
    if segs.size == 1 && (["Bool", "Int", "Nat", "String"].contains segs[0]!.name
        || (← get).typeParams.contains (Name.mkSimple segs[0]!.name)
        || (← get).fnTypeParams.any (·.2.contains (Name.mkSimple segs[0]!.name))) then
      return .plain ((← lowerTy segs).core (← get).spec)
    -- An instance of a generic type, with its type arguments as declared.
    if let some i := segs.findIdx? (·.name == Parser.argsOpen) then
      if i > 0 then
        let args ← (Parser.splitArgs (segs.extract (i + 1) (segs.size - 1))).mapM lowerPTy
        return { ty := (← lowerTy segs).core (← get).spec, elems := args }
    if let .item { kind := .typeItem, path, .. } ← resolve segs then
      if let some t := (← get).declaredAliases.find? path then return t
    return .plain ((← lowerTy segs).core (← get).spec)

/-- The value `v` of the type `t` (`Fren.Core.PVal`): a newtype's is its
underlying type's. -/
partial def Spec.ofPVal (sp : Spec) : VTy → Fren.Core.PVal → Val
  | _, .bool b => .bool b
  | _, .int i => .int i
  | .newtype _ u, .ctor _ #[w] => sp.ofPVal u w
  | .data p targs, .ctor idx args => match sp.data.find? p with
    | some d => .ctor p idx ((args.zip (d.ctors[idx]!.fields.map (·.2.subst targs))).map fun (w, u) => sp.ofPVal u w)
    | none => .ctor p idx #[]
  | _, .ctor idx _ => .ctor .anonymous idx #[]

/-- Every value of the declared type `pt`, of the type `t`, in the order of a
quantifier's instances, if it is listed, as the elaborator's
`binderValues` says (`lang::quantified_type`, `lang::pattern_finite`). -/
def Spec.listedValues (sp : Spec) (t : VTy) (pt : Fren.Core.PTy) : Option (Array Val) :=
  let shapes := sp.shapes.find?
  -- Only a listed type's values are listed, by the facts that the
  -- elaborator's `binderValues` reads (`Fren.Core.typeFacts`).
  if !(Fren.Core.typeFacts shapes pt.node).listed then none
  else if (pt.cons shapes).isNone then some (sp.values t)
  else match pt.count? shapes with
    | some n =>
      if n > Fren.Core.maxInstances then some #[]
      else some (((pt.values shapes Fren.Core.maxInstances).map (·.map (sp.ofPVal t))).getD #[])
    | none => none

/-- The operands of the chain of `and` `e`. -/
partial def andOperands : Expr → Array Expr
  | .bin _ "and" a b => andOperands a ++ andOperands b
  | e => #[e]

/-- Whether `e` is a pattern test whose pattern binds a name. -/
def bindingTest (e : Expr) : L Bool := do
  let .is _ _ p := e | return false
  let st ← get
  return p.names.any fun x =>
    let (n, bang) := Fren.Core.declaredName (Name.mkSimple x.name)
    let variant := st.table.namesVariant? st.scope n
    Fren.Core.patternName (n == `true || n == `false) bang variant == .binder

mutual
partial def lowerExpr (cx : Cx) : Expr → L (Ex × VTy)
  -- A condition whose pattern tests bind names: `when x is P, D` is
  -- `match x { P => D, _ => true }`, and `when a and b, D` is `when a, when
  -- b, D` (`Reqs/Lang/Expressions#pattern-tests`).
  | .when _ false c d => do
    let cs := andOperands c
    unless ← cs.anyM bindingTest do return (.when false (← lowerExpr cx c).1 (← lowerExpr cx d).1, .bool)
    let (x, _) ← lowerChain cx cs.toList (fun cx => lowerExpr cx d) (fun ci rest => .when false ci rest)
      (.lit (.bool true)) whenPos
    return (x, .bool)
  | .when _ negated c d => do
    return (.when negated (← lowerExpr cx c).1 (← lowerExpr cx d).1, .bool)
  -- Likewise, `if x is P then a else b` is `match x { P => a, _ => b }`, and
  -- `if c and d then a else b` is `if c then (if d then a else b) else b`.
  | .ite _ c a b => do
    let (y, _) ← lowerExpr cx b
    let cs := andOperands c
    unless ← cs.anyM bindingTest do
      let (a, t) ← lowerExpr cx a
      return (.ite (← lowerExpr cx c).1 a y, t)
    lowerChain cx cs.toList (fun cx => lowerExpr cx a) (fun ci rest => .ite ci rest y) y
  -- And `x is P and e` is `match x { P => e, _ => false }`.
  | e@(.bin _ "and" _ _) => do
    let cs := andOperands e
    unless ← (cs.pop).anyM bindingTest do
      let .bin _ _ a b := e | unreachable!
      return (.bin .and (← lowerExpr cx a).1 (← lowerExpr cx b).1, .bool)
    let (x, _) ← lowerChain cx (cs.pop).toList (fun cx => lowerExpr cx cs.back!) (fun ci rest => .bin .and ci rest)
      (.lit (.bool false))
    return (x, .bool)
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
      -- A binder shadows the procedure's variables; otherwise the longest
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
        -- the root is not a call and nothing shadows it here.
        let st ← get
        let .ok (.item { kind := .constItem, path, .. }) := st.table.resolvePath st.scope #[Name.mkSimple parts.head!]
          | throw s!"`{segs[0]!.name}` names no variable"
        let some (v, t) := st.spec.consts.find? path | throw s!"unknown constant `{showPath path}`"
        return ← readFields v t parts.tail
    match ← resolve segs with
    | .variant en idx => do
      let d ← dataDef en.path
      unless d.ctors[idx]!.fields.isEmpty do throw s!"`{showPath en.path}::{en.variants[idx]!}` needs a payload"
      return (.lit (.ctor en.path idx #[]), .data en.path [])
    | .item { kind := .constItem, path, .. } =>
      let some (v, t) := (← get).spec.consts.find? path | throw s!"unknown constant `{showPath path}`"
      return (v, t)
    | r => throw s!"`{showPath r.path}` is not a value"
  -- The elaborator has checked that a closure is an argument for a
  -- function parameter, which `lowerFnArg` lowers.
  | .closure .. => throw "a closure is only an argument for a function parameter"
  | .app span segs written => do
    -- A function parameter, applied as the uninterpreted function that it
    -- is in its function's own checks, which an application of the
    -- function replaces (`Ex.substFns`).
    if segs.size == 1 then
      if let some q := cx.fnParams.lookup (Name.mkSimple segs[0]!.name) then
        unless cx.binders.any (·.1 == Name.mkSimple segs[0]!.name) do
          let args ← written.mapM fun a => (·.1) <$> lowerExpr cx a
          let some (_, r) := (← get).spec.funs.find? q | throw s!"unknown function `{showPath q}`"
          return (.app q args, r)
    let st ← get
    if let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) then
      if let some ts := st.hofs.find? path then
        return ← lowerHigherOrder cx span path ts written
    let typed ← written.mapM (lowerExpr cx)
    let args := typed.map (·.1)
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
      -- A generic function without a body, at the instance that its
      -- arguments' types give it, a function of its own.
      if let some (_, tps, declared, result) := (← get).spec.generics.find? (·.1 == path) then
        let found := (List.range tps.size).map fun k =>
          (declared.zip typed).findSome? fun (d, (_, t)) => d.matchParam k t
        let targs := found.mapIdx fun k t? => (t?.map VTy.widen).getD (.param k)
        let r := result.subst targs
        -- Its type arguments not known here, as the type expected of it
        -- may give them: a function that has no value, which the
        -- evaluator does not know (`Reqs/Eval#searching-for-behaviours`).
        if found.any (·.isNone) then return (← withPres (.app (Name.str path "<?>") args), r)
        -- At its own type parameters, in its contract, the function itself.
        let own := (List.range tps.size).map fun k => VTy.abstract (Fren.Core.typeParamPath path k tps[k]!)
        if targs == own then return (← withPres (.app path args), r)
        let sp := (← get).spec
        let inst := Name.str path.getPrefix (path.getString! ++ Fren.Core.instanceText (targs.toArray.map (·.core sp)))
        modify fun s => { s with
          spec.funs := s.spec.funs.insert inst (declared.map (·.subst targs), r)
          spec.instanceOf := s.spec.instanceOf.insert inst path }
        return (← withPres (.app inst args), r)
      let some (_, r) := (← get).spec.funs.find? path | throw s!"unknown function `{showPath path}`"
      return (← withPres (.app path args), r)
    | .variant en idx =>
      let d ← dataDef en.path
      return (.ctor en.path idx args, d.constructed idx (typed.map (·.2)))
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
    let mut tys := #[]
    for (f, _) in c.fields do
      let some (x, e?) := fields.find? (fun (x, _) => Name.mkSimple x.name == f) | throw s!"no value for field `{f}`"
      let (v, t) ← lowerExpr cx (e?.getD (.path span #[x]))
      vals := vals.push v
      tys := tys.push t
    return (.ctor path 0 vals, d.constructed 0 tys)
  | .update _ base fields => do
    let (r, t) ← lowerExpr cx base
    let .data path targs := t | throw "an updated value is not a record"
    let d ← dataDef path
    let some c := d.ctors[0]? | throw s!"`{showPath path}` has no constructor"
    -- In the order of the record's fields, as the elaborator reads them.
    let mut vals := #[]
    for (f, _) in c.fields, k in [0:c.fields.size] do
      let some (x, e?) := fields.find? (fun (x, _) => Name.mkSimple x.name == f) | continue
      vals := vals.push (k, (← lowerExpr cx (e?.getD (.path x.span #[x]))).1)
    return (.update r vals, .data path targs)
  | .field _ e f => do
    let (x, t) ← lowerExpr cx e
    readFields x t [f.name]
  | .match span scrutinee arms isTable => do
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
    -- Whether some arm may not be taken, by the rule that the elaborators
    -- decide it with (`Fren.Core.checkMatch`). They have accepted the spec,
    -- so a rejection here is a disagreement with them, an internal error,
    -- never a default.
    let st ← get
    let sigs : Fren.Core.Sigs := fun p =>
      ((st.spec.data.find? p).map fun d => d.ctors.map fun c => (c.name, c.fields.map (·.2.patTy))).getD #[]
    let pats := out.map (·.1.core)
    let guarded := out.map (·.2.1.isSome)
    let checked := if isTable then Fren.Core.checkTableArms sigs t.patTy pats guarded
      else (Fren.Core.checkMatch sigs t.patTy pats guarded).map (·, #[])
    let (unguardedExhaustive, pairs) ← match checked with
      | .ok u => pure u
      | .error (_, msg) => throw s!"the evaluator rejects a `match` that the elaborator accepted: {msg.headline}"
    let pairs? := if isTable then some pairs else none
    let armPos := arms.map (·.1.span.start)
    if unguardedExhaustive then return (.match s out span.start armPos none pairs?, ty)
    -- The function of the interpretation for its type's unspecified value.
    let u := unspecifiedFn ty
    modify fun s => { s with spec.funs := s.spec.funs.insert u (#[], ty) }
    return (.match s out span.start armPos (some u) pairs?, ty)
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
    return (.match s #[(pat, none, .lit (.bool true)), (.wild, none, .lit (.bool false))] 0 #[] none none, .bool)
  | .«let» _ defs body _ => do
    -- Each name stands for its definition, which sees the earlier names.
    let mut cx := cx
    for (x, _, d) in defs do
      let (e, t) ← lowerExpr cx d
      let n := declName x
      cx := { cx with lets := (n, e, t) :: cx.lets, binders := cx.binders.filter (·.1 != n) }
    lowerExpr cx body
  | .quant span all bs body => do
    -- Each bound name with its type, as declared, and a name made unique,
    -- as a pattern's binder's is.
    let mut bound : Array (Name × VTy × Fren.Core.PTy × Name) := #[]
    for b in bs do
      let t ← lowerTy b.ty
      let pt ← lowerPTy b.ty
      for x in b.names do
        let k := (← get).fresh
        modify fun s => { s with fresh := s.fresh + 1 }
        bound := bound.push (declName x, t, pt, Name.mkNum (declName x) k)
    -- A bound name hides a name of an enclosing `let` or `where`.
    let names := bound.map (·.1)
    let inner := { cx with binders := (bound.map fun (n, t, _, u) => (n, t, u)).toList.reverse ++ cx.binders,
                           lets := cx.lets.filter (!names.contains ·.1) }
    let (b, _) ← lowerExpr inner body
    let low (e : Expr) : L Ex := return (← lowerExpr inner e).1
    let sp := (← get).spec
    -- Each bound name's domain: every value of a listed type, and for any
    -- other, what its guard bounds it to (`Reqs/Eval#quantifiers`).
    let strs := names.map (·.getString!)
    let mut doms : Array (Option Ex) := #[]
    for (_, t, pt, _) in bound, k in [0:bound.size] do
      if let some vs := sp.listedValues t pt then
        doms := doms.push (some (.lit (.seq vs)))
        continue
      let (d, reads) := domainOf all strs body k (t == .nat)
      let one := Ex.lit (.int 1)
      -- A lower bound, and an upper bound past the range's end.
      let lower (j : Nat) : L (Option Ex) := do
        let some (e, strict) := reads[j]?.bind id | return none
        let x ← low e
        return some (if strict then .bin .add x one else x)
      let upper (j : Nat) : L (Option Ex) := do
        let some (e, strict) := reads[j]?.bind id | return none
        let x ← low e
        return some (if strict then x else .bin .add x one)
      let dom ← match d with
        | .members j => match reads[j]?.bind id with
          | some (e, _) => some <$> low e
          | none => pure none
        | .range lo hi => do
          let (some l, some h) := (← lower lo, ← upper hi) | pure none
          pure (some (.range l h))
        | .fromZero hi => do pure ((← upper hi).map (Ex.range (.lit (.int 0))))
        | .unbounded => pure none
      doms := doms.push dom
    return (.quant (← get).file span.start all (bound.map (·.2.2.2)) doms (bound.map (·.2.2.1)) b, .bool)

/-- An application of the higher-order function at `path`, whose parameters
have the types `ts`, to `args`: its body, with each parameter standing for
its argument, and each function parameter for its closure
(`Reqs/Lang/HigherOrder#meaning`), and its body's names made unique first,
so that neither captures the other's. -/
partial def lowerHigherOrder (cx : Cx) (span : Span) (path : Name) (ts : Array (VTy ⊕ (Array VTy × VTy)))
    (args : Array Expr) : L (Ex × VTy) := do
  let some (ps, body, r) := (← get).spec.defs.find? path | throw s!"unknown function `{showPath path}`"
  let k := (← get).fresh
  modify fun s => { s with fresh := s.fresh + 1 }
  let ren (n : Name) : Name := Name.mkNum n k
  -- The value arguments first, whose types give the type parameters'.
  let mut σ : List (Name × Ex) := []
  let mut tσ : List (Name × VTy) := []
  for a in args, t in ts, p in ps do
    if let .inl d := t then
      let (x, tx) ← lowerExpr cx a
      σ := σ ++ [(ren p, x)]
      tσ := tσ ++ d.matchAbstract tx
  let mut fσ : List (Name × Array Name × Ex) := []
  for a in args, t in ts, p in ps do
    if let .inr (pts, _) := t then
      fσ := fσ ++ [(p, ← lowerFnArg cx span (pts.map (·.substAbstract tσ)) a)]
  let x := ((body.renameBound ren).subst σ).substFns fσ
  -- With its preconditions at its arguments, if it has any.
  -- Its preconditions are over its value parameters, as its body is.
  let x := match (← get).spec.pres.find? path with
    | some (_, pres) => Ex.pre span.start path (pres.map fun (n, g) => (n, ((g.renameBound ren).subst σ).substFns fσ)) x
    | none => x
  return (x, r.substAbstract tσ)

/-- A closure, or a function's name `g`, which is the closure `|x1, ...,
xn| g(x1, ..., xn)`, given for a function parameter whose parameters have
the types `pts`: its parameters' names, made unique, and its body. -/
partial def lowerFnArg (cx : Cx) (span : Span) (pts : Array VTy) (a : Expr) : L (Array Name × Ex) := do
  let (names, body) : Array Name × Expr := match a with
    | .closure _ params body => (params.map fun (x, _) => declName x, body)
    | .path s segs =>
      let xs := (List.range pts.size).toArray.map fun j => ({ name := s!"#{j}", span := s } : Ident)
      (xs.map (Name.mkSimple ·.name), .app s segs (xs.map fun x => .path s #[x]))
    | e => (#[], e)
  let _ := span
  let mut bound := #[]
  for n in names, t in pts do
    let k := (← get).fresh
    modify fun s => { s with fresh := s.fresh + 1 }
    bound := bound.push (n, t, Name.mkNum n k)
  let inner := { cx with binders := bound.toList.reverse ++ cx.binders, lets := cx.lets.filter fun (n, _) => !names.contains n }
  let (b, _) ← lowerExpr inner body
  return (bound.map (·.2.2), b)

/-- The chain of `and` `cs`, at the position `pos` for its `match`es
(`whenPos` for a `when`'s condition), each of whose operands decides whether what
`last` gives is the value: a pattern test that binds names, as `match x {
P => rest, _ => otherwise }`, with its binders in scope in the rest, and
any other operand `c` by `join c rest`. -/
partial def lowerChain (cx : Cx) (cs : List Expr) (last : Cx → L (Ex × VTy)) (join : Ex → Ex → Ex) (otherwise : Ex)
    (pos : Nat := 0) :
    L (Ex × VTy) := do
  match cs with
  | [] => last cx
  | c :: cs =>
    if let .is _ scrutinee p := c then
      if ← bindingTest c then
        let (s, t) ← lowerExpr cx scrutinee
        let (pat, bound) ← lowerPattern t p
        let bcx := { cx with binders := bound.reverse ++ cx.binders, lets := cx.lets.filter fun (n, _) => !bound.any (·.1 == n) }
        let (rest, ty) ← lowerChain bcx cs last join otherwise pos
        return (.match s #[(pat, none, rest), (.wild, none, otherwise)] pos #[] none none, ty)
    let (x, _) ← lowerExpr cx c
    let (rest, ty) ← lowerChain cx cs last join otherwise pos
    return (join x rest, ty)

end

def varTy (ty? : Option (Array Ident)) : L VTy := do
  match ty? with
  | some t => lowerTy t
  | none => return .bool

/-- `x`'s constraint of its declared type `t`, if it has one: what its
type brings, as a constraint (`Reqs/Lang/Procedures#pattern-types`). -/
def typeConstraint (kind : PropKind) (x : Name) (t : Fren.Core.PTy) : L (Option Constraint) := do
  let sp := (← get).spec
  if (t.cons sp.shapes.find?).isNone then return none
  -- The bounds of its patterns, and of those within it, to search among.
  let rec ints (fuel : Nat) (t : Fren.Core.PTy) : Array Int :=
    match fuel with
    | 0 => #[]
    | fuel + 1 =>
      let own := (t.pat?.map Fren.Core.Pat.bounds).getD #[]
      let parts := match t.ty with
        | .record p _ | .enum p _ | .newtype p _ => ((sp.shapes.find? p).map (·.parts.flatten)).getD #[]
        | _ => #[]
      own ++ (t.elems ++ parts).flatMap (ints fuel ·)
  return some { kind, name := .num x 0, e := .typed t (ints 8 t) (.var x), typed? := some "" }


/-- The name that an item's declaration `x` declares, without the `!` that
marks it as shadowing one of the prelude's names (`Fren.Core.declaredName`). -/
def itemName (x : Ident) : Name := (Fren.Core.declaredName (Name.mkSimple x.name)).1

/-- Imports `segs` into the current module, or into the procedure `scope`. -/
def declareUseIn (segs : Array Ident) (glob : Bool) (scope : Option Name) : L Unit := do
  let st ← get
  let u ← liftE (st.table.declareUse st.module (segNames segs) glob (scope.getD st.module))
  modify fun s => { s with table := s.table.addUse u, scope := scope.getD s.scope }

def lowerComp (isPub : Bool) (name : Ident) (header body : Array Member) : L Unit := do
  -- Each result with the definition that an `out` member gives it.
  let defs := body.filterMap fun | .define x e => some (x.name, e) | _ => none
  let members := header.map (fun
    | .var false true det x ty none => .var false true det x ty ((defs.find? (·.1 == Fren.Core.nameText (declName x))).map (·.2))
    | m => m) ++ body.filter (!· matches .define ..)
  let path := (← get).module ++ itemName name
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
    let .inst x p bs named _ := m | continue
    let cpath ← match ← resolve p with
      | .item { kind := .compItem, path, .. } => pure path
      | r => throw s!"`{showPath r.path}` is not a procedure"
    -- A call's arguments, in the order of the callee's parameters.
    let bs ← if named then pure bs else do
      let some callee := (← get).spec.comp? cpath | throw s!"unknown procedure `{showPath cpath}`"
      let params := callee.vars.filter (fun v => v.role == .input && v.name.isAtomic) |>.map (Fren.Core.nameText ·.name)
      let some bound := Fren.Core.callBindings params bs | throw s!"wrong number of arguments to `{showPath cpath}`"
      pure (bound.map fun (n, (a, e?)) => ({ a with name := n }, e?))
    pending := pending.push (declName x, cpath, bs)
  let shell : Comp := { path, vars, constraints := #[], insts := pending.map fun (w, c, _) => { name := w, comp := c, bindings := #[] } }
  let cx : Cx := { vars := st.spec.flatVars shell }
  let mut insts := #[]
  for (w, cpath, bs) in pending do
    let mut bindings := #[]
    for (b, e?) in bs do
      bindings := bindings.push (Name.mkSimple b.name, (← lowerExpr cx (e?.getD (.path b.span #[b]))).1)
    insts := insts.push { name := w, comp := cpath, bindings }
  -- What each variable's type brings, but a defined output's, first: an
  -- input's an assumption, an output's a guarantee.
  let mut constraints := #[]
  for m in members do
    let .var isIn _ _ x ty? defn? := m | continue
    let some ty := ty? | continue
    if defn?.isSome then continue
    if let some c ← typeConstraint (if isIn then .assume else .ensure) (declName x) (← lowerPTy ty) then
      constraints := constraints.push c
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
inputs `vars`, as a procedure for the checks of its tables and of the
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
    (clauses : Array (Bool × Ident × Expr)) (fnParams : List (Name × Name) := []) : L (Array Constraint) := do
  let cx : Cx := { binders := ps.toList.reverse.map fun (x, t) => (x, t, x), fnParams }
  let mut pres := #[]
  let mut posts := #[]
  let mut constraints := #[]
  for (post, x, e) in clauses do
    let cn := Name.mkSimple x.name
    let bound := (← lowerExpr cx e).1
    if post then posts := posts.push bound else pres := pres.push (cn, bound)
    if defined || !post then
      let c := (← lowerExpr { vars, fnParams } e).1
      constraints := constraints.push { kind := (if post then .ensure else .assume), name := n ++ cn, e := c }
  unless pres.isEmpty do
    let entry := (ps.map (path ++ ·.1), pres.map fun (cn, g) => (cn, g.renameBound (path ++ ·)))
    modify fun s => { s with spec.pres := s.spec.pres.insert path entry }
  unless defined || posts.isEmpty do
    modify fun s => { s with spec.contracts := s.spec.contracts.insert path (ps.map (·.1), pres.map (·.2), posts) }
  return constraints


/-- The path of the procedure that `segs` names. -/
def resolveComp (segs : Array Ident) : L Name := do
  match ← resolve segs with
  | .item { kind := .compItem, path, .. } => pure path
  | r => throw s!"`{showPath r.path}` is not a procedure"

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
  let n := itemName name
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
  | .enum isPub name variants _ params => do
    let st ← get
    let path := st.module ++ itemName name
    modify fun s => { s with typeParams := params.map (Name.mkSimple ·.name) }
    let vs := variants.map (Name.mkSimple ·.1.name)
    -- Declared first: a payload may have the enumeration's own type.
    modify fun s => { s with table := (s.table.addItem { kind := .enumItem, path, isPub, owner := s.module }).addEnum { path, variants := vs } }
    let mut ctors := #[]
    for (v, payload?) in variants do
      let tys ← (payload?.getD #[]).mapM lowerTy
      ctors := ctors.push { name := Name.mkSimple v.name, fields := tys.map (.anonymous, ·) }
    modify fun s => { s with spec.data := s.spec.data.insert path { path, isRecord := false, ctors } }
    -- Its payloads' types, as declared, once it is declared.
    let parts ← variants.mapM fun (_, payload?) => (payload?.getD #[]).mapM lowerPTy
    let recursive := ctors.any (·.fields.any fun (_, t) => match t with
      | .data q _ => q == path
      | _ => false)
    modify fun s => { s with spec.shapes := s.spec.shapes.insert path { recursive, parts }, typeParams := #[] }
  | .record isPub name fields _ params => do
    let st ← get
    let path := st.module ++ itemName name
    modify fun s => { s with typeParams := params.map (Name.mkSimple ·.name) }
    let mut fs := #[]
    for (f, ty?) in fields do fs := fs.push (Name.mkSimple f.name, ← varTy ty?)
    let parts ← fields.mapM fun (_, ty?) => match ty? with
      | some t => lowerPTy t
      | none => pure (.plain .bool)
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      spec.data := s.spec.data.insert path { path, isRecord := true, ctors := #[{ name := `mk, fields := fs }] }
      spec.shapes := s.spec.shapes.insert path { isRecord := true, parts := #[parts] }
      typeParams := #[] }
  | .newtype isPub name fields _ => do
    let path := (← get).module ++ itemName name
    let some ty := fields[0]? | throw s!"`{showPath path}` has no field"
    let u ← lowerTy ty
    let pt ← lowerPTy ty
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      spec.newtypes := s.spec.newtypes.insert path u
      spec.shapes := s.spec.shapes.insert path { isRecord := true, isNewtype := true, parts := #[#[pt]] } }
  | .typeAlias isPub name ty => do
    let path := (← get).module ++ itemName name
    let t ← lowerTy ty
    let pt ← lowerPTy ty
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
      aliases := s.aliases.insert path t
      declaredAliases := s.declaredAliases.insert path pt }
  | .abstractType isPub name => do
    let path := (← get).module ++ itemName name
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
      spec.sorts := s.spec.sorts.push path }
  | .function isPub name typeParams params result body clauses _ block => do
    let path := (← get).module ++ itemName name
    -- The `use`s of its block, in its scope.
    for m in block.uses do
      match m with
      | .use _ segs glob => declareUseIn segs glob (some path)
      | .useGroup _ pre paths => for p in paths do declareUseIn (pre ++ p) false (some path)
      | _ => pure ()
    let tps := typeParams.map (Name.mkSimple ·.name)
    modify fun s => { s with fnTypeParams := if tps.isEmpty then none else some (path, tps) }
    let r ← varTy result
    let contract := !clauses.isEmpty
    match body with
    | none =>
      -- Its results are values of its result type, as declared.
      let rt ← match result with
        | some t => lowerPTy t
        | none => pure (.plain .bool)
      let constrained := (rt.cons (← get).spec.shapes.find?).isSome
      modify fun s => { s with spec.results := if constrained then s.spec.results.insert path rt else s.spec.results }
      -- A generic one's instances are functions of their own, made at the
      -- applications that use them.
      let generic (ps : Array VTy) : L Unit := do
        unless tps.isEmpty do
          modify fun s => { s with
            spec.generics := s.spec.generics.push (path, tps, ps.map (·.asParams path tps), r.asParams path tps) }
      if !contract then
        let ps ← params.mapM (lowerTy ·.1)
        generic ps
        modify fun s => { s with spec.funs := s.spec.funs.insert path (ps, r) }
      else
        let ps ← params.mapM fun (p, ty?) => return (declName p[0]!, ← varTy ty?)
        generic (ps.map (·.2))
        modify fun s => { s with
          spec.funs := s.spec.funs.insert path (ps.map (·.2), r)
          table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
        -- Over the parameters as inputs, for the checks of its clauses.
        let vars := ps.map fun (x, t) => ({ name := x, ty := t, role := .input, isPub := true } : Var)
        let cs ← lowerContract path (itemName name) false ps vars clauses
        noteBody (itemName name) vars (.lit (.bool true)) cs
    | some body =>
      -- Its function parameters, each an uninterpreted function of its
      -- own for its checks (`Reqs/Lang/HigherOrder#function-parameters`).
      let mut ts : Array (VTy ⊕ (Array VTy × VTy)) := #[]
      let mut fnParams : List (Name × Name) := []
      let mut ps : Array (Name × VTy) := #[]
      for (p, ty?) in params do
        let x := declName p[0]!
        if let some segs := ty?.filter (·[0]?.any (·.name == Parser.fnSeg)) then
          let some (pss, rs) := Fren.Core.splitFnSegs (segs.map (·.name)) | throw "a function type"
          let mut i := 1
          let mut pts := #[]
          for q in pss do
            pts := pts.push (← lowerTy (segs.extract i (i + q.size)))
            i := i + q.size + 1
          let rt ← lowerTy (segs.extract (segs.size - rs.size) segs.size)
          modify fun s => { s with spec.funs := s.spec.funs.insert (path ++ x) (pts, rt) }
          fnParams := fnParams ++ [(x, path ++ x)]
          ts := ts.push (.inr (pts, rt))
        else
          let t ← varTy ty?
          ps := ps.push (x, t)
          ts := ts.push (.inl t)
      if !fnParams.isEmpty then modify fun s => { s with hofs := s.hofs.insert path ts }
      -- Its parameters in order, for an application.
      let all := params.map fun (p, _) => declName p[0]!
      let (b, _) ← lowerExpr { binders := ps.toList.reverse.map fun (n, t) => (n, t, n), fnParams } body
      -- Binders named after the function, so that substituting arguments
      -- never captures a binder of theirs: theirs are a procedure's or another
      -- function's.
      let b := b.renameBound (path ++ ·)
      modify fun s => { s with spec.defs := s.spec.defs.insert path (all.map (path ++ ·), b, r) }
      -- Over the parameters as inputs, for the checks of its tables, and
      -- its contract's, once it can be applied.
      let vars := ps.map fun (x, t) => ({ name := x, ty := t, role := .input, isPub := true } : Var)
      let e := (← lowerExpr { vars, fnParams } body).1
      modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
      let cs ← lowerContract path (itemName name) true ps vars clauses fnParams
      noteBody (itemName name) vars e cs
    modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module }
                             fnTypeParams := none }
  | .const isPub name ty value => do
    let path := (← get).module ++ itemName name
    let t ← lowerTy ty
    let (e, _) ← lowerExpr {} value
    noteBody (itemName name) #[] e
    -- Unknown where it reads an index out of range or a table where no
    -- row holds, which only an interpretation gives a value, or where an
    -- unbounded quantifier has a bound name without a domain, or one too
    -- large (`Reqs/Eval#quantifiers`): then it is the constant, kept as its
    -- expression, wherever it is mentioned, and testing what reads it is an
    -- error if a domain is missing (`Spec.untestable?`).
    let v ← match evalClosed e with
      | some v => pure (Ex.lit v)
      | none =>
        unless e.readsUnspecified || e.unbounded do throw s!"the value of `{showPath path}` cannot be evaluated"
        pure (.const path e)
    modify fun s => { s with
      table := s.table.addItem { kind := .constItem, path, isPub, owner := s.module }
      spec.consts := s.spec.consts.insert path (v, t) }
  | .comp isPub name header members .. => lowerComp isPub name header members
  | .global name binders body => lowerGlobal name binders body
  | .refine name concrete abstract bs => do
    let comp (segs : Array Ident) : L Comp := do
      let some c := (← get).spec.comp? (← resolveComp segs) | throw s!"unknown procedure `{segNames segs}`"
      return c
    let c ← comp concrete
    let a ← comp abstract
    let path := (← get).module ++ itemName name
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
      -- Paths resolve in the module, but in a block with `use`s.
      st := (← (lowerItem item).run { st with scope := st.module }).2
    st := { st with file := st.file + 1 }
  return st

/-- The state with the prelude lowered into it, before every spec
(`Reqs/Lang/Prelude`): its items, in the prelude's module. -/
def preludeState : Except String LState := do
  let chars := Fren.Core.preludeSource.toList.toArray
  let items ← match lex chars with
    | .error e => throw e.msg.headline
    | .ok toks => match parse toks chars with
      | .error e => throw e.msg.headline
      | .ok items => pure items
  let mut st : LState := { module := Fren.Core.preludeModule, scope := Fren.Core.preludeModule }
  for item in items do
    -- Paths resolve in the module, but in a block with `use`s.
    st := (← (lowerItem item).run { st with scope := st.module }).2
  return { st with module := .anonymous, scope := .anonymous }

/-- The spec of the files' items, which the elaborator accepted, with the
names it declares. Lowering files one after another is lowering them
together: `lowerFrom st (a ++ b)` is `lowerFrom st a >>= (lowerFrom · b)`,
which `fren mutate` relies on to lower only the files from a mutant's. -/
def lowerAll (files : Array (Array Item)) : Except String LState := do lowerFrom (← preludeState) files

def lowerFiles (files : Array (Array Item)) : Except String Spec := (·.spec) <$> lowerAll files

def VTy.show : VTy → String
  | .bool => "Bool"
  | .int => "Int"
  | .nat => "Nat"
  | .string => "String"
  | .set t => s!"Set<{t.show}>"
  | .rel a b => s!"Rel<{a.show}, {b.show}>"
  | .seq t => s!"Seq<{t.show}>"
  | .data p [] | .abstract p | .newtype p _ => showPath p
  | .data p args => s!"{showPath p}<{", ".intercalate (args.map VTy.show)}>"
  | .param k => s!"#{k}"

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

/-- Whether `v` is a value of `ty`, looking into a generic type's values,
whose constructions have no type arguments of their own (`VTy.data`). -/
partial def Spec.fits (sp : Spec) : VTy → Val → Bool
  | .bool, .bool _ | .int, .int _ | .string, .str _ => true
  | .nat, .int i => i ≥ 0
  | .set t, .set ms | .seq t, .seq ms => ms.all (sp.fits t)
  | .rel a b, .set ms => ms.all fun | .pair x y => sp.fits a x && sp.fits b y | _ => false
  | .newtype _ u, v => sp.fits u v
  | .abstract s, .abs s' _ => s == s'
  | .data p args, .ctor q idx vs => p == q && match (sp.data.find? p).bind (·.ctors[idx]?) with
    | some c => c.fields.size == vs.size && (c.fields.zip vs).all fun ((_, t), v) => sp.fits (t.subst args) v
    | none => false
  | _, _ => false

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
  let (e, ps) ← match (Parser.expr).run { toks, src := text.toList.toArray } with
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
  -- A construction of a generic type is typed by its values.
  let generic := match t, ty with
    | .data p [], .data q (_ :: _) => p == q
    | _, _ => false
  unless t == ty || empty || generic do throw s!"`{text}` is {a t} `{t.show}`, not {a ty} `{ty.show}`"
  let some v := evalClosed ex | throw s!"`{text}` is not a value"
  if generic && !st.spec.fits ty v then throw s!"`{text}` is not a value of `{ty.show}`"
  return v

end FrenCli.Eval
