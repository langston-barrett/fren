-- keep-sorted start
import FrenCli.Guard
import FrenCli.Parse
import FrenCore.Checking
import FrenCore.Closures
import FrenCore.Enumeration
import FrenCore.Evidence
import FrenCore.Generics
import FrenCore.Global
import FrenCore.Guards
import FrenCore.Lint
import FrenCore.Mentions
import FrenCore.Names
import FrenCore.Patterns
import FrenCore.Quantifier
import FrenCore.Recursion
import FrenCore.Regex
import FrenCore.SeqElems
import FrenCore.SubsetTypes
import FrenCore.Trace
import FrenCore.Traits
import FrenCore.Ty
import FrenCore.TypeFacts
import FrenCore.Typing
-- keep-sorted end

/-!
# Elaboration for `.fren` files

Resolves names with Fren's shared rules (`FrenCore.Names`), type-checks
expressions, and translates each procedure into SMT-LIB formulas over its
variables. Type rules mirror how the Lean-hosted front end elaborates the same
expressions.
-/

open Lean

namespace FrenCli

open Fren.Core (Ty Table Resolved Role Place showPath Msg Severity Lint LintLevel Levels LevelInEffect Named)

def quote (s : String) : String := s!"|{s}|"

/-- The symbol of an abstract type or a function: its path after `::`,
which no variable can be named, so `rename` and `prime` leave it alone. -/
def itemSym (path : Name) : String := quote s!"::{showPath path}"

/-- The SMT-LIB symbol of the enumeration or record at `p`: its path between
`|`s, or, for one of the prelude's types, the Lean type's name, as lean-smt
gives it (`Reqs/Lang/Prelude#smt`). A user's type whose path is a Lean
type's name, as `Option` declared with `!` at the root module is, has its
path after `::`, as an abstract type has, so that the two are apart. -/
def dataSortSym (p : Name) : String :=
  match Fren.Core.leanTypeOf? p with
  | some l => quote l.lean.toString
  | none => Fren.Core.userSortSym (showPath p)

/-- A type's SMT-LIB sort. A set is a unary relation, a set of 1-tuples, so
that relations need no conversions (`Reqs/Cli`). An instance of a generic
type is a sort application, and a type parameter, within its declaration,
a sort parameter (`Reqs/Lang/Generics#meaning`). -/
partial def _root_.Fren.Core.Ty.sort : Ty → String
  | .bool => "Bool"
  -- A `Nat` is an `Int`, with the constraint that it is at least 0
  -- (`natFacts`).
  | .int | .nat => "Int"
  | .string => "String"
  | .set t => s!"(Set (Tuple {t.sort}))"
  | .rel a b => s!"(Set (Tuple {a.sort} {b.sort}))"
  | .seq t => s!"(Seq {t.sort})"
  | .enum p [] | .record p [] => dataSortSym p
  -- A prelude type's instance is the Lean type's, with its arguments in
  -- the Lean type's order (`Fren.Core.LeanType.leanArgs`).
  | .enum p args | .record p args =>
    let args := ((Fren.Core.leanTypeOf? p).map (·.leanArgs args.toArray)).getD args.toArray
    s!"({dataSortSym p} {" ".intercalate (args.toList.map (·.sort))})"
  | .abstract p => itemSym p
  | .param _ n => quote n.toString
  -- Erased to its underlying type (`Reqs/Lang/Items#newtypes`).
  | .newtype _ u => u.sort

/-- The name under which `State.defs` holds the instance of the generic
function at `path` with the type arguments `args`: not a path, whose
segments have no `<`. -/
def instName (path : Name) (args : Array Ty) : Name :=
  Name.mkStr path (Fren.Core.instanceText args)

/-- The SMT-LIB symbol of that instance, as its type arguments print, such
as `|::unwrap_or<Int>|` (`Reqs/Lang/GenericFunctions#meaning`). -/
def instSym (path : Name) (args : Array Ty) : String :=
  quote s!"::{showPath path}{Fren.Core.instanceText args}"

/-- `smt` with each quoted symbol that `repl` maps replaced, but within
string literals. -/
def replaceSymbols (smt : String) (repl : Std.HashMap String String) : String := Id.run do
  let cs := smt.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      -- A string literal, whose `""` is a `"`.
      let mut j := i + 1
      while j < cs.size && !(cs[j]! == '"' && cs[j + 1]? != some '"') do
        j := if cs[j]! == '"' then j + 2 else j + 1
      out := out ++ String.ofList (cs.extract i (j + 1)).toList
      i := j + 1
    else if c == '|' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '|' do j := j + 1
      let sym := String.ofList (cs.extract i (j + 1)).toList
      out := out ++ (repl.getD sym sym)
      i := j + 1
    else
      out := out.push c
      i := i + 1
  return out

def ctorSym (enumPath : Name) (v : Name) : String := quote s!"{showPath enumPath}::{v}"

/-- The selector of the `k`th value of the payload of the variant `v`. -/
def payloadSym (enumPath : Name) (v : Name) (k : Nat) : String := quote s!"{showPath enumPath}::{v}::{k}"

/-- A record's constructor, `|R\{}|`: unlike `|R::mk|`, it cannot be the
selector of a field. -/
def recordCtorSym (r : Name) : String := quote s!"{showPath r}\{}"

def fieldSym (r : Name) (f : Name) : String := quote s!"{showPath r}::{f}"

/-- An enumeration or record, declared as an SMT-LIB datatype. -/
structure DataDecl where
  path : Name
  isRecord : Bool
  /-- The variants, each with its payload's types, or for a record, one
  constructor, `{}`, with its fields. Payload values are named by their
  index. -/
  ctors : Array (Name × Array (Name × Ty))
  /-- Its values can be arbitrarily large (`Reqs/Lang/Types`). -/
  unbounded : Bool
  /-- Its declaration in the prelude, `DataDecl.decl`, and the names of the
  symbols that it declares, computed once by `DataDecl.withPrelude` when it
  is added to the state, rather than each time the prelude is built, which
  `fren mutate` does for every mutant. -/
  text : String := ""
  syms : Array String := #[]
  /-- An ordered enumeration (`Reqs/Lang/Items#enumerations`). -/
  ordered : Bool := false
  /-- Its type parameters, which its payloads' or fields' types mention as
  `Ty.param` (`Reqs/Lang/Generics`). `unbounded` is whether it is unbounded
  whatever its arguments are. -/
  params : Array Name := #[]
  /-- The Lean type that it is, if it is one of the prelude's types, whose
  symbols are lean-smt's (`Reqs/Lang/Prelude#smt`). -/
  lean? : Option Fren.Core.LeanType := none
  deriving Inhabited

/-- The type of `d`'s instance with the arguments `args`. -/
def DataDecl.ty (d : DataDecl) (args : List Ty) : Ty := if d.isRecord then .record d.path args else .enum d.path args

/-- `d`'s constructors, with the types of their payloads or fields in its
instance with the arguments `args`. -/
def DataDecl.instCtors (d : DataDecl) (args : List Ty) : Array (Name × Array (Name × Ty)) :=
  if d.params.isEmpty then d.ctors
  else d.ctors.map fun (c, fs) => (c, fs.map fun (f, t) => (f, t.subst args.toArray))

def DataDecl.ctorSym (d : DataDecl) (c : Name) : String :=
  if let some l := d.lean? then quote (l.ctors[(l.variants.idxOf? c).getD 0]!.toString) else
  -- A generic type's constructors are qualified by their sort, as
  -- `(as C (D Int))`, where cvc5 finds only an unquoted symbol: so theirs
  -- are simple symbols, with `~`, which no Fren name has, for `::`.
  if !d.params.isEmpty then
    "~".intercalate ((showPath d.path).splitOn "::") ++ (if d.isRecord then "~" else s!"~{c}")
  else if d.isRecord then recordCtorSym d.path else FrenCli.ctorSym d.path c

def DataDecl.selSym (d : DataDecl) (c : Name) (k : Nat) : String :=
  if let some l := d.lean? then quote ((l.selectors[(l.variants.idxOf? c).getD 0]!)[k]!) else
  if d.isRecord then fieldSym d.path d.ctors[0]!.2[k]!.1 else payloadSym d.path c k

/-- The constructor `c` of `d`'s instance with the arguments `args`: of a
generic type, qualified by its sort, which SMT-LIB needs for a constructor
of a parametric datatype, `(as C (D A))`, applied as `((as C (D A)) x)`. -/
def DataDecl.ctorOf (d : DataDecl) (args : List Ty) (c : Name) : String :=
  if args.isEmpty then d.ctorSym c else s!"(as {d.ctorSym c} {(d.ty args).sort})"

/-- The constructor `c` of `d`'s instance with the arguments `args`,
applied to `xs`. -/
def DataDecl.build (d : DataDecl) (args : List Ty) (c : Name) (xs : List String) : String :=
  if xs.isEmpty then d.ctorOf args c else s!"({d.ctorOf args c} {" ".intercalate xs})"

/-- Whether `smt` is the variant `idx`: that it equals the variant built
from its own payload. cvc5 rejects the tester `(_ is |E::V|)` of a quoted
constructor. -/
def DataDecl.tester (d : DataDecl) (idx : Nat) (smt : String) (args : List Ty := []) : String :=
  let (c, fs) := d.ctors[idx]!
  let sels := (List.range fs.size).map fun k => s!"({d.selSym c k} {smt})"
  s!"(= {smt} {d.build args c sels})"

/-- The position of `smt`'s variant among the variants of the ordered
enumeration `d`, an `Int`: a conditional on each variant but the last, so
that comparing two values compares their positions without quantifiers.
Fren generates the same term in Lean (`Fren.ordinalTerm`). -/
def DataDecl.ordinal (d : DataDecl) (smt : String) (args : List Ty := []) : String :=
  (List.range (d.ctors.size - 1)).foldr (init := toString (d.ctors.size - 1)) fun k acc =>
    s!"(ite {d.tester k smt args} {k} {acc})"

/-- `(declare-datatype ...)`, or for a generic type, a parametric datatype,
`(declare-datatypes ((D n)) ((par (A ...) (...))))`, as lean-smt declares
the Lean inductive type (`Reqs/Lang/Generics#meaning`). -/
def DataDecl.decl (d : DataDecl) : String :=
  -- A prelude type's is lean-smt's: its constructors in the Lean type's
  -- order, and its parameters named as the Lean type's.
  let (order, params) := match d.lean? with
    | some l => (l.ctorOrder, l.argOrder.zip (l.leanParams.map Name.mkSimple))
    | none => (Array.range d.ctors.size, d.params.zipIdx.map fun (p, k) => (k, p))
  let paramSort (t : Ty) : String := match t with
    | .param k _ => quote (((params.find? (·.1 == k)).map (·.2)).getD (d.params[k]?.getD .anonymous)).toString
    | t => t.sort
  let ctors := " ".intercalate <| order.toList.map fun i =>
    let (c, fs) := d.ctors[i]!
    let sels := String.join <| (fs.toList.zipIdx).map fun ((_, t), k) => s!" ({d.selSym c k} {paramSort t})"
    s!"({d.ctorSym c}{sels})"
  if d.params.isEmpty then s!"(declare-datatype {dataSortSym d.path} ({ctors}))\n" else
  let ps := " ".intercalate (params.toList.map (quote ·.2.toString))
  s!"(declare-datatypes (({dataSortSym d.path} {d.params.size})) ((par ({ps}) ({ctors}))))\n"

/-- `d` with its declaration and the names of the symbols that it declares:
the datatype, its constructors and its selectors. -/
def DataDecl.withPrelude (d : DataDecl) : DataDecl :=
  let unquote (sym : String) : String := if sym.startsWith "|" then ((sym.drop 1).dropEnd 1).toString else sym
  let ctors := d.ctors.flatMap fun (c, fs) => #[d.ctorSym c] ++ (List.range fs.size).toArray.map (d.selSym c)
  { d with text := d.decl, syms := (#[dataSortSym d.path] ++ ctors).map unquote }

/-- The contract of a function: the SMT-LIB symbols of its preconditions
and postconditions, each with its name, which the prelude defines over the
function's parameters, and whether the function is defined
(`Reqs/Lang/Items#contracts`). -/
structure Contract where
  pres : Array (Name × String) := #[]
  posts : Array (Name × String) := #[]
  defined : Bool := false
  deriving Inhabited

/-- The SMT-LIB symbol of the clause `n` of the contract of the function at
`path`: not a Fren path, which never contains `#`. -/
def clauseSym (path n : Name) : String := quote s!"::{showPath path}#{n}"

/-! ## Subset types' constraints in SMT-LIB -/

/-- The integer `v` in SMT-LIB. -/
def smtInt (v : Int) : String := if v < 0 then s!"(- {-v})" else toString v

/-- The conjunction of `ts` in SMT-LIB, `true` for none. -/
def smtAll (ts : Array String) : String :=
  match ts with
  | #[] => "true"
  | #[t] => t
  | ts => s!"(and {" ".intercalate ts.toList})"

/-- That `x`, of type `ty`, matches the pattern `p`, in SMT-LIB, where
`dts` gives the enumerations: as a pattern test is, `resolvePattern`. -/
partial def patSmt (dts : Name → Option DataDecl) (ty : Fren.Core.Ty) (p : Fren.Core.Pat) (x : String) : String :=
  match p with
  | .wild _ => "true"
  | .bool b => if b then x else s!"(not {x})"
  | .int lo hi =>
    if lo.isSome && lo == hi then s!"(= {x} {smtInt lo.get!})" else
    smtAll (lo.toArray.map (s!"(<= {smtInt ·} {x})") ++ hi.toArray.map (s!"(<= {x} {smtInt ·})"))
  | .str v => s!"(= {x} {Fren.Core.smtStringLit v})"
  | .ctor idx args => Id.run do
    let .enum ep targs := ty | return "true"
    let some d := dts ep | return "true"
    let (c, fs) := d.ctors[idx]!
    let tests := #[d.tester idx x targs] ++ (args.zipIdx.filterMap fun (a, k) =>
      -- With an instance's arguments for its type parameters.
      let t := patSmt dts (fs[k]!.2.subst targs.toArray) a s!"({d.selSym c k} {x})"
      if t == "true" then none else some t)
    return smtAll tests
  | .or alts =>
    let ts := alts.map (patSmt dts ty · x)
    if ts.contains "true" then "true" else if ts.size == 1 then ts[0]! else s!"(or {" ".intercalate ts.toList})"

/-- The constraint `c` of `x` in SMT-LIB (`Fren.Core.Cons`), where `dts`
gives the enumerations and records, and `depth` numbers the bound
variables of the quantifiers around it. -/
partial def consSmt (dts : Name → Option DataDecl) (c : Fren.Core.Cons) (x : String) (depth : Nat := 0) : String :=
  match c with
  | .predicate i => s!"({itemSym i.predicate} {x})"
  | .pat ty p => patSmt dts ty p x
  | .atLeast0 => s!"(>= {x} 0)"
  | .fields path _ cs => Id.run do
    let some d := dts path | return "true"
    return smtAll (cs.map fun (k, c) => consSmt dts c s!"({d.selSym `mk k} {x})" depth)
  -- A newtype is its underlying type, to the solver.
  | .newtype _ c => consSmt dts c x depth
  | .payloads path args cs => Id.run do
    let some d := dts path | return "true"
    return smtAll (cs.map fun (v, k, c) =>
      s!"(=> {d.tester v x args} {consSmt dts c s!"({d.selSym d.ctors[v]!.1 k} {x})" depth})")
  | .elems seq e c =>
    let b := quote s!"#e{depth}"
    if seq then
      s!"(forall (({b} Int)) (=> (and (<= 0 {b}) (< {b} (seq.len {x}))) {consSmt dts c s!"(seq.nth {x} {b})" (depth + 1)}))"
    else
      s!"(forall (({b} {e.sort})) (=> (set.member (tuple {b}) {x}) {consSmt dts c b (depth + 1)}))"
  | .pairs a b ca cb =>
    let (u, v) := (quote s!"#a{depth}", quote s!"#b{depth}")
    let parts := (ca.map (consSmt dts · u (depth + 1))).toArray ++ (cb.map (consSmt dts · v (depth + 1))).toArray
    s!"(forall (({u} {a.sort}) ({v} {b.sort})) (=> (set.member (tuple {u} {v}) {x}) {smtAll parts}))"
  | .all cs => smtAll (cs.map (consSmt dts · x depth))

/-- The term that a function's fact is about, in its template
(`State.funFacts`), which no variable can be named. -/
def factHole : String := quote "#x"

/-- A procedure variable: one of its own, or one of a call's (`w.x`). -/
structure CVar where
  name : Name
  role : Role
  /-- Shown in counterexamples. -/
  isPub : Bool
  /-- A `det` variable of the procedure itself. -/
  isDet : Bool := false
  ty : Ty
  span : Span
  /-- The definition of a defined output of the procedure itself. -/
  defn? : Option Expr := none
  /-- Its type as declared, with its patterns. -/
  ptype : Fren.Core.PTy := default
  /-- The constraint that its type brings, over it (`Reqs/Lang/Procedures#subset-types`). -/
  fact? : Option String := none
  deriving Inhabited

/-- Closed definition-site templates; actual argument expressions are bound
simultaneously outside these formulas, preventing capture by body binders. -/
structure NamedClause where
  file : Nat
  name : String
  span : Span
  formula : String
  branches : Array (Fren.Core.BranchGroup String) := #[]
  groups : Array (Fren.Core.MemberGroup String) := #[]
  indexes : Array (Span × String × Option (String × Bool)) := #[]
  tables : Array (Span × Fren.Core.TableGoal × String) := #[]
  deriving Inhabited, BEq

structure NamedPredicate where
  sourcePath : Name
  params : Array Name
  clauses : Array NamedClause
  whole? : Option NamedClause := none
  deriving Inhabited, BEq

structure CProp where
  file? : Option Nat := none
  sourceRef : Bool := true
  kind : PropKind
  name : Name
  span : Span
  smt : String
  trigger? : Option String
  triggerSpan? : Option Span
  /-- For a refinement claim (`refines`): its abstraction, the procedure
  whose realizability its checks rest on (`Reqs/Evidence`). -/
  abstraction? : Option Name := none
  deriving Inhabited

/-- A call, with formulas over the calling procedure's variables. -/
structure CInst where
  name : Name
  comp : Name
  span : Span
  bindings : String
  behaviour : String
  assumes : Array (Name × String)
  /-- Which of `assumes` are the obligations of its inputs' types, with
  those types (`Fren.Core.Inst.typed`). -/
  typed : Array (Name × String) := #[]
  /-- One of those obligations quantifies over a collection's elements. -/
  bounded : Bool := false
  deriving Inhabited

structure CComp where
  distributed : Array Name := #[]
  branchGroups : Array (Fren.Core.BranchGroup String) := #[]
  memberGroups : Array (Fren.Core.MemberGroup String) := #[]
  subset? : Option Name := none
  subsetInvariant? : Option Name := none
  path : Name
  file : Nat
  span : Span
  /-- A global expectation in the short form, `expect n: e`, whose path is
  its module and whose one constraint is named after it, rather than one
  with a block, which is checked as a procedure is. -/
  short : Bool := false
  /-- A global expectation with a block (`Fren.Core.Comp.global`). -/
  global : Bool := false
  /-- For an expectation of a trait: the trait's laws, each a closed
  formula (`Fren.Core.Comp.laws`). -/
  laws : Array (Name × String) := #[]
  /-- Its own variables in declaration order, then each call's. -/
  vars : Array CVar
  props : Array CProp
  insts : Array CInst := #[]
  /-- Each defined output and its definition, each mentioning only earlier
  ones. -/
  defs : Array (Name × String) := #[]
  /-- No construct of it is outside the decidable core
  (`view::inconclusive_advice`). -/
  decidable : Bool := true
  /-- Each index of its constraints, definitions and bindings: the item it
  is in, where that is, the index's span, and the formula that it is in
  range (`check::definedness`). -/
  indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) := #[]
  /-- Each question about the rows of a table or the arms of a `match` of
  its constraints, definitions and bindings: the item it is in, where that
  is, where it is reported, the question, and the formula that it holds
  (`check::completeness`, `check::disjointness`, `check::reachability`). -/
  tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) := #[]
  /-- It, or one of its calls, applies a relational operator. -/
  relational : Bool := false
  /-- It, or one of its calls, uses `card`. -/
  counts : Bool := false
  /-- The checks that are tested rather than asked of the solver
  (`Reqs/Check#checking-by-testing`). -/
  tested : Fren.Core.Tested := {}
  /-- The checks that are enumerated rather than asked of the solver
  (`Reqs/Check#checking-by-enumeration`), and the size bound. -/
  enumerated : Fren.Core.Tested := {}
  enumSize : Nat := Fren.Core.Enumeration.defaultSize
  /-- The applications of uninterpreted functions whose result is a `Nat`,
  or that have postconditions, in its constraints, definitions, bindings
  and calls: each brings its facts (`Fren.Core.appFactsWith`). -/
  natApps : Array String := #[]
  /-- For the body or contract of a function, or the value of a constant:
  its name, which the evaluator's counterpart has (`Eval.Comp.body?`). -/
  bodyOf? : Option Name := none
  /-- For the body and contract of a function: the function, whose
  preconditions are the procedure's assumptions, and, if it is defined, whose
  postconditions are its guarantees, each named after the function and
  the clause (`check::postcondition`). -/
  fn? : Option Name := none
  /-- For the contract of a generic function without a body, checked once,
  at its type parameters (`Fren.Core.Comp.generic`). -/
  generic : Bool := false
  /-- Its queries use finite-model finding: the contract of an instance of
  a generic function without a body at another one's type parameters
  (`Fren.Core.Ty.hasTypeParam`). -/
  finiteModel : Bool := false
  /-- What each application of a function, or read of a payload, whose
  result brings a constraint brings, by its head symbol, about `factHole`
  (`State.funFacts`). -/
  funFacts : Std.HashMap String String := {}
  /-- Whether a query quantifies over a collection's elements, which sets
  `fmf-bound` (`CComp.bounded`). -/
  bounded : Bool := false
  /-- It has an unbounded quantifier with a bound name that has a domain,
  directly, through a call or through a defined function, which sets
  `fmf-bound` (`Reqs/Lang/Quantifiers#guards`). -/
  guarded : Bool := false
  /-- This function uses simultaneous Hoare induction. -/
  recursive : Bool := false
  deriving Inhabited

def conj (fs : Array String) : String :=
  if fs.isEmpty then "true" else if fs.size == 1 then fs[0]! else s!"(and {" ".intercalate fs.toList})"

/-- Everything a procedure says about its variables: assumptions, requirements
and calls. -/
def CComp.meaning (c : CComp) : String :=
  conj <| c.defs.map (fun (d, e) => s!"(= {quote d.toString} {e})")
    ++ (c.props.filter fun p => p.kind == .assume || p.kind == .ensure).map (·.smt)
    ++ c.insts.map fun i => conj #[i.bindings, i.behaviour]

/-- What the `Nat` variables of `c` bring (`Reqs/Check`): that each that is
not defined is at least 0 (`lang::nat_variable`). `outputs` gives those of
its own outputs, and otherwise those of the rest. Its applications' facts
are each query's own (`Fren.Core.natAppFacts`). -/
def CComp.natFacts (c : CComp) (outputs : Bool) : Array (Name × String) :=
  let vars := c.vars.filter fun v => match Fren.Core.natBrought (v.role == .output) v.defn?.isSome with
    | .nothing => false
    | .guarantee => outputs
    | .assumption => !outputs
  -- Each variable's `Nat`'s, then its type's (`Reqs/Check`).
  vars.flatMap fun v =>
    (if v.ty == .nat then #[(`nat, s!"(>= {quote v.name.toString} 0)")] else #[]) ++ (v.fact?.map (`type, ·)).toArray

/-- `w.x` as a `Name`. -/
def identName (s : String) : Name := (s.splitOn ".").foldl Name.mkStr .anonymous

/-- `smt` in pieces, in order: the text between quoted symbols, and the
name of each quoted symbol. A `|` in a string literal, where `""` is a `"`,
does not quote. -/
def quotedPieces (smt : String) : Array (String ⊕ String) := Id.run do
  let cs := smt.toList.toArray
  let mut out := #[]
  let mut text := ""
  let mut i := 0
  while h : i < cs.size do
    let c := cs[i]
    if c == '"' then
      let mut j := i + 1
      while j < cs.size && !(cs[j]! == '"' && cs[j + 1]? != some '"') do
        j := if cs[j]! == '"' then j + 2 else j + 1
      text := text ++ String.ofList (cs.extract i (j + 1)).toList
      i := j + 1
    else if c == '|' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '|' do j := j + 1
      out := (out.push (.inl text)).push (.inr (String.ofList (cs.extract (i + 1) j).toList))
      text := ""
      i := j + 1
    else
      text := text.push c
      i := i + 1
  return out.push (.inl text)

/-- Replaces each quoted symbol of `smt` with `f` of its name
(`quotedPieces`). -/
def substQuoted (f : String → String) (smt : String) : String :=
  String.join ((quotedPieces smt).toList.map fun | .inl text => text | .inr name => f name)

/-- Applies `f` to the name of each quoted symbol of `smt`. -/
def mapQuoted (f : String → String) (smt : String) : String := substQuoted (quote ∘ f) smt

/-- The name `s` of a quoted symbol as the solver is given it
(`Reqs/Cli#solver-queries`): renamed if it is a theory's symbol
(`Fren.Core.smtName`), and quoted, but for lean-smt's symbols of the
prelude's types, which are written as lean-smt writes them, without `|`s
(`Reqs/Lang/Prelude#smt`). -/
def solverSym (s : String) : String :=
  let n := Fren.Core.smtName s
  if Fren.Core.leanSymbols.contains n then n else quote n

/-- `smt` with each quoted symbol as the solver is given it (`solverSym`). -/
def solverText (smt : String) : String := substQuoted solverSym smt

/-- The names of the quoted symbols of `smt`, as `mapQuoted` finds them
(`quotedPieces`), without building the text between them. It reads the
UTF-8 bytes: `"` and `|` are ASCII, and no byte of a character that is not
ASCII is one of them, so the symbols are found where `quotedPieces` finds
them, and each is whole characters. -/
def quotedSymbols (smt : String) : Array String := Id.run do
  let bs := smt.toUTF8
  let mut out := #[]
  let mut i := 0
  while i < bs.size do
    let c := bs[i]!
    if c == '"'.toUInt8 then
      -- A string literal, in which `""` is a `"`.
      let mut j := i + 1
      while j < bs.size && !(bs[j]! == '"'.toUInt8 && bs[j + 1]? != some '"'.toUInt8) do
        j := if bs[j]! == '"'.toUInt8 then j + 2 else j + 1
      i := j + 1
    else if c == '|'.toUInt8 then
      let mut j := i + 1
      while j < bs.size && bs[j]! != '|'.toUInt8 do j := j + 1
      out := out.push (String.fromUTF8! (bs.extract (i + 1) j))
      i := j + 1
    else
      i := i + 1
  return out

/-- Renames the variables `vars` in `smt` to `pfx.x`. Variables are quoted
symbols, as are enum constructors, which contain `::` and so never clash. -/
def rename (pfx : Name) (vars : Array CVar) (smt : String) : String :=
  let names := vars.map (·.name.toString)
  mapQuoted (fun p => if names.contains p then (pfx ++ identName p).toString else p) smt

structure Diag where
  file : Nat
  span : Span
  severity : Severity := .error
  msg : Msg
  /-- The lint that reported it, if any. -/
  lint? : Option Lint := none
  /-- `fren fix` fixes it. -/
  fixed : Bool := false

/-- Where a `use` is written, for `fren fix`. -/
structure UseLoc where
  /-- The whole item, which a group shares with its other `use`s. -/
  item : Span
  /-- What removing it removes: the item, and any `set_option ... in`
  before it. -/
  removal : Span
  /-- Its path, without `::*`. -/
  path : Span
  /-- In a group, the path before `::{`. -/
  pre? : Option Span := none
  deriving Inhabited

/-- A `tested` or `trusted` claim. `tested` claims' files are checked by
`fren` itself, which can read them (`checkClaims`). -/
structure CClaim where
  file : Nat
  tested : Bool
  comp : Name
  texts : Array (String × Span)
  deriving Inhabited

def toRange (sp : Span) : Fren.Core.Range := { start := sp.start, stop := sp.stop }

/-- The kind of a constraint, or cover goal, that `duplicate_constraint`
compares. -/
def PropKind.core : PropKind → Fren.Core.ConstraintKind
  | .assume => .assume
  | .ensure => .ensure
  | .expect => .expect
  | .cover => .cover

/-- Where the word that ends before `pos`, but for whitespace, starts: the
keyword of a member, before its name. -/
def wordStart (src : Array Char) (pos : Nat) : Nat := Id.run do
  let mut i := pos
  while i > 0 && src[i - 1]!.isWhitespace do i := i - 1
  while i > 0 && Fren.Core.isWordChar src[i - 1]! do i := i - 1
  return i

/-- `stop`, or the end of its line if a `--` comment follows it there,
which a removal takes with it. -/
def withLineComment (src : Array Char) (stop : Nat) : Nat := Id.run do
  let mut i := stop
  while i < src.size && (src[i]! == ' ' || src[i]! == '\t') do i := i + 1
  unless src[i]? == some '-' && src[i + 1]? == some '-' do return stop
  while i < src.size && src[i]! != '\n' do i := i + 1
  return i

/-- The string literals and comments of `src` that `invisible_characters`
reports (`lint::invisible_character`), and the string literals that
`needless_raw_strings` and `non_ascii_literal` report, and the raw string
literals that `needless_raw_string_hashes` reports, each with its lint and
message, in order, from its tokens `toks` and the spans of its comments,
as `lexWithComments` gives them. -/
def literalLints (src : Array Char) (toks : Array Token) (comments : Array Span) : Array (Lint × Span × Msg) :=
  let lits := toks.filterMap fun t => if t.tok matches .str _ then some (t.span, false) else none
  let all := (lits ++ comments.map (·, true)).qsort (·.1.start < ·.1.start)
  all.flatMap fun (sp, comment) =>
    let text := String.ofList (src.extract sp.start sp.stop).toList
    let invisible := (Fren.Core.invisibleFix? comment text).toArray.map fun (found, fixed) =>
      (Lint.invisibleCharacters, sp, Fren.Core.invisibleMsg comment found fixed)
    let hashes := if comment then #[] else (Fren.Core.fewerHashes? text).toArray.map fun fixed =>
      (Lint.needlessRawStringHashes, sp, Fren.Core.needlessRawHashesMsg fixed)
    invisible ++ hashes ++ if comment then #[] else (Fren.Core.literalMsgs text).map fun (l, msg) => (l, sp, msg)

/-- A report of `manual_nat`, kept until the end of the file, where an
call or a refinement may keep its variable an `Int`
(`lint::manual_nat`): the procedure, the variable and the report. -/
structure NatReport where
  comp : Name
  var : String
  report : Fren.Core.LintReport Span
  deriving Inhabited

/-- The edits that fix a lint's message, which `fren fix` makes where the
message is reported. -/
structure LintFix where
  lint : Lint
  /-- Where the message is. -/
  span : Span
  edits : Array (Fren.Core.Range × String)
  /-- A message whose fix would undo this one's: if `fren fix` fixes it,
  this one is not fixed. -/
  unless? : Option (Lint × Span) := none
  deriving Inhabited

/-- A binder of a `match` pattern, a quantifier's bound name, or a name of a
`let` or `where` (`isDef`), in scope. -/
structure CBinder where
  name : Name
  /-- Its value: the selector applied to the scrutinee, the symbol of the
  SMT-LIB `let` that defines the name, or for a bound name, a symbol that
  each instance replaces with a value. -/
  smt : String
  ty : Ty
  /-- Its scrutinee or definition, and the number of binders in scope
  there: mentioning it counts as mentioning what that mentions. A bound
  name has none, and mentions nothing. -/
  scrutinee : Option Expr
  outer : Nat
  isDef : Bool := false
  /-- For a name, the indexes of its definition, each with the formula that
  it is in range, guarded only within the definition: a mention puts them
  under its own guards (`Reqs/Lang/Let#meaning`). -/
  obligations : Array (Span × String × Option (String × Bool)) := #[]
  /-- Likewise, the questions about the rows of its definition's tables. -/
  tableObligations : Array (Span × Fren.Core.TableGoal × String) := #[]
  /-- A bound name of a type that is not listed, of an unbounded quantifier,
  whose symbol the solver's quantifier binds: within the body, it mentions
  itself, as a variable does. -/
  unbounded : Bool := false
  /-- For a binder in a defined function's body, the position of the
  parameter that it is bound from a payload of, directly or nested
  (`lang::structural_recursion`). -/
  payloadOf? : Option Nat := none

/-- A generic defined function (`Reqs/Lang/GenericFunctions`): what its
applications need to infer their type arguments, and to unfold it at its
instances. -/
structure GenericFn where
  params : Array Name
  /-- Its parameters' and result's declared types, which mention the type
  parameters as `Ty.param`. -/
  declared : Array Ty
  result : Ty
  /-- Its `define-fun`'s parameters and body, in which each type parameter
  is an abstract type of its own (`Fren.Core.typeParamPath`). -/
  vars : Array (Name × Ty) := #[]
  body : String := ""
  /-- Its contract's clauses' `define-fun`s, as `State.clauseDefs` has them. -/
  clauses : Array (String × Array (Name × Ty) × String) := #[]
  /-- The generic functions that its body and contract apply, each with
  its type arguments, which may mention its own type parameters. -/
  calls : Array (Name × Array Ty) := #[]
  /-- Its result's declared type, with its patterns, which mentions the
  type parameters as `Ty.param`. -/
  resultP : Fren.Core.PTy := default
  /-- The file that declares it. -/
  file : Nat := 0
  /-- It has a body. One without is uninterpreted: each of its instances is
  an unknown function of its own, a `declare-fun`
  (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`). -/
  defined : Bool := true
  deriving Inhabited

/-- A closure given for a function parameter, as the solver sees it, with
its body's obligations over its parameters' symbols (`elabClosure`). -/
structure ClosureArg where
  closure : Fren.Core.SClosure
  indexes : Array (Span × String × Option (String × Bool)) := #[]
  tables : Array (Span × Fren.Core.TableGoal × String) := #[]
  deriving Inhabited

/-- A higher-order defined function (`Reqs/Lang/HigherOrder`): what its
applications need to unfold it. -/
structure HigherOrderFn where
  /-- Its type parameters, if it is generic. -/
  typeParams : Array Name := #[]
  /-- Its parameters, in order: each one's name, its symbol, and its type as
  its signature declares it, which mentions the type parameters as
  `Ty.param`. A function parameter's symbol is that of the uninterpreted
  function that it is for the function's own checks. -/
  params : Array (Name × String × Fren.Core.HoParam) := #[]
  result : Ty := .bool
  /-- Its body, over its value parameters' symbols, in which each type
  parameter is an abstract type of its own. -/
  body : String := ""
  /-- Its preconditions' bodies, as `body` is. -/
  pres : Array (Name × String) := #[]
  /-- The generic functions that its body and contract apply, each with its
  type arguments, which may mention its own type parameters. -/
  calls : Array (Name × Array Ty) := #[]
  deriving Inhabited, BEq

structure State where
  itemExcludeGroups : Array Name := #[]
  itemBranches : Array (Fren.Core.BranchGroup String) := #[]
  itemMemberGroups : Array (Fren.Core.MemberGroup String) := #[]
  inSubset : Bool := false
  table : Table := {}
  claims : Array CClaim := #[]
  module : Name := .anonymous
  /-- The scope that paths resolve in: the current module, or the
  procedure being elaborated, if it has `use`s. -/
  scope : Name := .anonymous
  file : Nat := 0
  comps : Array CComp := #[]
  /-- Each constant's value, as SMT-LIB, and type. -/
  consts : NameMap (String × Ty) := {}
  /-- The value of each constant whose value is an integer constant
  expression (`Reqs/Lang/Expressions#division-and-remainder`). -/
  constInts : NameMap Int := {}
  /-- The abstract types, in order. -/
  sorts : Array Name := #[]
  /-- The laws of the trait being elaborated so far, each with its closed
  formula, whether it is in the decidable core, the applications in it
  that bring facts, and whether it sets `fmf-bound` (`Reqs/Lang/Traits`). -/
  traitLaws : Array (Name × String × Bool × Array String × Bool) := #[]
  /-- Each uninterpreted function's parameter and result types, in order. -/
  funs : Array (Name × Array Ty × Ty) := #[]
  /-- Each defined function's parameters and result type, and its body over
  the parameters, in order. -/
  defs : Array (Name × Array (Name × Ty) × Ty × String) := #[]
  namedPredicates : NameMap NamedPredicate := {}
  namedOccurrences : Std.HashMap String Nat := {}
  contractIndexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) := #[]
  /-- Structural recursions, used opaquely with one-step ground equations. -/
  recursiveDefs : Std.HashSet Name := {}
  /-- The contracts of the functions that have one, by path
  (`Reqs/Lang/Items#contracts`). -/
  contracts : NameMap Contract := {}
  /-- Each clause of a contract, as its SMT-LIB symbol, the function's
  parameters, and the clause over them, in order (`State.prelude`). -/
  clauseDefs : Array (String × Array (Name × Ty) × String) := #[]
  /-- The enumerations and records, in order. -/
  datatypes : Array DataDecl := #[]
  /-- The newtypes, each with its underlying type. -/
  newtypes : NameMap Ty := {}
  /-- The newtypes declared `ordered` (`Reqs/Lang/Items#ordered-declarations`). -/
  orderedNewtypes : Array Name := #[]
  /-- The type aliases, each with the type it names (`Reqs/Lang/Items#type-aliases`). -/
  aliases : NameMap Fren.Core.PTy := {}
  /-- The fields of each record and newtype, and the payloads of each
  enumeration, as declared, for their constraints (`Fren.Core.DataShape`). -/
  shapes : NameMap Fren.Core.DataShape := {}
  /-- Each function's parameters' and result's types, as declared. -/
  funPTys : NameMap (Array Fren.Core.PTy × Fren.Core.PTy) := {}
  /-- The constraint that each application of an uninterpreted function
  whose result's type brings one brings, by the function's symbol, as
  SMT-LIB about `factHole` (`Reqs/Check`). -/
  funFacts : Std.HashMap String String := {}
  /-- The functions, by symbol, whose applications' facts quantify over a
  collection's elements. -/
  quantifiedFns : Std.HashSet String := {}
  /-- The spans of the function applications elaborated so far
  (`lang::constant`). -/
  applied : Array Span := #[]
  /-- Global expectations, each a `CComp` whose path is its module, with an
  call per binder and the expectation as its only constraint. -/
  globals : Array CComp := #[]
  /-- The bodies of defined functions and the values of constants that have
  tables, each as a procedure whose path is its module, with the function's
  parameters as inputs, for the checks of its tables (`check::applies`). -/
  bodies : Array CComp := #[]
  diags : Array Diag := #[]
  /-- The static errors of the current item so far, of its members that
  failed on their own (`Reqs/View#static-errors`). -/
  itemErrors : Array Diag := #[]
  /-- The lint levels from the command line, with which each file starts. -/
  cliLevels : Levels := Levels.defaults
  /-- The lint levels in effect, in the current file. -/
  levels : Levels := Levels.defaults
  /-- The current file's `use`s, the names resolved through imports, its
  expectations and its other lints (`Fren.Core.Lint`). -/
  useRecords : Array (Fren.Core.UseRecord × Span) := #[]
  used : Array Fren.Core.UsedName := #[]
  expectations : Array (Fren.Core.ExpectationRecord × Span) := #[]
  lintReports : Array (Fren.Core.LintReport Span) := #[]
  /-- The variables, parameters, calls and binders that the item being
  elaborated declares (`many_single_char_names`, `similar_names`). -/
  declared : Array (Name × Span) := #[]
  /-- For `fren fix`: where each of `useRecords` is written, and what
  removing each of `expectations` removes. -/
  useLocs : Array UseLoc := #[]
  expectationRemovals : Array Span := #[]
  /-- The lints that `fren fix` fixes in the current file. -/
  fixing : Array Lint := #[]
  /-- The current file's text. -/
  src : Array Char := #[]
  /-- Where the outermost `set_option ... in` around the current item starts. -/
  settingStart? : Option Nat := none
  /-- `set_option fren.evidence` in effect for the current item: its value,
  checked where it applies (`Reqs/Check#checking-by-testing`), and the
  value's span. -/
  evidence? : Option (String × Span) := none
  /-- The size bound of enumeration in effect (`fren.enumeration.size`). -/
  enumSize : Nat := Fren.Core.Enumeration.defaultSize
  /-- Where the current item starts. -/
  itemStart : Nat := 0
  /-- The string literals and comments of the current item that
  `literalLints` reports, each with its lint and message, until the item
  is elaborated at its level. -/
  literals : Array (Lint × Span × Msg) := #[]
  /-- The global expectations of the current file: each one's module, name
  and text (`duplicate_constraint`). -/
  globalTexts : Array (Name × String × String) := #[]
  /-- The edits of `fren fix`, by file. -/
  edits : Array (Nat × Fren.Core.Range × String) := #[]
  /-- The current file's private enumerations and constants, and the items
  that paths in it resolve to (`dead_code`). -/
  items : Array (Fren.Core.ItemRecord × Span) := #[]
  /-- The function parameters of the file's private higher-order functions,
  and what the applications give them, by where each is written
  (`needless_higher_order`). -/
  hofParams : Array (Fren.Core.HofParamRecord × Span) := #[]
  fnArgs : Array (Fren.Core.FnArgRecord × Span) := #[]
  usedItems : Array Name := #[]
  /-- The edits that fix the lints whose message suggests a replacement:
  the collection, membership, index, rewriting and match lints. -/
  lintFixes : Array LintFix := #[]
  /-- The current file's lint settings, what removing each removes, and
  those in effect at an item (`unused_lint_setting`). -/
  settings : Array (Fren.Core.SettingRecord × Span) := #[]
  settingRemovals : Array Span := #[]
  seenSettings : Array Nat := #[]
  /-- The current file's assumptions that `unused_assumption` may fire on,
  and what its global expectations read through calls, and its
  refinements of their abstractions: each read's procedure and input. -/
  assumptions : Array (Fren.Core.AssumptionRecord × Span) := #[]
  globalReads : Array (Name × Name) := #[]
  /-- The reports of `manual_nat` in the file so far. -/
  natReports : Array NatReport := #[]
  /-- The variables that calls in the file keep `Int`s. -/
  natKept : Array (Name × String) := #[]
  /-- Where the comparisons of `Bool`s in the expression being elaborated
  are, for `bool_equality`. -/
  boolEqs : Array Span := #[]
  /-- Where the conditions of `if`s and the operands of `*` in the
  expression being elaborated that mention a variable or an uninterpreted
  function are, and what each mentions, for `branches_sharing_code`. -/
  mentioning : Array (Span × List Fren.Core.Mention) := #[]
  /-- Where the variants without payloads in the expression being
  elaborated are, with their paths, for `contradictory_comparisons`. -/
  variants : Array (Span × String) := #[]
  /-- Where the calls of `abs` in the expression being elaborated end, for
  `invalid_upcast_comparisons`. -/
  absEnds : Array Nat := #[]
  /-- What is known of the variants of ordered enumerations, and of the
  newtypes built and read, in the expression being elaborated, for the
  lints of ordered enumerations and newtypes. -/
  facts : Array (Span × Fren.Core.NodeFact) := #[]
  /-- Where the bound names of quantifiers are mentioned, each with the
  bound name's symbol, for `trivial_quantifier`. -/
  boundMentions : Array (Span × String) := #[]
  /-- The current file's trailing commas that `unnecessary_trailing_comma`
  reports, each with the `}` or `]` after it. -/
  trailingCommas : Array (Span × String) := #[]
  /-- The span of the item being elaborated, up to where the next starts. -/
  itemSpan : Span := ⟨0, 0⟩
  /-- The orderings, by the type they compare, for the lints of integers. -/
  ordereds : Array (Span × Fren.Core.Ordered) := #[]
  /-- Some type or literal is a `String`, so the queries need the theory of
  strings (`cli::logic`). -/
  usesStrings : Bool := false
  /-- The type parameters of the generic enumeration or record being
  declared, which are types within it (`Reqs/Lang/Generics`). -/
  typeParams : Array Name := #[]
  /-- The generic function being declared, with its type parameters, which
are abstract types within it (`Reqs/Lang/GenericFunctions`). -/
  fnTypeParams : Option (Name × Array Name) := none
  /-- The generic functions, by path. -/
  genericFns : NameMap GenericFn := {}
  /-- The applications of generic functions within the function being
  declared, with their type arguments (`GenericFn.calls`). -/
  genericCalls : Array (Name × Array Ty) := #[]
  /-- The instances of the generic function being declared that its own
  contract applies, which `instantiate` makes once it is declared. -/
  pendingInsts : Array (Array Ty) := #[]
  /-- The SMT-LIB symbol of each instance of a generic function, and of
  each of its clauses, that `defs` and `clauseDefs` hold, by the name that
  they hold it under. -/
  instSyms : NameMap String := {}
  /-- The higher-order functions, by path (`Reqs/Lang/HigherOrder`). -/
  hofs : NameMap HigherOrderFn := {}
  /-- The number of the next capture symbol (`Fren.Core.captureSym`), and
  of the next closure, whose parameters' symbols have it. -/
  nextCapture : Nat := 0
  nextClosure : Nat := 0
  /-- Where each closure's obligation is checked, with the higher-order
  function that its closure is given to (`Fren.Core.viaNote`). -/
  vias : Array (Span × Name) := #[]
  /-- The contract of each instance of a generic function without a body,
  by the function, each with the instance's type arguments, as the
  contract's own comp at the instance's sorts, which is checked where the
  check at the type parameters' sorts does not pass (`lang::generic_contract`). -/
  instContracts : NameMap (Array (Array Ty × CComp)) := {}
  /-- The applications of generic functions, in order (`Fren.Core.GenericUse`),
  from which follow the instances whose contracts are checked, and where
  (`Fren.Core.instanceSites`). -/
  genericUses : Array Fren.Core.GenericUse := #[]
  /-- The item being elaborated, by its path, which an application is in. -/
  item : Name := .anonymous
  /-- Some type is a set. -/
  usesSets : Bool := false
  /-- Some quantifier is unbounded, or some refinement claim's abstraction
  has calls, over whose variables the claim quantifies, so every query may
  quantify (`cli::logic`, `cli::query_logic`). -/
  quantified : Bool := false
  /-- The memberships `x in e` of the guards of the quantifiers over elements
  being elaborated (`ExprCtx.elemGuards`), by the span of `e`: whether `e`
  is a sequence, and the `undecidable` report that `in` defers until the
  quantifier is known to be outside the core, if it has one. -/
  elemMembers : Array (Span × Bool × Option (Span × Fren.Core.Msg)) := #[]
  /-- The current item has an unbounded quantifier with a bound name that
  has a domain, directly, through a call or through a defined
  function, so its queries set `fmf-bound` (`Reqs/Lang/Quantifiers#guards`). -/
  guardedUsed : Bool := false
  /-- In a defined function's body, its uses of itself so far, each where
  it is written (`lang::structural_recursion`). -/
  recApps : Array (Span × Array String × Array String) := #[]
  recUses : Array (Span × Fren.Core.RecUse) := #[]
  /-- In a defined function's body, the patterns of the `match`es on a
  parameter, or on a binder bound from a payload of one, that are not a Lean
  `match` and have a recursive application under them, each the first
  pattern that a Lean `match` does not have (`lang::recursive_match`). -/
  recMatches : Array Span := #[]
  /-- The defined functions and constants whose bodies or values have such a
  quantifier, directly or through others. -/
  guardedItems : Std.HashSet Name := {}
  /-- Whether the spec uses sequences, which cvc5 decides in its strings
  solver (`cli::logic`). -/
  usesSeqs : Bool := false
  /-- Whether it takes the domain or range of a relation over a type that is
  not finite, which needs higher-order logic (`cli::logic`). -/
  usesProjection : Bool := false
  /-- Some construct of the current item is outside the decidable core,
  whatever the level of `undecidable` (`view::inconclusive_advice`). -/
  outsideCore : Bool := false
  /-- Whether the current procedure, or a call of it, applies a relational
  operator; with `card`, it is outside the decidable core. -/
  relationalUsed : Bool := false
  /-- Where the current procedure counts: its `card`s, and its calls whose
  procedures count. -/
  countSpans : Array Span := #[]
  /-- The indexes of the constraint being elaborated, each with the formula
  that it is in range where it is evaluated: its guard implies its bounds. -/
  indexes : Array (Span × String × Option (String × Bool)) := #[]
  /-- The questions about the rows of the tables of the constraint being
  elaborated, each where it is reported, with the formula that it holds
  where the table is evaluated: its guard implies it. -/
  tables : Array (Span × Fren.Core.TableGoal × String) := #[]
  /-- The applications of uninterpreted functions whose result is a `Nat`
  elaborated since the current procedure started, its calls' among them. -/
  natApps : Array String := #[]
  /-- Each `+` where a `Nat` is expected, by file, which `fren mutate`
  does not make a `-` (`Reqs/Mutate`). -/
  natSums : Array (Nat × Span) := #[]
  /-- The names of `let` and `where` definitions made so far, which number
  their SMT-LIB symbols. -/
  nLets : Nat := 0
  /-- Whether the current procedure's members are being elaborated, past
  its name and the distinctness of its members' names: after a failure
  there, its declaration and line lints still run, as in Lean. -/
  inCompBody : Bool := false
  /-- The names that the pattern tests of the chain of `and` being
  elaborated bind, innermost last, for the later operands of the chain and
  the body of the `when` or `if` whose condition it is (`lang::test_scope`). -/
  bound : Array CBinder := #[]
  /-- The pattern tests elaborated whose patterns bind names, for
  `lintBools`, which reads and clears them. -/
  bindingTests : Array Span := #[]

/-- `s`, with what `t` recorded for the lints: what a failed member or item
recorded before its error outlives it, as in Lean, where an error undoes
nothing (`Reqs/View#static-errors`). -/
def State.keepLints (s t : State) : State :=
  { s with lintReports := t.lintReports, lintFixes := t.lintFixes, used := t.used, usedItems := t.usedItems
           useRecords := t.useRecords, useLocs := t.useLocs, items := t.items, declared := t.declared
           seenSettings := t.seenSettings, globalReads := t.globalReads, hofParams := t.hofParams, fnArgs := t.fnArgs }

/-- Why an item failed: its static errors, the last of which stopped it,
and the state when it did, whose lints outlive it (`State.keepLints`). -/
structure Failure where
  diags : Array Diag
  state : State

abbrev M := StateT State (Except Failure)

def err (span : Span) (msg : Msg) : M α := do
  let s ← get
  throw { diags := s.itemErrors.push { file := s.file, span, msg }, state := s }

/-- Validation and inhabitation are compiler-generated procedures. Their
source expressions have already received their expression lints; procedural
unused-variable and manual-assumption suggestions do not apply to them. -/
def withoutGhostLints (action : M α) : M α := do
  let before ← get
  let restore (st : State) : State := { st with
    lintReports := before.lintReports
    lintFixes := before.lintFixes
    natReports := before.natReports
  }
  -- Also on a static error, which keeps the state it failed in.
  let result ← tryCatch action fun failure => throw { failure with state := restore failure.state }
  modify restore
  return result

/-- Runs `x`, a member of an item that is checked on its own: on a static
error, records it, undoes what `x` did but its lints, and gives `none`, so
that the item's other members are still checked (`Reqs/View#static-errors`). -/
def attempt (x : M α) : M (Option α) := do
  let s ← get
  match x.run s with
  | .ok (a, s') => set s'; return some a
  | .error f => set { s.keepLints f.state with itemErrors := f.diags }; return none

/-- The shape of each record, newtype and enumeration, for their constraints. -/
def State.shapeOf (s : State) (p : Name) : Option Fren.Core.DataShape := s.shapes.find? p

/-- Stops the current item if a member of it had a static error, as when
what follows would only repeat it (`Reqs/View#static-errors`). -/
def stopIfErrors : M Unit := do
  let s ← get
  unless s.itemErrors.isEmpty do throw { diags := s.itemErrors, state := s }

def internal (span : Span) (what : String) : M α := err span (Msg.internal what)

def State.dataOf? (s : State) (p : Name) : Option DataDecl := s.datatypes.find? (·.path == p)

/-- The facts of the declared type `t` (`lang::type_facts`), from the
declarations as both front ends give them to `Fren.Core.typeFacts`. -/
def State.typeFacts (s : State) (t : Fren.Core.PTy) : Fren.Core.TypeFacts := Fren.Core.typeFacts s.shapeOf t.node

/-- Whether `t` is unbounded (`Reqs/Lang/Types`). -/
def State.unbounded (s : State) (t : Ty) : Bool := (s.typeFacts (.plain t)).unbounded

/-- Whether a type has infinitely many values (`Reqs/Lang/Decidability#outputs`):
it is not finite (`lang::type_facts`), so an abstract type counts. -/
def State.infinite (s : State) (t : Ty) : Bool := !(s.typeFacts (.plain t)).finite

/-- Every value of a finite type, as SMT-LIB terms, if there are at most
`cap` of them. -/
partial def State.values (s : State) (cap : Nat := 64) : Ty → Option (Array String)
  | .bool => some #["true", "false"]
  | .enum p args | .record p args => do
    let d ← s.dataOf? p
    if s.unbounded (d.ty args) then none
    let mut out := #[]
    for (c, fs) in d.instCtors args do
      let mut combos : Array (Array String) := #[#[]]
      for (_, t) in fs do
        let vs ← s.values cap t
        combos := combos.flatMap fun pre => vs.map pre.push
        if combos.size > cap then none
      out := out ++ combos.map fun xs => d.build args c xs.toList
      if out.size > cap then none
    return out
  -- Erased, as a newtype's values are.
  | .newtype _ u => s.values cap u
  | _ => none

/-- The number of values of `t`, if a quantifier ranges over it
(`lang::quantified_type`), counted without listing them. An unbounded
enumeration or record is recursive or has a part that a quantifier does
not range over, so it is not looked into, and the recursion ends. -/
def State.valueCount (s : State) (t : Ty) : Option Nat :=
  t.valueCount fun p => (s.dataOf? p).map fun d =>
    { isRecord := d.isRecord, unbounded := d.unbounded, ctors := d.ctors.map (·.2.map (·.2)) }

def segNames (segs : Array Ident) : Array Name := segs.map (Name.mkSimple ·.name)

def liftResolve (segs : Array Ident) : Except Fren.Core.Error α → M α
  | .ok a => pure a
  | .error e => do
    let seg? := segs[e.seg]?
    let src := (← get).src
    let beforeEq := seg?.any fun x => src[x.span.stop]? == some '='
    err (seg?.map (·.span) |>.getD default) (Fren.Core.withBangEqFix e.msg.get ((seg?.map (·.name)).getD "") beforeEq)

def liftMsg (span : Span) : Except Msg α → M α
  | .ok a => pure a
  | .error msg => err span msg

/-- The identifier that `x` declares, without the `!` that marks it as
shadowing (`Fren.Core.declaredName`), and whether it has one. Its span
leaves out the `!`, so that a fix that renames it keeps the `!`. -/
def declaredIdent (x : Ident) : Ident × Bool :=
  let (n, bang) := Fren.Core.declaredName (Name.mkSimple x.name)
  ({ name := Fren.Core.nameText n, span := if bang then { x.span with stop := x.span.stop - 1 } else x.span }, bang)

/-- The declaration `x`, without its `!`, checked to be written with `!`
exactly when it hides something in the current scope or among `locals`
(`lang::shadowing`). An import that brings in what it hides counts as
used. -/
def declare (x : Ident) (locals : Fren.Core.Locals := #[]) : M Ident := do
  let (y, bang) := declaredIdent x
  if Fren.Core.generatedName y.name then return y
  let n := Name.mkSimple y.name
  let st ← get
  liftMsg x.span (Fren.Core.checkDeclaredName n bang)
  liftMsg x.span (Fren.Core.checkShadowing n (st.table.hidden? st.scope locals n) bang)
  if let some u := st.table.shadowedImport? st.scope locals n bang then
    modify fun s => { s with used := s.used.push u }
  return y

/-- Resolves a path in an expression or type in the current module,
recording the import it resolves through, if any (`unused_imports`), and
the item it uses (`dead_code`). -/
def resolve (segs : Array Ident) (extra : Array Name := #[]) : M Resolved := do
  let (table, scope) := ((← get).table, (← get).scope)
  let r ← liftResolve segs (table.resolvePath scope (segNames segs) extra)
  if let some u := table.importVia scope (segNames segs) then
    modify fun s => { s with used := s.used.push u }
  modify fun s => { s with usedItems := s.usedItems.push r.usedItem }
  return r

/-- Reports a lint at the level in effect. -/
def lint (lint : Lint) (span : Span) (msg : Msg) : M Unit :=
  -- Once at a place: a function's block gives a `let` to each expression
  -- that needs it, which elaborates it again (`Reqs/Lang/Items#function-blocks`).
  modify fun s =>
    if s.lintReports.any fun r => r.lint == lint && r.ref == span && r.msg.headline == msg.headline then s
    else { s with lintReports := s.lintReports.push { lint, level := s.levels.get lint, ref := span, msg } }

/-- `resolve` for a path written in an expression, a pattern or a type,
which also reports `absolute_paths` (`lint::absolute_paths`) if `report`:
an expression elaborated again, as a trigger is, reports nothing. -/
def resolveWritten (segs : Array Ident) (extra : Array Name := #[]) (report : Bool := true) : M Resolved := do
  let r ← resolve segs extra
  if let some msg := Fren.Core.absolutePathMsg? (segNames segs) r then
    unless report do return r
    lint .absolutePaths (segs[0]!.span.to segs.back!.span) msg
  return r

/-- Reports the lints about a declared name alone (`nameMsgs`): its case
(`lint::naming_case`), and the lints of the `style` and `restriction` groups
that look only at the name, at the level in effect; and, for an item other
than a module, `module_name_repetitions`. -/
def lintName (what : Named) (n : Name) (span : Span) : M Unit := do
  if Fren.Core.generatedName (Fren.Core.nameText n) then return
  for (l, msg) in Fren.Core.nameMsgs what n do lint l span msg
  unless what matches .module do
    if let some msg := Fren.Core.moduleNameMsg? what (← get).module n then lint .moduleNameRepetitions span msg
  if what matches .variable | .instance | .binder then
    modify fun s => { s with declared := s.declared.push (n, span) }

/-- Starts an item whose declared names `lintDeclared` checks. -/
def startDeclared : M Unit := modify fun s => { s with declared := #[] }

/-- Reports `many_single_char_names` and `similar_names` on the names that
the `what` named `n`, at `span`, declares (`lint::many_single_char_names`,
`lint::similar_names`): each name once, in source order. -/
def lintDeclared (what : Named) (n : Name) (span : Span) : M Unit := do
  -- Each name once, where it is first declared: `x!` declares `x` again.
  let ds := (← get).declared.qsort fun a b => a.2.start < b.2.start
  let ds := ds.foldl (init := #[]) fun acc d => if acc.any (·.1 == d.1) then acc else acc.push d
  modify fun s => { s with declared := #[] }
  let single := ds.filter (Fren.Core.singleChar ·.1)
  if Fren.Core.manySingleCharNames single.size then
    lint .manySingleCharNames span (Fren.Core.manySingleCharNamesMsg what n (single.map (·.1)))
  for i in [0:ds.size] do
    if let some a := (ds.extract 0 i).find? (Fren.Core.namesSimilar ·.1 ds[i]!.1) then
      lint .similarNames ds[i]!.2 (Fren.Core.similarNamesMsg a.1 ds[i]!.1 what n)

/-- Reports `too_many_lines` on the `what` named `n`, at `name`, whose text
runs from its name to the end of `last` (`lint::too_many_lines`). -/
def lintLines (what : Named) (n : Name) (name last : Span) : M Unit := do
  -- `codeLines` of the text from `name.start` up to `last.stop`, as
  -- `Array.extract` would cut it, read in place.
  let src := (← get).src
  let stop := min last.stop src.size
  let k := Fren.Core.codeLinesIn src (min name.start stop) stop
  if Fren.Core.tooManyLines k then lint .tooManyLines name (Fren.Core.tooManyLinesMsg what n k)

/-- Reports a lint whose message's first fix replaces its text, or its own range, which
`fren fix` applies. -/
def lintFix (l : Lint) (span : Span) (msg : Msg) (unless? : Option (Lint × Span) := none) : M Unit := do
  let some f := msg.fixes[0]? | lint l span msg
  modify fun s => { s with lintFixes := s.lintFixes.push { lint := l, span, edits := #[(f.range?.getD (toRange span), f.replacement)], unless? } }
  lint l span { msg with notes := msg.notes.push Fren.Core.fixHelp }

/-- Reports a lint whose fix is `edits`, which `fren fix` makes. -/
def lintEdits (l : Lint) (span : Span) (msg : Msg) (edits : Array (Fren.Core.Range × String)) : M Unit := do
  modify fun s => { s with lintFixes := s.lintFixes.push { lint := l, span, edits } }
  lint l span (msg.note Fren.Core.fixHelp)

/-! ## Expressions -/

/-- Records the use `u`, written at `span`, of the defined function `f`,
whose parameters are `ps`, in its own body; an error if with it the uses are
not a structural recursion (`lang::structural_recursion`). -/
def noteRecUse (span : Span) (f : Name) (ps : Array Name) (u : Fren.Core.RecUse) : M Unit := do
  -- Once for each use written: an expression elaborated again, such as a
  -- `match`'s scrutinee where a closure refers to an arm's binder, is not
  -- another use.
  if (← get).recUses.any (·.1 == span) then return
  modify fun s => { s with recUses := s.recUses.push (span, u) }
  let uses := (← get).recUses
  if let .notStructural _ i := Fren.Core.recursion ps.size (uses.toList.map (·.2)) then
    -- A function always has a parameter; without one, the message names the function.
    err span (Fren.Core.nonStructuralMsg f (ps[i]?.getD f) u.form (u.args[i]?.getD .expr))

structure ExprCtx where
  vars : Array CVar
  /-- The procedure's calls, in order. -/
  insts : Array Name := #[]
  place : Place
  /-- For a binding, the index of its call. -/
  current : Nat := 0
  /-- The binders in scope, innermost last. -/
  binders : Array CBinder := #[]
  /-- The instances of the quantifiers around this expression, multiplied
  (`lang::quantifier_size`). -/
  instances : Nat := 1
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- In a defined function's body, if it may recurse
  (`lang::structural_recursion`): its parameters' names, its type, and its
  symbol. -/
  selfRec? : Option (Array Name × Fren.Core.FnTy × String) := none
  /-- In a higher-order function's body or contract, its function
  parameters: each one's name, type and symbol (`Reqs/Lang/HigherOrder#function-parameters`). -/
  fnParams : Array (Name × Fren.Core.FnTy × String) := #[]
  /-- In a closure's body, which applies no uninterpreted function. -/
  inClosure : Bool := false
  /-- In a clause of a function's contract: the function, whether the
  clause is a postcondition, and the parameters (`lang::contract_application`). -/
  contract? : Option (Name × Bool × Array Name) := none
  /-- `++` here is in the decidable core: the receiver of a method, or a
  side of `=` or `!=` whose other side is a constant. -/
  concatOk : Bool := false
  /-- The type this expression must have, which gives `{}` its type. -/
  expected? : Option Ty := none
  /-- The conditions under which this expression is evaluated, read from
  left to right: an index's guard (`Reqs/Lang/Expressions#sequences`). -/
  guards : Array String := #[]
  /-- Whether to record the indexes and tables of this expression for their
  checks, and report its lints: not when it is elaborated a second time, as
  a trigger. -/
  noteIndexes : Bool := true
  /-- This expression is an operand of `or`, or of `and`, whose chain
  `membership_chain` looks at from its top: that operator, or `""`. -/
  chain : String := ""
  /-- The expression this one is part of, if any: where a `match` is, for
  the match lints. -/
  parent? : Option Expr := none
  /-- This expression is the `else` branch of an `if`, whose chain
  `if_chain_match` looks at from its top. -/
  inElse : Bool := false
  /-- In a definition of a `let` or `where`, the names of it and of the
  later definitions of its clause that hide nothing, each with whether it
  is its own: a mention of one is used before its definition
  (`lang::definition_order`). -/
  pending : Array (Name × Bool) := #[]
  /-- In a definition of a `let` or `where` that nothing mentions, which
  counts for nothing: what it may mention, linear arithmetic and the
  decidable core are not checked in it (`Reqs/Lang/Let#meaning`). -/
  unmentioned : Bool := false
  /-- What the chain of `and` that this expression is an operand of, or is,
  is a part of, for its pattern tests (`lang::test_scope`). Only `and` and
  `is` read it, and only their operands see it. -/
  testContext : Fren.Core.TestContext := .standalone
  /-- For an operand of a chain of `and`, its position in the chain and the
  chain's number of operands. -/
  testAt? : Option (Nat × Nat) := none
  /-- The members' expressions of the guards of the quantifiers over
  elements around this expression, by span (`State.elemMembers`). -/
  elemGuards : Array Span := #[]
  /-- Within the body of a quantifier over elements: whether it is a
  `forall`; and the quantifiers that are directly its body, or the body
  of one of those, by span (`Fren.Core.ElementNesting`). -/
  elemKind? : Option Bool := none
  elemDirect : Array Span := #[]
  /-- The bound names of the quantifiers over elements, of the same kind,
  that this expression is directly the body of, which its quantifier may
  mention (`Fren.Core.ElementVerdict.mentionsBound`). -/
  elemChain : Array Name := #[]

/-- What the binder `b` is, for a declaration that hides it (`Fren.Core.bindingLocals`). -/
def CBinder.what (b : CBinder) : Name × Fren.Core.BindingKind :=
  (b.name, if b.scrutinee.isNone then .boundName else if b.isDef then .definition else .patternBinder)

/-- The binder named `n` in scope, if any. -/
def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option CBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : CBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name) ++ cx.fnParams.map (·.1)

/-- The function parameter named `n`, with its type and symbol, if no
binder or variable hides it (`Reqs/Lang/HigherOrder#function-parameters`). -/
def ExprCtx.fnParam? (cx : ExprCtx) (n : Name) : Option (Fren.Core.FnTy × String) :=
  if (cx.binder? n).isSome || cx.vars.any (·.name == n) then none
  else (cx.fnParams.find? (·.1 == n)).map fun (_, t, sym) => (t, sym)

/-- The single name that the expression `a` is, if it is one. -/
def soleName? : Expr → Option Name
  | .path _ #[x] => some (identName x.name)
  | _ => none

/-- In a defined function's body that may recurse, where the expression `a`
comes from (`lang::structural_recursion`): the position of the parameter
that it is, or that it is bound from a payload of, with whether it is a
payload. -/
def ExprCtx.recOrigin? (cx : ExprCtx) (a : Expr) : Option (Nat × Bool) := do
  let (ps, _, _) ← cx.selfRec?
  let n ← soleName? a
  match cx.binder? n with
  | some b => return (← b.payloadOf?, true)
  | none =>
    guard (cx.vars.any (·.name == n))
    return (← ps.idxOf? n, false)

/-- Where the argument `a` at position `i` of a recursive application comes
from, relative to the parameter there (`lang::structural_recursion`). -/
def ExprCtx.recArg (cx : ExprCtx) (a : Expr) (i : Nat) : Fren.Core.RecArg :=
  match cx.recOrigin? a with
  | some (j, true) => if j == i then .payload else .name
  | some (j, false) => if j == i then .itself else .name
  | none => if (soleName? a).isSome then .name else .expr


/-- The constant that `segs` names, without recording its use. -/
def constPath? (cx : ExprCtx) (segs : Array Ident) : M (Option Name) := do
  let st ← get
  let .ok (.item { kind := .constItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing
    | return none
  return some path

/-- The value of `e`, if it is an integer constant expression: integer
literals and constants whose values are, combined by `+`, `-`, `*`, `div`,
`mod`, `abs`, `min` and `max` (`Reqs/Lang/Expressions#division-and-remainder`). -/
partial def intConstValue? (cx : ExprCtx) (e : Expr) : M (Option Int) := do
  match e with
  | .num _ v => return some v
  | .neg _ a => return (← intConstValue? cx a).map (- ·)
  | .bin _ op a b =>
    let some x ← intConstValue? cx a | return none
    let some y ← intConstValue? cx b | return none
    return Fren.Core.intConstOp? op x y
  | .path _ segs =>
    -- A constant, then the methods without arguments applied to it.
    let parts := if segs.size == 1 then segs[0]!.name.splitOn "." else [""]
    let root := if segs.size == 1 then #[{ segs[0]! with name := parts.head! }] else segs
    if segs.size > 1 && segs.any (·.name.contains '.') then return none
    if root.size == 1 && (cx.vars.any (·.name.getRoot == Name.mkSimple parts.head!) || (cx.binder? (Name.mkSimple parts.head!)).isSome) then
      return none
    let some path ← constPath? cx root | return none
    let some v := (← get).constInts.find? path | return none
    return parts.tail.foldlM (fun x m => Fren.Core.intConstMethod? m x []) v
  | .method _ r m args =>
    let some x ← intConstValue? cx r | return none
    let some ys := (← args.toList.mapM (intConstValue? cx)).mapM id | return none
    return Fren.Core.intConstMethod? m.name x ys
  | .field _ r f =>
    let some x ← intConstValue? cx r | return none
    return Fren.Core.intConstMethod? f.name x []
  | _ => return none

/-- The form of the divisor `k` (`lang::divisor`), without its `-`: its form,
its value if it is known, and the constant it names, if any. -/
partial def divisorForm (cx : ExprCtx) (k : Expr) : M (Fren.Core.DivisorForm × Int × Name) := do
  match k with
  | .neg _ a => let (f, v, c) ← divisorForm cx a; return (f, -v, c)
  | .num _ v => return (.literal, v, .anonymous)
  | .path _ segs =>
    if segs.any (·.name.contains '.') then return (.other, 0, .anonymous)
    if segs.size == 1 && (cx.vars.any (·.name == identName segs[0]!.name) || (cx.binder? (identName segs[0]!.name)).isSome) then
      return (.other, 0, .anonymous)
    let some path ← constPath? cx segs | return (.other, 0, .anonymous)
    return match (← get).constInts.find? path with
      | some v => (.knownConstant, v, path)
      | none => (.unknownConstant, 0, path)
  | _ => return (.other, 0, .anonymous)

/-- The newtype that `segs` names, with its underlying type, if it names
one. -/
def newtypeNamed? (cx : ExprCtx) (segs : Array Ident) : M (Option (Name × Ty)) := do
  let st ← get
  let .ok (.item { kind := .recordItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing
    | return none
  return (st.newtypes.find? path).map (path, ·)

/-- Whether `segs` names a variant. -/
def isVariant (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  return st.table.resolvePath st.scope (segNames segs) cx.shadowing matches .ok (.variant ..)

/-- Whether `segs`, applied, builds a variant or a newtype rather than
applying a function. -/
def isConstruction (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  if st.table.resolvePath st.scope (segNames segs) cx.shadowing matches .ok (.variant ..) then return true
  return (← newtypeNamed? cx segs).isSome

/-- Whether `segs`, applied, applies a cardinality operator
(`Reqs/Lang/Expressions#cardinality`). -/
def isCardinality (segs : Array Ident) : Bool :=
  segs.size == 1 && (Fren.Core.builtinFunction? (identName segs[0]!.name)).isSome

/-- Whether `segs`, applied, applies a defined function. -/
def isDefined (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing
    | return false
  return st.defs.any (·.1 == path)

/-- What the identifier `x` of one segment, not applied, is in a pattern
(`lang::pattern_name`). -/
def patternName (_cx : ExprCtx) (x : Ident) : M Fren.Core.PatternName := do
  let (d, bang) := declaredIdent x
  return Fren.Core.patternName (d.name == "true" || d.name == "false") bang
    ((← get).table.namesVariant? (← get).scope (Name.mkSimple d.name))

/-- The binders of the pattern `p`, in preorder. -/
def patternBinders (cx : ExprCtx) (p : Pattern) : M (Array Ident) :=
  p.names.filterM fun x => return (← patternName cx x) == .binder

/-- The operands of a chain of `op`, `or` or `and`. -/
partial def chainOperands (op : String) (e : Expr) : Array Expr :=
  match e with
  | .block _ op' members => if op' == op then members.flatMap fun (_, value) => chainOperands op value else #[e]
  | .bin _ op' l r => if op' == op then chainOperands op l ++ chainOperands op r else #[e]
  | _ => #[e]

/-- Whether a pattern test of the chain of `and` `c` binds names. -/
def chainBinds (cx : ExprCtx) (c : Expr) : M Bool :=
  (chainOperands "and" c).anyM fun
    | .is _ _ p => return !(← patternBinders cx p).isEmpty
    | _ => pure false

/-- The names that the pattern tests of the chain of `and` `c` bind, which
what follows the chain sees (`lang::test_scope`). -/
def chainBinders (cx : ExprCtx) (c : Expr) : M (List String) := do
  let bs ← (chainOperands "and" c).mapM fun
    | .is _ _ p => patternBinders cx p
    | _ => pure #[]
  return bs.toList.flatMap fun xs => xs.toList.map (·.name)

/-- The paths of the functions that `e` applies (`unused_assumption`). -/
partial def appliedPaths : Expr → Array (Array Ident)
  | .block _ _ members => members.flatMap (appliedPaths ·.2)
  | .app _ segs args => args.foldl (· ++ appliedPaths ·) #[segs]
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => appliedPaths c ++ appliedPaths d
  | .not _ a | .neg _ a | .field _ a _ => appliedPaths a
  | .method _ r _ args => args.foldl (· ++ appliedPaths ·) (appliedPaths r)
  | .set _ es | .seq _ es | .chain _ es _ => es.foldl (· ++ appliedPaths ·) #[]
  | .ite _ c a b => appliedPaths c ++ appliedPaths a ++ appliedPaths b
  | .record _ _ fs => fs.foldl (init := #[]) fun acc (_, e?) => acc ++ (e?.map appliedPaths).getD #[]
  | .update _ r fs => fs.foldl (init := appliedPaths r) fun acc (_, e?) => acc ++ (e?.map appliedPaths).getD #[]
  | .match _ s arms _ => (armParts arms).foldl (init := appliedPaths s) fun acc e => acc ++ appliedPaths e
  | .matches _ ss arms _ => (ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)).flatMap appliedPaths
  | .is _ s _ => appliedPaths s
  | _ => #[]

/-- The uninterpreted functions that `e` applies, as links of
`unused_assumption` (`Fren.Core.fnLink`). -/
def appliedFns (cx : ExprCtx) (e : Expr) : M (Array Name) := do
  let st ← get
  return (appliedPaths e).filterMap fun segs =>
    match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
    | .ok (.item { kind := .fnItem, path, .. }) => if st.defs.any (·.1 == path) then none else some (Fren.Core.fnLink path)
    | _ => none

/-- The shape of `e`, for what it mentions (`lang::mentions`), where `bs`
are the binders of `e` around the subexpression, each with the shape of its
scrutinee. -/
partial def shapeOf (cx : ExprCtx) (bs : Array (Name × Fren.Core.MentionShape) := #[]) (e : Expr) : M Fren.Core.MentionShape := do
  let parts (k : Fren.Core.MentionKind) (es : List Expr) : M Fren.Core.MentionShape :=
    return .node k (← es.mapM (shapeOf cx bs))
  -- The binders of the pattern tests of the chain of `and` `c`, each with
  -- the shape of its scrutinee.
  let testBinderShapes (c : Expr) : M (Array (Name × Fren.Core.MentionShape)) :=
    (chainOperands "and" c).flatMapM fun
      | .is _ sc p => do
        let s' ← shapeOf cx bs sc
        return (← patternBinders cx p).map fun x => (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.node .binder [s'])
      | _ => pure #[]
  match e with
  | .block sp op members => shapeOf cx bs (Expr.lowerBlock sp op members)
  | .path _ segs =>
    if segs.size != 1 then return .leaf .constant
    let n := identName segs[0]!.name
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then
      let some sc := b.scrutinee | return .leaf (if b.unbounded then .variable (n.toString (escape := false)) else .bound)
      return .node .binder [← shapeOf (cx.at b) #[] sc]
    -- Definitions are acyclic, so this ends.
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      return .node .definition [← shapeOf { cx with binders := #[] } #[] d]
    return .leaf (if cx.vars.any (·.name.isPrefixOf n) then .variable (n.toString (escape := false)) else .constant)
  -- The names that the pattern tests of a condition, or of the left
  -- operand of `and`, bind, in what sees them (`lang::test_scope`).
  | .when _ false c d | .bin _ "and" c d => do
    let new ← testBinderShapes c
    return .node .compound [← shapeOf cx bs c, ← shapeOf cx (bs ++ new) d]
  | .ite _ c a b => do
    let new ← testBinderShapes c
    return .node .compound [← shapeOf cx bs c, ← shapeOf cx (bs ++ new) a, ← shapeOf cx bs b]
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => parts .compound [c, d]
  | .not _ a | .neg _ a | .field _ a _ => parts .compound [a]
  | .method _ r _ args => parts .method (r :: args.toList)
  | .set _ es | .seq _ es | .chain _ es _ => parts .compound es.toList
  | .quant _ _ binders body =>
    let new := binders.flatMap (·.names) |>.map fun x => (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.leaf .bound)
    return .node .compound [← shapeOf cx (bs ++ new) body]
  -- A closure's parameter varies, as a variable does
  -- (`Reqs/Lang/HigherOrder#arguments`).
  | .closure _ ps body =>
    let new := ps.map fun (x, _) =>
      let n := (declaredIdent x).1.name
      (Name.mkSimple n, Fren.Core.MentionShape.leaf (.variable n))
    return .node .compound [← shapeOf cx (bs ++ new) body]
  | .app _ segs args =>
    -- A cardinality operator has a fixed meaning, as an operator does.
    let k : Fren.Core.MentionKind ← if isCardinality segs then pure .compound
      else if ← isConstruction cx segs then pure .construction
      else if ← isDefined cx segs then pure .defined else pure (.uninterpreted ("::".intercalate (segs.toList.map (·.name))))
    parts k args.toList
  | .record _ _ fs => parts .construction (fs.toList.map fun (f, e?) => e?.getD (.path f.span #[f]))
  | .update _ r fs => parts .compound (r :: fs.toList.map fun (f, e?) => e?.getD (.path f.span #[f]))
  | .match _ s arms _ =>
    let s' ← shapeOf cx bs s
    let arms ← arms.toList.flatMapM fun (p, g?, body) => do
      let new := (← patternBinders cx p).map fun x =>
        (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.node .binder [s'])
      (g?.toList ++ [body]).mapM (shapeOf cx (bs ++ new))
    return .node .compound (s' :: arms)
  | .matches _ ss arms _ =>
    let shapes ← ss.mapM (shapeOf cx bs)
    let children ← arms.toList.flatMapM fun (ps, g, body) => do
      let mut new := #[]
      for p in ps, j in [0:ps.size] do
        new := new ++ (← patternBinders cx p).map fun x =>
          (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.node .binder (shapes[j]?.toList))
      (g.toList ++ [body]).mapM (shapeOf cx (bs ++ new))
    return .node .compound (shapes.toList ++ children)
  | .is _ s _ => parts .compound [s]
  | .«let» _ defs body _ =>
    -- Each name stands for its definition, which sees the earlier names.
    let bs ← defs.foldlM (init := bs) fun bs (x, _, d) => do
      return bs.push (Name.mkSimple (declaredIdent x).1.name, .node .definition [← shapeOf cx bs d])
    return .node .compound [← shapeOf cx bs body]
  | .table _ rows => parts .compound (tableParts rows).toList
  | .num .. | .bool .. | .str .. => return .leaf .literal

/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def mentionsAny (cx : ExprCtx) (e : Expr) : M Bool := return (← shapeOf cx #[] e).mentions

/-- The names that the pattern tests of the chain of `and` `c` would bind,
as written, without their `!`. -/
def testNames (c : Expr) : Array Name :=
  (chainOperands "and" c).flatMap fun
    | .is _ _ p => p.names.map fun b => Name.mkSimple (declaredIdent b).1.name
    | _ => #[]

/-- The names of the variables and uninterpreted functions that `e`
mentions (`lang::mentions`). -/
def mentionedNames (cx : ExprCtx) (e : Expr) : M (List Fren.Core.Mention) := return (← shapeOf cx #[] e).mentioned

/-- The names of the variables that `e` mentions: its paths of one
segment, and for `p.x`, `p` too. -/
partial def mentions (e : Expr) (all : Bool := true) : Array Name :=
  let mentions (e : Expr) := mentions e all
  match e with
  | .block _ _ members => members.flatMap fun (_, value) => mentions value
  | .path _ segs =>
    if segs.size == 1 then
      let n := identName segs[0]!.name
      (n.components.foldl (init := (#[], Name.anonymous)) fun (acc, p) c => let p := p ++ c; (acc.push p, p)).1
    else #[]
  -- In what sees them, the names that the pattern tests of a condition,
  -- or of the left operand of `and`, bind mean them (`lang::test_scope`).
  | .when _ false c d | .bin _ "and" c d => mentions c ++ (mentions d).filter (!(testNames c).contains ·.getRoot)
  | .ite _ c a b => mentions c ++ (mentions a).filter (!(testNames c).contains ·.getRoot) ++ mentions b
  | .when _ _ c d => mentions c ++ mentions d
  | .not _ a | .neg _ a | .field _ a _ => mentions a
  | .method _ r _ args => args.foldl (· ++ mentions ·) (mentions r)
  | .set _ es => es.foldl (· ++ mentions ·) #[]
  | .pair _ a b | .index _ a b => mentions a ++ mentions b
  | .seq _ es | .chain _ es _ => es.foldl (· ++ mentions ·) #[]
  | .bin _ _ a b => mentions a ++ mentions b
  | .app _ _ args => args.foldl (· ++ mentions ·) #[]
  | .record _ _ fs => fs.foldl (init := #[]) fun acc (f, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple f.name]
  | .update _ r fs => fs.foldl (init := mentions r) fun acc (f, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple f.name]
  | .match _ s arms _ => arms.foldl (init := mentions s) fun acc (p, g?, body) =>
    -- In its arm, a binder's name means the binder, not what it shadows.
    let bound := p.names.map fun b => Name.mkSimple (declaredIdent b).1.name
    acc ++ ((g?.map mentions).getD #[] ++ mentions body).filter (!bound.contains ·.getRoot)
  | .matches _ ss arms _ => arms.foldl (init := ss.flatMap mentions) fun acc (ps, g, body) =>
    let bound := ps.flatMap Pattern.names |>.map fun b => Name.mkSimple (declaredIdent b).1.name
    acc ++ (g.toArray.flatMap mentions ++ mentions body).filter (!bound.contains ·.getRoot)
  | .is _ s _ => mentions s
  | .«let» _ defs body _ =>
    (Fren.Core.clauseMentions (defs.map fun (x, _, _) => Name.mkSimple (declaredIdent x).1.name)
      (defs.map fun (_, _, d) => mentions d) (mentions body) all).1
  | .quant _ _ binders body =>
    -- In its body, a bound name means the bound name, not what it shadows.
    let bound := binders.flatMap (·.names) |>.map fun x => Name.mkSimple (declaredIdent x).1.name
    (mentions body).filter (!bound.contains ·.getRoot)
  | .closure _ ps body =>
    let bound := ps.map fun (x, _) => Name.mkSimple (declaredIdent x).1.name
    (mentions body).filter (!bound.contains ·.getRoot)
  | .table _ rows => (tableParts rows).foldl (· ++ mentions ·) #[]
  | _ => #[]

/-- The first segment of the path `segs`. -/
def pathHead (segs : Array Ident) : Array Name := (segs[0]?.map fun s => (identName s.name).getRoot).toArray

/-- The names of a type's segments, but for those that write its form
(`fn(`, a type's pattern). -/
def typeNames (segs : Array Ident) : Array Name :=
  segs.filterMap fun s =>
    if Fren.Core.isIdStart s.name.front && s.name.all (fun c => Fren.Core.isIdRest c || c == '.') then
      some (identName s.name).getRoot
    else none

/-- The names that the pattern `p` writes other than its binders: the
variant of each pattern that is applied or written with `::`, and the
segments of each range pattern's bound (`lint::closure_names`). -/
partial def patternItemNames : Pattern → Array Name
  | .variant _ path args =>
    (if args.isNone && path.size == 1 then #[] else pathHead path) ++ (args.getD #[]).flatMap patternItemNames
  | .range _ lo hi _ =>
    #[lo, hi].flatMap fun | some (.path _ segs) => segs.map fun s => (identName s.name).getRoot | _ => #[]
  | .or _ alts => alts.flatMap patternItemNames
  | _ => #[]

/-- The names that `e` writes other than its variables, which no binder of
`e` declares (`lint::closure_names`): the first segment of the function
that each application applies, and of each path of more than one
segment, the type of each record literal, the names that its patterns
write other than their binders (`patternItemNames`), and the segments of
each type. -/
partial def itemNames (e : Expr) : Array Name :=
  match e with
  | .block _ _ members => members.flatMap fun (_, value) => itemNames value
  | .path _ segs => if segs.size > 1 then pathHead segs else #[]
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => itemNames c ++ itemNames d
  | .ite _ c a b => itemNames c ++ itemNames a ++ itemNames b
  | .not _ a | .neg _ a | .field _ a _ => itemNames a
  | .method _ r _ args => args.foldl (· ++ itemNames ·) (itemNames r)
  | .set _ es | .seq _ es | .chain _ es _ => es.flatMap itemNames
  | .app _ fn args =>
    (if fn.size == 1 && fn[0]!.name.contains '.' then #[] else pathHead fn) ++ args.flatMap itemNames
  | .record _ ty fs => pathHead ty ++ fs.flatMap fun (_, e?) => (e?.map itemNames).getD #[]
  | .update _ r fs => fs.foldl (init := itemNames r) fun acc (_, e?) => acc ++ (e?.map itemNames).getD #[]
  | .match _ s arms _ => arms.foldl (init := itemNames s) fun acc (p, g?, body) =>
    acc ++ patternItemNames p ++ (g?.map itemNames).getD #[] ++ itemNames body
  | .matches _ ss arms _ => arms.foldl (init := ss.flatMap itemNames) fun acc (ps, g, body) =>
    acc ++ ps.flatMap patternItemNames ++ g.toArray.flatMap itemNames ++ itemNames body
  | .is _ s p => itemNames s ++ patternItemNames p
  | .«let» _ defs body _ =>
    defs.foldl (init := itemNames body) fun acc (_, ty?, d) => acc ++ (ty?.map typeNames).getD #[] ++ itemNames d
  | .quant _ _ binders body => binders.foldl (init := itemNames body) fun acc b => acc ++ typeNames b.ty
  | .closure _ ps body => ps.foldl (init := itemNames body) fun acc (_, ty?) => acc ++ (ty?.map typeNames).getD #[]
  | .table _ rows => (tableParts rows).flatMap itemNames
  | .num .. | .bool .. | .str .. => #[]

/-- The names that the closure's body `body` has free, but for the
closure's own parameters `params` (`lint::closure_names`): the variables
it mentions (`mentions`) and the other names it writes (`itemNames`),
each once, as written. -/
def closureFreeNames (params : Array String) (body : Expr) : Array String :=
  (((mentions body).map (·.getRoot) ++ itemNames body).map Fren.Core.nameText).filter (!params.contains ·)
    |>.toList.eraseDups.toArray

/-- The atoms of `e`, a `Bool` expression: its operands through `and`
(`lint::unrelated_binders`). -/
partial def boolAtoms : Expr → Array Expr
  | .bin _ "and" a b => boolAtoms a ++ boolAtoms b
  | e => #[e]

/-- Which of the definitions `defs` of a `let` or `where` clause its body
`body` mentions, directly or through the later ones that it mentions: the
others count for nothing (`Reqs/Lang/Let#meaning`). -/
def usedDefinitions (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) : Array Bool :=
  (Fren.Core.clauseMentions (defs.map fun (x, _, _) => Name.mkSimple (declaredIdent x).1.name)
    (defs.map fun (_, _, d) => mentions d false) (mentions body false) false).2

/-- The variables that the defined output `v` stands for: those its
definition mentions, through other definitions, transitively. -/
partial def defDeps (vars : Array CVar) (v : CVar) (seen : Array Name := #[]) : Array CVar := Id.run do
  let some d := v.defn? | return #[v]
  let mut out := #[]
  for n in (mentions d).toList.eraseDups do
    let some u := vars.find? (·.name == n) | continue
    if seen.contains u.name then continue
    out := out ++ defDeps vars u (seen.push v.name)
  return out

/-- The cycle of definitions through `start`, if any, each mentioning the
next. -/
partial def defCycle? (vars : Array CVar) (start : Name) (path : Array Name := #[]) : Option (Array Name) :=
  match (vars.find? (·.name == start)).bind (·.defn?) with
  | none => none
  | some d =>
    let path := path.push start
    (mentions d).toList.eraseDups.findSome? fun n =>
      if n == path[0]! then some path
      else if path.contains n then none
      else defCycle? vars n path

/-- Whether `e` mentions an output of an infinite type, directly, through a
definition or through a binder (`Reqs/Lang/Decidability#outputs`). -/
partial def mentionsInfiniteOutput (cx : ExprCtx) (e : Expr) : M Bool := do
  let st ← get
  for n in mentions e do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsInfiniteOutput (cx.at b) sc then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    if (defDeps cx.vars v).any fun u => u.role == .output && st.infinite u.ty then return true
  return false

/-- Whether `e` is a constant: it mentions no variable or uninterpreted
function (`lang::mentions`). -/
def isConstant (cx : ExprCtx) (e : Expr) : M Bool := return !(← mentionsAny cx e)

/-- Whether `e` is a variable, a field read from one, or an application of
an uninterpreted function, which is as unknown as a variable. -/
partial def isVariable : Expr → Bool
  | .path _ segs => segs.size == 1
  | .field _ a _ => isVariable a
  | .app .. => true
  | _ => false

/-- The definition of `e`, if it names a defined output. -/
def definitionOf? (cx : ExprCtx) : Expr → Option Expr
  | .path _ segs => if segs.size == 1 then (cx.vars.find? (·.name == identName segs[0]!.name)).bind (·.defn?) else none
  | _ => none

/-- Whether `e` contains a `++` that is not a constant, itself or in a
defined output's definition (acyclic, so this ends). -/
partial def hasConcat (cx : ExprCtx) (e : Expr) : M Bool := do
  if e matches .bin _ "++" _ _ then
    if !(← isConstant cx e) then return true
  match e with
  | .path .. => match definitionOf? cx e with | some d => hasConcat cx d | none => return false
  | .when _ _ c d | .bin _ _ c d => return (← hasConcat cx c) || (← hasConcat cx d)
  | .not _ a | .neg _ a | .field _ a _ => hasConcat cx a
  | .method _ r _ args => (#[r] ++ args).anyM (hasConcat cx)
  | .set _ es | .app _ _ es => es.anyM (hasConcat cx)
  | .pair _ a b | .index _ a b => return (← hasConcat cx a) || (← hasConcat cx b)
  | .seq _ es | .chain _ es _ => es.anyM (hasConcat cx)
  | .ite _ c a b => return (← hasConcat cx c) || (← hasConcat cx a) || (← hasConcat cx b)
  | .record _ _ fs => fs.anyM fun (_, e?) => match e? with | some e => hasConcat cx e | none => pure false
  | .update _ r fs =>
    return (← hasConcat cx r) || (← fs.anyM fun (_, e?) => match e? with | some e => hasConcat cx e | none => pure false)
  | .match _ s arms _ => return (← hasConcat cx s) || (← (armParts arms).anyM (hasConcat cx))
  | .matches _ ss arms _ => return (← ss.anyM (hasConcat cx)) || (← (arms.flatMap fun (_, g, b) => g.toArray.push b).anyM (hasConcat cx))
  | .is _ s _ => hasConcat cx s
  | .«let» _ defs body _ => return (← defs.anyM (hasConcat cx ·.2.2)) || (← hasConcat cx body)
  | .quant _ _ _ b => hasConcat cx b
  | .table _ rows => (tableParts rows).anyM (hasConcat cx)
  | _ => return false

/-- Reports `undecidable` if construct `c`, with `operands` other than of
`=` and `!=`, is outside the decidable core (`lang::in_core`). -/
def checkCore (cx : ExprCtx) (span : Span) (c : Fren.Core.Construct) (constantArgs comparable : Bool)
    (operands : Array Expr) (ground : Bool := false) (infiniteElems : Bool := true) (finiteRange : Bool := true)
    (literalOperand : Bool := false) : M Unit := do
  if cx.unmentioned then return
  let infinite ← operands.anyM (mentionsInfiniteOutput cx)
  unless Fren.Core.inCore c constantArgs comparable infinite ground infiniteElems finiteRange literalOperand do
    modify fun s => { s with outsideCore := true }
    lint .undecidable span (Fren.Core.undecidableMsg c infinite)

/-- Whether `e` mentions an output that is not defined, directly, through a
definition or through a binder: one that the realizability check
quantifies over (`lang::ElementBinder`). -/
partial def mentionsOutput (cx : ExprCtx) (e : Expr) : M Bool := do
  for n in mentions e do
    if let some b := cx.binder? n then
      if let some sc := b.scrutinee then
        if ← mentionsOutput (cx.at b) sc then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    if (defDeps cx.vars v).any fun u => u.role == .output && u.defn?.isNone then return true
  return false

/-- Whether the body of the defined function `path` has a quantifier over a
type that is not listed, directly or through another defined function that
it applies, to a depth of `fuel`, beyond which it is taken to have one: its
`define-fun` has the solver's quantifier, or a quantifier over elements
(`Fren.Core.ElementUse.quantifiedArgument`). -/
partial def fnQuantifies (st : State) (fuel : Nat) (path : Name) : Bool :=
  if fuel == 0 then true else
  let body? := ((st.genericFns.find? path).map (·.body)).orElse fun _ =>
    (st.defs.find? (·.1 == path)).map (·.2.2.2)
  match body? with
  | none => false
  | some body =>
    let quantified := ["(forall (", "(exists (", "(fren.forall (", "(fren.exists ("].any fun h => (body.splitOn h).length > 1
    quantified || st.defs.any fun (p, _, _, _) =>
      p != path && (body.splitOn ((st.instSyms.find? p).getD (itemSym p))).length > 1 && fnQuantifies st (fuel - 1) p

/-- How an application of `segs` uses an argument that mentions a bound
name (`elementUses`): a defined function with a parameter that has a
sequence within it, or an uninterpreted function whose applications bring
facts. -/
def appElementUse (cx : ExprCtx) (segs : Array Ident) : M (Array Fren.Core.ElementUse) := do
  let st ← get
  let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | return #[]
  let declared : Option (Array Ty) := match st.genericFns.find? path, st.defs.find? (·.1 == path) with
    | some g, _ => some g.declared
    | none, some d => some (d.2.1.map (·.2))
    | none, none => none
  if let some ps := declared then
    if ps.any (Fren.Core.hasSeqWithin st.shapeOf 8) then return #[.seqArgument]
    return if fnQuantifies st 8 path then #[.quantifiedArgument] else #[]
  let facts : Bool := match st.funs.find? (·.1 == path) with
    | some f => f.2.2 == .nat || (st.contracts.find? path).isSome || st.funFacts.contains (itemSym path)
    | none => false
  return cond facts #[.factArgument] #[]

/-- How the expression `e`, within the body of a quantifier, uses the bound
name `x`, where `inner` are the names that the body declares, which may
stand for `x` (`Fren.Core.ElementUse`): as an index, or an `update`'s
position, of a sequence that is not a constant; in an argument of a
defined function with a parameter that has a sequence within it, or of an
uninterpreted function whose applications bring facts; or in the members of
a quantifier's guard. -/
partial def elementUses (cx : ExprCtx) (x : Name) (inner : Array Name) (e : Expr) : M (Array Fren.Core.ElementUse) := do
  let names (e : Expr) : Bool := (mentions e).any fun n => n.getRoot == x || inner.contains n.getRoot
  let own : Array Fren.Core.ElementUse ← match e with
    | .index _ r i => pure <| if names i && !(← isConstant cx r) then #[.index] else #[]
    | .method _ r m args =>
      let positions := match m.name with | "update" | "at" => 1 | "slice" => 2 | _ => 0
      pure <| if (args.extract 0 positions).any names && !(← isConstant cx r) then #[.index] else #[]
    | .app _ segs args => if args.any names then appElementUse cx segs else pure #[]
    | .quant _ all _ b =>
      let receivers := (guardConjuncts all b).filterMap fun
        | some (_, .mem, r) => some r
        | _ => none
      pure <| if receivers.any names then #[.receiver] else #[]
    | _ => pure #[]
  return own ++ (← e.children.flatMapM (elementUses cx x inner))

/-- The quantifier that is directly the body `e` of a quantifier over
elements, a `forall` if `all`, if any, by its span: under a `forall`'s
`when`s, or as the last conjunct of an `exists`'s body, of the same kind
(`Fren.Core.ElementNesting`). -/
partial def elementSpine (all : Bool) : Expr → Option Span
  | .when _ false _ d => if all then elementSpine all d else none
  | .bin _ "and" _ b => if all then none else elementSpine all b
  | .quant sp a _ _ => if a == all then some sp else none
  | _ => none

/-- The expressions directly within `e`, in order. -/
def Expr.operands : Expr → Array Expr
  | .block _ _ members => members.map (·.2)
  | .when _ _ c d => #[c, d]
  | .ite _ c a b => #[c, a, b]
  | .bin _ _ a b | .pair _ a b | .index _ a b => #[a, b]
  | .not _ a | .neg _ a | .field _ a _ => #[a]
  | .app _ _ args | .set _ args | .seq _ args | .chain _ args _ => args
  | .method _ r _ args => #[r] ++ args
  | .record _ _ fs => fs.filterMap (·.2)
  | .update _ r fs => #[r] ++ fs.filterMap (·.2)
  | .match _ s arms _ => #[s] ++ armParts arms
  | .matches _ ss arms _ => ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)
  | .quant _ _ _ b | .closure _ _ b => #[b]
  | .is _ s _ => #[s]
  | .«let» _ defs body _ => defs.map (·.2.2) |>.push body
  | .table _ rows => tableParts rows
  | .num .. | .bool .. | .path .. | .str .. => #[]

/-- The names of one segment that `e` applies as functions, anywhere within
it: a function parameter is mentioned by applying it. -/
partial def Expr.appliedNames (e : Expr) : Array Name :=
  (match e with | .app _ #[s] _ => #[identName s.name] | _ => #[]) ++ e.operands.flatMap (·.appliedNames)

/-- The names that `e` declares, without their `!`: those of its `let`s and
`where` clauses, its bound names and its patterns' binders
(`Fren.Core.ForallCx`). -/
partial def Expr.declaredNames (e : Expr) : Array String :=
  let own := match e with
    | .«let» _ defs _ _ => defs.map fun (x, _, _) => (declaredIdent x).1.name
    | .quant _ _ bs _ => bs.flatMap (·.names) |>.map fun x => (declaredIdent x).1.name
    | .matches _ _ arms _ => arms.flatMap fun (ps, _, _) => ps.flatMap Pattern.names |>.map fun x => (declaredIdent x).1.name
    | .closure _ ps _ => ps.map fun (x, _) => (declaredIdent x).1.name
    | .match _ _ arms _ => arms.flatMap fun (p, _, _) => p.names.map fun x => (declaredIdent x).1.name
    | .is _ _ p => p.names.map fun x => (declaredIdent x).1.name
    | _ => #[]
  own ++ e.operands.flatMap (·.declaredNames)

/-- The integer literals of a pattern: its own, its bounds' and those of
its parts. -/
partial def Pattern.integerSpans : Pattern → Array Span
  | .num s _ => #[s]
  | .range _ lo hi _ => (lo.toArray ++ hi.toArray).filterMap fun | .num s _ => some s | _ => none
  | .variant _ _ (some args) => args.flatMap (·.integerSpans)
  | .or _ alts => alts.flatMap (·.integerSpans)
  | _ => #[]

/-- The integer literals of `e` and of its patterns, which
`zero_prefixed_literal` reads. -/
partial def Expr.integerSpans (e : Expr) : Array Span :=
  let own := match e with
    | .num s _ => #[s]
    | .match _ _ arms _ => arms.flatMap (·.1.integerSpans)
    | .matches _ _ arms _ => arms.flatMap fun (ps, _, _) => ps.flatMap Pattern.integerSpans
    | .is _ _ p => p.integerSpans
    | _ => #[]
  own ++ e.operands.flatMap (·.integerSpans)

/-- The span of `e` as written: a field read, method call or index of a
receiver in parentheses starts at the `(`, which its span leaves out. -/
partial def Expr.writtenSpan (src : Array Char) (e : Expr) : Span :=
  match e with
  | .field _ r _ | .method _ r _ _ | .index _ r _ =>
    let r := Fren.Core.withParens src (toRange (r.writtenSpan src))
    { e.span with start := r.start }
  | _ => e.span

/-- `e` as the lints that rewrite it (`Fren.Core.ExLint`) and the operator
lints see it, with its ranges counted from `base`. Given `src`, a field
read or method call is at its span as written. -/
partial def Expr.boolNode (e : Expr) (src : Array Char := #[]) (base : Nat := 0) : Fren.Core.BNode Span :=
  match e with
  | .block sp _ members => .mk .atom (toRange sp) sp (members.map (fun m => m.2.boolNode src base))
  | .when s n c d => .mk (.when n) (toRange s) s #[c.boolNode src base, d.boolNode src base]
  | .ite s c a b => .mk .ite (toRange s) s #[c.boolNode src base, a.boolNode src base, b.boolNode src base]
  | .bin s op a b => .mk (.bin op) (toRange s) s #[a.boolNode src base, b.boolNode src base]
  | .not s a => .mk .not (toRange s) s #[a.boolNode src base]
  | .neg s a => .mk .neg (toRange s) s #[a.boolNode src base]
  | .bool s b => .mk (.lit b) (toRange s) s #[]
  | .method s r m args =>
    let s := if src.isEmpty then s else e.writtenSpan src
    .mk (.method m.name) (toRange s) s (#[r.boolNode src base] ++ args.map (·.boolNode src base))
  | .app s _ args | .set s args | .seq s args => .mk .atom (toRange s) s (args.map (·.boolNode src base))
  | .record s _ fields => .mk .atom (toRange s) s (fields.filterMap (·.2.map (·.boolNode src base)))
  | .update s r fields => .mk .atom (toRange s) s (#[r.boolNode src base] ++ fields.filterMap (·.2.map (·.boolNode src base)))
  | .field s a _ =>
    let s := if src.isEmpty then s else e.writtenSpan src
    .mk .atom (toRange s) s #[a.boolNode src base]
  | .is s scrutinee _ => .mk .patternTest (toRange s) s #[scrutinee.boolNode src base]
  | .match s scrutinee arms _ => .mk .atom (toRange s) s (#[scrutinee.boolNode src base] ++ (armParts arms).map (·.boolNode src base))
  | .table s rows => .mk .atom (toRange s) s ((tableParts rows).map (·.boolNode src base))
  | .pair s a b | .index s a b => .mk .atom (toRange s) s #[a.boolNode src base, b.boolNode src base]
  | .chain s es ops => .mk (.chain (ops.map (·.1))) (toRange s) s (es.map (·.boolNode src base))
  | .«let» s _ body _ => .mk .«let» (toRange s) s #[body.boolNode src base]
  | .matches s ss arms _ => .mk .atom (toRange s) s ((ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)).map (·.boolNode src base))
  | .quant s _ _ b | .closure s _ b => .mk .quant (toRange s) s #[b.boolNode src base]
  | .num s _ | .path s _ | .str s .. => .mk .atom (toRange s) s #[]
-- `base` is at most the start of `e`'s span as written, and every span in
-- `e` is within it, so the subtractions do not truncate.
where toRange (sp : Span) : Fren.Core.Range := { start := sp.start - base, stop := sp.stop - base }

/-- The pairs of parentheses directly around `sp` in `src`, from the inside
out, each from its `(` to its `)`. -/
def parenLayers (src : Array Char) (sp : Span) : Array Span := Id.run do
  let mut out := #[]
  let mut (i, j) := (sp.start, sp.stop)
  repeat
    let mut a := i
    while a > 0 && src[a - 1]!.isWhitespace do a := a - 1
    let mut b := j
    while b < src.size && src[b]!.isWhitespace do b := b + 1
    unless a > 0 && src[a - 1]! == '(' && b < src.size && src[b]! == ')' do break
    (i, j) := (a - 1, b + 1)
    out := out.push { start := i, stop := j }
  return out

/-- Reports `double_parens` in `e` and within it (`lint::double_parens`),
where `call` says that `e` is the only argument of an application, whose
parentheses are not its own. The parentheses around `e` are those around
it as written (`writtenSpan`): a receiver's own, as in `({1}).card`, are
not. -/
partial def lintParens (e : Expr) (call : Bool := false) : M Unit := do
  let src := (← get).src
  let layers := parenLayers src (e.writtenSpan src)
  let layers := if call then layers.pop else layers
  if Fren.Core.doubleParens layers.size then
    lintFix .doubleParens layers.back! (Fren.Core.doubleParensMsg (String.ofList (src.extract layers[0]!.start layers[0]!.stop).toList))
  match e with
  | .app _ _ #[a] => lintParens a true
  | .method _ r _ #[a] => lintParens r; lintParens a true
  | _ => for k in e.operands do lintParens k

/-- The members of `e` if it is a pair, `(a, b)`, not in parentheses: in
them it would be an expression, which a pair is not. -/
def Expr.pair? (src : Array Char) : Expr → Option (Expr × Expr)
  | .pair s a b => if Fren.Core.enclosed src { start := 0, stop := src.size } (toRange s) then none else some (a, b)
  | _ => none

/-- Where `e`, an operand of `p`, is, as `lang::operand` sees it; `none`
where any expression can be written, as in parentheses. -/
def Expr.operandSlot (src : Array Char) (p e : Expr) : Option Fren.Core.Slot :=
  if Fren.Core.enclosed src { start := 0, stop := src.size } (toRange e.span) then none else
  match p with
  | .field _ x _ | .method _ x _ _ | .index _ x _ | .match _ x _ _ =>
    if x.span == e.span then some Fren.Core.receiverSlot else none
  | _ =>
    let .mk k _ _ kids := p.boolNode
    (kids.findIdx? fun | .mk _ r _ _ => r == toRange e.span).bind (k.slots[·]?.join)

/-- `e` as written, with the parentheses around it, and its precedence
(`lang::operand`). -/
def Expr.text (src : Array Char) (e : Expr) : Fren.Core.BText :=
  let r := Fren.Core.withParens src (toRange e.span)
  let prec := if r != toRange e.span then Fren.Core.BKind.atom.prec else match e.boolNode with | .mk k .. => k.prec
  { text := Fren.Core.textOf src r, prec }

/-- Whether a name declared in `cx`, or among `extra`, would hide
something in scope (`lang::shadowing`). -/
def hidesIn (cx : ExprCtx) (extra : Fren.Core.Locals := #[]) : M (String → Bool) := do
  let st ← get
  let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
    (cx.binders.map (·.what)) cx.selfFn.isSome ++ extra
  return fun n => (st.table.hidden? st.scope locals (Name.mkSimple n)).isSome

/-- Reports the expressions in `e` that the lints that rewrite them
(`Fren.Core.ExLint`) report, such as `Bool` expressions with a simpler form
(`nonminimal_bool`), the operator and method lints, the arithmetic lints
and double parentheses in it, once `e` is elaborated, where `hides` says
whether a name declared there would hide something in scope. -/
def lintBools (e : Expr) (hides : String → Bool) (onlyArg : Bool := false) : M Unit := do
  -- Not a rewrite of an expression with a pattern test that binds names,
  -- which could move what mentions them out of their scope
  -- (`lang::test_scope`).
  let tests := (← get).bindingTests
  modify fun s => { s with bindingTests := #[] }
  let keeps (sp : Span) := !tests.any fun t => sp.start ≤ t.start && t.stop ≤ sp.stop
  -- The text of `e` alone, as written, and `e` over it, as the Lean front
  -- end gives them: the three lints read no text outside `e`
  -- (`Fren.Core.upTo`), and report at the spans, which stay as they are.
  -- Cutting out `e`, not all the text before it, keeps the cost of each
  -- expression to its size.
  let full := (← get).src
  let w := e.writtenSpan full
  let src := full.extract w.start w.stop
  let root := e.boolNode full w.start
  -- A fix's own range is counted in `src`, from `w.start`.
  let shift (m : Msg) : Msg :=
    { m with fixes := m.fixes.map fun f => { f with range? := f.range?.map fun r => { start := r.start + w.start, stop := r.stop + w.start } } }
  for (l, ref, msg) in Fren.Core.rewriteReports src root do
    if keeps ref then lintFix l ref (shift msg)
  let (boolEqs, ordereds, variants, absEnds, mentioning, facts) :=
    ((← get).boolEqs, (← get).ordereds, (← get).variants, (← get).absEnds, (← get).mentioning, (← get).facts)
  modify fun s => { s with boolEqs := #[], ordereds := #[], variants := #[], absEnds := #[], mentioning := #[], facts := #[] }
  -- Looked up by span, in maps, rather than by reading the arrays, which
  -- would take time quadratic in the expression's size: the first entry
  -- for each span, as `find?` gives it, and whether one has the span, as
  -- `contains` says.
  let firstBySpan {α : Type} (xs : Array (Span × α)) : Std.HashMap Span α :=
    xs.foldl (init := {}) fun m (sp, a) => if m.contains sp then m else m.insert sp a
  let (variants, facts, ordereds) := (firstBySpan variants, firstBySpan facts, firstBySpan ordereds)
  let mentioning := firstBySpan mentioning
  let boolEqs := Std.HashSet.ofArray boolEqs
  let absEnds := Std.HashSet.ofArray absEnds
  let variant? (sp : Span) := variants[sp]?
  let fact? (sp : Span) := facts[sp]?
  let ordered? (sp : Span) := ordereds[sp]?
  let mentioned (sp : Span) := mentioning[sp]?.getD []
  let st ← get
  let fcx : Fren.Core.ForallCx :=
    { variants? := fun p => (st.dataOf? p.toName).bind fun d =>
        if d.isRecord || d.ctors.any (!·.2.isEmpty) then none else some d.ctors.size
      declared := e.declaredNames, hides, unguarded := !Fren.Core.hasGuarded (String.ofList src.toList) }
  for r in Fren.Core.opReports src boolEqs.contains ordered? variant? (absEnds.contains ·.stop) mentioned fact? fcx root do
    let ref := match r.last? with | some l => r.ref.to l | none => r.ref
    if keeps ref then lintFix r.lint ref (shift r.msg) r.unless?
  for r in Fren.Core.arithReports src root do
    if keeps r.ref then lintFix r.lint r.ref (shift r.msg)
  for sp in e.integerSpans do
    if let some (r, msg) := Fren.Core.zeroPrefixedReport? full (toRange sp) then
      lintFix .zeroPrefixedLiteral { start := r.start, stop := r.stop } msg
  -- The only argument of a call is in the call's parentheses, as a
  -- function's is.
  lintParens e onlyArg

/-- Which enumerations, records and newtypes are declared `ordered`
(`Reqs/Lang/Items#ordered-declarations`), for `Fren.Core.Ty.ordered`. -/
def State.orderedDecl (s : State) (p : Name) : Bool :=
  (s.dataOf? p).any (·.ordered) || s.orderedNewtypes.contains p

/-- `State.orderedDecl` of the current state. -/
def orderedDecl : M (Name → Bool) := return (← get).orderedDecl

/-- How values of `t` are compared, if it is ordered (`Fren.Core.orderPlan?`). -/
def orderPlan? (t : Ty) : M (Option Fren.Core.OrderPlan) := do
  let s ← get
  let fieldsOf (p : Name) := ((s.dataOf? p).filter (·.isRecord)).bind (·.ctors[0]?) |>.map (·.2.toList) |>.getD []
  return Fren.Core.orderPlan? s.orderedDecl fieldsOf (s.datatypes.size + s.newtypes.size) t

/-- `x < y`, or `x <= y` if not `strict`, of values compared by `o`, as
SMT-LIB: a record's lexicographically, by its fields in the order
declared, and a newtype's as its value's, which it is erased to. -/
partial def orderSmt (o : Fren.Core.OrderPlan) (strict : Bool) (x y : String) : M String := do
  let op := if strict then "<" else "<="
  match o with
  | .number => return s!"({op} {x} {y})"
  | .string => return Fren.Core.strCompareSmt x y !strict
  | .enum p as =>
    let some d := (← get).dataOf? p | return s!"({op} {x} {y})"
    return s!"({op} {d.ordinal x as} {d.ordinal y as})"
  | .newtype _ u => orderSmt u strict x y
  | .record p fs =>
    -- From the last field, compared as the whole is, back to the first,
    -- which decides unless the two are equal.
    let sel (f : Name) (v : String) := s!"({fieldSym p f} {v})"
    let some (fl, ol) := fs.getLast? | return (if strict then "false" else "true")
    let mut acc ← orderSmt ol strict (sel fl x) (sel fl y)
    for (f, of) in fs.dropLast.reverse do
      let (a, b) := (sel f x, sel f y)
      acc := s!"(or {← orderSmt of true a b} (and (= {a} {b}) {acc}))"
    return acc

/-- The ordering `op` of `x` and `y`, compared by `o`, as SMT-LIB: as
`orderSmt` writes it, with `>` and `>=` as `<` and `<=` of `y` and `x`, but
of numbers and enumerations, and newtypes of them, with `op` itself. -/
partial def orderingSmt (o : Fren.Core.OrderPlan) (op : String) (x y : String) : M String := do
  match o with
  | .newtype _ u => orderingSmt u op x y
  | .number => return s!"({op} {x} {y})"
  | .enum p as =>
    let some d := (← get).dataOf? p | return s!"({op} {x} {y})"
    return s!"({op} {d.ordinal x as} {d.ordinal y as})"
  | _ => match op with
    | "<" => orderSmt o true x y
    | "<=" => orderSmt o false x y
    | ">" => orderSmt o true y x
    | _ => orderSmt o false y x

/-- `e` has type `found` where `expected` was required. -/
def mismatch (e : Expr) (expected found : Ty) (why : Option String := none) : M α :=
  err e.span (Fren.Core.typeMismatchMsg expected found why)

/-- Calls the method `m` of the value `recv` of type `t`, with the
arguments `args`, each with its type and span (`lang::method_type`). -/
def callMethod (span : Span) (recv : String) (t : Ty) (m : String) (args : Array (String × Ty × Span)) :
    M (String × Ty) := do
  if let .rel a b := t then
    let project (k : Nat) (other : Ty) : M String := do
      if let some vs := (← get).values 64 other then
        let u := match vs.toList.map (s!"(tuple {·})") with
          | [] => s!"(as set.empty {(Ty.set other).sort})"
          | [v] => s!"(set.singleton {v})"
          | v :: vs => s!"(set.insert {v} {" ".intercalate vs.dropLast} (set.singleton {vs.getLast!}))"
        return if k == 0 then s!"(rel.join {recv} {u})" else s!"(rel.join {u} {recv})"
      modify fun s => { s with usesProjection := true }
      return s!"((_ rel.project {k}) {recv})"
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false true)
      | err span (Fren.Core.unknownMethodMsg m t.show false false true)
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    return ← match method with
      | .card => pure (s!"(set.card {recv})", .int)
      | .inverse => pure (s!"(rel.transpose {recv})", .rel b a)
      -- A join with every value of the other type, if it is finite; else a
      -- projection, which needs higher-order logic.
      | .domain => do pure (← project 0 b, .set a)
      | .range => do pure (← project 1 a, .set b)
      | .closure => do
        unless a == b do err span (Fren.Core.closureTypeMsg t.show)
        pure (s!"(rel.tclosure {recv})", t)
      | _ => do
        -- `image(s)`: `s` as a unary relation, joined with the relation.
        let (x, ta, sp) := args[0]!
        unless ta == .set a do
          err sp { code? := some "F0304", headline := s!"type mismatch: expected `{(Ty.set a).show}`, found `{ta.show}`"
                   label? := some s!"expected `{(Ty.set a).show}`, found `{ta.show}`"
                   notes := #[s!"note: the image of a `{t.show}` is of a set of its pairs' first members"] }
        pure (s!"(rel.join {x} {recv})", .set b)
  if let .set _ := t then
    unless m == "card" do err span (Fren.Core.unknownSetMethodMsg m t.show)
    unless args.isEmpty do err span (Fren.Core.arityMsg (Name.mkSimple m) 0 args.size)
    return (s!"(set.card {recv})", .int)
  if let .seq elem := t then
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false false true)
      | err span (Fren.Core.unknownMethodMsg m t.show false false false true)
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    let tyOf : Fren.Core.MethodTy → Ty | .bool => .bool | .int => .int | .elem => elem | _ => t
    for (_, ta, sp) in args, p in method.params, k in [0:args.size] do
      let tp := tyOf p
      unless ta.widens tp do
        err sp { code? := some "F0304", headline := s!"type mismatch: expected `{tp.show}`, found `{ta.show}`"
                 label? := some s!"expected `{tp.show}`, found `{ta.show}`"
                 notes := #[s!"note: argument {k + 1} of `{m}` is {if tp == .int then "an" else "a"} `{tp.show}`"] }
    let a := (args.map (·.1))[0]?.getD ""
    let b := (args.map (·.1))[1]?.getD ""
    let smt := match method with
      | .len => s!"(seq.len {recv})"
      | .startsWith => s!"(seq.prefixof {a} {recv})"
      | .endsWith => s!"(seq.suffixof {a} {recv})"
      | .contains => s!"(seq.contains {recv} {a})"
      | .at => s!"(seq.at {recv} {a})"
      | .slice => s!"(seq.extract {recv} {a} {b})"
      | .indexOf => s!"(seq.indexof {recv} {a} {b})"
      | .replace => s!"(seq.replace {recv} {a} {b})"
      | .update => s!"(seq.update {recv} {a} (seq.unit {b}))"
      | _ => s!"(seq.rev {recv})"
    return (smt, tyOf method.result)
  if t == .int || t == .nat then
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false (int := true))
      | err span (Fren.Core.unknownMethodMsg m t.show false (int := true))
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    for (_, ta, sp) in args, k in [0:args.size] do
      unless ta.widens .int do
        err sp { code? := some "F0304", headline := s!"type mismatch: expected `Int`, found `{ta.show}`"
                 label? := some s!"expected `Int`, found `{ta.show}`"
                 notes := #[s!"note: argument {k + 1} of `{m}` is an `Int`"] }
    -- Conditionals, so that they stay linear.
    let y := (args.map (·.1))[0]?.getD ""
    -- `min` and `max` of `Nat`s are `Nat`s (`lang::nat_result`).
    let op : Fren.Core.NatOp := match method with | .min => .min | .max => .max | _ => .abs
    let nat := Fren.Core.natResult op (t == .nat) (args.any (·.2.1 == .nat)) false
    return (match method with
      | .min => s!"(ite (<= {recv} {y}) {recv} {y})"
      | .max => s!"(ite (>= {recv} {y}) {recv} {y})"
      | _ => s!"(ite (< {recv} 0) (- {recv}) {recv})", if nat then .nat else .int)
  -- `min` and `max` of a value of an ordered type, and an enumeration's,
  -- record's or newtype's other methods, which it has none of
  -- (`lang::method_type`, `lang::ordered_type`).
  if t.orderedDecl?.isSome || (t == .string && (m == "min" || m == "max")) then
    let ordered := t.ordered (← get).orderedDecl
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false (ordered := ordered))
      | if ordered then err span (Fren.Core.unknownMethodMsg m t.show false (ordered := true))
        else if m == "min" || m == "max" then err span (Fren.Core.unorderedMethodMsg (t.orderedDecl?.getD .record) m t.show)
        else err span (Fren.Core.noMethodsMsg m t.show)
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    for (_, ta, sp) in args do
      unless ta == t do
        err sp { code? := some "F0304", headline := s!"type mismatch: expected `{t.show}`, found `{ta.show}`"
                 label? := some s!"expected `{t.show}`, found `{ta.show}`"
                 notes := #[s!"note: the argument of `{m}` is a `{t.show}`, as its receiver is"] }
    -- Conditionals on the order, as for an `Int`.
    let y := (args.map (·.1))[0]?.getD ""
    let some plan ← orderPlan? t | internal span s!"`{t.show}` is not ordered"
    let cmp ← orderingSmt plan (if method == .min then "<=" else ">=") recv y
    return (s!"(ite {cmp} {recv} {y})", t)
  unless t == .string do err span (Fren.Core.noMethodsMsg m t.show)
  let some method := (Fren.Core.Method.ofName? m).filter (·.accepts true false)
    | err span (Fren.Core.unknownMethodMsg m t.show (ordered := true))
  unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
  let tyOf : Fren.Core.MethodTy → Ty | .bool => .bool | .int => .int | _ => .string
  for (_, ta, sp) in args, p in method.params, k in [0:args.size] do
    let tp := tyOf p
    unless ta.widens tp do
      err sp { code? := some "F0304", headline := s!"type mismatch: expected `{tp.show}`, found `{ta.show}`"
               label? := some s!"expected `{tp.show}`, found `{ta.show}`"
               notes := #[s!"note: argument {k + 1} of `{m}` is {if tp == .int then "an" else "a"} `{tp.show}`"] }
  let a := (args.map (·.1))[0]?.getD ""
  let b := (args.map (·.1))[1]?.getD ""
  let smt := match method with
    | .len => s!"(str.len {recv})"
    | .startsWith => s!"(str.prefixof {a} {recv})"
    | .endsWith => s!"(str.suffixof {a} {recv})"
    | .contains => s!"(str.contains {recv} {a})"
    | .matches => s!"(str.in_re {recv} {a})"
    | .at => s!"(str.at {recv} {a})"
    | .slice => s!"(str.substr {recv} {a} {b})"
    | .indexOf => s!"(str.indexof {recv} {a} {b})"
    | .replace => s!"(str.replace {recv} {a} {b})"
    | .replaceAll => s!"(str.replace_all {recv} {a} {b})"
    | _ => s!"(set.card {recv})"
  return (smt, tyOf method.result)

/-- Reads the field `f` of the value `smt` of type `t`; of a `String`, calls
the method `f`, without arguments. -/
def readField (span : Span) (smt : String) (t : Ty) (f : Name) : M (String × Ty) := do
  -- The field `0` of a newtype, which is erased (`Reqs/Lang/Expressions#newtypes`).
  if let .newtype p u := t then
    if f == Name.mkSimple "0" then return (smt, u)
    err span (Fren.Core.noFieldMsg f (showPath p) #[Name.mkSimple "0"])
  -- A field named by digits is no method's name.
  if Fren.Core.positionalField f && !(t matches .record ..) then err span (Fren.Core.noFieldMsg f t.show #[])
  -- For `invalid_upcast_comparisons`, at the end of the expression.
  if (t == .int || t == .nat) && f == `abs then modify fun s => { s with absEnds := s.absEnds.push span.stop }
  if t matches .string | .set _ | .rel .. | .seq _ | .int | .nat then return ← callMethod span smt t f.toString #[]
  -- An enumeration's methods, `min` and `max`, which take an argument.
  if t matches .enum .. && (f == `min || f == `max) then return ← callMethod span smt t f.toString #[]
  let .record p args := t | err span (Fren.Core.noFieldMsg f t.show #[])
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let fields : Array (Name × Ty) := ((← get).dataOf? p).map (·.instCtors args |>.getD 0 default |>.2) |>.getD #[]
  let some (_, ft) := fields.find? (·.1 == f) | err span (Fren.Core.noFieldMsg f t.show (fields.map (·.1)))
  return (s!"({fieldSym p f} {smt})", ft)

/-- The types that the method `m` of the relation type `t` ranges over
(`Reqs/Lang/Decidability#relations`), or `none` if it is not relational. -/
def relRange? (t : Ty) (m : String) : Option (Array Ty) :=
  match t, Fren.Core.Method.ofName? m with
  | .rel a b, some .inverse => some #[a, b]
  | .rel a _, some .closure | .rel a _, some .image | .rel a _, some .range => some #[a]
  | .rel _ b, some .domain => some #[b]
  | _, _ => none

def andSmt (a b : String) : String := s!"(and {a} {b})"

/-- The SMT-LIB disjunction of `cs`. -/
def orSmt (cs : Array String) : String := if cs.size == 1 then cs[0]! else s!"(or {" ".intercalate cs.toList})"

/-- The indexes recorded since the last call, which it forgets. -/
def takeIndexes : M (Array (Span × String × Option (String × Bool))) := do
  let xs := (← get).indexes
  modify fun s => { s with indexes := #[] }
  return xs

/-- The source text at `span`. -/
def srcAt (span : Span) : M String := return String.ofList ((← get).src.extract span.start span.stop).toList

/-- Whether an infix operator follows `span` (`Fren.Core.followedAt`). -/
def followedSpan (span : Span) : M Bool := return Fren.Core.followedAt (← get).src (toRange span)

/-- Whether `e` is a set or relation literal, rather than a string or
sequence literal, and its characters or elements, if it is one of those. -/
def Expr.literalCount? : Expr → Option (Bool × Nat)
  | .str _ v => some (false, v.length)
  | .seq _ xs => some (false, xs.size)
  | .set _ xs => some (true, xs.size)
  | _ => none

/-- The receiver of `e`, if it reads `len` or `card` without arguments. -/
def lengthOf? : Expr → Option (Expr × Bool)
  | .path sp #[seg] =>
    let parts := seg.name.splitOn "."
    let m := parts.getLast?.getD ""
    if parts.length < 2 || !(m == "len" || m == "card") then none else
    let recv := ".".intercalate parts.dropLast
    let rs : Span := { sp with stop := sp.start + recv.length }
    some (.path rs #[{ name := recv, span := rs }], m == "card")
  | .field _ r f | .method _ r f #[] =>
    if f.name == "len" then some (r, false) else if f.name == "card" then some (r, true) else none
  | _ => none

/-- The receiver of `e` and the name it reads, if it reads a field or calls a
method without arguments. -/
def lastName? : Expr → Option (Expr × String)
  | .path sp #[seg] =>
    let parts := seg.name.splitOn "."
    if parts.length < 2 then none else
    let recv := ".".intercalate parts.dropLast
    let rs : Span := { sp with stop := sp.start + recv.length }
    some (.path rs #[{ name := recv, span := rs }], parts.getLast!)
  | .field _ r f | .method _ r f #[] => some (r, f.name)
  | _ => none

/-- The names that `e` reads one after another, innermost first, each with
its receiver. -/
partial def namesRead (e : Expr) : Array (Expr × String) :=
  match lastName? e with
  | some (r, n) => (namesRead r).push (r, n)
  | none => #[]

/-- The sequences that `e` indexes, as their text. -/
partial def indexedIn : Expr → M (Array String)
  | .block _ _ members => members.foldlM (fun acc (_, value) => return acc ++ (← indexedIn value)) #[]
  | .index _ q i => return #[← srcAt q.span] ++ (← indexedIn q) ++ (← indexedIn i)
  | .bin _ _ a b | .when _ _ a b | .pair _ a b => return (← indexedIn a) ++ (← indexedIn b)
  | .not _ a | .neg _ a | .field _ a _ | .is _ a _ => indexedIn a
  | .ite _ c a b => return (← indexedIn c) ++ (← indexedIn a) ++ (← indexedIn b)
  | .method _ r _ args => return (← indexedIn r) ++ (← args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[])
  | .app _ _ args | .set _ args | .seq _ args | .chain _ args _ => args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[]
  | .record _ _ fs => fs.foldlM (fun acc (_, e?) => return acc ++ (← (e?.map indexedIn).getD (pure #[]))) #[]
  | .match _ sc arms _ => return (← indexedIn sc) ++ (← (armParts arms).foldlM (fun acc b => return acc ++ (← indexedIn b)) #[])
  | .matches _ ss arms _ => (ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)).foldlM (fun acc b => return acc ++ (← indexedIn b)) #[]
  -- As the Lean front end reads it: the record, and the new values.
  | .update _ r fs => do
    fs.foldlM (init := ← indexedIn r) fun acc (_, e?) => return acc ++ (← (e?.map indexedIn).getD (pure #[]))
  | .quant _ _ _ b => indexedIn b
  | .table _ rows => (tableParts rows).foldlM (fun acc a => return acc ++ (← indexedIn a)) #[]
  | _ => return #[]

/-- Whether `e` bounds the sequence written `q`: it mentions `q.len`, or
compares `q` with `[]` (`lint::index_after_use`). -/
def boundsSeq (e : Expr) (q : String) : M Bool := do
  let t := (← srcAt e.span).replace " " ""
  return (t.splitOn s!"{q}.len").length > 1 || (t.splitOn s!"{q}!=[]").length > 1 || (t.splitOn s!"{q}=[]").length > 1

/-- Remove leading evaluation guards, keeping the operation and actual
arguments as part of a generated site's identity. -/
partial def siteOperation (formula : String) : String :=
  match Fren.Core.STerm.parse formula with
  | .list [.atom "=>", _, body] => siteOperation body.print
  | .list [.atom "ite", condition, yes, no] =>
    (Fren.Core.STerm.list [.atom "ite", condition, Fren.Core.STerm.parse (siteOperation yes.print), Fren.Core.STerm.parse (siteOperation no.print)]).print
  | .list (.atom "and" :: members) =>
    let operations := members.map fun member => siteOperation member.print
    if let first :: rest := operations then
      if rest.all (· == first) then first else (Fren.Core.STerm.list (.atom "and" :: members)).print
    else "(and)"
  | .list [.atom binder, bindings, body] =>
    if binder == "let" || binder == "forall" || binder == "exists" then
      (Fren.Core.STerm.list [.atom binder, bindings, Fren.Core.STerm.parse (siteOperation body.print)]).print
    else (Fren.Core.STerm.list [.atom binder, bindings, body]).print
  | term => term.print

/-- `goal` where `guards` hold. -/
def guarded (guards : Array String) (goal : String) : String :=
  if guards.isEmpty then goal else s!"(=> (and true {" ".intercalate guards.toList}) {goal})"

/-- `e` within the SMT-LIB `let`s of `binds`, each a symbol and its
definition, the first outermost. -/
def wrapLets (binds : Array (String × String)) (e : String) : String :=
  binds.foldr (fun (x, d) acc => s!"(let (({x} {d})) {acc})") e

/-- The term within the SMT-LIB `let`s that `wrapLets` puts around it, and
the `forall`s that an unbounded quantifier puts around an application in
its body (`natApps`), read outside string literals, where `""` is a `"`. -/
partial def peelLets (t : String) : String := Id.run do
  let start := if t.startsWith "(let ((" then 5 else if t.startsWith "(forall ((" then 8 else 0
  if start == 0 then return t
  let cs := t.toList.toArray
  -- The bindings start at the second `(`, and end where it closes.
  let mut depth := 0
  let mut inString := false
  let mut i := start
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then inString := !inString
    else if !inString && c == '(' then depth := depth + 1
    else if !inString && c == ')' then
      depth := depth - 1
      if depth == 0 then break
    i := i + 1
  -- `(let BINDINGS TERM)`.
  return peelLets (String.ofList (cs.extract (i + 2) (cs.size - 1)).toList)

/-- Records the index `q[i]` at `span`, whose sequence and position are the
SMT-LIB `q` and `i`, for the definedness check (`check::definedness`). -/
def noteIndex (cx : ExprCtx) (span : Span) (q i : String) : M Unit := do
  unless cx.noteIndexes do return
  let bounds := s!"(and (<= 0 {i}) (< {i} (seq.len {q})))"
  modify fun s => { s with indexes := s.indexes.push (span, guarded cx.guards bounds, none) }

/-- Records the obligation of the value `value`, in SMT-LIB, given at
`span` where the type `t` is declared, if it has one, for the subset-type
check (`Reqs/Check#subset-types`): its guard implies that the value
matches. It is a definedness goal, with its type beside it. -/
def noteObligation (cx : ExprCtx) (place : Fren.Core.ValuePlace) (span : Span) (t : Fren.Core.PTy) (value : String) :
    M Unit := do
  unless cx.noteIndexes do return
  let some o := Fren.Core.siteObligation place (t.obligation (← get).shapeOf) | return
  let st ← get
  for (label, part) in o.namedParts do
    let text := if label.isAnonymous then t.text else "@invariant:" ++ Fren.Core.showPath label
    modify fun s => { s with indexes := s.indexes.push (span, guarded cx.guards (consSmt st.dataOf? part value), some (text, part.quantifies)) }

/-- The declared type of the `k`th field or payload value of the variant
`v` of the record, newtype or enumeration `p`, with the type arguments
`args` for its type parameters, if it is generic (`Fren.Core.PTy.subst`). -/
def partPTy (p : Name) (v k : Nat) (args : Array Ty := #[]) : M Fren.Core.PTy := do
  let some t := ((← get).shapeOf p).bind (·.parts[v]?) |>.bind (·[k]?) | return default
  return if args.isEmpty then t else t.subst (args.map .plain)

/-- The value of a table of type `t` where no row holds: an index out of
range of the empty sequence, which is unspecified
(`Reqs/Lang/Expressions#tables`). -/
def unspecified (t : Ty) : String := s!"(seq.nth (as seq.empty (Seq {t.sort})) 0)"

/-- The questions about tables recorded since the last call, which it forgets. -/
def takeTables : M (Array (Span × Fren.Core.TableGoal × String)) := do
  let xs := (← get).tables
  modify fun s => { s with tables := #[] }
  return xs

/-- Records what each application of the uninterpreted function whose
symbol is `sym`, whose result has the declared type `rp`, brings: what its
result's type does, a `Nat`'s among it (`State.funFacts`). -/
def noteResultFactAt (sym : String) (rp : Fren.Core.PTy) : M Unit := do
  let st ← get
  if (rp.cons st.shapeOf).isNone then return
  let some c := rp.cons st.shapeOf (rp.ty == .nat) | return
  modify fun s => { s with funFacts := s.funFacts.insert sym (consSmt st.dataOf? c factHole)
                           quantifiedFns := if c.quantifies then s.quantifiedFns.insert sym else s.quantifiedFns }

/-- The symbol of the clause whose symbol is `csym`, of the generic
function at `path`, at its instance with the type arguments `args`. -/
def clauseInstSym (path : Name) (args : Array Ty) (csym : String) : String :=
  ((instSym path args).dropEnd 1).toString ++ (csym.drop (3 + (showPath path).length)).toString

/-- The symbol of the instance of the generic function at `path` with the
type arguments `args`, whose `define-fun`, and its clauses', it adds to
`defs` and `clauseDefs` the first time, after the instances that they
apply (`Reqs/Lang/GenericFunctions#meaning`): each is the function's own,
with the arguments' sorts for its type parameters' and the instances that
they give for those that it applies. Where `args` are the function's own
type parameters, it is the function's own symbol. -/
partial def instantiate (path : Name) (args : Array Ty) : M String := do
  let some g := (← get).genericFns.find? path | return itemSym path
  let own := g.params.mapIdx fun k p => Ty.abstract (Fren.Core.typeParamPath path k p)
  if args == own then return itemSym path
  let name := instName path args
  if let some sym := (← get).instSyms.find? name then return sym
  let sym := instSym path args
  -- Applied in its own contract, at another instance: made once its body
  -- and contract are known (`State.pendingInsts`).
  if (← get).fnTypeParams.any (·.1 == path) then
    modify fun s => { s with pendingInsts := s.pendingInsts.push args }
    return sym
  let inst (t : Ty) : Ty := (t.asParams path g.params).subst args
  let mut repl : Std.HashMap String String := {}
  for p in g.params, k in [0:g.params.size] do
    repl := repl.insert (itemSym (Fren.Core.typeParamPath path k p)) args[k]!.sort
  repl := repl.insert (itemSym path) sym
  for (csym, _, _) in g.clauses do repl := repl.insert csym (clauseInstSym path args csym)
  for (callee, cargs) in g.calls do
    if callee == path then continue
    repl := repl.insert (instSym callee cargs) (← instantiate callee (cargs.map inst))
  let clauses := g.clauses.map fun (csym, cvars, cbody) =>
    (clauseInstSym path args csym, cvars.map fun (x, t) => (x, inst t), replaceSymbols cbody repl)
  if !g.defined then
    -- An unknown function of its own, with the instance's sorts, whose
    -- applications bring its contract's postconditions and its result
    -- type's constraint at the instance, as any uninterpreted function's
    -- do (`lang::uninterpreted_instance`).
    let (ps, r) := Fren.Core.instanceSig g.declared g.result args
    let k := ((← get).contracts.find? path).getD {}
    let atInst (cs : Array (Name × String)) := cs.map fun (n, csym) => (n, clauseInstSym path args csym)
    modify fun s => { s with
      instSyms := s.instSyms.insert name sym
      funs := s.funs.push (name, ps, r)
      contracts := s.contracts.insert name { k with pres := atInst k.pres, posts := atInst k.posts }
      clauseDefs := s.clauseDefs ++ clauses }
    -- Its result type's constraint is the instance's.
    noteResultFactAt sym (Fren.Core.instanceResult g.resultP args)
    -- Its contract at the instance's sorts, with the instance for the
    -- function, for the check of its realizability where the one at the
    -- type parameters' sorts does not pass.
    if let some b := (← get).bodies.find? fun b => b.fn? == some path && b.generic then
      let instP (t : Fren.Core.PTy) := Fren.Core.instanceResult (t.asParams path g.params) args
      let vars ← b.vars.mapM fun v => do
        let ptype := instP v.ptype
        let st ← get
        return { v with ty := inst v.ty, ptype, fact? := (ptype.cons st.shapeOf).map (consSmt st.dataOf? · (quote v.name.toString)) }
      let rs (t : String) := replaceSymbols t repl
      let ic : CComp := { b with
        vars, generic := false, fn? := some (Fren.Core.instanceName path args), finiteModel := args.any (·.hasTypeParam)
        props := b.props.map fun p => { p with smt := rs p.smt, trigger? := p.trigger?.map rs }
        defs := b.defs.map fun (d, e) => (d, rs e)
        indexes := b.indexes.map fun (n, pl, sp, g, t) => (n, pl, sp, rs g, t)
        tables := b.tables.map fun (n, pl, sp, q, g) => (n, pl, sp, q, rs g)
        natApps := b.natApps.map rs }
      modify fun s => { s with instContracts := s.instContracts.insert path (((s.instContracts.find? path).getD #[]).push (args, ic)) }
    return sym
  if let some template := (← get).namedPredicates.find? path then
    let map (f : String) := replaceSymbols f repl
    let transform (c : NamedClause) := { c with
      formula := map c.formula
      branches := c.branches.map (·.map map)
      groups := c.groups.map (·.map map)
      indexes := c.indexes.map fun (sp, f, t) => (sp, map f, t)
      tables := c.tables.map fun (sp, q, f) => (sp, q, map f) }
    modify fun s => { s with namedPredicates := s.namedPredicates.insert name { template with
      clauses := template.clauses.map transform
      whole? := template.whole?.map transform } }
  let vars := g.vars.map fun (x, t) => (x, inst t)
  modify fun s => { s with
    instSyms := s.instSyms.insert name sym
    defs := s.defs.push (name, vars, g.result.subst args, replaceSymbols g.body repl)
    clauseDefs := s.clauseDefs ++ clauses }
  return sym

/-- The quoted symbols that the prelude declares: a closure captures each
other quoted symbol that it mentions free (`Fren.Core.inlineCall`). -/
def globalSyms : M (Std.HashSet String) := do
  let s ← get
  let mut g : Std.HashSet String := {}
  for p in s.sorts do g := g.insert (itemSym p)
  for d in s.datatypes do
    for x in d.syms do g := g.insert (quote x)
  for (p, _, _) in s.funs do g := g.insert (itemSym p)
  for (p, _, _, _) in s.defs do g := g.insert ((s.instSyms.find? p).getD (itemSym p))
  for (x, _, _) in s.clauseDefs do g := g.insert x
  return g

/-- `text`, the body or a precondition of the higher-order function at
`path`, at its instance with the type arguments `targs`: each type
parameter's sort is the argument's, and each generic function that it
applies is at the instance that the arguments give, which the function
being declared applies too (`State.genericCalls`). -/
partial def hofText (path : Name) (h : HigherOrderFn) (targs : Array Ty) (text : String) : M String := do
  if h.typeParams.isEmpty then return text
  let inst (t : Ty) : Ty := (t.asParams path h.typeParams).subst targs
  let mut repl : Std.HashMap String String := {}
  for p in h.typeParams, k in [0:h.typeParams.size] do
    repl := repl.insert (itemSym (Fren.Core.typeParamPath path k p)) targs[k]!.sort
  for (callee, cargs) in h.calls do
    let cargs' := cargs.map inst
    repl := repl.insert (instSym callee cargs) (← instantiate callee cargs')
    modify fun s => { s with genericCalls := s.genericCalls.push (callee, cargs') }
  return replaceSymbols text repl

/-- Records the questions about the application at `span` of the function
at `path` to the SMT-LIB arguments `args`, if the function has
preconditions, for the precondition check (`check::precondition`): its
guard implies each precondition at the arguments, in order; for a generic
function, its clauses at the instance with the type arguments `targs`. -/
def notePreconditions (cx : ExprCtx) (span : Span) (path : Name) (args : Array String) (targs : Array Ty := #[]) :
    M Unit := do
  unless cx.noteIndexes do return
  let some k := (← get).contracts.find? path | return
  -- Of a generic function, its clauses at the instance.
  let generic := !targs.isEmpty && (← instantiate path targs) != itemSym path
  let pres := k.pres.map fun (n, sym) =>
    (n, s!"({if generic then clauseInstSym path targs sym else sym} {" ".intercalate args.toList})")
  for (q, goal) in Fren.Core.preconditionQuestions (guarded cx.guards) path pres do
    modify fun s => { s with tables := s.tables.push (span, q, goal) }

/-- Records the questions about the rows of the table at `span`, whose
rows other than `_` have the SMT-LIB conditions `conds`, written at
`starts`, each row's condition or its `_`, whose indexes are in range where
`defined` says, for its completeness, disjointness and reachability checks
(`check::completeness`, `check::disjointness`, `check::reachability`):
completeness is reported at `table`, the disjointness of two rows at the
later one's condition, and the reachability of a row at its condition or
`_`. -/
def noteTable (cx : ExprCtx) (span : Span) (starts : Array Span) (conds : Array String) (defined : Array (Option String))
    (wild : Bool) : M Unit := do
  unless cx.noteIndexes do return
  for (g, f) in Fren.Core.tableGoals orSmt andSmt (s!"(not {·})") "true" conds defined wild do
    let at_ := match g with
      | .disjointness _ _ j | .reachability _ j => starts[j]!
      | _ => { start := span.start, stop := span.start + "table".length }
    modify fun s => { s with tables := s.tables.push (at_, g, guarded cx.guards f) }

/-- An item's questions, with each case's reachability questions merged
(`Fren.Core.mergeReach`). -/
def mergeReachTables (tbl : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) :
    Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) :=
  (Fren.Core.mergeReach andSmt (tbl.map fun (n, place, sp, g, f) => ((n, place, sp), g, f))).map
    fun ((n, place, sp), g, f) => (n, place, sp, g, f)

/-- Records the questions about the arms of the `match` at `span`, whose
patterns are at `pats`, each taken where `taken` says, of which those with
a guard are `guarded`, for its completeness and reachability checks
(`check::completeness`, `check::reachability`): completeness, unless its
arms without guards are exhaustive, is reported at `match`, and the
reachability of an arm at its pattern. Of a table over a scrutinee
(`table?`, the pairs of its arms that the disjointness check asks about,
whose guards' indexes are in range where `defined` says), also the
disjointness of those pairs, at the later arm's pattern, and completeness
at `table`. -/
def noteMatch (cx : ExprCtx) (span : Span) (pats : Array Span) (taken : Array (Option String)) (hasGuard : Array Bool)
    (unguardedExhaustive : Bool) (table? : Option (Array (Nat × Nat))) (defined : Array (Option String)) : M Unit := do
  unless cx.noteIndexes do return
  let complete := Fren.Core.completenessAsked unguardedExhaustive
  let goals := match table? with
    | some pairs => Fren.Core.tableMatchGoals orSmt andSmt (s!"(not {·})") "true" taken hasGuard defined pairs complete
    | none => Fren.Core.splitGoals .match orSmt andSmt (s!"(not {·})") "true" taken hasGuard complete
  let kw := if table?.isSome then "table" else "match"
  for (g, f) in goals do
    let at_ := match g with
      | .reachability _ j | .disjointness _ _ j => pats[j]!
      | _ => { start := span.start, stop := span.start + kw.length }
    modify fun s => { s with tables := s.tables.push (at_, g, guarded cx.guards f) }

/-- Records a `card`, of the receiver `recv` of type `t`: in a procedure that
applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (span : Span) (t : Ty) (m : String) (recv : Expr) : M Unit := do
  if cx.unmentioned then return
  if m == "card" && t matches .set _ | .rel .. && !(← isConstant cx recv) then
    modify fun s => { s with countSpans := s.countSpans.push span }

/-- Reports `undecidable` at each count of the current procedure, if it also
applies a relational operator; gives whether it does and whether it counts. -/
def checkCounts : M (Bool × Bool) := do
  let st ← get
  if st.relationalUsed then
    for sp in st.countSpans do
      modify fun s => { s with outsideCore := true }
      lint .undecidable sp (Fren.Core.undecidableMsg .relationalCard false)
  return (st.relationalUsed, !st.countSpans.isEmpty)

/-- Reports `undecidable` if a relational construct that ranges over `tys` is
outside the decidable core. -/
def checkRelational (cx : ExprCtx) (span : Span) (tys : Array Ty) (operands : Array Expr) : M Unit := do
  if cx.unmentioned then return
  let st ← get
  modify fun s => { s with relationalUsed := true }
  checkCore cx span .relational true true operands (← operands.allM (isConstant cx)) (finiteRange := tys.all (!st.infinite ·))

/-- The pattern `p`, resolved as `q`, as written (`Fren.Core.PatNode`): an
or-pattern is where its alternatives are, without a leading `|`. -/
partial def patNode (src : Array Char) (p : Pattern) (q : Fren.Core.Pat) : Fren.Core.PatNode Span :=
  let ps : Array Pattern := match p with
    | .or _ alts => alts
    | .variant _ _ (some args) => args
    | _ => #[]
  let qs : Array Fren.Core.Pat := match q with
    | .or qs | .ctor _ qs => qs
    | _ => #[]
  let sp := match p with
    | .or _ alts => alts[0]!.span.to alts.back!.span
    | p => p.span
  .mk q (Fren.Core.textOf src (toRange sp)) sp ((ps.zip qs).map fun (a, b) => patNode src a b)

/-- The lints of each or-pattern within the pattern `n`, of a `match` arm
or of `is` (`Reqs/Lint/Complexity/Patterns`): `wildcard_in_or_patterns`,
`manual_range_patterns` and `unnested_or_patterns`. -/
def lintOrPatterns (n : Fren.Core.PatNode Span) : M Unit := do
  for o in n.orPatterns do
    let alts := o.kids
    if Fren.Core.wildcardInOr (alts.any (·.pat matches .wild false)) then
      lintFix .wildcardInOrPatterns o.at_ Fren.Core.wildcardInOrMsg
    else if let some fixed := Fren.Core.manualRangeFix? (alts.map fun a => (a.pat, a.text)) then
      lintFix .manualRangePatterns o.at_ (Fren.Core.manualRangeMsg fixed)
    else
      for (i, j, fixed) in Fren.Core.unnestedRuns alts do
        lintFix .unnestedOrPatterns (alts[i]!.at_.to alts[j]!.at_) (Fren.Core.unnestedOrMsg fixed)

/-- The name that the binder written `x` declares, without its `!`. -/
def binderName (x : Ident) : String := (declaredIdent x).1.name

/-- `collapsible_match` on the arm `i` of the `match` `e`, whose patterns
are `pats` (`lint::collapsible_match`): the arm's pattern is one variant
whose payload's patterns are `_` or binders, and its body a `match` on one
of those binders. -/
def lintCollapsible (cx : ExprCtx) (arms : Array (Pattern × Option Expr × Expr)) (pats : Array Fren.Core.Pat) (i : Nat) : M Unit := do
  let src := (← get).src
  let (p, _, body) := arms[i]!
  let .variant _ segs (some args) := p | return
  let .ctor _ qs := pats[i]! | return
  let .match inner (.path _ #[x]) innerArms false := body | return
  -- An arm with a guard may not be taken where its pattern matches.
  if arms.any (·.2.1.isSome) || innerArms.any (·.2.1.isSome) then return
  let binders := (args.zip qs).filterMap fun
    | (.variant _ #[b] none, .wild true) => some (binderName b)
    | _ => none
  let isX : Pattern × Fren.Core.Pat → Bool
    | (.variant _ #[b] none, .wild true) => binderName b == x.name
    | _ => false
  let some k := (args.zip qs).findIdx? isX | return
  let flat := qs.all (· matches .wild _)
  let innerWildcard := innerArms.back?.any (·.1 matches .wild _)
  -- The first later arm that matches a value of the variant: one with `_`
  -- or a binder among its alternatives, since an arm that names the variant
  -- after this one is unreachable.
  let wild? := ((List.range arms.size).filter (· > i)).find? fun j => pats[j]!.top.any (· matches .wild _)
  let some d := innerArms.back? | return
  let sameWildcard := wild?.any fun j => pats[j]! matches .wild false &&
    Fren.Core.writtenSame (arms[j]!.2.2.text src).text (d.2.2.text src).text
  -- The inner `_` arm's body is taken where the outer one's is after the
  -- fix, outside the arm's pattern, so it must mention none of its binders.
  let dText := (d.2.2.text src).text
  let mentioned := Fren.Core.mentionsName (← srcAt { start := x.span.stop, stop := inner.stop }) x.name ||
    binders.any (Fren.Core.mentionsName dText ·)
  let innerBinders ← innerArms.flatMapM fun (q, _, _) => return (← patternBinders cx q).map binderName
  let clash := innerBinders.any binders.contains
  unless Fren.Core.collapsibleMatch true flat innerWildcard sameWildcard mentioned clash innerArms.size do return
  let armRange : Fren.Core.Range := { start := p.span.start, stop := (Fren.Core.withParens src (toRange body.span)).stop }
  let commented := Fren.Core.hasComment (Fren.Core.textOf src armRange)
  let path ← srcAt (segs[0]!.span.to segs.back!.span)
  let argTexts ← args.mapM (srcAt ·.span)
  let innerTexts ← (innerArms.pop).mapM fun (q, _, b) => do
    return (" | ".intercalate (← q.alts.mapM (srcAt ·.span)).toList, (b.text src).text)
  let fixed := Fren.Core.collapsedArms path argTexts k innerTexts
  let msg := Fren.Core.collapsibleMatchMsg x.name (if commented then none else some fixed)
  -- The fix replaces the outer arm, and the message is at the inner `match`.
  lintFix .collapsibleMatch inner { msg with fixes := msg.fixes.map ({ · with range? := some armRange }) }

/-- The match lints of the `match` `e` on a value of type `ty`, whose arms'
patterns are `pats`, where `slot` is (`Reqs/Lint/Style#matches-that-are-memberships`,
`Reqs/Lint/Pedantic/Matches`). The lints that move or remove arms, or
replace `_` with a variant, look only at a `match` whose patterns are all
flat (`Fren.Core.Pat.flat`), where no arm overlaps another without
containing it. -/
def lintMatch (cx : ExprCtx) (e : Expr) (ty : Ty) (pats : Array Fren.Core.Pat) (slot : Option Fren.Core.Slot) :
    M Unit := do
  let .match span scrutinee arms isTable := e | return
  let src := (← get).src
  -- A table over a scrutinee is called a table (`Fren.Core.Msg.ofTable`).
  let tm (m : Fren.Core.Msg) : Fren.Core.Msg := if isTable then m.ofTable else m
  -- An arm with a guard may not be taken where its pattern matches, so
  -- the lints that move, merge or remove arms, or replace the `match`,
  -- look only at a `match` without guards, and the arms with guards name
  -- no variant for the lints of `_` (`Reqs/Lint/Pedantic/Matches#arms`).
  let guarded := arms.map (·.2.1.isSome)
  let anyGuard := guarded.any id
  let mut infos : Array Fren.Core.ArmInfo := #[]
  for (p, _, body) in arms, pat in pats do
    let alts := if p matches .wild _ then #[] else p.alts.map fun a => Fren.Core.textOf src (toRange a.span)
    let binds := !(← patternBinders cx p).isEmpty
    infos := infos.push { alts, binds, noPayload := pat.noPayload, equatable := Fren.Core.equatable pat alts
                          disjoint := alts.isEmpty || Fren.Core.disjointPat pat alts, body := body.text src }
  let flat := pats.all (·.flat)
  -- `trivial_match` (`lint::trivial_match`).
  if let #[info] := infos then
    if Fren.Core.trivialMatch infos.size info.binds && !anyGuard then
      lintFix .trivialMatch span (tm (Fren.Core.trivialMatchMsg (info.body.inSlot slot (← followedSpan span))))
  -- `needless_match` (`lint::needless_match`).
  let st ← get
  let scr ← srcAt scrutinee.span
  let mut givenBack := true
  let mut wildcard := false
  let mut scrutineeBack := false
  -- Only a `match` whose arms are `_` and variants whose payloads'
  -- patterns are `_` or binders.
  let ep := match ty with
    | .enum p _ => p
    | _ => .anonymous
  for (p, _, body) in arms, pat in pats do
    match p, pat with
    | _, .wild false =>
      wildcard := true
      scrutineeBack := Fren.Core.writtenSame (← srcAt body.span) scr
    | .variant _ _ args?, .ctor idx qs =>
      unless qs.all (· matches .wild _) do givenBack := false; continue
      let binders := (args?.getD #[]).map fun
        | .variant _ #[x] none => x.name
        | _ => "_"
      -- The arm's binders shadow items in its body.
      let shadowing := cx.shadowing ++ (binders.filter (· != "_")).map Name.mkSimple
      let (segs?, args) := match body with
        | .path _ segs => (some segs, #[])
        | .app _ segs args => (some segs, args)
        | _ => (none, #[])
      let same := segs?.any fun segs => match st.table.resolvePath st.scope (segNames segs) shadowing with
        | .ok (.variant en i) => en.path == ep && i == idx
        | _ => false
      unless Fren.Core.givesBack same binders (← args.mapM (srcAt ·.span)) do givenBack := false
    | _, _ => givenBack := false
  let trivial := Fren.Core.trivialMatch infos.size (infos[0]?.any (·.binds))
  let needless := Fren.Core.needlessMatch (givenBack && !anyGuard) wildcard scrutineeBack trivial
  if needless then
    let bare : Fren.Core.BText := { text := scr, prec := scrutinee.boolNode.kind.prec }
    lintFix .needlessMatch span (tm (Fren.Core.needlessMatchMsg (bare.inSlot slot (← followedSpan span))))
  let bodyRanges := arms.map fun (_, _, b) => Fren.Core.withParens src (toRange b.span)
  let armRanges := arms.zipWith (fun (p, _) (b : Fren.Core.Range) => { start := p.span.start, stop := b.stop }) bodyRanges
  let groups := if flat && !anyGuard then Fren.Core.sameArmGroups infos else #[]
  let mut firstSame? : Option Span := none
  if flat && !anyGuard then
    let edits := Fren.Core.sameArmsEdits (toRange span) infos armRanges (arms.map (toRange ·.1.span)) bodyRanges slot (← followedSpan span)
    for g in groups do
      let (i, msg) := Fren.Core.sameArmsMsg infos g slot (← followedSpan span)
      let at_ : Span := { start := armRanges[i]!.start, stop := armRanges[i]!.stop }
      lintEdits .matchSameArms at_ (tm msg) (if firstSame?.isNone then edits else #[])
      if firstSame?.isNone then firstSame? := some at_
  let scr := scrutinee.text src
  let membership? := if anyGuard then none else Fren.Core.membershipParts? infos scr slot
  if let some (pre, post, test) := membership? then
    let r := Fren.Core.withParens src (toRange scrutinee.span)
    lintEdits .matchLikeMembership span (tm (Fren.Core.membershipMsg (pre ++ scr.text ++ post) test))
      #[({ start := span.start, stop := r.start }, pre), ({ start := r.stop, stop := span.stop }, post)]
  -- `single_match_else` (`lint::single_match_else`).
  let followed ← followedSpan span
  if let some fixed := (if anyGuard then none else
      Fren.Core.singleMatchElseFix? infos scr slot (membership?.isSome || needless || trivial) followed (ty == .bool)) then
    lintFix .singleMatchElse span (tm (Fren.Core.singleMatchElseMsg fixed (Fren.Core.hasComment (← srcAt span))))
  -- `match_bool` (`lint::match_bool`).
  if ty == .bool && !anyGuard then
    if let some fixed := Fren.Core.matchBoolFix? pats infos scr.text slot (membership?.isSome || trivial) (← followedSpan span) then
      lintFix .matchBool span (tm (Fren.Core.matchBoolMsg fixed (Fren.Core.hasComment (← srcAt span))))
  -- `match_overlapping_arm` (`lint::match_overlapping_arm`). An arm with a
  -- guard is left out, as in Clippy; the arms of a table over a scrutinee
  -- are checked to be disjoint instead.
  let intervals := (pats.zip guarded).map fun (p, g) => p.top.map fun
    | .int lo hi => if g || isTable then none else some (lo, hi)
    | _ => none
  for ((j, b), (i, a)) in Fren.Core.overlappingArms intervals do
    lint .matchOverlappingArm arms[j]!.1.alts[b]!.span (Fren.Core.overlappingArmMsg (← srcAt arms[i]!.1.alts[a]!.span))
  unless isTable do
    for i in [0:arms.size] do lintCollapsible cx arms pats i
  for (p, _, _) in arms, q in pats do lintOrPatterns (patNode src p q)
  -- In a table over a scrutinee, `_` also takes what the guards of the
  -- other arms leave, which no pattern can name without overlapping them.
  unless flat && !(isTable && anyGuard) do return
  let .enum ep _ := ty | return
  let some d := (← get).dataOf? ep | return
  let some w := (Array.range arms.size).find? fun i => arms[i]!.1 matches .wild _ && !guarded[i]! | return
  let names (p : Fren.Core.Pat) : Array Nat := match p with
    | .ctor k _ => #[k]
    | .or alts => alts.filterMap fun | .ctor k _ => some k | _ => none
    | _ => #[]
  let unguarded := (pats.zip guarded).filterMap fun (p, g) => if g then none else some p
  let covered := ((List.range d.ctors.size).filter fun k => !unguarded.any (names · |>.contains k)).toArray
  let siblings := (arms.flatMap (·.1.alts)).filterMap fun | .variant _ segs _ => some (segs.map (Name.mkSimple ·.name)) | _ => none
  let st ← get
  -- The pattern that names each variant that `_` matches, if one resolves.
  let named := covered.map fun k => (st.table.variantPath? st.scope cx.shadowing d.path d.ctors[k]!.1 siblings).map
    (Fren.Core.variantPattern · d.ctors[k]!.2.size)
  -- Removing an arm into `_` makes it cover more variants.
  let unless? := if groups.any (Fren.Core.groupFix infos · == .remove) then firstSame?.map (.matchSameArms, ·) else none
  -- `wildcard_enum_match_arm` (`lint::wildcard_enum_match_arm`).
  let (_, fixable) := Fren.Core.wildcardEnumMatchArm true (named.filter (·.isNone)).size
  let pattern? := if fixable then some (" | ".intercalate (named.filterMap id).toList) else none
  lintFix .wildcardEnumMatchArm arms[w]!.1.span (tm (Fren.Core.wildcardEnumMsg (covered.map (d.path ++ d.ctors[·]!.1)) pattern?))
    unless?
  unless Fren.Core.wildcardSingle covered.size do return
  lintFix .wildcardSingleVariant arms[w]!.1.span (tm (Fren.Core.wildcardMsg (d.path ++ d.ctors[covered[0]!]!.1) named[0]!)) unless?

/-- `match_could_be_table` on the `match` `e`, whose arms' patterns are
`pats`, on a value of `pty` (`lint::match_could_be_table`): the fix writes
`table` in place of the keyword. -/
def lintCouldBeTable (e : Expr) (sigs : Fren.Core.Sigs) (pty : Fren.Core.PatTy) (pats : Array Fren.Core.Pat) : M Unit := do
  let .match span _ arms false := e | return
  let guarded := arms.map (·.2.1.isSome)
  unless Fren.Core.matchCouldBeTable arms.size (guarded.any id) (Fren.Core.acceptedAsTable sigs pty pats guarded) do return
  let keyword : Fren.Core.Range := { start := span.start, stop := span.start + "match".length }
  unless (← srcAt { start := keyword.start, stop := keyword.stop }) == "match" do return
  let msg := Fren.Core.matchCouldBeTableMsg
  lintFix .matchCouldBeTable span { msg with fixes := msg.fixes.map ({ · with range? := some keyword }) }

/-- The value that the guard operand `v` is, as `redundant_guards` reads it,
with its text in a pattern and in an expression: a literal, or a variant
without a payload, which is written by its path (`Fren.Core.Table.variantPath?`). -/
def guardValue (cx : ExprCtx) (extra : Array Name) (sigs : Fren.Core.Sigs) (siblings : Array (Array Name)) (v : Expr) :
    M (Fren.Core.GuardValue × String × String) := do
  let other := (Fren.Core.GuardValue.other, "", "")
  match v with
  | .bool _ b => return (.pattern (.bool b), toString b, toString b)
  | .num _ n => return (.pattern (.int (some n) (some n)), toString n, toString n)
  | .neg _ (.num _ n) => return (.pattern (.int (some (-(n : Int))) (some (-(n : Int)))), s!"-{n}", s!"(-{n})")
  | .str sp t => let w ← srcAt sp; return (.pattern (.str t), w, w)
  | .path _ segs =>
    let st ← get
    let shadowing := cx.shadowing ++ extra
    let .ok (.variant en i) := st.table.resolvePath st.scope (segNames segs) shadowing | return other
    unless ((sigs en.path)[i]?.map (·.2.size)) == some 0 do return other
    let some path := st.table.variantPath? st.scope shadowing en.path en.variants[i]! siblings | return other
    let t := Fren.Core.variantPattern path 0
    return (.pattern (.ctor i #[]), t, t)
  | _ => return other

/-- `trivial_guard` and `redundant_guards` on the arms of the `match` `e`,
whose patterns are `pats`, on a value of `pty` (`lint::trivial_guard`,
`lint::redundant_guards`): each fix is given only where the static rules
accept the `match` after it (`Fren.Core.matchAccepted`). -/
def lintGuards (cx : ExprCtx) (e : Expr) (sigs : Fren.Core.Sigs) (pty : Fren.Core.PatTy) (pats : Array Fren.Core.Pat) :
    M Unit := do
  let .match _ _ arms isTable := e | return
  let src := (← get).src
  let tm (m : Fren.Core.Msg) : Fren.Core.Msg := if isTable then m.ofTable else m
  let guarded := arms.map (·.2.1.isSome)
  let siblings := (arms.flatMap (·.1.alts)).filterMap fun | .variant _ segs _ => some (segs.map (Name.mkSimple ·.name)) | _ => none
  let bodyStop (i : Nat) : Nat := (Fren.Core.withParens src (toRange arms[i]!.2.2.span)).stop
  for h : i in [0:arms.size] do
    let (p, g?, body) := arms[i]
    let some g := g? | continue
    let gStop := (Fren.Core.withParens src (toRange g.span)).stop
    -- `trivial_guard` (`lint::trivial_guard`).
    if let .bool _ b := g then
      let accepted := if b then Fren.Core.matchAccepted sigs pty pats (guarded.set! i false) isTable
        else Fren.Core.matchAccepted sigs pty (pats.eraseIdxIfInBounds i) (guarded.eraseIdxIfInBounds i) isTable
      -- What the fix removes: the guard, from the pattern's end; or the
      -- arm, up to the next one, or from the previous one's end.
      let removed : Fren.Core.Range := if b then { start := p.span.stop, stop := gStop }
        else if i + 1 < arms.size then { start := p.span.start, stop := arms[i + 1]!.1.span.start }
        else if i > 0 then { start := bodyStop (i - 1), stop := bodyStop i }
        else { start := p.span.start, stop := bodyStop i }
      let (_, fix) := Fren.Core.trivialGuard (.literal b) accepted (Fren.Core.hasComment (Fren.Core.textOf src removed))
      let msg := tm (Fren.Core.trivialGuardMsg b fix !accepted)
      lintFix .trivialGuard g.span { msg with fixes := msg.fixes.map ({ · with range? := some removed }) }
      continue
    -- `redundant_guards` (`lint::redundant_guards`).
    let .bin _ "=" l r := g | continue
    let bs ← patternBinders cx p
    let binders := bs.map binderName
    let soleName? : Expr → Option String
      | .path _ #[n] => some n.name
      | _ => none
    let some (x, v) := #[(l, r), (r, l)].findSome? fun (a, b) => (soleName? a).bind fun n =>
      if binders.contains n then some (n, b) else none | continue
    let (value, inPattern, inExpr) ← guardValue cx (binders.map Name.mkSimple) sigs siblings v
    let some q := Fren.Core.redundantGuard? pats[i]! (Fren.Core.guardBinderPath? pats[i]! (binders.idxOf? x)) value | continue
    unless Fren.Core.matchAccepted sigs pty (pats.set! i q) (guarded.set! i false) isTable do continue
    let some bx := bs.find? (binderName · == x) | continue
    let pattern := Fren.Core.textOf src { start := p.span.start, stop := bx.span.start } ++ inPattern ++
      Fren.Core.textOf src { start := bx.span.stop, stop := p.span.stop }
    let bodyText := Fren.Core.textOf src (Fren.Core.withParens src (toRange body.span))
    let head : Fren.Core.Range := { start := p.span.start, stop := gStop }
    let commented := Fren.Core.hasComment (Fren.Core.textOf src head)
    let why := "note: the fix would drop the comments in the arm's pattern or guard, so it has none"
    let (fixed?, why?) :=
      if !Fren.Core.mentionsName bodyText x then
        if commented then (none, some why) else (some (pattern, head), none)
      else match Fren.Core.replaceMentions? bodyText x inExpr with
        | some b' => if commented then (none, some why)
          else (some (s!"{pattern} => {b'}", { head with stop := bodyStop i }), none)
        | none => (none, some s!"note: the body mentions `{x}` where its value cannot be written in its place, so it has no fix")
    let msg := tm (Fren.Core.redundantGuardsMsg x (← srcAt v.span) (fixed?.map (·.1)) why?)
    lintFix .redundantGuards g.span { msg with fixes := msg.fixes.map ({ · with range? := fixed?.map (·.2) }) }

/-- `match_arm_if_else` on the `match` `e`, whose arms' patterns are
`pats`, on a value of `pty` (`lint::match_arm_if_else`): the fix moves each
condition into its arm's guard, and adds a `_` arm with the `else` branch
where the last arm is not one. -/
def lintArmIfElse (cx : ExprCtx) (e : Expr) (sigs : Fren.Core.Sigs) (pty : Fren.Core.PatTy) (pats : Array Fren.Core.Pat) :
    M Unit := do
  let .match _ _ arms false := e | return
  if arms.any (·.2.1.isSome) then return
  let src := (← get).src
  let mut infos : Array (Fren.Core.IfArmInfo String) := #[]
  let mut binders : Array (Array String) := #[]
  for (p, _, body) in arms, q in pats do
    let armBody : Fren.Core.IfArmBody String := match body with
      | .ite _ _ _ d => .ifElse (d.text src).text
      | _ => .plain (body.text src).text
    -- A condition that binds names cannot be a guard (`F0334`).
    let condBinds ← match body with
      | .ite _ c _ _ => chainBinds cx c
      | _ => pure false
    binders := binders.push ((← patternBinders cx p).map binderName)
    infos := infos.push { wild := q matches .wild _, body := armBody, binds := condBinds }
  -- `d` names a binder of arm `j`'s pattern.
  let mentions (d : String) (j : Nat) : Bool := binders[j]!.any (Fren.Core.mentionsName d ·)
  let overlap (i j : Nat) : Bool := (pats[i]!.overlapWit? sigs pty pats[j]!).isSome
  let some (group, d, append) := Fren.Core.matchArmIfElse? Fren.Core.writtenSame mentions overlap infos.toList
    | return
  let guarded := (Array.range arms.size).map group.contains
  let (pats', guarded') := if append then (pats.push (.wild false), guarded.push false) else (pats, guarded)
  unless Fren.Core.matchAccepted sigs pty pats' guarded' false do return
  let bodyStop (i : Nat) : Nat := (Fren.Core.withParens src (toRange arms[i]!.2.2.span)).stop
  let part (e : Expr) : M String := return Fren.Core.rowPart (← srcAt e.span) (e matches .when .. | .quant .. | .«let» ..)
  let mut edits : Array (Fren.Core.Range × String) := #[]
  let mut commented := false
  for i in group do
    let (p, _, body) := arms[i]!
    let .ite _ c a _ := body | return
    let r : Fren.Core.Range := { start := p.span.stop, stop := bodyStop i }
    commented := commented || Fren.Core.hasComment (Fren.Core.textOf src r)
    edits := edits.push (r, s!" if {← part c} => {← part a}")
  if append then
    let .ite _ _ _ de := arms[group[0]!]!.2.2 | return
    let stop := bodyStop (arms.size - 1)
    edits := edits.push ({ start := stop, stop }, s!", _ => {← part de}")
  let msg := Fren.Core.matchArmIfElseMsg group.size d commented
  let at_ := arms[group[0]!]!.2.2.span
  if commented then lint .matchArmIfElse at_ msg else lintEdits .matchArmIfElse at_ msg edits

/-! ## Patterns -/

/-- A binder of a pattern, with the type of its value, and its value, read
from the scrutinee with selectors. -/
structure PBinder where
  source? : Option Expr := none
  ident : Ident
  ty : Ty
  smt : String
  /-- Bound from a payload of the scrutinee, directly or nested, rather
  than to the whole scrutinee. -/
  payload : Bool := false
  deriving Inhabited

/-- The variants of each enumeration, with their payloads' types, as
patterns see them. -/
def patSigs : M Fren.Core.Sigs := do
  let st ← get
  return fun p => ((st.dataOf? p).map fun d => d.ctors.map fun (c, fs) => (c, fs.map (·.2.patTy))).getD #[]

/-- The conjunction of `ts` in SMT-LIB, `none` for none. -/
def smtConj (ts : Array String) : Option String :=
  match ts with
  | #[] => none
  | #[t] => some t
  | ts => some s!"(and {" ".intercalate ts.toList})"

/-- The value of the bound `b` of a range pattern. -/
def boundValue (cx : ExprCtx) (b : Bound) : M Int := do
  match b with
  | .num _ v => return v
  | .path sp segs =>
    if segs.size == 1 then
      let n := identName segs[0]!.name
      if cx.vars.any (·.name == n.getRoot) then err sp (Fren.Core.rangeBoundMsg "a variable")
      if (cx.binder? n.getRoot).isSome then err sp (Fren.Core.rangeBoundMsg "a binder")
    match ← resolve segs cx.shadowing with
    | .item { kind := .constItem, path, .. } =>
      let some (_, t) := (← get).consts.find? path | internal sp s!"unknown constant `{path}`"
      unless t matches .int | .nat do err sp (Fren.Core.rangeBoundMsg s!"a constant of `{t.show}`")
      let some v := (← get).constInts.find? path | err sp (Fren.Core.rangeConstantMsg path)
      return v
    | r => err sp (Fren.Core.rangeBoundMsg r.describe)

/-- Resolves the pattern `p` of a value of type `ty`, which is `x` in
SMT-LIB (`Reqs/Lang/Patterns`), within an or-pattern if `inOr`: the
pattern, its binders in preorder, and its test, `none` if it matches every
value. In a pattern test (`test`), a binder is reported once the pattern is
resolved, rather than within an or-pattern. -/
partial def resolvePattern (cx : ExprCtx) (ty : Ty) (x : String) (inOr test : Bool) (p : Pattern) :
    M (Fren.Core.Pat × Array PBinder × Option String) := do
  let wrong (sp : Span) (what : String) : M Unit := err sp (Fren.Core.patternTypeMsg ty.show what)
  match p with
  | .wild _ => return (.wild, #[], none)
  | .str sp v =>
    unless ty == .string do wrong sp "a pattern of `String`"
    liftMsg sp (Fren.Core.checkStringChars v)
    modify fun s => { s with usesStrings := true }
    return (.str v, #[], some s!"(= {x} {Fren.Core.smtStringLit v})")
  | .num sp v =>
    unless ty matches .int | .nat do wrong sp "a pattern of `Int`"
    return (.int v v, #[], some s!"(= {x} {smtInt v})")
  | .range sp lo hi inclusive =>
    unless ty matches .int | .nat do wrong sp "a pattern of `Int`"
    let lo' ← lo.mapM (boundValue cx)
    let hi' ← hi.mapM (boundValue cx)
    if Fren.Core.rangeEmpty lo' hi' inclusive then err sp (Fren.Core.emptyRangeMsg (← srcAt sp))
    let (l, h) := Fren.Core.rangeInterval lo' hi' inclusive
    return (.int l h, #[], smtConj (l.toArray.map (s!"(<= {smtInt ·} {x})") ++ h.toArray.map (s!"(<= {x} {smtInt ·})")))
  | .variant sp segs args? =>
    if segs.size == 1 && args?.isNone then
      match ← patternName cx segs[0]! with
      | .boolLiteral =>
        unless ty == .bool do wrong sp "a pattern of `Bool`"
        let b := segs[0]!.name == "true"
        return (.bool b, #[], some (if b then x else s!"(not {x})"))
      | .binder =>
        if inOr && !test then err sp (Fren.Core.orBinderMsg (Name.mkSimple (declaredIdent segs[0]!).1.name))
        return (.wild true, #[{ ident := segs[0]!, ty, smt := x }], none)
      | .variant => pure ()
    let r ← resolveWritten segs cx.shadowing cx.noteIndexes
    let .enum ep tyArgs := ty
      | err sp (Fren.Core.patternTypeMsg ty.show (match r with
          | .variant en _ => s!"a pattern of `{showPath en.path}`"
          | r => r.describe))
    let .variant en idx := r | err sp (Fren.Core.notAVariantOfMsg ep r.describe)
    if en.path != ep then err sp (Fren.Core.notAVariantOfMsg ep s!"a variant of `{showPath en.path}`")
    let some d := (← get).dataOf? ep | internal sp s!"unknown enum `{ep}`"
    -- The payload's types, with the scrutinee's arguments (`lang::instantiation`).
    let (c, fs) := (d.instCtors tyArgs)[idx]!
    let v := ep ++ en.variants[idx]!
    if let some msg := Fren.Core.variantMentionMsg? v fs.size args?.isSome then err sp msg
    let args := args?.getD #[]
    unless args.size == fs.size do err sp (Fren.Core.arityMsg v fs.size args.size "pattern")
    let mut pats := #[]
    let mut bs := #[]
    let mut tests := #[d.tester idx x tyArgs]
    for a in args, (_, t) in fs, k in [0:args.size] do
      let (q, qbs, qt) ← resolvePattern cx t s!"({d.selSym c k} {x})" inOr test a
      pats := pats.push q
      bs := bs ++ qbs.map ({ · with payload := true })
      tests := tests ++ qt.toArray
    return (.ctor idx pats, bs, smtConj tests)
  | .or _ alts =>
    let mut pats := #[]
    let mut bs := #[]
    let mut tests := #[]
    let mut every := false
    for a in alts do
      let (q, qbs, qt) ← resolvePattern cx ty x true test a
      pats := pats.push q
      bs := bs ++ qbs
      match qt with
      | some t => tests := tests.push t
      | none => every := true
    return (.or pats, bs, if every then none else if tests.size == 1 then tests[0]? else some s!"(or {" ".intercalate tests.toList})")

/-- The variant that `e` names, if it is a path to one without a payload:
its enumeration, its index and its text. -/
def variantOf? (cx : ExprCtx) : Expr → M (Option (Name × Nat × String))
  | .path span segs => do
    let st ← get
    let .ok (.variant en idx) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | return none
    unless ((st.dataOf? en.path).bind (·.ctors[idx]?)).any (·.2.isEmpty) do return none
    return some (en.path, idx, ← srcAt span)
  | _ => return none

/-- `e` as a test of which variant a scrutinee is, if it is one
(`Fren.Core.VariantTest`). -/
partial def variantTest? (cx : ExprCtx) : Expr → M (Option Fren.Core.VariantTest)
  | .bin _ "or" a b => do
    let some x ← variantTest? cx a | return none
    let some y ← variantTest? cx b | return none
    return x.or y
  | .bin _ "=" l v => do
    let some (en, i, t) ← variantOf? cx v | return none
    return some { scrutinee := ← srcAt l.span, enum := en, variants := #[(i, t)] }
  | .is _ l p => do
    -- `x is P`, of the variants that `P` names, each with only `_` in its
    -- payload, so that it tests the variant alone.
    let st ← get
    let mut out : Array (Nat × String) := #[]
    let mut en? : Option Name := none
    for alt in p.alts do
      let .variant span segs args := alt | return none
      unless (args.getD #[]).all (· matches .wild _) do return none
      let .ok (.variant en i) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | return none
      unless en?.all (· == en.path) do return none
      en? := some en.path
      out := out.push (i, ← srcAt span)
    let some en := en? | return none
    return some { scrutinee := ← srcAt l.span, enum := en, variants := out }
  | .bin _ "in" l (.set _ vs) => do
    let mut out : Array (Nat × String) := #[]
    let mut en? : Option Name := none
    for v in vs do
      let some (en, i, t) ← variantOf? cx v | return none
      unless en?.all (· == en) do return none
      en? := some en
      out := out.push (i, t)
    let some en := en? | return none
    return some { scrutinee := ← srcAt l.span, enum := en, variants := out }
  | _ => return none

/-- The tests, the branches and the final `else` of a chain of `if`. -/
partial def ifChain : Expr → Array Expr × Array Expr × Expr
  | .ite _ c a b => let (cs, as, z) := ifChain b; (#[c] ++ cs, #[a] ++ as, z)
  | z => (#[], #[], z)

/-- The text of `e` as the body of a `match` arm. -/
def armBodyOf (e : Expr) : M String := return Fren.Core.armBody (← srcAt e.span) (e matches .when .. | .quant ..)

/-- The text of `e` as a row's condition or value in a table. -/
def rowPartOf (e : Expr) : M String := return Fren.Core.rowPart (← srcAt e.span) (e matches .when .. | .quant .. | .«let» ..)

/-- `if_chain_match` and `manual_table` on the chain of `if` that starts at
`e` (`lint::if_chain_match`, `lint::manual_table`). -/
def lintIfChain (cx : ExprCtx) (e : Expr) : M Unit := do
  let (cs, as, z) := ifChain e
  -- A table's row does not see what its condition's pattern tests bind
  -- (`lang::test_scope`).
  if ← cs.anyM (chainBinds cx) then return
  let ts? := Fren.Core.sameScrutinee (← cs.mapM (variantTest? cx))
  let ts := ts?.getD #[]
  let enums := (← get).table.enums
  let n := ((ts[0]?.bind fun t => enums.get? t.enum).map (·.variants.size)).getD 0
  let (fires, wildcard) := Fren.Core.ifChainMatch cs.size ts?.isSome (Fren.Core.repeatedVariants ts)
    (Fren.Core.untestedVariants n ts)
  -- `manual_table` (`lint::manual_table`).
  if Fren.Core.manualTable cs.size ts?.isSome then
    lint .manualTable e.span (Fren.Core.manualTableMsg (← cs.mapM rowPartOf) (← as.mapM rowPartOf) (← rowPartOf z))
  unless fires do return
  let final? ← if wildcard then some <$> armBodyOf z else pure none
  lintFix .ifChainMatch e.span (Fren.Core.ifChainMatchMsg ts (← as.mapM armBodyOf) final?)

/-- `redundant_bindings` on the binding, or field, `b := e`
(`lint::redundant_bindings`). -/
def lintRedundant (b : Ident) (e : Expr) (field : Bool) : M Unit := do
  let after := (Fren.Core.withoutComments (← srcAt { start := b.span.stop, stop := e.span.stop })).trimAscii.toString
  let value := String.ofList (after.toList.drop 2)
  if after.startsWith ":=" && Fren.Core.redundantBinding (Fren.Core.writtenForm b.name) (Fren.Core.writtenForm value) then
    lintFix .redundantBindings (b.span.to e.span) (Fren.Core.redundantBindingMsg b.name field)

/-- The generic enumeration or record that `e` builds, if it builds one
(`Reqs/Lang/Generics#type-arguments`): its declaration, the constructor's
index, its values' declared types, and its values in their order, a
record's fields in the order of its declaration, `none` for one that is not
given. -/
def construction? (cx : ExprCtx) (e : Expr) : M (Option (DataDecl × Nat × Array Ty × Array (Option Expr))) := do
  let st ← get
  let variant (segs : Array Ident) (vals : Array Expr) : Option (DataDecl × Nat × Array Ty × Array (Option Expr)) := do
    let .ok (.variant en idx) := st.table.resolvePath st.scope (segNames segs) cx.shadowing | none
    let d ← st.dataOf? en.path
    guard !d.params.isEmpty
    let (_, fs) ← d.ctors[idx]?
    return (d, idx, fs.map (·.2), vals.map some)
  match e with
  | .path _ segs => return variant segs #[]
  | .app _ segs args => return variant segs args
  | .record _ tySegs fields =>
    let .ok (.item { kind := .recordItem, path, .. }) := st.table.resolvePath st.scope (segNames tySegs) cx.shadowing
      | return none
    let some d := st.dataOf? path | return none
    if d.params.isEmpty then return none
    let fs := d.ctors[0]!.2
    return some (d, 0, fs.map (·.2), fs.map fun (f, _) =>
      (fields.find? (Name.mkSimple ·.1.name == f)).map fun (fi, e?) => e?.getD (.path fi.span #[fi]))
  | _ => return none

/-- `e`'s shape, for whether it synthesizes a type (`Fren.Core.TypeShape`). -/
partial def typeShape (cx : ExprCtx) (e : Expr) : M Fren.Core.TypeShape := do
  if let some (d, _, declared, vals) ← construction? cx e then
    let shapes ← vals.mapM fun v? => match v? with
      | some v => typeShape cx v
      | none => pure .other
    return Fren.Core.constructionShape d.params declared shapes
  -- An application of a generic function (`Reqs/Lang/GenericFunctions#applications`).
  if let .app _ segs args := e then
    let st ← get
    if let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing then
      if let some g := st.genericFns.find? path then
        return Fren.Core.callShape g.params.size g.declared g.result (← args.mapM (typeShape cx))
      if let some h := (st.hofs.find? path).filter (!·.typeParams.isEmpty) then
        return Fren.Core.callShape h.typeParams.size (h.params.map (·.2.2.ty)) h.result (← args.mapM (typeShape cx))
  match e with
  | .set _ #[] | .seq _ #[] => return .emptyLiteral
  | .set _ es | .seq _ es => return .anyPart (← es.toList.mapM (typeShape cx))
  | .pair _ a b => return .pair (← typeShape cx a) (← typeShape cx b)
  | .bin _ op a b => if op == "union" || op == "inter" || op == "minus" || op == "++" then
      return .anyPart [← typeShape cx a, ← typeShape cx b] else return .other
  | .ite _ _ a b => return .anyPart [← typeShape cx a, ← typeShape cx b]
  | .match _ _ arms _ => return .anyPart (← arms.toList.mapM (typeShape cx ·.2.2))
  | .matches _ ss arms _ => if ss.isEmpty then return .other else return .anyPart (← arms.toList.mapM (typeShape cx ·.2.2))
  | .«let» _ _ body _ => return .anyPart [← typeShape cx body]
  | .table _ rows => return .anyPart (← rows.toList.mapM (typeShape cx ·.2.2))
  | _ => return .other

/-- Whether `e` synthesizes a type (`lang::synthesizes`). -/
def synthesizes (cx : ExprCtx) (e : Expr) : M Bool := return (← typeShape cx e).synthesizes

/-- Elaborates the values `vals` of a construction of the generic type `d`,
written `what`, at `span`, whose values have the declared types `declared`,
with `elabValue`, and returns their SMT-LIB terms and its type arguments, which
are inferred (`Fren.Core.inferConstruction`). `note k t` explains that
value `k` has the type `t`. -/
def elabConstruction (elabValue : ExprCtx → Expr → M (String × Ty)) (site : Fren.Core.ExprSite) (cx : ExprCtx) (d : DataDecl) (declared : Array Ty)
    (vals : Array Expr) (span : Span) (what : String) (note : Nat → Ty → String) : M (Array String × Array Ty) := do
  let expected? := match cx.expected? with
    | some (.enum p as) | some (.record p as) => if p == d.path then some as.toArray else none
    | _ => none
  let synth ← vals.mapM (synthesizes cx)
  let go : StateT (Array String) M (Array Ty) :=
    Fren.Core.inferConstruction d.params declared synth expected?
      (err span (Fren.Core.cannotInferMsg what (showPath d.path)) : M Unit)
      (fun k x? => do
        let (smt, t) ← (elabValue { cx with expected? := site.expected x? none } vals[k]! : M _)
        modify fun a => a.set! k smt
        return some t)
      (fun k x f => (liftMsg vals[k]!.span (Fren.Core.checkType x f (some (note k x))) : M Unit))
  let (args, smts) ← go.run (vals.map fun _ => "")
  return (smts, args)

/-- How `e` is written, for whether it is written as a sequence
(`Fren.Core.WrittenShape`). Parentheses are not kept in an `Expr`, so
none is `WrittenShape.parenthesized`. -/
partial def writtenShape : Expr → Fren.Core.WrittenShape
  | .seq .. => .seqLiteral
  | .bin _ "++" a b => .concat (writtenShape a) (writtenShape b)
  | .ite _ _ a b => .conditional (writtenShape a) (writtenShape b)
  | .match _ _ arms _ => .match (arms.toList.map (writtenShape ·.2.2))
  | .matches _ _ arms _ => .match (arms.toList.map (writtenShape ·.2.2))
  | .«let» _ _ body _ => .let (writtenShape body)
  | .table _ rows => .table (rows.toList.map (writtenShape ·.2.2))
  | _ => .other

/-- Whether `e` is written as a sequence, so that the right of `in` is
checked against a sequence (`lang::written_sequence`). -/
def seqShaped (e : Expr) : Bool := (writtenShape e).sequence

/-- The span of the type written `segs`, from its first token to its last:
a pattern's segment may come before its base's (`Parser.patOuterSeg`). -/
def typeSpan (segs : Array Ident) : Span :=
  { start := segs.foldl (fun m s => min m s.span.start) segs[0]!.span.start
    stop := segs.foldl (fun m s => max m s.span.stop) 0 }

/-- The constraint that a value of the declared type `t` brings
(`Fren.Core.PTy.cons`). -/
def consOf (t : Fren.Core.PTy) : M (Option Fren.Core.Cons) := do
  let s ← get
  return t.cons s.shapeOf

/-- `x`'s constraint of the type `t`, in SMT-LIB, if it has one. -/
def factOf (t : Fren.Core.PTy) (x : String) : M (Option String) := do
  let s ← get
  return (t.cons s.shapeOf).map (consSmt s.dataOf? · x)

/-- The span of the type written `segs`, as `typeSpan` gives it, with the
`>` of each `Set<`, `Seq<` and `Rel<` within it that it leaves out. -/
def writtenTypeSpan (segs : Array Ident) : M Span := do
  let src := (← get).src
  let sp := typeSpan segs
  let mut depth : Int := 0
  for c in src.extract sp.start sp.stop do
    if c == '<' then depth := depth + 1 else if c == '>' then depth := depth - 1
  let mut stop := sp.stop
  while depth > 0 && stop < src.size do
    if src[stop]! == '>' then depth := depth - 1
    stop := stop + 1
  return { sp with stop }

/-- The type that the path `segs` names, written at `span`, with the
declared type arguments `args`, as many as its type parameters
(`lang::type_arguments`); a type alias's type as declared. -/
def instanceTy (segs : Array Ident) (args : Array Fren.Core.PTy) (span : Span) : M Fren.Core.PTy := do
  let builtin := segs.size == 1 && #["Bool", "Int", "Nat", "String", "Set", "Seq", "Rel"].contains segs[0]!.name
  let fnParam := segs.size == 1 && ((← get).fnTypeParams.any (·.2.contains (Name.mkSimple segs[0]!.name)))
  if builtin || fnParam || (segs.size == 1 && (← get).typeParams.contains (Name.mkSimple segs[0]!.name)) then
    unless Fren.Core.writtenArgumentsAccepted (if builtin then .builtin else .parameter) 0 args.size do
      err span (Fren.Core.typeArgsMsg segs[0]!.name #[] args.size)
  let arity (named : Fren.Core.TypeNamed) (path : Name) (params : Array Name) : M Unit := do
    unless Fren.Core.writtenArgumentsAccepted named params.size args.size do
      err span (Fren.Core.typeArgsMsg (showPath path) params args.size)
  let tys := args.toList.map (·.ty)
  match ← resolveWritten segs with
  | .item { kind := .enumItem, path, .. } =>
    arity .data path ((((← get).dataOf? path).map (·.params)).getD #[])
    return { ty := .enum path tys, elems := args }
  | .item { kind := .recordItem, path, .. } =>
    if let some u := (← get).newtypes.find? path then
      arity .other path #[]
      return .plain (.newtype path u)
    arity .data path ((((← get).dataOf? path).map (·.params)).getD #[])
    return { ty := .record path tys, elems := args }
  | .item { kind := .typeItem, path, .. } =>
    arity .other path #[]
    if let some t := (← get).aliases.find? path then return t
    return .plain (.abstract path)
  | r => err span (Fren.Core.notATypeMsg r)

/-- A function type written `segs` at `site`, where it may not be
(`lang::function_type_place`); a function type within another is reported
where that one is elaborated. -/
def checkFnTypeSite (site : Fren.Core.TypeSite) (segs : Array Ident) : M Unit := do
  if segs[0]?.any (·.name == Parser.fnSeg) then err (typeSpan segs) (Fren.Core.fnTypePlaceMsg site [])

mutual
/-- The declared type written `segs`, with the invariants of the subset
types within it (`Reqs/Lang/Types#subset-types`). -/
partial def elabPTy (segs : Array Ident) : M Fren.Core.PTy := do
  -- A function type is only a defined function's parameter's, which
  -- `elabFnTy` elaborates (`lang::function_type_place`).
  if let some w := Fren.Core.fnTypeWithin (segs.toList.map (·.name)) then
    err (typeSpan segs) (Fren.Core.fnTypePlaceMsg .constant w)
  let t ← elabBasePTy segs
  let text := Fren.Core.typeText (← srcAt (← writtenTypeSpan segs))
  return { t with text }

/-- The declared type `segs`, which has no pattern of its own: a type
parameter, within the declaration of a generic type, or an instance of one,
`G<A, B>` (`Reqs/Lang/Generics#type-arguments`), whose type arguments are
declared types, with their patterns. -/
partial def elabBasePTy (segs : Array Ident) : M Fren.Core.PTy := do
  let span := segs[0]!.span.to segs.back!.span
  if let some i := segs.findIdx? (·.name == Parser.argsOpen) then
    if i > 0 && segs[0]!.name != Parser.setSeg && segs[0]!.name != Parser.seqSeg && segs[0]!.name != Parser.relSeg then
      let argSegs := Parser.splitArgs (segs.extract (i + 1) (segs.size - 1))
      let mut args := #[]
      for a in argSegs do
        let t ← elabPTy a
        let aspan := a[0]!.span.to a.back!.span
        -- An argument is never `Nat` (`lang::nat_place`), and is a payload's
        -- type (`Reqs/Lang/Generics#type-parameters`).
        unless t.ty != .nat || Fren.Core.natPlaceAccepted .argument do err aspan (Fren.Core.natPlaceMsg .argument)
        if let some p := t.ty.abstractWithin? then err aspan (Fren.Core.abstractFieldMsg p true (!(t.ty matches .abstract _)))
        args := args.push t
      let t ← instanceTy (segs.extract 0 i) args span
      -- A recursive enumeration's type arguments bring no constraints
      -- (`Reqs/Lang/Generics#subset-types-as-type-arguments`).
      if let .enum p _ := t.ty then
        if ((← get).shapeOf p).any (·.recursive) then
          for a in args, aSegs in argSegs do
            if (← consOf a).isSome then
              err (← writtenTypeSpan aSegs) (Fren.Core.recursiveArgumentMsg a.text (showPath p))
      -- Nor do they within an instance, once its arguments stand for its
      -- parameters.
      if let some p := t.ty.dataPath? then
        if let some (a, q) := Fren.Core.recursiveArgumentWithin? (← get).shapeOf p args then
          err (← writtenTypeSpan segs) (Fren.Core.recursiveArgumentMsg a.text (showPath q))
      return t
  if let some k := (← get).typeParams.idxOf? (Name.mkSimple segs[0]!.name) then
    if segs.size == 1 then return .plain (.param k (Name.mkSimple segs[0]!.name))
  -- A generic function's type parameter, an abstract type within it
  -- (`Reqs/Lang/GenericFunctions#type-parameters`).
  if let some (fn, ps) := (← get).fnTypeParams then
    if let some k := ps.idxOf? (Name.mkSimple segs[0]!.name) then
      if segs.size == 1 then return .plain (.abstract (Fren.Core.typeParamPath fn k ps[k]!))
  if segs.size == 1 && segs[0]!.name == "Bool" then return .plain .bool
  if segs.size == 1 && segs[0]!.name == "Int" then return .plain .int
  if segs.size == 1 && segs[0]!.name == "Nat" then return .plain .nat
  if segs.size == 1 && segs[0]!.name == "String" then
    modify fun s => { s with usesStrings := true }
    return .plain .string
  -- An element type, which is never a `Nat` (`lang::nat_place`), nor a type
  -- parameter (`lang::type_parameter_place`), and whose constraint, if any,
  -- quantifies over the elements, outside the decidable core
  -- (`lang::subset_place`).
  let elem (segs : Array Ident) : M Fren.Core.PTy := do
    let t ← elabPTy segs
    if t.ty == .nat then err (typeSpan segs) (Fren.Core.natPlaceMsg .element)
    if let .param _ p := t.ty then err (typeSpan segs) (Fren.Core.typeParamPlaceMsg p .element "")
    if let .abstract p := t.ty then
      if let some n := Fren.Core.typeParamName? p then
        err (typeSpan segs) (Fren.Core.typeParamPlaceMsg (Name.mkSimple n) .element "")
    if (← consOf t).isSome then
      modify fun s => { s with outsideCore := true }
      lint .undecidable (typeSpan segs) Fren.Core.undecidableElementsMsg
    return t
  if segs[0]!.name == Parser.setSeg then
    modify fun s => { s with usesSets := true }
    let e ← elem (segs.extract 1)
    return { ty := .set e.ty, elems := #[e] }
  if segs[0]!.name == Parser.seqSeg then
    modify fun s => { s with usesSeqs := true }
    let e ← elem (segs.extract 1)
    return { ty := .seq e.ty, elems := #[e] }
  if segs[0]!.name == Parser.relSeg then
    modify fun s => { s with usesSets := true }
    let (a, b) := Parser.splitRel (segs.extract 1)
    let (pa, pb) := (← elem a, ← elem b)
    let (ta, tb) := (pa.ty, pb.ty)
    -- `zero_sized_map_values` (`lint::zero_sized_map_values`).
    if let .enum p _ := tb then
      if let some d := (← get).dataOf? p then
        if Fren.Core.zeroSizedMapValues true d.ctors.size (d.ctors.any (!·.2.isEmpty)) then
          let s ← get
          let text (xs : Array Ident) (stop : Nat) :=
            (String.ofList (s.src.extract (typeSpan xs).start stop).toList).trimAscii.toString
          let sep := segs[a.size + 1]!.span
          -- To the `>` after `B`.
          let mut stop := (typeSpan b).stop
          while stop < s.src.size && s.src[stop]! != '>' do stop := stop + 1
          lint .zeroSizedMapValues { start := segs[0]!.span.start, stop := stop + 1 }
            (Fren.Core.zeroSizedMapValuesMsg (text a sep.start) (text b (typeSpan b).stop) d.ctors[0]!.1.toString)
    return { ty := .rel ta tb, elems := #[pa, pb] }
  instanceTy segs #[] (segs[0]!.span.to segs.back!.span)
end

/-- The type written `segs`, without its patterns: the type that
expressions of it have. -/
def elabTy (segs : Array Ident) : M Ty := return (← elabPTy segs).ty

/-- The type of a quantifier's binder, written `segs`, which must not be a
procedure. -/
def binderTy (segs : Array Ident) : M Fren.Core.PTy := do
  let st ← get
  if let .ok (.item { kind := .compItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) #[] then
    err (segs[0]!.span.to segs.back!.span) (Fren.Core.quantifiedComponentMsg (showPath path))
  elabPTy segs

/-- The value `v` of the type `t` in SMT-LIB (`Fren.Core.PVal`). -/
partial def State.valueSmt (s : State) (t : Ty) (v : Fren.Core.PVal) : String :=
  match t, v with
  | _, .bool b => toString b
  | _, .int i => smtInt i
  -- Erased, as a newtype's values are.
  | .newtype _ u, .ctor _ #[w] => s.valueSmt u w
  | .enum p targs, .ctor idx args | .record p targs, .ctor idx args => Id.run do
    let some d := s.dataOf? p | return "?"
    -- With an instance's arguments for its type parameters.
    let (c, fs) := (d.instCtors targs)[idx]!
    return d.build targs c ((args.zip fs).toList.map fun (w, (_, ft)) => s.valueSmt ft w)
  | _, _ => "?"

/-- The values of the declared type `t` in SMT-LIB, and how many there are,
if a quantifier ranges over it (`lang::quantified_type`): a type whose
values bring no constraint as `State.values` lists them, and one that does,
those that meet it (`Fren.Core.PTy.values`). -/
def binderValues (t : Fren.Core.PTy) : M (Option (Nat × Array String)) := do
  let st ← get
  -- Only a listed type's values are listed (`lang::quantified_type`).
  unless (st.typeFacts t).listed do return none
  if (t.cons st.shapeOf).isNone then
    let some n := st.valueCount t.ty | return none
    return some (n, (st.values Fren.Core.maxInstances t.ty).getD #[])
  let some n := t.count? st.shapeOf | return none
  if n > Fren.Core.maxInstances then return some (n, #[])
  let vs := (t.values st.shapeOf Fren.Core.maxInstances).getD #[]
  return some (n, vs.map (st.valueSmt t.ty))

/-- A bound name of an unbounded quantifier, as the solver's quantifier
declares it: its symbol, its sort, and what its type brings of it, if
anything, as a formula (`Reqs/Cli#solver-queries`). -/
structure FreeBound where
  sym : String
  sort : String
  cons? : Option String

/-- The bound names of a quantifier's binders `bs`, declared in `cx`, every
combination of the values of those of listed types, as SMT-LIB terms, the
last name varying fastest (`Reqs/Lang/Quantifiers#meaning`), and those of
the other types, which the solver's quantifier binds
(`Reqs/Lang/Quantifiers#unbounded-quantifiers`). The names must be
distinct, follow the Boolean names rule and be written with `!` exactly
when they shadow (`lang::shadowing`), and the combinations be at most
`Fren.Core.maxInstances` (`lang::quantifier_size`). A bound name of a
listed type has a symbol that no variable has, which each instance
replaces; one of another type, the symbol `x'k`, with `k` its position
among the binders in scope, which the solver's quantifier binds, and which
`undecidable` reports at its binder (`lang::in_core`), unless `defer`,
for its caller to report at the spans returned last, once it knows whether
the quantifier is one over elements in the core
(`lang::element_quantifier`). -/
def quantBinders (cx : ExprCtx) (bs : Array Binder) (defer : Bool := false) :
    M (Array CBinder × Array (Array String) × Array FreeBound × Array Span) := do
  -- Distinct names (`lang::distinct_names`), by the names they declare.
  let ids := bs.flatMap (·.names)
  let declared := ids.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then err ids[k]!.span (Fren.Core.dupBoundMsg declared[k]!)
  let mut out : Array CBinder := #[]
  let mut sizes := #[]
  let mut listed := #[]
  let mut free := #[]
  let mut unlisted := #[]
  for b in bs do
    let pt ← binderTy b.ty
    let t := pt.ty
    let values? ← binderValues pt
    if values?.isNone then
      unlisted := unlisted.push b.span
      unless defer do
        modify fun s => { s with quantified := true }
        checkCore cx b.span .quantifier true true #[]
    for x in b.names do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        ((cx.binders ++ out).map (·.what)) cx.selfFn.isSome
      let y ← declare x locals
      let bn := Name.mkSimple y.name
      liftMsg y.span (Fren.Core.checkVarName bn (some (t == .bool)))
      lintName .binder bn y.span
      let k := cx.binders.size + out.size
      match values? with
      | some (n, vs) =>
        out := out.push { name := bn, smt := quote s!"{k} {bn}", ty := t, scrutinee := none, outer := k }
        sizes := sizes.push n
        listed := listed.push vs
      | none =>
        let sym := quote s!"{y.name}'{k}"
        let st ← get
        free := free.push { sym, sort := t.sort, cons? := (pt.cons st.shapeOf true).map (consSmt st.dataOf? · sym) }
        out := out.push { name := bn, smt := sym, ty := t, scrutinee := none, outer := k, unbounded := true }
  let n := cx.instances * Fren.Core.instanceCount sizes
  unless Fren.Core.quantifierSizeAccepted n do
    err (bs[0]!.span.to bs.back!.span) (Fren.Core.quantifierSizeMsg n (cx.instances > 1))
  return (out, listed.foldl (fun acc vs => acc.flatMap fun pre => vs.map pre.push) #[#[]], free, unlisted)

/-- An operand of `=` or `!=`, as `lang::function_comparison` sees it: a
closure, the name of a function or of a function parameter, or a value. -/
def comparand (cx : ExprCtx) (e : Expr) : M Fren.Core.Comparand := do
  match e with
  | .closure .. | .matches _ #[] _ _ => return .closure
  | .path _ #[s] =>
    let n := identName s.name
    if (cx.fnParam? n).isSome then return .functionName
    if (cx.binder? n.getRoot).isSome || cx.vars.any (·.name.isPrefixOf n) then return .value
    let st ← get
    match st.table.resolvePath st.scope #[n] cx.shadowing with
    | .ok (.item { kind := .fnItem, .. }) => return .functionName
    | _ => return .value
  | .path _ segs =>
    let st ← get
    match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
    | .ok (.item { kind := .fnItem, .. }) => return .functionName
    | _ => return .value
  | _ => return .value

/-- `body` under the solver's quantifier over `free`, a `forall` if `all`,
or `body` if there are none: what their types bring is a hypothesis of a
`forall`'s body, and a conjunct of an `exists`'s. A quantifier over
elements in the core (`elem`) is written with the head `fren.forall` or
`fren.exists`, which each query expands (`FrenCli.SeqElems`). -/
def bindFree (free : Array FreeBound) (all : Bool) (body : String) (elem : Bool := false) : String :=
  if free.isEmpty then body else
  let decls := " ".intercalate (free.toList.map fun u => s!"({u.sym} {u.sort})")
  let cons := free.filterMap (·.cons?)
  let body := if cons.isEmpty then body else if all then s!"(=> {conj cons} {body})" else s!"(and {conj cons} {body})"
  s!"({if elem then "fren." else ""}{if all then "forall" else "exists"} ({decls}) {body})"

/-- An operand of arithmetic, `e` of type `t`, is an `Int` or a `Nat`. -/
def exprNumber (e : Expr) (t : Ty) (op : String) : M Unit := liftMsg e.span (Fren.Core.checkNumber op t)

/-- The operator `op` at `span`, prefix if `pre`, of operands of the types
`tx` and `ty`: if one is a newtype, it must have `op`, and both must be
of it (`lang::newtype_operator`). -/
def exprNewtypeOp (op : String) (span : Span) (tx ty : Ty) (pre := false) : M Unit := do
  liftMsg span (Fren.Core.checkNewtypeOperator op pre tx ty (← orderedDecl))

/-- Reports the lints of the `let` or `where` clause at `span`, of the
definitions `defs` and the body `body`: its names that neither the body nor
a later definition mentions (`unused_variables`), `let_and_return` and
`redundant_locals` (`lint::let_and_return`, `lint::redundant_locals`). -/
def lintClause (span : Span) (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) (isWhere : Bool) :
    M Unit := do
  let names := defs.map fun (x, _, _) => Name.mkSimple (declaredIdent x).1.name
  let used := (Fren.Core.clauseMentions names (defs.map fun (_, _, d) => mentions d) (mentions body) true).2
  for (x, _, _) in defs, n in names, u in used do
    unless u do lint .unusedVariables (declaredIdent x).1.span (Fren.Core.unusedDefinitionMsg n)
  let src := (← get).src
  let clause := toRange span
  let commented := Fren.Core.hasComment (Fren.Core.textOf src clause)
  -- Each definition from its name to the end of its expression, and the
  -- body, with their parentheses.
  let written (e : Expr) := Fren.Core.withParensIn src clause (toRange e.span)
  let ranges : Array Fren.Core.Range := defs.map fun (x, _, d) => { start := x.span.start, stop := (written d).stop }
  if let some (x, ty?, d) := defs.back? then
    let bodyIsLast := match body with | .path _ #[y] => y.name == (declaredIdent x).1.name | _ => false
    if Fren.Core.letAndReturn bodyIsLast ty?.isSome then
      let earlier? := if defs.size < 2 then none
        else some (Fren.Core.textOf src { start := ranges[0]!.start, stop := ranges[defs.size - 2]!.stop })
      let fixed := Fren.Core.letAndReturnFixed isWhere earlier? (Fren.Core.textOf src (written d))
      lintFix .letAndReturn body.span (Fren.Core.letAndReturnMsg names.back! isWhere clause fixed commented)
  for (x, ty?, d) in defs, n in names do
    let (y, bang) := declaredIdent x
    let own := match d with | .path _ #[z] => z.name == y.name | _ => false
    if Fren.Core.redundantLocal bang ty?.isSome own then lint .redundantLocals x.span (Fren.Core.redundantLocalMsg n)

/-- Reports the lints of the quantifier at `span`, a `forall` if `all`,
whose binders `bs` declare `new` and whose body is `body`: its bound names
that the body does not mention (`unused_variables`), and
`trivial_quantifier` (`lint::trivial_quantifier`), whose fix writes the
value of each bound name in place of its mentions recorded since `mark`. -/
def lintQuant (span : Span) (all : Bool) (bs : Array Binder) (new : Array CBinder) (body : Expr) (mark : Nat) :
    M Unit := do
  let mentioned := (mentions body).map (·.getRoot)
  for x in bs.flatMap (·.names), b in new do
    unless mentioned.contains b.name do lint .unusedVariables (declaredIdent x).1.span (Fren.Core.unusedBoundMsg b.name all)
  let st ← get
  let counts := new.map fun b => (st.valueCount b.ty).getD 0
  unless Fren.Core.trivialQuantifier (counts.filter (· == 1)).size do return
  -- The binder of each bound name.
  let binders := bs.flatMap fun b => b.names.map fun _ => b
  let some i := counts.idxOf? 1 | return
  let tyText (k : Nat) : M String := srcAt (binders[k]!.ty[0]!.span.to binders[k]!.ty.back!.span)
  -- The value of a type of one value, if it is a variant without a payload.
  let values ← (List.range new.size).toArray.mapM fun k => do
    let some b := new[k]? | return none
    let Ty.enum p .. := b.ty | return none
    let some { ctors := #[(v, #[])], .. } := st.dataOf? p | return none
    return some s!"{← tyText k}::{v}"
  let quant := toRange span
  -- A global expectation's binders over values have no `forall` of their own.
  let own := bs[0]?.any (·.span.start != span.start)
  let fixed? : Option String := do
    -- A name the body declares again would hide nothing once the quantifier is gone.
    let redeclared := new.any fun b => body.declaredNames.contains (Fren.Core.nameText b.name)
    guard (Fren.Core.trivialQuantifierFixed (counts.filter (· == 1)).size counts.size (values.all Option.isSome) (!own)
      redeclared)
    guard (!Fren.Core.hasComment (Fren.Core.textOf st.src quant))
    let vs ← values.mapM id
    let ms := (st.boundMentions.extract mark).filterMap fun (sp, sym) =>
      (new.findIdx? (·.smt == sym)).map fun k => (toRange sp, vs[k]!)
    pure (Fren.Core.substituted st.src (Fren.Core.withParensIn st.src quant (toRange body.span)) ms)
  let some b := new[i]? | return
  lintFix .trivialQuantifier binders[i]!.span
    (Fren.Core.trivialQuantifierMsg all b.name (← tyText i) values[i]! quant fixed?)


/-- Runs `x`, and returns with its result the names that the pattern tests
that it elaborates bind (`State.bound`), which it removes: those of the
condition of a `when` or `if` (`lang::test_scope`). -/
def withBound (x : M α) : M (α × Array CBinder) := do
  let mark := (← get).bound.size
  let r ← x
  let new := (← get).bound.extract mark
  modify fun s => { s with bound := s.bound.extract 0 mark }
  return (r, new)

/-- `redundant_type_annotations` and `redundant_closure` on the closure at `span`, of the parameters `params` and the body `body`,
given for a function parameter whose parameters' types are `ps` where they
are known before the closure, and whose result's is `r?`
(`lint::redundant_type_annotations`, `lint::redundant_closure`). -/
def lintClosure (cx : ExprCtx) (ps : Array (Option Ty)) (r? : Option Ty) (span : Span)
    (params : Array (Ident × Option (Array Ident))) (body : Expr) : M Unit := do
  let names := params.map fun (x, _) => (declaredIdent x).1.name
  -- `redundant_type_annotations` (`lint::redundant_type_annotations`).
  for (x, ty?) in params, p? in ps do
    let some segs := ty? | continue
    unless Fren.Core.redundantTypeAnnotation true p?.isSome do continue
    let tr := typeSpan segs
    let msg := Fren.Core.redundantTypeAnnotationMsg (if x.name.startsWith "#_" then "_" else (declaredIdent x).1.name) (← srcAt tr)
    lintFix .redundantTypeAnnotations tr { msg with fixes := msg.fixes.map ({ · with range? := some { start := x.span.stop, stop := tr.stop } }) }
  -- `unused_variables` on its parameters (`lint::unused_closure_params`).
  let mentioned := (mentions body).map (·.getRoot)
  for (x, _) in params, n in names do
    unless Fren.Core.closureParamOptedOut n || mentioned.contains (Name.mkSimple n) do
      lint .unusedVariables (declaredIdent x).1.span (Fren.Core.unusedClosureParamMsg (Name.mkSimple n))
  -- `redundant_closure` (`lint::redundant_closure`).
  let .app _ segs args := body | return
  let args := args.toList.map fun | .path _ #[y] => names.idxOf? y.name | _ => none
  let st ← get
  let some rt := r? | return
  let some pts := ps.mapM id | return
  let (callee, exact) : Fren.Core.Callee × Bool :=
    if segs.size == 1 && names.contains segs[0]!.name then (.other, false)
    else if let some (ft, _) := (if segs.size == 1 then cx.fnParam? (identName segs[0]!.name) else none) then
      (.fnParameter, ft.params == pts && ft.result == rt)
    else match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
      | .ok (.item { kind := .fnItem, path, .. }) =>
        match (if st.hofs.contains path then none else st.defs.find? (·.1 == path)), st.funPTys.find? path with
        | some (_, dps, dr, _), some (pps, rp) =>
          (.defined, dps.map (·.2) == pts && dr == rt && (pps.push rp).all (!·.restricted))
        | _, _ => (.other, false)
      | _ => (.other, false)
  unless Fren.Core.redundantClosure names.size args true callee exact do return
  lintFix .redundantClosure span (Fren.Core.redundantClosureMsg (← srcAt (segs[0]!.span.to segs.back!.span)))

/-- Records what the application of the higher-order function `path` gives
its parameter at `k`, the closure or function's name `e`, for
`needless_higher_order` (`lint::needless_higher_order`): its text, and the
names that a closure's body has free (`closureFreeNames`), of which a
function's name is one, or that it is a lambda match. -/
def noteFnArg (path : Name) (k : Nat) (e : Expr) : M Unit := do
  if (← get).fnArgs.any fun (a, sp) => sp == e.span && a.index == k then return
  let src := (← get).src
  let (lambdaMatch, names) : Bool × Array String := match e with
    | .closure _ params body => (false, closureFreeNames (params.map fun (x, _) => (declaredIdent x).1.name) body)
    | .path _ segs => (false, #[(segs.map (·.name)).foldl (· ++ "::" ++ ·) ""])
    -- `elabFnArg` accepts nothing else but a lambda match.
    | _ => (true, #[])
  let text := (e.text src).text
  modify fun s => { s with fnArgs := s.fnArgs.push ({ path, index := k, text, lambdaMatch, names }, e.span) }

mutual
/-- Two parts of the same type at `site`, each checked against the other's,
when it does not synthesize its own (`lang::checked`). -/
partial def exprPair (site : Fren.Core.ExprSite) (cxa cxb : ExprCtx) (a b : Expr) : M ((String × Ty) × (String × Ty)) := do
  let sibling (cx' : ExprCtx) (t : Ty) := site.expected cx'.expected? (some t.widen)
  let (cxa, cxb) := ({ cxa with expected? := site.expected cxa.expected? none }, { cxb with expected? := site.expected cxb.expected? none })
  if !(← synthesizes cxa a) && (← synthesizes cxb b) then
    let rb ← elabExpr cxb b
    return (← elabExpr { cxa with expected? := sibling cxa rb.2 } a, rb)
  let ra ← elabExpr cxa a
  return (ra, ← elabExpr { cxb with expected? := sibling cxb ra.2 } b)

/-- `e`, elaborated in `cx`, which must be of the type `t`; `why` notes why. -/
partial def exprExpect (cx : ExprCtx) (e : Expr) (t : Ty) (why : Option String := none) : M String := do
  let (s, t') ← elabExpr cx e
  liftMsg e.span (Fren.Core.checkType t t' why)
  return s

/-- `length_zero`, `card_zero` and `absurd_extreme_comparisons` on `a op b`
(`lint::length_zero`, `lint::absurd_extreme_comparisons`). -/
partial def exprLintLength (cx : ExprCtx) (e : Expr) (op : String) (a b : Expr) : M Unit := do
  unless cx.noteIndexes do return
  let some c := Fren.Core.Comparison.ofOp? op | return
  let lit? : Expr → Option Int
    | .num _ d => some d
    | .neg _ (.num _ d) => some (-(d : Int))
    | _ => none
  -- The length, the literal, and whether the length is on the left.
  let (n, d, left) ← match lit? b, lit? a with
    | some d, _ => pure (a, d, true)
    | none, some d => pure (b, d, false)
    | none, none => return
  let some (recv, card) := lengthOf? n | return
  -- `const_is_empty` (`lint::const_is_empty`), rather than `length_zero`
  -- and `card_zero` on a literal, or `absurd_extreme_comparisons` where
  -- it fires.
  let literal := recv.literalCount?.isSome
  if let some (set, count) := recv.literalCount? then
    let (fires, value) := Fren.Core.constIsEmpty c d left set count
    -- `[]` and `{}` have no type here, which is an error.
    let untyped := count == 0 && !(recv matches .str ..)
    if fires && card == set && !untyped then
      lint .constIsEmpty e.span (Fren.Core.constIsEmptyMsg value)
      return
  let fires := !literal && (Fren.Core.lengthZero c d left).1
  let empty := (Fren.Core.lengthZero c d left).2
  let (absurd, value) := Fren.Core.absurdComparison c d left
  unless fires || absurd do return
  -- Only its type: what elaborating it reports is reported where it is.
  let saved ← get
  let t? ← tryCatch (some <$> (·.2) <$> elabExpr { cx with noteIndexes := false, concatOk := true } recv)
    fun _ => pure none
  set saved
  let some t := t? | return
  let isSet := t matches .set _ | .rel ..
  unless card == isSet do return
  if absurd then
    if card || t matches .string | .seq _ then lint .absurdExtremeComparisons e.span (Fren.Core.absurdComparisonMsg card value)
    return
  let emptyText := match t with | .string => "\"\"" | .seq _ => "[]" | _ => "{}"
  lintFix (if card then .cardZero else .lengthZero) e.span
    (Fren.Core.lengthZeroMsg card { text := ← srcAt (recv.writtenSpan (← get).src), prec := recv.boolNode.kind.prec }
      emptyText empty d)

/-- `redundant_method_chain`, at the end of a chain (`lint::method_chain`):
not on the receiver of a field or method read without arguments. -/
partial def exprLintChain (cx : ExprCtx) (e : Expr) (parent? : Option Expr) (src : Array Char) (slot : Option Fren.Core.Slot) : M Unit := do
  let inChain := parent?.any fun
    | .field _ r _ | .method _ r _ #[] => r.span == e.span
    | _ => false
  unless cx.noteIndexes && !inChain do return
  let steps := namesRead e
  let ms := steps.map (Fren.Core.Method.ofName? ·.2)
  let shortens (i : Nat) := match ms[i]?, ms[i + 1]? with
    | some (some a), some (some b) => Fren.Core.methodChain a b != .keep
    | _, _ => false
  unless (List.range steps.size).any shortens do return
  -- The first receiver that is a relation or a sequence, which has no
  -- fields: the names after it are its methods.
  for (recv, _) in steps, i in [0:steps.size] do
    let saved ← get
    let rcx := { cx with noteIndexes := false, concatOk := true }
    let t? : Option Ty ← tryCatch (some <$> (·.2) <$> elabExpr rcx recv) fun _ => pure none
    set saved
    unless t? matches some (.rel ..) | some (.seq _) do continue
    let some chain := (ms.extract i).mapM id | return
    let short := Fren.Core.shortestChain chain.toList
    if short.length < chain.size then
      let written := Fren.Core.textOf src (Fren.Core.withParens src (toRange (recv.writtenSpan src)))
      let fixed : Fren.Core.BText :=
        if short.isEmpty then { text := Fren.Core.textOf src (toRange recv.span), prec := recv.boolNode.kind.prec }
        else { text := written ++ String.join (short.map (s!".{·.name}")), prec := Fren.Core.BKind.atom.prec }
      lintFix .redundantMethodChain (e.writtenSpan src) (Fren.Core.methodChainMsg (fixed.inSlot slot (← followedSpan e.span)))
    return

partial def elabExpr (cx : ExprCtx) (e : Expr) : M (String × Ty) := do
  let original := cx
  let concatOk := cx.concatOk
  let expected? := cx.expected?
  let chain := cx.chain
  let parent? := cx.parent?
  let inElse := cx.inElse
  -- Only `and` and `is` read where their chain is (`lang::test_scope`).
  let test := (cx.testContext, cx.testAt?)
  let cx := { cx with concatOk := false, expected? := none, chain := "", parent? := some e, inElse := false
                      testContext := .standalone, testAt? := none }
  let opNote := Fren.Core.opNote
  match e with
  | .block sp op members => do
    let mut seen : Array String := #[]
    for (label, _) in members do
      if let some label := label then
        if seen.contains label.name then
          err label.span { code? := some "F0372", headline := s!"duplicate Boolean member label `{label.name}`", label? := some "already used in this block" }
        seen := seen.push label.name
    if op == "iff" && members.size <= 1 then
      for (_, member) in members do
        let (_, ty) ← elabExpr { original with noteIndexes := false, expected? := some .bool } member
        liftMsg member.span (Fren.Core.checkType .bool ty (some "note: a Boolean block member is a `Bool`"))
    let before ← get
    let result ← elabExpr original (Expr.lowerBlock sp op members)
    -- A source operation may occur in several branches of the generated
    -- decision tree. Conjoin its guarded obligations into one source site.
    let after ← get
    let mut indexes := #[]
    for (source, goal, kind) in after.indexes.extract before.indexes.size after.indexes.size do
      if let some k := indexes.findIdx? fun (old, previous, oldKind) => old == source && oldKind == kind && siteOperation previous == siteOperation goal then
        let (old, previous, oldKind) := indexes[k]!
        indexes := indexes.set! k (old, conj #[previous, goal], oldKind)
      else indexes := indexes.push (source, goal, kind)
    let mut tables := #[]
    for (source, kind, goal) in after.tables.extract before.tables.size after.tables.size do
      if let some k := tables.findIdx? fun (old, oldKind, previous) => old == source && oldKind == kind && siteOperation previous == siteOperation goal then
        let (old, oldKind, previous) := tables[k]!
        tables := tables.set! k (old, oldKind, conj #[previous, goal])
      else tables := tables.push (source, kind, goal)
    modify fun s => { s with
      indexes := before.indexes ++ indexes
      tables := before.tables ++ tables
      lintReports := before.lintReports ++ (s.lintReports.extract before.lintReports.size s.lintReports.size).filter (fun r => r.ref != sp)
      lintFixes := before.lintFixes ++ (s.lintFixes.extract before.lintFixes.size s.lintFixes.size).filter (fun r => r.span != sp) }
    return result
  | .when span neg c d => elabWhenExpr cx e span neg c d
  | .quant span all bs body => elabQuantExpr cx span all bs body
  | .not _ a => return (s!"(not {← exprExpect { cx with testContext := .notOperand } a .bool (opNote "not" .bool)})", .bool)
  | .ite span c a b => elabIteExpr cx e expected? inElse span c a b
  | .neg span a => elabNegExpr cx span a
  | .num _ v => return (toString v, Fren.Core.literalTy (expected? == some .nat))
  | .set span elems => elabSetExpr cx expected? span elems
  | .pair span .. => err span Fren.Core.pairPlaceMsg
  | .seq span elems => elabSeqExpr cx expected? span elems
  | .index span q i => elabIndexExpr cx span q i
  | .str span v => elabStrExpr span v
  | .method span recv m args => elabMethodExpr cx e expected? parent? span recv m args
  | .bool _ b => return (toString b, .bool)
  | .chain _ es ops => elabChainExpr cx es ops
  | .bin span op a b => elabBinExpr cx e concatOk expected? chain test span op a b
  | .path _ segs => elabPathExpr cx e expected? parent? segs
  | .app span segs args => elabAppExpr cx expected? span segs args
  | .field span a f => elabFieldExpr cx e parent? span a f
  | .record span tySegs fields => elabRecordExpr cx expected? span tySegs fields
  | .update span base fields => elabUpdateExpr cx span base fields
  | .match span scrutinee arms isTable => elabMatchExpr cx e expected? parent? span scrutinee arms isTable
  | .matches span scrutinees arms isTable =>
    if scrutinees.isEmpty then err span Fren.Core.closurePlaceMsg
    elabMatchExpr cx e expected? parent? span scrutinees[0]! (arms.map fun (ps, g, b) => (ps[0]!, g, b)) isTable
      (some (scrutinees, arms.map (·.1)))
  | .table span rows => elabTableExpr cx e expected? parent? span rows
  | .is span scrutinee p => elabIsExpr cx test span scrutinee p
  | .«let» span defs body isWhere => elabLetExpr cx span concatOk expected? defs body isWhere
  -- Only an argument for a function parameter (`lang::function_argument`).
  | .closure span .. => err span Fren.Core.closurePlaceMsg

/-- `elabExpr` on a `when` or `unless`. -/
partial def elabWhenExpr (cx : ExprCtx) (e : Expr) (span : Span) (neg : Bool) (c : Expr) (d : Expr) : M (String × Ty) := do
  -- `eq_op` (`lint::eq_op_conditional`).
  if cx.noteIndexes then
    let tc ← srcAt c.span
    -- The body of `when` sees the names that the condition's pattern tests
    -- bind (`lang::test_scope`).
    let seen ← if neg then pure [] else chainBinders cx c
    if let some v := Fren.Core.eqOpConditional neg (Fren.Core.writtenSameIn tc (← srcAt d.span) [] seen) then
      lint .eqOp span (Fren.Core.eqOpConditionalMsg neg v tc)
  let kw := if neg then "unless" else "when"
  -- The names that the condition's pattern tests bind, which the body of
  -- `when` sees (`lang::test_scope`).
  let context : Fren.Core.TestContext := if neg then .unlessCondition else .whenCondition
  let (c, new) ← withBound do
    exprExpect { cx with testContext := context } c .bool (some s!"note: the condition of `{kw}` is a `Bool`")
  let g := (if neg then Fren.Core.GuardedOperand.unlessBody else .whenBody).guard c s!"(not {c})"
  let seen := if Fren.Core.binderVisible context 0 1 .body then new else #[]
  let (d, td) ← elabExpr { cx with guards := cx.guards.push g, binders := cx.binders ++ seen } d
  unless td == .bool do mismatch e .bool td (some s!"note: the body of `{kw}` is a `Bool`")
  return (if neg then s!"(=> (not {c}) {d})" else s!"(=> {c} {d})", .bool)

/-- `elabExpr` on a quantifier. -/
partial def elabQuantExpr (cx : ExprCtx) (span : Span) (all : Bool) (bs : Array Binder) (body : Expr) : M (String × Ty) := do
  -- Expanded over the bound names of listed types: the body, elaborated
  -- once, at each combination of their values
  -- (`Reqs/Lang/Quantifiers#meaning`), and so are the definedness goals
  -- of its indexes, and the questions about its tables, which hold in
  -- every instance. The other bound names are the solver's quantifier's,
  -- around the expansion, and around those goals as a `forall`, whatever
  -- the quantifier (`Reqs/Lang/Quantifiers#unbounded-quantifiers`).
  let (new, combos, free, unlisted) ← quantBinders cx bs (defer := true)
  let names := new.map (·.name.getString!)
  -- A quantifier over a sequence's elements (`lang::element_quantifier`):
  -- each bound name of a type that is not listed has the members of `x in
  -- e` as its domain, by the first conjunct of the guard that names it.
  let parts := Fren.Core.guardPartsBy guardNode whenOf? all body
  let members : Array (Option Expr) := new.zipIdx.filterMap fun (c, k) =>
    if !c.unbounded then none else some <|
      match domainOf all names body k (c.ty == Ty.nat) with
      | (.members j, bounds) =>
        if (parts.extract 0 j).any (·.any (·.names names[k]!)) then none else bounds[j]?.bind (·.map (·.1))
      | _ => none
  let candidate := !members.isEmpty && members.all Option.isSome
  let nesting : Fren.Core.ElementNesting := match cx.elemKind? with
    | none => .top
    | some k => if k == all && cx.elemDirect.contains span then .direct else .other
  let bodyCx := if candidate then
      { cx with elemGuards := cx.elemGuards ++ members.filterMap (·.map (·.span)), elemKind? := some all
                elemDirect := cx.elemDirect ++ (elementSpine all body).toArray
                elemChain := (if nesting == .direct then cx.elemChain else #[]) ++ (new.filter (·.unbounded)).map (·.name) }
    else cx
  let outer ← takeIndexes
  let outerTables ← takeTables
  let natBefore := (← get).natApps.size
  let mark := (← get).boundMentions.size
  let (b, tb) ← elabExpr { bodyCx with binders := cx.binders ++ new, instances := cx.instances * combos.size } body
  if cx.noteIndexes then lintQuant span all bs new body mark
  let kw := if all then "forall" else "exists"
  unless tb == .bool do mismatch body .bool tb (some s!"note: the body of `{kw}` is a `Bool`")
  -- Its verdict, from its bound names of types that are not listed, in order.
  let verdict ← if !candidate then pure Fren.Core.ElementVerdict.notMembers else do
    let recorded := (← get).elemMembers
    let inner := body.declaredNames.map Name.mkSimple
    let unbounded := new.filter (·.unbounded)
    let mut infos := #[]
    for c in unbounded, e? in members, k in [0:unbounded.size] do
      let some e := e? | continue
      let seq := (recorded.find? (·.1 == e.span)).any (·.2.1)
      let earlier := (unbounded.extract 0 k).map (·.name) ++ (cx.binders.filter (·.unbounded)).map (·.name)
      infos := infos.push
        { members := if seq then .seq else .set
          receiverBound := (mentions e).any (earlier.contains ·.getRoot)
          uses := (← elementUses cx c.name inner body).toList : Fren.Core.ElementBinder }
    -- What the quantifier mentions, once its own bound names are not.
    let whole := Expr.quant span all bs body
    let chain := if nesting == .direct then cx.elemChain else #[]
    let bound := (mentions whole).any fun n =>
      let r := n.getRoot
      !chain.contains r && (cx.binder? r).any (·.unbounded)
    pure (Fren.Core.elementVerdict nesting (← mentionsOutput cx whole) bound infos.toList)
  let inCore := verdict == .inCore
  -- The reports that its guard's memberships deferred, and its binders'.
  let spans := members.filterMap (·.map (·.span))
  let deferred := (← get).elemMembers.filter (spans.contains ·.1)
  modify fun s => { s with elemMembers := s.elemMembers.filter (!spans.contains ·.1) }
  unless inCore do
    modify fun s => { s with quantified := true }
    for (_, _, r?) in deferred do
      if let some (sp, msg) := r? then
        modify fun s => { s with outsideCore := true }
        lint .undecidable sp msg
    unless cx.unmentioned do
      for sp in unlisted do
        modify fun s => { s with outsideCore := true }
        lint .undecidable sp ((Fren.Core.elementUndecidableMsg verdict).getD (Fren.Core.undecidableMsg .quantifier false))
  -- A bound name of a type that is not listed, with a domain, makes the
  -- queries set `fmf-bound` (`Reqs/Lang/Quantifiers#guards`), unless the
  -- quantifier is expanded.
  if !inCore && new.zipIdx.any (fun (c, k) => c.unbounded && (domainOf all names body k (c.ty == Ty.nat)).1 != .unbounded) then
    modify fun s => { s with guardedUsed := true }
  let syms := new.filterMap fun c => if c.unbounded then none else some c.smt
  let inst (smt : String) (vals : Array String) : String :=
    substQuoted (fun p => match syms.idxOf? (quote p) with | some i => vals[i]! | none => quote p) smt
  let inner ← takeIndexes
  let innerTables ← takeTables
  modify fun s => { s with indexes := outer ++ inner.map (fun (sp, g, t) => (sp, bindFree free true (conj (combos.map (inst g))) inCore, t)),
                           tables := outerTables ++ innerTables.map fun (sp, q, g) => (sp, q, bindFree free true (conj (combos.map (inst g))) inCore) }
  -- The `Nat` applications in the body, at each instance, as the solver
  -- sees them (`natFacts`); one whose arguments mention a bound name of a
  -- type that is not listed brings its facts for every value of the bound
  -- names, as each holds whatever the arguments: the solver's quantifier
  -- over them, around it, whose facts are within it (`appFactsOf`).
  let freeIn (app : String) : Array FreeBound := free.filter fun u => (app.splitOn u.sym).length > 1
  let close (app : String) : String :=
    let us := freeIn app
    if us.isEmpty then app
    else s!"(forall ({" ".intercalate (us.toList.map fun u => s!"({u.sym} {u.sort})")}) {app})"
  modify fun s => { s with natApps := s.natApps.extract 0 natBefore
    ++ ((s.natApps.extract natBefore).map close |>.flatMap fun app => combos.map (inst app)).toList.eraseDups.toArray }
  let instances := combos.map (inst b)
  let expanded := if all then conj instances else if instances.size == 1 then instances[0]! else s!"(or {" ".intercalate instances.toList})"
  return (bindFree free all expanded inCore, .bool)

/-- `elabExpr` on an `if`. -/
partial def elabIteExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (inElse : Bool) (span : Span) (c : Expr) (a : Expr) (b : Expr) : M (String × Ty) := do
  let pair := exprPair .branch
  if cx.noteIndexes && !inElse then lintIfChain cx e
  -- `same_branches` (`lint::same_branches`): not where the condition's
  -- pattern tests bind names, which the `then` branch sees and the `else`
  -- branch does not, so that the same text may mean different values
  -- (`lang::test_scope`).
  if cx.noteIndexes then
    let ta ← srcAt a.span
    if Fren.Core.sameBranches (← chainBinds cx c) (Fren.Core.writtenSame ta (← srcAt b.span)) then
      let .mk kind .. := a.boolNode
      lintFix .sameBranches span (Fren.Core.sameBranchesMsg ta kind.prec (← srcAt { start := 0, stop := span.start })
        (← srcAt { start := span.stop, stop := (← get).src.size }))
  if cx.noteIndexes then
    let ms ← mentionedNames cx c
    unless ms.isEmpty do modify fun s => { s with mentioning := s.mentioning.push (c.span, ms) }
  -- The names that the condition's pattern tests bind, which the `then`
  -- branch sees (`lang::test_scope`).
  let (c, new) ← withBound do
    exprExpect { cx with testContext := .ifCondition } c .bool (some "note: the condition of `if` is a `Bool`")
  let gx := Fren.Core.GuardedOperand.thenBranch.guard c s!"(not {c})"
  let gy := Fren.Core.GuardedOperand.elseBranch.guard c s!"(not {c})"
  let seen (site : Fren.Core.TestSite) := if Fren.Core.binderVisible .ifCondition 0 1 site then new else #[]
  let ((x, tx), (y, ty)) ← pair { cx with expected?, guards := cx.guards.push gx, binders := cx.binders ++ seen .body }
    { cx with expected?, guards := cx.guards.push gy, inElse := true, binders := cx.binders ++ seen .elseBranch } a b
  liftMsg span (Fren.Core.checkBranches tx ty)
  return (s!"(ite {c} {x} {y})", tx.join ty)

/-- `elabExpr` on a negation `-a`. -/
partial def elabNegExpr (cx : ExprCtx) (span : Span) (a : Expr) : M (String × Ty) := do
  let number := exprNumber
  let newtypeOp := @exprNewtypeOp
  let (x, t) ← elabExpr cx a
  newtypeOp "-" span t t (pre := true)
  number a t "-"
  return (s!"(- {x})", .int)

/-- `elabExpr` on a set literal. -/
partial def elabSetExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (elems : Array Expr) : M (String × Ty) := do
  -- A literal's type may be written nowhere, as in `x in {1}`.
  modify fun s => { s with usesSets := true }
  if elems.isEmpty then
    let t ← liftMsg span (Fren.Core.checkEmptyLiteral false expected?)
    return (s!"(as set.empty {t.sort})", t)
  -- Before its members, whose errors would hide them, as in Lean.
  checkCore cx span .setAlgebra true true elems
  -- `duplicate_elements` (`lint::duplicate_elements`).
  if cx.noteIndexes then
    let repeats := Fren.Core.repeatedElements (← elems.mapM (srcAt ·.span))
    if Fren.Core.duplicateElements repeats.size then
      let range (sp : Span) : Fren.Core.Range := { start := sp.start, stop := sp.stop }
      lintFix .duplicateElements span
        (Fren.Core.duplicateElementsMsg (← get).src (range span) (elems.map (range ·.span)) repeats)
  -- A member, as the fields of its tuple, and the type of the literal
  -- it makes: a pair makes a relation.
  let member (e : Expr) (expected? : Option Ty) : M (String × Ty) := do
    if let some (a, b) := e.pair? (← get).src then
      let (ea?, eb?) := match expected? with | some (.rel x y) => (some x, some y) | _ => (none, none)
      let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected ea? none } a
      let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected eb? none } b
      return (s!"{x} {y}", .rel tx.widen ty.widen)
    let (x, t) ← elabExpr { cx with expected? := expected?.bind fun | .set t => some t | _ => none } e
    return (x, .set t.widen)
  -- Each member is checked against the literal's type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  let sibling? ← if expected?.isNone && !(← synthesizes cx elems[0]!) then
      match ← elems.findM? (synthesizes cx) with
      | some m => do
        let saved ← get
        let t ← (·.2) <$> member m none
        set saved
        pure (some t)
      | none => pure none
    else pure none
  let (x0, t0) ← member elems[0]! (Fren.Core.ExprSite.element.expected expected? sibling?)
  let mut xs := #[x0]
  for e in elems.extract 1 do
    let (x, t) ← member e (Fren.Core.ExprSite.element.expected none (some t0))
    unless t == t0 do
      let (mt, mt0) := match t, t0 with | .set u, .set u0 => (u.show, u0.show) | _, _ => (t.show, t0.show)
      err e.span (Fren.Core.membersMsg false mt0 mt t0.show)
    xs := xs.push x
  let ts := xs.map (s!"(tuple {·})")
  let smt := if ts.size == 1 then s!"(set.singleton {ts[0]!})"
    else s!"(set.insert {" ".intercalate (ts.pop.toList)} (set.singleton {ts.back!}))"
  return (smt, t0)

/-- `elabExpr` on a sequence literal. -/
partial def elabSeqExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (elems : Array Expr) : M (String × Ty) := do
  modify fun s => { s with usesSeqs := true }
  if elems.isEmpty then
    let t ← liftMsg span (Fren.Core.checkEmptyLiteral true expected?)
    return (s!"(as seq.empty {t.sort})", t)
  -- Each element is checked against the literal's element type, or another's
  -- (`lang::checked`): the first that synthesizes one, if the first does not.
  let whole? := expected?.bind fun | .seq t => some t | _ => none
  let sibling? ← match whole? with
    | some _ => pure none
    | none => if ← synthesizes cx elems[0]! then pure none else
        match ← elems.findM? (synthesizes cx) with
        | some m => do
          let saved ← get
          let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } m
          set saved
          pure (some t)
        | none => pure none
  let (x0, t0) ← elabExpr { cx with expected? := Fren.Core.ExprSite.element.expected whole? sibling? } elems[0]!
  -- An element is never a `Nat` (`lang::nat_place`).
  let t0 := t0.widen
  let mut xs := #[x0]
  for e in elems.extract 1 do
    let (x, t) ← elabExpr { cx with expected? := Fren.Core.ExprSite.element.expected none (some t0) } e
    let t := t.widen
    unless t == t0 do
      err e.span (Fren.Core.membersMsg true t0.show t.show (Ty.seq t0).show)
    xs := xs.push x
  checkCore cx span .seqArray true true elems
  let us := xs.map (s!"(seq.unit {·})")
  return (if us.size == 1 then us[0]! else s!"(seq.++ {" ".intercalate us.toList})", .seq t0)

/-- `elabExpr` on an index `q[i]`. -/
partial def elabIndexExpr (cx : ExprCtx) (span : Span) (q : Expr) (i : Expr) : M (String × Ty) := do
  let expect := @exprExpect cx
  let (x, tq) ← elabExpr cx q
  let .seq elem := tq | err q.span (Fren.Core.notIndexableMsg tq.show)
  let ix ← expect i .int (some "note: an index is an `Int`")
  checkCore cx span .seqArray true true #[q, i]
  -- `negative_position` (`lint::negative_position`).
  if let (true, some k) := (cx.noteIndexes, Fren.Core.negativeLiteral? (← srcAt i.span)) then
    let src := (← get).src
    lint .negativePosition span (Fren.Core.negativeIndexMsg (Fren.Core.textOf src (Fren.Core.withParens src (toRange (q.writtenSpan src)))) k)
  noteIndex cx span x ix
  return (s!"(seq.nth {x} {ix})", elem)

/-- `elabExpr` on a string literal. -/
partial def elabStrExpr (span : Span) (v : String) : M (String × Ty) := do
  liftMsg span (Fren.Core.checkStringChars v)
  modify fun s => { s with usesStrings := true }
  return (Fren.Core.smtStringLit v, .string)

/-- `elabExpr` on a method call. -/
partial def elabMethodExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (span : Span) (recv : Expr) (m : Ident) (args : Array Expr) : M (String × Ty) := do
  let src := (← get).src
  -- Where `e` is, as `lang::operand` sees it.
  let slot := parent?.bind (Expr.operandSlot src · e)
  let lintChain := exprLintChain cx e parent? src slot
  if args.isEmpty then lintChain
  -- `trivial_pattern` (`lint::trivial_pattern`).
  if let (true, #[.str _ p], true) := (m.name == "matches?", args, cx.noteIndexes) then
    -- `manual_pattern_char_comparison` and `almost_complete_range`
    -- (`lint::manual_pattern_char_comparison`, `lint::almost_complete_range`).
    if (Fren.Core.parseRe p) matches .ok _ then
      let lit ← srcAt args[0]!.span
      if let some fixed := Fren.Core.charClassPattern? p then
        lintFix .manualPatternCharComparison args[0]!.span
          (Fren.Core.manualPatternCharComparisonMsg (Fren.Core.patternLiteral lit fixed))
      if let some (fixed, found) := Fren.Core.completeRangesPattern? p then
        lintFix .almostCompleteRange args[0]!.span (Fren.Core.almostCompleteRangeMsg found (Fren.Core.patternLiteral lit fixed))
      -- `literal_dot_in_pattern` (`lint::literal_dot_in_pattern`).
      if let some (fixed, found) := Fren.Core.literalDotsPattern? p then
        lintFix .literalDotInPattern args[0]!.span (Fren.Core.literalDotMsg found (Fren.Core.patternLiteral lit fixed))
    if let some (fix, lit) := Fren.Core.trivialPattern? p then
      let bare : Fren.Core.BText := { text := ← srcAt recv.span, prec := recv.boolNode.kind.prec }
      let fixed := Fren.Core.trivialPatternText bare (recv.text src).text fix lit
      lintFix .trivialPattern (e.writtenSpan src) (Fren.Core.trivialPatternMsg fix (fixed.inSlot slot))
  let (r, t) ← elabExpr { cx with concatOk := true, expected? := Fren.Core.ExprSite.receiver.expected none none } recv
  let mut as := #[]
  for a in args do
    -- A pattern, as SMT-LIB's regular expression.
    if m.name == "matches?" && t == .string then
      let .str sp pat := a | err a.span Fren.Core.patternNotLiteralMsg
      match Fren.Core.parseRe pat with
      | .ok re => as := as.push (re.toSmt, .string, sp)
      | .error e =>
        -- The column in the source: after `r`, `#`s and `"`.
        let st ← get
        let pre := ((st.src.extract sp.start sp.stop).toList.takeWhile (· != '"')).length + 1
        let col := sp.start + pre + e.column
        err { start := col, stop := min (col + 1) (sp.stop - 1) } e.msg
      continue
    -- A sequence method's argument has the receiver's type or its element's.
    let expected? := match t, Fren.Core.Method.ofName? m.name with
      | .seq elem, some method => Fren.Core.ExprSite.seqMethodArgument.expected (match method.params[as.size]? with
        | some .string => some t | some .elem => some elem | some .int => some .int | _ => none) none
      -- A `Nat` is expected of `min`'s and `max`'s argument where one is of
      -- the whole (`lang::nat_result`), which is no type it is checked
      -- against: an `Int` is one too.
      | .nat, some .min | .nat, some .max => expected?.filter (· == .nat)
      -- An enumeration's or record's `min` and `max` take the receiver's
      -- type, so a variant of a generic type takes its type arguments.
      | .enum .., some .min | .enum .., some .max | .record .., some .min | .record .., some .max =>
        Fren.Core.ExprSite.orderedMethodArgument.expected (some t) none
      | _, _ => Fren.Core.ExprSite.methodArgument.expected none none
    let (x, ta) ← elabExpr { cx with expected? } a
    as := as.push (x, ta, a.span)
  -- Typed before it is linted, as in Lean, so that a call with a type
  -- error reports no lint of its own (`Reqs/View#static-errors`).
  let res ← callMethod m.span r t m.name as
  if let (.string, some method) := (t, Fren.Core.Method.ofName? m.name) then
    let constantArgs ← args.allM (isConstant cx)
    let recvConstant ← isConstant cx recv
    -- `min` and `max` compare their strings, as `<=` does.
    let comparable := !(method matches .min | .max) || constantArgs || recvConstant
    checkCore cx span method.construct constantArgs comparable (#[recv] ++ args) (constantArgs && recvConstant)
  -- `min` and `max` of an ordered record or newtype with a `String`
  -- within compare strings (`Reqs/Lang/Decidability#orderings`).
  if (t matches .record .. | .newtype ..) && (m.name == "min" || m.name == "max") then
    if let some plan ← orderPlan? t then
      if plan.strings then
        let (ca, cb) := (← isConstant cx recv, ← args.allM (isConstant cx))
        checkCore cx span .stringCompare true (ca || cb) (#[recv] ++ args) (ca && cb)
  if let (.seq _, some method) := (t, Fren.Core.Method.ofName? m.name) then
    checkCore cx span method.seqConstruct true true (#[recv] ++ args)
      ((← args.allM (isConstant cx)) && (← isConstant cx recv)) (literalOperand := args.any (· matches .seq ..))
  if let some tys := relRange? t m.name then checkRelational cx span tys (#[recv] ++ args)
  checkRelationalCard cx span t m.name recv
  -- `empty_argument` (`lint::empty_argument`).
  if let (some meth, true) := (Fren.Core.Method.ofName? m.name, cx.noteIndexes) then
    -- The receiver as written, with its parentheses, as in the help
    -- `(a ++ b).at((a ++ b).len - 1)`.
    let src := (← get).src
    let recvText := Fren.Core.textOf src (Fren.Core.withParens src (toRange (recv.writtenSpan src)))
    if let some msg := Fren.Core.emptyArgumentMsg? meth (t matches .seq _) recvText (← args.mapM (srcAt ·.span)) then
      lint .emptyArgument span msg
    -- `negative_position` (`lint::negative_position`).
    if let some msg := Fren.Core.negativeArgumentMsg? meth (t matches .seq _) recvText (← args.mapM (srcAt ·.span)) then
      lint .negativePosition span msg
  return res

/-- What the first of the operands `es` of an ordering is expected to be:
if it does not synthesize its type, the type, widened, of the first that
does, elaborated without effect; otherwise nothing, as each later operand
is expected to be of the first's type (`lang::checked`). So a variant of a
generic enumeration takes its type arguments from the other side, as in
`Level::Low < x`. -/
partial def orderingExpected? (cx : ExprCtx) (es : Array Expr) : M (Option Ty) := do
  if ← synthesizes cx es[0]! then return none
  let some m ← es.findM? (synthesizes cx) | return none
  let saved ← get
  let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } m
  set saved
  return some t.widen

/-- `elabExpr` on a chain of comparisons. -/
partial def elabChainExpr (cx : ExprCtx) (es : Array Expr) (ops : Array (String × Span)) : M (String × Ty) := do
  let newtypeOp := @exprNewtypeOp
  -- `a < b <= c` is `a < b and b <= c`, with `b` elaborated once
  -- (`Reqs/Lang/Expressions#chained-comparisons`). As in that expansion,
  -- the comparisons before an operand guard it. The parser has checked
  -- its operators.
  let (x0, t0) ← elabExpr { cx with expected? := Fren.Core.ExprSite.comparedOperand.expected none (← orderingExpected? cx es) } es[0]!
  -- The first operand gives the operands' type, a `Nat` widened, if it
  -- is ordered (`lang::operator_type`, `lang::ordered_type`), which each
  -- later operand is expected to have (`lang::checked`).
  let u ← liftMsg es[0]!.span (Fren.Core.orderingType ops[0]!.1 t0 (← orderedDecl))
  let plan := (← orderPlan? u).getD .number
  let mut (x, ca) := (x0, ← isConstant cx es[0]!)
  let mut links := #[]
  for (op, _) in ops, a in es, b in es.extract 1 do
    let (y, tb) ← elabExpr { cx with guards := cx.guards ++ links, expected? := Fren.Core.ExprSite.comparedOperand.expected none (some u) } b
    newtypeOp op (a.span.to b.span) u tb
    liftMsg b.span (Fren.Core.checkType u tb (Fren.Core.opNote op u))
    let cb ← isConstant cx b
    if plan.strings then
      checkCore cx (a.span.to b.span) .stringCompare true (ca || cb) #[a, b] (ca && cb)
    -- SMT-LIB has only `str.<` and `str.<=`.
    links := links.push <| ← if u != .string then orderingSmt plan op x y else pure <| match op with
      | "<" => s!"(str.< {x} {y})"
      | "<=" => s!"(str.<= {x} {y})"
      | ">" => s!"(str.< {y} {x})"
      | _ => s!"(str.<= {y} {x})"
    (x, ca) := (y, cb)
  return (s!"(and {" ".intercalate links.toList})", .bool)

/-- `elabExpr` on a binary operator. -/
partial def elabBinExpr (cx : ExprCtx) (e : Expr) (concatOk : Bool) (expected? : Option Ty) (chain : String)
    (test : Fren.Core.TestContext × Option (Nat × Nat)) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  -- `eq_op` (`lint::eq_op`).
  if let (some o, true) := (Fren.Core.InfixOp.ofOp? op, cx.noteIndexes) then
    -- Only for an operator that `eqOp` can report, whatever the operands.
    if (Fren.Core.eqOp o true).isSome then
      let ta ← srcAt a.span
      -- The right operand of `and` sees the names that the left's pattern
      -- tests bind (`lang::test_scope`).
      let seen ← if op == "and" then chainBinders cx a else pure []
      if let some v := Fren.Core.eqOp o (Fren.Core.writtenSameIn ta (← srcAt b.span) [] seen) then
        lint .eqOp span (Fren.Core.eqOpMsg o v ta)
  match op with
  | "iff" | "or" | "and" => elabBoolOpExpr cx e chain test span op a b
  | "=" | "!=" => elabEqualityExpr cx e span op a b
  | "<" | "<=" | ">" | ">=" => elabComparisonExpr cx e span op a b
  | "in" => elabInExpr cx e span a b
  | "union" | "inter" | "minus" | "subset" => elabSetOpExpr cx expected? span op a b
  | "join" => elabJoinExpr cx span a b
  | "++" => elabConcatExpr cx e concatOk expected? span op a b
  | "div" | "mod" => elabDivModExpr cx expected? span op a b
  | _ => elabArithExpr cx expected? span op a b

/-- `elabExpr` on a Boolean operator. -/
partial def elabBoolOpExpr (cx : ExprCtx) (e : Expr) (chain : String) (test : Fren.Core.TestContext × Option (Nat × Nat))
    (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let opNote := Fren.Core.opNote
  let smt := if op == "iff" then "=" else op
  -- `membership_chain`, at the top of a chain of `or` or of `and` (`lint::membership_chain`).
  if op != "iff" && chain != op && cx.noteIndexes then
    let ds := chainOperands op e
    let cmp := if op == "and" then "!=" else "="
    let eqs := ds.filterMap fun | .bin _ c l r => if c == cmp then some (l, r) else none | _ => none
    let lefts ← eqs.mapM fun (l, _) => srcAt l.span
    let same := eqs.size == ds.size && lefts.all (· == lefts[0]!)
    let laterIndexes ← (eqs.extract 1).anyM fun (_, v) => return !(← indexedIn v).isEmpty
    let patterns ← eqs.allM fun (_, v) => return Fren.Core.patternValue (← srcAt v.span) (← variantOf? cx v).isSome
    if Fren.Core.membershipChainFires ds.size same laterIndexes patterns then
      lintFix .membershipChain span
        (Fren.Core.membershipChainMsg lefts[0]! (← eqs.mapM fun (_, r) => srcAt r.span) (op == "and"))
  -- `index_after_use` (`lint::index_after_use`).
  if op == "and" && cx.noteIndexes && !(← chainBinds cx a) then
    let qs ← indexedIn a
    if ← qs.anyM fun q => return (← boundsSeq b q) && !(← boundsSeq a q) then
      lintFix .indexAfterUse span (Fren.Core.indexAfterUseMsg (← srcAt a.span) (← srcAt b.span))
  -- For `manual_at_most_one`: whether the operands give a definedness
  -- obligation.
  let mark := (← get).indexes.size + (← get).tables.size
  -- Of `and`, the position of each operand in its chain, and the names
  -- that the left one's pattern tests bind, which the right one sees; at
  -- the top of the chain, those of the whole, which only the body of the
  -- `when` or `if` whose condition it is sees (`lang::test_scope`).
  let (context, at?) := test
  let (k, n) := at?.getD (0, (chainOperands "and" e).size)
  let left := (chainOperands "and" a).size
  let (acx, bcx) : ExprCtx × ExprCtx := match op with
    | "and" => ({ cx with testContext := context, testAt? := some (k, n) }, { cx with testContext := context, testAt? := some (k + left, n) })
    | "or" => ({ cx with testContext := .orOperand }, { cx with testContext := .orOperand })
    | _ => (cx, cx)
  let boundMark := (← get).bound.size
  let (x, tx) ← elabExpr { acx with chain := op } a
  unless tx == .bool do mismatch a .bool tx (opNote op .bool)
  -- `b` is evaluated when `a` does not decide the result.
  let guards := match op with
    | "and" => cx.guards.push (Fren.Core.GuardedOperand.andRight.guard x s!"(not {x})")
    | "or" => cx.guards.push (Fren.Core.GuardedOperand.orRight.guard x s!"(not {x})")
    | _ => cx.guards
  let bound := (← get).bound
  let new := if op == "and" then bound.extract boundMark else #[]
  let (y, ty) ← elabExpr { bcx with guards, chain := op, binders := cx.binders ++ new } b
  unless ty == .bool do mismatch b .bool ty (opNote op .bool)
  if op == "and" && at?.isNone && !Fren.Core.binderVisible context 0 n .body then
    modify fun s => { s with bound := s.bound.extract 0 boundMark }
  if op == "and" && cx.noteIndexes && (← get).indexes.size + (← get).tables.size > mark then
    modify fun s => { s with facts := s.facts.push (span, .obligations) }
  return (s!"({smt} {x} {y})", .bool)

/-- `elabExpr` on `=` or `!=`. -/
partial def elabEqualityExpr (cx : ExprCtx) (e : Expr) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  -- Functions are not compared (`lang::function_comparison`).
  unless Fren.Core.comparisonAccepted [← comparand cx a, ← comparand cx b] do
    err span (Fren.Core.functionComparisonMsg op)
  let pair := exprPair .comparedOperand
  let lintLength := exprLintLength cx e
  lintLength op a b
  -- `++` is in the core against a constant.
  let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
  let ((x, tx), (y, ty)) ← pair { cx with concatOk := cb } { cx with concatOk := ca } a b
  liftMsg span (Fren.Core.checkComparable op tx ty)
  -- For `manual_pattern_test`, at the end of the expression.
  if cx.noteIndexes && (tx == .nat || ty == .nat) then modify fun s => { s with facts := s.facts.push (span, .natOperands) }
  -- `const_is_empty` on a literal and an empty one (`lint::const_empty_equation`),
  -- after the sides and their types, as in Lean.
  if let (some (_, m), some (_, n), true) := (a.literalCount?, b.literalCount?, cx.noteIndexes) then
    let (fires, value) := Fren.Core.constEmptyEquation (op == "=") (max m n)
    if fires && min m n == 0 then lint .constIsEmpty span (Fren.Core.constIsEmptyMsg value)
  -- For `bool_equality`, at the end of the expression.
  if tx == .bool && cx.noteIndexes then modify fun s => { s with boolEqs := s.boolEqs.push span }
  -- A side that is a `++` is reported as one; one whose definition
  -- has a `++` stands for it, and is reported here.
  let named (e : Expr) : M Bool := do
    return (definitionOf? cx e).isSome && (← hasConcat cx e)
  let concat (e : Expr) := e matches .bin _ "++" _ _
  if tx == .string && ((← named a) || (← named b)) then
    checkCore cx span .stringSearch true true #[] (ca || cb)
  else if tx == .string && !concat a && !concat b then
    checkCore cx span .stringCompare true (ca || cb || (isVariable a && isVariable b)) #[] (ca && cb)
  return (if op == "=" then s!"(= {x} {y})" else s!"(distinct {x} {y})", .bool)

/-- `elabExpr` on an ordering comparison. -/
partial def elabComparisonExpr (cx : ExprCtx) (e : Expr) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let newtypeOp := @exprNewtypeOp
  let lintLength := exprLintLength cx e
  lintLength op a b
  -- The left operand gives the operands' type, if it is ordered
  -- (`lang::operator_type`, `lang::ordered_type`); a newtype on either
  -- side is the newtype's error (`lang::newtype_operator`). The right is
  -- expected to have the left's type, and the left the right's, if only the
  -- right synthesizes one (`lang::checked`).
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.comparedOperand.expected none (← orderingExpected? cx #[a, b]) } a
  let t ← liftMsg a.span (Fren.Core.orderingType op tx (← orderedDecl))
  let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.comparedOperand.expected none (some t) } b
  newtypeOp op span tx ty
  liftMsg b.span (Fren.Core.checkType t ty (Fren.Core.opNote op t))
  -- For the lints of integers, at the end of the expression: what it compares.
  if cx.noteIndexes && !(tx matches .newtype ..) then
    let ordered : Fren.Core.Ordered := if t matches .enum .. then .enumeration
      else if t == .int || t == .nat then .number else .other
    modify fun s => { s with ordereds := s.ordereds.push (span, ordered) }
  let plan := (← orderPlan? t).getD .number
  if plan.strings then
    let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
    checkCore cx span .stringCompare true (ca || cb) #[a, b] (ca && cb)
  -- An ordered enumeration's values compare by their positions, and an
  -- ordered record's by its fields (`Reqs/Lang/Items#ordered-declarations`).
  return (← orderingSmt plan op x y, .bool)

/-- `elabExpr` on `in`. -/
partial def elabInExpr (cx : ExprCtx) (e : Expr) (span : Span) (a : Expr) (b : Expr) : M (String × Ty) := do
  -- Before its operands, whose errors would hide it, as in Lean.
  checkCore cx span .setAlgebra true true #[a, b]
  if let (.set _ #[m], true) := (b, cx.noteIndexes) then
    unless m matches .pair .. do lintFix .singletonMembership span (Fren.Core.singletonMembershipMsg (← srcAt a.span) (← srcAt m.span))
  if let some (pa, pb) := a.pair? (← get).src then
    let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected none none } pa
    let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.pairMember.expected none none } pb
    let (tx, ty) := (tx.widen, ty.widen)
    let (r, tr) ← elabExpr { cx with expected? := Fren.Core.ExprSite.membershipRight.expected none (some (.rel tx ty)) } b
    unless tr == .rel tx ty do
      err span (Fren.Core.membershipTypeMsg (Ty.rel tx ty).show tr.show true)
    return (s!"(set.member (tuple {x} {y}) {r})", .bool)
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.membershipLeft.expected none none } a
  -- A member is never a `Nat`: one is widened (`lang::nat_place`).
  let tx := tx.widen
  -- The right is checked against a set or sequence of the left's type, as
  -- it is written (`lang::checked`).
  let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.membershipRight.expected none (some (if seqShaped b then .seq tx else .set tx)) } b
  -- The membership of a quantifier over elements' guard: its report waits
  -- for the quantifier's verdict (`elabQuantExpr`).
  if cx.elemGuards.contains b.span then
    let infinite ← #[a, b].anyM (mentionsInfiniteOutput cx)
    let ground ← isConstant cx e
    let report := if ty != .seq tx || cx.unmentioned
        || Fren.Core.inCore .seqWord true true infinite ground (literalOperand := b matches .seq ..)
      then none else some (span, Fren.Core.undecidableMsg .seqWord infinite)
    modify fun s => { s with elemMembers := s.elemMembers.push (b.span, ty == .seq tx, report) }
    if ty == .seq tx then return (s!"(seq.contains {y} (seq.unit {x}))", .bool)
  if ty == .seq tx then
    checkCore cx span .seqWord true true #[a, b] (← isConstant cx e) (literalOperand := b matches .seq ..)
    return (s!"(seq.contains {y} (seq.unit {x}))", .bool)
  unless ty == .set tx do
    err span { code? := some "F0325", headline := s!"`in` needs a `Set<{tx.show}>` on its right, found `{ty.show}`"
               label? := some s!"`{tx.show}` and `{ty.show}`"
               notes := #["note: `x in s` is membership: `s` is a set of values of `x`'s type"] }
  return (s!"(set.member (tuple {x}) {y})", .bool)

/-- `elabExpr` on a set operator. -/
partial def elabSetOpExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let site : Fren.Core.ExprSite := if op == "subset" then .subsetOperand else .setOperand
  let pair := exprPair site
  -- Before its operands, whose errors would hide it, as in Lean.
  checkCore cx span .setAlgebra true true #[a, b]
  -- The operands of `subset` give each other their type, and those of the
  -- others are also checked against the whole's (`lang::checked`).
  let expected? := if op == "subset" then none else expected?
  let ((x, tx), (y, ty)) ← pair { cx with expected? } { cx with expected? } a b
  match Fren.Core.checkSetOperands op tx ty with
  | .ok () => pure ()
  | .error (k, msg) => err (if k == 0 then a else b).span msg
  let smt := match op with
    | "union" => "set.union" | "inter" => "set.inter" | "minus" => "set.minus" | _ => "set.subset"
  return (s!"({smt} {x} {y})", if op == "subset" then .bool else tx)

/-- `elabExpr` on `join`. -/
partial def elabJoinExpr (cx : ExprCtx) (span : Span) (a : Expr) (b : Expr) : M (String × Ty) := do
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.joinOperand.expected none none } a
  let .rel ta tb := tx | err a.span (Fren.Core.joinTypeMsg tx.show none)
  -- Both operands synthesize their types (`lang::checked`).
  let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.joinOperand.expected none none } b
  let .rel tb' tc := ty | err b.span (Fren.Core.joinTypeMsg ty.show none)
  unless tb == tb' do err span (Fren.Core.joinTypeMsg tx.show (some ty.show))
  checkRelational cx span #[tb] #[a, b]
  return (s!"(rel.join {x} {y})", .rel ta tc)

/-- `elabExpr` on `++`. -/
partial def elabConcatExpr (cx : ExprCtx) (e : Expr) (concatOk : Bool) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let opNote := Fren.Core.opNote
  let newtypeOp := @exprNewtypeOp
  -- Each operand is checked against the whole's type, or the other's
  -- (`lang::checked`): `[] ++ q` takes its type from `q`.
  let sibling? ← if expected?.isNone && !(← synthesizes cx a) && (← synthesizes cx b) then do
      let saved ← get
      let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } b
      set saved
      pure (some t)
    else pure none
  let (x, tx) ← elabExpr { cx with expected? := Fren.Core.ExprSite.concatOperand.expected expected? sibling?, concatOk := true } a
  newtypeOp op span tx tx
  if let .seq _ := tx then
    let (y, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.concatOperand.expected none (some tx) } b
    liftMsg b.span (Fren.Core.checkConcatOperands tx ty)
    checkCore cx span .seqWord true true #[a, b] (← isConstant cx e)
    return (s!"(seq.++ {x} {y})", tx)
  -- Where the core allows it, only its operands' outputs matter.
  if concatOk then checkCore cx span .stringAtom true true #[a, b]
  else checkCore cx span .stringSearch true true #[a, b] (← isConstant cx e)
  unless tx == .string do mismatch a .string tx (opNote op .string)
  let (y, ty) ← elabExpr { cx with concatOk := true, expected? := Fren.Core.ExprSite.stringOperand.expected none none } b
  unless ty == .string do mismatch b .string ty (opNote op .string)
  return (s!"(str.++ {x} {y})", .string)

/-- `elabExpr` on `div` or `mod`. -/
partial def elabDivModExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let expect := @exprExpect cx
  let number := exprNumber
  let opNote := Fren.Core.opNote
  let newtypeOp := @exprNewtypeOp
  -- By the divisor's value (`lang::divisor`). A `Nat` is expected of
  -- the dividend where one is of the whole (`lang::nat_result`).
  let (x, tx) ← elabExpr { cx with expected? := if expected? == some .nat then some .nat else none } a
  newtypeOp op span tx tx
  number a tx op
  discard (expect b .int (opNote op .int))
  let (form, value, c) ← divisorForm cx b
  liftMsg b.span (Fren.Core.checkDivisor op form value c)
  -- By a numeral, which the linear logics require: Euclidean,
  -- `x div -k` is `-(x div k)` and `x mod -k` is `x mod k`.
  let k := value.natAbs
  let nat := Fren.Core.natResult (if op == "mod" then .mod else .div) (tx == .nat) false (value > 0)
  return (if op == "mod" then s!"(mod {x} {k})" else if value < 0 then s!"(- (div {x} {k}))" else s!"(div {x} {k})",
    if nat then .nat else .int)

/-- `elabExpr` on `+`, `-` or `*`. -/
partial def elabArithExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (op : String) (a : Expr) (b : Expr) : M (String × Ty) := do
  let number := exprNumber
  let newtypeOp := @exprNewtypeOp
  if op == "*" then
    let (ma, mb) := (← mentionedNames cx a, ← mentionedNames cx b)
    unless cx.unmentioned || Fren.Core.productAccepted ma mb do err span (Fren.Core.nonlinearMsg ma mb)
    -- For `branches_sharing_code`.
    if cx.noteIndexes then
      modify fun s => { s with mentioning := s.mentioning ++ ([(ma, a.span), (mb, b.span)].filter (!·.1.isEmpty) |>.map fun (m, sp) => (sp, m)) }
  -- `+` and `*` of `Nat`s are `Nat`s; `-` is always an `Int`, so that
  -- nothing truncates (`lang::operator_type`).
  let nat := op != "-" && expected? == some .nat
  if nat && op == "+" then modify fun s => { s with natSums := s.natSums.push (s.file, span) }
  let (x, tx) ← elabExpr { cx with expected? := if nat then some .nat else none } a
  -- Of a newtype, the `+` or `-` of the type it is erased to, as
  -- `N(a.0 + b.0)` is; of a number, a newtype on the right is the
  -- newtype's error (`lang::newtype_operator`).
  if let .newtype .. := tx then
    let (y, ty) ← elabExpr cx b
    newtypeOp op span tx ty
    -- `+` of a newtype of `Nat`, whose `-` would be an error.
    if op == "+" && tx.erased == .nat then modify fun s => { s with natSums := s.natSums.push (s.file, span) }
    -- The obligations of `N(a.0 + b.0)`, of each newtype from the
    -- innermost out, which is the erased sum at each.
    let sum := s!"({op} {x} {y})"
    for p in tx.newtypePaths.reverse do
      noteObligation cx .construction span (← partPTy p 0 0) sum
    return (sum, tx)
  number a tx op
  let (y, ty) ← elabExpr { cx with expected? := if nat then some .nat else none } b
  newtypeOp op span tx ty
  number b ty op
  return (s!"({op} {x} {y})", if op != "-" && tx == .nat && ty == .nat then .nat else .int)

/-- `elabExpr` on a path. -/
partial def elabPathExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (segs : Array Ident) : M (String × Ty) := do
  let src := (← get).src
  -- Where `e` is, as `lang::operand` sees it.
  let slot := parent?.bind (Expr.operandSlot src · e)
  let lintChain := exprLintChain cx e parent? src slot
  if segs.size == 1 then
    lintChain
    let n := identName segs[0]!.name
    let span := segs[0]!.span
    -- A binder or variable, then any fields read from it.
    let base? ← if let some b := cx.binder? n.getRoot then do
        if let some sc := b.scrutinee then
          if b.isDef then
            -- A name stands for its definition: its indexes are guarded
            -- here, and what it mentions may be mentioned here, which
            -- elaborating it again checks, without its lints.
            if cx.noteIndexes then
              modify fun s => { s with indexes := s.indexes ++ b.obligations.map (fun (sp, g, t) => (sp, guarded cx.guards g, t)),
                                       tables := s.tables ++ b.tableObligations.map fun (sp, q, g) => (sp, q, guarded cx.guards g) }
            let saved ← get
            discard (elabExpr { cx.at b with noteIndexes := false, pending := #[], expected? := some b.ty } sc)
            set saved
          else discard (elabExpr (cx.at b) sc)
        else if cx.noteIndexes && n.isAtomic then
          modify fun s => { s with boundMentions := s.boundMentions.push (span, b.smt) }
        pure (some ((b.smt, b.ty), n.components.drop 1))
      else
        let ks := (List.range n.components.length).reverse.map (· + 1)
        match ks.findSome? fun k => (cx.vars.find? (·.name == (n.components.take k).foldl (· ++ ·) .anonymous)).map (·, k) with
        | some (v, k) =>
          for u in if cx.unmentioned then #[] else defDeps cx.vars v do
            let earlier := (cx.insts.findIdx? (· == u.name.getRoot)).any (· < cx.current)
            let ok := Fren.Core.checkMention cx.place u.role earlier u.name
            match ok with
            | .ok () => pure ()
            | .error msg => err span (if u.name == v.name then msg else Fren.Core.throughDefinition v.name msg)
          pure (some ((quote v.name.toString, v.ty), n.components.drop k))
        | none =>
          -- A constant, then the fields read from its value, or the
          -- methods without arguments applied to it.
          let root := n.getRoot
          if n.isAtomic || cx.insts.contains root then pure none else
          let st ← get
          match st.table.resolvePath st.scope #[root] cx.shadowing with
          | .ok (.item { kind := .constItem, .. }) =>
            -- Resolved again, to record its use and any import it uses;
            -- the first lookup leaves a root that is not a constant to the
            -- errors below.
            -- The lexer admits only ASCII identifiers, so characters are
            -- offsets.
            let text := (segs[0]!.name.splitOn ".").head!
            let rootSeg : Ident := { name := text, span := { span with stop := span.start + text.length } }
            let .item { kind := .constItem, path, .. } ← resolve #[rootSeg] cx.shadowing | pure none
            let some c := (← get).consts.find? path | internal span s!"unknown constant `{path}`"
            pure (some (c, n.components.drop 1))
          | _ => pure none
    if let some (base, fields) := base? then
      -- The span of each component of the dotted name.
      let parts := segs[0]!.name.splitOn "."
      let starts := parts.foldl (init := #[span.start]) fun acc p => acc.push (acc.back! + p.length + 1)
      let first := parts.length - fields.length
      return ← (fields.zipIdx).foldlM (init := base) fun (smt, t) (f, j) => do
        let fspan : Span := { start := starts[first + j]!, stop := starts[first + j + 1]! - 1 }
        -- Typed before it is linted, as a call is.
        let res ← readField fspan smt t f
        if t == .string then
          let recvName := ".".intercalate (parts.take (first + j))
          let recvSpan : Span := { start := span.start, stop := fspan.start - 1 }
          checkCore cx (span.to fspan) .stringAtom true true #[.path recvSpan #[{ name := recvName, span := recvSpan }]]
        if let some tys := relRange? t f.toString then
          let recvName := ".".intercalate (parts.take (first + j))
          let recvSpan : Span := { start := span.start, stop := fspan.start - 1 }
          checkRelational cx (span.to fspan) tys #[.path recvSpan #[{ name := recvName, span := recvSpan }]]
        let recvName := ".".intercalate (parts.take (first + j))
        let recvSpan : Span := { start := span.start, stop := fspan.start - 1 }
        checkRelationalCard cx (span.to fspan) t f.toString (.path recvSpan #[{ name := recvName, span := recvSpan }])
        if let (.seq _, some m) := (t, Fren.Core.Method.ofName? f.toString) then
          let r : Expr := .path recvSpan #[{ name := recvName, span := recvSpan }]
          checkCore cx (span.to fspan) m.seqConstruct true true #[r] (← isConstant cx r)
        return res
    if let some (_, own) := cx.pending.find? (·.1 == n.getRoot) then
      err span (Fren.Core.definedLaterMsg n.getRoot own)
    if !n.isAtomic then
      err span (Fren.Core.dottedNameMsg n cx.insts (cx.vars.filter (·.role != .instHidden) |>.map (·.name)))
  if segs.size == 1 then
    if let some c := Fren.Core.builtinFunction? (identName segs[0]!.name) then
      err e.span (Fren.Core.unappliedMsg (.mkSimple c.name))
    -- A function parameter, which is applied (`lang::function_argument`).
    if (cx.fnParam? (identName segs[0]!.name)).isSome then
      err e.span (Fren.Core.unappliedMsg (identName segs[0]!.name))
  match ← resolveWritten segs cx.shadowing cx.noteIndexes with
  | .variant en idx =>
    let d := (← get).dataOf? en.path
    let n := (d.bind (·.ctors[idx]?)).map (·.2.size) |>.getD 0
    if let some msg := Fren.Core.variantMentionMsg? (en.path ++ en.variants[idx]!) n false then err e.span msg
    if cx.noteIndexes then
      modify fun s => { s with variants := s.variants.push (e.span, (en.path ++ en.variants[idx]!).toString) }
      if let some d := d then
        if d.ordered then
          modify fun s => { s with facts := s.facts.push (e.span, .ordinal en.path.toString idx d.ctors.size) }
    if let some d := d.filter (!·.params.isEmpty) then
      let (_, args) ← elabConstruction elabExpr .payload { cx with expected? } d #[] #[] e.span (showPath (en.path ++ en.variants[idx]!)) fun _ _ => ""
      return (d.build args.toList en.variants[idx]! [], .enum en.path args.toList)
    return (ctorSym en.path en.variants[idx]!, .enum en.path [])
  | .item { kind := .constItem, path, .. } =>
    let some c := (← get).consts.find? path | internal e.span s!"unknown constant `{path}`"
    -- Its value's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
    return c
  | .item { kind := .fnItem, path, .. } => err e.span (Fren.Core.unappliedMsg path)
  | r => err e.span (Fren.Core.notAValueMsg r)

/-- `elabExpr` on an application. -/
partial def elabAppExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (segs : Array Ident) (args : Array Expr) : M (String × Ty) := do
  let fnSpan := segs[0]!.span.to segs.back!.span
  if segs.size == 1 && (cx.vars.any (·.name == identName segs[0]!.name) || (cx.binder? (identName segs[0]!.name)).isSome) then
    err fnSpan (Fren.Core.varNotAFunctionMsg (identName segs[0]!.name))
  if segs.size == 1 && cx.selfFn == some (Name.mkSimple segs[0]!.name) then
    let f := (← get).module ++ Name.mkSimple segs[0]!.name
    let some (ps, ft, sym) := cx.selfRec? | err fnSpan (Fren.Core.recursiveMsg f)
    -- An application of itself, which must be structural recursion
    -- (`lang::structural_recursion`), typed as a function parameter's.
    unless args.size == ft.params.size do err span (Fren.Core.arityMsg f ft.params.size args.size)
    noteRecUse fnSpan f ps { form := if cx.inClosure then .inClosure else .applied
                             args := args.toList.zipIdx.map fun (a, i) => cx.recArg a i }
    let mut smts := #[]
    for a in args, t in ft.params, k in [0:args.size] do
      let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
      liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{showPath f}` has type `{t.show}`"))
      let pt := (((← get).funPTys.find? f).map (·.1[k]?.getD default)).getD default
      noteObligation cx .argument a.span pt x
      smts := smts.push x
    if cx.noteIndexes then
      modify fun s => { s with recApps := s.recApps.push (fnSpan, smts, cx.guards) }
    return (s!"({sym} {" ".intercalate smts.toList})", ft.result)
  -- A function parameter (`Reqs/Lang/HigherOrder#function-parameters`).
  if segs.size == 1 then
    if let some (ft, sym) := cx.fnParam? (identName segs[0]!.name) then
      let f := identName segs[0]!.name
      unless args.size == ft.params.size do err span (Fren.Core.arityMsg f ft.params.size args.size)
      let mut smts := #[]
      for a in args, t in ft.params, k in [0:args.size] do
        let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
        liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{f}` has type `{t.show}`"))
        smts := smts.push x
      return (s!"({sym} {" ".intercalate smts.toList})", ft.result)
  if segs.size == 1 then
    if let some c := Fren.Core.builtinFunction? (identName segs[0]!.name) then
      -- The number of its arguments that are `true`, compared with 1: a
      -- linear sum (`lang::cardinality`).
      if args.isEmpty then err span (Fren.Core.cardinalityNoArgsMsg c)
      let mut ites := #[]
      for a in args, k in [0:args.size] do
        -- `{}` and `[]` are never `Bool`s.
        if a matches .set _ #[] | .seq _ #[] then
          err a.span (Fren.Core.cardinalityArgMsg c (k + 1) (if a matches .set .. then "{}" else "[]"))
        let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.countArgument.expected none none } a
        unless ta == .bool do err a.span (Fren.Core.cardinalityArgMsg c (k + 1) ta.show)
        ites := ites.push s!"(ite {x} 1 0)"
      let count := if ites.size == 1 then ites[0]! else s!"(+ {" ".intercalate ites.toList})"
      return (s!"({c.smtOp} {count} 1)", .bool)
  -- In its own contract, the function is applied to its parameters, in a
  -- postcondition (`lang::contract_application`); it is not yet in scope.
  let own? := cx.contract?.filter fun (f, _, _) => segs.size == 1 && Name.mkSimple segs[0]!.name == Name.mkSimple f.getString!
  if let some (f, post, params) := own? then
    -- Each argument as written: a name of one segment, not hidden by a
    -- binder, or another expression.
    let written := args.map fun
      | .path _ #[s] => if (cx.binder? (identName s.name)).isNone then some (identName s.name) else none
      | _ => none
    let toParams := Fren.Core.appliesToParams written params
    unless Fren.Core.contractApplicationAccepted (if post then .postcondition else .precondition) true toParams do
      err fnSpan (Fren.Core.contractSelfMsg f !post)
  -- A variable shadows a function, as it does any other item.
  let module := (← get).module
  let resolved ← match own? with
    | some (f, _, _) => pure (.item { kind := .fnItem, path := f, isPub := true, owner := module })
    | none => resolveWritten segs cx.shadowing cx.noteIndexes
  let path ← match resolved with
    | .item { kind := .fnItem, path, .. } =>
      if let some h := (← get).hofs.find? path then
        return ← elabHigherOrderApp cx expected? span fnSpan path h args
      pure path
    | .variant en idx =>
      -- A variant with a payload, built from its values.
      let v := en.variants[idx]!
      let some d := (← get).dataOf? en.path | internal fnSpan s!"unknown enum `{en.path}`"
      let tys := d.ctors[idx]!.2.map (·.2)
      if let some msg := Fren.Core.variantMentionMsg? (en.path ++ v) tys.size true then err span msg
      unless args.size == tys.size do err span (Fren.Core.arityMsg (en.path ++ v) tys.size args.size "value")
      let note (k : Nat) (t : Ty) := s!"note: value {k + 1} of the payload of `{showPath (en.path ++ v)}` has type `{t.show}`"
      if !d.params.isEmpty then
        let (smts, targs) ← elabConstruction elabExpr .payload { cx with expected? } d tys args span (showPath (en.path ++ v)) note
        -- Each value's obligation, of its type with the enumeration's arguments.
        for a in args, x in smts, k in [0:args.size] do
          noteObligation cx .payload a.span (← partPTy en.path idx k targs) x
        return (d.build targs.toList v smts.toList, .enum en.path targs.toList)
      let mut smts := #[]
      for a in args, t in tys, k in [0:args.size] do
        let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.payload.expected (some t) none } a
        liftMsg a.span (Fren.Core.checkType t ta (some (note k t)))
        noteObligation cx .payload a.span (← partPTy en.path idx k) x
        smts := smts.push x
      return (s!"({ctorSym en.path v} {" ".intercalate smts.toList})", .enum en.path [])
    | .item { kind := .recordItem, path, .. } =>
      -- A newtype, built from its value, which is erased
      -- (`Reqs/Lang/Expressions#newtypes`).
      let some u := (← get).newtypes.find? path | err fnSpan (Fren.Core.constructionMsg path false)
      unless args.size == 1 do err span (Fren.Core.arityMsg path 1 args.size "value")
      let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.newtypeValue.expected (some u) none } args[0]!
      unless ta.widens u do mismatch args[0]! u ta (some s!"note: the value of `{showPath path}` has type `{u.show}`")
      if cx.noteIndexes then
        let synth ← synthesizes cx args[0]!
        modify fun s => { s with facts := s.facts.push (span, .wraps path.toString synth) }
      noteObligation cx .construction args[0]!.span (← partPTy path 0 0) x
      return (x, .newtype path u)
    | r => err fnSpan (Fren.Core.notAFunctionMsg r)
  if let some g := (← get).genericFns.find? path then
    -- A generic function, at the instance whose type arguments are inferred
    -- (`Reqs/Lang/GenericFunctions#applications`); its arguments may
    -- mention anything (`lang::argument`).
    -- One without a body is uninterpreted, at each instance
    -- (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`): a
    -- defined function's body applies none (`lang::function_body`), and
    -- outputs may not occur in its arguments (`inst::mention`).
    if !g.defined then
      if cx.selfFn.isSome then err fnSpan (Fren.Core.appliesUninterpretedMsg path)
      modify fun s => { s with applied := s.applied.push span }
    let acx := if !g.defined && cx.place == .prop then { cx with place := .argument } else cx
    unless args.size == g.declared.size do err span (Fren.Core.arityMsg path g.declared.size args.size)
    let synth ← args.mapM (synthesizes cx)
    let go : StateT (Array String) M (Array Ty) :=
      Fren.Core.inferCall g.params g.declared g.result synth expected?
        (err span (Fren.Core.cannotInferCallMsg (showPath path)) : M Unit)
        (fun k x? => do
          let (smt, t) ← (elabExpr { acx with expected? := Fren.Core.ExprSite.functionArgument.expected x? none } args[k]! : M _)
          modify fun a => a.set! k smt
          return some t)
        (fun k x f => (liftMsg args[k]!.span
          (Fren.Core.checkType x f (some s!"note: argument {k + 1} of `{showPath path}` has type `{x.show}`")) : M Unit))
    let (targs, smts) ← go.run (args.map fun _ => "")
    -- A function of sets of a type that may be finite, at its instance
    -- (`Reqs/Lang/Decidability#sets`).
    if !g.defined then
      let st ← get
      let finiteSet (t : Ty) : Bool := t matches .set _ | .rel .. && !st.infinite t
      let (ps, r) := Fren.Core.instanceSig g.declared g.result targs
      if (ps.push r).any finiteSet then
        checkCore cx span .setFunction true true #[] (infiniteElems := false)
    let ptys := ((← get).funPTys.find? path).map (·.1) |>.getD #[]
    for a in args, x in smts, k in [0:args.size] do
      noteObligation acx .argument a.span (ptys[k]?.getD default) x
    let sym ← instantiate path targs
    modify fun s => { s with genericCalls := s.genericCalls.push (path, targs)
                             genericUses := s.genericUses.push
                               { file := s.file, item := s.item, caller? := s.fnTypeParams.map (·.1), callee := path, targs } }
    notePreconditions cx fnSpan path smts targs
    if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
    let app := s!"({sym} {" ".intercalate smts.toList})"
    -- At least 0, if a `Nat`, its type's constraint, if it brings one, and
    -- meeting its postconditions where its arguments meet its
    -- preconditions, at its instance (`lang::uninterpreted_instance`).
    if !g.defined then
      let posts := (((← get).contracts.find? path).map (·.posts)).getD #[]
      if Fren.Core.instanceNat g.result || !posts.isEmpty || (← get).funFacts.contains sym then
        modify fun s => { s with natApps := s.natApps.push app }
    return (app, Fren.Core.callType g.result targs)
  if let some (_, params, result, _) := (← get).defs.find? (·.1 == path) then
    -- Its arguments may mention anything (`lang::argument`).
    unless args.size == params.size do err span (Fren.Core.arityMsg path params.size args.size)
    let mut smts := #[]
    let ptys := ((← get).funPTys.find? path).map (·.1) |>.getD #[]
    for a in args, (_, t) in params, k in [0:args.size] do
      let (x, ta) ← elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
      liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{showPath path}` has type `{t.show}`"))
      noteObligation cx .argument a.span (ptys[k]?.getD default) x
      smts := smts.push x
    notePreconditions cx fnSpan path smts
    -- Its body's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
    return (s!"({itemSym path} {" ".intercalate smts.toList})", result)
  if cx.inClosure then err fnSpan (Fren.Core.closureUninterpretedMsg path)
  if cx.selfFn.isSome then err fnSpan (Fren.Core.appliesUninterpretedMsg path)
  modify fun s => { s with applied := s.applied.push span }
  let some (_, params, result) := (← get).funs.find? (·.1 == path) | internal fnSpan s!"unknown function `{path}`"
  -- A function of sets of a type that may be finite (`Reqs/Lang/Decidability#sets`).
  let st ← get
  let finiteSet (t : Ty) : Bool := t matches .set _ | .rel .. && !st.infinite t
  if (params.push result).any finiteSet then
    checkCore cx span .setFunction true true #[] (infiniteElems := false)
  unless args.size == params.size do err span (Fren.Core.arityMsg path params.size args.size)
  -- Outputs may not occur in arguments (`inst::mention`); assumptions and
  -- bindings exclude them already.
  let acx := if cx.place == .prop then { cx with place := .argument } else cx
  let mut smts := #[]
  let ptys := (← get).funPTys.find? path
  for a in args, t in params, k in [0:args.size] do
    let (x, ta) ← elabExpr { acx with expected? := Fren.Core.ExprSite.functionArgument.expected (some t) none } a
    liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{showPath path}` has type `{t.show}`"))
    noteObligation acx .argument a.span ((ptys.bind (·.1[k]?)).getD default) x
    smts := smts.push x
  notePreconditions cx fnSpan path smts
  let app := s!"({itemSym path} {" ".intercalate smts.toList})"
  -- At least 0, if a `Nat`, its type's constraint, if it brings one, and
  -- meeting its postconditions where its arguments meet its
  -- preconditions (`Reqs/Lang/Items#uninterpreted-functions`).
  let posts := (((← get).contracts.find? path).map (·.posts)).getD #[]
  if result == .nat || !posts.isEmpty || (← get).funFacts.contains (itemSym path) then
    modify fun s => { s with natApps := s.natApps.push app }
  return (app, result)

/-- A closure, or the name of a function, given for the function parameter
of type `ft`, as its function's signature declares it, of the higher-order
function `f`, whose parameters' types are `ps` where they are known and
whose result's is `r?` if it is known: the closure as the solver sees it,
its parameters' types and its body's (`Reqs/Lang/HigherOrder#arguments`).
The name of a function `g` is the closure `|x1, ..., xn| g(x1, ..., xn)`. -/
partial def elabFnArg (cx : ExprCtx) (f : String) (ft : Fren.Core.FnTy) (ps : Array (Option Ty)) (r? : Option Ty)
    (e : Expr) : M (ClosureArg × Array Ty × Ty) := do
  match e with
  | .matches span #[] arms false =>
    let some types := ps.mapM id | err span (Fren.Core.closureParamUnknownMsg f)
    let names := types.mapIdx fun j _ => ({ name := s!"#match{j}", span } : Ident)
    let values := names.map fun n => Expr.path span #[n]
    let body := if types.size == 1 then Expr.match span values[0]! (arms.map fun (ps, g, b) => (ps[0]!, g, b)) false
      else Expr.matches span values arms false
    for (patterns, _, _) in arms do
      unless patterns.size == types.size do err patterns[0]!.span (Fren.Core.arityMsg `match types.size patterns.size "pattern")
    elabClosure cx (names.zip types) body r? true
  | .closure span params body =>
    if let some msg := Fren.Core.argumentMsg? ft (.closure params.size) then err span msg
    -- `_` declares no name: one that no spec can write or mention.
    let params := params.mapIdx fun k (x, ty?) => if x.name == "_" then ({ x with name := s!"#_{k}" }, ty?) else (x, ty?)
    -- Distinct names (`lang::distinct_names`).
    let declared := params.map fun (x, _) => Name.mkSimple (declaredIdent x).1.name
    if let some k := (Fren.Core.repeatsAt declared)[0]? then err params[k]!.1.span (Fren.Core.dupBoundMsg declared[k]!)
    let named ← params.zip ps |>.mapM fun ((x, ty?), p?) => do
      -- Its written type is the function type's (`lang::function_argument`).
      let t ← match ty?, p? with
        | some segs, some p => do
          let a := (← elabPTy segs).ty
          unless a == p do err (typeSpan segs) (Fren.Core.typeMismatchMsg p a (some s!"note: this parameter of the closure for `{f}` has type `{p.show}`"))
          pure p
        | some segs, none => pure (← elabPTy segs).ty
        | none, some p => pure p
        | none, none => err x.span (Fren.Core.closureParamUnknownMsg f)
      return (x, t)
    lintClosure cx ps r? span params body
    elabClosure cx named body r? false
  | .path span segs =>
    -- The function itself, in its own body, not applied.
    if let some (ps, _, _) := cx.selfRec? then
      if segs.size == 1 && cx.selfFn == some (Name.mkSimple segs[0]!.name) then
        noteRecUse span ((← get).module ++ Name.mkSimple segs[0]!.name) ps { form := .passed }
    -- A function parameter, or a defined function, but not an
    -- uninterpreted one (`lang::function_argument`).
    let isParam := segs.size == 1 && (cx.fnParam? (identName segs[0]!.name)).isSome
    unless isParam do
      let st ← get
      match st.table.resolvePath st.scope (segNames segs) cx.shadowing with
      | .ok (.item { kind := .fnItem, path, .. }) =>
        let shape := if st.defs.any (·.1 == path) || st.hofs.contains path then .definedName else .uninterpretedName
        if let some msg := Fren.Core.argumentMsg? ft shape path then err span msg
      | _ => err span ((Fren.Core.argumentMsg? ft .other).getD default)
    let some tys := ps.mapM id | err span (Fren.Core.closureParamUnknownMsg f)
    let xs := (List.range tys.size).toArray.map fun k => ({ name := s!"#{k}", span } : Ident)
    let call := Expr.app span segs (xs.map fun x => .path span #[x])
    elabClosure cx (xs.zip tys) call r? true
  | _ => err e.span ((Fren.Core.argumentMsg? ft .other).getD default)

/-- The closure whose parameters are `params`, of their types, and whose
body is `body`, of the type `r?` if it is known: its parameters are
declared as a quantifier's bound names are, but not where `synthetic`, as
those of a function's name are. Its body's indexes, tables and
applications with preconditions are its obligations, over its
parameters' symbols, which the application of the higher-order function
puts at each application of the function parameter (`lang::closure_obligation`). -/
partial def elabClosure (cx : ExprCtx) (params : Array (Ident × Ty)) (body : Expr) (r? : Option Ty) (synthetic : Bool) :
    M (ClosureArg × Array Ty × Ty) := do
  let n := (← get).nextClosure
  modify fun s => { s with nextClosure := s.nextClosure + 1 }
  let mut new : Array CBinder := #[]
  let mut free : Array FreeBound := #[]
  for (x, t) in params do
    -- `_`, which declares no name (`elabFnArg`), as a synthetic one.
    let bn ← if synthetic || x.name.startsWith "#_" then pure (Name.mkSimple x.name) else do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        ((cx.binders ++ new).map (·.what)) cx.selfFn.isSome
      let y ← declare x locals
      let bn := Name.mkSimple y.name
      liftMsg y.span (Fren.Core.checkVarName bn (some (t == .bool)))
      lintName .binder bn y.span
      pure bn
    let sym := quote s!"{bn}#{n}"
    let st ← get
    free := free.push { sym, sort := t.sort, cons? := ((Fren.Core.PTy.plain t).cons st.shapeOf true).map (consSmt st.dataOf? · sym) }
    new := new.push { name := bn, smt := sym, ty := t, scrutinee := none, outer := cx.binders.size + new.size, unbounded := true }
  let outer ← takeIndexes
  let outerTables ← takeTables
  let site : Fren.Core.ExprSite := if r?.isSome then .typedClosureBody else .untypedClosureBody
  let (b, tb) ← elabExpr { cx with binders := cx.binders ++ new, expected? := site.expected r? none, inClosure := true } body
  let inner ← takeIndexes
  let innerTables ← takeTables
  modify fun s => { s with indexes := outer, tables := outerTables }
  let _ := free
  return ({ closure := { params := new.toList.map (·.smt), body := Fren.Core.STerm.parse b }, indexes := inner
            tables := innerTables }, new.map (·.ty), tb)

/-- `elabExpr` on an application of the higher-order function `h` at
`path` (`Reqs/Lang/HigherOrder#applications`): its body, unfolded at its
arguments, each closure unfolded within it (`Fren.Core.inlineCall`), and
its preconditions so too. -/
partial def elabHigherOrderApp (cx : ExprCtx) (expected? : Option Ty) (span fnSpan : Span) (path : Name)
    (h : HigherOrderFn) (args : Array Expr) : M (String × Ty) := do
  unless args.size == h.params.size do err span (Fren.Core.arityMsg path h.params.size args.size)
  let synth ← args.mapM (synthesizes cx)
  let f := showPath path
  let go : StateT (Array String × Array (Option ClosureArg)) M (Array Ty) :=
    Fren.Core.inferHigherOrder h.typeParams (h.params.map (·.2.2)) h.result synth expected?
      (err span (Fren.Core.cannotInferCallMsg f) : M Unit)
      (fun k x? => do
        let (smt, t) ← (elabExpr { cx with expected? := Fren.Core.ExprSite.functionArgument.expected x? none } args[k]! : M _)
        modify fun (a, c) => (a.set! k smt, c)
        return some t)
      (fun k x t => (liftMsg args[k]!.span
        (Fren.Core.checkType x t (some s!"note: argument {k + 1} of `{f}` has type `{x.show}`")) : M Unit))
      (fun k ps r? => do
        let .function ft := h.params[k]!.2.2 | return none
        let (c, pts, rt) ← (elabFnArg cx f ft ps r? args[k]! : M _)
        noteFnArg path k args[k]!
        modify fun (a, cs) => (a, cs.set! k (some c))
        return some (pts, rt))
      (fun k ft (_, rt) => (liftMsg args[k]!.span
        (Fren.Core.checkType ft.result rt (some s!"note: the closure for argument {k + 1} of `{f}` returns `{ft.result.show}`")) : M Unit))
  let (targs, smts, closures) ← do
    let (targs, (smts, closures)) ← go.run (args.map fun _ => "", args.map fun _ => none)
    pure (targs, smts, closures)
  let ptys := ((← get).funPTys.find? path).map (·.1) |>.getD #[]
  for a in args, x in smts, k in [0:args.size] do
    if h.params[k]!.2.2 matches .value _ then noteObligation cx .argument a.span (ptys[k]?.getD default) x
  let values := (h.params.zip smts).toList.filterMap fun ((_, sym, p), x) => if p matches .value _ then some (sym, x) else none
  let fns := (h.params.zip closures).toList.filterMap fun ((_, sym, _), c?) => c?.map (sym, ·.closure)
  let globals ← globalSyms
  let isLocal (s : String) : Bool := (s.startsWith "|" || s.startsWith "let@") && !globals.contains s
  -- Its preconditions, at the arguments, with the closures unfolded.
  if cx.noteIndexes then
    let mut pres := #[]
    for (pn, text) in h.pres do
      let (pre, next) := Fren.Core.inlineCall (← hofText path h targs text) values fns isLocal (← get).nextCapture
      modify fun s => { s with nextCapture := next }
      pres := pres.push (pn, pre)
    for (q, goal) in Fren.Core.preconditionQuestions (guarded cx.guards) path pres do
      modify fun s => { s with tables := s.tables.push (fnSpan, q, goal) }
  let body ← hofText path h targs h.body
  -- Each closure's obligations, at each application of its function
  -- parameter in the body, with the other closures unfolded there
  -- (`lang::closure_obligation`).
  if cx.noteIndexes then
    for (fsym, c?) in (h.params.map (·.2.1)).zip closures do
      let some c := c? | continue
      let others := fns.filter (·.1 != fsym)
      let at_ (g : String) : M (Option String) := do
        let (b, next) := Fren.Core.inlineCall body [] others isLocal (← get).nextCapture
        modify fun s => { s with nextCapture := next }
        -- Its free names, as the closure's, are captured outside the body.
        let (g', lets, next) := Fren.Core.captureFree (Fren.Core.STerm.parse g) c.closure.params isLocal (← get).nextCapture
        modify fun s => { s with nextCapture := next }
        -- Where the body never applies it, the closure is never evaluated.
        let o := (Fren.Core.closureObligation (Fren.Core.STerm.parse b) fsym c.closure.params g').getD (.atom "true")
        -- With the closure unfolded where the arguments and the guards
        -- apply it too, and the other parameters at their arguments.
        let (t, next) := Fren.Core.inlineCall o.print values [(fsym, c.closure)] isLocal (← get).nextCapture
        modify fun s => { s with nextCapture := next }
        if lets.isEmpty then return some t
        return some s!"(let ({" ".intercalate (lets.map fun (x, v) => s!"({x} {v})")}) {t})"
      for (sp, g, t) in c.indexes do
        if let some o ← at_ g then modify fun s => { s with indexes := s.indexes.push (sp, o, t), vias := s.vias.push (sp, path) }
      for (sp, q, g) in c.tables do
        if let some o ← at_ g then modify fun s => { s with tables := s.tables.push (sp, q, o), vias := s.vias.push (sp, path) }
  let (smt, next) := Fren.Core.inlineCall body values fns isLocal (← get).nextCapture
  modify fun s => { s with nextCapture := next }
  if (← get).guardedItems.contains path then modify fun s => { s with guardedUsed := true }
  return (smt, h.result.subst targs)

/-- `elabExpr` on a field read. -/
partial def elabFieldExpr (cx : ExprCtx) (e : Expr) (parent? : Option Expr) (span : Span) (a : Expr) (f : Ident) : M (String × Ty) := do
  let src := (← get).src
  -- Where `e` is, as `lang::operand` sees it.
  let slot := parent?.bind (Expr.operandSlot src · e)
  let lintChain := exprLintChain cx e parent? src slot
  lintChain
  let (x, t) ← elabExpr { cx with concatOk := true } a
  if t == .string then checkCore cx span .stringAtom true true #[a]
  if let some tys := relRange? t f.name then checkRelational cx span tys #[a]
  checkRelationalCard cx span t f.name a
  if let (.seq _, some m) := (t, Fren.Core.Method.ofName? f.name) then
    checkCore cx span m.seqConstruct true true #[a] (← isConstant cx a)
  -- For `redundant_newtype_roundtrip`, at its span as written, as the
  -- lints see it (`Expr.boolNode`).
  if let (.newtype p _, "0", true) := (t, f.name, cx.noteIndexes) then
    modify fun s => { s with facts := s.facts.push (e.writtenSpan s.src, .unwraps p.toString) }
  readField f.span x t (Name.mkSimple f.name)

/-- `elabExpr` on a record literal. -/
partial def elabRecordExpr (cx : ExprCtx) (expected? : Option Ty) (span : Span) (tySegs : Array Ident) (fields : Array (Ident × Option Expr)) : M (String × Ty) := do
  let src := (← get).src
  let tySpan := tySegs[0]!.span.to tySegs.back!.span
  let path ← match ← resolveWritten tySegs cx.shadowing cx.noteIndexes with
    | .item { kind := .recordItem, path, .. } => pure path
    | r => err tySpan (Fren.Core.wrongKindMsg "a record" r)
  if (← get).newtypes.contains path then err tySpan (Fren.Core.constructionMsg path true)
  let some d := (← get).dataOf? path | internal tySpan s!"unknown record `{path}`"
  let fs := d.ctors[0]!.2
  match Fren.Core.checkFieldInits path (fs.map (·.1)) (fields.map (Name.mkSimple ·.1.name)) with
  | .ok () => pure ()
  | .error (some i, msg) => err fields[i]!.1.span msg
  | .error (none, msg) => err span msg
  -- `inconsistent_struct_constructor` (`lint::inconsistent_struct_constructor`).
  if cx.noteIndexes then
    let src := (← get).src
    let ranges := fields.map fun (f, e?) =>
      ({ start := f.span.start, stop := (e?.map fun e => (Fren.Core.withParens src (toRange e.span)).stop).getD f.span.stop } : Fren.Core.Range)
    if let some fixed? := Fren.Core.reorderedFields? src (toRange span) ranges (fields.map (Name.mkSimple ·.1.name)) (fs.map (·.1)) then
      lintFix .inconsistentStructConstructor span
        (Fren.Core.inconsistentStructConstructorMsg (Name.mkSimple path.getString!) (fs.map (·.1)) fixed?)
  let mut smts := #[]
  let mut vals := #[]
  for (f, _) in fs do
    let some (fi, e?) := fields.find? (Name.mkSimple ·.1.name == f) | internal span s!"no field `{f}`"
    if let (some e, true) := (e?, cx.noteIndexes) then lintRedundant fi e true
    vals := vals.push (e?.getD (.path fi.span #[fi]))
  let note (k : Nat) (t : Ty) := s!"note: `{fs[k]!.1}` of `{showPath path}` has type `{t.show}`"
  let mut targs := #[]
  if d.params.isEmpty then
    for (_, t) in fs, e in vals, k in [0:fs.size] do
      let (x, te) ← elabExpr { cx with expected? := Fren.Core.ExprSite.recordField.expected (some t) none } e
      liftMsg e.span (Fren.Core.checkType t te (some (note k t)))
      noteObligation cx .field e.span (← partPTy path 0 k) x
      smts := smts.push x
  else
    (smts, targs) ← elabConstruction elabExpr .recordField { cx with expected? } d (fs.map (·.2)) vals span (showPath path) note
    -- Each field's obligation, of its type with the record's arguments.
    for e in vals, x in smts, k in [0:fs.size] do
      noteObligation cx .field e.span (← partPTy path 0 k targs) x
  -- `unnecessary_struct_initialization`
  -- (`lint::unnecessary_struct_initialization`): each field's value as
  -- `r.f`, its own field `f` of `r`, with `r`'s text.
  if cx.noteIndexes then
    let src := (← get).src
    let reads := fields.filterMap fun (f, e?) => do
      match ← e? with
      | .path sp #[seg] =>
        let parts := seg.name.splitOn "."
        guard (parts.length ≥ 2 && parts.getLast! == f.name)
        let r := ".".intercalate parts.dropLast
        some (Expr.path { sp with stop := sp.start + r.length } #[{ name := r, span := { sp with stop := sp.start + r.length } }], r)
      | .field _ r g =>
        guard (g.name == f.name)
        some (r, Fren.Core.textOf src (Fren.Core.withParens src (toRange (r.writtenSpan src))))
      | _ => none
    if let some (r, t) := reads[0]? then
      let same := reads.all (Fren.Core.writtenSame ·.2 t)
      -- A value has a type; a call is not one.
      let ty? := match (elabExpr { cx with noteIndexes := false } r).run (← get) with
        | .ok ((_, ty), _) => some ty
        | .error _ => none
      if Fren.Core.unnecessaryStructInit fields.size (reads.size == fields.size) same ty?.isSome (ty? == some (.record path targs.toList)) then
        lintFix .unnecessaryStructInitialization span (Fren.Core.unnecessaryStructInitMsg t)
  if cx.noteIndexes then
    -- `manual_record_update` (`lint::manual_record_update`): the fields that
    -- read their own field from a value of this record, by the value's text.
    let mut copies : Array (String × Span × Array Nat) := #[]
    for h : i in [0:fields.size] do
      let (fi, e?) := fields[i]
      let some (recv, n) := e?.bind lastName? | continue
      unless n == fi.name do continue
      -- Only its type: what elaborating it reports is reported where it is.
      let saved ← get
      let t? ← tryCatch (some <$> (·.2) <$> elabExpr { cx with noteIndexes := false, expected? := Fren.Core.ExprSite.receiver.expected none none } recv)
        fun _ => pure none
      set saved
      unless t? == some (Ty.record path targs.toList) do continue
      let w := Fren.Core.writtenForm (← srcAt recv.span)
      match copies.findIdx? (·.1 == w) with
      | some k => copies := copies.modify k fun (w, s, ks) => (w, s, ks.push i)
      | none => copies := copies.push (w, recv.span, #[i])
    -- The value with the most copies, the first of those with as many.
    let best? := copies.foldl (init := none) fun acc c =>
      if acc.all (·.2.2.size < c.2.2.size) then some c else acc
    if let some (_, rs, ks) := best? then
      if Fren.Core.manualRecordUpdate fs.size ks.size then
        let kept ← ((Array.range fields.size).filter (!ks.contains ·)).mapM fun i =>
          let (fi, e?) := fields[i]!
          srcAt ((e?.map (fi.span.to ·.span)).getD fi.span)
        lintFix .manualRecordUpdate span (Fren.Core.manualRecordUpdateMsg (← srcAt rs) ks.size kept)
  return (d.build targs.toList `«{}» smts.toList, .record path targs.toList)

/-- `elabExpr` on a record update. -/
partial def elabUpdateExpr (cx : ExprCtx) (span : Span) (base : Expr) (fields : Array (Ident × Option Expr)) : M (String × Ty) := do
  let (rv, tr) ← elabExpr { cx with expected? := Fren.Core.ExprSite.updatedRecord.expected none none } base
  let .record path targs := tr | err base.span (Fren.Core.updateBaseMsg tr.show)
  let some d := (← get).dataOf? path | internal base.span s!"unknown record `{path}`"
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let fs := (d.instCtors targs)[0]!.2
  match Fren.Core.checkFieldUpdates path (fs.map (·.1)) (fields.map (Name.mkSimple ·.1.name)) with
  | .ok () => pure ()
  | .error (i, msg) => err fields[i]!.1.span msg
  -- The record literal whose other fields are read from `r`, bound once,
  -- so that nested updates grow linearly. No variable's name has `@`.
  let bind := fs.size > fields.size && rv.contains ' '
  let r := if bind then quote s!"update@{span.start}" else rv
  let mut smts := #[]
  for (f, t) in fs, k in [0:fs.size] do
    let some (fi, e?) := fields.find? (Name.mkSimple ·.1.name == f)
      | smts := smts.push s!"({fieldSym path f} {r})"; continue
    let e := e?.getD (.path fi.span #[fi])
    let (x, te) ← elabExpr { cx with expected? := Fren.Core.ExprSite.recordField.expected (some t) none } e
    liftMsg e.span (Fren.Core.checkType t te (some s!"note: `{f}` of `{showPath path}` has type `{t.show}`"))
    noteObligation cx .field e.span (← partPTy path 0 k targs.toArray) x
    smts := smts.push x
  if cx.noteIndexes then
    if Fren.Core.needlessUpdate fs.size fields.size then
      lint .needlessUpdate span (Fren.Core.needlessUpdateMsg (showPath path) (← srcAt base.span))
    -- `redundant_bindings` on each field (`lint::redundant_bindings`, `lint::field_copy`).
    let baseText := Fren.Core.writtenForm (← srcAt base.span)
    let values ← fields.mapM fun (_, e?) => e?.mapM fun e => do pure (Fren.Core.writtenForm (← srcAt e.span))
    let copy (i : Nat) : Bool := Fren.Core.fieldCopy fields[i]!.1.name ((values[i]!).getD "") baseText true
    let others := (Array.range fields.size).any (!copy ·)
    let stop (i : Nat) : Nat := let (fi, e?) := fields[i]!; ((e?.map (·.span.stop)).getD fi.span.stop)
    for h : i in [0:fields.size] do
      let (fi, e?) := fields[i]
      let some e := e? | continue
      lintRedundant fi e true
      if Fren.Core.fieldCopy fi.name ((values[i]!).getD "") baseText others then
        -- The field and the comma before it, or for the first, the comma after it.
        let r : Fren.Core.Range := if i == 0 then { start := fi.span.start, stop := fields[1]!.1.span.start }
          else { start := stop (i - 1), stop := e.span.stop }
        lintEdits .redundantBindings (fi.span.to e.span) (Fren.Core.fieldCopyMsg fi.name (← srcAt base.span)) #[(r, "")]
  let lit := d.build targs `«{}» smts.toList
  return (if bind then s!"(let (({r} {rv})) {lit})" else lit, .record path targs)

/-- `elabExpr` on a `match`. -/
partial def elabMatchExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (span : Span) (scrutinee : Expr) (arms : Array (Pattern × Option Expr × Expr)) (isTable : Bool)
    (many? : Option (Array Expr × Array (Array Pattern)) := none) : M (String × Ty) := do
  let scrutinees := many?.map (·.1) |>.getD #[scrutinee]
  let patterns := many?.map (·.2) |>.getD (arms.map fun a => #[a.1])
  for ps in patterns, arm in arms do
    unless ps.size == scrutinees.size do err arm.1.span (Fren.Core.arityMsg `match scrutinees.size ps.size "pattern")
  let origin? := scrutinees.findSome? cx.recOrigin?
  let values ← scrutinees.mapM (elabExpr cx)
  for scr in scrutinees, (_, ts) in values do
    unless ts matches .enum .. | .bool | .int | .nat | .string do err scr.span (Fren.Core.scrutineeMsg ts.show)
  let ts := values[0]!.2
  let mut resolved := #[]
  let mut rows := #[]
  for ps in patterns do
    let parts ← ps.zipIdx |>.mapM fun (p, j) => do
      let (q, bs, test) ← resolvePattern cx values[j]!.2 values[j]!.1 false false p
      return (q, bs.map fun b => { b with source? := some scrutinees[j]! }, test)
    rows := rows.push (parts.map (·.1))
    resolved := resolved.push (parts[0]!.1, parts.flatMap (·.2.1), Fren.Core.allOf? andSmt (parts.filterMap (·.2.2)))
  let baseSigs ← patSigs
  let (sigs, pty, pats) := if many?.isSome then Fren.Core.matchVector baseSigs (values.map (·.2.patTy)) rows
    else (baseSigs, ts.patTy, rows.map (·[0]!))
  let usesBefore := (← get).recUses.size
  let guarded := arms.map (·.2.1.isSome)
  -- In a table over a scrutinee, only the last arm may be `_` without a
  -- guard, the otherwise (`Reqs/Lang/Expressions#tables-over-a-scrutinee`).
  if isTable then
    if let some k := Fren.Core.rowAfterWild? ((pats.zip guarded).map fun (p, g) => p matches .wild false && !g) then
      err arms[k]!.1.span Fren.Core.armAfterWildMsg
  let checked := if isTable then Fren.Core.checkTableArms sigs pty pats guarded
    else (Fren.Core.checkMatch sigs pty pats guarded).map (·, #[])
  let (unguardedExhaustive, pairs) ← match checked with
    | .ok u => pure u
    | .error (some (i, some j), msg) => err (patterns[i]!.flatMap Pattern.alternatives)[j]!.span (if many?.isSome then Fren.Core.vectorMsg msg else msg)
    | .error (some (i, none), msg) => err arms[i]!.1.span (if many?.isSome then Fren.Core.vectorMsg msg else msg)
    | .error (none, msg) => err span (if many?.isSome then Fren.Core.vectorMsg msg else msg)
  let implicitArg := match scrutinee with | .path _ #[n] => n.name.startsWith "#match" | _ => false
  if cx.noteIndexes && many?.isNone && !implicitArg then
    lintMatch cx e ts pats (parent?.bind (Expr.operandSlot (← get).src · e))
    lintCouldBeTable e sigs pty pats
    lintGuards cx e sigs pty pats
    lintArmIfElse cx e sigs pty pats
  let mut bodies : Array String := #[]
  let mut ty? : Option Ty := none
  let mut waiting : Array (Nat × ExprCtx × Expr) := #[]
  -- Where each arm is taken, if no earlier one is: its test and its
  -- guard; `none` for an arm taken wherever it is tried.
  let mut taken : Array (Option String) := #[]
  -- Of a table over a scrutinee, that the indexes in each arm's guard are
  -- in range where it evaluates them, if it has any.
  let mut defined : Array (Option String) := #[]
  -- An arm's guard is guarded by its pattern's matching where no earlier
  -- arm is taken (`Fren.Core.GuardedOperand.armGuard`), and its body by
  -- its being the first arm taken (`Fren.Core.GuardedOperand.armBody`).
  -- They are built directly: their negations are never needed, so
  -- `guard` would only return them.
  for (_, guard?, body) in arms, (_, bs, test) in resolved do
    let before := cx.guards ++ taken.filterMap (·.map (s!"(not {·})"))
    let armGuards := before ++ test.toArray
    -- Distinct names (`lang::distinct_names`), by the names they declare,
    -- without the `!` of shadowing.
    let declared := bs.map fun b => Name.mkSimple (declaredIdent b.ident).1.name
    if let some k := (Fren.Core.repeatsAt declared)[0]? then
      err bs[k]!.ident.span (Fren.Core.dupPatternBinderMsg declared[k]!)
    let mut new : Array CBinder := #[]
    for b in bs do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let x ← declare b.ident locals
      let bn := Name.mkSimple x.name
      liftMsg x.span (Fren.Core.checkVarName bn (some (b.ty == .bool)))
      lintName .binder bn x.span
      -- A payload of a parameter, or of a binder bound from one, is bound
      -- from a payload of that parameter; so is the whole of such a binder.
      let source := b.source?.getD scrutinee
      let payloadOf? := cx.recOrigin? source |>.bind fun (j, p) => if b.payload || p then some j else none
      new := new.push { name := bn, smt := b.smt, ty := b.ty, scrutinee := some source, outer := cx.binders.size, payloadOf? }
    let gcx := { cx with binders := cx.binders ++ new, guards := armGuards }
    -- The guard, a `Bool`, checked as one (`Reqs/Lang/Expressions#matches`).
    let guardOf (g : Expr) : M (String × Option String) := do
      if !isTable then
        let (x, tg) ← elabExpr { gcx with expected? := Fren.Core.ExprSite.armGuard.expected none none } g
        liftMsg g.span (Fren.Core.checkType .bool tg (some Fren.Core.armGuardNote))
        return (x, none)
      -- In a table over a scrutinee, elaborated under its pattern's test
      -- alone, so that its indexes say where it defines them, for its
      -- disjointness; then they, and the questions about its tables, are
      -- put under the earlier arms' not being taken, as a row's
      -- condition is.
      let (k, kt) := ((← get).indexes.size, (← get).tables.size)
      let (x, tg) ← elabExpr { gcx with expected? := Fren.Core.ExprSite.armGuard.expected none none, guards := test.toArray } g
      liftMsg g.span (Fren.Core.checkType .bool tg (some Fren.Core.armGuardNote))
      let inGuard := (← get).indexes.extract k
      modify fun s => { s with
        indexes := s.indexes.extract 0 k ++ inGuard.map (fun (sp, f, t) => (sp, FrenCli.guarded before f, t)),
        tables := s.tables.extract 0 kt ++ (s.tables.extract kt).map fun (sp, q, f) => (sp, q, FrenCli.guarded before f) }
      return (x, Fren.Core.allOf? andSmt (inGuard.map (·.2.1)))
    let (g?, d?) ← match guard? with
      | some g => do let (x, d?) ← guardOf g; pure (some x, d?)
      | none => pure (none, none)
    defined := defined.push d?
    let own := (test.toArray ++ g?.toArray)
    taken := taken.push (Fren.Core.allOf? andSmt own)
    -- Each body is checked against the whole's type, or another's
    -- (`lang::checked`): one that does not synthesize its own, before any
    -- other has given a type, waits for a later one that does.
    let bcx := { gcx with guards := armGuards ++ g?.toArray }
    -- Another arm's `Nat` is widened: a `Nat` is expected only of the whole.
    -- The whole's type comes before the arms' (`ExprSite.wholeFirst`).
    let shared? := Fren.Core.ExprSite.armBody.expected expected? ty?
    if shared?.isNone && !(← synthesizes cx body) && (← arms.anyM (synthesizes cx ·.2.2)) then
      waiting := waiting.push (bodies.size, bcx, body)
      bodies := bodies.push ""
      continue
    let (x, t) ← elabExpr { bcx with expected? := shared? } body
    ty? := some (← liftMsg body.span (Fren.Core.checkArm ty? t))
    bodies := bodies.push x
  for (k, bcx, body) in waiting do
    let (x, t) ← elabExpr { bcx with expected? := Fren.Core.ExprSite.armBody.expected expected? ty? } body
    if ty?.isSome then ty? := some (← liftMsg body.span (Fren.Core.checkArm ty? t))
    bodies := bodies.set! k x
  let ty := ty?.get!
  noteMatch cx span (arms.map (·.1.span)) taken guarded unguardedExhaustive (if isTable then some pairs else none) defined
  -- A recursive application under a `match` on an enumeration's parameter
  -- or payload that is not a Lean `match` (`lang::recursive_match`).
  if origin?.isSome && values.any (fun (_, t) => t matches .enum ..) then
    let nonLean? := if many?.isSome then (rows.zipIdx.find? fun (ps, j) => ps.any (!·.leanPattern) || guarded[j]!).map (·.2)
      else Fren.Core.firstNonLeanPattern? pats guarded
    if let some k := nonLean? then
      if (← get).recUses.size > usesBefore then
        modify fun s => { s with recMatches := s.recMatches.push arms[k]!.1.span }
  -- The first arm that is taken. Where the arms without guards are
  -- exhaustive, the last arm has none, and takes whatever is left;
  -- otherwise, where none is taken, the `match` is unspecified, as a
  -- table where no row holds is.
  let complete := !Fren.Core.completenessAsked unguardedExhaustive
  let mut out := if complete then bodies.back! else unspecified ty
  if !complete then modify fun s => { s with usesSeqs := true }
  for i in (List.range (if complete then bodies.size - 1 else bodies.size)).reverse do
    if let some t := taken[i]! then
      out := s!"(ite {t} {bodies[i]!} {out})"
    else
      out := bodies[i]!
  return (out, ty)

/-- `elabExpr` on a table. -/
partial def elabTableExpr (cx : ExprCtx) (e : Expr) (expected? : Option Ty) (parent? : Option Expr) (span : Span)
    (rows : Array (Span × Option Expr × Expr)) : M (String × Ty) := do
  -- Only the last row may be `_` (`Reqs/Lang/Expressions#tables`).
  if let some k := Fren.Core.rowAfterWild? (rows.map (·.2.1.isNone)) then err rows[k]!.1 Fren.Core.rowAfterWildMsg
  let wild := rows.back!.2.1.isNone
  -- Each row's condition, other than `_`'s, and value.
  let mut conds : Array String := #[]
  let mut defined : Array (Option String) := #[]
  let mut values : Array String := #[]
  let mut ty? : Option Ty := none
  let mut waiting : Array (Nat × ExprCtx × Expr) := #[]
  for (_, c?, v) in rows do
    -- A row's condition is guarded by the earlier rows' not holding, and
    -- its value by its own holding too (`lang::guard`).
    let before := cx.guards ++ Fren.Core.earlierFail (s!"(not {·})") conds conds.size
    let mut own := #[]
    if let some c := c? then
      -- Elaborated under its own guards alone, so that its indexes say
      -- where it defines them; then they, and the questions about its
      -- tables, are put under the guards around it.
      let (k, kt) := ((← get).indexes.size, (← get).tables.size)
      let (x, tc) ← elabExpr { cx with guards := #[] } c
      liftMsg c.span (Fren.Core.checkType .bool tc (some Fren.Core.rowConditionNote))
      let inCond := (← get).indexes.extract k
      modify fun s => { s with
        indexes := s.indexes.extract 0 k ++ inCond.map (fun (sp, g, t) => (sp, guarded before g, t)),
        tables := s.tables.extract 0 kt ++ (s.tables.extract kt).map fun (sp, q, g) => (sp, q, guarded before g) }
      conds := conds.push x
      defined := defined.push (Fren.Core.allOf? andSmt (inCond.map (·.2.1)))
      own := #[x]
    -- Each value is checked against the whole's type, or another's
    -- (`lang::checked`), as a `match` arm's body is.
    let vcx := { cx with guards := before ++ own }
    let shared? := Fren.Core.ExprSite.rowValue.expected expected? ty?
    if shared?.isNone && !(← synthesizes cx v) && (← rows.anyM (synthesizes cx ·.2.2)) then
      waiting := waiting.push (values.size, vcx, v)
      values := values.push ""
      continue
    let (x, t) ← elabExpr { vcx with expected? := shared? } v
    if let some t0 := ty? then
      liftMsg v.span (Fren.Core.checkRowType t0 t)
    ty? := some ((ty?.map (·.join t)).getD t)
    values := values.push x
  for (k, vcx, v) in waiting do
    let (x, t) ← elabExpr { vcx with expected? := Fren.Core.ExprSite.rowValue.expected expected? ty? } v
    if let some t0 := ty? then
      liftMsg v.span (Fren.Core.checkRowType t0 t)
    ty? := ty?.map (·.join t)
    values := values.set! k x
  -- Each row's condition, or its `_`, which is last.
  noteTable cx span (rows.map fun (st, c?, _) => (c?.map (·.span)).getD st) conds defined wild
  -- `same_branches` on a table (`lint::same_rows`).
  if cx.noteIndexes then
    let src := (← get).src
    let v := rows[0]!.2.2
    let first := (v.text src).text
    let (fires, _) := Fren.Core.sameRows rows.size (rows.all fun r => Fren.Core.writtenSame (r.2.2.text src).text first) wild
    if fires then
      let fixed := (v.text src).inSlot (parent?.bind (Expr.operandSlot src · e)) (← followedSpan span)
      lintFix .sameBranches span (Fren.Core.sameRowsMsg first fixed wild)
  let ty := ty?.get!
  -- The first row whose condition holds; with no `_` row, where none
  -- does, the table is unspecified, as an index out of range is.
  let mut out := if wild then values.back! else
    s!"(ite {conds.back!} {values.back!} {unspecified ty})"
  if !wild then modify fun s => { s with usesSeqs := true }
  for i in (List.range (values.size - 1)).reverse do
    out := s!"(ite {conds[i]!} {values[i]!} {out})"
  return (out, ty)

/-- `elabExpr` on a pattern test `is`, an operand of a chain of `and` that
is a part of `test.1`, at the position and of the size that `test.2` gives,
if it is a chain of more than one. -/
partial def elabIsExpr (cx : ExprCtx) (test : Fren.Core.TestContext × Option (Nat × Nat)) (span : Span)
    (scrutinee : Expr) (p : Pattern) : M (String × Ty) := do
  let (s, ts) ← elabExpr cx scrutinee
  unless ts matches .enum .. | .bool | .int | .nat | .string do
    let shorthand := match scrutinee with
      | .path _ #[b] => b.name == Fren.Core.shorthandBinder
      | _ => false
    err scrutinee.span (Fren.Core.isScrutineeMsg ts.show shorthand)
  -- Whether the names that it binds are in scope anywhere (`lang::test_scope`):
  -- then its or-patterns bind none, as a `match` arm's do.
  let (context, at?) := test
  let (k, n) := at?.getD (0, 1)
  let binds := Fren.Core.testBinds context k n
  let (q, bs, smt) ← resolvePattern cx ts s false (!binds) p
  match Fren.Core.checkPatternTest (← patSigs) ts.patTy q (bs.map (Name.mkSimple ·.ident.name)) binds context with
  | .ok () => pure ()
  | .error (.binder k, msg) => err bs[k]!.ident.span msg
  | .error (.alternative j, msg) => err p.alternatives[j]!.span msg
  | .error (.whole, msg) => err p.span msg
  if cx.noteIndexes && !bs.isEmpty then modify fun s => { s with bindingTests := s.bindingTests.push span }
  if binds && !bs.isEmpty then
    -- Declared as a `match` arm's binders are, for the later operands of the
    -- chain and the body that sees them.
    let declared := bs.map fun b => Name.mkSimple (declaredIdent b.ident).1.name
    if let some k := (Fren.Core.repeatsAt declared)[0]? then
      err bs[k]!.ident.span (Fren.Core.dupPatternBinderMsg declared[k]!)
    let mut new : Array CBinder := #[]
    for b in bs do
      let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
        (cx.binders.map (·.what)) cx.selfFn.isSome
      let x ← declare b.ident locals
      let bn := Name.mkSimple x.name
      liftMsg x.span (Fren.Core.checkVarName bn (some (b.ty == .bool)))
      if cx.noteIndexes then lintName .binder bn x.span
      new := new.push { name := bn, smt := b.smt, ty := b.ty, scrutinee := some scrutinee, outer := cx.binders.size }
    modify fun s => { s with bound := s.bound ++ new }
  if cx.noteIndexes then
    -- `irrefutable_is` and `is_equality` (`lint::irrefutable_is`, `lint::is_equality`):
    -- not of a test that binds names, which it is needed for.
    let irrefutable := bs.isEmpty && Fren.Core.irrefutableIs (Fren.Core.matchesEvery (← patSigs) ts.patTy q)
    if irrefutable then lint .irrefutableIs span (Fren.Core.irrefutableIsMsg ts.show (q matches .wild _))
    lintOrPatterns (patNode (← get).src p q)
    let texts ← p.alts.mapM (srcAt ·.span)
    -- Not of the pattern shorthand's test, whose scrutinee is not written,
    -- and which has no form with `=` (`Reqs/Lang/SubsetTypes#the-pattern-shorthand`).
    let generated := match scrutinee with | .path _ #[x] => Fren.Core.generatedName x.name | _ => false
    if !generated && Fren.Core.isEquality texts.size (Fren.Core.equatable q texts) irrefutable then
      lintFix .isEquality span (Fren.Core.isEqualityMsg (scrutinee.text (← get).src) texts[0]!)
  return (smt.getD "true", .bool)

/-- `elabExpr` on a `let` or `where`. -/
partial def elabLetExpr (cx : ExprCtx) (span : Span) (concatOk : Bool) (expected? : Option Ty) (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) (isWhere : Bool) : M (String × Ty) := do
  let appMark := (← get).natApps.size
  let (bcx, binds) ← elabDefinitions cx defs (!isWhere) (usedDefinitions defs body)
  let mark := (← get).indexes.size
  let tableMark := (← get).tables.size
  -- A body that is a membership right after the `in` may have been meant
  -- as part of the last definition, which `in` ended.
  let lastStop := (defs.back?.map (·.2.2.span.stop)).getD body.span.start
  let between := ((Fren.Core.withoutComments (← srcAt { start := lastStop, stop := body.span.start })).toList.filter
    fun c => !c.isWhitespace && c != ')')
  let membership := !isWhere && between == "in".toList && body matches .bin _ "in" ..
  let (b, t) ← tryCatch (elabExpr { bcx with expected? := Fren.Core.ExprSite.letBody.expected expected? none, concatOk } body) fun f =>
    -- The error just thrown is the last.
    throw (if membership then { f with diags := f.diags.modify (f.diags.size - 1) fun d =>
      { d with msg := Fren.Core.membershipNote true d.msg } } else f)
  -- The indexes of the body, and of the names it mentions, are within the
  -- `let`s.
  modify fun s => { s with
    indexes := s.indexes.extract 0 mark ++ (s.indexes.extract mark s.indexes.size).map fun (sp, g, t) => (sp, wrapLets binds g, t),
    tables := s.tables.extract 0 tableMark ++
      (s.tables.extract tableMark s.tables.size).map fun (sp, q, g) => (sp, q, wrapLets binds g) }
  -- So are the applications of `Nat` functions of its definitions and body,
  -- which are asserted to be at least 0 outside it.
  modify fun s => { s with natApps := s.natApps.extract 0 appMark ++
    (s.natApps.extract appMark s.natApps.size).map (wrapLets binds) }
  -- Not of what a function's block lowers to, whose definitions are
  -- written outside it (`Reqs/Lang/Items#function-blocks`).
  let lowered := defs.any fun (x, _, _) => x.span.start < span.start || x.span.stop > span.stop
  if cx.noteIndexes && !lowered then lintClause span defs body isWhere
  return (wrapLets binds b, t)

/-- Elaborates the definitions of a `let` (`inLet`) or `where` clause, in
order, each in the scope of the earlier ones (`Reqs/Lang/Let`), and those
that its body does not mention (`used`) without the rules on mentions: the
context of its body, and each name's SMT-LIB symbol and definition. -/
partial def elabDefinitions (cx : ExprCtx) (defs : Array (Ident × Option (Array Ident) × Expr)) (inLet : Bool)
    (used : Array Bool) : M (ExprCtx × Array (String × String)) := do
  let mut cx := cx
  let mut binds := #[]
  for (x, ty?, e) in defs, k in [0:defs.size] do
    let locals := Fren.Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
      (cx.binders.map (·.what)) cx.selfFn.isSome
    let y ← declare x locals
    let n := Name.mkSimple y.name
    -- This name and the later ones that hide nothing are not in scope yet.
    let pending := (defs.extract k defs.size).toList.zipIdx.filterMap fun ((z, _, _), j) =>
      let (d, bang) := declaredIdent z
      if bang then none else some (Name.mkSimple d.name, j == 0)
    let pannot? ← ty?.mapM elabPTy
    let annot? := pannot?.map (·.ty)
    -- Its indexes are guarded where the name is mentioned, and so is its
    -- written type's obligation (`Reqs/Lang/Let#definitions`).
    let before := (← get).indexes
    let beforeTables := (← get).tables
    modify fun s => { s with indexes := #[], tables := #[] }
    let site : Fren.Core.ExprSite := if annot?.isSome then .typedDefinition else .untypedDefinition
    let dcx := { cx with guards := #[], pending := pending.toArray, expected? := site.expected annot? none
                         unmentioned := cx.unmentioned || !used[k]! }
    let (smt, t) ← elabExpr dcx e
    if let some a := pannot? then noteObligation dcx .letDefinition e.span a smt
    let obligations := (← get).indexes
    let tableObligations := (← get).tables
    modify fun s => { s with indexes := before, tables := beforeTables }
    let last := inLet && k + 1 == defs.size
    -- A `Nat` widens to an `Int`, as anywhere an `Int` is expected.
    if let some a := annot? then
      unless a == t || (a == .int && t == .nat) do err e.span (Fren.Core.definitionTypeMsg n a.show t.show last)
    let t := annot?.getD t
    liftMsg y.span ((Fren.Core.checkVarName n (some (t == .bool))).mapError (Fren.Core.membershipNote last))
    if cx.noteIndexes then lintName .binder n y.span
    let sym := s!"let@{(← get).nLets}"
    modify fun s => { s with nLets := s.nLets + 1 }
    binds := binds.push (sym, smt)
    cx := { cx with binders := cx.binders.push { name := n, smt := sym, ty := t, scrutinee := e, outer := cx.binders.size,
                                                 isDef := true, obligations, tableObligations } }
  return (cx, binds)
end

/-- Reports `assertions_on_constants` on the constraint `e`, an `assume`,
`ensure` or `expect` as `kind` says (`lint::assertions_on_constants`). -/
def lintConstant (cx : ExprCtx) (kind : String) (e : Expr) : M Unit := do
  if Fren.Core.assertionOnConstant (← mentionedNames cx e) then
    lint .assertionsOnConstants e.span (Fren.Core.assertionOnConstantMsg kind (match e with | .bool _ b => some b | _ => none))

/-- The conditions of a top-level `when`/`unless` chain, and their span. -/
partial def trigger? (cx : ExprCtx) : Expr → M (Option (String × Span))
  | .when span neg c d => do
    -- With the names that its pattern tests bind, which the body may see
    -- (`lang::test_scope`).
    let context : Fren.Core.TestContext := if neg then .unlessCondition else .whenCondition
    let ((cs, _), new) ← withBound (elabExpr { cx with noteIndexes := false, testContext := context } c)
    let cs := if neg then s!"(not {cs})" else cs
    let here : Span := { start := span.start, stop := c.span.stop }
    let seen := if Fren.Core.binderVisible context 0 1 .body then new else #[]
    match ← trigger? { cx with binders := cx.binders ++ seen } d with
    | none => return some (cs, here)
    | some (t, s) => return some (s!"(and {cs} {t})", here.to s)
  -- Through a `let` or `where`, whose names stand for their definitions.
  | .«let» _ defs body isWhere => do
    let saved ← get
    let (bcx, binds) ← elabDefinitions { cx with noteIndexes := false } defs (!isWhere) (usedDefinitions defs body)
    let t? ← trigger? bcx body
    set saved
    return t?.map fun (t, s) => (wrapLets binds t, s)
  | _ => return none

/-! ## Items -/

/-- Whether the type `segs` is the item `name`, and whether it has it as a
set's element type (`Fren.Core.ownIn`). -/
def ownIn (segs : Array Ident) (name : Ident) : Bool × Bool := Fren.Core.ownIn (segs.map (·.name)) name.name

/-- Whether the type `segs` is the item `name` being declared, whether with
its own type parameters `params`, and whether `name` is within its
arguments (`Fren.Core.ownArgs`). -/
def ownArgs (segs : Array Ident) (name : Ident) (params : Array Name) : Bool × Bool × Bool :=
  Fren.Core.ownArgs (segs.map (·.name)) name.name (params.map toString)

/-- The type parameters `params` of the enumeration or record being
declared, checked: distinct (`lang::distinct_names`), without `!`, and
without the name of a type or of an item in scope (`Reqs/Lang/Generics`). -/
def elabTypeParams (params : Array Ident) : M (Array Name) := do
  let ns := params.map (Name.mkSimple ·.name)
  if let some k := (Fren.Core.repeatsAt ns)[0]? then err params[k]!.span (Fren.Core.dupTypeParamMsg ns[k]!)
  for p in params, n in ns do
    liftMsg p.span (Fren.Core.checkNoBang n)
    if #["Bool", "Int", "Nat", "String", "Set", "Seq", "Rel"].contains p.name then
      err p.span (Fren.Core.typeParamNameMsg n s!"the built-in type `{p.name}`")
    let st ← get
    if let .ok r := st.table.resolvePath st.scope #[n] #[] then
      err p.span (Fren.Core.typeParamNameMsg n r.describe)
  return ns

/-- The span of the annotation `: T` of the type at `span`, from the end of
what precedes it. -/
def annotationSpan (span : Span) : M Span := do
  let src := (← get).src
  let mut i := span.start
  while i > 0 && src[i - 1]!.isWhitespace do i := i - 1
  if i > 0 && src[i - 1]! == ':' then i := i - 1
  while i > 0 && src[i - 1]!.isWhitespace do i := i - 1
  return { span with start := i }

/-- The declared type of the variable, field or function `name`, written
`ty?`, which is `Bool` if it is not written, with its patterns. -/
def varPTy (ty? : Option (Array Ident)) (name : Ident) : M Fren.Core.PTy := do
  let pt ← ty?.mapM elabPTy
  let t := pt.map (·.ty)
  let n := Name.mkSimple name.name
  unless Fren.Core.generatedName name.name do liftMsg name.span (Fren.Core.checkVarName n (t.map (· == .bool)))
  -- `redundant_bool_type` (`lint::redundant_bool_type`), but not of a
  -- subset type, whose invariants the annotation holds.
  if let (some segs, true, false) := (ty?, !Fren.Core.generatedName name.name && Fren.Core.redundantBoolType n (t.map (· == .bool)), pt.any (fun t => t.pat?.isSome || !t.invariants.isEmpty)) then
    let span ← annotationSpan (segs[0]!.span.to segs.back!.span)
    lintFix .redundantBoolType span (Fren.Core.redundantBoolTypeMsg n)
  return pt.getD (.plain .bool)

def varTy (ty? : Option (Array Ident)) (name : Ident) : M Ty := return (← varPTy ty? name).ty

/-- Records what a call of `c`, written at `span`, brings to the current
procedure's mix of relational operators and counting. -/
def noteCounts (c : CComp) (span : Span) : M Unit :=
  modify fun s => { s with relationalUsed := s.relationalUsed || c.relational, guardedUsed := s.guardedUsed || c.guarded
                           countSpans := if c.counts then s.countSpans.push span else s.countSpans }

/-- A call whose procedure has been resolved, before its bindings are
elaborated. -/
structure PendingInst where
  name : Ident
  comp : CComp
  bindings : Array (Ident × Option Expr)
  /-- A call's arguments, rather than bindings written by name. -/
  positional : Bool := true

/-- Resolves the call `call x := p(args)`: the called procedure and the
call's variables, with each argument bound to the parameter in its
position (`F0408`, `F0409`). -/
def resolveInst (x : Ident) (p : Array Ident) (bs : Array (Ident × Option Expr)) : M (PendingInst × Array CVar) := do
  let w := Name.mkSimple x.name
  let path ← match ← resolve p with
    | .item { kind := .compItem, path, .. } => pure path
    | r => err (p[0]!.span.to p.back!.span) (Fren.Core.notACompMsg r)
  let st ← get
  let some c := st.comps.find? (·.path == path) | internal x.span s!"unknown comp `{path}`"
  unless c.decidable do
    modify fun s => { s with outsideCore := true }
    lint .undecidable (p[0]!.span.to p.back!.span) (Fren.Core.undecidableInstMsg path)
  noteCounts c (p[0]!.span.to p.back!.span)
  let params := c.vars.filter (fun v => v.role == .input && v.name.isAtomic) |>.map (·.name)
  let callee := showPath path
  let some bound := Fren.Core.callBindings (params.map Fren.Core.nameText) bs
    | let at_ := if bs.size > params.size then bs[params.size]!.1.span.to bs.back!.1.span else p[0]!.span.to p.back!.span
      err at_ (Fren.Core.callArityMsg callee (params.map Fren.Core.nameText) bs.size)
  let bs := bound.map fun (n, (a, e?)) => ({ a with name := n }, e?)
  let vars := c.vars.map fun v =>
    let role := Role.ofInst v.role v.isPub
    -- An input's constraint is the call's obligation, which the
    -- call check asks, rather than a fact (`Reqs/Check#call-assumptions`).
    { name := w ++ v.name, role, isPub := role == .instOutput, ty := v.ty, span := x.span, ptype := v.ptype
      fact? := if v.role == .input then none else v.fact?.map (rename w c.vars) }
  return ({ name := x, comp := c, bindings := bs }, vars)

/-- Elaborates the bindings of a call. -/
def elabInst (cx : ExprCtx) (pi : PendingInst) : M CInst := do
  let w := Name.mkSimple pi.name.name
  let mut eqs := #[]
  let c := pi.comp
  for (b, e?) in pi.bindings do
    if let some e := e? then if !pi.positional then lintRedundant b e false
    let e := e?.getD (.path b.span #[b])
    let some v := cx.vars.find? (·.name == w ++ Name.mkSimple b.name)
      | internal b.span s!"no variable for `{b.name}`"
    let (smt, t) ← elabExpr { cx with expected? := Fren.Core.ExprSite.binding.expected (some v.ty) none } e
    liftMsg e.span (Fren.Core.checkType v.ty t (some s!"note: `{b.name}` of `{showPath c.path}` has type `{v.ty.show}`"))
    -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
    if v.ty == .int && t == .int then modify fun s => { s with natKept := s.natKept.push (c.path, b.name) }
    lintBools e (← hidesIn cx) (pi.positional && pi.bindings.size == 1)
    eqs := eqs.push s!"(= {quote v.name.toString} {smt})"
  modify fun s => { s with natApps := s.natApps ++ c.natApps.map (rename w c.vars) }
  -- Each input whose type has an obligation assumes it, before the
  -- procedure's own assumptions (`Reqs/Check#call-assumptions`).
  let st ← get
  let typed := c.vars.filter (·.role == .input) |>.flatMap fun v =>
    (v.ptype.obligation st.shapeOf).toArray.flatMap fun obligation =>
      obligation.namedParts.mapIdx fun k (label, part) =>
        let text := if label.isAnonymous then v.ptype.text else "@invariant:" ++ Fren.Core.showPath label
        (Name.num v.name k, text, rename w c.vars (consSmt st.dataOf? part (quote v.name.toString)))
  -- Preconditions may read local definitions. They must be substituted
  -- before becoming obligations: the call's own behaviour is deliberately
  -- not a hypothesis of its call check.
  let unfold (smt : String) := c.defs.foldr (fun (n, value) body =>
    substQuoted (fun p => if p == n.toString then value else quote p) body) smt
  return {
    name := w, comp := c.path, span := pi.name.span, bindings := conj eqs
    behaviour := rename w c.vars c.meaning
    assumes := typed.map (fun (n, _, f) => (n, f)) ++ (c.props.filter (·.kind == .assume) |>.map fun a => (a.name, rename w c.vars (unfold a.smt)))
    typed := typed.map fun (n, t, _) => (n, t)
    bounded := c.vars.any fun v => v.role == .input && (v.ptype.obligation st.shapeOf).any (·.quantifies) }

/-- Imports the path `segs`, written at `loc`, into the current module, or,
with `scope`, into the procedure of that path. -/
def declareUse (segs : Array Ident) (glob : Bool) (loc : UseLoc) (scope : Option Name := none) : M Unit := do
  let st ← get
  let u ← liftResolve segs (st.table.declareUse st.module (segNames segs) glob (scope.getD st.module))
  let record : Fren.Core.UseRecord := {
    module := u.scope, target := u.target, glob := u.glob
    unusedLevel := st.levels.get .unusedImports, globLevel := st.levels.get .globImports }
  modify fun s => { s with table := s.table.addUse u, useRecords := s.useRecords.push (record, loc.path),
                           useLocs := s.useLocs.push loc }

/-- Declares a procedure's `use`s, in the scope `path`, and makes it the
scope that paths resolve in if there are any. -/
def declareMemberUses (path : Name) (members : Array Member) : M Unit := do
  for m in members do
    match m with
    | .use span segs glob =>
      declareUse segs glob { item := span, removal := span, path := segs[0]!.span.to segs.back!.span } (some path)
      modify fun s => { s with scope := path }
    | .useGroup span pre paths =>
      for p in paths do
        declareUse (pre ++ p) false
          { item := span, removal := span, path := p[0]!.span.to p.back!.span, pre? := some (pre[0]!.span.to pre.back!.span) }
          (some path)
      modify fun s => { s with scope := path }
    | _ => pure ()

/-- The evidence that the `set_option fren.evidence` in effect sets
(`Reqs/Check#checking-by-enumeration`); an invalid value sets nothing. -/
def evidenceOfEffect : M Fren.Core.Evidence := do
  match (← get).evidence? with
  | none => return {}
  | some (value, _) => return (Fren.Core.evidenceOf? value).getD {}

/-- Whether the `set_option fren.evidence` in effect sets checks to testing.
An invalid value, reported once where it is set (`F0214`), sets nothing. -/
def evidenceInEffect : M Bool := return (← evidenceOfEffect).tested

/-- The conjuncts of `e`, a constraint: the operands of its `and`s, not
through parentheses but its own (`lint::manual_nat`). -/
partial def constraintConjuncts (src : Array Char) (e : Expr) : Array Expr :=
  let rec go (top : Bool) (e : Expr) : Array Expr :=
    let bare := top || Fren.Core.withParens src (toRange e.span) == toRange e.span
    match e with
    | .bin _ "and" a b => if bare then go false a ++ go false b else #[e]
    | _ => #[e]
  go true e

/-- Records `manual_nat` in the procedure `comp` of `members`
(`lint::manual_nat`): for each variable it fires on, at its first bound,
reported at the end of the file (`finishNat`). -/
def lintManualNat (comp : Name) (members : Array Member) : M Unit := do
  let src := (← get).src
  let vars := members.filterMap fun
    | .var isIn _ _ x ty? defn? => some ((declaredIdent x).1, ty?, isIn, defn?.isSome)
    | _ => none
  -- Only assumptions and guarantees constrain; an expectation or a cover goal has no bound.
  let props := members.filterMap fun
    | .prop kind x e => some (kind, x, e, if kind == .assume || kind == .ensure then constraintConjuncts src e else #[])
    | _ => none
  let wf (e : Expr) : String := Fren.Core.writtenForm (Fren.Core.textOf src (toRange e.span))
  let conjunct (assumption : Bool) (e : Expr) : Fren.Core.NatConjunct := match e with
    | .bin _ op l r => { assumption, op := .ofOp op, left := wf l, right := wf r }
    | _ => { assumption, op := .otherOp, left := "", right := "" }
  let isInt (ty? : Option (Array Ident)) : Bool := match ty? with | some #[t] => t.name == "Int" | _ => false
  let bounds := Fren.Core.manualNatBounds
    (vars.map fun (x, ty?, isIn, defined) =>
      { name := x.name, role := if isIn then .input else if defined then .definedOutput else .output, int := isInt ty? })
    (props.map fun (kind, _, _, cs) => cs.map (conjunct (kind == .assume)))
  for (i, p, k) in bounds do
    let (x, _, isIn, _) := vars[i]!
    let (_, name, _, cs) := props[p]!
    let msg := Fren.Core.manualNatMsg x.name isIn name.name (Fren.Core.textOf src (toRange cs[k]!.span))
    let report := { lint := .manualNat, level := (← get).levels.get .manualNat, ref := cs[k]!.span, msg }
    modify fun s => { s with natReports := s.natReports.push { comp, var := x.name, report } }

/-- The checks of a procedure with `members` that are tested
(`Reqs/Check#checking-by-testing`): `all` if the procedure is set to testing,
then each member's own setting. -/
def testedOf (all : Fren.Core.Evidence) (members : Array Member) : M (Fren.Core.Tested × Fren.Core.Tested) := do
  let reserved := members.filterMap fun | .prop _ x _ => some (Name.mkSimple x.name) | _ => none
  let mut refinesIndex := 0
  let mut pending : Option (Fren.Core.Evidence × Span) := none
  let mut expects := #[]
  let mut insts := #[]
  let mut dets := #[]
  let mut constraints := #[]
  for m in members do
    if let .evidence span value valueSpan := m then
      let some b := Fren.Core.evidenceOf? value | err valueSpan (Fren.Core.invalidEvidenceMsg value)
      pending := some (b, span)
      continue
    let set? := pending.map (·.1)
    match m, pending with
    | .refines .., _ =>
      refinesIndex := refinesIndex + 1
      while reserved.contains (Name.mkSimple s!"refines_{refinesIndex}") do refinesIndex := refinesIndex + 1
      expects := expects.push (Name.mkSimple s!"refines_{refinesIndex}", set?)
    | .prop .expect x _, _ | .prop .cover x _, _ => expects := expects.push (Name.mkSimple x.name, set?)
    -- By the names they declare, without the `!` of shadowing.
    | .inst x .., _ => insts := insts.push (Name.mkSimple (declaredIdent x).1.name, set?)
    | .var false _ true x _ _, _ => dets := dets.push (Name.mkSimple (declaredIdent x).1.name, set?)
    | _, some (_, span) =>
      let what := match m with
        | .prop .assume .. => "an assumption" | .prop .ensure .. => "a guarantee"
        | .var true .. => "a parameter" | .var .. => "a variable that is not `det`" | .define .. => "a result's definition"
        | _ => "a `use`"
      err span (Fren.Core.misplacedEvidenceMsg what)
    | _, none => pure ()
    match m with
    | .prop .assume x _ | .prop .ensure x _ => constraints := constraints.push (Name.mkSimple x.name)
    | .var false _ _ x _ (some _) => constraints := constraints.push (Name.mkSimple (declaredIdent x).1.name)
    | _ => pure ()
    pending := none
  if let some (_, span) := pending then err span (Fren.Core.misplacedEvidenceMsg "the end of the procedure")
  let by_ (f : Fren.Core.Evidence → Bool) :=
    let pick (xs : Array (Name × Option Fren.Core.Evidence)) := xs.map fun (n, e?) => (n, e?.map f)
    Fren.Core.Tested.ofSettings (f all) constraints (pick expects) (pick insts) (pick dets)
  return (by_ (·.tested), by_ (·.enumerated))

/-- Reports `arbitrary_source_item_ordering` on a procedure whose members,
written at `spans`, are `members`, and whose `{` ends at `openStop`
(`lint::arbitrary_source_item_ordering`). An evidence setting is part of
the member after it. -/
def lintMemberOrder (members : Array Member) (spans : Array Span) (openStop : Nat) : M Unit := do
  let mut kinds := #[]
  let mut ranges : Array Fren.Core.Range := #[]
  let mut names := #[]
  let mut mentioned := #[]
  let mut start? : Option Nat := none
  for m in members, sp in spans do
    let (kind, name?, ms) : Fren.Core.MemberKind × Option Ident × Array Name := match m with
      | .refines w _ args _ => (.expectation, none, #[Name.mkSimple w.name] ++ args.flatMap (fun e => (mentions e).map (·.getRoot)))
      | .evidence .. => (.use, none, #[])
      | .use .. | .useGroup .. => (.use, none, #[])
      | .var _ _ _ x _ none => (.exists, some x, #[])
      | .var _ _ _ x _ (some d) => (.let, some x, (mentions d).map (·.getRoot))
      | .define _ d => (.define, none, (mentions d).map (·.getRoot))
      | .inst x _ bs .. => (.call, some x, bs.foldl (init := #[]) fun acc (b, e?) =>
          acc ++ ((e?.map mentions).getD #[Name.mkSimple (declaredIdent b).1.name]).map (·.getRoot))
      | .prop .assume x _ => (.assumption, some x, #[])
      | .prop .ensure x _ => (.guarantee, some x, #[])
      | .prop .expect x _ => (.expectation, some x, #[])
      | .prop .cover x _ => (.cover, some x, #[])
    if m matches .evidence .. then
      start? := start?.orElse fun _ => some sp.start
      continue
    kinds := kinds.push kind
    ranges := ranges.push { start := start?.getD sp.start, stop := sp.stop }
    start? := none
    names := names.push (name?.map fun x => Name.mkSimple (declaredIdent x).1.name)
    mentioned := mentioned.push ms
  let some i := Fren.Core.firstOutOfOrder? kinds | return
  let msg := Fren.Core.memberOrderMsg kinds[i]! kinds[i - 1]!
  let mentions := mentioned.map (·.filterMap fun n => names.findIdx? (· == some n))
  let at_ : Span := { start := ranges[i]!.start, stop := ranges[i]!.stop }
  match Fren.Core.memberOrderFix? (← get).src openStop ranges kinds mentions with
  | some edit => lintEdits .arbitrarySourceItemOrdering at_ msg #[edit]
  | none => lint .arbitrarySourceItemOrdering at_ msg

/-! ### `elabComp`, in parts

Each part is a definition of its own, so that the compiler, whose time grows
faster than the length of a `do` block, compiles several short ones, and
in parallel. -/

/-- A procedure's variables, each reporting its own first static error, and one
cycle of definitions. -/
def elabCompVars (members : Array Member) : M (Array CVar) := do
  let mut vars := #[]
  for m in members do
    let .var isIn isPub' isDet x ty? defn? := m | continue
    -- An error in shadowing leaves the variable's meaning clear.
    let x := (← attempt (declare x)).getD (declaredIdent x).1
    let xn := Name.mkSimple x.name
    lintName .variable xn x.span
    let role := if isIn then Role.input else .output
    let some v ← attempt do
        if let some segs := ty? then checkFnTypeSite .variable segs
        let ptype ← varPTy ty? x
        let ty := ptype.ty
        unless (← get).inSubset || Fren.Core.variableTypeAccepted (role == .output) ((← get).unbounded ty) defn?.isSome do
          err x.span (Fren.Core.unboundedOutputMsg xn ptype.text)
        let fact? ← factOf ptype (quote xn.toString)
        return { name := xn, role, isPub := isPub', isDet, ty, span := x.span, defn?, ptype, fact? : CVar }
      | continue
    vars := vars.push v
  -- One cycle is reported.
  if let some (v, cycle) := vars.findSome? fun v => (defCycle? vars v.name).map (v, ·) then
    discard <| attempt (err (α := Unit) v.span (Fren.Core.cyclicDefinitionMsg cycle))
  return vars

/-- A procedure's calls, whose variables follow the procedure's own `vars`: the
calls still to elaborate, and all the variables. -/
def elabCompInsts (members : Array Member) (vars : Array CVar) : M (Array PendingInst × Array CVar) := do
  let mut vars := vars
  let mut pending := #[]
  for m in members do
    let .inst x p bs _ := m | continue
    -- Its name is checked once, whether or not it shadows.
    let x := (← attempt do
        let x ← declare x
        liftMsg x.span (Fren.Core.checkItemName "call" (Name.mkSimple x.name))
        return x).getD (declaredIdent x).1
    let xn := Name.mkSimple x.name
    lintName .instance xn x.span
    let some (pi, ivars) ← attempt (resolveInst x p bs) | continue
    pending := pending.push pi
    vars := vars ++ ivars
    -- Its bindings give each input of its procedure a value, and the
    -- call's assumption check reads them (`unused_assumption`).
    let reads := (pi.comp.vars.filter fun v => v.name.isAtomic && v.role == Role.input).map (pi.comp.path, ·.name)
    modify fun s => { s with globalReads := s.globalReads ++ reads }
  return (pending, vars)

/-- The bindings of a procedure's calls `pending`, with their indexes and
questions about tables. -/
def elabCompBindings (vars : Array CVar) (instNames : Array Name) (pending : Array PendingInst) :
    M (Array CInst × Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  let mut insts := #[]
  let mut indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) := #[]
  let mut tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) := #[]
  discard takeIndexes
  discard takeTables
  for pi in pending, k in [0:pending.size] do
    let some (i, idx, tbl) ← attempt do
        let i ← elabInst { vars, insts := instNames, place := .binding, current := k } pi
        return (i, (← takeIndexes).map fun (sp, g, t) => (Name.mkSimple pi.name.name, Fren.Core.IndexPlace.binding k, sp, g, t),
          (← takeTables).map fun (sp, q, g) => (Name.mkSimple pi.name.name, Fren.Core.IndexPlace.binding k, sp, q, g))
      | continue
    insts := insts.push i
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (insts, indexes, tables)

/-- A procedure's definitions, each after those it mentions, with their indexes
and questions about tables added to `indexes` and `tables`. -/
def elabCompDefinitions (name : Ident) (vars : Array CVar) (instNames : Array Name) (indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)))
    (tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) : M (Array (Name × String) × Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  let mut indexes := indexes
  let mut tables := tables
  let mut defs : Array (Name × String) := #[]
  let mut todo := vars.filter (·.defn?.isSome)
  while !todo.isEmpty do
    let some v := todo.find? fun v => (mentions v.defn?.get!).all fun n => !todo.any (·.name == n)
      | internal name.span "cyclic definitions"
    todo := todo.filter (·.name != v.name)
    let e := v.defn?.get!
    let some (smt, idx, tbl) ← attempt do
        -- A definition assigns once and acyclically, so `++` is in the core in it.
        let dcx : ExprCtx := { vars, insts := instNames, place := .prop, expected? := Fren.Core.ExprSite.outputDefinition.expected (some v.ty) none, concatOk := true }
        let (smt, t) ← elabExpr dcx e
        liftMsg e.span (Fren.Core.checkType v.ty t (some s!"note: `{v.name}` has type `{v.ty.show}`, so its definition must too"))
        noteObligation dcx .definition e.span v.ptype smt
        lintBools e (← hidesIn dcx)
        return (smt, (← takeIndexes).map fun (sp, g, t) => (v.name, Fren.Core.IndexPlace.prop, sp, g, t),
          (← takeTables).map fun (sp, q, g) => (v.name, Fren.Core.IndexPlace.prop, sp, q, g))
      | continue
    defs := defs.push (v.name, smt)
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (defs, indexes, tables)

/-- Branch facts and model observations annotate an already-checked source
expression; rebuilding their formulas adds no evaluation site or use. -/
def annotateBranches (cx : ExprCtx) (owner : Name) (e : Expr) : M Unit := do
  let saved ← get
  let mut branches := saved.itemBranches
  let mut observations := saved.itemMemberGroups
  if let some (kind, guard, members) := branchMembers e then
    if kind != .equivalence || members.size > 1 then
      let leaves ← members.zipIdx.mapM fun ((label, source, member), i) => do
        let name := Name.mkSimple (owner.toString ++ "." ++ (label.map (·.name) |>.getD (toString (i + 1))))
        let (formula, _) ← elabExpr { cx with noteIndexes := false, expected? := some .bool } member
        let span := label.map (·.span) |>.getD source
        let text ← srcAt source
        return ({ name, formula, range? := some (toRange span), text } : Fren.Core.BranchMember String)
      let guard ← guard.mapM fun guard => do pure (← elabExpr { cx with noteIndexes := false, expected? := some .bool } guard).1
      branches := branches.push { owner, kind, members := leaves, guard? := guard }
  if let some group := observedMembers e then
    let leaves ← group.members.zipIdx.mapM fun ((label, source, member, guard), i) => do
      let name := Name.mkSimple (owner.toString ++ "." ++ (label.map (·.name) |>.getD (toString (i + 1))))
      let (evaluation, _) ← elabExpr { cx with noteIndexes := false, expected? := some .bool } guard
      let (formula, _) ← if evaluation == "false" then pure ("true", Ty.bool)
        else elabExpr { cx with noteIndexes := false, expected? := some .bool } member
      let span := label.map (·.span) |>.getD source
      let text ← srcAt source
      return ({
        name := name
        formula := formula
        valueFormula? := some formula
        evaluationGuard? := some evaluation
        range? := some (toRange span)
        text := text
      } : Fren.Core.BranchMember String)
    observations := observations.push { owner, op := group.op, wanted := group.wanted, members := leaves }
  set { saved with itemBranches := branches, itemMemberGroups := observations }

/-- Instantiate closed member templates at an application. SMT `let` uses
simultaneous bindings, so caller variables cannot capture definition binders. -/
partial def predicateClauses (cx : ExprCtx) (e : Expr) (splitConjunction : Bool := true) : M (Option (Name × Array NamedClause)) := do
  match e with
  | .when _ negative condition body =>
    let saved ← get
    let context : Fren.Core.TestContext := if negative then .unlessCondition else .whenCondition
    let (condition, bound) ← withBound do
      exprExpect { cx with noteIndexes := false, testContext := context } condition .bool none
    set saved
    let guard := if negative then s!"(not {condition})" else condition
    let visible := if negative then #[] else bound
    let some (path, clauses) ← predicateClauses { cx with binders := cx.binders ++ visible } body splitConjunction | return none
    return some (path, clauses.map fun clause => { clause with
      formula := guarded #[guard] clause.formula
      branches := clause.branches.map fun group => { group with guard? := some (conj #[guard, group.guard?.getD "true"]) }
      groups := clause.groups.map fun group => { group with members := group.members.map fun member =>
        { member with
          formula := guarded #[guard] member.formula
          valueFormula? := member.valueFormula?.map (guarded #[guard])
          evaluationGuard? := some (conj #[guard, member.evaluationGuard?.getD "true"]) } }
      indexes := clause.indexes.map fun (sp, f, t) => (sp, guarded #[guard] f, t)
      tables := clause.tables.map fun (sp, q, f) => (sp, q, guarded #[guard] f) })
  | .not _ body =>
    let some (path, clauses) ← predicateClauses cx body false | return none
    if clauses.size != 1 || !clauses[0]!.name.isEmpty then return none
    return some (path, clauses.map fun clause => { clause with formula := s!"(not {clause.formula})", branches := #[], groups := clause.groups.map fun group => { group with wanted := !group.wanted } })
  | .app _ segs _ =>
    let saved ← get
    if let .ok (.item { kind := .fnItem, path, .. }) := saved.table.resolvePath saved.scope (segs.map (fun x => Name.mkSimple x.name)) then
      if let some higher := saved.hofs.find? path then
        if let some template := saved.namedPredicates.find? path then
          let mut clauses := #[]
          for clause in (if splitConjunction then template.clauses else template.whole?.toArray) do
            let instantiate (body : String) : M String := do
              set { saved with hofs := saved.hofs.insert path { higher with body } }
              let (formula, _) ← elabExpr { cx with noteIndexes := false } e
              return formula
            set { saved with hofs := saved.hofs.insert path { higher with body := clause.formula }, indexes := #[], tables := #[] }
            let (formula, _) ← elabExpr cx e
            let actualIndexes ← takeIndexes
            let actualTables ← takeTables
            let indexes ← clause.indexes.mapM fun (sp, f, t) => do pure (sp, ← instantiate f, t)
            let tables ← clause.tables.mapM fun (sp, q, f) => do pure (sp, q, ← instantiate f)
            let branches ← clause.branches.mapM fun group => do
              let members ← group.members.mapM fun member => do
                let formula ← instantiate member.formula
                pure { member with formula }
              let guard ← group.guard?.mapM instantiate
              pure { group with members, guard? := guard }
            let groups ← clause.groups.mapM fun group => do
              let members ← group.members.mapM fun member => do
                let formula ← instantiate member.formula
                let value ← member.valueFormula?.mapM instantiate
                let guard ← member.evaluationGuard?.mapM instantiate
                pure { member with formula, valueFormula? := value, evaluationGuard? := guard }
              pure { group with members }
            clauses := clauses.push { clause with formula, indexes := actualIndexes ++ indexes, tables := actualTables ++ tables, branches, groups }
          set saved
          return some (path, clauses)
    let (formula, _) ← elabExpr { cx with noteIndexes := false } e
    let st ← get
    set saved
    let .list (.atom symbol :: args) := Fren.Core.STerm.parse formula | return none
    let some (_, template) := st.namedPredicates.toArray.find? fun (path, _) =>
      itemSym path == symbol || st.instSyms.find? path == some symbol | return none
    if args.length != template.params.size then return none
    let binds := template.params.zip args.toArray |>.map fun (name, value) => s!"({quote name.toString} {value.print})"
    let bind (body : String) := if binds.isEmpty then body else s!"(let ({" ".intercalate binds.toList}) {body})"
    return some (template.sourcePath, (if splitConjunction then template.clauses else template.whole?.toArray).map fun clause => { clause with
      formula := bind clause.formula
      branches := clause.branches.map (·.map bind)
      groups := clause.groups.map (·.map bind)
      indexes := clause.indexes.map fun (sp, f, t) => (sp, bind f, t)
      tables := clause.tables.map fun (sp, q, f) => (sp, q, bind f) })
  | _ => return none

/-- A procedure's assumptions, requirements, expectations and cover goals, with
their indexes and questions about tables added to `indexes` and `tables`. -/
def elabCompConstraints (members : Array Member) (vars : Array CVar) (instNames : Array Name) (indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)))
    (tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) : M (Array CProp × Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  let mut indexes := indexes
  let mut tables := tables
  let mut props := #[]
  modify fun s => { s with namedOccurrences := {} }
  for m in members do
    let .prop kind x e := m | continue
    let xn := Name.mkSimple x.name
    let some (p, idx, tbl) ← attempt do
        liftMsg x.span (Fren.Core.checkNoBang xn)
        -- Before the `?` error, as in Lean.
        lintName .constraint xn x.span
        if x.name.endsWith "?" then err x.span (Fren.Core.propNameMsg xn)
        let cx : ExprCtx := { vars, insts := instNames, place := if kind == .assume then .assume else .prop }
        let (smt, t) ← elabExpr cx e
        liftMsg e.span (Fren.Core.checkType .bool t (some "note: a constraint is a `Bool`"))
        lintBools e (← hidesIn cx)
        lintConstant cx (match kind with | .assume => "assume" | .ensure => "ensure" | .expect => "expect" | .cover => "cover") e
        let trig ← trigger? cx e
        annotateBranches cx xn e
        let place := if kind == .assume then Fren.Core.IndexPlace.assume else .prop
        let originalIndexes ← takeIndexes
        let originalTables ← takeTables
        if let some (path, clauses) ← predicateClauses cx e (kind != .cover) then
          if clauses.any (fun clause => !clause.name.isEmpty) then
            modify fun s => { s with itemExcludeGroups := s.itemExcludeGroups.push xn }
          let root := (x.name.splitOn ".").head!
          let key := root ++ ":" ++ path.toString
          let occurrence := (← get).namedOccurrences.getD key 0 + 1
          modify fun s => { s with namedOccurrences := s.namedOccurrences.insert key occurrence }
          let mut expanded := #[]
          let mut idx := originalIndexes.map fun (sp, g, t) => (xn, place, sp, g, t)
          let mut tbl := originalTables.map fun (sp, q, g) => (xn, place, sp, q, g)
          for clause in clauses do
            let namePrefix := x.name ++ "." ++ Fren.Core.showPath path ++ "@" ++ toString occurrence
            let name := if clause.name.isEmpty then xn else Name.mkSimple (namePrefix ++ "." ++ clause.name)
            let memberPrefix := if clause.name.isEmpty then namePrefix else namePrefix ++ "." ++ clause.name
            let memberName (n : Name) := Name.mkSimple (memberPrefix ++ (n.toString.dropPrefix? "#template" |>.getD n.toString))
            let branches := clause.branches.map fun group => { group with owner := name, members := group.members.map fun member => { member with name := memberName member.name } }
            let groups := clause.groups.map fun group => { group with owner := name, members := group.members.map fun member => { member with name := memberName member.name } }
            modify fun s => { s with itemBranches := s.itemBranches ++ branches, itemMemberGroups := s.itemMemberGroups ++ groups }
            expanded := expanded.push ({
              file? := some clause.file
              sourceRef := kind != .cover
              kind := kind
              name := name
              span := if kind == .cover then x.span else clause.span
              smt := clause.formula
              trigger? := trig.map (·.1)
              triggerSpan? := trig.map (·.2)
            } : CProp)
            idx := idx ++ clause.indexes.map fun (sp, g, t) => (name, place, sp, g, t)
            tbl := tbl ++ clause.tables.map fun (sp, q, g) => (name, place, sp, q, g)
          return (expanded, idx, tbl)
        return (#[{ kind, name := xn, span := x.span, smt, trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) : CProp }],
          originalIndexes.map fun (sp, g, t) => (xn, place, sp, g, t), originalTables.map fun (sp, q, g) => (xn, place, sp, q, g))
      | continue
    props := props ++ p
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (props, indexes, tables)

/-- Written identity of a split clause. Synthetic guard/let nodes retain
an enclosing block's span, so that span cannot stand for their new body. -/
partial def Expr.clauseWritten (src : Array Char) (e : Expr) : String :=
  match e with
  | .when _ negative condition body =>
    (if negative then "unless " else "when ") ++
      Fren.Core.textOf src (toRange (condition.writtenSpan src)) ++ ", (" ++ body.clauseWritten src ++ ")"
  | .«let» _ defs body isWhere =>
    let bindings := defs.map fun (name, _, value) =>
      Fren.Core.textOf src { start := name.span.start, stop := value.span.stop }
    (if isWhere then "where{" else "let{") ++ String.intercalate "," bindings.toList ++
      "}in(" ++ body.clauseWritten src ++ ")"
  | _ => Fren.Core.textOf src (toRange (e.writtenSpan src))

/-- End of the actual written member, excluding enclosing synthetic wrappers. -/
partial def Expr.clauseWrittenStop (label : Span) (e : Expr) : Nat :=
  match e with
  | .when sp _ _ body | .«let» sp _ body _ =>
    max (if sp.start >= label.stop then sp.stop else 0) (body.clauseWrittenStop label)
  | _ => e.span.stop

/-- `duplicate_constraint` (`lint::duplicate_constraint`), of a procedure's
constraints. -/
def lintDuplicateConstraints (members writtenMembers : Array Member) : M Unit := do
  let src := (← get).src
  let writtenLabels := writtenMembers.filterMap fun | .prop _ name _ => some name.span | _ => none
  -- Cover goals are compared with each other, and constraints with each other.
  let all := members.filterMap fun | .prop k x e => some (k.core, x, e) | _ => none
  for constraints in #[all.filter (·.1 != .cover), all.filter (·.1 == .cover)] do
    for (i, j) in Fren.Core.repeatedConstraints (constraints.map fun (_, _, e) => e.clauseWritten src) do
      let (k, x, e) := constraints[i]!
      let (k', x', _) := constraints[j]!
      let msg := Fren.Core.duplicateConstraintMsg k' k x'.name
      if (Fren.Core.duplicateConstraint k' k true).2 then
        if !writtenLabels.contains x.span then
          -- Only a written label gives a removable member range. Never
          -- delete a generated clause's entire shared parent expression.
          let mut colon := x.span.stop
          while src[colon]?.any Char.isWhitespace do colon := colon + 1
          if src[colon]? == some ':' then
            let mut stop := e.clauseWrittenStop x.span
            while src[stop]?.any (fun c => c == ' ' || c == '\t') do stop := stop + 1
            if src[stop]? == some ',' then stop := stop + 1
            stop := withLineComment src stop
            lintEdits .duplicateConstraint x.span msg #[(Fren.Core.deletionRange src { start := x.span.start, stop }, "")]
          else lint .duplicateConstraint x.span msg
        else
          let stop := withLineComment src (Fren.Core.withParens src (toRange (e.writtenSpan src))).stop
          lintEdits .duplicateConstraint x.span msg #[(Fren.Core.deletionRange src { start := wordStart src x.span.start, stop }, "")]
      else lint .duplicateConstraint x.span msg

/-- `constant_output` and `definable_output` (`lint::output_lints`), of a
procedure's outputs. -/
def lintOutputs (lcx : ExprCtx) (members : Array Member) (vars : Array CVar) : M Unit := do
  let reqs := members.filterMap fun | .prop .ensure x e => some (Name.mkSimple x.name, e) | _ => none
  for v in vars.filter (fun v => v.role == .output && v.name.isAtomic) do
    let isX : Expr → Bool | .path _ #[seg] => Name.mkSimple seg.name == v.name | _ => false
    let about := reqs.filter fun (_, e) => (mentions e).contains v.name
    -- The only requirement that mentions it, as `x = e` or `x? iff e`, with `e` other variables'.
    let equation := match about with
      | #[(_, .bin _ op l r)] => (op == "=" || op == "iff") &&
          ((isX l && !(mentions r).contains v.name) || (isX r && !(mentions l).contains v.name))
      | _ => false
    let mentioned ← match v.defn? with | some d => mentionedNames lcx d | none => pure []
    let (constant, definable) := Fren.Core.outputLints v.defn?.isSome mentioned about.size equation
    if constant then lint .constantOutput v.span (Fren.Core.constantOutputMsg v.name)
    if definable then lint .definableOutput v.span (Fren.Core.definableOutputMsg v.name about[0]!.1)

/-- `trivial_cover` (`lint::trivial_cover`), of a procedure's cover goals: each
assumption and guarantee as its kind, its name and its written form. -/
def lintTrivialCover (lcx : ExprCtx) (members : Array Member) : M Unit := do
  let src := (← get).src
  let facts ← members.filterMapM fun m => match m with
    | .prop .assume x e => return some ("assumption", Name.mkSimple x.name, Fren.Core.writtenForm (← srcAt (e.writtenSpan src)))
    | .prop .ensure x e => return some ("guarantee", Name.mkSimple x.name, Fren.Core.writtenForm (← srcAt (e.writtenSpan src)))
    | _ => pure none
  for m in members do
    let .prop .cover x e := m | continue
    let w := Fren.Core.writtenForm (← srcAt (e.writtenSpan src))
    -- Only whether it has one: what elaborating it reports is reported where it is.
    let saved ← get
    let trigger ← tryCatch (Option.isSome <$> trigger? lcx e) fun _ => pure false
    set saved
    let same? := (facts.find? (·.2.2 == w)).map fun (k, n, _) => (k, n)
    if let some why := Fren.Core.trivialCover trigger same? then
      lint .trivialCover x.span (Fren.Core.trivialCoverMsg (Name.mkSimple x.name) why)

/-- `case_split_guarantees` (`lint::case_split_guarantees`), of a procedure's
requirements. -/
def lintCaseSplitGuarantees (lcx : ExprCtx) (members : Array Member) (vars : Array CVar) : M Unit := do
  -- `case_split_guarantees` (`lint::case_split_guarantees`): each requirement `when T, y = e`, as its name, where it is
  -- reported, `y`, the operator, `T` and the text of `e`.
  let mut cases : Array (Name × Span × String × String × Fren.Core.VariantTest × String) := #[]
  for m in members do
    let .prop .ensure x (.when _ false c (.bin _ op (.path _ #[y]) rhs)) := m | continue
    unless (op == "=" || op == "iff") && vars.any (fun v => v.role == .output && v.name == Name.mkSimple y.name) do continue
    let some t ← variantTest? lcx c | continue
    cases := cases.push (Name.mkSimple x.name, x.span, y.name, op, t, ← armBodyOf rhs)
  let mut grouped : Array Nat := #[]
  for i in [0:cases.size] do
    if grouped.contains i then continue
    let (_, _, y, op, t, _) := cases[i]!
    let group := (Array.range cases.size).filter fun j =>
      j ≥ i && cases[j]!.2.2.1 == y && cases[j]!.2.2.2.2.1.key == t.key && cases[j]!.2.2.2.2.1.enum == t.enum
    grouped := grouped ++ group
    let cs := group.map fun j => let (n, _, _, _, t, e) := cases[j]!; (n, t, e)
    let ts := cs.map (·.2.1)
    let n := (((← get).table.enums.get? t.enum).map (·.variants.size)).getD 0
    if Fren.Core.caseSplitGuarantees cs.size (Fren.Core.repeatedVariants ts) then
      lint .caseSplitGuarantees cases[group[1]!]!.2.1 (Fren.Core.caseSplitGuaranteesMsg y op cs (Fren.Core.untestedVariants n ts))

/-- `unused_variables` and `unused_assumption` of the procedure `n`, whose
members had no static error. -/
def lintCompUnused (n : Name) (members : Array Member) (vars : Array CVar) (instNames : Array Name)
    (global : Bool := false) : M Unit := do
  let mentioned := members.foldl (init := #[]) fun acc m => match m with
    | .prop _ _ e | .var _ _ _ _ _ (some e) => acc ++ mentions e
    | .refines w _ args _ => acc.push (Name.mkSimple w.name) ++ args.flatMap mentions
    | .inst _ _ bs .. => bs.foldl (init := acc) fun acc (b, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple b.name]
    | _ => acc
  -- A public definition says what the output is, so it is used.
  let candidates := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
  for (x, v) in Fren.Core.unmentioned (candidates.map fun v => (v.name, v)) mentioned do
    lint .unusedVariables v.span (Fren.Core.unusedVariableMsg x global (v.role == .output))
  -- `unused_assumption` (`lint::unused_assumption`), unless the file reads
  -- one of the inputs (`finishLints`), or one that another assumption ties to
  -- a used variable, transitively.
  let others := members.foldl (init := #[]) fun acc m => match m with
    | .prop .assume _ _ => acc
    | .prop _ _ e | .var _ _ _ _ _ (some e) => acc ++ mentions e
    | .refines w _ args _ => acc.push (Name.mkSimple w.name) ++ args.flatMap mentions
    | .inst _ _ bs .. => bs.foldl (init := acc) fun acc (b, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple b.name]
    | _ => acc
  -- The uninterpreted functions that they apply link too.
  let acx : ExprCtx := { vars, insts := instNames, place := .prop }
  let others ← members.foldlM (init := others) fun acc m => match m with
    | .prop .assume _ _ => pure acc
    | .prop _ _ e | .var _ _ _ _ _ (some e) => return acc ++ (← appliedFns acx e)
    | .refines _ _ args _ => args.foldlM (fun acc e => return acc ++ (← appliedFns acx e)) acc
    | .inst _ _ bs .. => bs.foldlM (init := acc) fun acc (_, e?) => match e? with
      | some e => return acc ++ (← appliedFns acx e)
      | none => pure acc
    | _ => pure acc
  let inputs := vars.filter (·.role == .input) |>.map (·.name)
  let assumed := members.filterMap fun | .prop .assume x e => some (x, e) | _ => none
  let mss := assumed.map fun (_, e) =>
    (mentions e).foldl (init := #[]) fun acc n => if vars.any (·.name == n) && !acc.contains n then acc.push n else acc
  let links ← assumed.mapIdxM fun i (_, e) => return mss[i]! ++ (← appliedFns acx e)
  let used := Fren.Core.usedAssumptions links others
  for (x, _) in assumed, ms in mss, ls in links, u in used do
    if Fren.Core.unusedAssumption ms.size (ms.all inputs.contains) u false then
      let r : Fren.Core.AssumptionRecord :=
        { component := (← get).module ++ n, name := Name.mkSimple x.name, inputs := ms, links := ls
          level := (← get).levels.get .unusedAssumption }
      modify fun s => { s with assumptions := s.assumptions.push (r, x.span) }

/-- A procedure's members as a component's: its parameters and results
(`header`), each result with the definition that an `out` member of its
block gives it, at most one (`F0421`), and then its block's other
members. -/
def procMembers (header body : Array Member) : M (Array Member) := do
  let mut defs : Array (String × Expr) := #[]
  for m in body do
    if let .define x e := m then
      if defs.any (·.1 == x.name) then err x.span (Fren.Core.resultDefinedTwiceMsg x.name)
      defs := defs.push (x.name, e)
  let header := header.map fun
    | .var false true det x ty none => .var false true det x ty ((defs.find? (·.1 == (declaredIdent x).1.name)).map (·.2))
    | m => m
  return header ++ body.filter (!· matches .define ..)

/-- `unrelated_binders` (`lint::unrelated_binders`) of the global
expectation `name` with the members `members`: whether its calls fall
into groups that nothing relates. An atom of a constraint relates the
calls it mentions and those whose arguments mention a parameter it
mentions; a call relates itself to the calls its arguments mention; and a
parameter relates the calls whose arguments mention it. -/
def lintUnrelatedCalls (name : Ident) (members : Array Member) : M Unit := do
  let calls := members.filterMap fun
    | .inst x _ bs .. => some (Name.mkSimple (declaredIdent x).1.name, bs.flatMap fun (b, e?) =>
        match e? with
        | some e => (mentions e).map (·.getRoot)
        | none => #[Name.mkSimple b.name])
    | _ => none
  let params := members.filterMap fun
    | .var true _ _ x _ _ => some (Name.mkSimple (declaredIdent x).1.name)
    | _ => none
  let names := calls.map (·.1)
  let reading (p : Name) := (calls.filter (·.2.contains p)).map (·.1)
  let expand (roots : Array Name) := roots.filter names.contains ++ (roots.filter params.contains).flatMap reading
  let atoms := members.flatMap (fun
      | .prop _ _ e => (boolAtoms e).map fun a => expand ((mentions a).map (·.getRoot))
      | .refines w _ args _ => #[expand (#[Name.mkSimple w.name] ++ (args.flatMap mentions).map (·.getRoot))]
      | _ => #[])
    -- A relation of one call alone puts it in no group.
    ++ (calls.map (fun ((w, roots) : Name × Array Name) => #[w] ++ roots.filter names.contains) ++ params.map reading).filter (fun (a : Array Name) => a.size ≥ 2)
  let groups := Fren.Core.binderGroups names atoms
  if Fren.Core.unrelatedBinders groups.size then
    lint .unrelatedBinders name.span (Fren.Core.unrelatedBindersMsg name.name groups)

/-- A member of a global expectation's block that it does not accept
(`lang::block_member`), with where it is reported. -/
def blockMemberError? (header body : Array Member) (spans : Array Span) : Option (Span × Fren.Core.Msg) :=
  let results := header.filterMap fun
    | .var false _ det x _ _ => some (x.span, Fren.Core.BlockMember.result, det)
    | _ => none
  let others := (body.zip spans).filterMap fun (m, sp) => match m with
    | .var _ _ det _ _ none => some (sp, Fren.Core.BlockMember.exists, det)
    | .var _ _ det _ _ (some _) => some (sp, .let, det)
    | .define .. => some (sp, .define, false)
    | .prop .assume .. => some (sp, .assume, false)
    | .prop .ensure .. => some (sp, .ensure, false)
    | .prop .expect .. => some (sp, .expect, false)
    | .prop .cover .. => some (sp, .cover, false)
    | .inst .. => some (sp, .call, false)
    | .use .. | .useGroup .. => some (sp, .use, false)
    | .refines .. => some (sp, .refines, false)
    | .evidence .. => none
  (results ++ others).findSome? fun (sp, m, det) => (Fren.Core.blockMemberReport? m det).map (sp, ·)

/-- Claims an abstract procedure's guarantees with positional inputs and
results. Abstract local definitions are substituted in dependency order. -/
def elabRefinesMember (vars : Array CVar) (pending : Array PendingInst)
    (w : Ident) (path : Array Ident) (args : Array Expr) (sp : Span) (index : Nat) : M CProp := do
  let some concrete := pending.find? (fun i => i.name.name == w.name)
    | err w.span { code? := some "F0201", headline := s!"`{w.name}` is not a call in this global expectation block" }
  let resolved ← resolve path
  let .item { kind := .compItem, path := abstractPath, .. } := resolved
    | err sp (Fren.Core.notACompMsg resolved)
  let some abstract := (← get).comps.find? (·.path == abstractPath)
    | internal sp "missing abstract procedure"
  unless abstract.decidable do modify fun s => { s with outsideCore := true }
  let params := abstract.vars.filter (fun v => v.name.isAtomic && v.role == .input)
  unless params.size == args.size do
    err sp (Fren.Core.callArityMsg (showPath abstractPath) (params.map (Fren.Core.nameText ·.name)) args.size)
  let actual := concrete.comp.vars.filter (fun v => v.name.isAtomic && v.role == .output && v.isPub)
  let results := abstract.vars.filter (fun v => v.name.isAtomic && v.role == .output && v.isPub)
  unless actual.size == results.size do
    err sp { code? := some "F0408", headline := s!"refinement result count mismatch: specification has {results.size}, call has {actual.size}" }
  if let some hidden := abstract.vars.find? (fun v => v.name.isAtomic && v.role == .output && !v.isPub && v.defn?.isNone) then
    err sp { code? := some "F0417", headline := s!"specification `exists` variable `{hidden.name}` is not supported by `refines`"
             notes := #["help: make it a result of the specification"] }
  let cx : ExprCtx := { vars, insts := pending.map (Name.mkSimple ·.name.name), place := .prop }
  let mut substitutions : Array (Name × String) := #[]
  for param in params, arg in args do
    let (value, ty) ← elabExpr { cx with expected? := Fren.Core.ExprSite.binding.expected (some param.ty) none } arg
    liftMsg arg.span (Fren.Core.checkType param.ty ty none)
    substitutions := substitutions.push (param.name, value)
  for required in results, given in actual do
    if let .error msg := Fren.Core.checkType required.ty given.ty none then
      err sp { msg with headline := s!"refinement result type mismatch at `{required.name}`: call result `{given.name}` cannot flow to the specification result" }
    substitutions := substitutions.push (required.name, quote (Name.mkSimple w.name ++ given.name).toString)
  let replace (subs : Array (Name × String)) (text : String) := substQuoted (fun p =>
    ((subs.find? (fun (n, _) => n.toString == p)).map (·.2)).getD (quote p)) text
  let internal := abstract.vars.filter (!·.name.isAtomic)
  -- The claim quantifies over the abstraction's call variables, so its
  -- queries need a logic with quantifiers (`cli::logic`), as Lean's have.
  unless internal.isEmpty do modify fun s => { s with quantified := true }
  for v in internal do
    substitutions := substitutions.push (v.name, quote s!"#refines{index}.{v.name}")
  for (name, value) in abstract.defs do
    unless results.any (·.name == name) do
      substitutions := substitutions.push (name, replace substitutions value)
  let claims := (abstract.props.filter (·.kind == .ensure)).map (fun p => replace substitutions p.smt)
    ++ abstract.defs.filterMap (fun (n, value) => if results.any (·.name == n) then
      some s!"(= {replace substitutions (quote n.toString)} {replace substitutions value})" else none)
    ++ (params ++ results).filterMap (fun v => v.fact?.map (replace substitutions))
  let internalFacts := internal.flatMap fun v =>
    (if v.ty == .nat then #[s!"(>= {replace substitutions (quote v.name.toString)} 0)"] else #[])
      ++ v.fact?.toArray.map (replace substitutions)
  let calls := internalFacts ++ abstract.insts.map fun i => replace substitutions (conj #[i.bindings, i.behaviour])
  let close (goal : String) :=
    let goal := if calls.isEmpty then goal else s!"(=> {conj calls} {goal})"
    if internal.isEmpty then goal else
      s!"(forall ({" ".intercalate (internal.map fun v => s!"({quote s!"#refines{index}.{v.name}"} {v.ty.sort})").toList}) {goal})"
  let body := close (conj claims)
  let defined := (abstract.props.filter (·.kind == .ensure)).map (·.name) ++ abstract.defs.map (·.1)
  modify fun s => { s with indexes := s.indexes ++ abstract.indexes.filterMap (fun (n, _, _, g, t) =>
    if defined.contains n then some (sp, close (replace substitutions g), t) else none) }
  noteCounts abstract sp
  let closeApp (app : String) :=
    let app := replace substitutions app
    let bound := internal.filter fun v => (app.splitOn (quote s!"#refines{index}.{v.name}")).length > 1
    if bound.isEmpty then app else
      s!"(forall ({" ".intercalate (bound.map fun v => s!"({quote s!"#refines{index}.{v.name}"} {v.ty.sort})").toList}) {app})"
  modify fun s => { s with natApps := s.natApps ++ abstract.natApps.map closeApp }
  return { kind := .expect, name := Name.mkSimple s!"refines_{index}"
           span := sp, smt := body, trigger? := none, triggerSpan? := none, abstraction? := some abstractPath }

def elabComp (isPub : Bool) (name : Ident) (header body : Array Member) (spans : Array Span) (openStop : Nat)
    (global : Bool := false) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  modify fun s => { s with outsideCore := false, guardedUsed := false, relationalUsed := false, countSpans := #[], natApps := #[], itemExcludeGroups := #[], itemBranches := #[], itemMemberGroups := #[] }
  if global then
    liftMsg name.span (Fren.Core.checkNoBang n)
    if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  else liftMsg name.span (Fren.Core.checkItemName "procedure" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName (if global then .global else .component) n name.span
  startDeclared
  -- What a global expectation's block accepts (`lang::block_member`).
  if global then
    if let some (sp, msg) := blockMemberError? header body spans then
      err sp msg
  let distributed := body.flatMap fun
    | .prop kind owner expression =>
      if kind != .cover && expression.blockRoot then (expression.clauseLeaves owner).map fun (name, _) => Name.mkSimple name.name else #[]
    | _ => #[]
  let members ← procMembers header (splitConjunctionMembers body)
  declareMemberUses (module ++ n) members
  -- Distinct names (`lang::distinct_names`): variables, calls and
  -- constraints share one namespace.
  let named := members.filterMap fun
    | .var _ _ _ x _ _ | .inst x .. | .prop _ x _ => some x
    | _ => none
  -- By the names they declare, without the `!` of shadowing.
  let declared := named.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err named[k]!.span (Fren.Core.dupMemberMsg declared[k]! global)
  lintMemberOrder body spans openStop
  modify fun s => { s with inCompBody := true }
  -- Each variable, call, binding, definition and constraint reports its
  -- own first static error; after those of the variables, and of the
  -- calls, the item stops, since what follows would only repeat them
  -- (`Reqs/View#static-errors`).
  let vars ← elabCompVars members
  stopIfErrors
  let (pending, vars) ← elabCompInsts members vars
  stopIfErrors
  let instNames := pending.map (Name.mkSimple ·.name.name)
  let (insts, indexes, tables) ← elabCompBindings vars instNames pending
  let (defs, indexes, tables) ← elabCompDefinitions name vars instNames indexes tables
  let (props, indexes, tables) ← elabCompConstraints members vars instNames indexes tables
  let mut props := props
  let mut indexes := indexes
  let mut tables := tables
  let mut refinesIndex := 0
  for m in members do
    if let .refines w abstract args sp := m then
      refinesIndex := refinesIndex + 1
      while props.any (·.name == Name.mkSimple s!"refines_{refinesIndex}") do refinesIndex := refinesIndex + 1
      unless global do err sp { code? := some "F0417", headline := "`refines` is accepted only in global expectation blocks" }
      discard takeIndexes
      discard takeTables
      if let some p ← attempt (elabRefinesMember vars pending w abstract args sp refinesIndex) then
        props := props.push p
        indexes := indexes ++ (← takeIndexes).map (fun (sp, g, t) => (p.name, Fren.Core.IndexPlace.prop, sp, g, t))
        tables := tables ++ (← takeTables).map (fun (sp, q, g) => (p.name, Fren.Core.IndexPlace.prop, sp, q, g))

  lintManualNat (module ++ n) members
  lintDuplicateConstraints members body
  let lcx : ExprCtx := { vars, insts := instNames, place := .prop }
  lintOutputs lcx members vars
  lintTrivialCover lcx members
  lintCaseSplitGuarantees lcx members vars
  if global then lintUnrelatedCalls name members
  -- The lints above are found despite a constraint's static error, as in
  -- Lean; `unused_variables`, and the rest, only without one.
  stopIfErrors
  lintCompUnused n members vars instNames global
  let path := module ++ n
  let (tested, enumerated) ← testedOf (← evidenceOfEffect) members
  let (relational, counts) ← checkCounts
  let c : CComp := { path, file := (← get).file, span := name.span, vars, props, insts, defs, indexes, tables, distributed := distributed ++ (← get).itemExcludeGroups ++ (props.filter (fun p => p.name.toString.contains '@')).map (·.name)
                     branchGroups := (← get).itemBranches
                     memberGroups := (← get).itemMemberGroups
                     decidable := !(← get).outsideCore, relational, counts, tested, enumerated, enumSize := (← get).enumSize
                     natApps := (← get).natApps, guarded := (← get).guardedUsed, global }
  -- A global expectation is an item that nothing calls
  -- (`Reqs/Lang/Global`).
  if global then
    modify fun s => { s with
      table := s.table.addItem { kind := .expectItem, path, isPub := false, owner := s.module }
      scope := s.module
      globals := s.globals.push c }
  else
    modify fun s => { s with
      table := s.table.addItem { kind := .compItem, path, isPub, owner := s.module }
      scope := s.module
      comps := s.comps.push c }

/-- Elaborates a global expectation (`Reqs/Lang/Global`). -/
def elabGlobal (name : Ident) (binders : Array Binder) (body : Expr) : M Unit := do
  if binders.isEmpty && (body.blockRoot || (observedMembers body).isSome) then
    elabComp false name #[] #[.prop .expect { name := "", span := name.span } body] #[body.span] name.span.stop (global := true)
    return
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkNoBang n)
  let all ← evidenceOfEffect
  if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  modify fun s => { s with outsideCore := false, guardedUsed := false, relationalUsed := false, countSpans := #[], natApps := #[] }
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .global n name.span
  startDeclared
  -- `duplicate_constraint` (`lint::duplicate_constraint`): its text after
  -- its name, against the earlier ones of its module.
  let st ← get
  let src := st.src
  let written := body.writtenSpan src
  let text := String.ofList (src.extract name.span.stop written.start).toList ++ (← srcAt written)
  if let some (_, earlier, _) := st.globalTexts.find? fun (m, _, t) => m == st.module && Fren.Core.writtenSame t text then
    let stop := withLineComment src (Fren.Core.withParens src (toRange written)).stop
    lintEdits .duplicateConstraint name.span (Fren.Core.duplicateConstraintMsg .expect .expect earlier)
      #[(Fren.Core.deletionRange src { start := st.settingStart?.getD st.itemStart, stop }, "")]
  modify fun s => { s with globalTexts := s.globalTexts.push (st.module, name.name, text) }
  -- Distinct names (`lang::distinct_names`).
  let binderIds := binders.flatMap (·.names)
  -- By the names they declare, without the `!` of shadowing.
  let declared := binderIds.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err binderIds[k]!.span (Fren.Core.dupBinderMsg declared[k]!)
  -- Its binders are a quantifier around the body, and it mentions no
  -- variables (`Reqs/Lang/Global#the-short-form`).
  let valueBinders := binders
  let cx : ExprCtx := { vars := #[], place := .prop }
  discard takeIndexes
  discard takeTables
  let quantified := if valueBinders.isEmpty then body
    else .quant { start := valueBinders[0]!.span.start, stop := body.span.stop } true valueBinders body
  let (smt, t) ← elabExpr cx quantified
  let indexes := (← takeIndexes).map fun (sp, g, t) => (n, Fren.Core.IndexPlace.prop, sp, g, t)
  let tables := (← takeTables).map fun (sp, q, g) => (n, Fren.Core.IndexPlace.prop, sp, q, g)
  liftMsg body.span (Fren.Core.checkType .bool t (some "note: an expectation is a `Bool`"))
  -- The body is in the scope of the binders over values too.
  lintBools body (← hidesIn cx (valueBinders.flatMap (·.names) |>.map fun x =>
    (Name.mkSimple (declaredIdent x).1.name, .boundName)))
  lintConstant cx "expect" body
  let trig ← trigger? cx quantified
  lintDeclared .global n name.span
  let prop : CProp := { kind := .expect, name := n, span := name.span, smt
                        trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) }
  discard checkCounts
  modify fun s => { s with
    table := s.table.addItem { kind := .expectItem, path := module ++ n, isPub := false, owner := s.module }
    globals := s.globals.push { path := s.module, file := s.file, span := name.span, vars := #[], props := #[prop], indexes, tables
                                short := true
                                decidable := !s.outsideCore, natApps := s.natApps, guarded := s.guardedUsed
                                tested := Fren.Core.Tested.ofSettings all.tested #[] #[(n, none)] #[] #[]
                                enumerated := Fren.Core.Tested.ofSettings all.enumerated #[] #[(n, none)] #[] #[]
                                enumSize := s.enumSize } }

/-- Elaborates a law of the trait being elaborated (`Reqs/Lang/Traits#laws`):
its variables are a quantifier around its equation, and it mentions no
variables, as a global expectation in the short form does. Records it in
`traitLaws`. -/
def elabLaw (name : Ident) (params : Array (Ident × Option (Array Ident))) (body : Expr) : M Unit := do
  -- Only variables, parameters, calls and binders are written with `!`.
  liftMsg name.span (Fren.Core.checkNoBang (Name.mkSimple name.name))
  let name := (declaredIdent name).1
  let n := Name.mkSimple name.name
  if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  modify fun s => { s with outsideCore := false, guardedUsed := false, relationalUsed := false, countSpans := #[], natApps := #[] }
  lintName .law n name.span
  startDeclared
  -- Distinct names (`lang::distinct_names`), without the `!` of shadowing.
  let declared := params.map fun (x, _) => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err params[k]!.1.span (Fren.Core.dupParamMsg declared[k]!)
  -- Each variable has its type written, but a `Bool`, which may be written
  -- `x?` alone, as a function's parameter may.
  let mut binders : Array Binder := #[]
  for (x, ty?) in params do
    let ty ← match ty? with
      | some segs => pure segs
      | none =>
        discard (varPTy none x)
        pure #[({ name := "Bool", span := x.span } : Ident)]
    binders := binders.push { names := #[x], ty, span := x.span.to ((ty.back?.map (·.span)).getD x.span) }
  let cx : ExprCtx := { vars := #[], place := .prop }
  discard takeIndexes
  discard takeTables
  let quantified := if binders.isEmpty then body
    else .quant { start := binders[0]!.span.start, stop := body.span.stop } true binders body
  let (smt, t) ← elabExpr cx quantified
  discard takeIndexes
  discard takeTables
  liftMsg body.span (Fren.Core.checkType .bool t (some "note: a law is a `Bool`"))
  lintBools body (← hidesIn cx (declared.map (·, .boundName)))
  lintDeclared .law n name.span
  discard checkCounts
  modify fun s => { s with traitLaws := s.traitLaws.push (n, smt, !s.outsideCore, s.natApps, s.guardedUsed) }

/-- Elaborates the clauses of the contract of the function `n` at `path`,
whose parameters are `vars`, and records the contract, and each clause's
definition for the prelude (`Reqs/Lang/Items#contracts`). Gives each
clause as a constraint of the function's body's procedure, named after the
function and the clause, a postcondition only if the function is defined;
and the questions about the tables and applications in them: a
precondition's under the other preconditions, a postcondition's under all
of them. -/
def elabContract (path n : Name) (defined : Bool) (vars : Array CVar) (clauses : Array (Bool × Ident × Expr)) (result : Ty)
    (span : Span) (fnParams : Array (Name × Fren.Core.FnTy × String) := #[]) (params : Array Name := vars.map (·.name)) : M (Array CVar × Array CProp × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  -- The clauses' names share one namespace with the parameters
  -- (`lang::distinct_names`).
  let names := vars.map (·.name) ++ clauses.map fun (_, x, _) => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt names)[0]? then
    if k ≥ vars.size then err clauses[k - vars.size]!.2.1.span (Fren.Core.dupClauseMsg names[k]!)
  let mut k : Contract := { defined }
  let mut props := #[]
  let mut sites := #[]
  let mut occurrences : Std.HashMap Name Nat := {}
  modify fun s => { s with contractIndexes := #[], itemBranches := #[], itemMemberGroups := #[] }
  for (post, x, e) in clauses do
    let cn := Name.mkSimple x.name
    liftMsg x.span (Fren.Core.checkNoBang cn)
    lintName .constraint cn x.span
    if x.name.endsWith "?" then err x.span (Fren.Core.propNameMsg cn)
    discard takeTables
    discard takeIndexes
    let cx : ExprCtx := { vars, place := .prop, contract? := some (path, post, params), fnParams }
    let (smt, t) ← elabExpr cx e
    liftMsg e.span (Fren.Core.checkType .bool t (some "note: a clause of a contract is a `Bool`"))
    let indexes ← takeIndexes
    let tables ← takeTables
    let place := if post then Fren.Core.IndexPlace.body else .assume
    lintBools e (← hidesIn cx)
    let app := s!"({itemSym path} {" ".intercalate (vars.toList.map fun v => quote v.name.toString)})"
    let value := quote (Fren.Core.contractValueName n (vars.map (·.name))).toString
    let output (formula : String) := if post && !defined then formula.replace app value else formula
    let entries ← if let some (predicate, templates) ← predicateClauses cx e then do
        let occurrence := occurrences.getD predicate 0 + 1
        occurrences := occurrences.insert predicate occurrence
        pure <| templates.map fun entry => { entry with
          name := if entry.name.isEmpty then x.name else x.name ++ "." ++ Fren.Core.showPath predicate ++ "@" ++ toString occurrence ++ "." ++ entry.name }
      else do
        let (nb, ng) := ((← get).itemBranches.size, (← get).itemMemberGroups.size)
        annotateBranches cx (n ++ cn) e
        -- Over the value, as its formula is.
        modify fun s => { s with
          itemBranches := s.itemBranches.extract 0 nb ++ (s.itemBranches.extract nb).map (·.map output)
          itemMemberGroups := s.itemMemberGroups.extract 0 ng ++ (s.itemMemberGroups.extract ng).map (·.map output) }
        pure #[{ file := (← get).file, name := x.name, span := x.span, formula := smt : NamedClause }]
    for entry in entries do
      let cn := Name.mkSimple entry.name
      let owner := n ++ cn
      let sym := clauseSym path cn
      modify fun s => { s with clauseDefs := s.clauseDefs.push (sym, vars.map fun v => (v.name, v.ty), entry.formula) }
      if post then k := { k with posts := k.posts.push (cn, sym) } else k := { k with pres := k.pres.push (cn, sym) }
      props := props.push ({
        file? := some entry.file
        kind := if post then .ensure else .assume
        name := owner
        span := entry.span
        smt := output entry.formula
        trigger? := none
        triggerSpan? := none
      } : CProp)
      sites := sites ++ (tables ++ entry.tables).map fun (sp, question, goal) => (owner, place, sp, question, output goal)
      modify fun s => { s with
        contractIndexes := s.contractIndexes ++ ((indexes ++ entry.indexes).filter (·.2.2.isSome)).map fun (sp, goal, kind) => (owner, place, sp, output goal, kind)
        itemBranches := s.itemBranches ++ entry.branches.map fun group => { (group.map output) with owner }
        itemMemberGroups := s.itemMemberGroups ++ entry.groups.map fun group => { (group.map output) with owner } }
  modify fun s => { s with contracts := s.contracts.insert path k }
  -- Without postconditions, an uninterpreted function's contract has
  -- nothing to realize.
  if defined || k.posts.isEmpty then return (vars, props.filter (defined || ·.kind == .assume), sites)
  -- With its result's type, which it is realized in.
  let name := Fren.Core.contractValueName n (vars.map (·.name))
  let ptype := (((← get).funPTys.find? path).map (·.2)).getD (.plain result)
  let v : CVar := { name, role := .output, isPub := true, ty := result, span, ptype, fact? := ← factOf ptype (quote name.toString) }
  return (vars.push v, props, sites)

/-- Records what each application of the uninterpreted function at `path`,
whose result has the declared type `rp`, brings: what its result's type
does, a `Nat`'s among it (`State.funFacts`). -/
def noteResultFact (path : Name) (rp : Fren.Core.PTy) : M Unit := noteResultFactAt (itemSym path) rp

/-- Records the tables of the body of the function `n`, whose parameters
are `vars`, or of the value of the constant `n`, just elaborated, its
subset types' `obligations`, and the questions about the tables and
applications of the function's contract and its clauses, `contract`, as a
procedure for their checks (`State.bodies`), if it has any questions or
postconditions to check. -/
def noteBody (n : Name) (span : Span) (vars : Array CVar)
    (contract : Array CProp × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) := (#[], #[]))
    (fn? : Option Name := none) (obligations : Array (Span × String × Option (String × Bool)) := #[])
    (generic : Bool := false) : M Unit := do
  let tables := (← takeTables).map fun (sp, q, g) => (n, Fren.Core.IndexPlace.body, sp, q, g)
  -- The indexes of its contract's clauses are not checked, nor their
  -- values given where subset types are declared.
  discard takeIndexes
  let (props, sites) := contract
  -- Its indexes are not checked either.
  let obligations := obligations.filter (·.2.2.isSome)
  if tables.isEmpty && sites.isEmpty && obligations.isEmpty && (← get).contractIndexes.isEmpty && !props.any (·.kind == .ensure) then return
  modify fun s => { s with
    bodies := s.bodies.push { path := s.module, file := s.file, span, vars, props, decidable := !s.outsideCore
                              tables := tables ++ sites, natApps := s.natApps, bodyOf? := some n, fn?, generic, guarded := s.guardedUsed
                              indexes := (obligations.map fun (sp, g, t) => (n, .body, sp, g, t)) ++ s.contractIndexes
                              branchGroups := s.itemBranches
                              memberGroups := s.itemMemberGroups
                              recursive := fn?.any s.recursiveDefs.contains } }

/-- The function type written `segs`, a defined function's parameter's
(`Reqs/Lang/HigherOrder#function-types`): its parameters' and result's
types are neither `Nat`s, subset types nor function types
(`lang::function_type_parts`). -/
def elabFnTy (segs : Array Ident) : M Fren.Core.FnTy := do
  let some (ps, r) := Fren.Core.splitFnSegs (segs.map (·.name)) | internal (typeSpan segs) "a function type"
  -- The segments of each part, which `splitFnSegs` gives by name.
  let mut i := 1
  let mut parts : Array (Array Ident) := #[]
  for p in ps do
    parts := parts.push (segs.extract i (i + p.size))
    i := i + p.size + 1
  parts := parts.push (segs.extract (segs.size - r.size) segs.size)
  let mut tys := #[]
  for part in parts do
    if part.isEmpty then internal (typeSpan segs) "a function type's part"
    if part.any (·.name == Parser.fnSeg) then
      if let some msg := Fren.Core.fnPartMsg? .function then err (typeSpan part) msg
    let pt ← elabPTy part
    let k : Fren.Core.FnPart := if pt.ty == .nat then .nat else if pt.pat?.isSome then .pattern else .plain
    if let some msg := Fren.Core.fnPartMsg? k then err (typeSpan part) msg
    tys := tys.push pt.ty
  return { params := tys.pop, result := tys.back! }

/-- `fn_params_excessive_bools` on the function `n`, declared at `span`,
whose parameters have the types `params` (`lint::fn_params_excessive_bools`). -/
def lintFnBools (n : Name) (span : Span) (params : Array Ty) : M Unit := do
  let nBools := (params.filter (· == .bool)).size
  if Fren.Core.fnParamsExcessiveBools nBools then lint .fnParamsExcessiveBools span (Fren.Core.fnParamsExcessiveBoolsMsg n nBools)

/-- Reports the lints of the string literals and comments of the current
item, at its level (`literalLints`). -/
def lintLiterals : M Unit := do
  for (l, span, msg) in (← get).literals do lintFix l span msg
  modify fun s => { s with literals := #[] }

/-- What `F0215` calls the item `item`, after `set_option ... in`, if it is
a function or a constant, through further settings with `in`, and what
its checks are of: a body, a constant's value, or a contract. -/
partial def evidenceTarget? : Item → Option (String × Fren.Core.CheckedItem)
  | .function _ _ _ _ _ body .. => some ("a function", if body.isSome then .body else .contract)
  | .const .. => some ("a constant", .body)
  | .lintSetting _ _ _ _ _ (some body) => evidenceTarget? body
  | _ => none

/-- Records that the settings that set `lints` here are in effect at an
item, or at a setting that reads their level (`unused_lint_setting`). -/
def noteSettingsSeen (lints : Array Lint := Lint.all) : M Unit :=
  modify fun s => { s with seenSettings := lints.foldl (init := s.seenSettings) fun acc l =>
    match (s.levels.get l).setting? with
    | some i => if acc.contains i then acc else acc.push i
    | none => acc }

mutual
partial def elabItem (item : Item) : M Unit := do
  -- Paths resolve in the module, but in a procedure's or a function's
  -- block with `use`s, which sets its own scope.
  modify fun s => { s with scope := s.module }
  -- A `set_option` leaves them to the item after it.
  unless item matches .lintSetting .. do
    lintLiterals
    let sp := (← get).itemSpan
    for (comma, closer) in (← get).trailingCommas do
      if sp.start ≤ comma.start && comma.start < sp.stop then
        lintFix .unnecessaryTrailingComma comma (Fren.Core.unnecessaryTrailingCommaMsg closer)
  -- A check, such as `#fren_check`, is not about any lint.
  unless item matches .lintSetting .. | .check _ do noteSettingsSeen
  match item with
  | .mod isPub segs => do
    let (path, new) ← liftResolve segs ((← get).table.declareModule (segNames segs) isPub)
    for i in new do
      if let some seg := segs[i.path.components.length - 1]? then
        -- Its name, without the `!` of one that shadows the prelude's, as
        -- the module's path has it.
        lintName .module (Name.mkSimple i.path.getString!) seg.span
        if let some msg := Fren.Core.moduleInceptionMsg? i.path then lint .moduleInception seg.span msg
        if let some msg := Fren.Core.moduleNameMsg? .module i.path.getPrefix (Name.mkSimple i.path.getString!) then
          lint .moduleNameRepetitions seg.span msg
    modify fun s => { s with table := new.foldl (·.addItem ·) s.table, module := path, scope := path }
  | .use span segs glob => do
    let removal := { span with start := (← get).settingStart?.getD span.start }
    declareUse segs glob { item := span, removal, path := segs[0]!.span.to segs.back!.span }
  | .useGroup span pre paths => do
    let removal := { span with start := (← get).settingStart?.getD span.start }
    for p in paths do
      declareUse (pre ++ p) false
        { item := span, removal, path := p[0]!.span.to p.back!.span, pre? := some (pre[0]!.span.to pre.back!.span) }
  | .enum isPub name variants isOrdered params => do
    let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "enum" n)
    let module := (← get).module
    liftMsg written ((← get).table.checkFreshItem module n bang)
    lintName .enumeration n name.span
    let path := module ++ n
    let params ← elabTypeParams params
    modify fun s => { s with typeParams := params }
    let mut vs := #[]
    let mut ctors := #[]
    let mut nRecursive := 0
    let mut unbounded := false
    let mut payloadTys : Array (Array (Fren.Core.PTy × Span)) := #[]
    -- Distinct names (`lang::distinct_names`).
    if let some k := (Fren.Core.repeatsAt (variants.map (Name.mkSimple ·.1.name)))[0]? then
      err variants[k]!.1.span (Fren.Core.dupVariantMsg (Name.mkSimple variants[k]!.1.name))
    for (v, payload?) in variants do
      let vn := Name.mkSimple v.name
      liftMsg v.span (Fren.Core.checkItemName "variant" vn)
      lintName .variant vn v.span
      vs := vs.push vn
      let mut fs := #[]
      let mut pts := #[]
      for segs in payload?.getD #[], k in [0:(payload?.getD #[]).size] do
        checkFnTypeSite .payload segs
        -- The enum's own name, which is not declared yet (`lang::field_type`).
        let (_, ownInSet) := ownIn segs name
        let (own, declared, nested) := ownArgs segs name params
        let tspan := typeSpan segs
        if ownInSet then err tspan (Fren.Core.recursiveSetMsg path)
        -- A recursive payload is the enumeration with its own parameters
        -- (`lang::type_parameter_place`).
        let place := Fren.Core.recursivePlace declared nested
        if (own || nested) && !Fren.Core.typeParamPlaceAccepted place then
          err tspan (Fren.Core.typeParamPlaceMsg .anonymous place (Fren.Core.ownWritten path params) !params.isEmpty)
        let pt ← if own then pure (.plain (Ty.enum path (params.toList.zipIdx.map fun (p, k) => .param k p)))
          else elabPTy segs
        let t := pt.ty
        pts := pts.push (pt, tspan)
        let abstract := t.abstractWithin?
        unless Fren.Core.fieldTypeAccepted abstract.isSome own ownInSet true do
          err tspan (Fren.Core.abstractFieldMsg (abstract.getD path) true (!(t matches .abstract _)))
        unbounded := unbounded || own || (← get).unbounded t
        fs := fs.push (Name.mkSimple (toString k), t)
      -- Recursive if a payload's type is the enumeration or built from it
      -- (`lang::well_founded`).
      let own := (Fren.Core.PTy.plain (Ty.enum path (params.toList.zipIdx.map fun (p, k) => .param k p))).node
      if Fren.Core.recursiveVariant (← get).shapeOf own (pts.toList.map (·.1.node)) then nRecursive := nRecursive + 1
      ctors := ctors.push (vn, fs)
      payloadTys := payloadTys.push pts
    unless Fren.Core.wellFounded variants.size nRecursive do err name.span (Fren.Core.illFoundedMsg n)
    -- A recursive enumeration's payloads are never `Nat`s (`lang::nat_place`),
    -- and a constraint of one is outside the decidable core
    -- (`lang::subset_place`).
    let isRecursive := nRecursive > 0
    let shape : Fren.Core.DataShape := { recursive := isRecursive, parts := payloadTys.map (·.map (·.1)) }
    if isRecursive then
      let st ← get
      for pts in payloadTys do
        for (pt, tspan) in pts do
          unless pt.ty != .nat do err tspan (Fren.Core.natPlaceMsg .recursivePayload)
          if (pt.cons (fun q => if q == path then some shape else st.shapeOf q) true).isSome then
            lint .undecidable tspan Fren.Core.undecidableRecursivePayloadMsg
    -- `enum_variant_names` (`lint::enum_variant_names`, `lint::variant_has_enum_name`).
    if let some msg := Fren.Core.enumVariantNamesMsg? n vs then lint .enumVariantNames name.span msg
    for (v, _) in variants, vn in vs do
      if let some msg := Fren.Core.variantNameMsg? n vn then lint .enumVariantNames v.span msg
    -- Only an enumeration without payloads may be ordered
    -- (`lang::ordered_declaration`); the first payload is reported.
    let withPayload := variants.filter (·.2.isSome)
    unless Fren.Core.orderedDeclAccepted isOrdered withPayload.size none do
      let (v, _) := withPayload[0]!
      err v.span (Fren.Core.orderedPayloadMsg n (Name.mkSimple v.name))
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .enumeration, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := (s.table.addItem { kind := .enumItem, path, isPub, owner := s.module }).addEnum { path, variants := vs }
      datatypes := s.datatypes.push { path, isRecord := false, ctors, unbounded, ordered := isOrdered, params
                                      lean? := Fren.Core.leanTypeOf? path : DataDecl }.withPrelude
      shapes := s.shapes.insert path shape
      typeParams := #[] }
    -- Each read of a recursive enumeration's payload brings the payload's
    -- constraint (`Fren.Core.readCons`), as an application does.
    if isRecursive then
      let st ← get
      let some d := st.dataOf? path | pure ()
      for (c, fs) in ctors, v in [0:ctors.size] do
        for k in [0:fs.size] do
          if let some c' := Fren.Core.readCons st.shapeOf path v k then
            modify fun s => { s with funFacts := s.funFacts.insert (d.selSym c k) (consSmt st.dataOf? c' factHole) }
  | .record isPub name fields isOrdered params => do
    let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "record" n)
    let module := (← get).module
    liftMsg written ((← get).table.checkFreshItem module n bang)
    lintName .record n name.span
    let path := module ++ n
    let params ← elabTypeParams params
    -- A generic record is not ordered, for now (`Fren.Core.orderedGenericAccepted`).
    unless Fren.Core.orderedGenericAccepted isOrdered params.size do err name.span (Fren.Core.orderedGenericMsg n)
    modify fun s => { s with typeParams := params }
    let mut fs : Array (Name × Ty) := #[]
    let mut fieldTys : Array Fren.Core.PTy := #[]
    -- Distinct names (`lang::distinct_names`).
    if let some k := (Fren.Core.repeatsAt (fields.map (Name.mkSimple ·.1.name)))[0]? then
      err fields[k]!.1.span (Fren.Core.dupFieldMsg (Name.mkSimple fields[k]!.1.name))
    for (f, ty?) in fields do
      let fn := Name.mkSimple f.name
      liftMsg f.span (Fren.Core.checkNoBang fn)
      lintName .field fn f.span
      if let some segs := ty? then
        checkFnTypeSite .field segs
        let (_, ownInSet) := ownIn segs name
        let (own, _, nested) := ownArgs segs name params
        if own || nested then err (segs[0]!.span.to segs.back!.span) (Fren.Core.recursiveRecordMsg n)
        if ownInSet then err (segs[0]!.span.to segs.back!.span) (Fren.Core.recursiveSetMsg path)
      let pt ← varPTy ty? f
      let t := pt.ty
      fieldTys := fieldTys.push pt
      if let some p := t.abstractWithin? then
        err ((ty?.map fun segs => segs[0]!.span.to segs.back!.span).getD f.span)
          (Fren.Core.abstractFieldMsg p false (!(t matches .abstract _)))
      fs := fs.push (fn, t)
    -- `struct_field_names` (`lint::struct_field_names`, `lint::field_has_record_name`).
    if let some msg := Fren.Core.structFieldNamesMsg? n (fs.map (·.1)) then lint .structFieldNames name.span msg
    for (f, _) in fields, (fn, _) in fs do
      if let some msg := Fren.Core.fieldNameMsg? n fn then lint .structFieldNames f.span msg
    -- `struct_excessive_bools` (`lint::struct_excessive_bools`).
    let nBools := (fs.filter (·.2 == .bool)).size
    if Fren.Core.structExcessiveBools nBools then lint .structExcessiveBools name.span (Fren.Core.structExcessiveBoolsMsg n nBools)
    let st ← get
    -- An ordered record's fields are ordered (`lang::ordered_declaration`);
    -- the first that is not is reported.
    let first? := Fren.Core.PTy.firstUnordered? st.orderedDecl fieldTys.toList
    unless Fren.Core.orderedDeclAccepted isOrdered 0 first? do
      if let some k := first? then
        let (f, ty?) := fields[k]!
        err ((ty?.map fun segs => segs[0]!.span.to segs.back!.span).getD f.span)
          (Fren.Core.unorderedFieldMsg .record n fs[k]!.1 fs[k]!.2)
    let unbounded := fs.any fun (_, t) => st.unbounded t
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .record, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      datatypes := s.datatypes.push { path, isRecord := true, ctors := #[(`«{}», fs)], unbounded, ordered := isOrdered, params : DataDecl }.withPrelude
      shapes := s.shapes.insert path { isRecord := true, parts := #[fieldTys] }
      typeParams := #[] }
  | .newtype isPub name fields isOrdered => do
    let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "record" n)
    let module := (← get).module
    liftMsg written ((← get).table.checkFreshItem module n bang)
    lintName .record n name.span
    let path := module ++ n
    -- Exactly one field, whose type is accepted as a record's field's
    -- (`lang::newtype`).
    let some segs := fields[0]? | err name.span (Fren.Core.newtypeFieldsMsg path 0)
    unless Fren.Core.newtypeAccepted fields.size true do err name.span (Fren.Core.newtypeFieldsMsg path fields.size)
    let span := typeSpan segs
    checkFnTypeSite .field segs
    let (own, ownInSet) := ownIn segs name
    if own then err span (Fren.Core.recursiveRecordMsg n)
    if ownInSet then err span (Fren.Core.recursiveSetMsg path)
    let pt ← elabPTy segs
    let t := pt.ty
    if let some p := t.abstractWithin? then err span (Fren.Core.abstractFieldMsg p false (!(t matches .abstract _)))
    -- An ordered newtype's underlying type is ordered
    -- (`lang::ordered_declaration`).
    unless Fren.Core.orderedDeclAccepted isOrdered 0 (Fren.Core.PTy.firstUnordered? (← get).orderedDecl [pt]) do
      err span (Fren.Core.unorderedFieldMsg .newtype n (Name.mkSimple "0") t)
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .record, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      newtypes := s.newtypes.insert path t
      orderedNewtypes := if isOrdered then s.orderedNewtypes.push path else s.orderedNewtypes
      shapes := s.shapes.insert path { isRecord := true, isNewtype := true, parts := #[#[pt]] } }
  | .subsetType isPub name binder base clauses => do
    let module := (← get).module
    let n := Name.mkSimple (declaredIdent name).1.name
    let path := module ++ n
    liftMsg name.span (Fren.Core.checkItemName "subset type" n)
    liftMsg name.span ((← get).table.checkFreshItem module n (declaredIdent name).2)
    let baseTy ← elabPTy base
    let mut seen : Array Name := #[]
    let mut invariants := baseTy.invariants
    let mut previous : Array Expr := #[]
    let mut pattern := baseTy.pat?
    for (label, expression) in clauses do
      let logical := Name.mkSimple label.name
      if seen.contains logical then
        err label.span { code? := some "F0372", headline := s!"duplicate invariant `{Fren.Core.showPath (path ++ logical)}`", label? := some "already declared in this subset type" }
      seen := seen.push logical
      let predicate := subsetPredicateIdent name label
      let before := (← get).bodies.size
      let generatedBefore ← get
      let priorSubset := (← get).inSubset
      modify fun st => { st with inSubset := true }
      -- Only the lints of the invariant's own source are reported, as for
      -- any expression, whether or not it has a static error: not those of
      -- the binder, which the pattern shorthand does not write.
      let ownLints (st : State) : State := { st with
        lintReports := generatedBefore.lintReports ++ (st.lintReports.extract generatedBefore.lintReports.size st.lintReports.size).filter (fun report => report.ref.start >= expression.span.start && report.ref.stop <= expression.span.stop)
        lintFixes := generatedBefore.lintFixes ++ (st.lintFixes.extract generatedBefore.lintFixes.size st.lintFixes.size).filter (fun fix => fix.span.start >= expression.span.start && fix.span.stop <= expression.span.stop)
        natReports := generatedBefore.natReports }
      try
        elabItem (.function true predicate #[] #[(#[binder], some base)] none (some expression) #[] expression.span {})
      catch failure =>
        if failure.diags.any (·.msg.code? == some "F0201") then
          err expression.span { code? := some "F0373", headline := "an invariant may mention only its binder, constants and functions", label? := some (Fren.Core.invariantScopeLabel binder.name) }
        throw { failure with state := ownLints failure.state }
      modify fun st => { ownLints st with inSubset := priorSubset }
      -- Its full-definedness check is guarded by earlier invariants below,
      -- rather than checked unconditionally as an ordinary function body.
      modify fun st => { st with bodies := st.bodies.extract 0 before }
      invariants := invariants.push { name := path ++ logical, predicate := module ++ Name.mkSimple predicate.name }
      if pattern.isNone && clauses.size == 1 then
        if let .is _ (.path _ #[x]) p := expression then
          if x.name == binder.name then
            let (pat, bs, _) ← resolvePattern { vars := #[], place := .prop } baseTy.ty binder.name false true p
            if bs.isEmpty then pattern := some pat
      let validator := subsetCheckIdent name s!"defined_{label.name.toLower}"
      let localName : Ident := { name := "subset_predicate?", span := label.span }
      let assumptions := previous.mapIdx fun i e => Member.prop .assume { name := s!"earlier_{i}", span := label.span } e
      let header := #[Member.var true true false binder (some base) none]
      let body := assumptions.push (.var false false false localName none (some expression))
      withoutGhostLints <| elabItem (.comp true validator header body expression.span (body.map fun _ => expression.span) label.span.stop)
      modify fun st => { st with comps := st.comps.map fun c => if c.path == module ++ Name.mkSimple validator.name then
        { c with subsetInvariant? := some (path ++ logical) } else c }
      previous := previous.push expression
    let restricted := { baseTy with invariants, pat? := pattern, text := name.name }
    modify fun st => { st with
      table := st.table.addItem { kind := .typeItem, path, isPub, owner := module }
      aliases := st.aliases.insert path restricted }
    let inhabit := subsetCheckIdent name "inhabited"
    let binderExpr := Expr.path binder.span #[binder]
    let guarantees := clauses.map fun (label, _) =>
      let predicate := subsetPredicateIdent name label
      Member.prop .ensure label (.app label.span #[predicate] #[binderExpr])
    let header := #[Member.var false true false binder (some base) none]
    modify fun st => { st with inSubset := true }
    withoutGhostLints <| elabItem (.comp true inhabit header guarantees name.span (guarantees.map fun _ => name.span) name.span.stop)
    modify fun st => { st with inSubset := false, comps := st.comps.map fun c => if c.path == module ++ Name.mkSimple inhabit.name then
      { c with subset? := some path, finiteModel := true } else c }
  | .typeAlias isPub name ty => do
    let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "type alias" n)
    let module := (← get).module
    liftMsg written ((← get).table.checkFreshItem module n bang)
    lintName .typeAlias n name.span
    let t ← elabPTy ty
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .typeAlias, path := module ++ n, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path := module ++ n, isPub, owner := s.module }
      aliases := s.aliases.insert (module ++ n) t }
  | .abstractType isPub name => do
    let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "abstract type" n)
    let module := (← get).module
    liftMsg written ((← get).table.checkFreshItem module n bang)
    lintName .abstractType n name.span
    let path := module ++ n
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .abstractType, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
      sorts := s.sorts.push path }
  | .function isPub name typeParams params result body clauses last block => do
    modify fun s => { s with contractIndexes := #[], itemBranches := #[], itemMemberGroups := #[] }
    let clauses := splitContractClauses clauses
    -- A precondition or body of its block that mentions the result
    -- (`F0165`).
    if let some (sp, r) := block.resultMention? then err sp (Fren.Core.fnResultMentionMsg r)
    let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkNoBang n)
    liftMsg name.span (Fren.Core.checkFnName n)
    let module := (← get).module
    liftMsg written ((← get).table.checkFreshItem module n bang)
    lintName .function n name.span
    startDeclared
    let path := module ++ n
    modify fun s => { s with item := path }
    -- The `use`s of its block, in its scope, as a procedure's
    -- (`Reqs/Lang/Items#function-blocks`).
    declareMemberUses path block.uses
    -- Its block's `let`s that nothing needs, as a procedure's
    -- (`unused_variables`).
    for x in block.unusedLets do
      lint .unusedVariables x.span (Fren.Core.unusedVariableMsg (Name.mkSimple (declaredIdent x).1.name) false true)
    -- Its type parameters, which are abstract types within it, whether it
    -- is defined or not (`lang::generic_function`).
    let tps ← elabTypeParams typeParams
    if !tps.isEmpty then
      modify fun s => { s with fnTypeParams := some (path, tps), genericCalls := #[], pendingInsts := #[]
                               sorts := s.sorts ++ tps.mapIdx fun k p => Fren.Core.typeParamPath path k p }
    let (params, body) := lambdaMatchFunction params body
    let contract := !clauses.isEmpty
    -- A parameter is named if it has a type after `:`, or is a `Bool`
    -- written `x?` (`lang::function_params`).
    let named (p : Array Ident × Option (Array Ident)) :=
      p.2.isSome || (p.1.size == 1 && (declaredIdent p.1[0]!).1.name.endsWith "?")
    unless Fren.Core.functionParamsAccepted body.isSome contract params.size (params.filter named).size do
      let bad := (params.find? (named · != (body.isSome || contract))).map (·.1[0]!.span) |>.getD name.span
      err bad (Fren.Core.functionParamsMsg path body.isSome contract)
    -- The parameters, declared like a procedure's parameters, but for the function
    -- parameters, each with its position, which only a defined function
    -- has (`lang::function_type_place`).
    let fnParamsOf : StateT (Array (Nat × Name × Span × Fren.Core.FnTy)) M (Array CVar) := do
      let mut vars : Array CVar := #[]
      -- Distinct names (`lang::distinct_names`).
      -- By the names they declare, without the `!` of shadowing.
      let declared := params.map fun p => Name.mkSimple (declaredIdent p.1[0]!).1.name
      if let some k := (Fren.Core.repeatsAt declared)[0]? then
        err params[k]!.1[0]!.span (Fren.Core.dupParamMsg declared[k]!)
      for (p, ty?) in params, j in [0:params.size] do
        let x ← declare p[0]!
        let xn := Name.mkSimple x.name
        lintName .variable xn x.span
        if let some segs := ty?.filter (·[0]?.any (·.name == Parser.fnSeg)) then
          unless body.isSome do checkFnTypeSite .uninterpretedParameter segs
          let ft ← elabFnTy segs
          modify (·.push (j, xn, x.span, ft))
          continue
        let ptype ← varPTy ty? x
        let fact? ← factOf ptype (quote xn.toString)
        vars := vars.push { name := xn, role := .input, isPub := true, ty := ptype.ty, span := x.span, ptype, fact? }
      return vars
    let paramVars : M (Array CVar) := return (← fnParamsOf.run #[]).1
    -- A generic function's signature, with its type parameters as
    -- `Ty.param`, each inferred at applications from it
    -- (`lang::generic_signature`).
    let signature (ps : Array Ty) (rp : Fren.Core.PTy) (defined : Bool) : M Unit := do
      if tps.isEmpty then return
      let r := rp.ty
      let declared := ps.map (·.asParams path tps)
      if let some k := Fren.Core.firstUnmentioned? declared (r.asParams path tps) tps.size then
        err typeParams[k]!.span (Fren.Core.unmentionedTypeParamMsg n tps[k]!)
      let g : GenericFn := { params := tps, declared, result := r.asParams path tps, resultP := rp.asParams path tps, defined
                             file := (← get).file }
      modify fun s => { s with genericFns := s.genericFns.insert path g }
    match body with
    | none =>
      -- Generic or not, the `declare-fun` of the function itself; a generic
      -- one's is over its type parameters' sorts, for the checks of its
      -- contract, and each instance that an application uses has its own
      -- (`instantiate`).
      if !contract then
        let pps ← params.mapM (elabPTy ·.1)
        let ps := pps.map (·.ty)
        lintFnBools n name.span ps
        -- As for a variable, with the result type (`lang::bool_naming`),
        -- after the parameters, in source order.
        let rp ← varPTy result name
        signature ps rp false
        noteResultFact path rp
        modify fun s => { s with funs := s.funs.push (path, ps, rp.ty), funPTys := s.funPTys.insert path (pps, rp) }
      else
        let vars ← paramVars
        lintFnBools n name.span (vars.map (·.ty))
        let rp ← varPTy result name
        signature (vars.map (·.ty)) rp false
        noteResultFact path rp
        modify fun s => { s with funs := s.funs.push (path, vars.map (·.ty), rp.ty)
                                 funPTys := s.funPTys.insert path (vars.map (·.ptype), rp) }
        discard takeTables
        modify fun s => { s with outsideCore := false, guardedUsed := false, natApps := #[] }
        let clausesBefore := (← get).clauseDefs.size
        let (vars, props, sites) ← elabContract path n false vars clauses rp.ty name.span
        -- What its instances need (`instantiate`): its clauses, and the
        -- generic functions that they apply.
        if !tps.isEmpty then
          modify fun s => { s with
            genericFns := s.genericFns.insert path { (s.genericFns.find? path).getD default with
              calls := s.genericCalls, clauses := s.clauseDefs.extract clausesBefore s.clauseDefs.size } }
        noteBody n name.span vars (props, sites) path (generic := !tps.isEmpty)
        lintDeclared .function n name.span
        lintLines .function n name.span last
      modify fun s => { s with fnTypeParams := none }
    | some body =>
      let (vars, fnPs) ← fnParamsOf.run #[]
      lintFnBools n name.span (vars.map (·.ty))
      let rp ← varPTy result name
      let r := rp.ty
      -- The parameters in order, a function parameter's type standing in
      -- for its own (`HigherOrderFn.params`).
      let ptypes := Id.run do
        let mut out : Array Fren.Core.PTy := vars.map (·.ptype)
        for (j, _, _, ft) in fnPs do out := out.insertIdxIfInBounds j (.plain ft.result)
        return out
      modify fun s => { s with funPTys := s.funPTys.insert path (ptypes, rp) }
      -- Each type parameter is inferred at applications from the signature
      -- (`lang::generic_signature`), where a function parameter's type
      -- stands for its parameters' and its result's.
      let declared := vars.map (·.ty.asParams path tps)
      let fnDeclared := fnPs.flatMap fun (_, _, _, ft) => (ft.asParams path tps).params.push (ft.asParams path tps).result
      if let some k := Fren.Core.firstUnmentioned? (declared ++ fnDeclared) (r.asParams path tps) tps.size then
        err typeParams[k]!.span (Fren.Core.unmentionedTypeParamMsg n tps[k]!)
      if fnPs.isEmpty then signature (vars.map (·.ty)) rp true
      -- Each function parameter is an uninterpreted function for the
      -- function's own checks (`Reqs/Lang/HigherOrder#function-parameters`).
      let fnParams := fnPs.map fun (_, x, _, ft) => (x, ft, itemSym (path ++ x))
      for (_, x, _, ft) in fnPs do
        modify fun s => { s with funs := s.funs.push (path ++ x, ft.params, ft.result) }
      discard takeTables
      discard takeIndexes
      modify fun s => { s with outsideCore := false, guardedUsed := false, natApps := #[] }
      -- A first-order function that is not generic may apply itself, in a
      -- structural recursion (`lang::structural_recursion`).
      let selfRec? := if tps.isEmpty && fnPs.isEmpty then
        some (vars.map (·.name), ({ params := vars.map (·.ty), result := r } : Fren.Core.FnTy), itemSym path) else none
      -- The body is checked against the result type (`lang::checked`).
      let cx : ExprCtx := { vars, place := .prop, selfFn := if (← get).inSubset then none else some n, expected? := Fren.Core.ExprSite.functionBody.expected (some r) none, fnParams, selfRec? }
      modify fun s => { s with recUses := #[], recApps := #[], recMatches := #[] }
      let (smt, t) ← elabExpr cx body
      let uses := (← get).recUses
      let recursion := Fren.Core.recursion vars.size (uses.toList.map (·.2))
      if recursion matches .structural _ then
        if let some m := (← get).recMatches[0]? then err m (Fren.Core.recursiveMatchMsg path)
        modify fun s => { s with recursiveDefs := s.recursiveDefs.insert path }
      -- Keep independently elaborated conjunction leaves at their definition
      -- site, rather than substituting raw source syntax into a caller's scope.
      if body.conjunctionRoot || (observedMembers body).isSome || (← predicateClauses cx body).isSome then
        let leaves := if body.conjunctionRoot then body.clauseLeaves { name := "", span := body.span } else #[({ name := "", span := body.span }, body)]
        if true then
          let saved ← get
          let mut templates := #[]
          let mut nestedOccurrences : Std.HashMap Name Nat := {}
          for (label, expression) in leaves do
            discard takeIndexes
            discard takeTables
            let (formula, _) ← elabExpr cx expression
            let indexes ← takeIndexes
            let tables ← takeTables
            modify fun s => { s with itemBranches := #[], itemMemberGroups := #[] }
            annotateBranches cx (Name.mkSimple "#template") expression
            let own := ({
              file := saved.file
              name := label.name
              span := label.span
              formula := formula
              indexes := indexes
              tables := tables
              branches := (← get).itemBranches
              groups := (← get).itemMemberGroups
            } : NamedClause)
            if let some (nestedPath, nested) ← predicateClauses cx expression then
              let occurrence := nestedOccurrences.getD nestedPath 0 + 1
              nestedOccurrences := nestedOccurrences.insert nestedPath occurrence
              let nestedPrefix := Fren.Core.showPath nestedPath ++ "@" ++ toString occurrence
              for clause in nested do
                let name := (if label.name.isEmpty then "" else label.name ++ ".") ++ nestedPrefix ++ (if clause.name.isEmpty then "" else "." ++ clause.name)
                let rename (n : Name) := if !clause.name.isEmpty then n else Name.mkSimple ("#template." ++ nestedPrefix ++ (n.toString.dropPrefix? "#template" |>.getD ("." ++ n.toString)))
                templates := templates.push { clause with
                  name := name
                  indexes := indexes ++ clause.indexes
                  tables := tables ++ clause.tables
                  branches := clause.branches.map fun group => { group with members := group.members.map fun member => { member with name := rename member.name } }
                  groups := clause.groups.map fun group => { group with members := group.members.map fun member => { member with name := rename member.name } } }
            else templates := templates.push own
          modify fun s => { s with itemBranches := #[], itemMemberGroups := #[] }
          annotateBranches cx (Name.mkSimple "#template") body
          let whole : NamedClause := {
            file := saved.file
            name := ""
            span := body.span
            formula := smt
            branches := (← get).itemBranches
            groups := (← get).itemMemberGroups
          }
          set { saved with namedPredicates := saved.namedPredicates.insert path { sourcePath := path, params := vars.map (fun (v : CVar) => v.name), clauses := templates, whole? := some whole } }
      noteObligation cx .body body.span rp smt
      let bodyTables ← takeTables
      let bodyObligations ← takeIndexes
      liftMsg body.span (Fren.Core.checkType r t (some s!"note: `{n}` returns `{r.show}`"))
      lintBools body (← hidesIn cx)
      -- A parameter that only the contract mentions is used too.
      let mentioned := (mentions body ++ clauses.flatMap fun (_, _, e) => mentions e).map (·.getRoot)
      let mentioned := if fnPs.isEmpty then mentioned
        else mentioned ++ body.appliedNames ++ clauses.flatMap fun (_, _, e) => e.appliedNames
      let paramSpans := Id.run do
        let mut out := vars.map fun v => (v.name, v.span)
        for (j, x, sp, _) in fnPs do out := out.insertIdxIfInBounds j (x, sp)
        return out
      for (x, sp) in Fren.Core.unmentioned paramSpans mentioned do
        lint .unusedVariables sp (Fren.Core.unusedParamMsg x)
      modify fun s => { s with defs := s.defs.push (path, vars.map fun v => (v.name, v.ty), r, smt)
                               guardedItems := if s.guardedUsed then s.guardedItems.insert path else s.guardedItems }
      -- What its applications need to unfold it (`elabHigherOrderApp`):
      -- its contract may apply it, to its own parameters.
      let hofParams := Id.run do
        let mut out : Array (Name × String × Fren.Core.HoParam) := vars.map fun v => (v.name, quote v.name.toString, .value (v.ty.asParams path tps))
        for (j, x, _, ft) in fnPs do out := out.insertIdxIfInBounds j (x, itemSym (path ++ x), .function (ft.asParams path tps))
        return out
      if !fnPs.isEmpty then
        let h : HigherOrderFn := { typeParams := tps, params := hofParams, result := r.asParams path tps, body := smt
                                   calls := (← get).genericCalls }
        modify fun s => { s with hofs := s.hofs.insert path h }
        unless isPub do
          for (j, x, sp, _) in fnPs do
            let r : Fren.Core.HofParamRecord :=
              { path, index := j, name := x, generic := !tps.isEmpty, level := (← get).levels.get .needlessHigherOrder }
            modify fun s => { s with hofParams := s.hofParams.push (r, sp) }
      let clausesBefore := (← get).clauseDefs.size
      let (_, props, sites) ← if contract then elabContract path n true vars clauses r name.span fnParams (paramSpans.map (·.1)) else pure (vars, #[], #[])
      if !fnPs.isEmpty then
        let st ← get
        let newClauses := st.clauseDefs.extract clausesBefore st.clauseDefs.size
        let pres := ((st.contracts.find? path).map (·.pres)).getD #[] |>.filterMap fun (pn, sym) =>
          (newClauses.find? (·.1 == sym)).map fun (_, _, body) => (pn, body)
        let calls := st.genericCalls
        modify fun s => { s with hofs := s.hofs.modify path (fun h => { h with pres, calls }), fnTypeParams := none }
      -- What its instances need (`instantiate`).
      if !tps.isEmpty && fnPs.isEmpty then
        modify fun s => { s with
          genericFns := s.genericFns.insert path { (s.genericFns.find? path).getD default with
            vars := vars.map fun v => (v.name, v.ty), body := smt, calls := s.genericCalls
            clauses := s.clauseDefs.extract clausesBefore s.clauseDefs.size }
          fnTypeParams := none }
        for args in (← get).pendingInsts do discard (instantiate path args)
        modify fun s => { s with pendingInsts := #[] }
      modify fun s => { s with tables := bodyTables }
      let st ← get
      let pres := ((st.contracts.find? path).map (·.pres)).getD #[]
      let selfSites := st.recApps.flatMap fun (sp, args, gs) =>
        pres.map fun (pn, sym) =>
          let p := s!"({sym} {" ".intercalate args.toList})"
          (sp, Fren.Core.TableGoal.precondition path pn, if gs.isEmpty then p else s!"(=> {conj gs} {p})")
      modify fun s => { s with tables := s.tables ++ selfSites }
      noteBody n name.span vars (props, sites) path bodyObligations
      lintDeclared .function n name.span
      lintLines .function n name.span last
    unless isPub do
      modify fun s =>
        let r : Fren.Core.ItemRecord :=
          { what := .function, path, level := s.levels.get .deadCode, singleCall? := body.map fun _ => s.levels.get .singleCallFn }
        { s with items := s.items.push (r, name.span) }
    modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
  | .comp isPub name header members close spans openStop => do
    -- Its declaration and line lints are about its name, without its `!`.
    let shown := (declaredIdent name).1
    modify fun s => { s with item := s.module ++ Name.mkSimple shown.name }
    -- Its `use`s end with it, even when it has an error.
    modify fun s => { s with inCompBody := false }
    try elabComp isPub name header members spans openStop
    catch e =>
      modify (fun s => { s.keepLints e.state with scope := s.module })
      -- Its declaration and line lints, after an error in its members.
      if e.state.inCompBody then
        lintDeclared .component (Name.mkSimple shown.name) shown.span
        lintLines .component (Name.mkSimple shown.name) shown.span close
      throw { e with state := ← get }
    lintDeclared .component (Name.mkSimple shown.name) shown.span
    lintLines .component (Name.mkSimple shown.name) shown.span close
  | .const isPub name ty value => do
    modify fun s => { s with contractIndexes := #[], itemBranches := #[], itemMemberGroups := #[] }
    let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkConstName n)
    let module := (← get).module
    liftMsg written ((← get).table.checkFreshItem module n bang)
    lintName .constant n name.span
    let pt ← elabPTy ty
    let t := pt.ty
    -- Its value must be known (`lang::constant`): first its type, then,
    -- once the functions it applies count as used, its value.
    let abstract := t matches .abstract _
    unless Fren.Core.constantAccepted abstract false do
      err (ty[0]!.span.to ty.back!.span) (Fren.Core.unknownConstantMsg abstract)
    let before := (← get).applied.size
    discard takeTables
    discard takeIndexes
    modify fun s => { s with outsideCore := false, guardedUsed := false, natApps := #[] }
    let cx : ExprCtx := { vars := #[], place := .prop, expected? := Fren.Core.ExprSite.constantValue.expected (some t) none }
    let (smt, t') ← elabExpr cx value
    noteObligation cx .constant value.span pt smt
    noteBody n name.span #[] (obligations := ← takeIndexes)
    let applies := (← get).applied.extract before
    unless Fren.Core.constantAccepted abstract applies.isEmpty.not do
      err applies[0]! (Fren.Core.unknownConstantMsg abstract)
    liftMsg value.span (Fren.Core.checkType t t' (some s!"note: `{n}` has type `{t.show}`"))
    lintBools value (← hidesIn cx)
    let path := module ++ n
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .constant, path, level := s.levels.get .deadCode }, name.span) }
    let int? ← if t == .int || t == .nat then intConstValue? { vars := #[], place := .prop } value else pure none
    modify fun s => { s with
      table := s.table.addItem { kind := .constItem, path, isPub, owner := s.module }
      consts := s.consts.insert path (smt, t)
      guardedItems := if s.guardedUsed then s.guardedItems.insert path else s.guardedItems
      constInts := match int? with | some v => s.constInts.insert path v | none => s.constInts }
  | .global name binders body => do
    modify fun s => { s with item := s.module ++ Name.mkSimple (declaredIdent name).1.name }
    elabGlobal name binders body
  | .globalBlock name header members close spans openStop => do
    let shown := (declaredIdent name).1
    modify fun s => { s with item := s.module ++ Name.mkSimple shown.name }
    modify fun s => { s with inCompBody := false }
    try elabComp false name header members spans openStop (global := true)
    catch e =>
      modify (fun s => { s.keepLints e.state with scope := s.module })
      if e.state.inCompBody then
        lintDeclared .global (Name.mkSimple shown.name) shown.span
        lintLines .global (Name.mkSimple shown.name) shown.span close
      throw { e with state := ← get }
    lintDeclared .global (Name.mkSimple shown.name) shown.span
    lintLines .global (Name.mkSimple shown.name) shown.span close
  | .law name params body => do
    -- Only a trait's members are laws, which the parser reads only there.
    modify fun s => { s with item := s.module ++ Name.mkSimple (declaredIdent name).1.name }
    elabLaw name params body
  | .«trait» isPub name members _ => elabTrait isPub name members
  | .claim tested segs texts => do
    let path ← match ← resolve segs with
      | .item { kind := .compItem, path, .. } => pure path
      | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.notACompMsg r)
    if !tested then
      for (why, span) in texts do liftMsg span (Fren.Core.checkTrusted why)
    modify fun s => { s with claims := s.claims.push { file := s.file, tested, comp := path, texts } }
  | .check none => pure ()
  | .check (some segs) => do
    match ← resolve segs with
    | .item { kind := .compItem, .. } | .item { kind := .expectItem, .. } => pure ()
    | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.wrongKindMsg "a procedure or a global expectation" r)
  | .lintSetting stx opt value valueSpan removal body? => do
    if opt.name == "fren.enumeration.size" then
      -- Like `fren.evidence`: for the item after `in`, or the rest of the
      -- file (`Reqs/Check#checking-by-enumeration`).
      let prev := (← get).enumSize
      let n := value.toNat!
      if n > Fren.Core.Enumeration.maxSize then
        modify fun s => { s with diags := s.diags.push { file := s.file, span := valueSpan, msg := Fren.Core.Enumeration.sizeTooLargeMsg n } }
      else modify fun s => { s with enumSize := n }
      if let some body := body? then
        elabItem body
        modify fun s => { s with enumSize := prev }
      return
    if opt.name == "fren.evidence" then
      -- Like a lint setting: for the item after `in`, or the rest of the file.
      let prev := (← get).evidence?
      -- An invalid value is reported here, once, and does not stop the
      -- items it would set (`Reqs/Check#checking-by-testing`).
      if (Fren.Core.evidenceTested? value).isNone then
        modify fun s => { s with diags := s.diags.push { file := s.file, span := valueSpan, msg := Fren.Core.invalidEvidenceMsg value } }
      if let some body := body? then
        -- Before a function or a constant, whose checks are the solver's,
        -- only the solver can be set (`F0215`), and the item is elaborated
        -- as though it were (`Fren.Core.dispatchOf`).
        if let (some (what, item), some ev) := (evidenceTarget? body, Fren.Core.evidenceOf? value) then
          unless ev.settable item do
            modify fun s => { s with diags := s.diags.push { file := s.file, span := stx, msg := Fren.Core.itemEvidenceMsg what value } }
            elabItem body
            return
        modify fun s => { s with evidence? := some (value, valueSpan) }
        elabItem body
        modify fun s => { s with evidence? := prev }
      else modify fun s => { s with evidence? := some (value, valueSpan) }
      return
    let some rest := opt.name.dropPrefix? "fren.lint." | internal opt.span "not a lint option"
    let some target := Fren.Core.LintTarget.ofName? rest.toString | err opt.span (Fren.Core.unknownLintMsg rest.toString)
    let some requested := LintLevel.ofName? value | err valueSpan (Fren.Core.invalidLevelMsg value)
    -- What the body restores; not the whole state, which would make each
    -- change to it while the body is elaborated a copy.
    let levels := (← get).levels
    let settingStart? := (← get).settingStart?
    -- A forbidden lint's setting decides whether this one is accepted.
    noteSettingsSeen (Fren.Core.settingLints ++ target.members.filter fun l => (levels.get l).level == .forbid)
    if let some lint := target.rejectedBy? (levels.get · |>.level) requested then
      err stx (Fren.Core.forbiddenMsg target lint requested)
    -- `allow_attributes` (`lint::allow_attributes`), at the level before the setting.
    let (allows, fix) := Fren.Core.allowAttributes requested (target == .lint .unfulfilledExpectations)
    if allows then lintFix .allowAttributes valueSpan (Fren.Core.allowAttributesMsg target fix)
    let expectation? ← if requested == .expect then do
        let e : Fren.Core.ExpectationRecord := { target, level := levels.get .unfulfilledExpectations }
        let k := (← get).expectations.size
        modify fun s => { s with expectations := s.expectations.push (e, stx),
                                 expectationRemovals := s.expectationRemovals.push removal }
        pure (some k)
      else pure none
    -- `unused_lint_setting` (`lint::unused_lint_setting`).
    let r : Fren.Core.SettingRecord := { target, requested, level := levels.get .unusedLintSetting }
    let setting := (← get).settings.size
    modify fun s => { s with settings := (Fren.Core.SettingRecord.replace s.settings s.levels.get target requested).push (r, stx)
                             settingRemovals := s.settingRemovals.push removal }
    let set : LevelInEffect := { level := requested, isSet := true, group? := target.group?, expectation?
                                 setting? := some setting }
    for lint in target.members do
      modify fun s => { s with levels := s.levels.set lint set }
    if let some body := body? then
      modify fun s => { s with settingStart? := some (settingStart?.getD stx.start) }
      elabItem body
      modify fun s => { s with levels, settingStart? }

/-- Elaborates a trait (`Reqs/Lang/Traits`): its carrier `Self`, an
abstract type; its methods, uninterpreted functions, each seen by those
after it; its laws; and its expectations, global expectations whose checks
have the laws among their hypotheses (`Fren.Core.Comp.laws`). Each member
is in the trait's scope, whose names shadow its module's, and reports its
own first static error. -/
partial def elabTrait (isPub : Bool) (name : Ident) (members : Array Item) : M Unit := do
  let (name, bang, written) := ((declaredIdent name).1, (declaredIdent name).2, name.span)
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "trait" n)
  let module := (← get).module
  liftMsg written ((← get).table.checkFreshItem module n bang)
  lintName .trait n name.span
  let path := module ++ n
  let selfPath := path ++ Fren.Core.selfName
  -- What each member is, under its settings (`lang::trait_member`).
  let rec under : Item → Item
    | .lintSetting _ _ _ _ _ (some b) => under b
    | i => i
  let kindOf : Item → Fren.Core.TraitMember × Bool × Bool × Bool × Option Ident
    | .function isPub f tps _ _ body _ _ block =>
      (if body.isSome then .definedFunction else .method, isPub, !tps.isEmpty, !block.uses.isEmpty, some f)
    | .law f .. => (.law, false, false, false, some f)
    | .global f .. => (.expectation, false, false, false, some f)
    | .globalBlock f _ ms .. => (.expectation, false, false, ms.any (· matches .use .. | .useGroup ..), some f)
    | .comp isPub f .. => (.other "procedures", isPub, false, false, some f)
    | .enum .. | .record .. | .newtype .. => (.other "enums or structs", false, false, false, none)
    | .abstractType .. | .typeAlias .. | .subsetType .. => (.other "types", false, false, false, none)
    | .const .. => (.other "constants", false, false, false, none)
    | .mod .. => (.other "modules", false, false, false, none)
    | .use .. | .useGroup .. => (.other "`use`s", false, false, false, none)
    | .trait .. => (.other "traits", false, false, false, none)
    | .claim .. => (.other "claims", false, false, false, none)
    | .check .. | .lintSetting .. => (.other "commands", false, false, false, none)
  let spanOf : Item → Span
    | .function _ f .. | .law f .. | .global f .. | .globalBlock f .. | .comp _ f .. | .enum _ f .. | .record _ f ..
    | .newtype _ f .. | .abstractType _ f | .typeAlias _ f _ | .subsetType _ f .. | .const _ f .. | .trait _ f .. => f.span
    | .mod _ segs => segs[0]!.span
    | .use sp .. | .useGroup sp .. => sp
    | .claim _ segs _ => segs[0]!.span
    | _ => name.span
  for m in members do
    let (kind, isPubM, generic, uses, _) := kindOf (under m)
    if let some msg := Fren.Core.traitMemberMsg? path kind isPubM generic uses then err (spanOf (under m)) msg
  -- Distinct names, with the carrier's (`lang::distinct_names`).
  let named := members.filterMap fun m => (kindOf (under m)).2.2.2.2
  let declared := #[Fren.Core.selfName] ++ named.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err named[k - 1]!.span (Fren.Core.dupTraitMemberMsg declared[k]!)
  -- The trait, and its carrier, which its members see first.
  let traitItem : Fren.Core.Item := { kind := .traitItem, path, isPub, owner := module }
  let selfItem : Fren.Core.Item := { kind := .typeItem, path := selfPath, isPub := true, owner := path }
  let selfUse : Fren.Core.UseDef := { module, scope := path, target := selfPath, glob := false }
  modify fun s => { s with
    table := ((s.table.addItem traitItem).addItem selfItem).addUse selfUse
    sorts := s.sorts.push selfPath
    traitLaws := #[] }
  -- Each member, in the trait's scope, reporting its own first error, and
  -- without the item's trailing commas, which the trait reported.
  let commas := (← get).trailingCommas
  let member (m : Item) : M Unit := do
    -- Its own errors alone stop what follows them in it, as an item's do.
    let errors := (← get).itemErrors
    modify fun s => { s with module := path, scope := path, trailingCommas := #[], itemErrors := #[] }
    discard (attempt (elabItem m))
    modify fun s => { s with module, scope := module, trailingCommas := commas, itemErrors := errors ++ s.itemErrors }
  let isMethod (m : Item) := (kindOf (under m)).1 == .method
  let isLaw (m : Item) := (kindOf (under m)).1 == .law
  -- The methods, as functions of the trait, each in scope after it; one is
  -- never dead, being part of the trait.
  for m in members.filter isMethod do
    let some f := (kindOf (under m)).2.2.2.2 | continue
    let rec asPub : Item → Item
      | .lintSetting a b c d e (some i) => .lintSetting a b c d e (some (asPub i))
      | .function _ f tps ps r b cs l blk => .function true f tps ps r b cs l blk
      | i => i
    let before := (← get).itemErrors.size
    member (asPub m)
    if (← get).itemErrors.size == before then
      let u : Fren.Core.UseDef := { module, scope := path, target := path ++ Name.mkSimple (declaredIdent f).1.name, glob := false }
      modify fun s => { s with table := s.table.addUse u }
  for m in members.filter isLaw do member m
  let laws := (← get).traitLaws
  -- The expectations, each checked with the laws among its hypotheses.
  for m in members.filter fun m => !isMethod m && !isLaw m do
    let before := (← get).globals.size
    member m
    let st ← get
    if st.globals.size > before then
      let c := st.globals.back!
      -- Its checks are the solver's (`F0215`).
      if c.tested.any || c.enumerated.any then
        let sp := ((kindOf (under m)).2.2.2.2.map (·.span)).getD name.span
        discard (attempt (α := Unit) (err sp (Fren.Core.traitEvidenceMsg (if c.tested.any then "random" else "enumerated"))))
      let c := { c with laws := laws.map fun (l, f, _) => (l, f)
                        decidable := c.decidable && laws.all (·.2.2.1)
                        natApps := c.natApps ++ laws.flatMap (·.2.2.2.1)
                        guarded := c.guarded || laws.any (·.2.2.2.2) }
      modify fun s => { s with globals := s.globals.pop.push c }
  modify fun s => { s with traitLaws := #[] }
end

/-- The text of the current file at `sp`. -/
def State.text (s : State) (sp : Span) : String := String.ofList (s.src.extract sp.start sp.stop).toList

/-- `use pre::a`, or `use pre::{a, b}` for several names. -/
def useText (pre : String) (names : Array String) : String :=
  match names with
  | #[n] => s!"use {pre}::{n}"
  | ns => s!"use {pre}::\{{", ".intercalate ns.toList}}"

/-- The edits of `fren fix` in the current file (`Reqs/Lint#fixing-lints`),
given the lints that fire in it, and the lints they fix, each with the
span of its message. -/
def State.fixes (s : State) (fired : Array (Lint × Span)) :
    Array (Fren.Core.Range × String) × Array (Lint × Span) := Id.run do
  let fixU := s.fixing.contains .unusedImports
  let fixG := s.fixing.contains .globImports
  let fires (l : Lint) (sp : Span) := fired.contains (l, sp)
  let delete (sp : Span) := (Fren.Core.deletionRange s.src (toRange sp), "")
  let mut edits := #[]
  let mut fixed := #[]
  let items := s.useLocs.foldl (init := #[]) fun acc l => if acc.contains l.item then acc else acc.push l.item
  for item in items do
    let members := (Array.range s.useLocs.size).filter (s.useLocs[·]!.item == item)
    let path (i : Nat) := s.useRecords[i]!.2
    match s.useLocs[members[0]!]!.pre? with
    | none =>
      let i := members[0]!
      let u := s.useRecords[i]!.1
      let names := u.globNames s.used
      match Fren.Core.importFix (fires .unusedImports (path i)) (fires .globImports (path i)) fixU fixG names.size with
      | .remove =>
        edits := edits.push (delete s.useLocs[i]!.removal)
        fixed := fixed ++ #[(.unusedImports, path i), (.globImports, path i)]
      | .byName =>
        edits := edits.push (toRange item, useText (s.text s.useLocs[i]!.path) (names.map toString))
        fixed := fixed.push (.globImports, path i)
      | .keep => pure ()
    | some pre =>
      let removed := members.filter fun i => fixU && fires .unusedImports (path i)
      if removed.isEmpty then continue
      fixed := fixed ++ removed.map (.unusedImports, path ·)
      let kept := members.filter (!removed.contains ·)
      edits := edits.push <| if kept.isEmpty then delete s.useLocs[members[0]!]!.removal
        else (toRange item, useText (s.text pre) (kept.map (s.text s.useLocs[·]!.path)))
  let fixes (l : Lint) (sp : Span) := s.fixing.contains l && fires l sp
  for f in s.lintFixes do
    if fixes f.lint f.span && !(f.unless?.any fun (l, sp) => fixes l sp) then
      edits := edits ++ f.edits
      fixed := fixed.push (f.lint, f.span)
  if s.fixing.contains .unfulfilledExpectations then
    for (_, sp) in s.expectations, removal in s.expectationRemovals do
      if fires .unfulfilledExpectations sp then
        edits := edits.push (if removal == sp then delete sp else (toRange removal, ""))
        fixed := fixed.push (.unfulfilledExpectations, sp)
  if s.fixing.contains .unusedLintSetting then
    for (_, sp) in s.settings, removal in s.settingRemovals do
      if fires .unusedLintSetting sp then
        edits := edits.push (if removal == sp then delete sp else (toRange removal, ""))
        fixed := fixed.push (.unusedLintSetting, sp)
  return (edits, fixed)

/-- Records the reports of `manual_nat` in the file that no call or
refinement in it keeps an `Int` (`lint::manual_nat`). Their fix is a
suggestion, which `fren fix` does not make. -/
def finishNat : StateM State Unit := do
  let s ← get
  let rs := s.natReports.filter fun r => !s.natKept.contains (r.comp, r.var)
  set { s with lintReports := s.lintReports ++ rs.map NatReport.report }

/-- The lints of the file just elaborated, at its end, and the edits that
fix them, if `fren fix` fixes any. -/
def finishLints : StateM State Unit := do
  finishNat
  let s ← get
  let atEnd := Lint.all.filterMap (s.levels.get · |>.setting?)
  let (reports, fulfilled) := Fren.Core.finishReports
    (s.lintReports ++ Fren.Core.importReports s.useRecords s.used true ++ Fren.Core.deadCodeReports s.items s.usedItems
      ++ Fren.Core.unusedAssumptionReports s.assumptions s.globalReads
      ++ Fren.Core.unusedSettingReports s.settings s.seenSettings atEnd true
      ++ Fren.Core.singleCallReports s.items s.usedItems
      ++ Fren.Core.needlessHigherOrderReports s.hofParams (s.fnArgs.map (·.1)))
  let (unfulfilled, _) := Fren.Core.finishReports (Fren.Core.expectationReports s.expectations fulfilled true)
  let all := reports ++ unfulfilled
  let (edits, fixed) := s.fixes (all.map fun (r, _) => (r.lint, r.ref))
  let diags := all.map fun (r, severity) =>
    { file := s.file, span := r.ref, severity, msg := r.msg, lint? := some r.lint
      fixed := fixed.contains (r.lint, r.ref) : Diag }
  set { s with diags := s.diags ++ diags, edits := s.edits ++ edits.map (s.file, ·) }

/-- The trailing commas among `toks` that `unnecessary_trailing_comma`
reports, each with the `}` or `]` after it
(`lint::unnecessary_trailing_comma`). -/
def trailingCommas (toks : Array Token) : Array (Span × String) :=
  let texts := toks.map fun t => ((match t.tok with | .kw k => k | _ => ""), t.nlBefore)
  (Fren.Core.trailingCommas texts).map fun i => (toks[i]!.span, texts[i + 1]!.1)

/-- The index of the first of `found`, which is in order of where each
starts, that starts at `pos` or after, or its size if none does. -/
def firstFrom (found : Array (Lint × Span × Msg)) (pos : Nat) : Nat :=
  go 0 found.size
where
  go (lo hi : Nat) : Nat :=
    if h : lo < hi then
      let mid := (lo + hi) / 2
      if found[mid]!.2.1.start < pos then go (mid + 1) hi else go lo mid
    else lo
  termination_by hi - lo

/-- Elaborates the items of one file, whose text is `src`, and which start
at `starts`, collecting an error per failed item, where `trailingCommas`
are the commas that `unnecessary_trailing_comma` reports, and `found` the
file's `literalLints`, in order of where each starts. `fren fix` fixes the lints `fixing` in it. -/
def elabFile (file : Nat) (src : Array Char) (items : Array Item) (starts : Array Nat)
    (trailingCommas : Array (Span × String)) (found : Array (Lint × Span × Msg)) (fixing : Array Lint := #[])
    (module : Name := .anonymous) :
    StateM State Unit := do
  modify fun s => { s with file, src, fixing, module, scope := module, levels := s.cliLevels, useRecords := #[], evidence? := none,
                           enumSize := Fren.Core.Enumeration.defaultSize,
                           used := #[], expectations := #[], lintReports := #[], useLocs := #[],
                           expectationRemovals := #[], items := #[], usedItems := #[], lintFixes := #[],
                           hofParams := #[], fnArgs := #[],
                           globalTexts := #[], natReports := #[], natKept := #[], settings := #[], settingRemovals := #[], seenSettings := #[],
                           assumptions := #[], globalReads := #[], trailingCommas }
  for item in items, k in [0:items.size] do
    -- An item has the literals and comments up to the next item, and the
    -- first, those before it too, and those that a `set_option` before it
    -- left.
    let start := starts[k]?.getD 0
    let stop := starts[k + 1]?.getD src.size
    let left ← if k > 0 && items[k - 1]! matches .lintSetting .. then pure (← get).literals else pure #[]
    -- `found` is in order of where each starts, so those that start in
    -- `[start, stop)` are a slice of it.
    let lo := if k == 0 then 0 else firstFrom found start
    let literals := left ++ found.extract lo (firstFrom found stop)
    modify fun s => { s with itemStart := start, literals, itemSpan := { start, stop } }
    let s ← get
    match (elabItem item).run s with
    | .ok ((), s') =>
      if s'.itemErrors.isEmpty then set s'
      else set { s.keepLints s' with diags := s.diags ++ s'.itemErrors }
    | .error f => set { s.keepLints f.state with diags := s.diags ++ f.diags }
  finishLints

/-- The file id of the prelude's items: no file that the `fren` command is
given has it, so that nothing of the prelude's is taken for a spec's. -/
def preludeFile : Nat := 1000000

/-- `st` with the prelude elaborated into it, before every spec
(`Reqs/Lang/Prelude`): its items, in the prelude's module, and none of its
messages. It has none: an error in it, as one that it does not parse, is
an internal error of every spec. -/
def State.withPrelude (st : State) : State :=
  let chars := Fren.Core.preludeSource.toList.toArray
  let broken (what : String) : State :=
    { st with diags := st.diags.push { file := 0, span := default, msg := Msg.internal s!"the prelude {what}" } }
  match lexWithComments chars with
  | .error e => broken s!"does not lex: {e.msg.headline}"
  | .ok (toks, _) => match parseItems toks chars with
    | .error e => broken s!"does not parse: {e.msg.headline}"
    | .ok (items, starts) =>
      let st' := (elabFile preludeFile chars items starts #[] #[] (module := Fren.Core.preludeModule) |>.run st).2
      match (st'.diags.extract st.diags.size st'.diags.size).find? (·.severity == .error) with
      | some d => broken s!"has an error: {d.msg.headline}"
      | none => { st' with diags := st.diags, file := 0, module := .anonymous, scope := .anonymous }

/-- Whether the queries of `c` may quantify over a collection's elements,
as the constraints of its variables' types, the facts of the applications
it makes, and the obligations it asks may: they then set `fmf-bound`
(`Fren.Core.boundedOptions`). It is read from the types, not the formulas,
as the Lean front end's `bounded` is. -/
def State.bounded (s : State) (c : CComp) : Bool :=
  c.guarded || c.vars.any (fun v => v.fact?.isSome && (v.ptype.cons s.shapeOf).any (·.quantifies))
    || c.indexes.any (fun (_, _, _, _, t) => t.any (·.2))
    || c.insts.any (·.bounded)
    || c.natApps.any fun app => ((quotedSymbols (peelLets app))[0]?).any fun h => s.quantifiedFns.contains (quote h)

/-- A declaration of the prelude: its SMT-LIB text, and the names of the
quoted symbols that it declares. -/
structure PreludeDecl where
  text : String
  syms : Array String
  recursion? : Option (Array String × String) := none
  domain : Array String := #[]
  deriving Inhabited, BEq

/-- `(declare-sort ...)` for every abstract type, `(declare-datatype ...)`
for every enum and record, in order, since each may contain those before
it, `(declare-fun ...)` for every uninterpreted function, and
`(define-fun ...)` for every defined function, in order, since each may
apply those before it, and then for every clause of a contract. -/
def State.prelude (s : State) : Array PreludeDecl :=
  let unquote (sym : String) : String := if sym.startsWith "|" then ((sym.drop 1).dropEnd 1).toString else sym
  let sorts := s.sorts.map fun p => { text := s!"(declare-sort {itemSym p} 0)\n", syms := #[unquote (itemSym p)] }
  -- A datatype declares its constructors and selectors too.
  let enums := s.datatypes.map fun d => { text := d.text, syms := d.syms }
  let funs := s.funs.map fun (p, ps, r) =>
    -- An instance of a generic function has a symbol of its own.
    let sym := (s.instSyms.find? p).getD (itemSym p)
    { text := s!"(declare-fun {sym} ({" ".intercalate (ps.toList.map (·.sort))}) {r.sort})\n", syms := #[unquote sym] }
  let defs := s.defs.map fun (p, ps, r, body) =>
    let binders := " ".intercalate (ps.toList.map fun (x, t) => s!"({quote x.toString} {t.sort})")
    -- An instance of a generic function has a symbol of its own.
    let sym := (s.instSyms.find? p).getD (itemSym p)
    if s.recursiveDefs.contains p then
      ({ text := s!"(declare-fun {sym} ({" ".intercalate (ps.toList.map (·.2.sort))}) {r.sort})\n"
         syms := #[unquote sym], recursion? := some (ps.map (quote ∘ toString ∘ Prod.fst), body)
         domain := ((s.bodies.find? (·.fn? == some p)).map fun b => b.vars.filterMap (·.fact?)).getD #[] } : PreludeDecl)
    else
      { text := s!"(define-fun {sym} ({binders}) {r.sort} {body})\n", syms := #[unquote sym] }
  -- After every function, since a clause may apply its own and those
  -- declared before it.
  let clauses := s.clauseDefs.map fun (sym, ps, body) =>
    let ps := " ".intercalate (ps.toList.map fun (x, t) => s!"({quote x.toString} {t.sort})")
    { text := s!"(define-fun {sym} ({ps}) Bool {body})\n", syms := #[unquote sym] }
  sorts ++ enums ++ funs ++ defs ++ clauses

/-- Of each uninterpreted function, by its SMT-LIB symbol: whether its
result is a `Nat`, and its contract, for the facts that its applications
bring (`appFactsOf`). -/
def State.appFuns (s : State) : Std.HashMap String (Bool × Contract) :=
  (s.funs ++ s.defs.filterMap (fun (p, ps, r, _) => if s.recursiveDefs.contains p then some (p, ps.map (·.2), r) else none)).foldl (init := {}) fun m (p, _, r) =>
    m.insert ((s.instSyms.find? p).getD (itemSym p)) (r == .nat, (s.contracts.find? p).getD {})

/-- Of each uninterpreted function with postconditions, by its SMT-LIB
symbol, its path: the function whose contract's realizability the checks
whose queries apply it rest on (`Fren.Core.appFactsWith`). Not instances
of generic functions, whose premise is not applied yet (#522), nor
recursive functions, which are defined. -/
def State.contractFns (s : State) : Std.HashMap String Name :=
  s.funs.foldl (init := {}) fun m (p, _, _) =>
    if s.instSyms.contains p || s.genericFns.contains p then m
    else match s.contracts.find? p with
      | some k => if k.posts.isEmpty then m else m.insert (itemSym p) p
      | none => m

/-- Each instance that the spec's items use of a generic function without a
body, with where its contract is checked (`Fren.Core.instanceSites`). -/
def State.instanceSites (s : State) : Array (Fren.Core.InstanceSite × Name × Array Ty) :=
  Fren.Core.instanceSites s.genericUses (fun g => ((s.genericFns.find? g).map (·.params)).getD #[])
    fun g => (s.genericFns.find? g).bind fun gf => if gf.defined then none else some gf.file

/-- The whole prelude, as one script. -/
def State.preludeText (s : State) : String := String.join (s.prelude.toList.map (·.text))

end FrenCli
