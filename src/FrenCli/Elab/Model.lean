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
import FrenCore.Induction
import FrenCore.Lint
import FrenCore.Mentions
import FrenCore.Names
import FrenCore.Patterns
import FrenCore.Quantifier
import FrenCore.Recursion
import FrenCore.Regex
import FrenCore.SeqElems
import FrenCore.SubsetTypes
import FrenCore.Symbols
import FrenCore.Trace
import FrenCore.Traits
import FrenCore.Ty
import FrenCore.TypeFacts
import FrenCore.Typing
-- keep-sorted end

/-!
# State and SMT-LIB data for `.fren` elaboration

Symbols, datatype declarations, compiled procedures, diagnostics and the
elaboration state shared by expression and item elaboration. Expression
helpers and their context are in `FrenCli.Elab.ExprSupport`.
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
  /-- The written constraint whose evidence applies to this generated leaf. -/
  evidenceOwner? : Option Name := none
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
  /-- For a global expectation, the functions generated for induction on
  its parameters, by its claims (`Reqs/Lang/Recursion#induction`): each
  claim's name, with the paths of its functions, one for each candidate,
  in order, whose bodies are in `State.inductionBodies`. -/
  inductions : Array (Name × Array Name) := #[]
  /-- For an expectation of a trait: the trait's laws, each a closed
  formula (`Fren.Core.Comp.laws`), and the trait. -/
  laws : Array (Name × String) := #[]
  lawsOf : Name := .anonymous
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
does not quote. It reads characters, slowly, and nothing but the tests
calls it: it is the reference that `FrenTest.QuotedSymbols` checks the
byte readers `substQuoted` and `quotedSymbols` against, so a change to
how symbols are read changes it and them together. -/
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

/-- Replaces each quoted symbol of `smt` with `f` of its name: the text
of `quotedPieces smt`, each name replaced by `f` of it. It reads the UTF-8
bytes, as `quotedSymbols` does, and copies the text between symbols a run
at a time, where `quotedPieces` makes a list of the text's characters and
builds its pieces a character at a time. `"` and `|` are ASCII, and no
byte of a character that is not ASCII is one of them, so it cuts the text
only at character boundaries: each run and each name is whole characters,
and the bytes it puts together are UTF-8, which `String.fromUTF8!` accepts. -/
def substQuoted (f : String → String) (smt : String) : String := Id.run do
  let bs := smt.toUTF8
  let mut out := ByteArray.emptyWithCapacity bs.size
  -- Where the text since the last symbol starts.
  let mut start := 0
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
      out := bs.copySlice start out out.size (i - start) false
      out := out ++ (f (String.fromUTF8! (bs.extract (i + 1) j))).toUTF8
      i := j + 1
      start := i
    else
      i := i + 1
  out := bs.copySlice start out out.size (bs.size - start) false
  return String.fromUTF8! out

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
  that bring facts, whether it sets `fmf-bound`, and whether `undecidable`
  is an error in it (`Reqs/Lang/Traits`). -/
  traitLaws : Array (Name × String × Bool × Array String × Bool × Bool) := #[]
  /-- A trait's members are being elaborated. -/
  inTrait : Bool := false
  /-- Each uninterpreted function's parameter and result types, in order. -/
  funs : Array (Name × Array Ty × Ty) := #[]
  /-- Each defined function's parameters and result type, and its body over
  the parameters, in order. -/
  defs : Array (Name × Array (Name × Ty) × Ty × String) := #[]
  namedPredicates : NameMap NamedPredicate := {}
  namedOccurrences : Std.HashMap String Nat := {}
  contractIndexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) := #[]
  /-- Structural recursions, used opaquely with one-step ground equations:
  each instance of a generic one too, by its name (`instantiate`). -/
  recursiveDefs : Std.HashSet Name := {}
  /-- Of each structural recursion, by its path, the position of its
  decreasing parameter (`lang::structural_recursion`). -/
  recursiveDecreasing : Std.HashMap Name Nat := {}
  /-- Of the item being elaborated, the variables that are the argument at
  the decreasing parameter of an application of a structural recursion
  in it, written as their names (`lang::induction_candidate`). -/
  inductionArgs : Array Name := #[]
  /-- The bodies of the functions generated for induction on global
  expectations' parameters, by their paths (`CComp.inductions`), which
  are checked only for those expectations, never as functions of the
  spec's. -/
  inductionBodies : Std.HashMap Name CComp := {}
  /-- Of each instance of a generic structural recursion, by its name, its
  function, and the facts that its parameters' types bring, at the
  instance, as its function's `CComp.vars` give them
  (`PreludeDecl.domain`). -/
  recInstances : NameMap (Name × Array String) := {}
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
  /-- `fren check --evidence`: the evidence of every check that the source
  could set, in place of the source's settings (`cli::evidence_in_effect`). -/
  evidenceOverride? : Option Fren.Core.Evidence := none
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
  /-- The current file's private procedures that `proc_without_outputs` may
  fire on, unless a path in it resolves to one. -/
  procs : Array (Fren.Core.ProcRecord × Span) := #[]
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
  /-- The type arguments that each application of a generic function was
  inferred at (`Fren.Core.inferCall`), by its file and the start of its
  span, outside the prelude: the evaluator's lowering applies the instance
  that they give (`Eval.LState.callTargs`). -/
  callTargs : Std.HashMap (Nat × Nat) (Array Ty) := {}
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
           seenSettings := t.seenSettings, globalReads := t.globalReads, hofParams := t.hofParams, fnArgs := t.fnArgs
           -- A `set_option ... in` before the item is read whatever becomes
           -- of the item, as the Lean front end reads it.
           settings := t.settings, settingRemovals := t.settingRemovals }

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

/-! ## Recording recursive uses -/

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

end FrenCli
