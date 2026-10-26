-- keep-sorted start
import FrenCli.Parse
import FrenCore.Checking
import FrenCore.Evidence
import FrenCore.Guards
import FrenCore.Lint
import FrenCore.Mentions
import FrenCore.Names
import FrenCore.PatternTypes
import FrenCore.Patterns
import FrenCore.Quantifier
import FrenCore.Refine
import FrenCore.Regex
import FrenCore.Trace
import FrenCore.Ty
import FrenCore.Typing
-- keep-sorted end

/-!
# Elaboration for `.fren` files

Resolves names with Fren's shared rules (`FrenCore.Names`), type-checks
expressions, and translates each comp into SMT-LIB formulas over its
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

/-- A type's SMT-LIB sort. A set is a unary relation, a set of 1-tuples, so
that relations need no conversions (`Reqs/Cli`). -/
def _root_.Fren.Core.Ty.sort : Ty → String
  | .bool => "Bool"
  -- A `Nat` is an `Int`, with the constraint that it is at least 0
  -- (`natFacts`).
  | .int | .nat => "Int"
  | .string => "String"
  | .set t => s!"(Set (Tuple {t.sort}))"
  | .rel a b => s!"(Set (Tuple {a.sort} {b.sort}))"
  | .seq t => s!"(Seq {t.sort})"
  | .enum p | .record p => quote (showPath p)
  | .abstract p => itemSym p
  -- Erased to its underlying type (`Reqs/Lang/Items#newtypes`).
  | .newtype _ u => u.sort

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
  deriving Inhabited

def DataDecl.ctorSym (d : DataDecl) (c : Name) : String :=
  if d.isRecord then recordCtorSym d.path else FrenCli.ctorSym d.path c

def DataDecl.selSym (d : DataDecl) (c : Name) (k : Nat) : String :=
  if d.isRecord then fieldSym d.path d.ctors[0]!.2[k]!.1 else payloadSym d.path c k

/-- Whether `smt` is the variant `idx`: that it equals the variant built
from its own payload. cvc5 rejects the tester `(_ is |E::V|)` of a quoted
constructor. -/
def DataDecl.tester (d : DataDecl) (idx : Nat) (smt : String) : String :=
  let (c, fs) := d.ctors[idx]!
  if fs.isEmpty then s!"(= {smt} {d.ctorSym c})" else
  let sels := (List.range fs.size).map fun k => s!"({d.selSym c k} {smt})"
  s!"(= {smt} ({d.ctorSym c} {" ".intercalate sels}))"

/-- The position of `smt`'s variant among the variants of the ordered
enumeration `d`, an `Int`: a conditional on each variant but the last, so
that comparing two values compares their positions without quantifiers.
Fren generates the same term in Lean (`Fren.ordinalTerm`). -/
def DataDecl.ordinal (d : DataDecl) (smt : String) : String :=
  (List.range (d.ctors.size - 1)).foldr (init := toString (d.ctors.size - 1)) fun k acc =>
    s!"(ite {d.tester k smt} {k} {acc})"

/-- `(declare-datatype ...)` -/
def DataDecl.decl (d : DataDecl) : String :=
  let ctors := " ".intercalate <| d.ctors.toList.map fun (c, fs) =>
    let sels := String.join <| (fs.toList.zipIdx).map fun ((_, t), k) => s!" ({d.selSym c k} {t.sort})"
    s!"({d.ctorSym c}{sels})"
  s!"(declare-datatype {quote (showPath d.path)} ({ctors}))\n"

/-- `d` with its declaration and the names of the symbols that it declares:
the datatype, its constructors and its selectors. -/
def DataDecl.withPrelude (d : DataDecl) : DataDecl :=
  let unquote (sym : String) : String := ((sym.drop 1).dropEnd 1).toString
  let ctors := d.ctors.flatMap fun (c, fs) => #[d.ctorSym c] ++ (List.range fs.size).toArray.map (d.selSym c)
  { d with text := d.decl, syms := (#[quote (showPath d.path)] ++ ctors).map unquote }

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

/-! ## Pattern types' constraints in SMT-LIB -/

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
    let .enum ep := ty | return "true"
    let some d := dts ep | return "true"
    let (c, fs) := d.ctors[idx]!
    let tests := #[d.tester idx x] ++ (args.zipIdx.filterMap fun (a, k) =>
      let t := patSmt dts (fs[k]!.2) a s!"({d.selSym c k} {x})"
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
  | .pat ty p => patSmt dts ty p x
  | .atLeast0 => s!"(>= {x} 0)"
  | .fields path cs => Id.run do
    let some d := dts path | return "true"
    return smtAll (cs.map fun (k, c) => consSmt dts c s!"({d.selSym `mk k} {x})" depth)
  -- A newtype is its underlying type, to the solver.
  | .newtype _ c => consSmt dts c x depth
  | .payloads path cs => Id.run do
    let some d := dts path | return "true"
    return smtAll (cs.map fun (v, k, c) =>
      s!"(=> {d.tester v x} {consSmt dts c s!"({d.selSym d.ctors[v]!.1 k} {x})" depth})")
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

/-- A comp variable: one of its own, or one of an instance's (`w.x`). -/
structure CVar where
  name : Name
  role : Role
  /-- Shown in counterexamples. -/
  isPub : Bool
  /-- A `det out` of the comp itself. -/
  isDet : Bool := false
  ty : Ty
  span : Span
  /-- The definition of a defined output of the comp itself. -/
  defn? : Option Expr := none
  /-- Its type as declared, with its patterns. -/
  ptype : Fren.Core.PTy := default
  /-- The constraint that its type brings, over it (`Reqs/Lang/Components#pattern-types`). -/
  fact? : Option String := none
  deriving Inhabited

structure CProp where
  kind : PropKind
  name : Name
  span : Span
  smt : String
  trigger? : Option String
  triggerSpan? : Option Span
  deriving Inhabited

/-- An instance, with formulas over the instantiating comp's variables. -/
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
  path : Name
  file : Nat
  span : Span
  /-- Its own variables in declaration order, then each instance's. -/
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
  /-- It, or one of its instances, applies a relational operator. -/
  relational : Bool := false
  /-- It, or one of its instances, uses `card`. -/
  counts : Bool := false
  /-- The checks that are tested rather than asked of the solver
  (`Reqs/Check#checking-by-testing`). -/
  tested : Fren.Core.Tested := {}
  /-- The applications of uninterpreted functions whose result is a `Nat`,
  or that have postconditions, in its constraints, definitions, bindings
  and instances: each brings its facts (`Fren.Core.appFacts`). -/
  natApps : Array String := #[]
  /-- For the body or contract of a function, or the value of a constant:
  its name, which the evaluator's counterpart has (`Eval.Comp.body?`). -/
  bodyOf? : Option Name := none
  /-- For the body and contract of a function: the function, whose
  preconditions are the comp's assumptions, and, if it is defined, whose
  postconditions are its guarantees, each named after the function and
  the clause (`check::postcondition`). -/
  fn? : Option Name := none
  /-- What each application of a function, or read of a payload, whose
  result brings a constraint brings, by its head symbol, about `factHole`
  (`State.funFacts`). -/
  funFacts : Std.HashMap String String := {}
  /-- Whether a query quantifies over a collection's elements, which sets
  `fmf-bound` (`CComp.bounded`). -/
  bounded : Bool := false
  deriving Inhabited

def conj (fs : Array String) : String :=
  if fs.isEmpty then "true" else if fs.size == 1 then fs[0]! else s!"(and {" ".intercalate fs.toList})"

/-- Everything a comp says about its variables: assumptions, requirements
and instances. -/
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
instance or a refinement may keep its variable an `Int`
(`lint::manual_nat`): the component, the variable and the report. -/
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

structure State where
  table : Table := {}
  claims : Array CClaim := #[]
  module : Name := .anonymous
  /-- The scope that paths resolve in: the current module, or the
  component being elaborated, if it has `use`s. -/
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
  /-- Each uninterpreted function's parameter and result types, in order. -/
  funs : Array (Name × Array Ty × Ty) := #[]
  /-- Each defined function's parameters and result type, and its body over
  the parameters, in order. -/
  defs : Array (Name × Array (Name × Ty) × Ty × String) := #[]
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
  instance per binder and the expectation as its only constraint. -/
  globals : Array CComp := #[]
  /-- Refinements, each a `CComp` whose path is the refinement's
  (`Reqs/Lang/Refinement`). -/
  refinements : Array CComp := #[]
  /-- The bodies of defined functions and the values of constants that have
  tables, each as a comp whose path is its module, with the function's
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
  /-- The variables, parameters, instances and binders that the item being
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
  and what its global expectations read through instances, and its
  refinements of their abstractions: each read's component and input. -/
  assumptions : Array (Fren.Core.AssumptionRecord × Span) := #[]
  globalReads : Array (Name × Name) := #[]
  /-- The reports of `manual_nat` in the file so far. -/
  natReports : Array NatReport := #[]
  /-- The variables that an instance or a refinement in the file keeps
  `Int`s, by their components (`Fren.Core.refinementGiven`). -/
  natKept : Array (Name × String) := #[]
  /-- Where the comparisons of `Bool`s in the expression being elaborated
  are, for `bool_equality`. -/
  boolEqs : Array Span := #[]
  /-- Where the conditions of `if`s and the operands of `*` in the
  expression being elaborated that mention a variable or an uninterpreted
  function are, for `branches_sharing_code`. -/
  mentioning : Array Span := #[]
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
  /-- Some type is a set. -/
  usesSets : Bool := false
  /-- Whether the spec uses sequences, which cvc5 decides in its strings
  solver (`cli::logic`). -/
  usesSeqs : Bool := false
  /-- Whether it takes the domain or range of a relation over a type that is
  not finite, which needs higher-order logic (`cli::logic`). -/
  usesProjection : Bool := false
  /-- Some construct of the current item is outside the decidable core,
  whatever the level of `undecidable` (`view::inconclusive_advice`). -/
  outsideCore : Bool := false
  /-- Whether the current comp, or an instance of it, applies a relational
  operator; with `card`, it is outside the decidable core. -/
  relationalUsed : Bool := false
  /-- Where the current comp counts: its `card`s, and its instances whose
  comps count. -/
  countSpans : Array Span := #[]
  /-- The indexes of the constraint being elaborated, each with the formula
  that it is in range where it is evaluated: its guard implies its bounds. -/
  indexes : Array (Span × String × Option (String × Bool)) := #[]
  /-- The questions about the rows of the tables of the constraint being
  elaborated, each where it is reported, with the formula that it holds
  where the table is evaluated: its guard implies it. -/
  tables : Array (Span × Fren.Core.TableGoal × String) := #[]
  /-- The applications of uninterpreted functions whose result is a `Nat`
  elaborated since the current comp started, its instances' among them. -/
  natApps : Array String := #[]
  /-- Each `+` where a `Nat` is expected, by file, which `fren mutate`
  does not make a `-` (`Reqs/Mutate`). -/
  natSums : Array (Nat × Span) := #[]
  /-- The names of `let` and `where` definitions made so far, which number
  their SMT-LIB symbols. -/
  nLets : Nat := 0
  /-- Whether the current component's members are being elaborated, past
  its name and the distinctness of its members' names: after a failure
  there, its declaration and line lints still run, as in Lean. -/
  inCompBody : Bool := false

/-- `s`, with what `t` recorded for the lints: what a failed member or item
recorded before its error outlives it, as in Lean, where an error undoes
nothing (`Reqs/View#static-errors`). -/
def State.keepLints (s t : State) : State :=
  { s with lintReports := t.lintReports, lintFixes := t.lintFixes, used := t.used, usedItems := t.usedItems
           useRecords := t.useRecords, useLocs := t.useLocs, items := t.items, declared := t.declared
           seenSettings := t.seenSettings, globalReads := t.globalReads }

/-- Why an item failed: its static errors, the last of which stopped it,
and the state when it did, whose lints outlive it (`State.keepLints`). -/
structure Failure where
  diags : Array Diag
  state : State

abbrev M := StateT State (Except Failure)

def err (span : Span) (msg : Msg) : M α := do
  let s ← get
  throw { diags := s.itemErrors.push { file := s.file, span, msg }, state := s }

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

partial def State.unbounded (s : State) : Ty → Bool
  | .string | .set _ | .rel .. | .seq _ => true
  | .enum p | .record p => (s.dataOf? p).any (·.unbounded)
  | .newtype _ u => Fren.Core.newtypeUnbounded (s.unbounded u)
  | _ => false

/-- Whether a type has infinitely many values (`Reqs/Lang/Decidability#outputs`):
an abstract type may, so it counts. -/
partial def State.infinite (s : State) : Ty → Bool
  | .bool => false
  | .int | .nat | .string | .abstract _ | .seq _ => true
  | .set t => s.infinite t
  | .rel a b => s.infinite a || s.infinite b
  | .newtype _ u => s.infinite u
  | .enum p | .record p => match s.dataOf? p with
    | some d => d.unbounded || d.ctors.any fun (_, fs) => fs.any fun (_, t) => s.infinite t
    | none => true

/-- Every value of a finite type, as SMT-LIB terms, if there are at most
`cap` of them. -/
partial def State.values (s : State) (cap : Nat := 64) : Ty → Option (Array String)
  | .bool => some #["true", "false"]
  | .enum p | .record p => do
    let d ← s.dataOf? p
    if d.unbounded then none
    let mut out := #[]
    for (c, fs) in d.ctors do
      let mut combos : Array (Array String) := #[#[]]
      for (_, t) in fs do
        let vs ← s.values cap t
        combos := combos.flatMap fun pre => vs.map pre.push
        if combos.size > cap then none
      out := out ++ combos.map fun args => if args.isEmpty then d.ctorSym c else s!"({d.ctorSym c} {" ".intercalate args.toList})"
      if out.size > cap then none
    return out
  -- Erased, as a newtype's values are.
  | .newtype _ u => s.values cap u
  | _ => none

/-- The number of values of `t`, if a quantifier ranges over it
(`lang::quantified_type`), counted without listing them. An unbounded
enumeration or record is recursive or has a part that a quantifier does
not range over, so it is not looked into, and the recursion ends. -/
partial def State.valueCount (s : State) : Ty → Option Nat
  | .bool => some 2
  | .enum p | .record p => do
    let d ← s.dataOf? p
    if d.unbounded then none
    let counts : Array (Array (Option Nat)) := d.ctors.map fun (_, fs) => fs.map fun (_, t) => s.valueCount t
    let kind := if d.isRecord then Fren.Core.QuantifiedKind.record else .enum
    unless Fren.Core.quantifiedTypeAccepted kind false (counts.all (·.all Option.isSome)) do none
    return counts.foldl (fun n cs => n + cs.foldl (fun m c => m * c.getD 0) 1) 0
  | _ => none

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
def declare (x : Ident) (locals : Array (Name × String) := #[]) : M Ident := do
  let (y, bang) := declaredIdent x
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
  modify fun s => { s with lintReports := s.lintReports.push { lint, level := s.levels.get lint, ref := span, msg } }

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

structure ExprCtx where
  vars : Array CVar
  /-- The comp's instances, in order. -/
  insts : Array Name := #[]
  place : Place
  /-- For a binding, the index of its instance. -/
  current : Nat := 0
  /-- In a refinement's binding, over the concrete comp's variables, which
  binding it is: its mentions follow `refinement::mention` instead. -/
  refining? : Option Fren.Core.RefineBinding := none
  /-- The binders in scope, innermost last. -/
  binders : Array CBinder := #[]
  /-- The instances of the quantifiers around this expression, multiplied
  (`lang::quantifier_size`). -/
  instances : Nat := 1
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- In a clause of a function's contract: the function, whether the
  clause is a postcondition, and the parameters (`lang::contract_application`). -/
  contract? : Option (Name × Bool × Array Name) := none
  /-- In a global expectation, whose instances are its binders. -/
  inGlobal : Bool := false
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

/-- What the binder `b` is, for a declaration that hides it (`Fren.Core.bindingLocals`). -/
def CBinder.what (b : CBinder) : Name × String :=
  (b.name, if b.scrutinee.isNone then "the bound name" else if b.isDef then "the definition" else "the binder")

/-- The binder named `n` in scope, if any. -/
def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option CBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : CBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name)


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
def patternName (cx : ExprCtx) (x : Ident) : M Fren.Core.PatternName := do
  let (d, bang) := declaredIdent x
  return Fren.Core.patternName (d.name == "true" || d.name == "false") bang (← isVariant cx #[x])

/-- The binders of the pattern `p`, in preorder. -/
def patternBinders (cx : ExprCtx) (p : Pattern) : M (Array Ident) :=
  p.names.filterM fun x => return (← patternName cx x) == .binder

/-- The paths of the functions that `e` applies (`unused_assumption`). -/
partial def appliedPaths : Expr → Array (Array Ident)
  | .app _ segs args => args.foldl (· ++ appliedPaths ·) #[segs]
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => appliedPaths c ++ appliedPaths d
  | .not _ a | .neg _ a | .field _ a _ => appliedPaths a
  | .method _ r _ args => args.foldl (· ++ appliedPaths ·) (appliedPaths r)
  | .set _ es | .seq _ es | .chain _ es _ => es.foldl (· ++ appliedPaths ·) #[]
  | .ite _ c a b => appliedPaths c ++ appliedPaths a ++ appliedPaths b
  | .record _ _ fs => fs.foldl (init := #[]) fun acc (_, e?) => acc ++ (e?.map appliedPaths).getD #[]
  | .update _ r fs => fs.foldl (init := appliedPaths r) fun acc (_, e?) => acc ++ (e?.map appliedPaths).getD #[]
  | .match _ s arms => (armParts arms).foldl (init := appliedPaths s) fun acc e => acc ++ appliedPaths e
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
  match e with
  | .path _ segs =>
    if segs.size != 1 then return .leaf .constant
    let n := identName segs[0]!.name
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then
      let some sc := b.scrutinee | return .leaf .bound
      return .node .binder [← shapeOf (cx.at b) #[] sc]
    -- Definitions are acyclic, so this ends.
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      return .node .definedOutput [← shapeOf { cx with binders := #[] } #[] d]
    return .leaf (if cx.vars.any (·.name.isPrefixOf n) then .variable else .constant)
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => parts .compound [c, d]
  | .not _ a | .neg _ a | .field _ a _ => parts .compound [a]
  | .method _ r _ args => parts .method (r :: args.toList)
  | .set _ es | .seq _ es | .chain _ es _ => parts .compound es.toList
  | .ite _ c a b => parts .compound [c, a, b]
  | .quant _ _ binders body =>
    let new := binders.flatMap (·.names) |>.map fun x => (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.leaf .bound)
    return .node .compound [← shapeOf cx (bs ++ new) body]
  | .app _ segs args =>
    -- A cardinality operator has a fixed meaning, as an operator does.
    let k : Fren.Core.MentionKind ← if isCardinality segs then pure .compound
      else if ← isConstruction cx segs then pure .construction
      else if ← isDefined cx segs then pure .defined else pure .uninterpreted
    parts k args.toList
  | .record _ _ fs => parts .construction (fs.toList.map fun (f, e?) => e?.getD (.path f.span #[f]))
  | .update _ r fs => parts .construction (r :: fs.toList.map fun (f, e?) => e?.getD (.path f.span #[f]))
  | .match _ s arms =>
    let s' ← shapeOf cx bs s
    let arms ← arms.toList.flatMapM fun (p, g?, body) => do
      let new := (← patternBinders cx p).map fun x =>
        (Name.mkSimple (declaredIdent x).1.name, Fren.Core.MentionShape.node .binder [s'])
      (g?.toList ++ [body]).mapM (shapeOf cx (bs ++ new))
    return .node .compound (s' :: arms)
  | .is _ s _ => parts .compound [s]
  | .«let» _ defs body _ =>
    -- Each name stands for its definition, which sees the earlier names.
    let bs ← defs.foldlM (init := bs) fun bs (x, _, d) => do
      return bs.push (Name.mkSimple (declaredIdent x).1.name, .node .binder [← shapeOf cx bs d])
    return .node .compound [← shapeOf cx bs body]
  | .table _ rows => parts .compound (tableParts rows).toList
  | .num .. | .bool .. | .str .. => return .leaf .literal

/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def mentionsAny (cx : ExprCtx) (e : Expr) : M Bool := return (← shapeOf cx #[] e).mentions

/-- The names of the variables that `e` mentions: its paths of one
segment, and for `p.x`, `p` too. -/
partial def mentions (e : Expr) (all : Bool := true) : Array Name :=
  let mentions (e : Expr) := mentions e all
  match e with
  | .path _ segs =>
    if segs.size == 1 then
      let n := identName segs[0]!.name
      (n.components.foldl (init := (#[], Name.anonymous)) fun (acc, p) c => let p := p ++ c; (acc.push p, p)).1
    else #[]
  | .when _ _ c d => mentions c ++ mentions d
  | .not _ a | .neg _ a | .field _ a _ => mentions a
  | .method _ r _ args => args.foldl (· ++ mentions ·) (mentions r)
  | .set _ es => es.foldl (· ++ mentions ·) #[]
  | .pair _ a b | .index _ a b => mentions a ++ mentions b
  | .seq _ es | .chain _ es _ => es.foldl (· ++ mentions ·) #[]
  | .ite _ c a b => mentions c ++ mentions a ++ mentions b
  | .bin _ _ a b => mentions a ++ mentions b
  | .app _ _ args => args.foldl (· ++ mentions ·) #[]
  | .record _ _ fs => fs.foldl (init := #[]) fun acc (f, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple f.name]
  | .update _ r fs => fs.foldl (init := mentions r) fun acc (f, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple f.name]
  | .match _ s arms => arms.foldl (init := mentions s) fun acc (p, g?, body) =>
    -- In its arm, a binder's name means the binder, not what it shadows.
    let bound := p.names.map fun b => Name.mkSimple (declaredIdent b).1.name
    acc ++ ((g?.map mentions).getD #[] ++ mentions body).filter (!bound.contains ·.getRoot)
  | .is _ s _ => mentions s
  | .«let» _ defs body _ =>
    (Fren.Core.clauseMentions (defs.map fun (x, _, _) => Name.mkSimple (declaredIdent x).1.name)
      (defs.map fun (_, _, d) => mentions d) (mentions body) all).1
  | .quant _ _ binders body =>
    -- In its body, a bound name means the bound name, not what it shadows.
    let bound := binders.flatMap (·.names) |>.map fun x => Name.mkSimple (declaredIdent x).1.name
    (mentions body).filter (!bound.contains ·.getRoot)
  | .table _ rows => (tableParts rows).foldl (· ++ mentions ·) #[]
  | _ => #[]

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
  | .match _ s arms => return (← hasConcat cx s) || (← (armParts arms).anyM (hasConcat cx))
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

/-- The expressions directly within `e`, in order. -/
def Expr.operands : Expr → Array Expr
  | .when _ _ c d => #[c, d]
  | .ite _ c a b => #[c, a, b]
  | .bin _ _ a b | .pair _ a b | .index _ a b => #[a, b]
  | .not _ a | .neg _ a | .field _ a _ => #[a]
  | .app _ _ args | .set _ args | .seq _ args | .chain _ args _ => args
  | .method _ r _ args => #[r] ++ args
  | .record _ _ fs => fs.filterMap (·.2)
  | .update _ r fs => #[r] ++ fs.filterMap (·.2)
  | .match _ s arms => #[s] ++ armParts arms
  | .quant _ _ _ b => #[b]
  | .is _ s _ => #[s]
  | .«let» _ defs body _ => defs.map (·.2.2) |>.push body
  | .table _ rows => tableParts rows
  | .num .. | .bool .. | .path .. | .str .. => #[]

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
    | .match _ _ arms => arms.flatMap (·.1.integerSpans)
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
  | .match s scrutinee arms => .mk .atom (toRange s) s (#[scrutinee.boolNode src base] ++ (armParts arms).map (·.boolNode src base))
  | .table s rows => .mk .atom (toRange s) s ((tableParts rows).map (·.boolNode src base))
  | .pair s a b | .index s a b => .mk .atom (toRange s) s #[a.boolNode src base, b.boolNode src base]
  | .chain s es ops => .mk (.chain (ops.map (·.1))) (toRange s) s (es.map (·.boolNode src base))
  | .«let» s _ body _ => .mk .«let» (toRange s) s #[body.boolNode src base]
  | .quant s _ _ b => .mk .quant (toRange s) s #[b.boolNode src base]
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
  | .field _ x _ | .method _ x _ _ | .index _ x _ | .match _ x _ =>
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

/-- Reports the expressions in `e` that the lints that rewrite them
(`Fren.Core.ExLint`) report, such as `Bool` expressions with a simpler form
(`nonminimal_bool`), the operator and method lints, the arithmetic lints
and double parentheses in it, once `e` is elaborated. -/
def lintBools (e : Expr) : M Unit := do
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
    lintFix l ref (shift msg)
  let (boolEqs, ordereds, variants, absEnds, mentioning, facts) :=
    ((← get).boolEqs, (← get).ordereds, (← get).variants, (← get).absEnds, (← get).mentioning, (← get).facts)
  modify fun s => { s with boolEqs := #[], ordereds := #[], variants := #[], absEnds := #[], mentioning := #[], facts := #[] }
  let variant? (sp : Span) := (variants.find? (·.1 == sp)).map (·.2)
  let fact? (sp : Span) := (facts.find? (·.1 == sp)).map (·.2)
  let ordered? (sp : Span) := (ordereds.find? (·.1 == sp)).map (·.2)
  for r in Fren.Core.opReports src boolEqs.contains ordered? variant? (absEnds.contains ·.stop) mentioning.contains fact? root do
    lintFix r.lint (match r.last? with | some l => r.ref.to l | none => r.ref) (shift r.msg) r.unless?
  for r in Fren.Core.arithReports src root do
    lintFix r.lint r.ref (shift r.msg)
  for sp in e.integerSpans do
    if let some (r, msg) := Fren.Core.zeroPrefixedReport? full (toRange sp) then
      lintFix .zeroPrefixedLiteral { start := r.start, stop := r.stop } msg
  lintParens e

/-- Whether `t` is an ordered enumeration (`Reqs/Lang/Items#enumerations`). -/
def isOrdered (t : Ty) : M Bool := do
  let .enum p := t | return false
  return ((← get).dataOf? p).any (·.ordered)

/-- The ordered enumeration that `t` is, if it is one. -/
def orderedData? (t : Ty) : M (Option DataDecl) := do
  let .enum p := t | return none
  return ((← get).dataOf? p).filter (·.ordered)

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
  if let .enum p := t then
    let some d := (← get).dataOf? p | internal span s!"unknown enum `{p}`"
    let some method := (Fren.Core.Method.ofName? m).filter (·.accepts false false (ordered := d.ordered))
      | if d.ordered then err span (Fren.Core.unknownMethodMsg m t.show false (ordered := true))
        else if m == "min" || m == "max" then err span (Fren.Core.unorderedMethodMsg m t.show)
        else err span (Fren.Core.noMethodsMsg m t.show)
    unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
    for (_, ta, sp) in args do
      unless ta == t do
        err sp { code? := some "F0304", headline := s!"type mismatch: expected `{t.show}`, found `{ta.show}`"
                 label? := some s!"expected `{t.show}`, found `{ta.show}`"
                 notes := #[s!"note: the argument of `{m}` is a `{t.show}`, as its receiver is"] }
    -- Conditionals on the variants' positions, as for an `Int`.
    let y := (args.map (·.1))[0]?.getD ""
    let cmp := if method == .min then "<=" else ">="
    return (s!"(ite ({cmp} {d.ordinal recv} {d.ordinal y}) {recv} {y})", t)
  unless t == .string do err span (Fren.Core.noMethodsMsg m t.show)
  let some method := (Fren.Core.Method.ofName? m).filter (·.accepts true false)
    | err span (Fren.Core.unknownMethodMsg m t.show)
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
  if Fren.Core.positionalField f && !(t matches .record _) then err span (Fren.Core.noFieldMsg f t.show #[])
  -- For `invalid_upcast_comparisons`, at the end of the expression.
  if (t == .int || t == .nat) && f == `abs then modify fun s => { s with absEnds := s.absEnds.push span.stop }
  if t matches .string | .set _ | .rel .. | .seq _ | .int | .nat then return ← callMethod span smt t f.toString #[]
  -- An enumeration's methods, `min` and `max`, which take an argument.
  if t matches .enum _ && (f == `min || f == `max) then return ← callMethod span smt t f.toString #[]
  let .record p := t | err span (Fren.Core.noFieldMsg f t.show #[])
  let fields : Array (Name × Ty) := ((← get).dataOf? p).map (·.ctors[0]!.2) |>.getD #[]
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

/-- The operands of a chain of `op`, `or` or `and`. -/
partial def chainOperands (op : String) (e : Expr) : Array Expr :=
  match e with
  | .bin _ op' l r => if op' == op then chainOperands op l ++ chainOperands op r else #[e]
  | _ => #[e]

/-- The sequences that `e` indexes, as their text. -/
partial def indexedIn : Expr → M (Array String)
  | .index _ q i => return #[← srcAt q.span] ++ (← indexedIn q) ++ (← indexedIn i)
  | .bin _ _ a b | .when _ _ a b | .pair _ a b => return (← indexedIn a) ++ (← indexedIn b)
  | .not _ a | .neg _ a | .field _ a _ | .is _ a _ => indexedIn a
  | .ite _ c a b => return (← indexedIn c) ++ (← indexedIn a) ++ (← indexedIn b)
  | .method _ r _ args => return (← indexedIn r) ++ (← args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[])
  | .app _ _ args | .set _ args | .seq _ args | .chain _ args _ => args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[]
  | .record _ _ fs => fs.foldlM (fun acc (_, e?) => return acc ++ (← (e?.map indexedIn).getD (pure #[]))) #[]
  | .match _ sc arms => return (← indexedIn sc) ++ (← (armParts arms).foldlM (fun acc b => return acc ++ (← indexedIn b)) #[])
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

/-- `goal` where `guards` hold. -/
def guarded (guards : Array String) (goal : String) : String :=
  if guards.isEmpty then goal else s!"(=> (and true {" ".intercalate guards.toList}) {goal})"

/-- `e` within the SMT-LIB `let`s of `binds`, each a symbol and its
definition, the first outermost. -/
def wrapLets (binds : Array (String × String)) (e : String) : String :=
  binds.foldr (fun (x, d) acc => s!"(let (({x} {d})) {acc})") e

/-- The term within the SMT-LIB `let`s that `wrapLets` puts around it,
read outside string literals, where `""` is a `"`. -/
partial def peelLets (t : String) : String := Id.run do
  unless t.startsWith "(let ((" do return t
  let cs := t.toList.toArray
  -- The bindings start at the second `(`, and end where it closes.
  let mut depth := 0
  let mut inString := false
  let mut i := 5
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
`span` where the type `t` is declared, if it has one, for the pattern-type
check (`Reqs/Check#pattern-types`): its guard implies that the value
matches. It is a definedness goal, with its type beside it. -/
def noteObligation (cx : ExprCtx) (place : Fren.Core.ValuePlace) (span : Span) (t : Fren.Core.PTy) (value : String) :
    M Unit := do
  unless cx.noteIndexes do return
  let some o := Fren.Core.siteObligation place t.obligation | return
  let st ← get
  modify fun s => { s with indexes := s.indexes.push (span, guarded cx.guards (consSmt st.dataOf? o value), some (t.text, o.quantifies)) }

/-- The declared type of the `k`th field or payload value of the variant
`v` of the record, newtype or enumeration `p`. -/
def partPTy (p : Name) (v k : Nat) : M Fren.Core.PTy := do
  let some t := ((← get).shapeOf p).bind (·.parts[v]?) |>.bind (·[k]?) | return default
  return t

/-- The value of a table of type `t` where no row holds: an index out of
range of the empty sequence, which is unspecified
(`Reqs/Lang/Expressions#tables`). -/
def unspecified (t : Ty) : String := s!"(seq.nth (as seq.empty (Seq {t.sort})) 0)"

/-- The questions about tables recorded since the last call, which it forgets. -/
def takeTables : M (Array (Span × Fren.Core.TableGoal × String)) := do
  let xs := (← get).tables
  modify fun s => { s with tables := #[] }
  return xs

/-- Records the questions about the application at `span` of the function
at `path` to the SMT-LIB arguments `args`, if the function has
preconditions, for the precondition check (`check::precondition`): its
guard implies each precondition at the arguments, in order. -/
def notePreconditions (cx : ExprCtx) (span : Span) (path : Name) (args : Array String) : M Unit := do
  unless cx.noteIndexes do return
  let some k := (← get).contracts.find? path | return
  let pres := k.pres.map fun (n, sym) => (n, s!"({sym} {" ".intercalate args.toList})")
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
      | .disjointness _ j | .reachability _ j => starts[j]!
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
reachability of an arm at its pattern. -/
def noteMatch (cx : ExprCtx) (span : Span) (pats : Array Span) (taken : Array (Option String)) (hasGuard : Array Bool)
    (unguardedExhaustive : Bool) : M Unit := do
  unless cx.noteIndexes do return
  let goals := Fren.Core.splitGoals .match orSmt andSmt (s!"(not {·})") "true" taken hasGuard
    (Fren.Core.completenessAsked unguardedExhaustive)
  for (g, f) in goals do
    let at_ := match g with
      | .reachability _ j => pats[j]!
      | _ => { start := span.start, stop := span.start + "match".length }
    modify fun s => { s with tables := s.tables.push (at_, g, guarded cx.guards f) }

/-- Records a `card`, of the receiver `recv` of type `t`: in a comp that
applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (span : Span) (t : Ty) (m : String) (recv : Expr) : M Unit := do
  if cx.unmentioned then return
  if m == "card" && t matches .set _ | .rel .. && !(← isConstant cx recv) then
    modify fun s => { s with countSpans := s.countSpans.push span }

/-- Reports `undecidable` at each count of the current comp, if it also
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

/-- The match lints of the `match` `e` on a value of type `ty`, whose arms'
patterns are `pats`, where `slot` is (`Reqs/Lint/Style#matches-that-are-memberships`,
`Reqs/Lint/Pedantic/Matches`). The lints that move or remove arms, or
replace `_` with a variant, look only at a `match` whose patterns are all
flat (`Fren.Core.Pat.flat`), where no arm overlaps another without
containing it. -/
def lintMatch (cx : ExprCtx) (e : Expr) (ty : Ty) (pats : Array Fren.Core.Pat) (slot : Option Fren.Core.Slot) :
    M Unit := do
  let .match span scrutinee arms := e | return
  let src := (← get).src
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
      lintFix .trivialMatch span (Fren.Core.trivialMatchMsg (info.body.inSlot slot (← followedSpan span)))
  -- `needless_match` (`lint::needless_match`).
  let st ← get
  let scr ← srcAt scrutinee.span
  let mut givenBack := true
  let mut wildcard := false
  let mut scrutineeBack := false
  -- Only a `match` whose arms are `_` and variants whose payloads'
  -- patterns are `_` or binders.
  let ep := match ty with
    | .enum p => p
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
    lintFix .needlessMatch span (Fren.Core.needlessMatchMsg (bare.inSlot slot (← followedSpan span)))
  let bodyRanges := arms.map fun (_, _, b) => Fren.Core.withParens src (toRange b.span)
  let armRanges := arms.zipWith (fun (p, _) (b : Fren.Core.Range) => { start := p.span.start, stop := b.stop }) bodyRanges
  let groups := if flat && !anyGuard then Fren.Core.sameArmGroups infos else #[]
  let mut firstSame? : Option Span := none
  if flat && !anyGuard then
    let edits := Fren.Core.sameArmsEdits (toRange span) infos armRanges (arms.map (toRange ·.1.span)) bodyRanges slot (← followedSpan span)
    for g in groups do
      let (i, msg) := Fren.Core.sameArmsMsg infos g slot (← followedSpan span)
      let at_ : Span := { start := armRanges[i]!.start, stop := armRanges[i]!.stop }
      lintEdits .matchSameArms at_ msg (if firstSame?.isNone then edits else #[])
      if firstSame?.isNone then firstSame? := some at_
  let scr := scrutinee.text src
  let membership? := if anyGuard then none else Fren.Core.membershipParts? infos scr slot
  if let some (pre, post, test) := membership? then
    let r := Fren.Core.withParens src (toRange scrutinee.span)
    lintEdits .matchLikeMembership span (Fren.Core.membershipMsg (pre ++ scr.text ++ post) test)
      #[({ start := span.start, stop := r.start }, pre), ({ start := r.stop, stop := span.stop }, post)]
  -- `single_match_else` (`lint::single_match_else`).
  let followed ← followedSpan span
  if let some fixed := (if anyGuard then none else
      Fren.Core.singleMatchElseFix? infos scr slot (membership?.isSome || needless || trivial) followed) then
    lintFix .singleMatchElse span (Fren.Core.singleMatchElseMsg fixed (Fren.Core.hasComment (← srcAt span)))
  unless flat do return
  let .enum ep := ty | return
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
  lintFix .wildcardEnumMatchArm arms[w]!.1.span (Fren.Core.wildcardEnumMsg (covered.map (d.path ++ d.ctors[·]!.1)) pattern?)
    unless?
  unless Fren.Core.wildcardSingle covered.size do return
  lintFix .wildcardSingleVariant arms[w]!.1.span (Fren.Core.wildcardMsg (d.path ++ d.ctors[covered[0]!]!.1) named[0]!) unless?

/-! ## Patterns -/

/-- A binder of a pattern, with the type of its value, and its value, read
from the scrutinee with selectors. -/
structure PBinder where
  ident : Ident
  ty : Ty
  smt : String
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
    let .enum ep := ty
      | err sp (Fren.Core.patternTypeMsg ty.show (match r with
          | .variant en _ => s!"a pattern of `{showPath en.path}`"
          | r => r.describe))
    let .variant en idx := r | err sp (Fren.Core.notAVariantOfMsg ep r.describe)
    if en.path != ep then err sp (Fren.Core.notAVariantOfMsg ep s!"a variant of `{showPath en.path}`")
    let some d := (← get).dataOf? ep | internal sp s!"unknown enum `{ep}`"
    let (c, fs) := d.ctors[idx]!
    let v := ep ++ en.variants[idx]!
    if let some msg := Fren.Core.variantMentionMsg? v fs.size args?.isSome then err sp msg
    let args := args?.getD #[]
    unless args.size == fs.size do err sp (Fren.Core.arityMsg v fs.size args.size "pattern")
    let mut pats := #[]
    let mut bs := #[]
    let mut tests := #[d.tester idx x]
    for a in args, (_, t) in fs, k in [0:args.size] do
      let (q, qbs, qt) ← resolvePattern cx t s!"({d.selSym c k} {x})" inOr test a
      pats := pats.push q
      bs := bs ++ qbs
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

/-- `if_chain_match` on the chain of `if` that starts at `e`
(`lint::if_chain_match`). -/
def lintIfChain (cx : ExprCtx) (e : Expr) : M Unit := do
  let (cs, as, z) := ifChain e
  let ts? := Fren.Core.sameScrutinee (← cs.mapM (variantTest? cx))
  let ts := ts?.getD #[]
  let enums := (← get).table.enums
  let n := ((ts[0]?.bind fun t => enums.get? t.enum).map (·.variants.size)).getD 0
  let (fires, wildcard) := Fren.Core.ifChainMatch cs.size ts?.isSome (Fren.Core.repeatedVariants ts)
    (Fren.Core.untestedVariants n ts)
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

/-- `e`'s shape, for whether it synthesizes a type (`Fren.Core.TypeShape`). -/
partial def typeShape : Expr → Fren.Core.TypeShape
  | .set _ #[] | .seq _ #[] => .emptyLiteral
  | .set _ es | .seq _ es => .anyPart (es.toList.map typeShape)
  | .pair _ a b => .pair (typeShape a) (typeShape b)
  | .bin _ op a b => if op == "union" || op == "inter" || op == "minus" || op == "++" then
      .anyPart [typeShape a, typeShape b] else .other
  | .ite _ _ a b => .anyPart [typeShape a, typeShape b]
  | .match _ _ arms => .anyPart (arms.toList.map (typeShape ·.2.2))
  | .«let» _ _ body _ => .anyPart [typeShape body]
  | .table _ rows => .anyPart (rows.toList.map (typeShape ·.2.2))
  | _ => .other

/-- Whether `e` synthesizes a type (`lang::synthesizes`). -/
def synthesizes (e : Expr) : Bool := (typeShape e).synthesizes

/-- Whether `e` is written as a sequence: a sequence literal, or a `++`, a
conditional or a `match` with one among its shared parts, so that the
right of `in` is checked against a sequence. -/
partial def seqShaped : Expr → Bool
  | .seq .. => true
  | .bin _ "++" a b | .ite _ _ a b => seqShaped a || seqShaped b
  | .match _ _ arms => arms.any (seqShaped ·.2.2)
  | .«let» _ _ body _ => seqShaped body
  | .table _ rows => rows.any (seqShaped ·.2.2)
  | _ => false

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
`)` of each `Set(`, `Seq(` and `Rel(` within it that it leaves out. -/
def writtenTypeSpan (segs : Array Ident) : M Span := do
  let src := (← get).src
  let sp := typeSpan segs
  let mut depth : Int := 0
  for c in src.extract sp.start sp.stop do
    if c == '(' then depth := depth + 1 else if c == ')' then depth := depth - 1
  let mut stop := sp.stop
  while depth > 0 && stop < src.size do
    if src[stop]! == ')' then depth := depth - 1
    stop := stop + 1
  return { sp with stop }

mutual
/-- The declared type written `segs`, with the patterns of the pattern
types within it (`Reqs/Lang/Types#pattern-types`). -/
partial def elabPTy (segs : Array Ident) : M Fren.Core.PTy := do
  let (base, seg?) := splitPatternType segs
  let t ← elabBasePTy base
  let text := Fren.Core.typeText (← srcAt (← writtenTypeSpan segs))
  let some seg := seg? | return { t with text }
  -- Pattern types are not nested, also through an alias.
  if t.pat?.isSome then err (typeSpan base) (Fren.Core.nestedAliasMsg (← srcAt (typeSpan base)))
  let some p := seg.pattern? | internal seg.span "a pattern type's pattern"
  let (q, bs, _) ← resolvePattern { vars := #[], place := .prop } t.ty "x" false true p
  if let some b := bs[0]? then err b.ident.span (Fren.Core.patternTypeBinderMsg (identName b.ident.name))
  return { t with pat? := some q, text }

/-- The declared type `segs`, which has no pattern of its own. -/
partial def elabBasePTy (segs : Array Ident) : M Fren.Core.PTy := do
  if segs.size == 1 && segs[0]!.name == "Bool" then return .plain .bool
  if segs.size == 1 && segs[0]!.name == "Int" then return .plain .int
  if segs.size == 1 && segs[0]!.name == "Nat" then return .plain .nat
  if segs.size == 1 && segs[0]!.name == "String" then
    modify fun s => { s with usesStrings := true }
    return .plain .string
  -- An element type, which is never a `Nat` (`lang::nat_place`), and whose
  -- constraint, if any, quantifies over the elements, outside the decidable
  -- core (`lang::pattern_place`).
  let elem (segs : Array Ident) : M Fren.Core.PTy := do
    let t ← elabPTy segs
    if t.ty == .nat then err (typeSpan segs) (Fren.Core.natPlaceMsg .element)
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
    if let .enum p := tb then
      if let some d := (← get).dataOf? p then
        if Fren.Core.zeroSizedMapValues true d.ctors.size (d.ctors.any (!·.2.isEmpty)) then
          let s ← get
          let text (xs : Array Ident) (stop : Nat) :=
            (String.ofList (s.src.extract (typeSpan xs).start stop).toList).trimAscii.toString
          let sep := segs[a.size + 1]!.span
          -- To the `)` after `B`.
          let mut stop := (typeSpan b).stop
          while stop < s.src.size && s.src[stop]! != ')' do stop := stop + 1
          lint .zeroSizedMapValues { start := segs[0]!.span.start, stop := stop + 1 }
            (Fren.Core.zeroSizedMapValuesMsg (text a sep.start) (text b (typeSpan b).stop) d.ctors[0]!.1.toString)
    return { ty := .rel ta tb, elems := #[pa, pb] }
  match ← resolveWritten segs with
  | .item { kind := .enumItem, path, .. } => return .plain (.enum path)
  | .item { kind := .recordItem, path, .. } =>
    if let some u := (← get).newtypes.find? path then return .plain (.newtype path u)
    return .plain (.record path)
  | .item { kind := .typeItem, path, .. } =>
    if let some t := (← get).aliases.find? path then return t
    return .plain (.abstract path)
  | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.notATypeMsg r)
end

/-- The type written `segs`, without its patterns: the type that
expressions of it have. -/
def elabTy (segs : Array Ident) : M Ty := return (← elabPTy segs).ty

/-- The type of a quantifier's binder, written `segs`, which must not be a
component. -/
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
  | .enum p, .ctor idx args | .record p, .ctor idx args => Id.run do
    let some d := s.dataOf? p | return "?"
    let (c, fs) := d.ctors[idx]!
    if args.isEmpty then return d.ctorSym c
    return s!"({d.ctorSym c} {" ".intercalate ((args.zip fs).toList.map fun (w, (_, ft)) => s.valueSmt ft w)})"
  | _, _ => "?"

/-- The values of the declared type `t` in SMT-LIB, and how many there are,
if a quantifier ranges over it (`lang::quantified_type`): a type whose
values bring no constraint as `State.values` lists them, and one that does,
those that meet it (`Fren.Core.PTy.values`). -/
def binderValues (t : Fren.Core.PTy) : M (Option (Nat × Array String)) := do
  let st ← get
  if (t.cons st.shapeOf).isNone then
    let some n := st.valueCount t.ty | return none
    return some (n, (st.values Fren.Core.maxInstances t.ty).getD #[])
  let some n := t.count? st.shapeOf | return none
  if n > Fren.Core.maxInstances then return some (n, #[])
  let vs := (t.values st.shapeOf Fren.Core.maxInstances).getD #[]
  return some (n, vs.map (st.valueSmt t.ty))

/-- The bound names of a quantifier's binders `bs`, declared in `cx`, and
every combination of their values, as SMT-LIB terms, the last name
varying fastest (`Reqs/Lang/Quantifiers#meaning`). Each type must be one
that a quantifier ranges over (`lang::quantified_type`), the names
distinct, following the Boolean names rule and written with `!` exactly
when they shadow (`lang::shadowing`), and the combinations at most
`Fren.Core.maxInstances` (`lang::quantifier_size`). A bound name's term is
a symbol that no variable has, which each instance replaces. -/
def quantBinders (cx : ExprCtx) (bs : Array Binder) : M (Array CBinder × Array (Array String)) := do
  -- Distinct names (`lang::distinct_names`), by the names they declare.
  let ids := bs.flatMap (·.names)
  let declared := ids.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then err ids[k]!.span (Fren.Core.dupBoundMsg declared[k]!)
  let mut out : Array CBinder := #[]
  let mut sizes := #[]
  let mut listed := #[]
  for b in bs do
    let pt ← binderTy b.ty
    let t := pt.ty
    let some (n, vs) ← binderValues pt
      | err (typeSpan b.ty) (Fren.Core.quantifiedTypeMsg (if pt.pat?.isSome then pt.text else t.show) (t matches .set _ | .rel .. | .seq _))
    for x in b.names do
      let locals := Fren.Core.bindingLocals (cx.vars.map fun v => (v.name, v.role)) cx.insts
        ((cx.binders ++ out).map (·.what)) cx.selfFn.isSome cx.inGlobal
      let y ← declare x locals
      let bn := Name.mkSimple y.name
      liftMsg y.span (Fren.Core.checkVarName bn (some (t == .bool)))
      lintName .binder bn y.span
      let k := cx.binders.size + out.size
      out := out.push { name := bn, smt := quote s!"{k} {bn}", ty := t, scrutinee := none, outer := k }
      sizes := sizes.push n
      listed := listed.push vs
  let n := cx.instances * Fren.Core.instanceCount sizes
  unless Fren.Core.quantifierSizeAccepted n do
    err (bs[0]!.span.to bs.back!.span) (Fren.Core.quantifierSizeMsg n (cx.instances > 1))
  return (out, listed.foldl (fun acc vs => acc.flatMap fun pre => vs.map pre.push) #[#[]])

mutual
partial def elabExpr (cx : ExprCtx) (e : Expr) : M (String × Ty) := do
  let concatOk := cx.concatOk
  let expected? := cx.expected?
  let chain := cx.chain
  let parent? := cx.parent?
  let inElse := cx.inElse
  let cx := { cx with concatOk := false, expected? := none, chain := "", parent? := some e, inElse := false }
  -- What one operand expects of the other: its type, but a `Nat` only where
  -- one is expected of both.
  let sibling (cx' : ExprCtx) (t : Ty) : Option Ty := if cx'.expected? == some .nat then some .nat else some t.widen
  -- Two operands of the same type, each checked against the other's, when it
  -- does not synthesize its own (`lang::checked`).
  let pair (cxa cxb : ExprCtx) (a b : Expr) : M ((String × Ty) × (String × Ty)) := do
    if !synthesizes a && synthesizes b then
      let rb ← elabExpr cxb b
      return (← elabExpr { cxa with expected? := sibling cxa rb.2 } a, rb)
    let ra ← elabExpr cxa a
    return (ra, ← elabExpr { cxb with expected? := sibling cxb ra.2 } b)
  let expect (e : Expr) (t : Ty) (why : Option String := none) : M String := do
    let (s, t') ← elabExpr cx e
    liftMsg e.span (Fren.Core.checkType t t' why)
    return s
  -- An operand of arithmetic, `e` of type `t`, is an `Int` or a `Nat`.
  let number (e : Expr) (t : Ty) (op : String) : M Unit := liftMsg e.span (Fren.Core.checkNumber op t)
  let opNote := Fren.Core.opNote
  -- The operator `op` at `span`, prefix if `pre`, of operands of the types
  -- `tx` and `ty`: if one is a newtype, it must have `op`, and both must be
  -- of it (`lang::newtype_operator`).
  let newtypeOp (op : String) (span : Span) (tx ty : Ty) (pre := false) : M Unit := do
    let ordered ← match Fren.Core.newtypeOf? tx ty with
      | some (_, u) => isOrdered u
      | none => pure false
    liftMsg span (Fren.Core.checkNewtypeOperator op pre tx ty ordered)
  -- `length_zero`, `card_zero` and `absurd_extreme_comparisons` on `a op b`
  -- (`lint::length_zero`, `lint::absurd_extreme_comparisons`).
  let lintLength (op : String) (a b : Expr) : M Unit := do
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
  let src := (← get).src
  -- Where `e` is, as `lang::operand` sees it.
  let slot := parent?.bind (Expr.operandSlot src · e)
  -- `redundant_method_chain`, at the end of a chain (`lint::method_chain`):
  -- not on the receiver of a field or method read without arguments.
  let lintChain : M Unit := do
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
  match e with
  | .when span neg c d =>
    -- `eq_op` (`lint::eq_op_conditional`).
    if cx.noteIndexes then
      let tc ← srcAt c.span
      if let some v := Fren.Core.eqOpConditional neg (Fren.Core.writtenSame tc (← srcAt d.span)) then
        lint .eqOp span (Fren.Core.eqOpConditionalMsg neg v tc)
    let kw := if neg then "unless" else "when"
    let c ← expect c .bool (some s!"note: the condition of `{kw}` is a `Bool`")
    let g := (if neg then Fren.Core.GuardedOperand.unlessBody else .whenBody).guard c s!"(not {c})"
    let (d, td) ← elabExpr { cx with guards := cx.guards.push g } d
    unless td == .bool do mismatch e .bool td (some s!"note: the body of `{kw}` is a `Bool`")
    return (if neg then s!"(=> (not {c}) {d})" else s!"(=> {c} {d})", .bool)
  | .quant _ all bs body =>
    -- Expanded: the body, elaborated once, at each combination of the bound
    -- names' values (`Reqs/Lang/Quantifiers#meaning`), and so are the
    -- definedness goals of its indexes, and the questions about its
    -- tables, which hold in every instance.
    let (new, combos) ← quantBinders cx bs
    let outer ← takeIndexes
    let outerTables ← takeTables
    let natBefore := (← get).natApps.size
    let (b, tb) ← elabExpr { cx with binders := cx.binders ++ new, instances := cx.instances * combos.size } body
    let kw := if all then "forall" else "exists"
    unless tb == .bool do mismatch body .bool tb (some s!"note: the body of `{kw}` is a `Bool`")
    let syms := new.map (·.smt)
    let inst (smt : String) (vals : Array String) : String :=
      substQuoted (fun p => match syms.idxOf? (quote p) with | some i => vals[i]! | none => quote p) smt
    let inner ← takeIndexes
    let innerTables ← takeTables
    modify fun s => { s with indexes := outer ++ inner.map (fun (sp, g, t) => (sp, conj (combos.map (inst g)), t)),
                             tables := outerTables ++ innerTables.map fun (sp, q, g) => (sp, q, conj (combos.map (inst g))) }
    -- The `Nat` applications in the body, at each instance, as the solver sees them (`natFacts`).
    modify fun s => { s with natApps := s.natApps.extract 0 natBefore
      ++ ((s.natApps.extract natBefore).flatMap fun app => combos.map (inst app)).toList.eraseDups.toArray }
    let instances := combos.map (inst b)
    return (if all then conj instances else if instances.size == 1 then instances[0]! else s!"(or {" ".intercalate instances.toList})", .bool)
  | .not _ a => return (s!"(not {← expect a .bool (opNote "not" .bool)})", .bool)
  | .ite span c a b =>
    if cx.noteIndexes && !inElse then lintIfChain cx e
    -- `same_branches` (`lint::same_branches`).
    if cx.noteIndexes then
      let ta ← srcAt a.span
      if Fren.Core.sameBranches (Fren.Core.writtenSame ta (← srcAt b.span)) then
        let .mk kind .. := a.boolNode
        lintFix .sameBranches span (Fren.Core.sameBranchesMsg ta kind.prec (← srcAt { start := 0, stop := span.start })
          (← srcAt { start := span.stop, stop := (← get).src.size }))
    if cx.noteIndexes && (← mentionsAny cx c) then modify fun s => { s with mentioning := s.mentioning.push c.span }
    let c ← expect c .bool (some "note: the condition of `if` is a `Bool`")
    let gx := Fren.Core.GuardedOperand.thenBranch.guard c s!"(not {c})"
    let gy := Fren.Core.GuardedOperand.elseBranch.guard c s!"(not {c})"
    let ((x, tx), (y, ty)) ← pair { cx with expected?, guards := cx.guards.push gx }
      { cx with expected?, guards := cx.guards.push gy, inElse := true } a b
    liftMsg span (Fren.Core.checkBranches tx ty)
    return (s!"(ite {c} {x} {y})", tx.join ty)
  | .neg span a =>
    let (x, t) ← elabExpr cx a
    newtypeOp "-" span t t (pre := true)
    number a t "-"
    return (s!"(- {x})", .int)
  | .num _ v => return (toString v, Fren.Core.literalTy (expected? == some .nat))
  | .set span elems =>
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
        let (x, tx) ← elabExpr { cx with expected? := ea? } a
        let (y, ty) ← elabExpr { cx with expected? := eb? } b
        return (s!"{x} {y}", .rel tx.widen ty.widen)
      let (x, t) ← elabExpr { cx with expected? := expected?.bind fun | .set t => some t | _ => none } e
      return (x, .set t.widen)
    -- Each member is checked against the literal's type, or another's
    -- (`lang::checked`): the first that synthesizes one, if the first does not.
    let expected? ← if expected?.isNone && !synthesizes elems[0]! then
        match elems.find? synthesizes with
        | some m => do
          let saved ← get
          let t ← (·.2) <$> member m none
          set saved
          pure (some t)
        | none => pure none
      else pure expected?
    let (x0, t0) ← member elems[0]! expected?
    let mut xs := #[x0]
    for e in elems.extract 1 do
      let (x, t) ← member e (some t0)
      unless t == t0 do
        let (mt, mt0) := match t, t0 with | .set u, .set u0 => (u.show, u0.show) | _, _ => (t.show, t0.show)
        err e.span (Fren.Core.membersMsg false mt0 mt t0.show)
      xs := xs.push x
    let ts := xs.map (s!"(tuple {·})")
    let smt := if ts.size == 1 then s!"(set.singleton {ts[0]!})"
      else s!"(set.insert {" ".intercalate (ts.pop.toList)} (set.singleton {ts.back!}))"
    return (smt, t0)
  | .pair span .. => err span Fren.Core.pairPlaceMsg
  | .seq span elems =>
    modify fun s => { s with usesSeqs := true }
    if elems.isEmpty then
      let t ← liftMsg span (Fren.Core.checkEmptyLiteral true expected?)
      return (s!"(as seq.empty {t.sort})", t)
    -- Each element is checked against the literal's element type, or another's
    -- (`lang::checked`): the first that synthesizes one, if the first does not.
    let elemExpected ← match expected?.bind fun | .seq t => some t | _ => none with
      | some t => pure (some t)
      | none => if synthesizes elems[0]! then pure none else
          match elems.find? synthesizes with
          | some m => do
            let saved ← get
            let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } m
            set saved
            pure (some t)
          | none => pure none
    let (x0, t0) ← elabExpr { cx with expected? := elemExpected } elems[0]!
    -- An element is never a `Nat` (`lang::nat_place`).
    let t0 := t0.widen
    let mut xs := #[x0]
    for e in elems.extract 1 do
      let (x, t) ← elabExpr { cx with expected? := some t0 } e
      let t := t.widen
      unless t == t0 do
        err e.span (Fren.Core.membersMsg true t0.show t.show (Ty.seq t0).show)
      xs := xs.push x
    checkCore cx span .seqArray true true elems
    let us := xs.map (s!"(seq.unit {·})")
    return (if us.size == 1 then us[0]! else s!"(seq.++ {" ".intercalate us.toList})", .seq t0)
  | .index span q i =>
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
  | .str span v =>
    liftMsg span (Fren.Core.checkStringChars v)
    modify fun s => { s with usesStrings := true }
    return (Fren.Core.smtStringLit v, .string)
  | .method span recv m args =>
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
    let (r, t) ← elabExpr { cx with concatOk := true } recv
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
        | .seq elem, some method => match method.params[as.size]? with
          | some .string => some t | some .elem => some elem | some .int => some .int | _ => none
        -- A `Nat` is expected of `min`'s and `max`'s argument where one is of
        -- the whole (`lang::nat_result`).
        | .nat, some .min | .nat, some .max => expected?.filter (· == .nat)
        | _, _ => none
      let (x, ta) ← elabExpr { cx with expected? } a
      as := as.push (x, ta, a.span)
    -- Typed before it is linted, as in Lean, so that a call with a type
    -- error reports no lint of its own (`Reqs/View#static-errors`).
    let res ← callMethod m.span r t m.name as
    if let (.string, some method) := (t, Fren.Core.Method.ofName? m.name) then
      let constantArgs ← args.allM (isConstant cx)
      checkCore cx span method.construct constantArgs true (#[recv] ++ args) (constantArgs && (← isConstant cx recv))
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
  | .bool _ b => return (toString b, .bool)
  | .chain _ es ops =>
    -- `a < b <= c` is `a < b and b <= c`, with `b` elaborated once
    -- (`Reqs/Lang/Expressions#chained-comparisons`). As in that expansion,
    -- the comparisons before an operand guard it. The parser has checked
    -- its operators.
    let (x0, t0) ← elabExpr cx es[0]!
    -- The first operand gives the operands' type, a `Nat` widened
    -- (`lang::operator_type`); of a newtype, its underlying type's orderings,
    -- on the erased values (`lang::newtype_operator`).
    if let .newtype .. := t0 then newtypeOp ops[0]!.1 (es[0]!.span.to es[1]!.span) t0 t0
    let under := match t0 with | .newtype _ u => u | t => t
    let u ← liftMsg es[0]!.span (Fren.Core.orderingType ops[0]!.1 under (← isOrdered under))
    let t0 := if t0 matches .newtype .. then t0 else u
    -- An ordered enumeration's values compare by their positions.
    let ordinal ← orderedData? u
    let pos (smt : String) := match ordinal with | some d => d.ordinal smt | none => smt
    let mut (x, ca) := (x0, ← isConstant cx es[0]!)
    let mut links := #[]
    for (op, _) in ops, a in es, b in es.extract 1 do
      let (y, tb) ← elabExpr { cx with guards := cx.guards ++ links } b
      newtypeOp op (a.span.to b.span) t0 tb
      liftMsg b.span (Fren.Core.checkType t0 tb (Fren.Core.opNote op t0))
      let cb ← isConstant cx b
      if u == .string then
        checkCore cx (a.span.to b.span) .stringCompare true (ca || cb) #[a, b] (ca && cb)
      -- SMT-LIB has only `str.<` and `str.<=`.
      links := links.push <| if u != .string then s!"({op} {pos x} {pos y})" else match op with
        | "<" => s!"(str.< {x} {y})"
        | "<=" => s!"(str.<= {x} {y})"
        | ">" => s!"(str.< {y} {x})"
        | _ => s!"(str.<= {y} {x})"
      (x, ca) := (y, cb)
    return (s!"(and {" ".intercalate links.toList})", .bool)
  | .bin span op a b =>
    -- `eq_op` (`lint::eq_op`).
    if let (some o, true) := (Fren.Core.InfixOp.ofOp? op, cx.noteIndexes) then
      -- Only for an operator that `eqOp` can report, whatever the operands.
      if (Fren.Core.eqOp o true).isSome then
        let ta ← srcAt a.span
        if let some v := Fren.Core.eqOp o (Fren.Core.writtenSame ta (← srcAt b.span)) then lint .eqOp span (Fren.Core.eqOpMsg o v ta)
    match op with
    | "iff" | "or" | "and" =>
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
      if op == "and" && cx.noteIndexes then
        let qs ← indexedIn a
        if ← qs.anyM fun q => return (← boundsSeq b q) && !(← boundsSeq a q) then
          lintFix .indexAfterUse span (Fren.Core.indexAfterUseMsg (← srcAt a.span) (← srcAt b.span))
      -- For `manual_at_most_one`: whether the operands give a definedness
      -- obligation.
      let mark := (← get).indexes.size + (← get).tables.size
      let (x, tx) ← elabExpr { cx with chain := op } a
      unless tx == .bool do mismatch a .bool tx (opNote op .bool)
      -- `b` is evaluated when `a` does not decide the result.
      let guards := match op with
        | "and" => cx.guards.push (Fren.Core.GuardedOperand.andRight.guard x s!"(not {x})")
        | "or" => cx.guards.push (Fren.Core.GuardedOperand.orRight.guard x s!"(not {x})")
        | _ => cx.guards
      let (y, ty) ← elabExpr { cx with guards, chain := op } b
      unless ty == .bool do mismatch b .bool ty (opNote op .bool)
      if op == "and" && cx.noteIndexes && (← get).indexes.size + (← get).tables.size > mark then
        modify fun s => { s with facts := s.facts.push (span, .obligations) }
      return (s!"({smt} {x} {y})", .bool)
    | "=" | "!=" =>
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
    | "<" | "<=" | ">" | ">=" =>
      lintLength op a b
      -- The left operand gives the operands' type (`lang::operator_type`).
      let (x, tx) ← elabExpr cx a
      -- Of a newtype, its underlying type's ordering, on the erased values;
      -- of another type, a newtype on the right is the newtype's error
      -- (`lang::newtype_operator`).
      let (y, t) ← match tx with
        | .newtype _ u => do
          let (y, ty) ← elabExpr cx b
          newtypeOp op span tx ty
          pure (y, u)
        | _ => do
          let t ← liftMsg a.span (Fren.Core.orderingType op tx (← isOrdered tx))
          let (y, ty) ← elabExpr cx b
          newtypeOp op span tx ty
          liftMsg b.span (Fren.Core.checkType t ty (Fren.Core.opNote op t))
          pure (y, t)
      -- For the lints of integers, at the end of the expression: what it compares.
      if cx.noteIndexes && !(tx matches .newtype ..) then
        let ordered : Fren.Core.Ordered := if (← orderedData? t).isSome then .enumeration
          else if t == .int || t == .nat then .number else .other
        modify fun s => { s with ordereds := s.ordereds.push (span, ordered) }
      -- An ordered enumeration's values compare by their positions.
      if let some d ← orderedData? t then return (s!"({op} {d.ordinal x} {d.ordinal y})", .bool)
      unless t == .string do return (s!"({op} {x} {y})", .bool)
      let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
      checkCore cx span .stringCompare true (ca || cb) #[a, b] (ca && cb)
      -- SMT-LIB has only `str.<` and `str.<=`.
      return (match op with
        | "<" => Fren.Core.strCompareSmt x y false
        | "<=" => Fren.Core.strCompareSmt x y true
        | ">" => Fren.Core.strCompareSmt y x false
        | _ => Fren.Core.strCompareSmt y x true, .bool)
    | "in" =>
      -- Before its operands, whose errors would hide it, as in Lean.
      checkCore cx span .setAlgebra true true #[a, b]
      if let (.set _ #[m], true) := (b, cx.noteIndexes) then
        unless m matches .pair .. do lintFix .singletonMembership span (Fren.Core.singletonMembershipMsg (← srcAt a.span) (← srcAt m.span))
      if let some (pa, pb) := a.pair? (← get).src then
        let (x, tx) ← elabExpr cx pa
        let (y, ty) ← elabExpr cx pb
        let (tx, ty) := (tx.widen, ty.widen)
        let (r, tr) ← elabExpr { cx with expected? := some (.rel tx ty) } b
        unless tr == .rel tx ty do
          err span (Fren.Core.membershipTypeMsg (Ty.rel tx ty).show tr.show true)
        return (s!"(set.member (tuple {x} {y}) {r})", .bool)
      let (x, tx) ← elabExpr cx a
      -- A member is never a `Nat`: one is widened (`lang::nat_place`).
      let tx := tx.widen
      -- The right is checked against a set or sequence of the left's type, as
      -- it is written (`lang::checked`).
      let (y, ty) ← elabExpr { cx with expected? := some (if seqShaped b then .seq tx else .set tx) } b
      if ty == .seq tx then
        checkCore cx span .seqWord true true #[a, b] (← isConstant cx e) (literalOperand := b matches .seq ..)
        return (s!"(seq.contains {y} (seq.unit {x}))", .bool)
      unless ty == .set tx do
        err span { code? := some "F0325", headline := s!"`in` needs a `Set({tx.show})` on its right, found `{ty.show}`"
                   label? := some s!"`{tx.show}` and `{ty.show}`"
                   notes := #["note: `x in s` is membership: `s` is a set of values of `x`'s type"] }
      return (s!"(set.member (tuple {x}) {y})", .bool)
    | "union" | "inter" | "minus" | "subset" =>
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
    | "join" =>
      let (x, tx) ← elabExpr cx a
      let .rel ta tb := tx | err a.span (Fren.Core.joinTypeMsg tx.show none)
      -- Both operands synthesize their types (`lang::checked`).
      let (y, ty) ← elabExpr cx b
      let .rel tb' tc := ty | err b.span (Fren.Core.joinTypeMsg ty.show none)
      unless tb == tb' do err span (Fren.Core.joinTypeMsg tx.show (some ty.show))
      checkRelational cx span #[tb] #[a, b]
      return (s!"(rel.join {x} {y})", .rel ta tc)
    | "++" =>
      -- Each operand is checked against the whole's type, or the other's
      -- (`lang::checked`): `[] ++ q` takes its type from `q`.
      let expected? ← if expected?.isNone && !synthesizes a && synthesizes b then do
          let saved ← get
          let t ← (·.2) <$> elabExpr { cx with noteIndexes := false } b
          set saved
          pure (some t)
        else pure expected?
      let (x, tx) ← elabExpr { cx with expected?, concatOk := true } a
      newtypeOp op span tx tx
      if let .seq _ := tx then
        let (y, ty) ← elabExpr { cx with expected? := some tx } b
        liftMsg b.span (Fren.Core.checkConcatOperands tx ty)
        checkCore cx span .seqWord true true #[a, b] (← isConstant cx e)
        return (s!"(seq.++ {x} {y})", tx)
      -- Where the core allows it, only its operands' outputs matter.
      if concatOk then checkCore cx span .stringAtom true true #[a, b]
      else checkCore cx span .stringSearch true true #[a, b] (← isConstant cx e)
      unless tx == .string do mismatch a .string tx (opNote op .string)
      let (y, ty) ← elabExpr { cx with concatOk := true } b
      unless ty == .string do mismatch b .string ty (opNote op .string)
      return (s!"(str.++ {x} {y})", .string)
    | "div" | "mod" =>
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
    | _ =>
      if op == "*" then
        let (ma, mb) := (← mentionsAny cx a, ← mentionsAny cx b)
        unless cx.unmentioned || Fren.Core.productAccepted ma mb do err span Fren.Core.nonlinearMsg
        -- For `branches_sharing_code`.
        if cx.noteIndexes then
          modify fun s => { s with mentioning := s.mentioning ++ ([(ma, a.span), (mb, b.span)].filter (·.1) |>.map (·.2)) }
      -- `+` and `*` of `Nat`s are `Nat`s; `-` is always an `Int`, so that
      -- nothing truncates (`lang::operator_type`).
      let nat := op != "-" && expected? == some .nat
      if nat && op == "+" then modify fun s => { s with natSums := s.natSums.push (s.file, span) }
      let (x, tx) ← elabExpr { cx with expected? := if nat then some .nat else none } a
      -- Of a newtype, its underlying type's `+` or `-`, which it is erased
      -- to; of a number, a newtype on the right is the newtype's error.
      if let .newtype .. := tx then
        let (y, ty) ← elabExpr cx b
        newtypeOp op span tx ty
        return (s!"({op} {x} {y})", tx)
      number a tx op
      let (y, ty) ← elabExpr { cx with expected? := if nat then some .nat else none } b
      newtypeOp op span tx ty
      number b ty op
      return (s!"({op} {x} {y})", if op != "-" && tx == .nat && ty == .nat then .nat else .int)
  | .path _ segs =>
    if segs.size == 1 then
      lintChain
      let n := identName segs[0]!.name
      let span := segs[0]!.span
      -- A binder or variable, then any fields read from it.
      let base? ← if let some b := cx.binder? n.getRoot then do
          -- A bound name has no scrutinee: it mentions nothing.
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
          pure (some ((b.smt, b.ty), n.components.drop 1))
        else
          let ks := (List.range n.components.length).reverse.map (· + 1)
          match ks.findSome? fun k => (cx.vars.find? (·.name == (n.components.take k).foldl (· ++ ·) .anonymous)).map (·, k) with
          | some (v, k) =>
            -- A defined output mentions what its definition does.
            for u in if cx.unmentioned then #[] else defDeps cx.vars v do
              let earlier := (cx.insts.findIdx? (· == u.name.getRoot)).any (· < cx.current)
              let ok := match cx.refining? with
                | some rb => rb.checkMention u.role u.isPub u.name
                | none => Fren.Core.checkMention cx.place u.role earlier u.name
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
      return (ctorSym en.path en.variants[idx]!, .enum en.path)
    | .item { kind := .constItem, path, .. } =>
      let some c := (← get).consts.find? path | internal e.span s!"unknown constant `{path}`"
      return c
    | .item { kind := .fnItem, path, .. } => err e.span (Fren.Core.unappliedMsg path)
    | r => err e.span (Fren.Core.notAValueMsg r)
  | .app span segs args =>
    let fnSpan := segs[0]!.span.to segs.back!.span
    if segs.size == 1 && (cx.vars.any (·.name == identName segs[0]!.name) || (cx.binder? (identName segs[0]!.name)).isSome) then
      err fnSpan (Fren.Core.varNotAFunctionMsg (identName segs[0]!.name))
    if segs.size == 1 && cx.selfFn == some (Name.mkSimple segs[0]!.name) then
      err fnSpan (Fren.Core.recursiveMsg ((← get).module ++ Name.mkSimple segs[0]!.name))
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
          let (x, ta) ← elabExpr { cx with expected? := some .bool } a
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
      | .item { kind := .fnItem, path, .. } => pure path
      | .variant en idx =>
        -- A variant with a payload, built from its values.
        let v := en.variants[idx]!
        let some d := (← get).dataOf? en.path | internal fnSpan s!"unknown enum `{en.path}`"
        let tys := d.ctors[idx]!.2.map (·.2)
        if let some msg := Fren.Core.variantMentionMsg? (en.path ++ v) tys.size true then err span msg
        unless args.size == tys.size do err span (Fren.Core.arityMsg (en.path ++ v) tys.size args.size "value")
        let mut smts := #[]
        for a in args, t in tys, k in [0:args.size] do
          let (x, ta) ← elabExpr { cx with expected? := some t } a
          liftMsg a.span (Fren.Core.checkType t ta (some s!"note: value {k + 1} of the payload of `{showPath (en.path ++ v)}` has type `{t.show}`"))
          noteObligation cx .payload a.span (← partPTy en.path idx k) x
          smts := smts.push x
        return (s!"({ctorSym en.path v} {" ".intercalate smts.toList})", .enum en.path)
      | .item { kind := .recordItem, path, .. } =>
        -- A newtype, built from its value, which is erased
        -- (`Reqs/Lang/Expressions#newtypes`).
        let some u := (← get).newtypes.find? path | err fnSpan (Fren.Core.constructionMsg path false)
        unless args.size == 1 do err span (Fren.Core.arityMsg path 1 args.size "value")
        let (x, ta) ← elabExpr { cx with expected? := some u } args[0]!
        unless ta.widens u do mismatch args[0]! u ta (some s!"note: the value of `{showPath path}` has type `{u.show}`")
        if cx.noteIndexes then modify fun s => { s with facts := s.facts.push (span, .wraps path.toString (synthesizes args[0]!)) }
        noteObligation cx .construction args[0]!.span (← partPTy path 0 0) x
        return (x, .newtype path u)
      | r => err fnSpan (Fren.Core.notAFunctionMsg r)
    if let some (_, params, result, _) := (← get).defs.find? (·.1 == path) then
      -- Its arguments may mention anything (`lang::argument`).
      unless args.size == params.size do err span (Fren.Core.arityMsg path params.size args.size)
      let mut smts := #[]
      let ptys := ((← get).funPTys.find? path).map (·.1) |>.getD #[]
      for a in args, (_, t) in params, k in [0:args.size] do
        let (x, ta) ← elabExpr { cx with expected? := some t } a
        liftMsg a.span (Fren.Core.checkType t ta (some s!"note: argument {k + 1} of `{showPath path}` has type `{t.show}`"))
        noteObligation cx .argument a.span (ptys[k]?.getD default) x
        smts := smts.push x
      notePreconditions cx fnSpan path smts
      return (s!"({itemSym path} {" ".intercalate smts.toList})", result)
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
      let (x, ta) ← elabExpr { acx with expected? := some t } a
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
  | .field span a f =>
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
  | .record span tySegs fields =>
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
    for (f, t) in fs, k in [0:fs.size] do
      let some (fi, e?) := fields.find? (Name.mkSimple ·.1.name == f) | internal span s!"no field `{f}`"
      if let (some e, true) := (e?, cx.noteIndexes) then lintRedundant fi e true
      let e := e?.getD (.path fi.span #[fi])
      let (x, te) ← elabExpr { cx with expected? := some t } e
      liftMsg e.span (Fren.Core.checkType t te (some s!"note: `{f}` of `{showPath path}` has type `{t.show}`"))
      noteObligation cx .field e.span (← partPTy path 0 k) x
      smts := smts.push x
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
        -- A value has a type; an instance is not one.
        let ty? := match (elabExpr { cx with noteIndexes := false } r).run (← get) with
          | .ok ((_, ty), _) => some ty
          | .error _ => none
        if Fren.Core.unnecessaryStructInit fields.size (reads.size == fields.size) same ty?.isSome (ty? == some (.record path)) then
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
        let t? ← tryCatch (some <$> (·.2) <$> elabExpr { cx with noteIndexes := false, expected? := none } recv)
          fun _ => pure none
        set saved
        unless t? == some (Ty.record path) do continue
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
    return (s!"({recordCtorSym path} {" ".intercalate smts.toList})", .record path)
  | .update span base fields =>
    let (rv, tr) ← elabExpr { cx with expected? := none } base
    let .record path := tr | err base.span (Fren.Core.updateBaseMsg tr.show)
    let some d := (← get).dataOf? path | internal base.span s!"unknown record `{path}`"
    let fs := d.ctors[0]!.2
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
      let (x, te) ← elabExpr { cx with expected? := some t } e
      liftMsg e.span (Fren.Core.checkType t te (some s!"note: `{f}` of `{showPath path}` has type `{t.show}`"))
      noteObligation cx .field e.span (← partPTy path 0 k) x
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
    let lit := s!"({recordCtorSym path} {" ".intercalate smts.toList})"
    return (if bind then s!"(let (({r} {rv})) {lit})" else lit, .record path)
  | .match span scrutinee arms =>
    let (s, ts) ← elabExpr cx scrutinee
    unless ts matches .enum _ | .bool | .int | .nat | .string do err scrutinee.span (Fren.Core.scrutineeMsg ts.show)
    -- Each arm's pattern, its binders and its test.
    let mut resolved := #[]
    for (p, _, _) in arms do resolved := resolved.push (← resolvePattern cx ts s false false p)
    let pats := resolved.map (·.1)
    let guarded := arms.map (·.2.1.isSome)
    let unguardedExhaustive ← match Fren.Core.checkMatch (← patSigs) ts.patTy pats guarded with
      | .ok u => pure u
      | .error (some (i, some j), msg) => err arms[i]!.1.alternatives[j]!.span msg
      | .error (some (i, none), msg) => err arms[i]!.1.span msg
      | .error (none, msg) => err span msg
    if cx.noteIndexes then lintMatch cx e ts pats (parent?.bind (Expr.operandSlot (← get).src · e))
    let mut bodies : Array String := #[]
    let mut ty? : Option Ty := none
    let mut waiting : Array (Nat × ExprCtx × Expr) := #[]
    -- Where each arm is taken, if no earlier one is: its test and its
    -- guard; `none` for an arm taken wherever it is tried.
    let mut taken : Array (Option String) := #[]
    -- An arm's guard is guarded by its pattern's matching where no earlier
    -- arm is taken (`Fren.Core.GuardedOperand.armGuard`), and its body by
    -- its being the first arm taken (`Fren.Core.GuardedOperand.armBody`).
    -- They are built directly: their negations are never needed, so
    -- `guard` would only return them.
    for (_, guard?, body) in arms, (_, bs, test) in resolved do
      let armGuards := cx.guards ++ taken.filterMap (·.map (s!"(not {·})")) ++ test.toArray
      -- Distinct names (`lang::distinct_names`), by the names they declare,
      -- without the `!` of shadowing.
      let declared := bs.map fun b => Name.mkSimple (declaredIdent b.ident).1.name
      if let some k := (Fren.Core.repeatsAt declared)[0]? then
        err bs[k]!.ident.span (Fren.Core.dupPatternBinderMsg declared[k]!)
      let mut new : Array CBinder := #[]
      for b in bs do
        let locals := Fren.Core.bindingLocals (cx.vars.map fun v => (v.name, v.role)) cx.insts
          (cx.binders.map (·.what)) cx.selfFn.isSome cx.inGlobal
        let x ← declare b.ident locals
        let bn := Name.mkSimple x.name
        liftMsg x.span (Fren.Core.checkVarName bn (some (b.ty == .bool)))
        lintName .binder bn x.span
        new := new.push { name := bn, smt := b.smt, ty := b.ty, scrutinee := some scrutinee, outer := cx.binders.size }
      let gcx := { cx with binders := cx.binders ++ new, guards := armGuards }
      -- The guard, a `Bool`, checked as one (`Reqs/Lang/Expressions#matches`).
      let g? ← guard?.mapM fun g => do
        let (x, tg) ← elabExpr { gcx with expected? := none } g
        liftMsg g.span (Fren.Core.checkType .bool tg (some Fren.Core.armGuardNote))
        pure x
      let own := (test.toArray ++ g?.toArray)
      taken := taken.push (Fren.Core.allOf? andSmt own)
      -- Each body is checked against the whole's type, or another's
      -- (`lang::checked`): one that does not synthesize its own, before any
      -- other has given a type, waits for a later one that does.
      let bcx := { gcx with guards := armGuards ++ g?.toArray }
      -- Another arm's `Nat` is widened: a `Nat` is expected only of the whole.
      let shared? := expected?.orElse fun _ => ty?.map (·.widen)
      if shared?.isNone && !synthesizes body && arms.any (synthesizes ·.2.2) then
        waiting := waiting.push (bodies.size, bcx, body)
        bodies := bodies.push ""
        continue
      let (x, t) ← elabExpr { bcx with expected? := shared? } body
      ty? := some (← liftMsg body.span (Fren.Core.checkArm ty? t))
      bodies := bodies.push x
    for (k, bcx, body) in waiting do
      let (x, t) ← elabExpr { bcx with expected? := ty?.map (·.widen) } body
      if ty?.isSome then ty? := some (← liftMsg body.span (Fren.Core.checkArm ty? t))
      bodies := bodies.set! k x
    let ty := ty?.get!
    noteMatch cx span (arms.map (·.1.span)) taken guarded unguardedExhaustive
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
  | .table span rows =>
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
      let shared? := expected?.orElse fun _ => ty?.map (·.widen)
      if shared?.isNone && !synthesizes v && rows.any (synthesizes ·.2.2) then
        waiting := waiting.push (values.size, vcx, v)
        values := values.push ""
        continue
      let (x, t) ← elabExpr { vcx with expected? := shared? } v
      if let some t0 := ty? then
        liftMsg v.span (Fren.Core.checkRowType t0 t)
      ty? := some ((ty?.map (·.join t)).getD t)
      values := values.push x
    for (k, vcx, v) in waiting do
      let (x, t) ← elabExpr { vcx with expected? := ty?.map (·.widen) } v
      if let some t0 := ty? then
        liftMsg v.span (Fren.Core.checkRowType t0 t)
      ty? := ty?.map (·.join t)
      values := values.set! k x
    -- Each row's condition, or its `_`, which is last.
    noteTable cx span (rows.map fun (st, c?, _) => (c?.map (·.span)).getD st) conds defined wild
    let ty := ty?.get!
    -- The first row whose condition holds; with no `_` row, where none
    -- does, the table is unspecified, as an index out of range is.
    let mut out := if wild then values.back! else
      s!"(ite {conds.back!} {values.back!} {unspecified ty})"
    if !wild then modify fun s => { s with usesSeqs := true }
    for i in (List.range (values.size - 1)).reverse do
      out := s!"(ite {conds[i]!} {values[i]!} {out})"
    return (out, ty)
  | .is span scrutinee p =>
    let (s, ts) ← elabExpr cx scrutinee
    unless ts matches .enum _ | .bool | .int | .nat | .string do err scrutinee.span (Fren.Core.isScrutineeMsg ts.show)
    let (q, bs, test) ← resolvePattern cx ts s false true p
    match Fren.Core.checkPatternTest (← patSigs) ts.patTy q (bs.map (Name.mkSimple ·.ident.name)) with
    | .ok () => pure ()
    | .error (.binder k, msg) => err bs[k]!.ident.span msg
    | .error (.alternative j, msg) => err p.alternatives[j]!.span msg
    | .error (.whole, msg) => err p.span msg
    if cx.noteIndexes then
      -- `irrefutable_is` and `is_equality` (`lint::irrefutable_is`, `lint::is_equality`).
      let irrefutable := Fren.Core.irrefutableIs (Fren.Core.matchesEvery (← patSigs) ts.patTy q)
      if irrefutable then lint .irrefutableIs span (Fren.Core.irrefutableIsMsg ts.show (q matches .wild _))
      let texts ← p.alts.mapM (srcAt ·.span)
      if Fren.Core.isEquality texts.size (Fren.Core.equatable q texts) irrefutable then
        lintFix .isEquality span (Fren.Core.isEqualityMsg (scrutinee.text (← get).src) texts[0]!)
    return (test.getD "true", .bool)
  | .«let» _ defs body isWhere =>
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
    let (b, t) ← tryCatch (elabExpr { bcx with expected?, concatOk } body) fun f =>
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
    let locals := Fren.Core.bindingLocals (cx.vars.map fun v => (v.name, v.role)) cx.insts
      (cx.binders.map (·.what)) cx.selfFn.isSome cx.inGlobal
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
    let dcx := { cx with guards := #[], pending := pending.toArray, expected? := annot?
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
  if Fren.Core.assertionOnConstant (← mentionsAny cx e) then
    lint .assertionsOnConstants e.span (Fren.Core.assertionOnConstantMsg kind (match e with | .bool _ b => some b | _ => none))

/-- The conditions of a top-level `when`/`unless` chain, and their span. -/
partial def trigger? (cx : ExprCtx) : Expr → M (Option (String × Span))
  | .when span neg c d => do
    let (cs, _) ← elabExpr { cx with noteIndexes := false } c
    let cs := if neg then s!"(not {cs})" else cs
    let here : Span := { start := span.start, stop := c.span.stop }
    match ← trigger? cx d with
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
set's element type (`lang::field_type`). -/
def ownIn (segs : Array Ident) (name : Ident) : Bool × Bool :=
  let core := segs.filter fun s => s.name != Parser.setSeg && s.name != Parser.relSeg && s.name != Parser.relSep
    && s.name != Parser.seqSeg && !s.isPatternSeg
  let isName := core.size == 1 && core[0]!.name == name.name
  (isName && core.size == segs.size, core.size < segs.size && core.any (·.name == name.name))

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
  liftMsg name.span (Fren.Core.checkVarName n (t.map (· == .bool)))
  -- `redundant_bool_type` (`lint::redundant_bool_type`), but not of a
  -- pattern type, whose pattern the annotation holds.
  if let (some segs, true, false) := (ty?, Fren.Core.redundantBoolType n (t.map (· == .bool)), pt.any (·.pat?.isSome)) then
    let span ← annotationSpan (segs[0]!.span.to segs.back!.span)
    lintFix .redundantBoolType span (Fren.Core.redundantBoolTypeMsg n)
  return pt.getD (.plain .bool)

def varTy (ty? : Option (Array Ident)) (name : Ident) : M Ty := return (← varPTy ty? name).ty

/-- Records what an instance of `c`, written at `span`, brings to the current
comp's mix of relational operators and counting. -/
def noteCounts (c : CComp) (span : Span) : M Unit :=
  modify fun s => { s with relationalUsed := s.relationalUsed || c.relational
                           countSpans := if c.counts then s.countSpans.push span else s.countSpans }

/-- An instance whose comp has been resolved, before its bindings are
elaborated. -/
structure PendingInst where
  name : Ident
  comp : CComp
  bindings : Array (Ident × Option Expr)

/-- Resolves `inst x: p { bs }`: the instantiated comp and the instance's
variables, checking the names it binds (`inst::binding`). -/
def resolveInst (x : Ident) (p : Array Ident) (bs : Array (Ident × Option Expr)) :
    M (PendingInst × Array CVar) := do
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
  let own := c.vars.filterMap fun v =>
    if v.role == .input || v.role == .output then some (v.name, v.role) else none
  match Fren.Core.checkBindings path own (bs.map (Name.mkSimple ·.1.name)) with
  | .ok () => pure ()
  | .error (some i, msg) => err bs[i]!.1.span msg
  | .error (none, msg) => err x.span msg
  let vars := c.vars.map fun v =>
    let role := Role.ofInst v.role v.isPub
    -- An input's constraint is the instance's obligation, which the
    -- instance check asks, rather than a fact (`Reqs/Check#instance-assumptions`).
    { name := w ++ v.name, role, isPub := role == .instOutput, ty := v.ty, span := x.span, ptype := v.ptype
      fact? := if v.role == .input then none else v.fact?.map (rename w c.vars) }
  return ({ name := x, comp := c, bindings := bs }, vars)

/-- Elaborates the bindings of an instance. -/
def elabInst (cx : ExprCtx) (pi : PendingInst) : M CInst := do
  let w := Name.mkSimple pi.name.name
  let mut eqs := #[]
  let c := pi.comp
  for (b, e?) in pi.bindings do
    if let some e := e? then lintRedundant b e false
    let e := e?.getD (.path b.span #[b])
    let some v := cx.vars.find? (·.name == w ++ Name.mkSimple b.name)
      | internal b.span s!"no variable for `{b.name}`"
    let (smt, t) ← elabExpr { cx with expected? := some v.ty } e
    liftMsg e.span (Fren.Core.checkType v.ty t (some s!"note: `{b.name}` of `{showPath c.path}` has type `{v.ty.show}`"))
    -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
    if v.ty == .int && t == .int then modify fun s => { s with natKept := s.natKept.push (c.path, b.name) }
    lintBools e
    eqs := eqs.push s!"(= {quote v.name.toString} {smt})"
  modify fun s => { s with natApps := s.natApps ++ c.natApps.map (rename w c.vars) }
  -- Each input whose type has an obligation assumes it, before the
  -- component's own assumptions (`Reqs/Check#instance-assumptions`).
  let st ← get
  let typed := c.vars.filter (·.role == .input) |>.filterMap fun v =>
    v.ptype.obligation.map fun o => (Name.num v.name 0, v.ptype.text, rename w c.vars (consSmt st.dataOf? o (quote v.name.toString)))
  return {
    name := w, comp := c.path, span := pi.name.span, bindings := conj eqs
    behaviour := rename w c.vars c.meaning
    assumes := typed.map (fun (n, _, f) => (n, f)) ++ (c.props.filter (·.kind == .assume) |>.map fun a => (a.name, rename w c.vars a.smt))
    typed := typed.map fun (n, t, _) => (n, t)
    bounded := c.vars.any fun v => v.role == .input && v.ptype.obligation.any (·.quantifies) }

/-- Imports the path `segs`, written at `loc`, into the current module, or,
with `scope`, into the component of that path. -/
def declareUse (segs : Array Ident) (glob : Bool) (loc : UseLoc) (scope : Option Name := none) : M Unit := do
  let st ← get
  let u ← liftResolve segs (st.table.declareUse st.module (segNames segs) glob (scope.getD st.module))
  let record : Fren.Core.UseRecord := {
    module := u.scope, target := u.target, glob := u.glob
    unusedLevel := st.levels.get .unusedImports, globLevel := st.levels.get .globImports }
  modify fun s => { s with table := s.table.addUse u, useRecords := s.useRecords.push (record, loc.path),
                           useLocs := s.useLocs.push loc }

/-- Declares a component's `use`s, in the scope `path`, and makes it the
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

/-- Whether the `set_option fren.evidence` in effect sets checks to testing.
An invalid value, reported once where it is set (`F0214`), sets nothing. -/
def evidenceInEffect : M Bool := do
  match (← get).evidence? with
  | none => return false
  | some (value, _) => return (Fren.Core.evidenceTested? value).getD false

/-- The conjuncts of `e`, a constraint: the operands of its `and`s, not
through parentheses but its own (`lint::manual_nat`). -/
partial def constraintConjuncts (src : Array Char) (e : Expr) : Array Expr :=
  let rec go (top : Bool) (e : Expr) : Array Expr :=
    let bare := top || Fren.Core.withParens src (toRange e.span) == toRange e.span
    match e with
    | .bin _ "and" a b => if bare then go false a ++ go false b else #[e]
    | _ => #[e]
  go true e

/-- Records `manual_nat` in the component `comp` of `members`
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

/-- The checks of a comp with `members` that are tested
(`Reqs/Check#checking-by-testing`): `all` if the comp is set to testing,
then each member's own setting. -/
def testedOf (all : Bool) (members : Array Member) : M Fren.Core.Tested := do
  let mut pending : Option (Bool × Span) := none
  let mut expects := #[]
  let mut insts := #[]
  let mut dets := #[]
  let mut constraints := #[]
  for m in members do
    if let .evidence span value valueSpan := m then
      let some b := Fren.Core.evidenceTested? value | err valueSpan (Fren.Core.invalidEvidenceMsg value)
      pending := some (b, span)
      continue
    let set? := pending.map (·.1)
    match m, pending with
    | .prop .expect x _, _ | .prop .cover x _, _ => expects := expects.push (Name.mkSimple x.name, set?)
    -- By the names they declare, without the `!` of shadowing.
    | .inst x _ _, _ => insts := insts.push (Name.mkSimple (declaredIdent x).1.name, set?)
    | .var false _ true x _ _, _ => dets := dets.push (Name.mkSimple (declaredIdent x).1.name, set?)
    | _, some (_, span) =>
      let what := match m with
        | .prop .assume .. => "an assumption" | .prop .ensure .. => "a guarantee"
        | .var true .. => "an input" | .var .. => "an output that is not `det`" | _ => "a `use`"
      err span (Fren.Core.misplacedEvidenceMsg what)
    | _, none => pure ()
    match m with
    | .prop .assume x _ | .prop .ensure x _ => constraints := constraints.push (Name.mkSimple x.name)
    | .var false _ _ x _ (some _) => constraints := constraints.push (Name.mkSimple (declaredIdent x).1.name)
    | _ => pure ()
    pending := none
  if let some (_, span) := pending then err span (Fren.Core.misplacedEvidenceMsg "the end of the component")
  return Fren.Core.Tested.ofSettings all constraints expects insts dets

/-- Reports `arbitrary_source_item_ordering` on a component whose members,
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
      | .evidence .. => (.use, none, #[])
      | .use .. | .useGroup .. => (.use, none, #[])
      | .var true _ _ x _ _ => (.input, some x, #[])
      | .var false _ _ x _ defn? => (.output, some x, ((defn?.map mentions).getD #[]).map (·.getRoot))
      | .inst x _ bs => (.inst, some x, bs.foldl (init := #[]) fun acc (b, e?) =>
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

/-- A comp's variables, each reporting its own first static error, and one
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
        let ptype ← varPTy ty? x
        let ty := ptype.ty
        unless Fren.Core.variableTypeAccepted (role == .output) ((← get).unbounded ty) defn?.isSome do
          err x.span (Fren.Core.unboundedOutputMsg xn ptype.text)
        let fact? ← factOf ptype (quote xn.toString)
        return { name := xn, role, isPub := isPub', isDet, ty, span := x.span, defn?, ptype, fact? : CVar }
      | continue
    vars := vars.push v
  -- One cycle is reported.
  if let some (v, cycle) := vars.findSome? fun v => (defCycle? vars v.name).map (v, ·) then
    discard <| attempt (err (α := Unit) v.span (Fren.Core.cyclicDefinitionMsg cycle))
  return vars

/-- A comp's instances, whose variables follow the comp's own `vars`: the
instances still to elaborate, and all the variables. -/
def elabCompInsts (members : Array Member) (vars : Array CVar) : M (Array PendingInst × Array CVar) := do
  let mut vars := vars
  let mut pending := #[]
  for m in members do
    let .inst x p bs := m | continue
    -- Its name is checked once, whether or not it shadows.
    let x := (← attempt do
        let x ← declare x
        liftMsg x.span (Fren.Core.checkItemName "instance" (Name.mkSimple x.name))
        return x).getD (declaredIdent x).1
    let xn := Name.mkSimple x.name
    lintName .instance xn x.span
    let some (pi, ivars) ← attempt (resolveInst x p bs) | continue
    pending := pending.push pi
    vars := vars ++ ivars
    -- Its bindings give each input of its component a value, and the
    -- instance's assumption check reads them (`unused_assumption`).
    let reads := (pi.comp.vars.filter fun v => v.name.isAtomic && v.role == Role.input).map (pi.comp.path, ·.name)
    modify fun s => { s with globalReads := s.globalReads ++ reads }
  return (pending, vars)

/-- The bindings of a comp's instances `pending`, with their indexes and
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

/-- A comp's definitions, each after those it mentions, with their indexes
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
        let dcx : ExprCtx := { vars, insts := instNames, place := .prop, expected? := some v.ty, concatOk := true }
        let (smt, t) ← elabExpr dcx e
        liftMsg e.span (Fren.Core.checkType v.ty t (some s!"note: `{v.name}` has type `{v.ty.show}`, so its definition must too"))
        noteObligation dcx .definition e.span v.ptype smt
        lintBools e
        return (smt, (← takeIndexes).map fun (sp, g, t) => (v.name, Fren.Core.IndexPlace.prop, sp, g, t),
          (← takeTables).map fun (sp, q, g) => (v.name, Fren.Core.IndexPlace.prop, sp, q, g))
      | continue
    defs := defs.push (v.name, smt)
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (defs, indexes, tables)

/-- A comp's assumptions, requirements, expectations and cover goals, with
their indexes and questions about tables added to `indexes` and `tables`. -/
def elabCompConstraints (members : Array Member) (vars : Array CVar) (instNames : Array Name) (indexes : Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)))
    (tables : Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) : M (Array CProp × Array (Name × Fren.Core.IndexPlace × Span × String × Option (String × Bool)) × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  let mut indexes := indexes
  let mut tables := tables
  let mut props := #[]
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
        lintBools e
        lintConstant cx (match kind with | .assume => "assume" | .ensure => "ensure" | .expect => "expect" | .cover => "cover") e
        let trig ← trigger? cx e
        let place := if kind == .assume then Fren.Core.IndexPlace.assume else .prop
        return ({ kind, name := xn, span := x.span, smt, trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) : CProp },
          (← takeIndexes).map fun (sp, g, t) => (xn, place, sp, g, t), (← takeTables).map fun (sp, q, g) => (xn, place, sp, q, g))
      | continue
    props := props.push p
    indexes := indexes ++ idx
    tables := tables ++ mergeReachTables tbl
  return (props, indexes, tables)

/-- `duplicate_constraint` (`lint::duplicate_constraint`), of a comp's
constraints. -/
def lintDuplicateConstraints (members : Array Member) : M Unit := do
  let src := (← get).src
  -- Cover goals are compared with each other, and constraints with each other.
  let all := members.filterMap fun | .prop k x e => some (k.core, x, e) | _ => none
  for constraints in #[all.filter (·.1 != .cover), all.filter (·.1 == .cover)] do
    for (i, j) in Fren.Core.repeatedConstraints (← constraints.mapM fun (_, _, e) => srcAt (e.writtenSpan src)) do
      let (k, x, e) := constraints[i]!
      let (k', x', _) := constraints[j]!
      let msg := Fren.Core.duplicateConstraintMsg k' k x'.name
      if (Fren.Core.duplicateConstraint k' k true).2 then
        let stop := withLineComment src (Fren.Core.withParens src (toRange (e.writtenSpan src))).stop
        lintEdits .duplicateConstraint x.span msg #[(Fren.Core.deletionRange src { start := wordStart src x.span.start, stop }, "")]
      else lint .duplicateConstraint x.span msg

/-- `constant_output` and `definable_output` (`lint::output_lints`), of a
comp's outputs. -/
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
    let mentions ← match v.defn? with | some d => mentionsAny lcx d | none => pure true
    let (constant, definable) := Fren.Core.outputLints v.defn?.isSome mentions about.size equation
    if constant then lint .constantOutput v.span (Fren.Core.constantOutputMsg v.name)
    if definable then lint .definableOutput v.span (Fren.Core.definableOutputMsg v.name about[0]!.1)

/-- `trivial_cover` (`lint::trivial_cover`), of a comp's cover goals: each
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

/-- `case_split_guarantees` (`lint::case_split_guarantees`), of a comp's
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

/-- `unused_variables` and `unused_assumption` of the comp `n`, whose
members had no static error. -/
def lintCompUnused (n : Name) (members : Array Member) (vars : Array CVar) (instNames : Array Name) : M Unit := do
  let mentioned := members.foldl (init := #[]) fun acc m => match m with
    | .prop _ _ e | .var _ _ _ _ _ (some e) => acc ++ mentions e
    | .inst _ _ bs => bs.foldl (init := acc) fun acc (b, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple b.name]
    | _ => acc
  -- A public definition says what the output is, so it is used.
  let candidates := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
  for (x, v) in Fren.Core.unmentioned (candidates.map fun v => (v.name, v)) mentioned do
    lint .unusedVariables v.span (Fren.Core.unusedVariableMsg x false (v.role == .output))
  -- `unused_assumption` (`lint::unused_assumption`), unless the file reads
  -- one of the inputs (`finishLints`), or one that another assumption ties to
  -- a used variable, transitively.
  let others := members.foldl (init := #[]) fun acc m => match m with
    | .prop .assume _ _ => acc
    | .prop _ _ e | .var _ _ _ _ _ (some e) => acc ++ mentions e
    | .inst _ _ bs => bs.foldl (init := acc) fun acc (b, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple b.name]
    | _ => acc
  -- The uninterpreted functions that they apply link too.
  let acx : ExprCtx := { vars, insts := instNames, place := .prop }
  let others ← members.foldlM (init := others) fun acc m => match m with
    | .prop .assume _ _ => pure acc
    | .prop _ _ e | .var _ _ _ _ _ (some e) => return acc ++ (← appliedFns acx e)
    | .inst _ _ bs => bs.foldlM (init := acc) fun acc (_, e?) => match e? with
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

def elabComp (isPub : Bool) (name : Ident) (members : Array Member) (spans : Array Span) (openStop : Nat) : M Unit := do
  let n := Name.mkSimple name.name
  modify fun s => { s with outsideCore := false, relationalUsed := false, countSpans := #[], natApps := #[] }
  liftMsg name.span (Fren.Core.checkItemName "component" n)
  let module := (← get).module
  liftMsg name.span ((← get).table.checkFresh module n)
  lintName .component n name.span
  startDeclared
  declareMemberUses (module ++ n) members
  -- Distinct names (`lang::distinct_names`): variables, instances and
  -- constraints share one namespace.
  let named := members.filterMap fun
    | .var _ _ _ x _ _ | .inst x _ _ | .prop _ x _ => some x
    | _ => none
  -- By the names they declare, without the `!` of shadowing.
  let declared := named.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err named[k]!.span (Fren.Core.dupMemberMsg declared[k]!)
  lintMemberOrder members spans openStop
  modify fun s => { s with inCompBody := true }
  -- Each variable, instance, binding, definition and constraint reports its
  -- own first static error; after those of the variables, and of the
  -- instances, the item stops, since what follows would only repeat them
  -- (`Reqs/View#static-errors`).
  let vars ← elabCompVars members
  stopIfErrors
  let (pending, vars) ← elabCompInsts members vars
  stopIfErrors
  let instNames := pending.map (Name.mkSimple ·.name.name)
  let (insts, indexes, tables) ← elabCompBindings vars instNames pending
  let (defs, indexes, tables) ← elabCompDefinitions name vars instNames indexes tables
  let (props, indexes, tables) ← elabCompConstraints members vars instNames indexes tables
  lintManualNat (module ++ n) members
  lintDuplicateConstraints members
  let lcx : ExprCtx := { vars, insts := instNames, place := .prop }
  lintOutputs lcx members vars
  lintTrivialCover lcx members
  lintCaseSplitGuarantees lcx members vars
  -- The lints above are found despite a constraint's static error, as in
  -- Lean; `unused_variables`, and the rest, only without one.
  stopIfErrors
  lintCompUnused n members vars instNames
  let path := module ++ n
  let tested ← testedOf (← evidenceInEffect) members
  let (relational, counts) ← checkCounts
  modify fun s => { s with
    table := s.table.addItem { kind := .compItem, path, isPub, owner := s.module }
    scope := s.module
    comps := s.comps.push { path, file := s.file, span := name.span, vars, props, insts, defs, indexes, tables, decidable := !s.outsideCore
                            relational, counts, tested, natApps := s.natApps } }

/-- Elaborates `refine name: concrete refines abstract { bindings }` into
the comp that checks it (`Reqs/Lang/Refinement`): `concrete`'s inputs,
`abstract`'s assumptions, an instance of `concrete` named as it is,
`abstract`'s instances, and `abstract`'s requirements and definitions as
expectations, with `abstract`'s variables read as their bindings or as
`concrete`'s of the same names, and `concrete`'s outputs from the
instance. -/
def elabRefine (name : Ident) (concreteSegs abstractSegs : Array Ident) (bs : Array (Ident × Option Expr)) :
    M Unit := do
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "refinement" n)
  let module := (← get).module
  liftMsg name.span ((← get).table.checkFresh module n)
  let comp (segs : Array Ident) : M CComp := do
    let sp := segs[0]!.span.to segs.back!.span
    let path ← match ← resolve segs with
      | .item { kind := .compItem, path, .. } => pure path
      | r => err sp (Fren.Core.notACompMsg r)
    let some c := (← get).comps.find? (·.path == path) | internal sp s!"unknown comp `{path}`"
    return c
  let c ← comp concreteSegs
  let a ← comp abstractSegs
  let aSpan := abstractSegs[0]!.span.to abstractSegs.back!.span
  let bound := bs.map (Name.mkSimple ·.1.name)
  -- The bindings (`refinement::binding`).
  match Fren.Core.checkRefineBindings a.path ((a.vars.filter (·.name.isAtomic)).map (·.name)) bound with
  | .ok () => pure ()
  | .error (i, msg) => err bs[i]!.1.span msg
  -- The interface (`refinement::interface`), for the variables not bound.
  for v in a.vars.filter fun v => v.name.isAtomic && !bound.contains v.name do
    let cv? := c.vars.find? (·.name == v.name)
    let input := v.role == Role.input
    -- Widening in the direction values flow: an input's from `a`, an
    -- output's from `c`.
    let typed (cv : CVar) := if input then v.ty.widens cv.ty else cv.ty.widens v.ty
    let ok := Fren.Core.interfaceAccepted input cv?.isSome (cv?.any (·.role == Role.input))
      (cv?.any (·.isPub)) (cv?.any (v.ty.widens ·.ty)) (cv?.any (·.ty.widens v.ty))
    unless ok do
      let why := match cv? with
        | none => s!"it has no variable `{v.name}`"
        | some cv => if !typed cv then s!"its `{v.name}` has another type"
          else if input then s!"its `{v.name}` is not an input"
          else if cv.role == Role.input then s!"its `{v.name}` is an input, not an output"
          else s!"its output `{v.name}` is not public"
      err aSpan (Fren.Core.interfaceMsg c.path a.path v.name why)
    -- What it reads by name keeps an `Int` one (`lint::manual_nat`).
    if let some cv := cv? then
      let given (t : Ty) : Fren.Core.Given := if t == .int then .givenInt else .givenNat
      if let (concrete, .givenInt) := Fren.Core.refinementGiven input (given v.ty) (given cv.ty) then
        let kept := (if concrete then c.path else a.path, Fren.Core.nameText v.name)
        modify fun s => { s with natKept := s.natKept.push kept }
  -- The instance of `concrete`, named as it is.
  let w := Name.mkSimple (c.path.getString!)
  if a.insts.any (·.name == w) then err aSpan (Fren.Core.dupMemberMsg w)
  -- `a`'s assumptions are hypotheses here, so it reads each input of `a`,
  -- through its binding or by name (`unused_assumption`).
  let reads := (a.vars.filter fun v => v.name.isAtomic && v.role == Role.input).map (a.path, ·.name)
  modify fun s => { s with globalReads := s.globalReads ++ reads }
  -- The bindings, over `concrete`'s own variables, seen from outside, as
  -- the instance's: a defined output is an output (`refinement::mention`).
  let own := (c.vars.filter (·.name.isAtomic)).map fun v =>
    { v with role := if v.role == .input then .input else Role.ofInst v.role v.isPub, defn? := none }
  -- The mix of relational operators and counting, as in a component
  -- (`Reqs/Lang/Decidability#relations`): `concrete`'s, `abstract`'s and
  -- the bindings'.
  modify fun s => { s with outsideCore := false, relationalUsed := false, countSpans := #[], natApps := #[] }
  noteCounts c (concreteSegs[0]!.span.to concreteSegs.back!.span)
  noteCounts a aSpan
  discard takeIndexes
  discard takeTables
  let mut bindings := #[]
  for (b, e?) in bs do
    let e := e?.getD (.path b.span #[b])
    let some v := a.vars.find? (·.name == Name.mkSimple b.name) | internal b.span s!"no variable for `{b.name}`"
    let cx : ExprCtx := { vars := own, place := .prop, expected? := some v.ty
                          refining? := some { concrete := c.path, abstract := a.path, input := v.role == .input } }
    let (smt, t) ← elabExpr cx e
    liftMsg e.span (Fren.Core.checkType v.ty t (some s!"note: `{b.name}` of `{showPath a.path}` has type `{v.ty.show}`"))
    -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
    if v.ty == .int && t == .int then modify fun s => { s with natKept := s.natKept.push (a.path, b.name) }
    lintBools e
    bindings := bindings.push (v, smt, ← takeIndexes, ← takeTables)
  let (relational, counts) ← checkCounts
  let afterBindings ← get
  -- `concrete`'s variables as a binding reads them, its outputs from the instance.
  let ownC (smt : String) := rename w (own.filter (·.role != .input)) smt
  -- `abstract`'s variables: their bindings, or else `concrete`'s of the same names.
  let outs := a.vars.filter fun v => v.name.isAtomic && v.role == .output
  let ren (smt : String) := substQuoted (fun p => match bindings.find? (·.1.name.toString == p) with
    | some (_, b, _, _) => ownC b
    | none => if outs.any (·.name.toString == p) then quote (w ++ identName p).toString else quote p) smt
  -- An input that `a` reads has `a`'s type, which widens to `c`'s
  -- (`refinement::interface`).
  let inputs := (c.vars.filter fun v => v.name.isAtomic && v.role == .input).map fun v =>
    -- It brings what `a`'s type of it brings, and an input that `a` does
    -- not read brings nothing (`Reqs/Lang/Refinement#the-interface`).
    match a.vars.find? fun u => u.name == v.name && u.role == .input && !bound.contains u.name with
    | some u => { v with ty := u.ty, ptype := u.ptype, fact? := u.fact? }
    | none => { v with fact? := none }
  -- `c`'s inputs' constraints are its instance's obligations.
  let vars := inputs ++ c.vars.map (fun v =>
      let role := Role.ofInst v.role v.isPub
      { v with name := w ++ v.name, role, isPub := role != .instHidden, isDet := false, defn? := none
               fact? := if v.role == .input then none else v.fact?.map (rename w c.vars) })
    ++ a.vars.filter (!·.name.isAtomic)
  let st ← get
  let typed := c.vars.filter (·.role == .input) |>.filterMap fun v =>
    v.ptype.obligation.map fun o => (Name.num v.name 0, v.ptype.text, rename w c.vars (consSmt st.dataOf? o (quote v.name.toString)))
  let instC : CInst := { name := w, comp := c.path, span := name.span
                         bindings := conj (inputs.map fun v => s!"(= {quote (w ++ v.name).toString} {quote v.name.toString})")
                         behaviour := rename w c.vars c.meaning
                         assumes := typed.map (fun (n, _, f) => (n, f))
                           ++ (c.props.filter (·.kind == .assume)).map fun p => (p.name, rename w c.vars p.smt)
                         typed := typed.map fun (n, t, _) => (n, t)
                         bounded := c.vars.any fun v => v.role == .input && v.ptype.obligation.any (·.quantifies) }
  -- `a`'s instances are hypotheses: their assumptions are `a`'s own
  -- obligations, checked in `a` (`Reqs/Lang/Refinement#the-obligation`).
  let insts := #[instC] ++ a.insts.map fun i =>
    { i with bindings := ren i.bindings, behaviour := ren i.behaviour, assumes := #[] }
  -- Reported at the refinement (`Reqs/Lang/Refinement#the-obligation`).
  let props := (a.props.filter (·.kind == .assume)).map (fun p => { p with smt := ren p.smt, span := name.span, triggerSpan? := none })
    ++ (a.props.filter (·.kind == .ensure)).map (fun p =>
      -- No triggers, as in Lean: vacuity does not run on a refinement.
      { p with kind := .expect, smt := ren p.smt, trigger? := none, span := name.span, triggerSpan? := none })
    ++ a.defs.map fun (d, e) =>
      { kind := .expect, name := d, span := name.span
        smt := s!"(= {ren (quote d.toString)} {ren e})", trigger? := none, triggerSpan? := none : CProp }
  -- Reported at the refinement, as its other checks are.
  let indexes := a.indexes.map fun (x, place, _, goal, t) =>
    (x, (match place with | .binding k => .binding (k + 1) | p => p), name.span, ren goal, t)
  -- A binding's, where it is read (`Reqs/Lang/Refinement#bindings`): an
  -- input's under the assumptions, an output's as a requirement.
  let indexes := indexes ++ bindings.flatMap fun (v, _, idx, _) => idx.map fun (sp, g, t) =>
    (v.name, if v.role == .input then .binding 0 else .prop, sp, ownC g, t)
  -- What the types of `a`'s outputs bring, checked as its guarantees are
  -- (`Reqs/Lang/Refinement#the-interface`): an obligation of each.
  let st ← get
  let indexes := indexes ++ (a.vars.filter fun v => v.name.isAtomic && v.role == .output && v.defn?.isNone).filterMap fun v =>
    v.ptype.obligation.map fun o =>
      (v.name, .prop, name.span, ren (consSmt st.dataOf? o (quote v.name.toString)), some (v.ptype.text, o.quantifies))
  -- And the questions about tables, as the indexes.
  let tables := a.tables.map fun (x, place, _, q, goal) =>
    (x, (match place with | .binding k => .binding (k + 1) | p => p), name.span, q, ren goal)
  let tables := tables ++ bindings.flatMap fun (v, _, _, tbl) => tbl.map fun (sp, q, g) =>
    (v.name, if v.role == .input then .binding 0 else .prop, sp, q, ownC g)
  let tested := Fren.Core.Tested.ofSettings (← evidenceInEffect)
    -- The bindings too, for the definedness of their indexes.
    ((a.props.filter (·.kind == .assume)).map (·.name) ++ bound) (props.filter (·.kind == .expect) |>.map (·.name, none))
    -- `a`'s instances too, for the definedness of their bindings.
    (#[(w, none)] ++ a.insts.map (·.name, none)) #[]
  -- The applications in the bindings, `concrete`'s and `abstract`'s.
  let natApps := afterBindings.natApps.map ownC ++ c.natApps.map (rename w c.vars) ++ a.natApps.map ren
  modify fun s => { s with
    table := s.table.addItem { kind := .expectItem, path := module ++ n, isPub := false, owner := s.module }
    refinements := s.refinements.push { path := module ++ n, file := s.file, span := name.span, vars, props, insts
                                        indexes, tables, decidable := c.decidable && a.decidable && !afterBindings.outsideCore
                                        relational, counts, tested, natApps } }

/-- The component that a global expectation's binder of type `segs` ranges
over the behaviours of, or `none` if it ranges over the values of a type
(`lang::quantifier_binder`), which a quantifier checks. A path that names
neither is an error. -/
def globalBinderComp? (segs : Array Ident) : M (Option Name) := do
  if [Parser.setSeg, Parser.seqSeg, Parser.relSeg].contains segs[0]!.name
      || (segs.size == 1 && ["Bool", "Int", "Nat", "String"].contains segs[0]!.name) then
    return none
  match ← resolve segs with
  | .item { kind := .compItem, path, .. } => return some path
  | .item { kind := .enumItem, .. } | .item { kind := .recordItem, .. } | .item { kind := .typeItem, .. } => return none
  | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.wrongKindMsg "a component or a type" r)

/-- Elaborates a global expectation (`Reqs/Lang/Global`). -/
def elabGlobal (name : Ident) (binders : Array Binder) (body : Expr) : M Unit := do
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkNoBang n)
  let all ← evidenceInEffect
  if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  modify fun s => { s with outsideCore := false, relationalUsed := false, countSpans := #[], natApps := #[] }
  let module := (← get).module
  liftMsg name.span ((← get).table.checkFresh module n)
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
  let mut vars : Array CVar := #[]
  let mut insts : Array CInst := #[]
  -- Distinct names (`lang::distinct_names`).
  let binderIds := binders.flatMap (·.names)
  -- By the names they declare, without the `!` of shadowing.
  let declared := binderIds.map fun x => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt declared)[0]? then
    err binderIds[k]!.span (Fren.Core.dupBinderMsg declared[k]!)
  -- The binders over values, a quantifier around the body (`lang::quantifier_binder`).
  let mut valueBinders := #[]
  for b in binders do
    let p := b.ty
    let path ← match ← globalBinderComp? p with
      | some path => pure path
      | none => valueBinders := valueBinders.push b; continue
    let xs := b.names
    let some c := (← get).comps.find? (·.path == path) | internal p[0]!.span s!"unknown comp `{path}`"
    unless c.decidable do
      modify fun s => { s with outsideCore := true }
      lint .undecidable (p[0]!.span.to p.back!.span) (Fren.Core.undecidableInstMsg path)
    noteCounts c (p[0]!.span.to p.back!.span)
    for x in xs do
      let x ← declare x
      let w := Name.mkSimple x.name
      liftMsg x.span (Fren.Core.checkItemName "instance" w)
      lintName .instance w x.span
      -- Like an instance's, but its inputs are shown in counterexamples.
      vars := vars ++ c.vars.map fun v =>
        let role := Role.ofInst v.role v.isPub
        { name := w ++ v.name, role, isPub := role != .instHidden, ty := v.ty, span := x.span, ptype := v.ptype
          fact? := v.fact?.map (rename w c.vars) }
      -- Its assumptions are hypotheses, not obligations.
      insts := insts.push { name := w, comp := path, span := x.span, bindings := "true",
                            behaviour := rename w c.vars c.meaning, assumes := #[] }
      modify fun s => { s with natApps := s.natApps ++ c.natApps.map (rename w c.vars) }
  let cx : ExprCtx := { vars, insts := insts.map (·.name), place := .prop, inGlobal := true }
  discard takeIndexes
  discard takeTables
  let quantified := if valueBinders.isEmpty then body
    else .quant { start := valueBinders[0]!.span.start, stop := body.span.stop } true valueBinders body
  let (smt, t) ← elabExpr cx quantified
  let indexes := (← takeIndexes).map fun (sp, g, t) => (n, Fren.Core.IndexPlace.prop, sp, g, t)
  let tables := (← takeTables).map fun (sp, q, g) => (n, Fren.Core.IndexPlace.prop, sp, q, g)
  liftMsg body.span (Fren.Core.checkType .bool t (some "note: an expectation is a `Bool`"))
  lintBools body
  lintConstant cx "expect" body
  let binders := insts.map fun i => (i.name, i.span)
  for (w, sp) in Fren.Core.unmentioned binders ((mentions body).map (·.getRoot)) do
    lint .unusedVariables sp (Fren.Core.unusedVariableMsg w true false)
  -- What it reads through instances (`unused_assumption`).
  let reads := (mentions body).filterMap fun m => match m.components with
    | [w, x] => (insts.find? (·.name == w)).map fun i => (i.comp, x)
    | _ => none
  -- And the uninterpreted functions it applies, which its binders'
  -- assumptions may constrain.
  let fns ← appliedFns cx body
  let reads := reads ++ insts.flatMap fun i => fns.map (i.comp, ·)
  modify fun s => { s with globalReads := s.globalReads ++ reads }
  -- `unrelated_binders` (`lint::unrelated_binders`).
  let groups := Fren.Core.binderGroups (insts.map (·.name)) ((boolAtoms body).map fun a => (mentions a).map (·.getRoot))
  if Fren.Core.unrelatedBinders groups.size then
    lint .unrelatedBinders name.span (Fren.Core.unrelatedBindersMsg name.name groups)
  let trig ← trigger? cx quantified
  lintDeclared .global n name.span
  let prop : CProp := { kind := .expect, name := n, span := name.span, smt
                        trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) }
  discard checkCounts
  modify fun s => { s with
    table := s.table.addItem { kind := .expectItem, path := module ++ n, isPub := false, owner := s.module }
    globals := s.globals.push { path := s.module, file := s.file, span := name.span, vars, props := #[prop], insts, indexes, tables
                                decidable := !s.outsideCore, natApps := s.natApps
                                tested := Fren.Core.Tested.ofSettings all #[] #[(n, none)] #[] #[] } }

/-- Elaborates the clauses of the contract of the function `n` at `path`,
whose parameters are `vars`, and records the contract, and each clause's
definition for the prelude (`Reqs/Lang/Items#contracts`). Gives each
clause as a constraint of the function's body's comp, named after the
function and the clause, a postcondition only if the function is defined;
and the questions about the tables and applications in them: a
precondition's under the other preconditions, a postcondition's under all
of them. -/
def elabContract (path n : Name) (defined : Bool) (vars : Array CVar) (clauses : Array (Bool × Ident × Expr)) (result : Ty)
    (span : Span) : M (Array CVar × Array CProp × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String)) := do
  -- The clauses' names share one namespace with the parameters
  -- (`lang::distinct_names`).
  let names := vars.map (·.name) ++ clauses.map fun (_, x, _) => Name.mkSimple (declaredIdent x).1.name
  if let some k := (Fren.Core.repeatsAt names)[0]? then
    if k ≥ vars.size then err clauses[k - vars.size]!.2.1.span (Fren.Core.dupClauseMsg names[k]!)
  let mut k : Contract := { defined }
  let mut props := #[]
  let mut sites := #[]
  for (post, x, e) in clauses do
    let cn := Name.mkSimple x.name
    liftMsg x.span (Fren.Core.checkNoBang cn)
    lintName .constraint cn x.span
    if x.name.endsWith "?" then err x.span (Fren.Core.propNameMsg cn)
    discard takeTables
    let (smt, t) ← elabExpr { vars, place := .prop, contract? := some (path, post, vars.map (·.name)) } e
    liftMsg e.span (Fren.Core.checkType .bool t (some "note: a clause of a contract is a `Bool`"))
    let place := if post then Fren.Core.IndexPlace.body else .assume
    sites := sites ++ (← takeTables).map fun (sp, q, g) => (n ++ cn, place, sp, q, g)
    lintBools e
    let sym := clauseSym path cn
    modify fun s => { s with clauseDefs := s.clauseDefs.push (sym, vars.map fun v => (v.name, v.ty), smt) }
    if post then k := { k with posts := k.posts.push (cn, sym) } else k := { k with pres := k.pres.push (cn, sym) }
    -- An uninterpreted function's postcondition is of its value, for its
    -- contract's realizability: the function applied to its parameters is
    -- the value (`Reqs/Check#contracts-of-uninterpreted-functions`).
    let app := s!"({itemSym path} {" ".intercalate (vars.toList.map fun v => quote v.name.toString)})"
    let value := quote (Fren.Core.contractValueName n (vars.map (·.name))).toString
    let smt := if post && !defined then smt.replace app value else smt
    props := props.push ({ kind := if post then .ensure else .assume, name := n ++ cn, span := x.span, smt
                           trigger? := none, triggerSpan? := none } : CProp)
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
def noteResultFact (path : Name) (rp : Fren.Core.PTy) : M Unit := do
  let st ← get
  if (← consOf rp).isNone then return
  let some c := rp.cons st.shapeOf (rp.ty == .nat) | return
  modify fun s => { s with funFacts := s.funFacts.insert (itemSym path) (consSmt st.dataOf? c factHole)
                           quantifiedFns := if c.quantifies then s.quantifiedFns.insert (itemSym path) else s.quantifiedFns }

/-- Records the tables of the body of the function `n`, whose parameters
are `vars`, or of the value of the constant `n`, just elaborated, its
pattern types' `obligations`, and the questions about the tables and
applications of the function's contract and its clauses, `contract`, as a
comp for their checks (`State.bodies`), if it has any questions or
postconditions to check. -/
def noteBody (n : Name) (span : Span) (vars : Array CVar)
    (contract : Array CProp × Array (Name × Fren.Core.IndexPlace × Span × Fren.Core.TableGoal × String) := (#[], #[]))
    (fn? : Option Name := none) (obligations : Array (Span × String × Option (String × Bool)) := #[]) : M Unit := do
  let tables := (← takeTables).map fun (sp, q, g) => (n, Fren.Core.IndexPlace.body, sp, q, g)
  -- The indexes of its contract's clauses are not checked, nor their
  -- values given where pattern types are declared.
  discard takeIndexes
  let (props, sites) := contract
  -- Its indexes are not checked either.
  let obligations := obligations.filter (·.2.2.isSome)
  if tables.isEmpty && sites.isEmpty && obligations.isEmpty && !props.any (·.kind == .ensure) then return
  modify fun s => { s with
    bodies := s.bodies.push { path := s.module, file := s.file, span, vars, props, decidable := !s.outsideCore
                              tables := tables ++ sites, natApps := s.natApps, bodyOf? := some n, fn?
                              indexes := obligations.map fun (sp, g, t) => (n, .body, sp, g, t) } }

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

/-- Records that the settings that set `lints` here are in effect at an
item, or at a setting that reads their level (`unused_lint_setting`). -/
def noteSettingsSeen (lints : Array Lint := Lint.all) : M Unit :=
  modify fun s => { s with seenSettings := lints.foldl (init := s.seenSettings) fun acc l =>
    match (s.levels.get l).setting? with
    | some i => if acc.contains i then acc else acc.push i
    | none => acc }

partial def elabItem (item : Item) : M Unit := do
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
        lintName .module (Name.mkSimple seg.name) seg.span
        if let some msg := Fren.Core.moduleInceptionMsg? i.path then lint .moduleInception seg.span msg
        if let some msg := Fren.Core.moduleNameMsg? .module i.path.getPrefix (Name.mkSimple seg.name) then
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
  | .enum isPub name variants isOrdered => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "enum" n)
    let module := (← get).module
    liftMsg name.span ((← get).table.checkFresh module n)
    lintName .enumeration n name.span
    let path := module ++ n
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
      let mut recursive := false
      for segs in payload?.getD #[], k in [0:(payload?.getD #[]).size] do
        -- The enum's own name, which is not declared yet (`lang::field_type`).
        let (own, ownInSet) := ownIn segs name
        let tspan := typeSpan segs
        if ownInSet then err tspan (Fren.Core.recursiveSetMsg path)
        let pt ← if own then pure (.plain (Ty.enum path)) else elabPTy segs
        let t := pt.ty
        pts := pts.push (pt, tspan)
        let abstract := t.abstractWithin?
        unless Fren.Core.fieldTypeAccepted abstract.isSome own ownInSet true do
          err tspan (Fren.Core.abstractFieldMsg (abstract.getD path) true (!(t matches .abstract _)))
        recursive := recursive || own
        unbounded := unbounded || own || (← get).unbounded t
        fs := fs.push (Name.mkSimple (toString k), t)
      if recursive then nRecursive := nRecursive + 1
      ctors := ctors.push (vn, fs)
      payloadTys := payloadTys.push pts
    unless Fren.Core.wellFounded variants.size nRecursive do err name.span (Fren.Core.illFoundedMsg n)
    -- A recursive enumeration's payloads are never `Nat`s (`lang::nat_place`),
    -- and a constraint of one is outside the decidable core
    -- (`lang::pattern_place`).
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
    -- (`lang::ordered_enumeration`); the first payload is reported.
    let withPayload := variants.filter (·.2.isSome)
    unless Fren.Core.orderedEnumAccepted isOrdered withPayload.size do
      let (v, _) := withPayload[0]!
      err v.span (Fren.Core.orderedPayloadMsg n (Name.mkSimple v.name))
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .enumeration, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := (s.table.addItem { kind := .enumItem, path, isPub, owner := s.module }).addEnum { path, variants := vs }
      datatypes := s.datatypes.push { path, isRecord := false, ctors, unbounded, ordered := isOrdered : DataDecl }.withPrelude
      shapes := s.shapes.insert path shape }
    -- Each read of a recursive enumeration's payload brings the payload's
    -- constraint (`Fren.Core.readCons`), as an application does.
    if isRecursive then
      let st ← get
      let some d := st.dataOf? path | pure ()
      for (c, fs) in ctors, v in [0:ctors.size] do
        for k in [0:fs.size] do
          if let some c' := Fren.Core.readCons st.shapeOf path v k then
            modify fun s => { s with funFacts := s.funFacts.insert (d.selSym c k) (consSmt st.dataOf? c' factHole) }
  | .record isPub name fields => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "record" n)
    let module := (← get).module
    liftMsg name.span ((← get).table.checkFresh module n)
    lintName .record n name.span
    let path := module ++ n
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
        let (own, ownInSet) := ownIn segs name
        if own then err (segs[0]!.span.to segs.back!.span) (Fren.Core.recursiveRecordMsg n)
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
    let unbounded := fs.any fun (_, t) => st.unbounded t
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .record, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      datatypes := s.datatypes.push { path, isRecord := true, ctors := #[(`«{}», fs)], unbounded : DataDecl }.withPrelude
      shapes := s.shapes.insert path { isRecord := true, parts := #[fieldTys] } }
  | .newtype isPub name fields => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "record" n)
    let module := (← get).module
    liftMsg name.span ((← get).table.checkFresh module n)
    lintName .record n name.span
    let path := module ++ n
    -- Exactly one field, whose type is accepted as a record's field's
    -- (`lang::newtype`).
    let some segs := fields[0]? | err name.span (Fren.Core.newtypeFieldsMsg path 0)
    unless Fren.Core.newtypeAccepted fields.size true do err name.span (Fren.Core.newtypeFieldsMsg path fields.size)
    let span := typeSpan segs
    let (own, ownInSet) := ownIn segs name
    if own then err span (Fren.Core.recursiveRecordMsg n)
    if ownInSet then err span (Fren.Core.recursiveSetMsg path)
    let pt ← elabPTy segs
    let t := pt.ty
    if let some p := t.abstractWithin? then err span (Fren.Core.abstractFieldMsg p false (!(t matches .abstract _)))
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .record, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      newtypes := s.newtypes.insert path t
      shapes := s.shapes.insert path { isRecord := true, isNewtype := true, parts := #[#[pt]] } }
  | .typeAlias isPub name ty => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "type alias" n)
    let module := (← get).module
    liftMsg name.span ((← get).table.checkFresh module n)
    lintName .typeAlias n name.span
    let t ← elabPTy ty
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .typeAlias, path := module ++ n, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path := module ++ n, isPub, owner := s.module }
      aliases := s.aliases.insert (module ++ n) t }
  | .abstractType isPub name => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "abstract type" n)
    let module := (← get).module
    liftMsg name.span ((← get).table.checkFresh module n)
    lintName .abstractType n name.span
    let path := module ++ n
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .abstractType, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
      sorts := s.sorts.push path }
  | .function isPub name params result body clauses last => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkNoBang n)
    liftMsg name.span (Fren.Core.checkFnName n)
    let module := (← get).module
    liftMsg name.span ((← get).table.checkFresh module n)
    lintName .function n name.span
    startDeclared
    let path := module ++ n
    let contract := !clauses.isEmpty
    -- A parameter is named if it has a type after `:`, or is a `Bool`
    -- written `x?` (`lang::function_params`).
    let named (p : Array Ident × Option (Array Ident)) :=
      p.2.isSome || (p.1.size == 1 && (declaredIdent p.1[0]!).1.name.endsWith "?")
    unless Fren.Core.functionParamsAccepted body.isSome contract params.size (params.filter named).size do
      let bad := (params.find? (named · != (body.isSome || contract))).map (·.1[0]!.span) |>.getD name.span
      err bad (Fren.Core.functionParamsMsg path body.isSome contract)
    -- The parameters, declared like a comp's inputs.
    let paramVars : M (Array CVar) := do
      let mut vars : Array CVar := #[]
      -- Distinct names (`lang::distinct_names`).
      -- By the names they declare, without the `!` of shadowing.
      let declared := params.map fun p => Name.mkSimple (declaredIdent p.1[0]!).1.name
      if let some k := (Fren.Core.repeatsAt declared)[0]? then
        err params[k]!.1[0]!.span (Fren.Core.dupParamMsg declared[k]!)
      for (p, ty?) in params do
        let x ← declare p[0]!
        let xn := Name.mkSimple x.name
        lintName .variable xn x.span
        let ptype ← varPTy ty? x
        let fact? ← factOf ptype (quote xn.toString)
        vars := vars.push { name := xn, role := .input, isPub := true, ty := ptype.ty, span := x.span, ptype, fact? }
      return vars
    match body with
    | none =>
      if !contract then
        let pps ← params.mapM (elabPTy ·.1)
        let ps := pps.map (·.ty)
        lintFnBools n name.span ps
        -- As for a variable, with the result type (`lang::bool_naming`),
        -- after the parameters, in source order.
        let rp ← varPTy result name
        noteResultFact path rp
        modify fun s => { s with funs := s.funs.push (path, ps, rp.ty), funPTys := s.funPTys.insert path (pps, rp) }
      else
        let vars ← paramVars
        lintFnBools n name.span (vars.map (·.ty))
        let rp ← varPTy result name
        noteResultFact path rp
        modify fun s => { s with funs := s.funs.push (path, vars.map (·.ty), rp.ty)
                                 funPTys := s.funPTys.insert path (vars.map (·.ptype), rp) }
        discard takeTables
        modify fun s => { s with outsideCore := false, natApps := #[] }
        let (vars, props, sites) ← elabContract path n false vars clauses rp.ty name.span
        noteBody n name.span vars (props, sites) path
        lintDeclared .function n name.span
        lintLines .function n name.span last
    | some body =>
      let vars ← paramVars
      lintFnBools n name.span (vars.map (·.ty))
      let rp ← varPTy result name
      let r := rp.ty
      modify fun s => { s with funPTys := s.funPTys.insert path (vars.map (·.ptype), rp) }
      discard takeTables
      discard takeIndexes
      modify fun s => { s with outsideCore := false, natApps := #[] }
      let cx : ExprCtx := { vars, place := .prop, selfFn := some n, expected? := if r == .nat then some .nat else none }
      let (smt, t) ← elabExpr cx body
      noteObligation cx .body body.span rp smt
      let bodyTables ← takeTables
      let bodyObligations ← takeIndexes
      liftMsg body.span (Fren.Core.checkType r t (some s!"note: `{n}` returns `{r.show}`"))
      lintBools body
      -- A parameter that only the contract mentions is used too.
      let mentioned := (mentions body ++ clauses.flatMap fun (_, _, e) => mentions e).map (·.getRoot)
      for (x, v) in Fren.Core.unmentioned (vars.map fun v => (v.name, v)) mentioned do
        lint .unusedVariables v.span (Fren.Core.unusedParamMsg x)
      modify fun s => { s with defs := s.defs.push (path, vars.map fun v => (v.name, v.ty), r, smt) }
      let (_, props, sites) ← if contract then elabContract path n true vars clauses r name.span else pure (vars, #[], #[])
      modify fun s => { s with tables := bodyTables }
      noteBody n name.span vars (props, sites) path bodyObligations
      lintDeclared .function n name.span
      lintLines .function n name.span last
    unless isPub do
      modify fun s =>
        let r : Fren.Core.ItemRecord :=
          { what := .function, path, level := s.levels.get .deadCode, singleCall? := body.map fun _ => s.levels.get .singleCallFn }
        { s with items := s.items.push (r, name.span) }
    modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
  | .comp isPub name members close spans openStop => do
    -- Its `use`s end with it, even when it has an error.
    modify fun s => { s with inCompBody := false }
    try elabComp isPub name members spans openStop
    catch e =>
      modify (fun s => { s.keepLints e.state with scope := s.module })
      -- Its declaration and line lints, after an error in its members.
      if e.state.inCompBody then
        lintDeclared .component (Name.mkSimple name.name) name.span
        lintLines .component (Name.mkSimple name.name) name.span close
      throw { e with state := ← get }
    lintDeclared .component (Name.mkSimple name.name) name.span
    lintLines .component (Name.mkSimple name.name) name.span close
  | .const isPub name ty value => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkConstName n)
    let module := (← get).module
    liftMsg name.span ((← get).table.checkFresh module n)
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
    modify fun s => { s with outsideCore := false, natApps := #[] }
    let cx : ExprCtx := { vars := #[], place := .prop, expected? := some t }
    let (smt, t') ← elabExpr cx value
    noteObligation cx .constant value.span pt smt
    noteBody n name.span #[] (obligations := ← takeIndexes)
    let applies := (← get).applied.extract before
    unless Fren.Core.constantAccepted abstract applies.isEmpty.not do
      err applies[0]! (Fren.Core.unknownConstantMsg abstract)
    liftMsg value.span (Fren.Core.checkType t t' (some s!"note: `{n}` has type `{t.show}`"))
    lintBools value
    let path := module ++ n
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .constant, path, level := s.levels.get .deadCode }, name.span) }
    let int? ← if t == .int || t == .nat then intConstValue? { vars := #[], place := .prop } value else pure none
    modify fun s => { s with
      table := s.table.addItem { kind := .constItem, path, isPub, owner := s.module }
      consts := s.consts.insert path (smt, t)
      constInts := match int? with | some v => s.constInts.insert path v | none => s.constInts }
  | .global name binders body => elabGlobal name binders body
  | .refine name c a bs => elabRefine name c a bs
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
    | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.wrongKindMsg "a component or a global expectation" r)
  | .lintSetting stx opt value valueSpan removal body? => do
    if opt.name == "fren.evidence" then
      -- Like a lint setting: for the item after `in`, or the rest of the file.
      let prev := (← get).evidence?
      -- An invalid value is reported here, once, and does not stop the
      -- items it would set (`Reqs/Check#checking-by-testing`).
      if (Fren.Core.evidenceTested? value).isNone then
        modify fun s => { s with diags := s.diags.push { file := s.file, span := valueSpan, msg := Fren.Core.invalidEvidenceMsg value } }
      modify fun s => { s with evidence? := some (value, valueSpan) }
      if let some body := body? then
        elabItem body
        modify fun s => { s with evidence? := prev }
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

/-- Records the reports of `manual_nat` in the file that no instance or
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
      ++ Fren.Core.singleCallReports s.items s.usedItems)
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
    (trailingCommas : Array (Span × String)) (found : Array (Lint × Span × Msg)) (fixing : Array Lint := #[]) :
    StateM State Unit := do
  modify fun s => { s with file, src, fixing, module := .anonymous, scope := .anonymous, levels := s.cliLevels, useRecords := #[], evidence? := none,
                           used := #[], expectations := #[], lintReports := #[], useLocs := #[],
                           expectationRemovals := #[], items := #[], usedItems := #[], lintFixes := #[],
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

/-- Whether the queries of `c` may quantify over a collection's elements,
as the constraints of its variables' types, the facts of the applications
it makes, and the obligations it asks may: they then set `fmf-bound`
(`Fren.Core.boundedOptions`). It is read from the types, not the formulas,
as the Lean front end's `bounded` is. -/
def State.bounded (s : State) (c : CComp) : Bool :=
  c.vars.any (fun v => v.fact?.isSome && (v.ptype.cons s.shapeOf).any (·.quantifies))
    || c.indexes.any (fun (_, _, _, _, t) => t.any (·.2))
    || c.insts.any (·.bounded)
    || c.natApps.any fun app => ((quotedSymbols (peelLets app))[0]?).any fun h => s.quantifiedFns.contains (quote h)

/-- A declaration of the prelude: its SMT-LIB text, and the names of the
quoted symbols that it declares. -/
structure PreludeDecl where
  text : String
  syms : Array String
  deriving Inhabited, BEq

/-- `(declare-sort ...)` for every abstract type, `(declare-datatype ...)`
for every enum and record, in order, since each may contain those before
it, `(declare-fun ...)` for every uninterpreted function, and
`(define-fun ...)` for every defined function, in order, since each may
apply those before it, and then for every clause of a contract. -/
def State.prelude (s : State) : Array PreludeDecl :=
  let unquote (sym : String) : String := ((sym.drop 1).dropEnd 1).toString
  let sorts := s.sorts.map fun p => { text := s!"(declare-sort {itemSym p} 0)\n", syms := #[unquote (itemSym p)] }
  -- A datatype declares its constructors and selectors too.
  let enums := s.datatypes.map fun d => { text := d.text, syms := d.syms }
  let funs := s.funs.map fun (p, ps, r) =>
    { text := s!"(declare-fun {itemSym p} ({" ".intercalate (ps.toList.map (·.sort))}) {r.sort})\n", syms := #[unquote (itemSym p)] }
  let defs := s.defs.map fun (p, ps, r, body) =>
    let ps := " ".intercalate (ps.toList.map fun (x, t) => s!"({quote x.toString} {t.sort})")
    { text := s!"(define-fun {itemSym p} ({ps}) {r.sort} {body})\n", syms := #[unquote (itemSym p)] }
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
  s.funs.foldl (init := {}) fun m (p, _, r) => m.insert (itemSym p) (r == .nat, (s.contracts.find? p).getD {})

/-- The whole prelude, as one script. -/
def State.preludeText (s : State) : String := String.join (s.prelude.toList.map (·.text))

end FrenCli
