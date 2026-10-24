-- keep-sorted start
import FrenCli.Parse
import FrenCore.Evidence
import FrenCore.Lint
import FrenCore.Names
import FrenCore.Refine
import FrenCore.Regex
import FrenCore.Trace
import FrenCore.Ty
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
  | .int => "Int"
  | .string => "String"
  | .set t => s!"(Set (Tuple {t.sort}))"
  | .rel a b => s!"(Set (Tuple {a.sort} {b.sort}))"
  | .seq t => s!"(Seq {t.sort})"
  | .enum p | .record p => quote (showPath p)
  | .abstract p => itemSym p

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

/-- `(declare-datatype ...)` -/
def DataDecl.decl (d : DataDecl) : String :=
  let ctors := " ".intercalate <| d.ctors.toList.map fun (c, fs) =>
    let sels := String.join <| (fs.toList.zipIdx).map fun ((_, t), k) => s!" ({d.selSym c k} {t.sort})"
    s!"({d.ctorSym c}{sels})"
  s!"(declare-datatype {quote (showPath d.path)} ({ctors}))\n"

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
  indexes : Array (Name × Fren.Core.IndexPlace × Span × String) := #[]
  /-- It, or one of its instances, applies a relational operator. -/
  relational : Bool := false
  /-- It, or one of its instances, uses `card`. -/
  counts : Bool := false
  /-- The checks that are tested rather than asked of the solver
  (`Reqs/Check#checking-by-testing`). -/
  tested : Fren.Core.Tested := {}
  deriving Inhabited

def conj (fs : Array String) : String :=
  if fs.isEmpty then "true" else if fs.size == 1 then fs[0]! else s!"(and {" ".intercalate fs.toList})"

/-- Everything a comp says about its variables: assumptions, requirements
and instances. -/
def CComp.meaning (c : CComp) : String :=
  conj <| c.defs.map (fun (d, e) => s!"(= {quote d.toString} {e})")
    ++ (c.props.filter (·.kind != .expect)).map (·.smt)
    ++ c.insts.map fun i => conj #[i.bindings, i.behaviour]

/-- `w.x` as a `Name`. -/
def identName (s : String) : Name := (s.splitOn ".").foldl Name.mkStr .anonymous

/-- Applies `f` to the name of each quoted symbol of `smt`. A `|` in a
string literal, where `""` is a `"`, does not quote. -/
def mapQuoted (f : String → String) (smt : String) : String := Id.run do
  let cs := smt.toList.toArray
  let mut out := ""
  let mut i := 0
  while h : i < cs.size do
    let c := cs[i]
    if c == '"' then
      let mut j := i + 1
      while j < cs.size && !(cs[j]! == '"' && cs[j + 1]? != some '"') do
        j := if cs[j]! == '"' then j + 2 else j + 1
      out := out ++ String.ofList (cs.extract i (j + 1)).toList
      i := j + 1
    else if c == '|' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '|' do j := j + 1
      out := out ++ quote (f (String.ofList (cs.extract (i + 1) j).toList))
      i := j + 1
    else
      out := out.push c
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
  /-- The abstract types, in order. -/
  sorts : Array Name := #[]
  /-- Each uninterpreted function's parameter and result types, in order. -/
  funs : Array (Name × Array Ty × Ty) := #[]
  /-- Each defined function's parameters and result type, and its body over
  the parameters, in order. -/
  defs : Array (Name × Array (Name × Ty) × Ty × String) := #[]
  /-- The enumerations and records, in order. -/
  datatypes : Array DataDecl := #[]
  /-- The spans of the function applications elaborated so far
  (`lang::constant`). -/
  applied : Array Span := #[]
  /-- Global expectations, each a `CComp` whose path is its module, with an
  instance per binder and the expectation as its only constraint. -/
  globals : Array CComp := #[]
  /-- Refinements, each a `CComp` whose path is the refinement's
  (`Reqs/Lang/Refinement`). -/
  refinements : Array CComp := #[]
  diags : Array Diag := #[]
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
  /-- The edits of `fren fix`, by file. -/
  edits : Array (Nat × Fren.Core.Range × String) := #[]
  /-- The current file's private enumerations and constants, and the items
  that paths in it resolve to (`dead_code`). -/
  items : Array (Fren.Core.ItemRecord × Span) := #[]
  usedItems : Array Name := #[]
  /-- The simpler forms that `nonminimal_bool` suggests, at its messages. -/
  boolFixes : Array (Span × String) := #[]
  /-- The edits that fix the lints whose message suggests one replacement of
  the text it is at: the collection, membership and index lints. -/
  lintFixes : Array (Lint × Span × String) := #[]
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
  indexes : Array (Span × String) := #[]

/-- Why an item failed, and the items that its paths used before it did
(`dead_code`), which outlive it. -/
structure Failure where
  diag : Diag
  usedItems : Array Name

abbrev M := StateT State (Except Failure)

def err (span : Span) (msg : Msg) : M α := do
  let s ← get
  throw { diag := { file := s.file, span, msg }, usedItems := s.usedItems }

def internal (span : Span) (what : String) : M α := err span (Msg.internal what)

def State.dataOf? (s : State) (p : Name) : Option DataDecl := s.datatypes.find? (·.path == p)

def State.unbounded (s : State) : Ty → Bool
  | .string | .set _ | .rel .. | .seq _ => true
  | .enum p | .record p => (s.dataOf? p).any (·.unbounded)
  | _ => false

/-- Whether a type has infinitely many values (`Reqs/Lang/Decidability#outputs`):
an abstract type may, so it counts. -/
partial def State.infinite (s : State) : Ty → Bool
  | .bool => false
  | .int | .string | .abstract _ | .seq _ => true
  | .set t => s.infinite t
  | .rel a b => s.infinite a || s.infinite b
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
  | _ => none

def segNames (segs : Array Ident) : Array Name := segs.map (Name.mkSimple ·.name)

def liftResolve (segs : Array Ident) : Except Fren.Core.Error α → M α
  | .ok a => pure a
  | .error e => err (segs[e.seg]?.map (·.span) |>.getD default) e.msg

def liftMsg (span : Span) : Except Msg α → M α
  | .ok a => pure a
  | .error msg => err span msg

/-- Resolves a path in an expression or type in the current module,
recording the import it resolves through, if any (`unused_imports`), and
the item it uses (`dead_code`). -/
def resolve (segs : Array Ident) (extra : Array Name := #[]) : M Resolved := do
  let st ← get
  let r ← liftResolve segs (st.table.resolvePath st.scope (segNames segs) extra)
  if let some u := st.table.importVia st.scope (segNames segs) then
    modify fun s => { s with used := s.used.push u }
  modify fun s => { s with usedItems := s.usedItems.push r.usedItem }
  return r

/-- Reports a declared name that is not in its case (`lint::naming_case`),
at the level in effect. -/
def lintName (what : Named) (n : Name) (span : Span) : M Unit := do
  if let some (lint, msg) := Fren.Core.namingMsg? what n then
    modify fun s => { s with lintReports := s.lintReports.push { lint, level := s.levels.get lint, ref := span, msg } }

/-- Reports a lint at the level in effect. -/
def lint (lint : Lint) (span : Span) (msg : Msg) : M Unit :=
  modify fun s => { s with lintReports := s.lintReports.push { lint, level := s.levels.get lint, ref := span, msg } }

/-- Reports a lint whose message's first fix replaces its text, which
`fren fix` applies. -/
def lintFix (l : Lint) (span : Span) (msg : Msg) : M Unit := do
  let some f := msg.fixes[0]? | lint l span msg
  modify fun s => { s with lintFixes := s.lintFixes.push (l, span, f.replacement) }
  lint l span { msg with notes := msg.notes.push Fren.Core.fixHelp }

/-! ## Expressions -/

/-- A binder of a `match` pattern in scope. -/
structure CBinder where
  name : Name
  /-- Its value: the selector applied to the scrutinee. -/
  smt : String
  ty : Ty
  /-- Its scrutinee, and the number of binders in scope there: mentioning
  it counts as mentioning what the scrutinee mentions. -/
  scrutinee : Expr
  outer : Nat

structure ExprCtx where
  vars : Array CVar
  /-- The comp's instances, in order. -/
  insts : Array Name := #[]
  place : Place
  /-- For a binding, the index of its instance. -/
  current : Nat := 0
  /-- The binders in scope, innermost last. -/
  binders : Array CBinder := #[]
  /-- In a defined function's body, the function's name. -/
  selfFn : Option Name := none
  /-- `++` here is in the decidable core: the receiver of a method, or a
  side of `=` or `!=` whose other side is a constant. -/
  concatOk : Bool := false
  /-- The type this expression must have, which gives `{}` its type. -/
  expected? : Option Ty := none
  /-- The conditions under which this expression is evaluated, read from
  left to right: an index's guard (`Reqs/Lang/Expressions#sequences`). -/
  guards : Array String := #[]
  /-- Whether to record the indexes of this expression for the definedness
  check, and report its lints: not when it is elaborated a second time, as
  a trigger. -/
  noteIndexes : Bool := true
  /-- This expression is an operand of `or`, whose chain `membership_chain`
  looks at from its top. -/
  inOr : Bool := false

/-- The binder named `n` in scope, if any. -/
def ExprCtx.binder? (cx : ExprCtx) (n : Name) : Option CBinder := cx.binders.reverse.find? (·.name == n)

/-- The context of a binder's scrutinee. -/
def ExprCtx.at (cx : ExprCtx) (b : CBinder) : ExprCtx := { cx with binders := cx.binders.extract 0 b.outer }

/-- Names that shadow items: variables of one segment, and binders. -/
def ExprCtx.shadowing (cx : ExprCtx) : Array Name :=
  (cx.vars.filter (·.name.isAtomic) |>.map (·.name)) ++ cx.binders.map (·.name)


/-- Whether `segs`, applied, builds a variant rather than applying a
function. -/
def isVariant (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  return st.table.resolvePath st.scope (segNames segs) cx.shadowing matches .ok (.variant ..)

/-- Whether `segs`, applied, applies a defined function. -/
def isDefined (cx : ExprCtx) (segs : Array Ident) : M Bool := do
  let st ← get
  let .ok (.item { kind := .fnItem, path, .. }) := st.table.resolvePath st.scope (segNames segs) cx.shadowing
    | return false
  return st.defs.any (·.1 == path)

/-- How many variables `e` mentions, counted with repetition, where `bs`
are the binders of `e` around the subexpression, each with the count of
its scrutinee. A name that is not a variable, such as a constant, is not
counted (`lang::linear_product`). -/
partial def varsMentioned (cx : ExprCtx) (bs : Array (Name × Nat) := #[]) : Expr → M Nat
  | .path _ segs => do
    if segs.size != 1 then return 0
    let n := identName segs[0]!.name
    if let some (_, k) := bs.reverse.find? (·.1 == n.getRoot) then return k
    if let some b := cx.binder? n.getRoot then return ← varsMentioned (cx.at b) #[] b.scrutinee
    -- A defined output counts as its definition (acyclic, so this ends).
    if let some d := (cx.vars.find? (·.name == n.getRoot)).bind (·.defn?) then
      return ← varsMentioned { cx with binders := #[] } #[] d
    return if cx.vars.any (·.name.isPrefixOf n) then 1 else 0
  | .when _ _ c d | .bin _ _ c d => return (← varsMentioned cx bs c) + (← varsMentioned cx bs d)
  | .not _ a | .neg _ a | .field _ a _ => varsMentioned cx bs a
  -- A method has a fixed meaning, like a variant.
  | .method _ r _ args => (#[r] ++ args).foldlM (fun n a => return n + (← varsMentioned cx bs a)) 0
  | .set _ es => es.foldlM (fun n a => return n + (← varsMentioned cx bs a)) 0
  | .pair _ a b | .index _ a b => return (← varsMentioned cx bs a) + (← varsMentioned cx bs b)
  | .seq _ es => es.foldlM (fun n a => return n + (← varsMentioned cx bs a)) 0
  | .ite _ c a b => return (← varsMentioned cx bs c) + (← varsMentioned cx bs a) + (← varsMentioned cx bs b)
  | .app _ segs args => do
    let n ← args.foldlM (fun n a => return n + (← varsMentioned cx bs a)) 0
    -- A function's value is unknown, like a variable's; a variant's is
    -- not, and a defined function's is linear in its arguments'.
    return if (← isVariant cx segs) || (← isDefined cx segs) then n else n + 1
  | .record _ _ fs => fs.foldlM (init := 0) fun n (f, e?) => return n + (← varsMentioned cx bs (e?.getD (.path f.span #[f])))
  | .match _ s arms => do
    let k ← varsMentioned cx bs s
    arms.foldlM (init := k) fun n (p, body) => do
      let new := match p with
        | .variant _ _ (some xs) => xs.map fun x => (Name.mkSimple x.name, k)
        | _ => #[]
      return n + (← varsMentioned cx (bs ++ new) body)
  | _ => return 0

/-- The names of the variables that `e` mentions: its paths of one
segment, and for `p.x`, `p` too. -/
partial def mentions : Expr → Array Name
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
  | .seq _ es => es.foldl (· ++ mentions ·) #[]
  | .ite _ c a b => mentions c ++ mentions a ++ mentions b
  | .bin _ _ a b => mentions a ++ mentions b
  | .app _ _ args => args.foldl (· ++ mentions ·) #[]
  | .record _ _ fs => fs.foldl (init := #[]) fun acc (f, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple f.name]
  | .match _ s arms => arms.foldl (· ++ mentions ·.2) (mentions s)
  | _ => #[]

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
      if ← mentionsInfiniteOutput (cx.at b) b.scrutinee then return true
      continue
    let some v := cx.vars.find? (·.name == n) | continue
    if (defDeps cx.vars v).any fun u => u.role == .output && st.infinite u.ty then return true
  return false

/-- Whether `e` is a constant: it mentions no variable, binder or
uninterpreted function. -/
def isConstant (cx : ExprCtx) (e : Expr) : M Bool := return (← varsMentioned cx #[] e) == 0

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
  | .seq _ es => es.anyM (hasConcat cx)
  | .ite _ c a b => return (← hasConcat cx c) || (← hasConcat cx a) || (← hasConcat cx b)
  | .record _ _ fs => fs.anyM fun (_, e?) => match e? with | some e => hasConcat cx e | none => pure false
  | .match _ s arms => return (← hasConcat cx s) || (← arms.anyM (hasConcat cx ·.2))
  | _ => return false

/-- Reports `undecidable` if construct `c`, with `operands` other than of
`=` and `!=`, is outside the decidable core (`lang::in_core`). -/
def checkCore (cx : ExprCtx) (span : Span) (c : Fren.Core.Construct) (constantArgs comparable : Bool)
    (operands : Array Expr) (ground : Bool := false) (infiniteElems : Bool := true) (finiteRange : Bool := true)
    (literalOperand : Bool := false) : M Unit := do
  let infinite ← operands.anyM (mentionsInfiniteOutput cx)
  unless Fren.Core.inCore c constantArgs comparable infinite ground infiniteElems finiteRange literalOperand do
    modify fun s => { s with outsideCore := true }
    lint .undecidable span (Fren.Core.undecidableMsg c infinite)

/-- `e` as `nonminimal_bool` sees it. -/
partial def Expr.boolNode : Expr → Fren.Core.BNode Span
  | .when s _ c d => .mk .when (toRange s) s #[c.boolNode, d.boolNode]
  | .ite s c a b => .mk .ite (toRange s) s #[c.boolNode, a.boolNode, b.boolNode]
  | .bin s op a b => .mk (.bin op) (toRange s) s #[a.boolNode, b.boolNode]
  | .not s a => .mk .not (toRange s) s #[a.boolNode]
  | .neg s a => .mk .neg (toRange s) s #[a.boolNode]
  | .bool s b => .mk (.lit b) (toRange s) s #[]
  | .num s _ | .path s _ | .app s .. | .record s .. | .field s .. | .match s .. | .str s .. | .method s .. | .set s .. | .pair s .. | .seq s .. | .index s .. =>
    .mk .atom (toRange s) s #[]
where toRange (sp : Span) : Fren.Core.Range := { start := sp.start, stop := sp.stop }

/-- Reports the `Bool` expressions in `e` that have a simpler form
(`nonminimal_bool`). -/
def lintBools (e : Expr) : M Unit := do
  for r in Fren.Core.simplerBools (← get).src e.boolNode do
    lint .nonminimalBool r.ref (Fren.Core.nonminimalMsg r true)
    modify fun s => { s with boolFixes := s.boolFixes.push (r.ref, r.replacement) }

/-- `e` has type `found` where `expected` was required. -/
def mismatch (e : Expr) (expected found : Ty) (why : Option String := none) : M α :=
  let hint := match expected, found with
    | .bool, .int => #["help: compare it to make a `Bool`, e.g. `x > 0` or `x != 0`"]
    | .int, .bool => #["help: to turn a `Bool` into an `Int`, write `if b? then 1 else 0`"]
    | .bool, .enum p | .int, .enum p => #[s!"help: compare it with a variant to make a `Bool`, e.g. `x = {p.getString!}::Variant`"]
    | _, _ => #[]
  err e.span {
    code? := some "F0304", headline := s!"type mismatch: expected `{expected.show}`, found `{found.show}`"
    label? := some s!"expected `{expected.show}`, found `{found.show}`"
    notes := why.toArray ++ hint }

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
      unless ta == tp do
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
  unless t == .string do err span (Fren.Core.noMethodsMsg m t.show)
  let some method := (Fren.Core.Method.ofName? m).filter (·.accepts true false)
    | err span (Fren.Core.unknownMethodMsg m t.show)
  unless args.size == method.arity do err span (Fren.Core.arityMsg (Name.mkSimple m) method.arity args.size)
  let tyOf : Fren.Core.MethodTy → Ty | .bool => .bool | .int => .int | _ => .string
  for (_, ta, sp) in args, p in method.params, k in [0:args.size] do
    let tp := tyOf p
    unless ta == tp do
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
  if t matches .string | .set _ | .rel .. | .seq _ then return ← callMethod span smt t f.toString #[]
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

/-- The indexes recorded since the last call, which it forgets. -/
def takeIndexes : M (Array (Span × String)) := do
  let xs := (← get).indexes
  modify fun s => { s with indexes := #[] }
  return xs

/-- The source text at `span`. -/
def srcAt (span : Span) : M String := return String.ofList ((← get).src.extract span.start span.stop).toList

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

/-- The disjuncts of a chain of `or`. -/
partial def orDisjuncts : Expr → Array Expr
  | .bin _ "or" l r => orDisjuncts l ++ orDisjuncts r
  | d => #[d]

/-- The sequences that `e` indexes, as their text. -/
partial def indexedIn : Expr → M (Array String)
  | .index _ q i => return #[← srcAt q.span] ++ (← indexedIn q) ++ (← indexedIn i)
  | .bin _ _ a b | .when _ _ a b | .pair _ a b => return (← indexedIn a) ++ (← indexedIn b)
  | .not _ a | .neg _ a | .field _ a _ => indexedIn a
  | .ite _ c a b => return (← indexedIn c) ++ (← indexedIn a) ++ (← indexedIn b)
  | .method _ r _ args => return (← indexedIn r) ++ (← args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[])
  | .app _ _ args | .set _ args | .seq _ args => args.foldlM (fun acc a => return acc ++ (← indexedIn a)) #[]
  | _ => return #[]

/-- Whether `e` bounds the sequence written `q`: it mentions `q.len`, or
compares `q` with `[]` (`lint::index_after_use`). -/
def boundsSeq (e : Expr) (q : String) : M Bool := do
  let t := (← srcAt e.span).replace " " ""
  return (t.splitOn s!"{q}.len").length > 1 || (t.splitOn s!"{q}!=[]").length > 1 || (t.splitOn s!"{q}=[]").length > 1

/-- Records the index `q[i]` at `span`, whose sequence and position are the
SMT-LIB `q` and `i`, for the definedness check (`check::definedness`). -/
def noteIndex (cx : ExprCtx) (span : Span) (q i : String) : M Unit := do
  unless cx.noteIndexes do return
  let bounds := s!"(and (<= 0 {i}) (< {i} (seq.len {q})))"
  let goal := if cx.guards.isEmpty then bounds else s!"(=> (and true {" ".intercalate cx.guards.toList}) {bounds})"
  modify fun s => { s with indexes := s.indexes.push (span, goal) }

/-- Records a `card`, of the receiver `recv` of type `t`: in a comp that
applies a relational operator, it is outside the decidable core
(`Reqs/Lang/Decidability#relations`). -/
def checkRelationalCard (cx : ExprCtx) (span : Span) (t : Ty) (m : String) (recv : Expr) : M Unit := do
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
  let st ← get
  modify fun s => { s with relationalUsed := true }
  checkCore cx span .relational true true operands (← operands.allM (isConstant cx)) (finiteRange := tys.all (!st.infinite ·))

partial def elabExpr (cx : ExprCtx) (e : Expr) : M (String × Ty) := do
  let concatOk := cx.concatOk
  let expected? := cx.expected?
  let cx := { cx with concatOk := false, expected? := none, inOr := false }
  let isEmptySet : Expr → Bool | .set _ #[] => true | _ => false
  -- Two operands of the same type: `{}` takes the other's.
  let pair (cxa cxb : ExprCtx) (a b : Expr) : M ((String × Ty) × (String × Ty)) := do
    if isEmptySet a && !isEmptySet b then
      let rb ← elabExpr cxb b
      return (← elabExpr { cxa with expected? := some rb.2 } a, rb)
    let ra ← elabExpr cxa a
    return (ra, ← elabExpr { cxb with expected? := some ra.2 } b)
  let expect (e : Expr) (t : Ty) (why : Option String := none) : M String := do
    let (s, t') ← elabExpr cx e
    unless t == t' do mismatch e t t' why
    return s
  let opNote (op : String) (t : Ty) := some s!"note: the operands of `{op}` are `{t.show}`s"
  -- `length_zero` and `card_zero` on `a op b` (`lint::length_zero`).
  let lintLength (op : String) (a b : Expr) : M Unit := do
    unless cx.noteIndexes do return
    let (.num _ d, some (recv, card), some c) := (b, lengthOf? a, Fren.Core.Comparison.ofOp? op) | return
    let (fires, empty) := Fren.Core.lengthZero c d.toNat!
    unless fires do return
    -- Only its type: what elaborating it reports is reported where it is.
    let saved ← get
    let t? ← tryCatch (some <$> (·.2) <$> elabExpr { cx with noteIndexes := false, concatOk := true } recv)
      fun _ => pure none
    set saved
    let some t := t? | return
    let isSet := t matches .set _ | .rel ..
    unless card == isSet do return
    let emptyText := match t with | .string => "\"\"" | .seq _ => "[]" | _ => "{}"
    lintFix (if card then .cardZero else .lengthZero) e.span
      (Fren.Core.lengthZeroMsg card (← srcAt recv.span) emptyText empty)
  match e with
  | .when _ neg c d =>
    let kw := if neg then "unless" else "when"
    let c ← expect c .bool (some s!"note: the condition of `{kw}` is a `Bool`")
    let g := if neg then s!"(not {c})" else c
    let (d, td) ← elabExpr { cx with guards := cx.guards.push g } d
    unless td == .bool do mismatch e .bool td (some s!"note: the body of `{kw}` is a `Bool`")
    return (if neg then s!"(=> (not {c}) {d})" else s!"(=> {c} {d})", .bool)
  | .not _ a => return (s!"(not {← expect a .bool (opNote "not" .bool)})", .bool)
  | .ite span c a b =>
    let c ← expect c .bool (some "note: the condition of `if` is a `Bool`")
    let ((x, tx), (y, ty)) ← pair { cx with expected?, guards := cx.guards.push c }
      { cx with expected?, guards := cx.guards.push s!"(not {c})" } a b
    unless tx == ty do
      err span { code? := some "F0306", headline := s!"the branches of `if` have different types: `{tx.show}` and `{ty.show}`"
                 label? := some "branches of different types"
                 notes := #["note: `if c then a else b` is `a` or `b`, so both must have the same type"] }
    return (s!"(ite {c} {x} {y})", tx)
  | .neg _ a => return (s!"(- {← expect a .int (opNote "-" .int)})", .int)
  | .num _ d => return (d, .int)
  | .set span elems =>
    if elems.isEmpty then
      let some t := expected? | err span Fren.Core.emptySetTypeMsg
      unless t matches .set _ | .rel .. do err span Fren.Core.emptySetTypeMsg
      return (s!"(as set.empty {t.sort})", t)
    -- A member, as the fields of its tuple, and the type of the literal
    -- it makes: a pair makes a relation.
    let member (e : Expr) (expected? : Option Ty) : M (String × Ty) := do
      if let .pair _ a b := e then
        let (ea?, eb?) := match expected? with | some (.rel x y) => (some x, some y) | _ => (none, none)
        let (x, tx) ← elabExpr { cx with expected? := ea? } a
        let (y, ty) ← elabExpr { cx with expected? := eb? } b
        return (s!"{x} {y}", .rel tx ty)
      let (x, t) ← elabExpr { cx with expected? := expected?.bind fun | .set t => some t | _ => none } e
      return (x, .set t)
    let (x0, t0) ← member elems[0]! expected?
    let mut xs := #[x0]
    for e in elems.extract 1 do
      let (x, t) ← member e (some t0)
      unless t == t0 do
        let (mt, mt0) := match t, t0 with | .set u, .set u0 => (u.show, u0.show) | _, _ => (t.show, t0.show)
        err e.span { code? := some "F0326", headline := s!"the members of a set have different types: `{mt0}` and `{mt}`"
                     label? := some s!"a `{mt}`"
                     notes := #[s!"note: the first member is a `{mt0}`, so the literal is a `{t0.show}`"] }
      xs := xs.push x
    checkCore cx span .setAlgebra true true elems
    let ts := xs.map (s!"(tuple {·})")
    let smt := if ts.size == 1 then s!"(set.singleton {ts[0]!})"
      else s!"(set.insert {" ".intercalate (ts.pop.toList)} (set.singleton {ts.back!}))"
    return (smt, t0)
  | .pair span .. => err span Fren.Core.pairPlaceMsg
  | .seq span elems =>
    if elems.isEmpty then
      let some t := expected? | err span Fren.Core.emptySeqTypeMsg
      unless t matches .seq _ do err span Fren.Core.emptySeqTypeMsg
      return (s!"(as seq.empty {t.sort})", t)
    let elemExpected := expected?.bind fun | .seq t => some t | _ => none
    let (x0, t0) ← elabExpr { cx with expected? := elemExpected } elems[0]!
    let mut xs := #[x0]
    for e in elems.extract 1 do
      let (x, t) ← elabExpr { cx with expected? := some t0 } e
      unless t == t0 do
        err e.span { code? := some "F0326", headline := s!"the elements of a sequence have different types: `{t0.show}` and `{t.show}`"
                     label? := some s!"a `{t.show}`"
                     notes := #[s!"note: the first element is a `{t0.show}`, so the literal is a `{(Ty.seq t0).show}`"] }
      xs := xs.push x
    checkCore cx span .seqArray true true elems
    let us := xs.map (s!"(seq.unit {·})")
    return (if us.size == 1 then us[0]! else s!"(seq.++ {" ".intercalate us.toList})", .seq t0)
  | .index span q i =>
    let (x, tq) ← elabExpr cx q
    let .seq elem := tq | err q.span (Fren.Core.notIndexableMsg tq.show)
    let ix ← expect i .int (some "note: an index is an `Int`")
    checkCore cx span .seqArray true true #[q, i]
    noteIndex cx span x ix
    return (s!"(seq.nth {x} {ix})", elem)
  | .str span v =>
    liftMsg span (Fren.Core.checkStringChars v)
    modify fun s => { s with usesStrings := true }
    return (Fren.Core.smtStringLit v, .string)
  | .method span recv m args =>
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
        | _, _ => none
      let (x, ta) ← elabExpr { cx with expected? } a
      as := as.push (x, ta, a.span)
    if let (.string, some method) := (t, Fren.Core.Method.ofName? m.name) then
      let constantArgs ← args.allM (isConstant cx)
      checkCore cx span method.construct constantArgs true (#[recv] ++ args) (constantArgs && (← isConstant cx recv))
    if let (.seq _, some method) := (t, Fren.Core.Method.ofName? m.name) then
      checkCore cx span method.seqConstruct true true (#[recv] ++ args)
        ((← args.allM (isConstant cx)) && (← isConstant cx recv)) (literalOperand := args.any (· matches .seq ..))
    if let some tys := relRange? t m.name then checkRelational cx span tys (#[recv] ++ args)
    checkRelationalCard cx span t m.name recv
    callMethod m.span r t m.name as
  | .bool _ b => return (toString b, .bool)
  | .bin span op a b =>
    match op with
    | "iff" | "or" | "and" =>
      let smt := if op == "iff" then "=" else op
      -- `membership_chain`, at the top of a chain of `or` (`lint::membership_chain`).
      if op == "or" && !cx.inOr && cx.noteIndexes then
        let ds := orDisjuncts e
        let eqs := ds.filterMap fun | .bin _ "=" l r => some (l, r) | _ => none
        let lefts ← eqs.mapM fun (l, _) => srcAt l.span
        let same := eqs.size == ds.size && lefts.all (· == lefts[0]!)
        if Fren.Core.membershipChainFires ds.size same then
          lintFix .membershipChain span (Fren.Core.membershipChainMsg lefts[0]! (← eqs.mapM fun (_, r) => srcAt r.span))
      -- `index_after_use` (`lint::index_after_use`).
      if op == "and" && cx.noteIndexes then
        let qs ← indexedIn a
        if ← qs.anyM fun q => return (← boundsSeq b q) && !(← boundsSeq a q) then
          lintFix .indexAfterUse span (Fren.Core.indexAfterUseMsg (← srcAt a.span) (← srcAt b.span))
      let (x, tx) ← elabExpr { cx with inOr := op == "or" } a
      unless tx == .bool do mismatch a .bool tx (opNote op .bool)
      -- `b` is evaluated when `a` does not decide the result.
      let guards := match op with | "and" => cx.guards.push x | "or" => cx.guards.push s!"(not {x})" | _ => cx.guards
      let (y, ty) ← elabExpr { cx with guards, inOr := op == "or" } b
      unless ty == .bool do mismatch b .bool ty (opNote op .bool)
      return (s!"({smt} {x} {y})", .bool)
    | "=" | "!=" =>
      lintLength op a b
      -- `++` is in the core against a constant.
      let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
      let ((x, tx), (y, ty)) ← pair { cx with concatOk := cb } { cx with concatOk := ca } a b
      unless tx == ty do
        let hint := match tx, ty with
          | .enum p, .int | .int, .enum p => #[s!"note: enums are not numbers", s!"help: compare with a variant, e.g. `{p.getString!}::Variant`"]
          | .bool, .int | .int, .bool => #["note: `Bool`s are not numbers: `true` and `false` are `Bool`s"]
          | _, _ => #[]
        err span { code? := some "F0305", headline := s!"cannot compare `{tx.show}` with `{ty.show}`"
                   label? := some s!"`{tx.show}` and `{ty.show}`"
                   notes := #[s!"note: both sides of `{op}` must have the same type"] ++ hint }
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
      let (x, tx) ← elabExpr cx a
      unless tx == .string do
        unless tx == .int do mismatch a .int tx (opNote op .int)
        return (s!"({op} {x} {← expect b .int (opNote op .int)})", .bool)
      let y ← expect b .string (opNote op .string)
      let (ca, cb) := (← isConstant cx a, ← isConstant cx b)
      checkCore cx span .stringCompare true (ca || cb) #[a, b] (ca && cb)
      -- SMT-LIB has only `str.<` and `str.<=`.
      return (match op with
        | "<" => s!"(str.< {x} {y})"
        | "<=" => s!"(str.<= {x} {y})"
        | ">" => s!"(str.< {y} {x})"
        | _ => s!"(str.<= {y} {x})", .bool)
    | "in" =>
      if let .pair _ pa pb := a then
        let (x, tx) ← elabExpr cx pa
        let (y, ty) ← elabExpr cx pb
        let (r, tr) ← elabExpr { cx with expected? := some (.rel tx ty) } b
        unless tr == .rel tx ty do
          err span (Fren.Core.membershipTypeMsg (Ty.rel tx ty).show tr.show true)
        checkCore cx span .setAlgebra true true #[pa, pb, b]
        return (s!"(set.member (tuple {x} {y}) {r})", .bool)
      let (x, tx) ← elabExpr cx a
      let (y, ty) ← elabExpr { cx with expected? := some (.set tx) } b
      if let (.set _ #[m], true) := (b, cx.noteIndexes) then
        unless m matches .pair .. do lintFix .singletonMembership span (Fren.Core.singletonMembershipMsg (← srcAt a.span) (← srcAt m.span))
      if ty == .seq tx then
        checkCore cx span .seqWord true true #[a, b] (← isConstant cx e) (literalOperand := b matches .seq ..)
        return (s!"(seq.contains {y} (seq.unit {x}))", .bool)
      unless ty == .set tx do
        err span { code? := some "F0325", headline := s!"`in` needs a `Set({tx.show})` on its right, found `{ty.show}`"
                   label? := some s!"`{tx.show}` and `{ty.show}`"
                   notes := #["note: `x in s` is membership: `s` is a set of values of `x`'s type"] }
      checkCore cx span .setAlgebra true true #[a, b]
      return (s!"(set.member (tuple {x}) {y})", .bool)
    | "union" | "inter" | "minus" | "subset" =>
      let ((x, tx), (y, ty)) ← pair { cx with expected? } { cx with expected? } a b
      unless tx matches .set _ | .rel .. do mismatch a (.set tx) tx (some s!"note: the operands of `{op}` are sets or relations")
      unless tx == ty do mismatch b tx ty (some s!"note: both operands of `{op}` are `{tx.show}`s")
      checkCore cx span .setAlgebra true true #[a, b]
      let smt := match op with
        | "union" => "set.union" | "inter" => "set.inter" | "minus" => "set.minus" | _ => "set.subset"
      return (s!"({smt} {x} {y})", if op == "subset" then .bool else tx)
    | "join" =>
      let (x, tx) ← elabExpr cx a
      let .rel ta tb := tx | err a.span (Fren.Core.joinTypeMsg tx.show none)
      let (y, ty) ← elabExpr { cx with expected? := some (.rel tb tb) } b
      let .rel tb' tc := ty | err b.span (Fren.Core.joinTypeMsg ty.show none)
      unless tb == tb' do err span (Fren.Core.joinTypeMsg tx.show (some ty.show))
      checkRelational cx span #[tb] #[a, b]
      return (s!"(rel.join {x} {y})", .rel ta tc)
    | "++" =>
      -- `[] ++ q` takes its type from `q`.
      let expected? ← if a matches .seq _ #[] && !(b matches .seq _ #[]) then
          pure (some (← elabExpr { cx with noteIndexes := false } b).2)
        else pure expected?
      let (x, tx) ← elabExpr { cx with expected?, concatOk := true } a
      if let .seq _ := tx then
        let (y, ty) ← elabExpr { cx with expected? := some tx } b
        unless ty == tx do mismatch b tx ty (some s!"note: the operands of `++` are `{tx.show}`s")
        checkCore cx span .seqWord true true #[a, b] (← isConstant cx e)
        return (s!"(seq.++ {x} {y})", tx)
      -- Where the core allows it, only its operands' outputs matter.
      if concatOk then checkCore cx span .stringAtom true true #[a, b]
      else checkCore cx span .stringSearch true true #[a, b] (← isConstant cx e)
      unless tx == .string do mismatch a .string tx (opNote op .string)
      let (y, ty) ← elabExpr { cx with concatOk := true } b
      unless ty == .string do mismatch b .string ty (opNote op .string)
      return (s!"(str.++ {x} {y})", .string)
    | "*" =>
      unless Fren.Core.productAccepted (← varsMentioned cx #[] a) (← varsMentioned cx #[] b) do err span Fren.Core.nonlinearMsg
      return (s!"(* {← expect a .int (opNote op .int)} {← expect b .int (opNote op .int)})", .int)
    | _ => return (s!"({op} {← expect a .int (opNote op .int)} {← expect b .int (opNote op .int)})", .int)
  | .path _ segs =>
    if segs.size == 1 then
      let n := identName segs[0]!.name
      let span := segs[0]!.span
      -- A binder or variable, then any fields read from it.
      let base? ← if let some b := cx.binder? n.getRoot then do
          discard (elabExpr (cx.at b) b.scrutinee)
          pure (some ((b.smt, b.ty), n.components.drop 1))
        else
          let ks := (List.range n.components.length).reverse.map (· + 1)
          match ks.findSome? fun k => (cx.vars.find? (·.name == (n.components.take k).foldl (· ++ ·) .anonymous)).map (·, k) with
          | some (v, k) =>
            -- A defined output mentions what its definition does.
            for u in defDeps cx.vars v do
              let earlier := (cx.insts.findIdx? (· == u.name.getRoot)).any (· < cx.current)
              match Fren.Core.checkMention cx.place u.role earlier u.name with
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
          readField fspan smt t f
      if !n.isAtomic then
        err span (Fren.Core.dottedNameMsg n cx.insts (cx.vars.filter (·.role != .instHidden) |>.map (·.name)))
    let st ← get
    match ← resolve segs cx.shadowing with
    | .variant en idx =>
      let d := st.dataOf? en.path
      let n := (d.bind (·.ctors[idx]?)).map (·.2.size) |>.getD 0
      if n > 0 then err e.span (Fren.Core.unappliedVariantMsg (en.path ++ en.variants[idx]!) n)
      return (ctorSym en.path en.variants[idx]!, .enum en.path)
    | .item { kind := .constItem, path, .. } =>
      let some c := st.consts.find? path | internal e.span s!"unknown constant `{path}`"
      return c
    | .item { kind := .fnItem, path, .. } => err e.span (Fren.Core.unappliedMsg path)
    | r => err e.span (Fren.Core.notAValueMsg r)
  | .app span segs args =>
    let fnSpan := segs[0]!.span.to segs.back!.span
    if segs.size == 1 && (cx.vars.any (·.name == identName segs[0]!.name) || (cx.binder? (identName segs[0]!.name)).isSome) then
      err fnSpan (Fren.Core.varNotAFunctionMsg (identName segs[0]!.name))
    if segs.size == 1 && cx.selfFn == some (Name.mkSimple segs[0]!.name) then
      err fnSpan (Fren.Core.recursiveMsg ((← get).module ++ Name.mkSimple segs[0]!.name))
    -- A variable shadows a function, as it does any other item.
    let path ← match ← resolve segs cx.shadowing with
      | .item { kind := .fnItem, path, .. } => pure path
      | .variant en idx =>
        -- A variant with a payload, built from its values.
        let v := en.variants[idx]!
        let some d := (← get).dataOf? en.path | internal fnSpan s!"unknown enum `{en.path}`"
        let tys := d.ctors[idx]!.2.map (·.2)
        if tys.isEmpty then err span (Fren.Core.noPayloadMsg (en.path ++ v))
        unless args.size == tys.size do err span (Fren.Core.arityMsg (en.path ++ v) tys.size args.size "value")
        let mut smts := #[]
        for a in args, t in tys, k in [0:args.size] do
          let (x, ta) ← elabExpr { cx with expected? := some t } a
          unless ta == t do
            mismatch a t ta (some s!"note: value {k + 1} of the payload of `{showPath (en.path ++ v)}` has type `{t.show}`")
          smts := smts.push x
        return (s!"({ctorSym en.path v} {" ".intercalate smts.toList})", .enum en.path)
      | r => err fnSpan (Fren.Core.notAFunctionMsg r)
    if let some (_, params, result, _) := (← get).defs.find? (·.1 == path) then
      -- Its arguments may mention anything (`lang::argument`).
      unless args.size == params.size do err span (Fren.Core.arityMsg path params.size args.size)
      let mut smts := #[]
      for a in args, (_, t) in params, k in [0:args.size] do
        let (x, ta) ← elabExpr { cx with expected? := some t } a
        unless ta == t do
          mismatch a t ta (some s!"note: argument {k + 1} of `{showPath path}` has type `{t.show}`")
        smts := smts.push x
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
    for a in args, t in params, k in [0:args.size] do
      let (x, ta) ← elabExpr { acx with expected? := some t } a
      unless ta == t do
        mismatch a t ta (some s!"note: argument {k + 1} of `{showPath path}` has type `{t.show}`")
      smts := smts.push x
    return (s!"({itemSym path} {" ".intercalate smts.toList})", result)
  | .field span a f =>
    let (x, t) ← elabExpr { cx with concatOk := true } a
    if t == .string then checkCore cx span .stringAtom true true #[a]
    if let some tys := relRange? t f.name then checkRelational cx span tys #[a]
    checkRelationalCard cx span t f.name a
    if let (.seq _, some m) := (t, Fren.Core.Method.ofName? f.name) then
      checkCore cx span m.seqConstruct true true #[a] (← isConstant cx a)
    readField f.span x t (Name.mkSimple f.name)
  | .record span tySegs fields =>
    let tySpan := tySegs[0]!.span.to tySegs.back!.span
    let path ← match ← resolve tySegs cx.shadowing with
      | .item { kind := .recordItem, path, .. } => pure path
      | r => err tySpan (Fren.Core.wrongKindMsg "a record" r)
    let some d := (← get).dataOf? path | internal tySpan s!"unknown record `{path}`"
    let fs := d.ctors[0]!.2
    match Fren.Core.checkFieldInits path (fs.map (·.1)) (fields.map (Name.mkSimple ·.1.name)) with
    | .ok () => pure ()
    | .error (some i, msg) => err fields[i]!.1.span msg
    | .error (none, msg) => err span msg
    let mut smts := #[]
    for (f, t) in fs do
      let some (fi, e?) := fields.find? (Name.mkSimple ·.1.name == f) | internal span s!"no field `{f}`"
      let e := e?.getD (.path fi.span #[fi])
      let (x, te) ← elabExpr { cx with expected? := some t } e
      unless te == t do mismatch e t te (some s!"note: `{f}` of `{showPath path}` has type `{t.show}`")
      smts := smts.push x
    return (s!"({recordCtorSym path} {" ".intercalate smts.toList})", .record path)
  | .match span scrutinee arms =>
    let (s, ts) ← elabExpr cx scrutinee
    let .enum ep := ts | err scrutinee.span (Fren.Core.scrutineeMsg ts.show)
    let some d := (← get).dataOf? ep | internal scrutinee.span s!"unknown enum `{ep}`"
    -- Each arm's variants, one for each alternative, or `none` for `_`.
    let mut pats : Array (Option (Array Nat)) := #[]
    for (p, _) in arms do
      if p matches .wild _ then pats := pats.push none; continue
      let mut idxs := #[]
      for alt in p.alts do
        let .variant pspan segs binders? := alt | internal alt.span "nested or-pattern"
        match ← resolve segs cx.shadowing with
        | .variant en idx =>
          if en.path != ep then err pspan (Fren.Core.notAVariantOfMsg ep s!"a variant of `{showPath en.path}`")
          let v := ep ++ en.variants[idx]!
          let n := d.ctors[idx]!.2.size
          match binders? with
          | none => if n > 0 then err pspan (Fren.Core.unappliedVariantMsg v n)
          | some bs =>
            if n == 0 then err pspan (Fren.Core.noPayloadMsg v)
            unless bs.size == n do err pspan (Fren.Core.arityMsg v n bs.size "binder")
            if p.alts.size > 1 then
              if let some b := bs.find? (·.name != "_") then err b.span (Fren.Core.orBinderMsg (Name.mkSimple b.name))
          idxs := idxs.push idx
        | r => err pspan (Fren.Core.notAVariantOfMsg ep r.describe)
      pats := pats.push (some idxs)
    match Fren.Core.checkArms ep (d.ctors.map (·.1)) (pats.map (·.map (·.map (d.ctors[·]!.1)))) with
    | .ok () => pure ()
    | .error (some (i, some j), msg) => err arms[i]!.1.alts[j]!.span msg
    | .error (some (i, none), msg) => err arms[i]!.1.span msg
    | .error (none, msg) => err span msg
    -- An arm's test: that one of its alternatives matches.
    let tests := pats.map (·.map fun idxs =>
      if idxs.size == 1 then d.tester idxs[0]! s else s!"(or {" ".intercalate (idxs.map (d.tester · s)).toList})")
    let mut bodies : Array String := #[]
    let mut ty? : Option Ty := none
    -- An arm is evaluated when its pattern matches and no earlier one does.
    let mut earlier : Array String := #[]
    for (p, body) in arms, pat in pats, test in tests do
      let armGuards := cx.guards ++ earlier.map (s!"(not {·})") ++ test.toArray
      earlier := earlier ++ test.toArray
      let mut new : Array CBinder := #[]
      if let (.variant _ _ (some bs), some #[idx]) := (p, pat) then
        let (c, fs) := d.ctors[idx]!
        for b in bs, f in fs, k in [0:bs.size] do
          let t := f.2
          if b.name == "_" then continue
          let bn := Name.mkSimple b.name
          if new.any (·.name == bn) then err b.span (Fren.Core.dupPatternBinderMsg bn)
          liftMsg b.span (Fren.Core.checkVarName bn (some (t == .bool)))
          lintName .binder bn b.span
          new := new.push { name := bn, smt := s!"({d.selSym c k} {s})", ty := t, scrutinee, outer := cx.binders.size }
      let (x, t) ← elabExpr { cx with binders := cx.binders ++ new, guards := armGuards } body
      if let some t0 := ty? then
        unless t == t0 do err body.span (Fren.Core.armTypesMsg t0.show t.show)
      ty? := some t
      bodies := bodies.push x
    -- The first arm that matches; the last arm matches whatever is left.
    let mut out := bodies.back!
    for i in (List.range (bodies.size - 1)).reverse do
      if let some t := tests[i]! then
        out := s!"(ite {t} {bodies[i]!} {out})"
    return (out, ty?.get!)

/-- The conditions of a top-level `when`/`unless` chain, and their span. -/
partial def trigger? (cx : ExprCtx) : Expr → M (Option (String × Span))
  | .when span neg c d => do
    let (cs, _) ← elabExpr { cx with noteIndexes := false } c
    let cs := if neg then s!"(not {cs})" else cs
    let here : Span := { start := span.start, stop := c.span.stop }
    match ← trigger? cx d with
    | none => return some (cs, here)
    | some (t, s) => return some (s!"(and {cs} {t})", here.to s)
  | _ => return none

/-! ## Items -/

partial def elabTy (segs : Array Ident) : M Ty := do
  if segs.size == 1 && segs[0]!.name == "Bool" then return Ty.bool
  if segs.size == 1 && segs[0]!.name == "Int" then return .int
  if segs.size == 1 && segs[0]!.name == "String" then
    modify fun s => { s with usesStrings := true }
    return .string
  if segs[0]!.name == Parser.setSeg then
    modify fun s => { s with usesSets := true }
    return .set (← elabTy (segs.extract 1))
  if segs[0]!.name == Parser.seqSeg then
    modify fun s => { s with usesSeqs := true }
    return .seq (← elabTy (segs.extract 1))
  if segs[0]!.name == Parser.relSeg then
    modify fun s => { s with usesSets := true }
    let (a, b) := Parser.splitRel (segs.extract 1)
    return .rel (← elabTy a) (← elabTy b)
  match ← resolve segs with
  | .item { kind := .enumItem, path, .. } => return .enum path
  | .item { kind := .recordItem, path, .. } => return .record path
  | .item { kind := .typeItem, path, .. } => return .abstract path
  | r => err (segs[0]!.span.to segs.back!.span) (Fren.Core.notATypeMsg r)

/-- Whether the type `segs` is the item `name`, and whether it has it as a
set's element type (`lang::field_type`). -/
def ownIn (segs : Array Ident) (name : Ident) : Bool × Bool :=
  let core := segs.filter fun s => s.name != Parser.setSeg && s.name != Parser.relSeg && s.name != Parser.relSep
    && s.name != Parser.seqSeg
  let isName := core.size == 1 && core[0]!.name == name.name
  (isName && core.size == segs.size, core.size < segs.size && core.any (·.name == name.name))

def varTy (ty? : Option (Array Ident)) (name : Ident) : M Ty := do
  let t ← ty?.mapM elabTy
  liftMsg name.span (Fren.Core.checkVarName (Name.mkSimple name.name) (t.map (· == .bool)))
  return t.getD .bool

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
  liftMsg x.span (Fren.Core.checkItemName "instance" w)
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
    { name := w ++ v.name, role, isPub := role == .instOutput, ty := v.ty, span := x.span }
  return ({ name := x, comp := c, bindings := bs }, vars)

/-- Elaborates the bindings of an instance. -/
def elabInst (cx : ExprCtx) (pi : PendingInst) : M CInst := do
  let w := Name.mkSimple pi.name.name
  let mut eqs := #[]
  let c := pi.comp
  for (b, e?) in pi.bindings do
    let e := e?.getD (.path b.span #[b])
    let some v := cx.vars.find? (·.name == w ++ Name.mkSimple b.name)
      | internal b.span s!"no variable for `{b.name}`"
    let (smt, t) ← elabExpr { cx with expected? := some v.ty } e
    unless t == v.ty do mismatch e v.ty t (some s!"note: `{b.name}` of `{showPath c.path}` has type `{v.ty.show}`")
    lintBools e
    eqs := eqs.push s!"(= {quote v.name.toString} {smt})"
  return {
    name := w, comp := c.path, span := pi.name.span, bindings := conj eqs
    behaviour := rename w c.vars c.meaning
    assumes := c.props.filter (·.kind == .assume) |>.map fun a => (a.name, rename w c.vars a.smt) }

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

/-- Whether the `set_option fren.evidence` in effect sets checks to testing
(`F0214` if its value is invalid). -/
def evidenceInEffect : M Bool := do
  match (← get).evidence? with
  | none => return false
  | some (value, sp) =>
    let some b := Fren.Core.evidenceTested? value | err sp (Fren.Core.invalidEvidenceMsg value)
    return b

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
    | .prop .expect x _, _ => expects := expects.push (Name.mkSimple x.name, set?)
    | .inst x _ _, _ => insts := insts.push (Name.mkSimple x.name, set?)
    | .var false _ true x _ _, _ => dets := dets.push (Name.mkSimple x.name, set?)
    | _, some (_, span) =>
      let what := match m with
        | .prop .assume .. => "an assumption" | .prop .req .. => "a requirement"
        | .var true .. => "an input" | .var .. => "an output that is not `det`" | _ => "a `use`"
      err span (Fren.Core.misplacedEvidenceMsg what)
    | _, none => pure ()
    match m with
    | .prop .assume x _ | .prop .req x _ => constraints := constraints.push (Name.mkSimple x.name)
    | .var false _ _ x _ (some _) => constraints := constraints.push (Name.mkSimple x.name)
    | _ => pure ()
    pending := none
  if let some (_, span) := pending then err span (Fren.Core.misplacedEvidenceMsg "the end of the component")
  return Fren.Core.Tested.ofSettings all constraints expects insts dets

def elabComp (isPub : Bool) (name : Ident) (members : Array Member) : M Unit := do
  let n := Name.mkSimple name.name
  modify fun s => { s with outsideCore := false, relationalUsed := false, countSpans := #[] }
  liftMsg name.span (Fren.Core.checkItemName "component" n)
  let st ← get
  liftMsg name.span (st.table.checkFresh st.module n)
  lintName .component n name.span
  declareMemberUses (st.module ++ n) members
  let mut seen : Array Name := #[]
  let mut vars := #[]
  for m in members do
    let .var isIn isPub' isDet x ty? defn? := m | continue
    let xn := Name.mkSimple x.name
    if seen.contains xn then err x.span (Fren.Core.dupMemberMsg xn)
    seen := seen.push xn
    lintName .variable xn x.span
    if let some c := (← get).table.shadowedConstant? (← get).scope xn then
      lint .shadowedConstants x.span (Fren.Core.shadowedMsg xn c)
    let role := if isIn then Role.input else .output
    let ty ← varTy ty? x
    unless Fren.Core.variableTypeAccepted (role == .output) ((← get).unbounded ty) defn?.isSome do
      err x.span (Fren.Core.unboundedOutputMsg xn ty.show)
    vars := vars.push { name := xn, role, isPub := isPub', isDet, ty, span := x.span, defn? }
  for v in vars do
    if let some cycle := defCycle? vars v.name then err v.span (Fren.Core.cyclicDefinitionMsg cycle)
  -- Instances, whose variables follow the comp's own
  let mut pending := #[]
  for m in members do
    let .inst x p bs := m | continue
    let xn := Name.mkSimple x.name
    if seen.contains xn then err x.span (Fren.Core.dupMemberMsg xn)
    seen := seen.push xn
    lintName .instance xn x.span
    let (pi, ivars) ← resolveInst x p bs
    pending := pending.push pi
    vars := vars ++ ivars
  let instNames := pending.map (Name.mkSimple ·.name.name)
  let mut insts := #[]
  let mut indexes : Array (Name × Fren.Core.IndexPlace × Span × String) := #[]
  discard takeIndexes
  for pi in pending, k in [0:pending.size] do
    insts := insts.push (← elabInst { vars, insts := instNames, place := .binding, current := k } pi)
    indexes := indexes ++ (← takeIndexes).map fun (sp, g) => (Name.mkSimple pi.name.name, .binding k, sp, g)
  -- Definitions, each after those it mentions.
  let mut defs : Array (Name × String) := #[]
  let mut todo := vars.filter (·.defn?.isSome)
  while !todo.isEmpty do
    let some v := todo.find? fun v => (mentions v.defn?.get!).all fun n => !todo.any (·.name == n)
      | internal name.span "cyclic definitions"
    todo := todo.filter (·.name != v.name)
    let e := v.defn?.get!
    -- A definition assigns once and acyclically, so `++` is in the core in it.
    let (smt, t) ← elabExpr { vars, insts := instNames, place := .prop, expected? := some v.ty, concatOk := true } e
    unless t == v.ty do mismatch e v.ty t (some s!"note: `{v.name}` has type `{v.ty.show}`, so its definition must too")
    lintBools e
    defs := defs.push (v.name, smt)
    indexes := indexes ++ (← takeIndexes).map fun (sp, g) => (v.name, .prop, sp, g)
  let mut props := #[]
  for m in members do
    let .prop kind x e := m | continue
    let xn := Name.mkSimple x.name
    if seen.contains xn then err x.span (Fren.Core.dupMemberMsg xn)
    seen := seen.push xn
    if x.name.endsWith "?" then err x.span (Fren.Core.propNameMsg xn)
    lintName .constraint xn x.span
    let cx : ExprCtx := { vars, insts := instNames, place := if kind == .assume then .assume else .prop }
    let (smt, t) ← elabExpr cx e
    unless t == .bool do mismatch e .bool t (some "note: a constraint is a `Bool`")
    lintBools e
    let trig ← trigger? cx e
    props := props.push { kind, name := xn, span := x.span, smt, trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) }
    let place := if kind == .assume then .assume else .prop
    indexes := indexes ++ (← takeIndexes).map fun (sp, g) => (xn, place, sp, g)
  let mentioned := members.foldl (init := #[]) fun acc m => match m with
    | .prop _ _ e | .var _ _ _ _ _ (some e) => acc ++ mentions e
    | .inst _ _ bs => bs.foldl (init := acc) fun acc (b, e?) => acc ++ (e?.map mentions).getD #[Name.mkSimple b.name]
    | _ => acc
  -- A public definition says what the output is, so it is used.
  let candidates := vars.filter fun v => v.role == .input || (v.role == .output && !(v.isPub && v.defn?.isSome))
  for (x, v) in Fren.Core.unmentioned (candidates.map fun v => (v.name, v)) mentioned do
    lint .unusedVariables v.span (Fren.Core.unusedVariableMsg x false (v.role == .output))
  -- `constant_output` and `definable_output` (`lint::output_lints`).
  let lcx : ExprCtx := { vars, insts := instNames, place := .prop }
  let reqs := members.filterMap fun | .prop .req x e => some (Name.mkSimple x.name, e) | _ => none
  for v in vars.filter (fun v => v.role == .output && v.name.isAtomic) do
    let isX : Expr → Bool | .path _ #[seg] => Name.mkSimple seg.name == v.name | _ => false
    let about := reqs.filter fun (_, e) => (mentions e).contains v.name
    -- The only requirement that mentions it, as `x = e` or `x? iff e`, with `e` other variables'.
    let equation := match about with
      | #[(_, .bin _ op l r)] => (op == "=" || op == "iff") &&
          ((isX l && !(mentions r).contains v.name) || (isX r && !(mentions l).contains v.name))
      | _ => false
    let nVars ← match v.defn? with | some d => varsMentioned lcx #[] d | none => pure 1
    let (constant, definable) := Fren.Core.outputLints v.defn?.isSome nVars about.size equation
    if constant then lint .constantOutput v.span (Fren.Core.constantOutputMsg v.name)
    if definable then lint .definableOutput v.span (Fren.Core.definableOutputMsg v.name about[0]!.1)
  let path := st.module ++ n
  let tested ← testedOf (← evidenceInEffect) members
  let (relational, counts) ← checkCounts
  modify fun s => { s with
    table := s.table.addItem { kind := .compItem, path, isPub, owner := s.module }
    scope := s.module
    comps := s.comps.push { path, file := s.file, span := name.span, vars, props, insts, defs, indexes, decidable := !s.outsideCore
                            relational, counts, tested } }

/-- Elaborates `refine name: concrete refines abstract` into the comp that
checks it (`Reqs/Lang/Refinement`): `concrete`'s inputs, `abstract`'s
assumptions, an instance of `concrete` named as it is, `abstract`'s
instances, and `abstract`'s requirements and definitions as expectations,
over the instance's outputs. -/
def elabRefine (name : Ident) (concreteSegs abstractSegs : Array Ident) : M Unit := do
  let n := Name.mkSimple name.name
  liftMsg name.span (Fren.Core.checkItemName "refinement" n)
  let st ← get
  liftMsg name.span (st.table.checkFresh st.module n)
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
  -- The interface (`refinement::interface`).
  for v in a.vars.filter (·.name.isAtomic) do
    let cv? := c.vars.find? (·.name == v.name)
    let input := v.role == Role.input
    let ok := Fren.Core.interfaceAccepted input cv?.isSome (cv?.any (·.role == Role.input))
      (cv?.any (·.isPub)) (cv?.any (·.ty == v.ty))
    unless ok do
      let why := match cv? with
        | none => s!"it has no variable `{v.name}`"
        | some cv => if cv.ty != v.ty then s!"its `{v.name}` has type `{cv.ty.show}`, not `{v.ty.show}`"
          else if input then s!"its `{v.name}` is not an input"
          else if cv.role == Role.input then s!"its `{v.name}` is an input, not an output"
          else s!"its output `{v.name}` is not public"
      err aSpan (Fren.Core.interfaceMsg c.path a.path v.name why)
  -- The instance of `concrete`, named as it is.
  let w := Name.mkSimple (c.path.getString!)
  if a.insts.any (·.name == w) then err aSpan (Fren.Core.dupMemberMsg w)
  let outs := a.vars.filter fun v => v.name.isAtomic && v.role == .output
  let ren (smt : String) := rename w outs smt
  let inputs := c.vars.filter fun v => v.name.isAtomic && v.role == .input
  let vars := inputs ++ c.vars.map (fun v =>
      let role := Role.ofInst v.role v.isPub
      { v with name := w ++ v.name, role, isPub := role != .instHidden, isDet := false, defn? := none })
    ++ a.vars.filter (!·.name.isAtomic)
  let instC : CInst := { name := w, comp := c.path, span := name.span
                         bindings := conj (inputs.map fun v => s!"(= {quote (w ++ v.name).toString} {quote v.name.toString})")
                         behaviour := rename w c.vars c.meaning
                         assumes := (c.props.filter (·.kind == .assume)).map fun p => (p.name, rename w c.vars p.smt) }
  -- `a`'s instances are hypotheses: their assumptions are `a`'s own
  -- obligations, checked in `a` (`Reqs/Lang/Refinement#the-obligation`).
  let insts := #[instC] ++ a.insts.map fun i =>
    { i with bindings := ren i.bindings, behaviour := ren i.behaviour, assumes := #[] }
  -- Reported at the refinement (`Reqs/Lang/Refinement#the-obligation`).
  let props := (a.props.filter (·.kind == .assume)).map ({ · with span := name.span, triggerSpan? := none })
    ++ (a.props.filter (·.kind == .req)).map (fun p =>
      { p with kind := .expect, smt := ren p.smt, trigger? := p.trigger?.map ren, span := name.span, triggerSpan? := none })
    ++ a.defs.map fun (d, e) =>
      { kind := .expect, name := d, span := name.span
        smt := s!"(= {quote (w ++ d).toString} {ren e})", trigger? := none, triggerSpan? := none : CProp }
  let indexes := a.indexes.map fun (x, place, sp, goal) =>
    (x, (match place with | .binding k => .binding (k + 1) | p => p), sp, ren goal)
  let tested := Fren.Core.Tested.ofSettings (← evidenceInEffect)
    ((a.props.filter (·.kind == .assume)).map (·.name)) (props.filter (·.kind == .expect) |>.map (·.name, none))
    #[(w, none)] #[]
  modify fun s => { s with
    table := s.table.addItem { kind := .expectItem, path := st.module ++ n, isPub := false, owner := s.module }
    refinements := s.refinements.push { path := st.module ++ n, file := s.file, span := name.span, vars, props, insts
                                        indexes, decidable := c.decidable && a.decidable
                                        relational := c.relational || a.relational, counts := c.counts || a.counts, tested } }

/-- Elaborates a global expectation (`Reqs/Lang/Global`). -/
def elabGlobal (name : Ident) (binders : Array (Array Ident × Array Ident)) (body : Expr) : M Unit := do
  let n := Name.mkSimple name.name
  let all ← evidenceInEffect
  if name.name.endsWith "?" then err name.span (Fren.Core.propNameMsg n)
  modify fun s => { s with outsideCore := false, relationalUsed := false, countSpans := #[] }
  let st ← get
  liftMsg name.span (st.table.checkFresh st.module n)
  lintName .global n name.span
  let mut vars : Array CVar := #[]
  let mut insts : Array CInst := #[]
  for (xs, p) in binders do
    let path ← match ← resolve p with
      | .item { kind := .compItem, path, .. } => pure path
      | r => err (p[0]!.span.to p.back!.span) (Fren.Core.notACompMsg r)
    let some c := st.comps.find? (·.path == path) | internal p[0]!.span s!"unknown comp `{path}`"
    unless c.decidable do
      modify fun s => { s with outsideCore := true }
      lint .undecidable (p[0]!.span.to p.back!.span) (Fren.Core.undecidableInstMsg path)
    noteCounts c (p[0]!.span.to p.back!.span)
    for x in xs do
      let w := Name.mkSimple x.name
      liftMsg x.span (Fren.Core.checkItemName "instance" w)
      if insts.any (·.name == w) then err x.span (Fren.Core.dupBinderMsg w)
      lintName .instance w x.span
      -- Like an instance's, but its inputs are shown in counterexamples.
      vars := vars ++ c.vars.map fun v =>
        let role := Role.ofInst v.role v.isPub
        { name := w ++ v.name, role, isPub := role != .instHidden, ty := v.ty, span := x.span }
      -- Its assumptions are hypotheses, not obligations.
      insts := insts.push { name := w, comp := path, span := x.span, bindings := "true",
                            behaviour := rename w c.vars c.meaning, assumes := #[] }
  let cx : ExprCtx := { vars, insts := insts.map (·.name), place := .prop }
  discard takeIndexes
  let (smt, t) ← elabExpr cx body
  let indexes := (← takeIndexes).map fun (sp, g) => (n, Fren.Core.IndexPlace.prop, sp, g)
  unless t == .bool do mismatch body .bool t (some "note: an expectation is a `Bool`")
  lintBools body
  let binders := insts.map fun i => (i.name, i.span)
  for (w, sp) in Fren.Core.unmentioned binders ((mentions body).map (·.getRoot)) do
    lint .unusedVariables sp (Fren.Core.unusedVariableMsg w true false)
  let trig ← trigger? cx body
  let prop : CProp := { kind := .expect, name := n, span := name.span, smt
                        trigger? := trig.map (·.1), triggerSpan? := trig.map (·.2) }
  discard checkCounts
  modify fun s => { s with
    table := s.table.addItem { kind := .expectItem, path := st.module ++ n, isPub := false, owner := s.module }
    globals := s.globals.push { path := s.module, file := s.file, span := name.span, vars, props := #[prop], insts, indexes
                                decidable := !s.outsideCore
                                tested := Fren.Core.Tested.ofSettings all #[] #[(n, none)] #[] #[] } }

partial def elabItem : Item → M Unit
  | .mod isPub segs => do
    let (path, new) ← liftResolve segs ((← get).table.declareModule (segNames segs) isPub)
    for i in new do
      if let some seg := segs[i.path.components.length - 1]? then lintName .module (Name.mkSimple seg.name) seg.span
    modify fun s => { s with table := new.foldl (·.addItem ·) s.table, module := path, scope := path }
  | .use span segs glob => do
    let removal := { span with start := (← get).settingStart?.getD span.start }
    declareUse segs glob { item := span, removal, path := segs[0]!.span.to segs.back!.span }
  | .useGroup span pre paths => do
    let removal := { span with start := (← get).settingStart?.getD span.start }
    for p in paths do
      declareUse (pre ++ p) false
        { item := span, removal, path := p[0]!.span.to p.back!.span, pre? := some (pre[0]!.span.to pre.back!.span) }
  | .enum isPub name variants => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "enum" n)
    let st ← get
    liftMsg name.span (st.table.checkFresh st.module n)
    lintName .enumeration n name.span
    let path := st.module ++ n
    let mut vs := #[]
    let mut ctors := #[]
    let mut nRecursive := 0
    let mut unbounded := false
    for (v, payload?) in variants do
      let vn := Name.mkSimple v.name
      liftMsg v.span (Fren.Core.checkItemName "variant" vn)
      if vs.contains vn then err v.span (Fren.Core.dupVariantMsg vn)
      lintName .variant vn v.span
      vs := vs.push vn
      let mut fs := #[]
      let mut recursive := false
      for segs in payload?.getD #[], k in [0:(payload?.getD #[]).size] do
        -- The enum's own name, which is not declared yet (`lang::field_type`).
        let (own, ownInSet) := ownIn segs name
        let tspan := segs[0]!.span.to segs.back!.span
        if ownInSet then err tspan (Fren.Core.recursiveSetMsg path)
        let t ← if own then pure (Ty.enum path) else elabTy segs
        let abstract := t.abstractWithin?
        unless Fren.Core.fieldTypeAccepted abstract.isSome own ownInSet true do
          err tspan (Fren.Core.abstractFieldMsg (abstract.getD path) true (!(t matches .abstract _)))
        recursive := recursive || own
        unbounded := unbounded || own || (← get).unbounded t
        fs := fs.push (Name.mkSimple (toString k), t)
      if recursive then nRecursive := nRecursive + 1
      ctors := ctors.push (vn, fs)
    unless Fren.Core.wellFounded variants.size nRecursive do err name.span (Fren.Core.illFoundedMsg n)
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .enumeration, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := (s.table.addItem { kind := .enumItem, path, isPub, owner := s.module }).addEnum { path, variants := vs }
      datatypes := s.datatypes.push { path, isRecord := false, ctors, unbounded } }
  | .record isPub name fields => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "record" n)
    let st ← get
    liftMsg name.span (st.table.checkFresh st.module n)
    lintName .record n name.span
    let path := st.module ++ n
    let mut fs : Array (Name × Ty) := #[]
    for (f, ty?) in fields do
      let fn := Name.mkSimple f.name
      if fs.any (·.1 == fn) then err f.span (Fren.Core.dupFieldMsg fn)
      lintName .field fn f.span
      if let some segs := ty? then
        let (own, ownInSet) := ownIn segs name
        if own then err (segs[0]!.span.to segs.back!.span) (Fren.Core.recursiveRecordMsg n)
        if ownInSet then err (segs[0]!.span.to segs.back!.span) (Fren.Core.recursiveSetMsg path)
      let t ← varTy ty? f
      if let some p := t.abstractWithin? then
        err ((ty?.map fun segs => segs[0]!.span.to segs.back!.span).getD f.span)
          (Fren.Core.abstractFieldMsg p false (!(t matches .abstract _)))
      fs := fs.push (fn, t)
    let unbounded := fs.any fun (_, t) => st.unbounded t
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .record, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .recordItem, path, isPub, owner := s.module }
      datatypes := s.datatypes.push { path, isRecord := true, ctors := #[(`«{}», fs)], unbounded } }
  | .abstractType isPub name => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkItemName "abstract type" n)
    let st ← get
    liftMsg name.span (st.table.checkFresh st.module n)
    lintName .abstractType n name.span
    let path := st.module ++ n
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .abstractType, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .typeItem, path, isPub, owner := s.module }
      sorts := s.sorts.push path }
  | .function isPub name params result body => do
    let n := Name.mkSimple name.name
    let st ← get
    liftMsg name.span (st.table.checkFresh st.module n)
    lintName .function n name.span
    let path := st.module ++ n
    -- A parameter is named if it has a type after `:`, or is a `Bool`
    -- written `x?` (`lang::function_params`).
    let named (p : Array Ident × Option (Array Ident)) := p.2.isSome || (p.1.size == 1 && p.1[0]!.name.endsWith "?")
    unless Fren.Core.functionParamsAccepted body.isSome params.size (params.filter named).size do
      let bad := (params.find? (named · != body.isSome)).map (·.1[0]!.span) |>.getD name.span
      err bad (Fren.Core.functionParamsMsg path body.isSome)
    -- As for a variable, with the result type (`lang::bool_naming`).
    let r ← varTy result name
    match body with
    | none =>
      let ps ← params.mapM (elabTy ·.1)
      modify fun s => { s with funs := s.funs.push (path, ps, r) }
    | some body =>
      -- The parameters, declared like a comp's inputs.
      let mut vars : Array CVar := #[]
      for (p, ty?) in params do
        let x := p[0]!
        let xn := Name.mkSimple x.name
        if vars.any (·.name == xn) then err x.span (Fren.Core.dupParamMsg xn)
        lintName .variable xn x.span
        let t ← varTy ty? x
        vars := vars.push { name := xn, role := .input, isPub := true, ty := t, span := x.span }
      let (smt, t) ← elabExpr { vars, place := .prop, selfFn := some n } body
      unless t == r do mismatch body r t (some s!"note: `{n}` returns `{r.show}`")
      lintBools body
      for (x, v) in Fren.Core.unmentioned (vars.map fun v => (v.name, v)) ((mentions body).map (·.getRoot)) do
        lint .unusedVariables v.span (Fren.Core.unusedParamMsg x)
      modify fun s => { s with defs := s.defs.push (path, vars.map fun v => (v.name, v.ty), r, smt) }
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .function, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with table := s.table.addItem { kind := .fnItem, path, isPub, owner := s.module } }
  | .comp isPub name members => do
    -- Its `use`s end with it, even when it has an error.
    try elabComp isPub name members
    catch e => modify (fun s => { s with scope := s.module }); throw e
  | .const isPub name ty value => do
    let n := Name.mkSimple name.name
    liftMsg name.span (Fren.Core.checkConstName n)
    let st ← get
    liftMsg name.span (st.table.checkFresh st.module n)
    lintName .constant n name.span
    let t ← elabTy ty
    -- Its value must be known (`lang::constant`): first its type, then,
    -- once the functions it applies count as used, its value.
    let abstract := t matches .abstract _
    unless Fren.Core.constantAccepted abstract false do
      err (ty[0]!.span.to ty.back!.span) (Fren.Core.unknownConstantMsg abstract)
    let before := (← get).applied.size
    let (smt, t') ← elabExpr { vars := #[], place := .prop, expected? := some t } value
    let applies := (← get).applied.extract before
    unless Fren.Core.constantAccepted abstract applies.isEmpty.not do
      err applies[0]! (Fren.Core.unknownConstantMsg abstract)
    unless t == t' do mismatch value t t' (some s!"note: `{n}` has type `{t.show}`")
    lintBools value
    let path := st.module ++ n
    unless isPub do
      modify fun s => { s with items := s.items.push ({ what := .constant, path, level := s.levels.get .deadCode }, name.span) }
    modify fun s => { s with
      table := s.table.addItem { kind := .constItem, path, isPub, owner := s.module }
      consts := s.consts.insert path (smt, t) }
  | .global name binders body => elabGlobal name binders body
  | .refine name c a => elabRefine name c a
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
      let st ← get
      modify fun s => { s with evidence? := some (value, valueSpan) }
      if let some body := body? then
        elabItem body
        modify fun s => { s with evidence? := st.evidence? }
      return
    let some rest := opt.name.dropPrefix? "fren.lint." | internal opt.span "not a lint option"
    let some lint := Lint.ofName? rest.toString | err opt.span (Fren.Core.unknownLintMsg rest.toString)
    let some requested := LintLevel.ofName? value | err valueSpan (Fren.Core.invalidLevelMsg value)
    let st ← get
    let cur := st.levels.get lint
    let (ok, level) := Fren.Core.setLevel cur.level requested
    unless ok do err stx (Fren.Core.forbiddenMsg lint requested)
    let expectation? ← if requested == .expect then do
        let e : Fren.Core.ExpectationRecord := { lint, level := st.levels.get .unfulfilledExpectations }
        modify fun s => { s with expectations := s.expectations.push (e, stx),
                                 expectationRemovals := s.expectationRemovals.push removal }
        pure (some st.expectations.size)
      else pure none
    modify fun s => { s with levels := s.levels.set lint { level, isSet := true, expectation? } }
    if let some body := body? then
      modify fun s => { s with settingStart? := some (st.settingStart?.getD stx.start) }
      elabItem body
      modify fun s => { s with levels := st.levels, settingStart? := st.settingStart? }

/-- The text of the current file at `sp`. -/
def State.text (s : State) (sp : Span) : String := String.ofList (s.src.extract sp.start sp.stop).toList

def toRange (sp : Span) : Fren.Core.Range := { start := sp.start, stop := sp.stop }

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
  if s.fixing.contains .nonminimalBool then
    for (sp, text) in s.boolFixes do
      if fires .nonminimalBool sp then
        edits := edits.push (toRange sp, text)
        fixed := fixed.push (.nonminimalBool, sp)
  for (l, sp, text) in s.lintFixes do
    if s.fixing.contains l && fires l sp then
      edits := edits.push (toRange sp, text)
      fixed := fixed.push (l, sp)
  if s.fixing.contains .unfulfilledExpectations then
    for (_, sp) in s.expectations, removal in s.expectationRemovals do
      if fires .unfulfilledExpectations sp then
        edits := edits.push (if removal == sp then delete sp else (toRange removal, ""))
        fixed := fixed.push (.unfulfilledExpectations, sp)
  return (edits, fixed)

/-- The lints of the file just elaborated, at its end, and the edits that
fix them, if `fren fix` fixes any. -/
def finishLints : StateM State Unit := do
  let s ← get
  let (reports, fulfilled) := Fren.Core.finishReports
    (s.lintReports ++ Fren.Core.importReports s.useRecords s.used true ++ Fren.Core.deadCodeReports s.items s.usedItems)
  let (unfulfilled, _) := Fren.Core.finishReports (Fren.Core.expectationReports s.expectations fulfilled true)
  let all := reports ++ unfulfilled
  let (edits, fixed) := s.fixes (all.map fun (r, _) => (r.lint, r.ref))
  let diags := all.map fun (r, severity) =>
    { file := s.file, span := r.ref, severity, msg := r.msg, lint? := some r.lint
      fixed := fixed.contains (r.lint, r.ref) : Diag }
  set { s with diags := s.diags ++ diags, edits := s.edits ++ edits.map (s.file, ·) }

/-- Elaborates the items of one file, whose text is `src`, collecting an
error per failed item. `fren fix` fixes the lints `fixing` in it. -/
def elabFile (file : Nat) (src : Array Char) (items : Array Item) (fixing : Array Lint := #[]) :
    StateM State Unit := do
  modify fun s => { s with file, src, fixing, module := .anonymous, scope := .anonymous, levels := s.cliLevels, useRecords := #[], evidence? := none,
                           used := #[], expectations := #[], lintReports := #[], useLocs := #[],
                           expectationRemovals := #[], items := #[], usedItems := #[], boolFixes := #[],
                           lintFixes := #[] }
  for item in items do
    let s ← get
    match (elabItem item).run s with
    | .ok ((), s') => set s'
    | .error f => set { s with diags := s.diags.push f.diag, usedItems := f.usedItems }
  finishLints

/-- `(declare-sort ...)` for every abstract type, `(declare-datatype ...)`
for every enum and record, in order, since each may contain those before
it, `(declare-fun ...)` for every uninterpreted function, and
`(define-fun ...)` for every defined function, in order, since each may
apply those before it. -/
def State.prelude (s : State) : String :=
  let sorts := String.join (s.sorts.toList.map fun p => s!"(declare-sort {itemSym p} 0)\n")
  let enums := String.join (s.datatypes.toList.map (·.decl))
  let funs := String.join (s.funs.toList.map fun (p, ps, r) =>
    s!"(declare-fun {itemSym p} ({" ".intercalate (ps.toList.map (·.sort))}) {r.sort})\n")
  let defs := String.join (s.defs.toList.map fun (p, ps, r, body) =>
    let ps := " ".intercalate (ps.toList.map fun (x, t) => s!"({quote x.toString} {t.sort})")
    s!"(define-fun {itemSym p} ({ps}) {r.sort} {body})\n")
  sorts ++ enums ++ funs ++ defs

end FrenCli
