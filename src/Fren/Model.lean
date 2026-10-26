-- keep-sorted start
import Fren.FinSet
import Fren.Seq
import FrenCore.Check
import FrenCore.Evidence
import FrenCore.Lint
import FrenCore.Names
import FrenCore.Refine
import Lean
-- keep-sorted end

/-!
# The Fren model

Fren's own representation of specifications: modules, items, imports, enums
and comps. It lives in environment extensions and is changed only by Fren's
elaborators (`Fren.Elab`). Everything else reads it. In particular, Fren never
recovers the meaning of a spec by inspecting the Lean declarations it
generates; those are derived artifacts for users.

Module paths are `Name`s (`check`, `a.b`); the root module is
`Name.anonymous`.
-/

open Lean

namespace Fren

register_option fren.evidence : String := {
  defValue := "solver"
  descr := "the evidence of the checks of the next component, global expectation or refinement: \"tested\" to have the `fren` command test them, or \"solver\""
}

export Core (ItemKind Item EnumDef UseDef)

/-- `p₁ ∧ (p₂ ∧ ...)`, or `True`. -/
def mkAndN : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkAnd p (mkAndN ps)

/-- Where an item was declared. -/
structure ItemRef where
  item : Item
  ref : Syntax
  deriving Inhabited

/-- An enum and the Lean inductive generated for it. -/
structure EnumInfo where
  path : Name
  decl : Name
  variants : Array Name
  /-- The Lean types of each variant's payload. -/
  payloads : Array (Array Expr) := #[]
  /-- Its values can be arbitrarily large (`Reqs/Lang/Types`). -/
  unbounded : Bool := false
  /-- Declared `ordered` (`Reqs/Lang/Items#enumerations`). -/
  ordered : Bool := false
  deriving Inhabited

/-- The selector of the `k`th value of the payload of the constructor
`ctor`, generated for an enum. Its name is that of lean-smt's selector of
the constructor's field, which is named `xk`. -/
def selectorName (ctor : Name) (k : Nat) : Name := ctor ++ Name.mkSimple s!"x{k}"

/-- A record and the Lean structure generated for it. -/
structure RecordInfo where
  path : Name
  decl : Name
  /-- The fields, with their Lean types. -/
  fields : Array (Name × Expr)
  unbounded : Bool := false
  deriving Inhabited

/-- The constructor of the structure generated for a record: not `mk`,
which may be a field. -/
def recordCtor (decl : Name) : Name := decl ++ `«{}»

/-- A newtype and the Lean structure generated for it, with one field,
`«0»`, and the constructor `mk` (`Reqs/Generated#newtypes`). -/
structure NewtypeInfo where
  path : Name
  decl : Name
  /-- The Lean type of its underlying type. -/
  under : Expr
  unbounded : Bool := false
  deriving Inhabited

/-- The field of the structure generated for a newtype. -/
def NewtypeInfo.field (n : NewtypeInfo) : Name := n.decl ++ Name.mkSimple "0"

/-- The constructor of the structure generated for a newtype. -/
def NewtypeInfo.ctor (n : NewtypeInfo) : Name := n.decl ++ `mk

/-- A constant and the Lean definition generated for it. -/
structure ConstInfo where
  path : Name
  decl : Name
  type : Expr
  /-- Closed; used wherever the constant is mentioned. -/
  value : Expr
  /-- Its value, if it is an integer constant expression
  (`Reqs/Lang/Expressions#division-and-remainder`). -/
  int? : Option Int := none
  deriving Inhabited

/-- An abstract type or a function. In the model it is a placeholder: an
axiom of its type, which every expression that mentions it uses, so that
instances and global expectations need no plumbing. Where a spec leaves the
model, the placeholder is replaced: by a parameter in the generated
definitions, a local for the solver, and an interpretation in an `impl`. -/
structure AbstractInfo where
  path : Name
  /-- The placeholder axiom. -/
  placeholder : Name
  isType : Bool
  /-- The placeholders of the abstract types in a function's signature. -/
  deps : Array Name := #[]
  deriving Inhabited

/-- The placeholder for the item at `path`. -/
def placeholderName (path : Name) : Name := `Fren.Abstract ++ path

/-- The placeholder of the `Inhabited` instance of the abstract type whose
placeholder, or path, is `n`: not a Fren name, which cannot contain `#`. -/
def inhabitedName (n : Name) : Name := n.str "#inhabited"

/-- Whether `n` is the path or placeholder of an abstract type's `Inhabited`
instance. -/
def isInhabitedName (n : Name) : Bool := n matches .str _ "#inhabited"

/-- A defined function: the generated definition `decl`, which takes a
parameter for each placeholder of `uses`, then its own parameters, and
which the solver unfolds. -/
structure DefinedInfo where
  path : Name
  decl : Name
  uses : Array Name
  nParams : Nat
  deriving Inhabited

/-- A clause of a function's contract, and the Lean definition generated
for it (`Reqs/Generated#contracts`), which takes a parameter for each
placeholder of `uses`, then one for each of the function's parameters. -/
structure ClauseInfo where
  name : Name
  decl : Name
  uses : Array Name
  deriving Inhabited

/-- The contract of the function at `path` (`Reqs/Lang/Items#contracts`). -/
structure ContractInfo where
  path : Name
  pres : Array ClauseInfo
  posts : Array ClauseInfo
  /-- Whether the function is defined: an uninterpreted function's
  postconditions are facts about its applications. -/
  defined : Bool
  deriving Inhabited

/-- The clause `k`'s statement at the arguments `args`. -/
def ClauseInfo.at (k : ClauseInfo) (args : Array Expr) : Expr :=
  mkAppN (mkConst k.decl) (k.uses.map (mkConst ·) ++ args)

/-- `e` with each placeholder of `uses` replaced by the corresponding
expression of `xs`. -/
def replaceUses (uses : Array Name) (xs : Array Expr) (e : Expr) : Expr :=
  e.replace fun
    | .const c _ => (uses.idxOf? c).map (xs[·]!)
    | _ => none

/-- A comp variable: one of its own, or one of an instance's (`w.x`). -/
structure Var where
  name : Name
  role : Core.Role
  /-- Shown in counterexamples: inputs, `pub out`s and instances' `pub out`s. -/
  isPub : Bool
  /-- A `det out` of the comp itself. -/
  isDet : Bool := false
  type : Expr
  ref : Syntax
  /-- The definition of a defined output of the comp itself. -/
  defn? : Option Syntax := none
  deriving Inhabited

inductive PropKind where
  | assume
  | ensure
  | expect
  | cover
  deriving Inhabited, BEq, Repr

def PropKind.keyword : PropKind → String
  | .assume => "assume"
  | .ensure => "ensure"
  | .expect => "expect"
  | .cover => "cover"

/-- An `assume`, `ensure`, `expect` or `cover`. Expressions are closed lambdas over all
of the comp's variables (`CompInfo.vars`). -/
structure PropInfo where
  kind : PropKind
  name : Name
  ref : Syntax
  body : Expr
  /-- The conditions of the top-level `when`/`unless` chain, if any. -/
  trigger? : Option Expr
  triggerRef? : Option Syntax
  /-- The Lean definition generated for this item. -/
  decl : Name
  deriving Inhabited

/-- An instance. Expressions are closed lambdas over all of the
instantiating comp's variables. -/
structure InstInfo where
  name : Name
  comp : Name
  ref : Syntax
  bindings : Expr
  /-- The instantiated comp's meaning (`CompInfo.meaning`) over the instance's
  variables. -/
  behaviour : Expr
  /-- The instantiated comp's assumptions over the instance's variables. -/
  assumes : Array (Name × Expr)
  decl : Name
  deriving Inhabited

structure CompInfo where
  path : Name
  /-- Its own variables in declaration order, then each instance's. -/
  vars : Array Var
  props : Array PropInfo
  insts : Array InstInfo := #[]
  ref : Syntax
  /-- The prefix of the Lean definitions generated for it. -/
  decl : Name
  /-- The placeholders of the abstract types and functions it uses, in
  declaration order: its generated definitions take a parameter for each. -/
  uses : Array Name := #[]
  /-- Each defined output and its definition, a closed lambda over all of
  the comp's variables that mentions no defined output. -/
  defs : Array (Name × Expr) := #[]
  /-- No construct of it is outside the decidable core
  (`view::inconclusive_advice`). -/
  decidable : Bool := true
  /-- `undecidable` is reported as an error in it, so it is not checked
  (`Reqs/Lint/Decidability#undecidable-constructs`), even where the error
  does not stop `#fren_check`, as in a `#guard_msgs`. -/
  undecidableDenied : Bool := false
  /-- It, or one of its instances, applies a relational operator. -/
  relational : Bool := false
  /-- It, or one of its instances, uses `card`. -/
  counts : Bool := false
  /-- Each index and table of its constraints and definitions: the item it
  is in, where that is, the index, or where the question about the table's
  rows is reported, the question (`none` for an index), and the closed
  formula that the index is in range, or that the question holds. -/
  indexes : Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr) := #[]
  /-- The checks that only the `fren` command runs, by testing
  (`Reqs/Check#checking-by-testing`). -/
  tested : Core.Tested := {}
  /-- For the body and contract of a function, the function: then its
  assumptions are its preconditions, and its guarantees, if it is defined,
  its postconditions, each named after the function and the clause. -/
  fn? : Option Name := none
  deriving Inhabited

def CompInfo.assumes (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .assume)
def CompInfo.ensures (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .ensure)
def CompInfo.expects (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .expect)
def CompInfo.covers (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .cover)

/-- Everything a comp says about its variables `args`: assumptions,
requirements and instances. -/
def CompInfo.meaning (c : CompInfo) (args : Array Expr) : Expr :=
  let defEq (d : Name) (e : Expr) : Expr := match c.vars.findIdx? (·.name == d) with
    | some i => mkApp3 (mkConst ``Eq [1]) (c.vars[i]!.type) args[i]! (e.beta args)
    | none => mkConst ``True
  mkAndN <| c.defs.toList.map (fun (d, e) => defEq d e) ++ (c.assumes ++ c.ensures).toList.map (·.body.beta args)
    ++ c.insts.toList.map fun i => mkAnd (i.bindings.beta args) (i.behaviour.beta args)

/-- `CompInfo.meaning` as applications of the generated definitions, to the
placeholders it uses. -/
def CompInfo.meaningDecl (c : CompInfo) (args : Array Expr) : Expr :=
  let args := c.uses.map (mkConst ·) ++ args
  mkAndN <| ((if c.defs.isEmpty then [] else [`defs]) ++ [`assumes, `ensures]).map (fun n => mkAppN (mkConst (c.decl ++ n)) args)
    ++ c.insts.toList.map fun i => mkAppN (mkConst i.decl) args

/-- An `impl` whose obligation was proved (or added as an axiom). -/
structure ImplInfo where
  /-- The theorem or axiom. -/
  decl : Name
  comp : Name
  /-- Proved by the solver, so `decl` is an axiom. -/
  isAxiom : Bool := false
  deriving Inhabited

/-- A `tested` or `trusted` claim. -/
structure ClaimInfo where
  comp : Name
  /-- `tested`: the test files; `trusted`: the justification. -/
  tested : Bool
  texts : Array String
  deriving Inhabited

inductive Entry where
  | item (i : ItemRef)
  | enumInfo (e : EnumInfo)
  | recordInfo (r : RecordInfo)
  | newtypeInfo (n : NewtypeInfo)
  | useDef (u : UseDef)
  | compInfo (c : CompInfo)
  | constInfo (c : ConstInfo)
  | abstractInfo (a : AbstractInfo)
  | definedInfo (d : DefinedInfo)
  | contractInfo (c : ContractInfo)
  /-- An `interp` of the item at `path`, as the definition `decl`. -/
  | interpInfo (path decl : Name)
  /-- A global expectation, as a `CompInfo` whose path is its module, with
  an instance per binder and the expectation as its only constraint. -/
  | globalInfo (path : Name) (c : CompInfo)
  /-- A refinement, as the comp that checks it (`Reqs/Lang/Refinement`). -/
  | refinementInfo (c : CompInfo)
  /-- The body of the defined function, or the value of the constant, at
  `path`, which has tables, as a comp whose path is its module, with the
  function's parameters as inputs, for the checks of its tables. -/
  | bodyInfo (path : Name) (c : CompInfo)
  | implInfo (i : ImplInfo)
  | claimInfo (c : ClaimInfo)
  deriving Inhabited

/-- Everything declared so far, across all imported Lean files. -/
structure State where
  /-- Names, modules and visibility, shared with the standalone binary. -/
  table : Core.Table := {}
  refs : NameMap Syntax := {}
  enums : NameMap EnumInfo := {}
  records : NameMap RecordInfo := {}
  newtypes : NameMap NewtypeInfo := {}
  comps : NameMap CompInfo := {}
  consts : NameMap ConstInfo := {}
  /-- Abstract types and functions, by path. -/
  abstracts : NameMap AbstractInfo := {}
  /-- Each placeholder's position in declaration order. -/
  placeholders : NameMap Nat := {}
  /-- Defined functions, by path. -/
  defined : NameMap DefinedInfo := {}
  /-- The contracts of functions that have one, by the function's path. -/
  contracts : NameMap ContractInfo := {}
  /-- The definition of each abstract type's and function's interpretation,
  by path. -/
  interps : NameMap Name := {}
  /-- Global expectations, by full path. -/
  globals : NameMap CompInfo := {}
  /-- Refinements, as the comps that check them, by path. -/
  refinements : NameMap CompInfo := {}
  /-- The bodies of functions and values of constants that have tables, by
  the function's or constant's path (`Entry.bodyInfo`). -/
  bodies : NameMap CompInfo := {}
  /-- The `impl`s of each comp. -/
  impls : NameMap (Array Name) := {}
  /-- The `impl`s proved by the solver, which are axioms. -/
  axiomImpls : NameSet := {}
  /-- The files of each component's `tested` claims. -/
  tested : NameMap (Array String) := {}
  /-- The justifications of each component's `trusted` claims. -/
  trusted : NameMap (Array String) := {}
  deriving Inhabited

def State.add (s : State) : Entry → State
  | .item i => { s with table := s.table.addItem i.item, refs := s.refs.insert i.item.path i.ref }
  | .enumInfo e =>
    { s with table := s.table.addEnum { path := e.path, variants := e.variants }, enums := s.enums.insert e.path e }
  | .recordInfo r => { s with records := s.records.insert r.path r }
  | .newtypeInfo n => { s with newtypes := s.newtypes.insert n.path n }
  | .useDef u => { s with table := s.table.addUse u }
  | .compInfo c => { s with comps := s.comps.insert c.path c }
  | .constInfo c => { s with consts := s.consts.insert c.path c }
  | .abstractInfo a =>
    { s with abstracts := s.abstracts.insert a.path a
             placeholders := s.placeholders.insert a.placeholder s.placeholders.size }
  | .definedInfo d => { s with defined := s.defined.insert d.path d }
  | .contractInfo c => { s with contracts := s.contracts.insert c.path c }
  | .interpInfo p d => { s with interps := s.interps.insert p d }
  | .globalInfo p c => { s with globals := s.globals.insert p c }
  | .refinementInfo c => { s with refinements := s.refinements.insert c.path c }
  | .bodyInfo p c => { s with bodies := s.bodies.insert p c }
  | .implInfo i =>
    { s with impls := s.impls.insert i.comp ((s.impls.getD i.comp #[]).push i.decl)
             axiomImpls := if i.isAxiom then s.axiomImpls.insert i.decl else s.axiomImpls }
  | .claimInfo c =>
    if c.tested then { s with tested := s.tested.insert c.comp (s.tested.getD c.comp #[] ++ c.texts) }
    else { s with trusted := s.trusted.insert c.comp (s.trusted.getD c.comp #[] ++ c.texts) }

initialize frenExt : SimplePersistentEnvExtension Entry State ←
  registerSimplePersistentEnvExtension {
    addEntryFn := State.add
    addImportedFn := fun arrays => arrays.foldl (fun s es => es.foldl State.add s) {}
  }

/-- The enum whose generated inductive is `decl`. -/
def State.enumOfDecl? (s : State) (decl : Name) : Option EnumInfo :=
  s.enums.foldl (init := none) fun acc _ e => acc <|> if e.decl == decl then some e else none

/-- The record whose generated structure is `decl`. -/
def State.recordOfDecl? (s : State) (decl : Name) : Option RecordInfo :=
  s.records.foldl (init := none) fun acc _ r => acc <|> if r.decl == decl then some r else none

/-- The newtype whose generated structure is `decl`. -/
def State.newtypeOfDecl? (s : State) (decl : Name) : Option NewtypeInfo :=
  s.newtypes.foldl (init := none) fun acc _ n => acc <|> if n.decl == decl then some n else none

/-- The newtype whose Lean type is `ty`, if it is one. -/
def State.newtypeOf? (s : State) (ty : Expr) : Option NewtypeInfo := ty.constName?.bind s.newtypeOfDecl?

/-- Whether the Lean type of a Fren type is unbounded (`Reqs/Lang/Types`). -/
def State.unbounded (s : State) (ty : Expr) : Bool :=
  ty.isConstOf ``String || ty.isAppOf ``Fren.FinSet || ty.isAppOf ``Fren.Seq || match ty.constName? with
  | some d => (s.enumOfDecl? d).any (·.unbounded) || (s.recordOfDecl? d).any (·.unbounded)
    || (s.newtypeOfDecl? d).any (·.unbounded)
  | none => false

/-- Per-file state; not visible to importing files. -/
structure LocalState where
  /-- The module that items are currently being declared in. -/
  currentModule : Name := .anonymous
  /-- Comps declared in this file, in order. -/
  comps : Array Name := #[]
  /-- Global expectations declared in this file, in order. -/
  globals : Array Name := #[]
  /-- Refinements declared in this file, in order. -/
  refinements : Array Name := #[]
  /-- The global expectations of this file, or Markdown spec: each one's
  module, name and text (`duplicate_constraint`). -/
  globalTexts : Array (Name × Name × String) := #[]
  /-- Functions and constants declared in this file whose bodies or values
  have tables, in order. -/
  bodies : Array Name := #[]
  /-- What the lints of this file need (`Fren.Lint`): its `use`s, the names
  resolved through imports, its expectations, and its other lints. -/
  useRecords : Array (Core.UseRecord × Syntax) := #[]
  used : Array Core.UsedName := #[]
  expectations : Array (Core.ExpectationRecord × Syntax) := #[]
  lintReports : Array (Core.LintReport Syntax) := #[]
  /-- The variables, parameters, instances and binders that the item being
  elaborated declares (`many_single_char_names`, `similar_names`). -/
  declaredNames : Array (Name × Syntax) := #[]
  /-- The file's private enumerations and constants, and the items that
  paths in it resolve to (`dead_code`). -/
  items : Array (Core.ItemRecord × Syntax) := #[]
  usedItems : Array Name := #[]
  /-- The lint settings of this file, or Markdown spec, the identifier of
  each, and the identifiers of those in effect at an item
  (`unused_lint_setting`). An identifier is the number of settings before
  it in the Lean file, those of the specs it reads among them, so that a
  setting of the file in effect in a spec is told apart from the spec's
  own. -/
  settings : Array (Core.SettingRecord × Syntax) := #[]
  settingIds : Array Nat := #[]
  seenSettings : Array Nat := #[]
  nextSetting : Nat := 0
  /-- The settings of the Lean file, or of a spec that reads this one, that
  this spec's replace: each one's identifier, and what replaces it. -/
  outerReplaced : Array (Nat × Core.LintTarget × Core.LintLevel) := #[]
  /-- Its assumptions that `unused_assumption` may fire on, and what its
  global expectations read through instances, and its refinements of their
  abstractions: each read's component and input. -/
  assumptions : Array (Core.AssumptionRecord × Syntax) := #[]
  globalReads : Array (Name × Name) := #[]
  /-- Elaborating a Markdown spec (`#fren_md`), which reports its own lints. -/
  inMarkdown : Bool := false
  /-- For each comp, global expectation and refinement declared in a
  Markdown spec, the spec's name in messages, its path relative to the Lean
  file (`Fren.elabMd`), and its text's line map. Its syntax has positions
  in that text, wherever it is checked. -/
  mdSources : NameMap (String × FileMap) := {}
  /-- The Markdown spec being read, if any: what `mdSources` records for the
  items declared now. -/
  mdSource? : Option (String × FileMap) := none
  /-- Where `invisible_characters` has read the comments up to, as a byte
  offset in the text being elaborated: the end of the last Fren command's
  trailing whitespace and comments. -/
  invisibleFrom : Nat := 0
  /-- The items that the Lean file declares itself, not in a spec. An item
  in neither is imported, and its syntax has positions in another module's
  text. -/
  leanItems : NameSet := {}
  /-- While a Markdown spec is elaborated, the Lean file that reads it: its
  name and its text's line map, which place the messages about the items it
  declares itself (`leanItems`). -/
  leanFile? : Option (String × FileMap) := none
  /-- Where the comparisons of `Bool`s in the expression being elaborated
  are, for `bool_equality`. -/
  boolEqs : Array (Option String.Pos.Raw × Option String.Pos.Raw) := #[]
  /-- Where the conditions of `if`s and the operands of `*` in the
  expression being elaborated that mention a variable or an uninterpreted
  function are, for `branches_sharing_code`. -/
  mentioning : Array (Option String.Pos.Raw × Option String.Pos.Raw) := #[]
  /-- Where the variants without payloads in the expression being
  elaborated are, with their paths, for `contradictory_comparisons`. -/
  variants : Array ((Option String.Pos.Raw × Option String.Pos.Raw) × String) := #[]
  /-- Where the calls of `abs` in the expression being elaborated end, for
  `invalid_upcast_comparisons`. -/
  absEnds : Array (Option String.Pos.Raw) := #[]
  /-- What is known of the variants of ordered enumerations, and of the
  newtypes built and read, in the expression being elaborated, for the
  lints of ordered enumerations and newtypes. -/
  facts : Array ((Option String.Pos.Raw × Option String.Pos.Raw) × Core.NodeFact) := #[]
  /-- Some construct of the current item is outside the decidable core,
  whatever the level of `undecidable` (`view::inconclusive_advice`). -/
  outsideCore : Bool := false
  /-- `undecidable` is reported as an error in the current item, which is
  then not checked (`Reqs/Lint/Decidability#undecidable-constructs`). -/
  undecidableDenied : Bool := false
  /-- Whether the current comp, or an instance of it, applies a relational
  operator; with `card`, it is outside the decidable core. -/
  relationalUsed : Bool := false
  /-- Where the current comp counts: its `card`s, and its instances whose
  comps count. -/
  countRefs : Array Syntax := #[]
  /-- The indexes of the constraint being elaborated, each with the term
  that it is in range where it is evaluated (`check::definedness`). -/
  indexes : Array (Syntax × Lean.Term) := #[]
  /-- The questions about the rows of its tables and the arms of its
  `match`es, each where it is reported, with the term that it holds where
  the table or `match` is evaluated (`check::completeness`,
  `check::disjointness`, `check::reachability`). -/
  tables : Array (Syntax × Core.TableGoal × Lean.Term) := #[]
  /-- The static errors so far, by top-level command: its file, where it
  starts and how many errors it has logged (`recordingErrors`). They stop
  `#fren_check` (`Reqs/View#static-errors`). -/
  staticErrors : Array (String × Nat × Nat) := #[]
  /-- How many errors `#fren_check` has logged, which are not static. -/
  checkErrors : Nat := 0
  deriving Inhabited

/-- Records that the item `path` is declared now: in the Markdown spec being
read, if any (`mdSources`). -/
def LocalState.declared (l : LocalState) (path : Name) : LocalState :=
  match l.mdSource? with
  | some source => { l with mdSources := l.mdSources.insert path source }
  | none => { l with leanItems := l.leanItems.insert path }

initialize localExt : EnvExtension LocalState ←
  registerEnvExtension (pure {})

variable {m : Type → Type} [Monad m] [MonadEnv m]

def getState : m State := return frenExt.getState (← getEnv)

/-- The placeholders that `es` mention, and those in the signatures of the
functions among them, in declaration order. -/
def usesOf (es : Array Expr) : m (Array Name) := do
  let s ← getState
  let direct := es.foldl (init := #[]) fun acc e =>
    e.foldConsts acc fun c acc => if s.placeholders.contains c && !acc.contains c then acc.push c else acc
  let deps := direct.foldl (init := direct) fun acc c =>
    let ds := s.abstracts.foldl (init := #[]) fun ds _ a => if a.placeholder == c then a.deps else ds
    ds.foldl (fun acc d => if acc.contains d then acc else acc.push d) acc
  return deps.qsort fun a b => s.placeholders.getD a 0 < s.placeholders.getD b 0

def record (e : Entry) : m Unit := modifyEnv (frenExt.addEntry · e)

/-- Runs `k` with a local for each placeholder of `uses`, in order, named
after its item: a type for an abstract type, and for a function, its type
over the earlier locals. -/
def withUses {α : Type} (uses : Array Name) (k : Array Expr → Meta.MetaM α) : Meta.MetaM α :=
  go 0 #[]
where
  go (i : Nat) (xs : Array Expr) : Meta.MetaM α := do
    if h : i < uses.size then
      let ty := replaceUses uses xs (← getConstInfo uses[i]).type
      -- An abstract type's `Inhabited` instance is an instance argument.
      let bi := if isInhabitedName uses[i] then .instImplicit else .default
      Meta.withLocalDecl (Name.mkSimple uses[i].getString!) bi ty fun x => go (i + 1) (xs.push x)
    else k xs

def getLocal : m LocalState := return localExt.getState (← getEnv)

def modifyLocal (f : LocalState → LocalState) : m Unit :=
  modifyEnv (localExt.modifyState · f)

open Lean Elab Command in
/-- Runs `k`, then records how many errors its top-level command has
logged (`LocalState.staticErrors`), but those of checks
(`LocalState.checkErrors`). An error that `k` throws is logged here, as
`elabCommand` would, to be counted. -/
def recordingErrors (k : CommandElab) : CommandElab := fun stx => do
  let checks := (← getLocal).checkErrors
  try k stx
  catch ex =>
    match ex with
    | .internal id _ => if id == unsupportedSyntaxExceptionId || id == interruptExceptionId then throw ex
                        else logException ex
    | _ => logException ex
  let n := (← get).messages.toList.filter (·.severity == .error) |>.length
  let n := n - ((← getLocal).checkErrors - checks)
  if n == 0 then return
  let key := (← getFileName, (← read).cmdPos.byteIdx)
  modifyLocal fun l =>
    -- A top-level command can elaborate several, as `set_option ... in`
    -- does: the count of its last is the command's.
    match l.staticErrors.back? with
    | some (f, p, _) => if (f, p) == key then { l with staticErrors := l.staticErrors.pop.push (f, p, n) }
                        else { l with staticErrors := l.staticErrors.push (key.1, key.2, n) }
    | none => { l with staticErrors := l.staticErrors.push (key.1, key.2, n) }

end Fren
