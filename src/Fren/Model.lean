-- keep-sorted start
import Fren.FinSet
import Fren.Seq
import FrenCore.Check
import FrenCore.Closures
import FrenCore.Enumeration
import FrenCore.Evidence
import FrenCore.Lint
import FrenCore.Names
import FrenCore.PatternTypes
import FrenCore.Recursion
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

register_option fren.enumeration.size : Nat := {
  defValue := 3
  descr := "the size bound of enumeration: the checks set to `\"enumerated\"` enumerate every behaviour whose values have at most this size"
}

register_option fren.evidence : String := {
  defValue := "solver"
  descr := "the evidence of the checks of the next procedure, global expectation or refinement: \"tested\" to have the `fren` command test them, \"enumerated\" to decide them by enumerating behaviours, \"enumerated+tested\" for both, or \"solver\""
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
  /-- Its payloads' types, as declared, for their constraints. -/
  shape : Core.DataShape := {}
  /-- For a recursive enumeration, what each read of a payload whose type
  brings a constraint brings: its selector, and the constraint as a
  predicate (`Core.readCons`). -/
  readFacts : Array (Name × Expr) := #[]
  /-- Its type parameters (`Reqs/Lang/Generics`), which its payloads' types
  mention as loose bound variables: `.bvar k` for the `k`th. -/
  params : Array Name := #[]
  /-- The Lean type that it is, if it is one of the prelude's types, rather
  than an inductive type generated for it (`Reqs/Lang/Prelude#lean`). -/
  lean? : Option Core.LeanType := none
  deriving Inhabited

/-- The type arguments of an instance, in the order of the enumeration's
type parameters, from those of its Lean type, `args`: a prelude type's Lean
type may order them otherwise (`Core.LeanType.frenArgs`). -/
def EnumInfo.frenArgs (e : EnumInfo) (args : Array α) [Inhabited α] : Array α :=
  match e.lean? with
  | some l => l.frenArgs args
  | none => args

/-- The arguments of its Lean type, from the instance's type arguments: the
inverse of `frenArgs`. -/
def EnumInfo.leanArgs (e : EnumInfo) (args : Array α) [Inhabited α] : Array α :=
  match e.lean? with
  | some l => l.leanArgs args
  | none => args

/-- The Lean types of each variant's payload, in the instance whose Lean
type has the arguments `args` (`lang::instantiation`). -/
def EnumInfo.payloadsAt (e : EnumInfo) (args : Array Expr) : Array (Array Expr) :=
  if e.params.isEmpty then e.payloads else e.payloads.map (·.map (·.instantiate (e.frenArgs args)))

/-- Its Lean type, at universe 0 if it is universe polymorphic, as Lean's
`Option` is: once for each type parameter. -/
def EnumInfo.const (e : EnumInfo) : Expr :=
  mkConst e.decl (if e.lean?.isSome then e.params.toList.map fun _ => .zero else [])

/-- The Lean constructor of the variant at position `idx`: the one generated
for it, or the Lean type's (`Core.LeanType.ctors`). -/
def EnumInfo.ctor (e : EnumInfo) (idx : Nat) : Name :=
  match e.lean? with
  | some l => l.ctors[idx]!
  | none => e.decl ++ e.variants[idx]!

/-- `ctor idx` as a constant, at universe 0, as `const` is. -/
def EnumInfo.ctorConst (e : EnumInfo) (idx : Nat) : Expr :=
  mkConst (e.ctor idx) (if e.lean?.isSome then e.params.toList.map fun _ => .zero else [])

/-- The position of the variant whose Lean constructor is `c`, if it is
one of the enumeration's. -/
def EnumInfo.ctorIdx? (e : EnumInfo) (c : Name) : Option Nat :=
  match e.lean? with
  | some l => l.variantOf? c
  | none => if c.getPrefix == e.decl then e.variants.idxOf? (Name.mkSimple c.getString!) else none

/-- The selector of the `k`th value of the payload of the constructor
`ctor`, generated for an enum. Its name is that of lean-smt's selector of
the constructor's field, which is named `xk`. -/
def selectorName (ctor : Name) (k : Nat) : Name := ctor ++ Name.mkSimple s!"x{k}"

/-- The namespace of the selectors of the Lean constructors of the
prelude's types (`Fren/Prelude.lean`), which Lean's own namespaces do not
get. -/
def preludeSelectors : Name := `Fren.Prelude

/-- The selector of the `k`th value of the payload of the variant at
position `idx`: `selectorName` of its constructor, or for a prelude type's,
the one under `preludeSelectors`. -/
def EnumInfo.sel (e : EnumInfo) (idx k : Nat) : Name :=
  match e.lean? with
  | some l => preludeSelectors ++ selectorName l.ctors[idx]! k
  | none => selectorName (e.ctor idx) k

/-- A record and the Lean structure generated for it. -/
structure RecordInfo where
  path : Name
  decl : Name
  /-- The fields, with their Lean types. -/
  fields : Array (Name × Expr)
  unbounded : Bool := false
  /-- Its fields' types, as declared, for their constraints. -/
  shape : Core.DataShape := {}
  /-- Its type parameters, which its fields' types mention as loose bound
  variables, as an `EnumInfo`'s do. -/
  params : Array Name := #[]
  /-- Declared `ordered` (`Reqs/Lang/Items#ordered-declarations`). -/
  ordered : Bool := false
  deriving Inhabited

/-- The fields, with their Lean types in the instance with the arguments
`args` (`lang::instantiation`). -/
def RecordInfo.fieldsAt (r : RecordInfo) (args : Array Expr) : Array (Name × Expr) :=
  if r.params.isEmpty then r.fields else r.fields.map fun (f, t) => (f, t.instantiate args)

/-- The constructor of the structure generated for a record: not `mk`,
which may be a field. -/
def recordCtor (decl : Name) : Name := decl ++ `«{}»

/-- The constructor of a generic record's structure: `mk!`, which no field
is named, since a field's name has no `!`, rather than `«{}»`. lean-smt
qualifies a parametric datatype's constructor by its sort, as
`(as |Pair.«{}»| (Pair Int Bool))`, where cvc5 finds a constructor only by
a symbol without `|`s (`Reqs/Generated#generic-types`). -/
def genericRecordCtor (decl : Name) : Name := decl ++ Name.mkSimple "mk!"

/-- The constructor of the structure generated for `r`. -/
def RecordInfo.ctor (r : RecordInfo) : Name := if r.params.isEmpty then recordCtor r.decl else genericRecordCtor r.decl

/-- A newtype and the Lean structure generated for it, with one field,
`«0»`, and the constructor `mk` (`Reqs/Generated#newtypes`). -/
structure NewtypeInfo where
  path : Name
  decl : Name
  /-- The Lean type of its underlying type. -/
  under : Expr
  unbounded : Bool := false
  /-- Its field's type, as declared, for its constraint. -/
  shape : Core.DataShape := {}
  /-- Declared `ordered` (`Reqs/Lang/Items#ordered-declarations`). -/
  ordered : Bool := false
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
  /-- Its value has an unbounded quantifier with a bound name that has a
  domain, which sets `fmf-bound` (`Reqs/Lang/Quantifiers#guards`). -/
  guarded : Bool := false
  deriving Inhabited

/-- An abstract type or a function. In the model it is a placeholder: an
axiom of its type, which every expression that mentions it uses, so that
calls and global expectations need no plumbing. Where a spec leaves the
model, the placeholder is replaced: by a parameter in the generated
definitions, a local for the solver, and an interpretation in an `impl`. -/
structure AbstractInfo where
  path : Name
  /-- The placeholder axiom. -/
  placeholder : Name
  isType : Bool
  /-- The placeholders of the abstract types in a function's signature. -/
  deps : Array Name := #[]
  /-- A function's parameters' and result's types, as declared. -/
  ptys : Array Core.PTy × Core.PTy := (#[], default)
  /-- What each application of a function brings, as a predicate of its
  result, if its result's type brings a constraint (`Reqs/Check`). -/
  fact? : Option Expr := none
  /-- A generic function's type parameters, whose placeholder takes a
  `Type` and its `Inhabited` instance for each, before its parameters, and
  its parameters' and result's types, which mention them as
  `Core.Ty.param` (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
  Its signature's own types, `ptys` and `fact?`, mention the placeholders
  of the type parameters (`Core.typeParamPath`). -/
  typeParams : Array Name := #[]
  declared : Array Core.Ty := #[]
  result : Core.Ty := .bool
  /-- And its result's declared type, with its patterns, which mentions the
  type parameters as `Core.Ty.param`. -/
  resultP : Core.PTy := default
  /-- The Lean module that declares it. -/
  module : Name := .anonymous
  deriving Inhabited

/-- The Lean namespace, under the current one, of every declaration generated
for a Fren item (`Reqs/Generated#names`): Lean declares nothing in it but
them, so that no item's name can be one of Lean's, such as `Option`. -/
def generatedNamespace : Name := `Fren.Generated

/-- `pre` followed by the components of `n`: `pre ++ n`, without `++`'s
treatment of macro scopes, which neither has. -/
def underName (pre : Name) : Name → Name
  | .anonymous => pre
  | .str p s => .str (underName pre p) s
  | .num p k => .num (underName pre p) k

/-- The Lean name of the declaration generated for the item at the Fren
path `path`, declared where `ns` is the current Lean namespace
(`Reqs/Generated#names`): `ns.Fren.Generated.path`. Every generated name is
this, or a name under it; a message never shows it, but names the item by
its path. With `ns` anonymous, it is the name relative to the current
namespace, by which a command declares it. -/
def leanName (ns path : Name) : Name := underName (underName ns generatedNamespace) path

/-- The Lean name of the declaration generated for the item at `path`, in
the current namespace (`leanName`). -/
def generatedName [Monad m] [MonadResolveName m] (path : Name) : m Name :=
  return leanName (← getCurrNamespace) path

/-- Opens the namespace of the generated declarations (`leanName`) for the
rest of the current section, so that Lean code there names an item's
declarations by its path, as `climate.Mode.Heat`. Every Fren command does. -/
def openGenerated : Elab.Command.CommandElabM Unit := do
  let d := OpenDecl.simple (underName (← getCurrNamespace) generatedNamespace) []
  unless (← getOpenDecls).contains d do
    Elab.Command.modifyScope fun sc => { sc with openDecls := d :: sc.openDecls }

open Elab Command in
/-- `open`, which, where it opens `Fren.Lang`, Fren's syntax, also opens the
namespace of the generated declarations (`openGenerated`), so that Lean code
that imports a spec names its items' declarations by their paths, as
`check.Verdict`. Any other `open` is Lean's own. -/
@[command_elab Lean.Parser.Command.open] def elabOpenLang : CommandElab := fun stx => do
  let isLang (d : OpenDecl) := d matches .simple `Fren.Lang _
  let before := (← getOpenDecls).filter isLang |>.length
  elabOpen stx
  if ((← getOpenDecls).filter isLang |>.length) > before then openGenerated

/-- What the checks need of the elaborator, which runs them: the Lean type
of a type, the constraint that a value of a declared type brings as a
predicate, over an `Int` for a `Nat` if asked, as `resultFact?` gives it,
and the type that a Lean type stands for, if one does. -/
structure ElabHooks where
  leanType : Core.Ty → MetaM Expr
  fact : Core.PTy → Bool → MetaM (Option Expr)
  coreTy : Expr → MetaM (Option Core.Ty)

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
  /-- Its parameters' and result's types, as declared. -/
  ptys : Array Core.PTy × Core.PTy := (#[], default)
  /-- Its type parameters, if it is generic, and its parameters' and
  result's types, which mention them as `Core.Ty.param`
  (`Reqs/Lang/GenericFunctions`). -/
  typeParams : Array Name := #[]
  declared : Array Core.Ty := #[]
  result : Core.Ty := .bool
  /-- Its parameters, if it is higher-order: each a value's type or a
  function type, as its signature declares them (`Reqs/Lang/HigherOrder`).
  Its definition takes its value parameters first, then its function
  parameters. -/
  hoParams : Array Core.HoParam := #[]
  /-- For each of its function parameters, in order, the definition of the
  obligations of a closure given for it, and the placeholders that it uses:
  over the parameters and a predicate of the closure's parameters, that the
  predicate holds at each application of the function parameter, under its
  guards (`lang::closure_obligation`). -/
  oblDecls : Array (Name × Array Name) := #[]
  /-- Its body has an unbounded quantifier with a bound name that has a
  domain, directly or through the functions and constants it applies,
  which sets `fmf-bound` (`Reqs/Lang/Quantifiers#guards`). -/
  guarded : Bool := false
  /-- The definition of its body as the solver sees it, if `decl`'s is a
  Lean `match` instead (`Reqs/Generated#matches`): the solver unfolds
  this one (`deltaDefined`). -/
  solver? : Option Name := none
  /-- It is a structural recursion (`lang::structural_recursion`): `solver?`
  is then its recursive definition over the placeholders themselves, not
  over a local for each, which the solver is given as a recursive
  definition (`define-fun-rec`) rather than unfolded
  (`Reqs/Lang/Recursion#solver-encoding`). -/
  recursive : Bool := false
  /-- Its applications are decided on arguments that vary: not a structural
  recursion, or one that `Core.RecKind.decided` decides
  (`lang::recursive_kind`). -/
  decided : Bool := true
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

/-- The placeholders of the type parameters `tps` of the generic function
at `path`, each followed by that of its `Inhabited` instance: what its
placeholder, or a definition of it, takes first
(`Reqs/Generated#generic-functions`). -/
def typeParamPlaceholders (path : Name) (tps : Array Name) : Array Name :=
  tps.mapIdx (fun k p => placeholderName (Core.typeParamPath path k p)) |>.flatMap fun ph => #[ph, inhabitedName ph]

/-- `e`, of the generic function at `path` with the type parameters `tps`,
at the instance whose type arguments and `Inhabited` instances are
`targs`, in the order of `typeParamPlaceholders`: each placeholder of a
type parameter, or of its instance, replaced. -/
def atInstance (path : Name) (tps : Array Name) (targs : Array Expr) (e : Expr) : Expr :=
  replaceUses (typeParamPlaceholders path tps) targs e

/-- The clause `k`, of the generic function at `path` with the type
parameters `tps`, at the instance `targs` (`atInstance`), at the arguments
`args`. -/
def ClauseInfo.atInst (k : ClauseInfo) (path : Name) (tps : Array Name) (targs args : Array Expr) : Expr :=
  atInstance path tps targs (k.at args)

/-- A procedure variable: one of its own, or one of a call's (`w.x`). -/
structure Var where
  name : Name
  role : Core.Role
  /-- Shown in counterexamples: parameters, results and calls' results. -/
  isPub : Bool
  /-- A `det` variable of the procedure itself. -/
  isDet : Bool := false
  type : Expr
  ref : Syntax
  /-- The definition of a defined output of the procedure itself. -/
  defn? : Option Syntax := none
  /-- Its type as declared, with its patterns. -/
  ptype : Core.PTy := default
  /-- The constraint that its type brings, as a predicate of its value
  (`Reqs/Lang/Procedures#pattern-types`). -/
  fact? : Option Expr := none
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
of the procedure's variables (`CompInfo.vars`). -/
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

/-- A call. Expressions are closed lambdas over all of the
calling procedure's variables. -/
structure InstInfo where
  name : Name
  comp : Name
  ref : Syntax
  bindings : Expr
  /-- The called procedure's meaning (`CompInfo.meaning`) over the call's
  variables. -/
  behaviour : Expr
  /-- The called procedure's assumptions over the call's variables,
  after its inputs' types' obligations (`Core.Inst.typed`). -/
  assumes : Array (Name × Expr)
  /-- Which of `assumes` are its inputs' types' obligations, with those types. -/
  typed : Array (Name × String) := #[]
  decl : Name
  deriving Inhabited

structure CompInfo where
  path : Name
  /-- Its own variables in declaration order, then each call's. -/
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
  the procedure's variables that mentions no defined output. -/
  defs : Array (Name × Expr) := #[]
  /-- No construct of it is outside the decidable core
  (`view::inconclusive_advice`). -/
  decidable : Bool := true
  /-- `undecidable` is reported as an error in it, so it is not checked
  (`Reqs/Lint/Decidability#undecidable-constructs`), even where the error
  does not stop `#fren_check`, as in a `#guard_msgs`. -/
  undecidableDenied : Bool := false
  /-- It, or one of its calls, applies a relational operator. -/
  relational : Bool := false
  /-- It, or one of its calls, uses `card`. -/
  counts : Bool := false
  /-- It has an unbounded quantifier with a bound name that has a domain,
  directly, through a call or through a defined function, which sets
  `fmf-bound` (`Reqs/Lang/Quantifiers#guards`). -/
  guarded : Bool := false
  /-- Each index and table of its constraints and definitions: the item it
  is in, where that is, the index, or where the question about the table's
  rows is reported, the question (`none` for an index), and the closed
  formula that the index is in range, or that the question holds. -/
  indexes : Array (Name × Core.IndexPlace × Syntax × Option Core.TableGoal × Expr) := #[]
  /-- The checks that only the `fren` command runs, by testing
  (`Reqs/Check#checking-by-testing`). -/
  tested : Core.Tested := {}
  /-- The checks that are decided by enumeration
  (`Reqs/Check#checking-by-enumeration`), and the size bound. -/
  enumerated : Core.Tested := {}
  /-- Its queries use finite-model finding: the contract of an instance of
  a generic function without a body at another one's type parameters
  (`Core.Ty.hasTypeParam`). -/
  finiteModel : Bool := false
  enumSize : Nat := 3
  /-- For the body and contract of a function, the function: then its
  assumptions are its preconditions, and its guarantees, if it is defined,
  its postconditions, each named after the function and the clause. -/
  fn? : Option Name := none
  /-- A global expectation with a block (`Core.Comp.global`). -/
  global : Bool := false
  deriving Inhabited

def CompInfo.assumes (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .assume)
def CompInfo.ensures (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .ensure)
def CompInfo.expects (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .expect)
def CompInfo.covers (c : CompInfo) : Array PropInfo := c.props.filter (·.kind == .cover)

/-- Everything a procedure says about its variables `args`: assumptions,
requirements and calls. -/
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
  a call per binder and the expectation as its only constraint. -/
  | globalInfo (path : Name) (c : CompInfo)
  /-- A refinement, as the procedure that checks it (`Reqs/Lang/Refinement`). -/
  | refinementInfo (c : CompInfo)
  /-- The body of the defined function, or the value of the constant, at
  `path`, which has tables, as a procedure whose path is its module, with the
  function's parameters as inputs, for the checks of its tables. -/
  | bodyInfo (path : Name) (c : CompInfo)
  /-- A type alias, with the Lean type and the declared type it names. -/
  | aliasInfo (path : Name) (ty : Expr) (pty : Core.PTy)
  | implInfo (i : ImplInfo)
  | claimInfo (c : ClaimInfo)
  /-- An application of a generic function, in the Lean module `module`
  (`State.genericUses`). -/
  | genericUse (module : Name) (u : Core.GenericUse)
  /-- A run of checks checked the contract of the instance of the generic
  function `f` at `targs` (`State.checkedInstances`). -/
  | instanceChecked (f : Name) (targs : Array Core.Ty)
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
  /-- Refinements, as the procedures that check them, by path. -/
  refinements : NameMap CompInfo := {}
  /-- The bodies of functions and values of constants that have tables, by
  the function's or constant's path (`Entry.bodyInfo`). -/
  bodies : NameMap CompInfo := {}
  /-- The type aliases, each with the Lean type and the declared type it names. -/
  aliases : NameMap (Expr × Core.PTy) := {}
  /-- The `impl`s of each comp. -/
  impls : NameMap (Array Name) := {}
  /-- The `impl`s proved by the solver, which are axioms. -/
  axiomImpls : NameSet := {}
  /-- The files of each procedure's `tested` claims. -/
  tested : NameMap (Array String) := {}
  /-- The justifications of each procedure's `trusted` claims. -/
  trusted : NameMap (Array String) := {}
  /-- The applications of generic functions, in order (`Entry.genericUse`),
  from which the instances that the spec applies follow
  (`State.appliedInstances`). -/
  genericUses : Array (Name × Core.GenericUse) := #[]
  /-- The instances whose contracts a run of checks, in this module or one
  it imports, has checked, which a later run does not check again
  (`lang::instance_site`). -/
  checkedInstances : Array (Name × Array Core.Ty) := #[]
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
  | .genericUse m u => { s with genericUses := s.genericUses.push (m, u) }
  | .instanceChecked f targs => { s with checkedInstances := s.checkedInstances.push (f, targs) }
  | .contractInfo c => { s with contracts := s.contracts.insert c.path c }
  | .interpInfo p d => { s with interps := s.interps.insert p d }
  | .globalInfo p c => { s with globals := s.globals.insert p c }
  | .refinementInfo c => { s with refinements := s.refinements.insert c.path c }
  | .bodyInfo p c => { s with bodies := s.bodies.insert p c }
  | .aliasInfo p t pt => { s with aliases := s.aliases.insert p (t, pt) }
  | .implInfo i =>
    { s with impls := s.impls.insert i.comp ((s.impls.getD i.comp #[]).push i.decl)
             axiomImpls := if i.isAxiom then s.axiomImpls.insert i.decl else s.axiomImpls }
  | .claimInfo c =>
    if c.tested then { s with tested := s.tested.insert c.comp (s.tested.getD c.comp #[] ++ c.texts) }
    else { s with trusted := s.trusted.insert c.comp (s.trusted.getD c.comp #[] ++ c.texts) }

/-- The type parameters of the generic function at `path`, defined or not. -/
def State.typeParamsOf (s : State) (path : Name) : Array Name :=
  match s.defined.get? path, s.abstracts.get? path with
  | some d, _ => d.typeParams
  | none, some a => a.typeParams
  | none, none => #[]

/-- Each instance that the spec's items use of a generic function without a
body, with where its contract is checked (`Core.instanceSites`), from the
Lean module `main` being checked: the modules that it imports are earlier
files, as the `fren` command's are, and a function declared in one of them
does not know of the instances that `main` applies. `checked` says which items the run
checks, by path, and an instance that an earlier run checked is not checked
again. -/
def State.instanceSites (s : State) (main : Name) (checked : Name → Bool) : Array (Core.InstanceSite × Name × Array Core.Ty) :=
  let file (m : Name) : Nat := if m == main then 1 else 0
  Core.instanceSites (s.genericUses.map fun (m, u) => { u with file := file m }) s.typeParamsOf
    (fun g => (s.abstracts.get? g).bind fun a => if a.typeParams.isEmpty then none else some (file a.module))
    checked fun f targs => s.checkedInstances.contains (f, targs)

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

/-- Whether the enumeration, record or newtype at `path` is declared
`ordered`, for `Core.Ty.ordered`. -/
def State.orderedDecl (s : State) (path : Name) : Bool :=
  (s.enums.get? path).any (·.ordered) || (s.records.get? path).any (·.ordered) || (s.newtypes.get? path).any (·.ordered)

/-- How values of `t` are compared, if it is ordered (`Core.orderPlan?`). -/
def State.orderPlan? (s : State) (t : Core.Ty) : Option Core.OrderPlan :=
  let fieldsOf (p : Name) := ((s.records.get? p).map fun r =>
    r.fields.zipIdx.toList.map fun ((f, _), k) => (f, ((r.shape.parts[0]?.bind (·[k]?)).map (·.ty)).getD .bool)).getD []
  Core.orderPlan? s.orderedDecl fieldsOf (s.records.size + s.newtypes.size) t

/-- What is known of the record, newtype or enumeration at `path`, for
the constraints of its values (`Core.DataShape`). -/
def State.shapeOf (s : State) (path : Name) : Option Core.DataShape :=
  (s.enums.get? path).map (·.shape) <|> (s.records.get? path).map (·.shape) <|> (s.newtypes.get? path).map (·.shape)

/-- The obligation of a value given where the type `ty` is declared, in a
definedness goal: `p`, marked with the type, as written, so that the check
reports it (`Reqs/Check#pattern-types`). -/
def typeObligation (_ty : String) (p : Prop) : Prop := p

/-- `ty`, if `e` is marked with it as an obligation (`typeObligation`). -/
def obligationTy? (e : Expr) : Option String :=
  (e.find? (·.isAppOfArity ``Fren.typeObligation 2)).bind fun m =>
    match m.appFn!.appArg!.consumeMData with
    | .lit (.strVal s) => some s
    | _ => none

/-- The enumeration whose Lean type, or an instance of it, is `ty`. -/
def State.enumOf? (s : State) (ty : Expr) : Option EnumInfo := ty.getAppFn.constName?.bind s.enumOfDecl?

/-- The record whose Lean type, or an instance of it, is `ty`. -/
def State.recordOf? (s : State) (ty : Expr) : Option RecordInfo := ty.getAppFn.constName?.bind s.recordOfDecl?

/-- Per-file state; not visible to importing files. -/
structure LocalState where
  /-- The module that items are currently being declared in. -/
  currentModule : Name := .anonymous
  /-- The names that the pattern tests of the chain of `and` being
  translated bind, innermost last, for the later operands of the chain and
  the body of the `when` or `if` whose condition it is
  (`lang::test_scope`): each with its term, its type, its scrutinee, and
  the number of binders in scope there. -/
  bound : Array (Name × Syntax × Expr × Syntax × Nat) := #[]
  /-- The positions of the pattern tests translated whose patterns bind
  names, for `lintBools`, which reads and clears them. -/
  bindingTests : Array (Option String.Pos.Raw × Option String.Pos.Raw) := #[]
  /-- The generic function being declared, with its type parameters, which
  are abstract types within it (`Reqs/Lang/GenericFunctions`). -/
  fnTypeParams : Option (Name × Array Name) := none
  /-- The item being elaborated, by its path, which an application is in
  (`Core.GenericUse`). -/
  currentItem : Name := .anonymous
  /-- Where each closure's obligation is checked, by its position, with the
  higher-order function that its closure is given to (`Core.viaNote`). -/
  vias : Array (Option String.Pos.Raw × Name) := #[]
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
  /-- The reports of `manual_nat` in the file, by their procedures and
  variables, reported at its end unless a call or a refinement in it
  keeps the variable an `Int` (`natKept`). -/
  natReports : Array (Name × String × Core.LintReport Syntax) := #[]
  /-- The variables that a call or a refinement in the file keeps
  `Int`s, by their procedures (`Core.refinementGiven`). -/
  natKept : Array (Name × String) := #[]
  /-- The variables, parameters, calls and binders that the item being
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
  global expectations read through calls, and its refinements of their
  abstractions: each read's procedure and input. -/
  assumptions : Array (Core.AssumptionRecord × Syntax) := #[]
  globalReads : Array (Name × Name) := #[]
  /-- Elaborating a Markdown spec (`#fren_md`), which reports its own lints. -/
  inMarkdown : Bool := false
  /-- For each procedure, global expectation and refinement declared in a
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
  function are, and what each mentions, for `branches_sharing_code`. -/
  mentioning : Array ((Option String.Pos.Raw × Option String.Pos.Raw) × List Fren.Core.Mention) := #[]
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
  /-- Where the orderings in it are, by the type they compare, for the
  lints of integers. -/
  ordereds : Array ((Option String.Pos.Raw × Option String.Pos.Raw) × Core.Ordered) := #[]
  /-- Where the bound names of quantifiers are mentioned, each with the
  number of binders outside the bound name, for `trivial_quantifier`. -/
  boundMentions : Array ((Option String.Pos.Raw × Option String.Pos.Raw) × Nat) := #[]
  /-- Some construct of the current item is outside the decidable core,
  whatever the level of `undecidable` (`view::inconclusive_advice`). -/
  outsideCore : Bool := false
  /-- `undecidable` is reported as an error in the current item, which is
  then not checked (`Reqs/Lint/Decidability#undecidable-constructs`). -/
  undecidableDenied : Bool := false
  /-- Whether the current procedure, or a call of it, applies a relational
  operator; with `card`, it is outside the decidable core. -/
  relationalUsed : Bool := false
  /-- The current item has an unbounded quantifier with a bound name that
  has a domain, directly, through a call or through a defined function
  or constant, so its queries set `fmf-bound` (`Reqs/Lang/Quantifiers#guards`). -/
  guardedUsed : Bool := false
  /-- In a defined function's body, its uses of itself so far, each where
  it is written (`lang::structural_recursion`). -/
  recUses : Array (Lean.Syntax × Core.RecUse) := #[]
  /-- In a defined function's body, the occurrences so far of its
  parameters and of the binders bound from their payloads, each by where
  it starts (`lang::recursive_kind`). -/
  recOccs : Array (String.Pos.Raw × Core.PayloadOcc) := #[]
  /-- In a defined function's body, the patterns of the `match`es on a
  parameter, or on a binder bound from a payload of one, that are not a Lean
  `match` and have a recursive application under them, each the first
  pattern that a Lean `match` does not have (`lang::recursive_match`). -/
  recMatches : Array Lean.Syntax := #[]
  /-- The memberships `x in e` of the guards of the quantifiers over elements
  being elaborated, by where `e` is: whether `e` is a sequence, and the
  `undecidable` report that `in` defers until the quantifier is known to
  be outside the core, if it has one. -/
  elemMembers : Array ((Option String.Pos.Raw × Option String.Pos.Raw) × Bool × Option (Lean.Syntax × Core.Msg)) := #[]
  /-- Where the current procedure counts: its `card`s, and its calls whose
  procedures count. -/
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

/-! ## The forms of generated definitions (`Reqs/Generated#computable-definitions`) -/

/-- What a generated definition's value is (`generated::ValueKind`). -/
inductive ValueKind where
  /-- A proposition, or a function to one: a type, with nothing to run. -/
  | proposition
  /-- Data, or a function to it. -/
  | data
  deriving DecidableEq, Repr, Inhabited

/-- A declaration that a generated definition's value mentions
(`generated::Mention`). -/
inductive Mention where
  /-- One with code: a compiled definition, a constructor, and so on. -/
  | computable
  /-- `Classical.propDecidable`, which decides an unbounded quantifier, or
  equality on an abstract type, where a `Bool` is needed of it. -/
  | classicalDecision
  /-- A definition marked `noncomputable`, such as another generated one. -/
  | noncomputableDecl
  /-- An axiom that is not a proposition, which has no code. -/
  | dataAxiom
  deriving DecidableEq, Repr, Inhabited

/-- How a generated definition is added (`generated::DefinitionForm`). -/
inductive DefinitionForm where
  | notCompiled
  | compiled
  | markedNoncomputable
  deriving DecidableEq, Repr, Inhabited

/-- How a generated definition, whose value is `value` and mentions the
declarations `mentions`, is added (`generated::definition_form`): a
proposition is not compiled, and data is compiled unless it mentions a
declaration without code, when it is `noncomputable`. -/
def definitionForm (value : ValueKind) (mentions : Array Mention) : DefinitionForm :=
  match value with
  | .proposition => .notCompiled
  | .data =>
    if mentions.contains .classicalDecision || mentions.contains .noncomputableDecl || mentions.contains .dataAxiom then
      .markedNoncomputable
    else .compiled

/-- What the head of a pattern is, where Lean's `match` sees it
(`generated::Head`): an or-pattern at the top of an arm's pattern is its
alternatives, each its own Lean pattern, and not an `orPattern`. -/
inductive PatHead where
  | wildcard
  | binder
  | variant
  /-- A literal or a range. -/
  | literal
  | orPattern
  deriving DecidableEq, Repr, Inhabited

/-- What a `match`'s scrutinee is (`generated::Scrutinee`). -/
inductive ScrutineeKind where
  | enumeration
  | other
  deriving DecidableEq, Repr, Inhabited

/-- What a `match`'s arms are (`generated::ArmKind`). -/
inductive ArmKind where
  | values
  /-- Propositions, a `Bool`'s Lean form, which have no `Decidable`
  instance as a Lean `match`, but do as an `if`. -/
  | propositions
  deriving DecidableEq, Repr, Inhabited

/-- What a `match` becomes in a defined function's Lean definition
(`generated::MatchForm`). -/
inductive MatchForm where
  | leanMatch
  | ifChain
  deriving DecidableEq, Repr, Inhabited

/-- What a `match` on a `scrutinee`, whose arms are `arms` and whose
patterns have the heads `heads`, becomes in a defined function's Lean
definition (`generated::match_form`): a Lean `match` where its scrutinee is
an enumeration, its arms are values, and each of its patterns is Lean's,
with no literal, range or or-pattern within it; `if`s otherwise. -/
def matchForm (scrutinee : ScrutineeKind) (arms : ArmKind) (heads : Array PatHead) : MatchForm :=
  if scrutinee == .enumeration && arms == .values && !heads.contains .literal && !heads.contains .orPattern then
    .leanMatch
  else .ifChain

/-- The name of the definition of a defined function's body as the solver
sees it, beside its declaration `decl`, whose body is a Lean `match`
(`DefinedInfo.solver?`): not a Fren name, which has no `#`. -/
def solverName (decl : Name) : Name := decl.str "#solver"

/-- `e` with the definitions that `p` holds of unfolded, as
`Meta.deltaExpand` unfolds them, where a defined function with a solver
form (`DefinedInfo.solver?`) is unfolded to that form instead of its
declaration's body, so that the solver sees the same terms whatever form
the declaration has. -/
def deltaDefined (s : State) (e : Expr) (p : Name → Bool) : CoreM Expr := do
  -- Each declaration with a solver form: that form, and how many of the
  -- arguments, its placeholders', the form does not take, as a structural
  -- recursion's does not.
  let redirect := s.defined.foldl (init := ({} : NameMap (Name × Nat))) fun acc _ d =>
    match d.solver? with
    | some n => acc.insert d.decl (n, if d.recursive then d.uses.size else 0)
    | none => acc
  if redirect.isEmpty then return ← Meta.deltaExpand e p
  let solvers := redirect.foldl (init := ({} : NameSet)) fun acc _ (n, _) => acc.insert n
  -- A structural recursion's solver form is not unfolded: the solver is
  -- given its recursive definition.
  let recursive := s.defined.foldl (init := ({} : NameSet)) fun acc _ d =>
    if d.recursive then d.solver?.elim acc acc.insert else acc
  Core.transform e fun e => do
    let e := match e.getAppFn with
      | .const c ls => match redirect.get? c with
        | some (n, k) => mkAppN (.const n ls) (e.getAppArgs.extract k)
        | none => e
      | _ => e
    match ← Meta.delta? e fun n => (p n || solvers.contains n) && !recursive.contains n with
    | some e' => return .visit e'
    | none => return .continue e

def getLocal : m LocalState := return localExt.getState (← getEnv)

def modifyLocal (f : LocalState → LocalState) : m Unit :=
  modifyEnv (localExt.modifyState · f)

open Lean Elab Command in
/-- Runs `k`, then records how many errors its top-level command has
logged (`LocalState.staticErrors`), but those of checks
(`LocalState.checkErrors`). An error that `k` throws is logged here, as
`elabCommand` would, to be counted. Then it opens the namespace of the
generated declarations (`openGenerated`).

A command that Lean's parser recovered from a parse error, which it has
reported, has missing parts: it is not elaborated, as the `fren` command
stops at the parse error (`Reqs/View#static-errors`). -/
def recordingErrors (k : CommandElab) : CommandElab := fun stx => do
  if stx.hasMissing then return
  let checks := (← getLocal).checkErrors
  try k stx
  catch ex =>
    match ex with
    | .internal id _ => if id == unsupportedSyntaxExceptionId || id == interruptExceptionId then throw ex
                        else logException ex
    | _ => logException ex
  -- A generic function's type parameters end with it, even after an error.
  modifyLocal fun l => { l with fnTypeParams := none }
  openGenerated
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
