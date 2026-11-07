-- keep-sorted start
import Fren.Check
import Fren.Elab
import Fren.Prelude
import FrenCore.Enumeration
-- keep-sorted end

/-!
# Checking by enumeration in Lean (`Reqs/Check#checking-by-enumeration`)

The Lean-hosted front end's side of `Fren.Core.Enumeration`: each atom, a
proposition over the procedure's variables, is compiled, with Lean's
evaluator, into a function of an assignment of the slots, which reads each
variable's value from its slot's values and decides the proposition. The
defined outputs are replaced by their definitions, the abstract types by
`Nat`, whose `k` is the type's `k`th value, and the unspecified value of
each type, `Fren.Seq.nth ∅ 0`, by its hidden slot's, which an index out
of range reads too (`Enum.nthOr`).
-/

open Lean Meta

namespace Fren

/-- The value of slot `i` in the assignment `env`, of the slot's values
`vs`, or `d` if there is none. -/
def Enum.pick {α : Type} (vs : Array α) (d : α) (env : Array Nat) (i : Nat) : α := vs.getD (env.getD i 0) d

/-! The slots' values as the search holds them, `EVal`s, read at run time
by decoders that the atoms are compiled with, so that the compiled code
does not grow with the number of values (`decoderOf`); and a defined
output's value read back to an `EVal` by an encoder (`encoderOf`). Each
decoder gives a value for any `EVal`, so that none needs a default. -/

open Core.Enumeration (EVal) in
def Enum.decBool : EVal → Bool
  | .bool b => b
  | _ => false

open Core.Enumeration (EVal) in
def Enum.decInt : EVal → Int
  | .int i => i
  | .abs k => k
  | _ => 0

open Core.Enumeration (EVal) in
def Enum.decNat : EVal → Nat
  | .abs k => k
  | .int i => i.toNat
  | _ => 0

open Core.Enumeration (EVal) in
def Enum.decStr : EVal → String
  | .str t => t
  | _ => ""

open Core.Enumeration (EVal) in
def Enum.decPair.{u, v} {α : Type u} {β : Type v} (fa : EVal → α) (fb : EVal → β) : EVal → α × β
  | .pair a b => (fa a, fb b)
  | _ => (fa (.bool false), fb (.bool false))

open Core.Enumeration (EVal) in
def Enum.decSeq.{u} {α : Type u} (f : EVal → α) : EVal → Seq α
  | .seq xs => Seq.ofList (xs.map f)
  | _ => Seq.ofList []

open Core.Enumeration (EVal) in
def Enum.decSet.{u} {α : Type u} (f : EVal → α) : EVal → FinSet α
  | .set xs => FinSet.ofList (xs.map f)
  | _ => FinSet.ofList []

open Core.Enumeration (EVal) in
/-- `f` at a constructor's position and its values, `(0, [])` for any
other value. -/
def Enum.decCtor.{u} {α : Type u} (f : Nat → List EVal → α) : EVal → α
  | .ctor i as => f i as
  | _ => f 0 []

open Core.Enumeration (EVal) in
/-- The `j`th of `as`, or `false`, which every decoder reads as some value. -/
def Enum.arg (as : List EVal) (j : Nat) : EVal := as.getD j (.bool false)

open Core.Enumeration (EVal) in
/-- A recursive type's decoder: `step`, which reads a value whose fields of
that same type `self` reads, iterated `d` times from `dflt`. `d` is at
least how deeply the values read nest (`evalDepth`), so that `dflt` is
never reached. -/
def Enum.decFix.{u} {α : Type u} (dflt : α) (step : (EVal → α) → EVal → α) : Nat → EVal → α
  | 0, _ => dflt
  | d + 1, v => step (Enum.decFix dflt step d) v

/-- How often a recursive type's encoder is iterated (`Enum.encFix`): far
more often than any value that a check can compute nests, which the stack
would not hold. -/
def Enum.encFuel : Nat := 1000000

open Core.Enumeration (EVal) in
/-- What a recursive type's encoder gives where it has been iterated too
often (`Enum.encFix`): a constructor at a position no type has, which
`EVal.unread` finds. -/
def Enum.unread : EVal := .ctor Enum.encFuel []

open Core.Enumeration (EVal) in
/-- A recursive type's encoder: `step`, which encodes a value whose fields
of that same type `self` encodes, iterated `d` times, `Enum.unread` where
that is not enough. -/
def Enum.encFix.{u} {α : Type u} (step : (α → EVal) → α → EVal) : Nat → α → EVal
  | 0, _ => Enum.unread
  | d + 1, x => step (Enum.encFix step d) x

open Core.Enumeration (EVal) in
/-- Whether `v` has `Enum.unread` in it: a value that its encoder did not
read to the end. -/
partial def Enum.hasUnread : EVal → Bool
  | .ctor i as => i == Enum.encFuel || as.any Enum.hasUnread
  | .pair a b => Enum.hasUnread a || Enum.hasUnread b
  | .seq xs | .set xs => xs.any Enum.hasUnread
  | _ => false

open Core.Enumeration (EVal) in
/-- The value of slot `i` in the assignment `env`, of the slots' values
`tables`, by `dec`. -/
def Enum.pickE.{u} {α : Type u} (dec : EVal → α) (tables : Array (Array EVal)) (env : Array Nat) (i : Nat) : α :=
  dec ((tables.getD i #[]).getD (env.getD i 0) (.bool false))

open Core.Enumeration (EVal) in
def Enum.encSeq.{u} {α : Type u} (f : α → EVal) (q : Seq α) : EVal := .seq (q.toList.map f)

open Core.Enumeration (EVal) in
def Enum.encSet.{u} {α : Type u} (f : α → EVal) (s : FinSet α) : EVal := .set ((FinSet.toListImpl s).map f)

/-- The position of `a` among `vs`, or `vs.size` if it is not there. -/
def Enum.index {α : Type} [BEq α] (vs : Array α) (a : α) : Nat := (vs.findIdx? (· == a)).getD vs.size

/-- An uninterpreted function's value, in the assignment `env`, at the
arguments at the positions `idx` among its parameters' values, of sizes
`sizes`: the result of `rs` that the table of its slot `slot` gives, or
the first, `d` if none, where an argument is not among them
(`Core.Enumeration.FunSlot`). -/
def Enum.apply {β : Type} (rs : Array β) (d : β) (tables env : Array Nat) (slot : Nat) (sizes idx : Array Nat) : β :=
  match Core.Enumeration.tupleIndex sizes idx with
  | some pos => rs.getD (Core.Enumeration.tableEntry rs.size (tables.getD (env.getD slot 0) 0) pos) d
  | none => rs.getD 0 d

/-! ## Partial truth (`Reqs/Check#quantifiers-up-to-the-bound`)

A quantifier evaluated by enumeration ranges over its domain, or its
type's values up to the bound, and its truth is `none` where no instance
decides it and the values are not all of its type's. Connectives are the
strong Kleene ones, as the `fren` command's evaluator has them. -/

/-- A quantifier's truth, a `forall` if `universal`, over `values`, all of
its domain's if `exact`: an instance that decides it does so; the other
value needs every instance known and the domain exhausted. -/
def Enum.quantify {α : Type} (values : Array α) (exact universal : Bool) (body : α → Option Bool) : Option Bool :=
  Core.Enumeration.quantifiedTruth exact universal body values.toList

/-- `Enum.quantify` over the members of a set or the elements of a
sequence, which are all of its domain's. -/
def Enum.quantifyList {α : Type} (values : List α) (universal : Bool) (body : α → Option Bool) : Option Bool :=
  Enum.quantify values.toArray true universal body

/-- `Enum.quantify` over the integers from `lower` to `upper`, excluded. -/
def Enum.quantifyIntRange (lower upper : Int) (universal : Bool) (body : Int → Option Bool) : Option Bool :=
  -- Too many values leave it unknown, as the `fren` command's evaluator
  -- has it (`Core.Enumeration.maxEnumerated`).
  if upper - lower > Core.Enumeration.maxEnumerated then none else
  Enum.quantify ((List.range (upper - lower).toNat).toArray.map fun (k : Nat) => lower + (k : Int)) true universal body

/-- `Enum.quantifyIntRange` for a `Nat`, from 0 at least. -/
def Enum.quantifyNatRange (lower upper : Int) (universal : Bool) (body : Nat → Option Bool) : Option Bool :=
  -- Counted before the negative values are left out, as by the `fren`
  -- command's evaluator.
  if upper - lower > Core.Enumeration.maxEnumerated then none else
  Enum.quantifyIntRange (max 0 lower) upper universal fun i => body i.toNat

/-- The members of a collection of `Int`s that are naturals, as values of
a name whose values are naturals: a `Nat` may be given where an `Int` is
expected, so `x in s` with `s: Set<Int>` ranges over its members that
are not negative, the others being no values of the name. -/
def Enum.natMembers (xs : List Int) : List Nat := xs.filterMap fun i => if 0 ≤ i then some i.toNat else none

def Enum.notTruth (a : Option Bool) : Option Bool := Core.Enumeration.notTruth a

/-- The strong Kleene disjunction. -/
def Enum.orTruth (a b : Option Bool) : Option Bool := Core.Enumeration.orTruth a b

/-- The strong Kleene conjunction, without evaluating a right side that a
false left side settles. -/
def Enum.andLazy (a : Option Bool) (b : Unit → Option Bool) : Option Bool :=
  if a == some false then some false else Core.Enumeration.andTruth a (b ())

def Enum.orLazy (a : Option Bool) (b : Unit → Option Bool) : Option Bool :=
  if a == some true then some true else Enum.orTruth a (b ())

def Enum.iffLazy (a : Option Bool) (b : Unit → Option Bool) : Option Bool :=
  match a with
  | none => none
  | some x => (b ()).map (x == ·)

/-- A conditional's value: its branch's, or, with its condition unknown,
the value that both branches have, if they have the same, as the `fren`
command's evaluator has it. -/
def Enum.iteValue {α : Type} [DecidableEq α] (c : Option Bool) (yes no : Unit → Option α) : Option α :=
  match c with
  | some true => yes ()
  | some false => no ()
  | none => let a := yes (); if a.isSome && decide (a = no ()) then a else none

/-- `v`, if `k`, and otherwise unknown. -/
def Enum.ifKnown {α : Type} (k : Bool) (v : Option α) : Option α := if k then v else none

/-- Whether two values are the same, unknown if either is. -/
def Enum.sameValue {α : Type} [DecidableEq α] (a b : Option α) : Option Bool :=
  match a, b with
  | some x, some y => some (decide (x = y))
  | _, _ => none

/-- A conditional's truth: its branch's, or, with its condition unknown,
the truth that both branches have, if they have the same. -/
def Enum.iteLazy (c : Option Bool) (yes no : Unit → Option Bool) : Option Bool :=
  match c with
  | some true => yes ()
  | some false => no ()
  | none => let a := yes (); if a.isSome && a == no () then a else none

/-- The compiled functions of one procedure's enumeration, over the slots'
values and an assignment (`Enumerate.enumerateOnly`). They come from one
evaluation, so that they share its environment, and `batch` with them: Lean
interprets each, and a call of one from compiled code starts an
interpreter, whose caches of the symbols and constants that the function
reads start empty, unless an interpreter of the same environment is
running. `batch` runs its argument within one (`Core.Enumeration.Atoms.batch`),
so that each call of the others then runs in it. -/
structure Enum.Compiled where
  truths : Array (Array (Array Core.Enumeration.EVal) → Array Nat → Option Bool)
  atomKnown : Array (Array (Array Core.Enumeration.EVal) → Array Nat → Bool)
  defKnown : Array (Array (Array Core.Enumeration.EVal) → Array Nat → Bool)
  sames : Array (Array (Array Core.Enumeration.EVal) → Array Nat → Array Nat → Option Bool)
  batch : (Unit → Array Nat) → Array Nat
  deriving Inhabited

unsafe def Enum.compileAllUnsafe (e : Expr) : MetaM Enum.Compiled :=
  evalExpr Enum.Compiled (mkConst ``Enum.Compiled) e

/-- The value of `e`, an `Enum.Compiled`, compiled and evaluated. -/
@[implemented_by Enum.compileAllUnsafe]
opaque Enum.compileAll (e : Expr) : MetaM Enum.Compiled

namespace Enumerate

open Core.Enumeration

/-- The declared arguments of a recursive call, excluding the placeholders
and generic dictionaries that the two generated forms take differently. -/
def evaluationInstance (d : DefinedInfo) (e : Expr) : RecInstance × Array Expr :=
  let args := e.getAppArgs
  let name := d.solver?.getD d.decl
  if e.isAppOf d.decl then
    ((name, d.solverTypeArgs.map (args[·]!)), args.extract d.uses.size)
  else ((name, args.extract 0 d.solverTypeArgs.size), args.extract d.solverTypeArgs.size)

/-- Immediate value arguments, excluding Lean's type, instance and proof
arguments. These are representation details, not expression steps. -/
def valueArgs (e : Expr) (recs : Array DefinedInfo := #[]) : MetaM (Array Nat) := do
  let args := e.getAppArgs
  if let some d := recs.find? (fun d => e.isAppOf d.decl || d.solver?.any e.isAppOf) then
    let first := if e.isAppOf d.decl then d.uses.size else d.solverTypeArgs.size
    return (Array.range args.size).filter (· ≥ first)
  let info ← getFunInfoNArgs e.getAppFn args.size
  return (Array.range args.size).filter fun i =>
    match info.paramInfo[i]? with
    | some p => p.binderInfo == .default && !p.isProp
    | none => true

/-- The function table's lookup machinery is not source syntax. Its
indices retain the original arguments, each underneath `Enum.index`. -/
def interpretedArgs? (e : Expr) : Option (Array Expr) := do
  guard (e.isAppOfArity ``Enum.apply 8)
  let (_, indices) ← e.appArg!.arrayLit?
  indices.toArray.mapM fun index => do
    guard (index.isAppOfArity ``Enum.index 4)
    return index.appArg!

/-- Find source operands without traversing a native helper recursively.
A nested match or collection owns its own operands. -/
def sourceOperands (names : Array Name) (root : Expr) : MetaM (Array Expr) :=
  visit maxEvalNodes 1 [root] {} #[]
where
  visit : Nat → Nat → List Expr → Std.HashSet Expr → Array Expr → MetaM (Array Expr)
    | _, _, [], _, found => pure found
    | 0, _, _ :: _, _, _ => throwError "evaluation helper exceeds the expression work limit"
    | fuel + 1, pending, e :: rest, seen, found => do
      let e := e.consumeMData
      if seen.contains e then return ← visit fuel (pending - 1) rest seen found
      let seen := seen.insert e
      if names.any e.isAppOf then return ← visit fuel (pending - 1) rest seen (found.push e)
      if e.isAppOf ``Fren.evalMatch || e.isAppOf ``Fren.evalCollection then
        return ← visit fuel (pending - 1) rest seen found
      let children ← match e with
        | .letE _ _ v b _ => pure #[b.instantiate1 v]
        | .mdata _ b => pure #[b]
        | .app .. => do return (← valueArgs e).map (e.getAppArgs[·]!)
        | _ => pure #[]
      let pending := pending - 1 + children.size
      if pending > fuel then throwError "evaluation helper exceeds the expression work limit"
      visit fuel pending (children.foldr (· :: ·) rest) seen found

/-- The adapter exposes source expression boundaries. In particular native
pattern tests, selectors and literal constructors do not spend extra depth. -/
def expressionLayer (e : Expr) (recs : Array DefinedInfo := #[]) : MetaM (ExpressionLayer Expr) := do
  let e := e.consumeMData
  if let some args := interpretedArgs? e then return { children := args }
  if e.isAppOf ``Enum.pickE || e.isAppOf ``Enum.pick || e.isAppOf ``Fren.Str.lit || e.isAppOf ``Fren.evalBinding then return {}
  if e.isAppOf ``Fren.evalCollection then
    return { children := ← sourceOperands #[``Fren.evalElement] e.appArg! }
  if e.isAppOf ``Fren.evalTest then
    return { children := ← sourceOperands #[``Fren.evalScrutinee, ``Fren.evalGuard] e.appArg!, transparent := true }
  if e.isAppOf ``Fren.evalCase then
    let body := e.appArg!.consumeMData
    return { children := if body.isAppOfArity ``ite 5 then #[body.getArg! 1, body.getArg! 3, body.getArg! 4] else #[body], transparent := true, branching := true }
  if e.isAppOf ``Fren.evalScrutinee then
    return { children := #[e.appArg!], transparent := (e.getArg! 1).nat?.getD 1 ≤ 1 }
  if e.isAppOf ``Fren.evalGuard || e.isAppOf ``Fren.evalElement || e.isAppOf ``Fren.lastArm then
    return { children := #[e.appArg!], transparent := true }
  if e.isAppOf ``Fren.evalKeep || e.isAppOf ``Fren.evalArgument then
    return { children := #[e.getArg! 2, e.appArg!], transparent := true }
  if e.isAppOf ``Fren.evalMatch then return { children := #[e.appArg!], branching := true }
  -- Recursive calls expose their arguments; each body is admitted as a
  -- separate root, as in the command-line lowering. Evaluation still
  -- spends a call step before entering that body.
  if e.isAppOfArity ``Decidable.decide 2 then
    return { children := #[e.getArg! 0], transparent := true }
  if e.isAppOfArity ``Eq 3 && e.getArg! 0 == mkConst ``Bool && e.getArg! 2 == mkConst ``Bool.true then
    return { children := #[e.getArg! 1], transparent := true }
  if e.isAppOfArity ``Fren.typeObligation 2 then
    return { children := #[e.appArg!], transparent := true }
  if e.isAppOfArity ``Int.ofNat 1 && e.appArg!.nat?.isNone then
    return { children := #[e.appArg!], transparent := true }
  if e.isAppOfArity ``ite 5 then return { children := #[e.getArg! 1, e.getArg! 3, e.getArg! 4], branching := true }
  match e with
  | .lam _ _ b _ => return { children := #[b], transparent := true }
  | .forallE _ t b _ =>
    return { children := if t.hasLooseBVars || !(← isProp t) then #[b] else #[t, b], branching := true }
  | .letE _ _ v b _ => return { children := #[b.instantiate1 v], transparent := true }
  | .proj _ _ b => return { children := #[b] }
  | .app .. =>
    if e.isAppOf ``OfNat.ofNat || e.isAppOf ``Int.ofNat || e.isAppOf ``Int.negSucc then return {}
    if e.isAppOfArity ``Not 1 then return { children := #[e.appArg!] }
    if e.isAppOf ``And || e.isAppOf ``Or || e.isAppOf ``Iff then return { children := e.getAppArgs, branching := true }
    return { children := (← valueArgs e recs).map (e.getAppArgs[·]!) }
  | _ => return {}

/-- `base` with the first number after it that names no declaration. -/
partial def freshDeclName (base : Name) (k : Nat := 1) : MetaM Name := do
  let n := base.appendIndexAfter k
  if (← getEnv).contains n then freshDeclName base (k + 1) else return n

/-- The values `vs`, of the type `t`, as an array: in literals of at most
32, each a definition of its own, `base` with a number, joined by
`Array.append` in a balanced tree. One literal of thousands, such as a
slot's values of a struct with a sequence in it, would exceed the
recursion depth of the passes over it, the code generator's among them. -/
partial def tableOf (base : Name) (t : Expr) (vs : List Expr) : MetaM Expr := do
  if vs.length ≤ 32 then
    let n ← freshDeclName base
    let value ← mkArrayLit t vs
    addAndCompile (.defnDecl { name := n, levelParams := [], type := ← inferType value, value
                               hints := .opaque, safety := .safe })
    return mkConst n
  else
    let k := vs.length / 2
    mkAppM ``Array.append #[← tableOf base t (vs.take k), ← tableOf base t (vs.drop k)]

/-- The values `vs`, of the type `t`, as an array: a literal if there are
few, else `tableOf`'s. -/
def mkArrayChunked (base : Name) (t : Expr) (vs : List Expr) : MetaM Expr := do
  if vs.length ≤ 32 then mkArrayLit t vs else tableOf base t vs

/-- `f`, a constant over one universe `{α : Type u}`, applied to the type
`α` and to `x`, as `mkAppM` applies it, at the universe of `α`'s type. -/
def mkApp1Typed (f : Name) (α x : Expr) : MetaM Expr := do
  return mkApp2 (mkConst f [← getDecLevel α]) α x

/-- The value `v` of the Lean type `ty` (`Core.Enumeration.EVal`), the
`k`th value of an abstract type being `k : Nat`. Each application is
built as `mkAppM` builds it, at its arguments' types, but without its
unification, which took most of the time of enumerating a slot of
thousands of values. -/
partial def valueExpr (ty : Expr) (v : EVal) : MetaM Expr := do
  let s ← getState
  match v with
  | .bool b => return mkConst (if b then ``Bool.true else ``Bool.false)
  | .int i => if ty.isConstOf ``Int then intExpr i else return mkNatLit i.toNat
  | .abs k => return mkNatLit k
  | .str t => return mkStrLit t
  | .pair a b =>
    let ts := ty.getAppArgs
    let a ← valueExpr ts[0]! a
    let b ← valueExpr ts[1]! b
    let α ← inferType a
    let β ← inferType b
    return mkApp4 (mkConst ``Prod.mk [← getDecLevel α, ← getDecLevel β]) α β a b
  | .set xs =>
    let elem := (← whnfR ty).getAppArgs[0]!
    mkApp1Typed ``Fren.FinSet.ofList elem (← mkListLit elem (← xs.mapM (valueExpr elem)))
  | .seq xs =>
    let elem := (← whnfR ty).getAppArgs[0]!
    mkApp1Typed ``Fren.Seq.ofList elem (← mkListLit elem (← xs.mapM (valueExpr elem)))
  | .ctor idx args =>
    let ty ← whnfR ty
    let some d := ty.getAppFn.constName? | throwError "not a datatype: {ty}"
    let targs := ty.getAppArgs
    -- A prelude type's constructor is at universe 0 (`EnumInfo.ctorConst`).
    let (c, ts) :=
      if let some e := s.enumOfDecl? d then (e.ctorConst idx, (e.payloadsAt targs)[idx]?.getD #[])
      else if let some r := s.recordOfDecl? d then (mkConst r.ctor, (r.fieldsAt targs).map (·.2))
      else if let some n := s.newtypeOfDecl? d then (mkConst n.ctor, #[n.under])
      else (mkConst .anonymous, #[])
    let as ← (args.toArray.zip ts).mapM fun (w, t) => valueExpr t w
    return mkAppN c (targs ++ as)

/-- `EVal`'s type, and a list of them. -/
def evalTy : Expr := mkConst ``Fren.Core.Enumeration.EVal

/-- How deeply `v`'s constructors nest, which is how often a recursive
type's decoder has to be iterated to read it (`Enum.decFix`). -/
partial def evalDepth : EVal → Nat
  | .ctor _ as => 1 + as.foldl (fun m w => max m (evalDepth w)) 0
  | .pair a b => max (evalDepth a) (evalDepth b)
  | .seq xs | .set xs => xs.foldl (fun m w => max m (evalDepth w)) 0
  | _ => 0

/-- Whether `ty` is within one of the types `seen` that has its head, at
arguments that are not part of that type's own: a type that recurs at
other arguments, as `T<Seq<A>>` within `T<A>`, whose decoders and encoders
would never end. Each type with a head that is within another with the
same head, at a part of its arguments, is smaller than it, so following
them ends. -/
def nonUniform (seen : List Expr) (ty : Expr) : Bool :=
  !ty.getAppFn.isFVar && seen.any fun t =>
    t.getAppFn == ty.getAppFn && t != ty && !(t.getAppArgs.any fun a => (a.find? (· == ty)).isSome)

/-- A decoder of the slot values of the Lean type `ty` (`Enum.pickE`):
an `EVal → ty`, which reads a value as `valueExpr` writes it, or `none` for
a type it cannot read, whose values are then written into the code instead.
A recursive type's decoder is iterated `depth` times (`Enum.decFix`), so
`depth` must be at least how deeply the slot's values nest (`evalDepth`).
`seen` are the types whose decoders are being built, each with the local
that stands for its own decoder within it. -/
partial def decoderOf (ty : Expr) (depth : Nat) (seen : List (Expr × Expr) := []) : MetaM (Option Expr) := do
  let ty ← whnfR ty
  if let some (_, self) := seen.find? fun (t, _) => t == ty then return some self
  -- A type within itself at other arguments that are not part of its own,
  -- as `T<Seq<A>>` within `T<A>`, has no decoder: its values have no one
  -- shape for a decoder to read. One at a part of its own arguments, as
  -- `Box<Wide>` within `Box<Box<Wide>>`, is a smaller type, with a decoder
  -- of its own (`nonUniform`).
  if nonUniform (seen.map (·.1)) ty then return none
  if ty.isConstOf ``Bool then return some (mkConst ``Enum.decBool)
  if ty.isConstOf ``Int then return some (mkConst ``Enum.decInt)
  if ty.isConstOf ``Nat then return some (mkConst ``Enum.decNat)
  if ty.isConstOf ``String then return some (mkConst ``Enum.decStr)
  if ty.isAppOfArity ``Prod 2 then
    let some a ← decoderOf ty.appFn!.appArg! depth seen | return none
    let some b ← decoderOf ty.appArg! depth seen | return none
    return some (← mkAppM ``Enum.decPair #[a, b])
  if ty.isAppOfArity ``Fren.Seq 1 then
    let some a ← decoderOf ty.appArg! depth seen | return none
    return some (← mkAppM ``Enum.decSeq #[a])
  if ty.isAppOfArity ``Fren.FinSet 1 then
    let some a ← decoderOf ty.appArg! depth seen | return none
    return some (← mkAppM ``Enum.decSet #[a])
  let .const I lvls := ty.getAppFn | return none
  let some (.inductInfo ind) := (← getEnv).find? I | return none
  if ind.numIndices != 0 || ind.ctors.isEmpty then return none
  let targs := ty.getAppArgs
  -- Each constructor applied to its fields' decoders of the values `as`,
  -- the last where no earlier one's position is `idx`; a field of `ty`'s
  -- own type by `self`.
  let ctorsDec (self : Expr) : MetaM (Option Expr) := do
    withLocalDeclD `as (← mkAppM ``List #[evalTy]) fun as => withLocalDeclD `idx (mkConst ``Nat) fun idx => do
      let mut apps := #[]
      for c in ind.ctors do
        let some app ← forallTelescope (← inferType (mkAppN (mkConst c lvls) targs)) fun fields _ => do
            let mut vals := #[]
            for f in fields, j in [0:fields.size] do
              let some dec ← decoderOf (← inferType f) depth ((ty, self) :: seen) | return none
              vals := vals.push (mkApp dec (← mkAppM ``Enum.arg #[as, mkNatLit j]))
            return some (mkAppN (mkConst c lvls) (targs ++ vals))
          | return none
        apps := apps.push app
      let mut body := apps.back!
      for k in (List.range (apps.size - 1)).reverse do
        body ← mkAppM ``cond #[← mkAppM ``Nat.beq #[idx, mkNatLit k], apps[k]!, body]
      let f ← mkLambdaFVars #[idx, as] body
      return some (← mkAppM ``Enum.decCtor #[f])
  withLocalDeclD `self (← mkArrow evalTy ty) fun self => do
    let some dec ← ctorsDec self | return none
    -- A type with no field of its own type reads a value by `dec` itself.
    unless dec.containsFVar self.fvarId! do return some dec
    -- A recursive one iterates `dec` from a value of a constructor without
    -- such a field, its fields read from `false` (`Enum.decFix`).
    if depth == 0 then return none
    let mut base? := none
    for c in ind.ctors do
      if base?.isSome then continue
      base? ← forallTelescope (← inferType (mkAppN (mkConst c lvls) targs)) fun fields _ => do
        let mut vals := #[]
        for f in fields do
          let some dec ← decoderOf (← inferType f) 0 seen | return none
          vals := vals.push (mkApp dec (mkApp (mkConst ``Fren.Core.Enumeration.EVal.bool) (mkConst ``Bool.false)))
        return some (mkAppN (mkConst c lvls) (targs ++ vals))
    let some base := base? | return none
    return some (← mkAppM ``Enum.decFix #[base, ← mkLambdaFVars #[self] dec, mkNatLit depth])

/-- An encoder of the values of the Lean type `ty`: a `ty → EVal`, the
inverse of `decoderOf`'s decoder, or `none` for a type it cannot read.
A recursive type's encoder is iterated `Enum.encFuel` times
(`Enum.encFix`). `seen` are the types whose encoders are being built,
each with the local that stands for its own encoder within it. -/
partial def encoderOf (ty : Expr) (seen : List (Expr × Expr) := []) : MetaM (Option Expr) := do
  let ty ← whnfR ty
  if let some (_, self) := seen.find? fun (t, _) => t == ty then return some self
  if nonUniform (seen.map (·.1)) ty then return none
  let lam (body : Expr → MetaM (Option Expr)) : MetaM (Option Expr) := withLocalDeclD `x ty fun x => do
    let some b ← body x | return none
    return some (← mkLambdaFVars #[x] b)
  if ty.isConstOf ``Bool then return ← lam fun x => return some (mkApp (mkConst ``Fren.Core.Enumeration.EVal.bool) x)
  if ty.isConstOf ``Int then return ← lam fun x => return some (mkApp (mkConst ``Fren.Core.Enumeration.EVal.int) x)
  if ty.isConstOf ``Nat then return ← lam fun x => return some (mkApp (mkConst ``Fren.Core.Enumeration.EVal.abs) x)
  if ty.isConstOf ``String then return ← lam fun x => return some (mkApp (mkConst ``Fren.Core.Enumeration.EVal.str) x)
  if ty.isAppOfArity ``Prod 2 then
    let some a ← encoderOf ty.appFn!.appArg! seen | return none
    let some b ← encoderOf ty.appArg! seen | return none
    return ← lam fun x => do
      return some (mkApp2 (mkConst ``Fren.Core.Enumeration.EVal.pair) (mkApp a (← mkAppM ``Prod.fst #[x])) (mkApp b (← mkAppM ``Prod.snd #[x])))
  if ty.isAppOfArity ``Fren.Seq 1 then
    let some a ← encoderOf ty.appArg! seen | return none
    return some (← mkAppM ``Enum.encSeq #[a])
  if ty.isAppOfArity ``Fren.FinSet 1 then
    let some a ← encoderOf ty.appArg! seen | return none
    return some (← mkAppM ``Enum.encSet #[a])
  let .const I lvls := ty.getAppFn | return none
  let some (.inductInfo ind) := (← getEnv).find? I | return none
  if ind.numIndices != 0 || ind.ctors.isEmpty then return none
  let targs := ty.getAppArgs
  let listTy ← mkAppM ``List #[evalTy]
  withLocalDeclD `self (← mkArrow ty evalTy) fun self => do
    -- Each constructor's fields, encoded, by `casesOn`; a field of `ty`'s
    -- own type by `self`.
    let mut minors := #[]
    for c in ind.ctors do
      let some m ← forallTelescope (← inferType (mkAppN (mkConst c lvls) targs)) fun fields _ => do
          let mut encs := #[]
          for f in fields do
            let some enc ← encoderOf (← inferType f) ((ty, self) :: seen) | return none
            encs := encs.push (mkApp enc f)
          return some (← mkLambdaFVars fields (← mkListLit evalTy encs.toList))
        | return none
      minors := minors.push m
    let some enc ← lam fun x => do
        let motive ← withLocalDeclD `_ ty fun y => mkLambdaFVars #[y] listTy
        let fields := mkAppN (mkConst (I ++ `casesOn) (Level.one :: lvls)) (targs ++ #[motive, x] ++ minors)
        let idx ← mkAppM (I ++ `ctorIdx) #[x]
        return some (mkApp2 (mkConst ``Fren.Core.Enumeration.EVal.ctor) idx fields)
      | return none
    -- A type with no field of its own type encodes a value by `enc` itself;
    -- a recursive one iterates it (`Enum.encFix`).
    unless enc.containsFVar self.fvarId! do return some enc
    return some (← mkAppM ``Enum.encFix #[← mkLambdaFVars #[self] enc, mkConst ``Enum.encFuel])

/-- `e` with its integers written as literals: `Int.ofNat n` and
`Int.negSucc n`, as reduction leaves them, become `n` and `-(n + 1)`. -/
def normInts (e : Expr) : MetaM Expr :=
  Lean.Core.transform e (pre := fun x => do
    let n? := fun (y : Expr) => y.rawNatLit? <|> y.nat?
    if x.isAppOfArity ``Int.ofNat 1 then
      if let some n := n? x.appArg! then return .done (← intExpr n)
    if x.isAppOfArity ``Int.negSucc 1 then
      if let some n := n? x.appArg! then return .done (← intExpr (-(n : Int) - 1))
    return .continue)

/-- The Lean type of the hidden slot for the unspecified value of `t`: `t`,
but `Bool` for `Prop`, a table's of propositions, whose values cannot be
compiled or decided, and which is the same slot as `Bool`'s, as the `fren`
command, which has only `Bool`s, has it. -/
def hiddenTy (t : Expr) : Expr := if t.isProp then mkConst ``Bool else t

/-- `e` with `u`, the unspecified value of a type, replaced by `h`
wherever it is written, by any instances; the unspecified value of `Prop`
by `h = true` where `h` is `Bool`'s (`hiddenTy`). -/
def replaceUnspecified (e u h : Expr) : Expr :=
  e.replace fun x =>
    if isUnspecified x && hiddenTy (x.getArg! 0) == hiddenTy (u.getArg! 0) then
      some (if (x.getArg! 0).isProp then mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) h (mkConst ``Bool.true) else h)
    else none

/-- The unspecified values of types that `e` reads, `Fren.Seq.nth ∅ 0`:
each application, once. -/
def unspecifiedIn (e : Expr) : Array Expr := go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    if isUnspecified e then
      if acc.contains e then acc else acc.push e
    else match e with
      | .app f a => go a (go f acc)
      | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b | .proj _ _ b => go b acc
      | _ => acc

/-- Whether `e` has an unbounded quantifier: a `∀` or `∃` over values
rather than propositions, which a quantifier over a listed type is not,
since it is expanded. -/
partial def hasQuantifier (e : Expr) : MetaM Bool := do
  match e with
  | .forallE _ t b _ =>
    if !(← isProp t) then return true
    -- An implication; its body may mention the hypothesis only in a proof.
    hasQuantifier t <||> hasQuantifier (b.instantiate1 (mkConst ``True.intro))
  | .app .. =>
    if e.isAppOf ``Exists then return true
    e.getAppArgs.anyM hasQuantifier <||> hasQuantifier e.getAppFn
  | .lam n t b bi => withLocalDecl n bi t fun x => hasQuantifier (b.instantiate1 x)
  | .letE _ _ v b _ => hasQuantifier v <||> hasQuantifier (b.instantiate1 v)
  | .mdata _ b | .proj _ _ b => hasQuantifier b
  | _ => return false

/-- A guard's node, as both front ends read guards (`Core.guardConjunctsBy`). -/
def typedGuardNode (source : Expr) : Core.GuardNode Expr :=
  let e := source.consumeMData
  let args := e.getAppArgs
  if e.isAppOfArity ``And 2 then .conj args[0]! args[1]!
  -- Membership takes the collection before the member.
  else if (e.isAppOf ``Membership.mem || e.isAppOf ``Fren.FinSet.Mem) && args.size >= 2 then
    .compare #[args[args.size - 1]!, args[args.size - 2]!] #["in"]
  else if e.isAppOf ``LT.lt && args.size >= 2 then .compare #[args[args.size - 2]!, args[args.size - 1]!] #["<"]
  else if e.isAppOf ``LE.le && args.size >= 2 then .compare #[args[args.size - 2]!, args[args.size - 1]!] #["<="]
  else if e.isAppOf ``GT.gt && args.size >= 2 then .compare #[args[args.size - 2]!, args[args.size - 1]!] #[">"]
  else if e.isAppOf ``GE.ge && args.size >= 2 then .compare #[args[args.size - 2]!, args[args.size - 1]!] #[">="]
  else .other

/-- The implications at the top of a universal's body, whose hypotheses
are its guard. -/
partial def leadingGuards (source : Expr) : MetaM (Array Expr) := do
  let e := source.consumeMData
  if let .forallE _ condition body _ := e then
    if !body.hasLooseBVars && (← isProp condition) then return #[e] ++ (← leadingGuards body)
  return #[]

/-- The Fren type that the Lean type `ty` is, as far as a comparison
guard's range needs it, with the constructors of the newtypes that it is,
from the innermost out: `Int` and `Nat` themselves, a pattern type over
them being its base type here, and a newtype the type that its field is,
wrapped back by its constructor. `none` where `ty` names no Fren type.
Whether a comparison bounds such a name is `Core.countedBetween`, which
both front ends ask (`lang::range_domain`). -/
partial def rangeTy? (ty : Expr) : MetaM (Option (Core.Ty × Array Expr)) := do
  if ← isDefEq ty (mkConst ``Nat) then return some (.nat, #[])
  if ← isDefEq ty (mkConst ``Int) then return some (.int, #[])
  if let some n := (← getState).newtypeOf? ty then
    if let some (under, wrap) ← rangeTy? n.under then
      return some (.newtype n.path under, wrap.push (mkAppN (mkConst n.ctor) ty.getAppArgs))
  return (coreTyOf (← getState) ty).map (·, #[])

/-- `e` without the newtype fields, `fields`, that it reads outermost, and
its name, `0`, for each, for `Core.nameAlone`: `m.0` of a newtype `m`, and an
ordering of a newtype, which `orderingTerm` writes as one of its fields,
elaborate alike, to the field's projection of `m`. -/
partial def withoutFields (fields : Array Name) (e : Expr) : Expr × List String :=
  if e.isApp && e.getAppFn.constName?.any fields.contains then
    let (base, fs) := withoutFields fields e.appArg!.consumeMData
    (base, fs ++ ["0"])
  else (e, [])

/-- The domain of the bound local `x`, of a `forall` if `universal`, by its
guard in `body`, as the `fren` command reads it (`lang::guard_domain`):
the members of a collection, or a range of integers. -/
def guardedDomain (universal : Bool) (x body : Expr) : MetaM (Core.GuardDomain × Array (Option (Expr × Bool))) := do
  let leading ← leadingGuards body
  let when? (source : Expr) :=
    let e := source.consumeMData
    if leading.contains e then match e with
      | .forallE _ condition tail _ => some (condition, tail)
      | _ => none
    else none
  let conjuncts := Core.guardConjunctsBy typedGuardNode when? universal body
  -- The fields of the newtypes, whose values are their underlying types'
  -- (`Reqs/Lang/Expressions#newtypes`): an ordering of a newtype compares
  -- them (`orderingTerm`), so a field of the bound name is the name
  -- itself, written alone, as the `fren` command's syntax has it.
  let fields := (← getState).newtypes.foldl (init := (#[] : Array Name)) fun acc _ n => acc.push n.field
  -- The bound name's type, of which `Core.nameAlone` and
  -- `Core.startsAtZero` decide, as the `fren` command asks them.
  let t := ((← rangeTy? (← inferType x)).map (·.1)).getD .bool
  let alone (source : Expr) :=
    let e := source.consumeMData
    let e := if e.isAppOfArity ``Int.ofNat 1 then e.appArg!.consumeMData else e
    let e := if (e.isAppOf ``NatCast.natCast || e.isAppOf ``Nat.cast) && e.getAppArgs[0]?.any (·.isConstOf ``Int) then
      e.appArg!.consumeMData else e
    let (e, fs) := withoutFields fields e
    Core.nameAlone (if e == x then some 0 else none) t fs
  let names (e : Expr) := if e.containsFVar x.fvarId! then [0] else []
  -- A name whose values are naturals ranges from 0, as in the `fren`
  -- command (`Core.startsAtZero`).
  return Core.boundDomain alone names conjuncts 0 (Core.startsAtZero t)

/-- How `partialDecide` evaluates: `values` gives a quantified type's
values up to the bound and whether they are all of its type's; with
`known?`, whether a quantifier-free part's value is known with every
index out of range unknown (`knownOf`), and unknown where it is not. -/
structure PartialEnv where
  values : Expr → MetaM (Array Expr × Bool)
  /-- The prefix of the definitions that hold large domains' values. -/
  base : Name
  known? : Option (Expr → MetaM Expr) := none
  depth : Expr := mkNatLit maxEvalDepth
  compileDepth : Nat := maxEvalDepth
  compileWork? : Option (IO.Ref Nat) := none
  recursiveNames : Array Name := #[]
  recursiveInfos : Array DefinedInfo := #[]
  scrutinees : Array (Expr × Expr) := #[]
  recursiveCall? : Option (Expr → Expr → MetaM (Option Expr)) := none
  /-- Completed depth families, by type instance and strictness. Captured
  locals must still be in scope before an entry can be reused. -/
  recursiveCache? : Option (IO.Ref (Array (RecInstance × Bool × Expr))) := none

/-- Whether native evaluation would enter a structural recursion. -/
def PartialEnv.hasRecursion (env : PartialEnv) (e : Expr) : Bool :=
  (e.find? fun x => env.recursiveNames.any x.isConstOf).isSome

/-- Bound generation of partial evaluator code as well as its execution.
Substituted definitions can share a subtree along exponentially many paths. -/
def PartialEnv.charge (env : PartialEnv) : MetaM Bool := do
  if env.compileDepth == 0 then return false
  let some work := env.compileWork? | return true
  let left ← work.get
  if left == 0 then return false
  work.set (left - 1)
  return true

/-- Compile a budget step, with its remainder available to every child. -/
def PartialEnv.step (env : PartialEnv) (body : PartialEnv → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `remaining (mkConst ``Nat) fun remaining => do
    mkAppM ``Core.Enumeration.atDepth
      #[env.depth, ← mkLambdaFVars #[remaining] (← body { env with depth := remaining, compileDepth := env.compileDepth - 1 })]

/-- A recursion-free native subtree runs only after the shared traversal
has admitted it for this caller's remaining depth. -/
def PartialEnv.native (env : PartialEnv) (e value : Expr) : MetaM Expr := do
  let some height ← expressionDepthM (expressionLayer · env.recursiveInfos) e
    | return ← mkAppOptM ``Option.none #[some (← inferType value)]
  if let some depth := env.depth.nat? then
    if height ≤ boundedEvalDepth depth then return ← mkAppM ``Option.some #[value]
  withLocalDeclD `_ (mkConst ``Unit) fun unit => do
    mkAppM ``Core.Enumeration.atExpressionDepth
      #[mkNatLit height, env.depth, ← mkLambdaFVars #[unit] (← mkAppM ``Option.some #[value])]

/-- `v`, an `Option`, unknown where `env.known?` says that one of `parts`
is not known. -/
def PartialEnv.wrap (env : PartialEnv) (parts : Array Expr) (v : Expr) : MetaM Expr := do
  let some known := env.known? | return v
  let ks ← parts.mapM known
  mkAppM ``Enum.ifKnown #[ks.foldl (fun acc k => mkApp2 (mkConst ``and) acc k) (mkConst ``Bool.true), v]

/-- The truth of a quantifier over the bound local `x`, whose instance's
truth is `fn x`, over its guard's domain, if it has one: unknown, under
`env.known?`, where the domain's bounds are not known. `none` only where
the guard gives no domain, which includes a comparison that does not bound
the name (`Core.countedBetween`). -/
def quantifyGuarded (env : PartialEnv) (universal : Bool) (x body fn : Expr) : MetaM (Option Expr) := do
  let (domain, bounds) ← guardedDomain universal x body
  let ty ← inferType x
  let toInt (e : Expr) : MetaM (Option Expr) := do
    let t ← inferType e
    if t.isConstOf ``Int then return some e
    if t.isConstOf ``Nat then return some (mkApp (mkConst ``Int.ofNat) e)
    return none
  -- A guard that gives a domain that cannot be read here, which well-typed
  -- Fren does not write, leaves the quantifier unknown, as the `fren`
  -- command's evaluator leaves a domain without a value: never its type's
  -- values instead.
  let unknown ← mkAppOptM ``Option.none #[some (mkConst ``Bool)]
  match domain with
  | .members index =>
    let some (collection, _) := bounds[index]?.getD none | return some unknown
    let collectionType ← inferType collection
    let some element := collectionType.getAppArgs[0]? | return some unknown
    let values ← if collectionType.isAppOf ``Fren.FinSet then mkAppM ``Fren.FinSet.toListImpl #[collection]
      else if collectionType.isAppOf ``Fren.Seq then mkAppM ``Fren.Seq.toList #[collection]
      else return some unknown
    -- The members are of the bound name's type, or, where it reads them
    -- through its newtypes' fields `0`, as `m.0 in s` does, of the type
    -- of that field, each wrapped back into the name's type: a newtype's
    -- values are its field's (`lang::name_alone`).
    -- A name whose values are naturals ranges over the members of a
    -- collection of `Int`s that are not negative (`Enum.natMembers`).
    let mut cur := ty
    let mut ctors : Array Expr := #[]
    let mut found := false
    let mut nat := false
    for _ in [0:16] do
      if ← isDefEq element cur then found := true; break
      if (← isDefEq cur (mkConst ``Nat)) && (← isDefEq element (mkConst ``Int)) then
        found := true; nat := true; break
      let some n := (← getState).newtypeOf? cur | break
      ctors := ctors.push (mkAppN (mkConst n.ctor) cur.getAppArgs)
      cur := n.under
    unless found do return some unknown
    let (values, element) ← if nat then pure (← mkAppM ``Enum.natMembers #[values], mkConst ``Nat)
      else pure (values, element)
    let fn ← if ctors.isEmpty then pure fn else
      withLocalDeclD `v element fun v =>
        mkLambdaFVars #[v] (mkApp fn (ctors.foldr (init := v) fun c acc => mkApp c acc))
    return some (← env.wrap #[collection] (← mkAppM ``Enum.quantifyList #[values, toExpr universal, fn]))
  | .range _ hi | .fromZero hi =>
    let lower ← match domain with
      | .range lo _ => do
        let some (value, strict) := bounds[lo]?.getD none | return some unknown
        let some value ← toInt value | return some unknown
        pure (some (value, strict))
      | _ => pure (some (← intExpr 0, false))
    let some (lower, strictLower) := lower | return some unknown
    let some (upper, strictUpper) := bounds[hi]?.getD none | return some unknown
    let some upper ← toInt upper | return some unknown
    let lo ← if strictLower then mkAppM ``HAdd.hAdd #[lower, ← intExpr 1] else pure lower
    let hi ← if strictUpper then pure upper else mkAppM ``HAdd.hAdd #[upper, ← intExpr 1]
    -- A comparison bounds the name only where finitely many values lie
    -- between any two bounds, as both front ends have it
    -- (`lang::range_domain`); where it does not, its guard gives no
    -- range, and the quantifier ranges over its type's values. A pattern
    -- type over `Int` is `Int` here; its pattern is the body's.
    let some (core, wrap) ← rangeTy? ty | return none
    unless Core.countedBetween core do return none
    let nat := Core.startsAtZero core
    -- A newtype's values are its field's, so the range is of those, and
    -- each is wrapped back into the bound name's type.
    let fn ← if wrap.isEmpty then pure fn else
      withLocalDeclD `x (mkConst (if nat then ``Nat else ``Int)) fun i =>
        mkLambdaFVars #[i] (mkApp fn (wrap.foldl (init := i) fun acc c => mkApp c acc))
    if nat then
      return some (← env.wrap #[lower, upper] (← mkAppM ``Enum.quantifyNatRange #[lo, hi, toExpr universal, fn]))
    return some (← env.wrap #[lower, upper] (← mkAppM ``Enum.quantifyIntRange #[lo, hi, toExpr universal, fn]))
  | .unbounded => return none

/-- A value comparison's dictionary may repeat its fields' dictionaries.
Its size is bounded by enumeration's admitted type-work budget rather than
Lean's small default for source-level instance search. -/
def valueComparison (name : Name) (args : Array Expr) : MetaM Expr :=
  withOptions (synthInstance.maxSize.set · maxTypeNodes) (mkAppM name args)

/-- Compact native negations without changing the source tree that the
resource guard measures. Nested decision dictionaries otherwise make a
supported quantifier body exceed the compiler's heartbeat allowance. -/
def nativeDecision (p : Expr) : MetaM Expr := do
  let (negative, base) := strip maxEvalNodes false p
  let value := mkApp2 (mkConst ``Decidable.decide) base (← decidableOf base)
  if negative then mkAppM ``Bool.not #[value] else pure value
where
  strip : Nat → Bool → Expr → Bool × Expr
    | 0, negative, p => (negative, p)
    | fuel + 1, negative, p =>
      let p := p.consumeMData
      if p.isAppOfArity ``Not 1 then strip fuel (!negative) p.appArg! else
      if p.isAppOfArity ``Eq 3 && p.getArg! 0 == mkConst ``Bool && p.getArg! 2 == mkConst ``Bool.true then
        let value := (p.getArg! 1).consumeMData
        if value.isAppOfArity ``Decidable.decide 2 then strip fuel negative (value.getArg! 0)
        else (negative, p)
      else (negative, p)

mutual
/-- The truth of the proposition `p`, an `Option Bool`, `none` where it is
unknown: by the strong Kleene connectives, and each quantifier over its
guard's domain or, without one, over `domain` of its type, which gives
its values up to the bound and whether they are all of its type's. -/
partial def partialDecide (domain : PartialEnv) (p : Expr) : MetaM Expr := do
  unless ← domain.charge do return ← mkAppOptM ``Option.none #[some (mkConst ``Bool)]
  let p := p.consumeMData
  if p.isAppOfArity ``Fren.typeObligation 2 then return ← partialDecide domain p.appArg!
  if p.isAppOfArity ``Eq 3 && p.getArg! 0 == mkConst ``Bool && p.getArg! 2 == mkConst ``Bool.true then
    return ← partialValue domain (p.getArg! 1)
  if let .letE _ _ value body _ := p then return ← partialDecide domain (body.instantiate1 value)
  if p.isAppOf ``Enum.definedValue || p.isAppOf ``Fren.evalCall then return ← domain.step fun child => partialDecide child p.appArg!
  if p.isAppOf ``Fren.evalMatch then return ← domain.step fun child => partialMatch child p.appArg! true
  if p.isAppOf ``Fren.evalCase then
    if p.appArg!.isAppOfArity ``ite 5 then return ← partialDecideAt domain p.appArg!
    return ← partialDecide domain p.appArg!
  if p.isAppOf ``Fren.evalTest then
    return ← partialFree domain (← sourceOperands #[``Fren.evalScrutinee, ``Fren.evalGuard] p.appArg!) p.appArg! fun value => do
      mkAppM ``Option.some #[mkApp2 (mkConst ``Decidable.decide) value (← decidableOf value)]
  if p.isAppOf ``Fren.evalGuard || p.isAppOf ``Fren.evalElement then return ← partialDecide domain p.appArg!
  if p.isAppOf ``Fren.evalBinding then return ← domain.step fun child => do
    partialFree child (← sourceOperands #[``Fren.evalScrutinee] p.appArg!) p.appArg! fun value => do
      mkAppM ``Option.some #[mkApp2 (mkConst ``Decidable.decide) value (← decidableOf value)]
  if p.isAppOf ``Fren.evalKeep then return ← partialDecide domain p.appArg!
  if p.isAppOf ``Fren.evalArgument then
    if domain.known?.isNone then return ← partialDecide domain p.appArg!
    return ← partialFree domain #[p.getArg! 2] p fun _ => partialDecide domain p.appArg!
  if p.isAppOf ``Fren.lastArm then
    return ← partialFree domain #[p.getArg! 2] p fun _ => partialDecide domain p.appArg!
  if p.isAppOf ``Fren.evalScrutinee then
    return ← partialSource domain p
  unless domain.hasRecursion p || (← hasQuantifier p) do
    if nativeAllowed (← expressionInfoM (expressionLayer · domain.recursiveInfos) p) domain.depth.nat? then
      return ← domain.wrap #[p] (← domain.native p (← nativeDecision p))
  domain.step fun child => partialDecideAt child p

partial def partialDecideAt (domain : PartialEnv) (p : Expr) : MetaM Expr := do
  let p := p.consumeMData
  if p.isAppOfArity ``Fren.typeObligation 2 then return ← partialDecide domain p.appArg!
  -- A relation obligation quantifies over its actual pairs. Bounding its
  -- two components independently loses that finite guard when either
  -- component's type has values beyond the enumeration size.
  if p.isAppOfArity ``Fren.relationObligation 1 then
    return ← forallBoundedTelescope p.appArg! (some 2) fun components tail => do
      let .forallE _ guard claim _ := tail | throwError "malformed relation obligation"
      if components.size != 2 || claim.hasLooseBVars then throwError "malformed relation obligation"
      let guard := guard.consumeMData
      let args := guard.getAppArgs
      unless (guard.isAppOf ``Membership.mem || guard.isAppOf ``Fren.FinSet.Mem) && args.size >= 2 do
        throwError "a relation obligation has no membership guard"
      let collection := args[args.size - 2]!
      let member := args[args.size - 1]!
      unless member.isAppOfArity ``Prod.mk 4 && member.getAppArgs[2]! == components[0]! &&
          member.getAppArgs[3]! == components[1]! do
        throwError "a relation obligation has no pair guard"
      withLocalDeclD `pair (← inferType member) fun pair => do
        let first ← mkAppM ``Prod.fst #[pair]
        let second ← mkAppM ``Prod.snd #[pair]
        let claim := claim.replaceFVars components #[first, second]
        let body ← partialDecide domain claim
        let fn ← mkLambdaFVars #[pair] body
        let values ← mkAppM ``Fren.FinSet.toListImpl #[collection]
        domain.wrap #[collection] (← mkAppM ``Enum.quantifyList #[values, toExpr true, fn])
  -- `decide P = true`, or `= false`.
  if p.isAppOfArity ``Eq 3 && p.getAppArgs[0]!.isConstOf ``Bool then
    let value := p.getAppArgs[1]!
    let wanted := p.getAppArgs[2]!
    if value.isAppOfArity ``Decidable.decide 2 && (wanted.isConstOf ``Bool.true || wanted.isConstOf ``Bool.false) then
      let truth ← partialDecide domain value.getAppArgs[0]!
      return ← if wanted.isConstOf ``Bool.true then pure truth else mkAppM ``Enum.notTruth #[truth]
  if let .letE _ _ value body _ := p then return ← partialDecide domain (body.instantiate1 value)
  let thunk (value : Expr) := withLocalDeclD `_ (mkConst ``Unit) fun u => mkLambdaFVars #[u] value
  let combine (name : Name) (a b : Expr) := do
    let value ← partialDecide domain a
    if a == b then
      if name == ``Enum.iffLazy then
        let constant ← withLocalDeclD `_ (mkConst ``Bool) fun x => mkLambdaFVars #[x] (mkConst ``Bool.true)
        return ← mkAppM ``Option.map #[constant, value]
      return value
    mkAppM name #[value, ← thunk (← partialDecide domain b)]
  let quantified (universal : Bool) (x ty body : Expr) : MetaM Expr := do
    let fn ← mkLambdaFVars #[x] (← partialDecide domain body)
    if let some guarded ← quantifyGuarded domain universal x body fn then return guarded
    let (values, exact) ← domain.values ty
    -- A type may have thousands of values: chunked, as the slots' are.
    mkAppM ``Enum.quantify #[← mkArrayChunked domain.base ty values.toList, toExpr exact, toExpr universal, fn]
  match p.getAppFn.constName?, p.getAppArgs with
  | some ``And, #[a, b] => combine ``Enum.andLazy a b
  | some ``Or, #[a, b] => combine ``Enum.orLazy a b
  | some ``Not, #[a] => mkAppM ``Enum.notTruth #[← partialDecide domain a]
  | some ``Iff, #[a, b] => combine ``Enum.iffLazy a b
  | some ``ite, #[_, c, _, yes, no] =>
    mkAppM ``Enum.iteLazy #[← partialDecide domain c, ← thunk (← partialDecide domain yes), ← thunk (← partialDecide domain no)]
  | some ``Exists, #[ty, body] =>
    withLocalDeclD `x ty fun x => quantified false x ty (body.beta #[x])
  | _, _ =>
    if let .forallE name ty body bi := p then
      if ← isProp ty then
        if body.hasLooseBVars then throwError "a proof-dependent implication cannot be evaluated"
        return ← mkAppM ``Enum.orLazy #[← mkAppM ``Enum.notTruth #[← partialDecide domain ty], ← thunk (← partialDecide domain body)]
      return ← withLocalDecl name bi ty fun x => quantified true x ty (body.instantiate1 x)
    -- A quantifier within an argument, as in `n = (if forall ... then 1
    -- else 2)`: the argument's value, if it is known.
    liftArgs domain p fun q => do
      if let some call := domain.recursiveCall? then
        if let some value ← call q domain.depth then return value
      domain.wrap #[q] (← mkAppM ``Option.some #[mkApp2 (mkConst ``Decidable.decide) q (← decidableOf q)])

/-- The value of `e`, which is not a proposition, as an `Option`, `none`
where it is unknown, as the `fren` command's evaluator has it: a
conditional whose condition is unknown has the value that its branches
share, and an application with an unknown argument has none. -/
partial def partialValue (domain : PartialEnv) (e : Expr) : MetaM Expr := do
  unless ← domain.charge do return ← mkAppOptM ``Option.none #[some (← inferType e)]
  let e := e.consumeMData
  if e.isAppOfArity ``Decidable.decide 2 then return ← partialDecide domain e.getAppArgs[0]!
  if let .letE _ _ value body _ := e then return ← partialValue domain (body.instantiate1 value)
  if e.isAppOf ``Enum.definedValue || e.isAppOf ``Fren.evalCall then return ← domain.step fun child => partialValue child e.appArg!
  if e.isAppOf ``Fren.evalMatch then return ← domain.step fun child => partialMatch child e.appArg! false
  if e.isAppOf ``Fren.evalCase then
    if e.appArg!.isAppOfArity ``ite 5 then return ← partialValueAt domain e.appArg!
    return ← partialValue domain e.appArg!
  if e.isAppOf ``Fren.evalCollection then return ← domain.step fun child => do
    partialFree child (← sourceOperands #[``Fren.evalElement] e.appArg!) e.appArg! fun value => mkAppM ``Option.some #[value]
  if e.isAppOf ``Fren.evalElement then return ← partialValue domain e.appArg!
  if e.isAppOf ``Fren.evalBinding then return ← domain.step fun child => do
    partialFree child (← sourceOperands #[``Fren.evalScrutinee] e.appArg!) e.appArg! fun value => mkAppM ``Option.some #[value]
  if e.isAppOf ``Fren.evalKeep then return ← partialValue domain e.appArg!
  if e.isAppOf ``Fren.evalArgument then
    if domain.known?.isNone then return ← partialValue domain e.appArg!
    return ← partialFree domain #[e.getArg! 2] e fun _ => partialValue domain e.appArg!
  if e.isAppOf ``Fren.lastArm then
    return ← partialFree domain #[e.getArg! 2] e fun _ => partialValue domain e.appArg!
  if e.isAppOf ``Fren.evalScrutinee then return ← partialSource domain e
  if e.isAppOfArity ``Int.ofNat 1 && e.appArg!.nat?.isNone then
    return ← mkAppM ``Option.map #[mkConst ``Int.ofNat, ← partialValue domain e.appArg!]
  unless domain.hasRecursion e || (← hasQuantifier e) do
    if nativeAllowed (← expressionInfoM (expressionLayer · domain.recursiveInfos) e) domain.depth.nat? then
      return ← domain.wrap #[e] (← domain.native e e)
  domain.step fun child => partialValueAt child e

partial def partialValueAt (domain : PartialEnv) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let some args := interpretedArgs? e then
    return ← partialFree domain args e fun value => do
      domain.wrap #[value] (← mkAppM ``Option.some #[value])
  if e.isLambda then
    return ← mkAppOptM ``Option.none #[some (← inferType e)]
  if e.isAppOfArity ``Decidable.decide 2 then return ← partialDecide domain e.getAppArgs[0]!
  if let .letE _ _ value body _ := e then return ← partialValue domain (body.instantiate1 value)
  let thunk (value : Expr) := withLocalDeclD `_ (mkConst ``Unit) fun u => mkLambdaFVars #[u] value
  if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    return ← valueComparison ``Enum.iteValue
      #[← partialDecide domain args[1]!, ← thunk (← partialValue domain args[3]!), ← thunk (← partialValue domain args[4]!)]
  liftArgs domain e fun x => do
    if let some call := domain.recursiveCall? then
      if let some value ← call x domain.depth then return value
    domain.wrap #[x] (← mkAppM ``Option.some #[x])

/-- `leaf` of the application `e`, an `Option`, with each of its arguments
evaluated first by `partialValue`, with the remaining depth: `none` if
one is unknown. -/
partial def liftArgs (domain : PartialEnv) (e : Expr) (leaf : Expr → MetaM Expr) : MetaM Expr := do
  let rec go (indices : List Nat) (e : Expr) (known : Array (Expr × Expr)) : MetaM Expr := do
    match indices with
    | [] => leaf e
    | i :: indices =>
      let arg := e.getAppArgs[i]!
      if let some (_, value) := known.find? (·.1 == arg) then
        return ← go indices (mkAppN e.getAppFn (e.getAppArgs.set! i value)) known
      let ty ← inferType arg
      if (← isProp arg) || (← isProp ty) then throwError "a proposition's dependent argument cannot be enumerated: {e}"
      let value ← partialValue domain arg
      withLocalDeclD `v ty fun x => do
        let e' := mkAppN e.getAppFn (e.getAppArgs.set! i x)
        unless ← isTypeCorrect e' do throwError "a dependent argument cannot be enumerated: {e}"
        mkAppM ``Option.bind #[value, ← mkLambdaFVars #[x] (← go indices e' (known.push (arg, x)))]
  go (← valueArgs e domain.recursiveInfos).toList e #[]

/-- A source scrutinee is evaluated at the match's budget. A multiple
scrutinee match has the same extra vector step as the command-line IR. -/
partial def partialSource (domain : PartialEnv) (marker : Expr) : MetaM Expr := do
  let value := marker.appArg!
  let run (domain : PartialEnv) : MetaM Expr := do
    if ← isProp value then partialDecide domain value else partialValue domain value
  if marker.isAppOf ``Fren.evalScrutinee && (marker.getArg! 1).nat?.getD 1 > 1 then
    return ← domain.step run
  run domain

/-- Evaluate source operands, then run native matching or construction on
known values. Native helpers do not consume source expression depth. -/
partial def partialFree (domain : PartialEnv) (parts : Array Expr) (e : Expr)
    (leaf : Expr → MetaM Expr) : MetaM Expr := do
  let rec go (i : Nat) (e : Expr) : MetaM Expr := do
    if h : i < parts.size then
      let part := parts[i]
      let cached := domain.scrutinees.foldl (init := none) fun found (source, value) =>
        if source == part then some value else found
      let value ← match cached with
        | some value => pure value
        | none =>
          if part.isAppOf ``Fren.evalScrutinee then partialSource domain part else
          let source := if part.isAppOf ``Fren.evalGuard || part.isAppOf ``Fren.evalElement then part.appArg! else part
          if ← isProp source then partialDecide domain source else partialValue domain source
      let prop ← isProp part
      let ty ← if prop then pure (mkConst ``Bool) else inferType part
      withLocalDeclD `operand ty fun x => do
        let replacement ← if prop then mkEq x (mkConst ``Bool.true) else pure x
        let next := e.replace fun original => if original.consumeMData == part then some replacement else none
        mkAppM ``Option.bind #[value, ← mkLambdaFVars #[x] (← go (i + 1) next)]
    else leaf e
  go 0 e

/-- Share a match's scrutinees even when unknown, before selecting cases.
Bindings read these cached values rather than recomputing their selectors'
source expression at another depth. -/
partial def partialMatch (domain : PartialEnv) (body : Expr) (proposition : Bool) : MetaM Expr := do
  let sources ← sourceOperands #[``Fren.evalScrutinee] body
  let rec cache (i : Nat) (domain : PartialEnv) : MetaM Expr := do
    if h : i < sources.size then
      let source := sources[i]
      let value ← partialSource domain source
      withLetDecl `scrutinee (← inferType value) value fun cached => do
        let body ← cache (i + 1) { domain with scrutinees := domain.scrutinees.push (source, cached) }
        mkLetFVars #[cached] body
    else if proposition then partialDecide domain body else partialValue domain body
  cache 0 domain

end

/-- Compile the solver body's syntax rather than calling its unrestricted
native recursion. Self calls read strictly smaller entries of Core's depth
family; dependencies are earlier declarations and use the same remainder. -/
partial def boundedRecursiveCall (domain : PartialEnv) (prepare : Expr → MetaM Expr)
    (e remaining : Expr) (fuel : Nat := maxEvalDepth) : MetaM (Option Expr) := do
  if fuel == 0 then
    let ty ← if ← isProp e then pure (mkConst ``Bool) else inferType e
    return some (← mkAppOptM ``Option.none #[some ty])
  let some d := domain.recursiveInfos.find? fun d => e.isAppOf d.decl || d.solver?.any e.isAppOf
    | return none
  let (inst, args) := evaluationInstance d e
  if let some cache := domain.recursiveCache? then
    let lctx ← getLCtx
    for (key, strict, family) in ← cache.get do
      if RecInstance.same key (d.decl, inst.2) && strict == domain.known?.isSome &&
          (family.find? fun x => x.isFVar && !lctx.contains x.fvarId!).isNone then
        return some (mkAppN (mkApp family remaining) args)
  let some body := d.recBody? | throwError "a structural recursion has no body"
  let body ← prepare (d.atRecInstance inst.2 body)
  lambdaTelescope body fun params result => do
    let resultTy ← if ← isProp result then pure (mkConst ``Bool) else inferType result
    let zero ← mkLambdaFVars params (mkApp (mkConst ``Option.none [0]) resultTy)
    if (← expressionDepthM (expressionLayer · domain.recursiveInfos) result).isNone then
      return some (mkAppN zero args)
    let fnTy ← inferType zero
    let familyTy ← mkArrow (mkConst ``Nat) fnTy
    let step ← withLocalDeclD `depth (mkConst ``Nat) fun depth =>
      withLocalDeclD `previous familyTy fun previous => do
        let call (e budget : Expr) : MetaM (Option Expr) := do
          if e.isAppOf d.decl || d.solver?.any e.isAppOf then
            let (other, args) := evaluationInstance d e
            if RecInstance.same (d.decl, inst.2) (d.decl, other.2) then return some (mkAppN (mkApp previous budget) args)
          boundedRecursiveCall domain prepare e budget (fuel - 1)
        let child := { domain with depth, recursiveCall? := some call }
        let value ← if ← isProp result then partialDecide child result else partialValue child result
        let fn ← mkLambdaFVars params value
        mkLambdaFVars #[depth, previous] fn
    let family ← mkAppM ``Core.Enumeration.depthFamily #[zero, step]
    -- Keep repeated dependencies as named functions, so checking the next
    -- caller does not traverse another copy of every dependency's code.
    let family ← mkAuxDefinitionFor (← freshDeclName (domain.base ++ `_recursive)) family
    if let some cache := domain.recursiveCache? then
      cache.modify (·.push ((d.decl, inst.2), domain.known?.isSome, family))
    return some (mkAppN (mkApp family remaining) args)


instance : Inhabited (Array Nat → Option Bool) := ⟨fun _ => none⟩
instance : Inhabited (Array Nat → Bool) := ⟨fun _ => false⟩
instance : Inhabited (Array Nat → Array Nat → Bool) := ⟨fun _ _ => false⟩
instance : Inhabited (Array (Array EVal) → Array Nat → Bool) := ⟨fun _ _ => false⟩
instance : Inhabited (Array (Array EVal) → Array Nat → Option Bool) := ⟨fun _ _ => none⟩
instance : Inhabited (Array (Array EVal) → Array Nat → Array Nat → Bool) := ⟨fun _ _ _ => false⟩
instance : Inhabited (Array (Array EVal) → Array Nat → Array Nat → Option Bool) := ⟨fun _ _ _ => none⟩

/-- What a message about `c`'s checks is about: a global expectation by its
module and name, as the `fren` command shows it. -/
def subjectOf (c : CompInfo) : MetaM String := do
  let global := (← getState).globals.toList.any fun (p, g) => g.decl == c.decl && p != g.path
  return Core.subjectOf c.path global (c.props[0]?.map (·.name))

/-- Enumerates the checks of `c` set to enumeration
(`Reqs/Check#checking-by-enumeration`), as `checkComp`'s hook
(`EnumHook`): `full` is its procedure, over the locals `fvs` of its variables
and `ufs` of the abstract types and functions it uses, of which `fns` are
the functions. -/
def enumerateOnly (c : CompInfo) (full : Core.Comp Expr) (fvs ufs : Array Expr) (fns : Array (Name × Expr × Nat × Bool))
    (kinds : Array CheckKind) (t : Core.Tested) (testing : Bool) : MetaM (Except Core.Msg Enumerated) :=
    withOptions (fun opts => maxRecDepth.set opts (max (maxRecDepth.get opts) (16 * maxEvalDepth))) do
  let st ← getState
  let recInfos := st.defined.toArray.filterMap fun (_, d) => if d.recursive then some d else none
  let subject ← subjectOf c
  let n := c.enumSize
  let (core, ks) := full.only t kinds
  let (ecomp, sourceAtoms) := core.atoms
  -- Enumerated shapes may optimize literal patterns, but are not the
  -- semantic meaning of arbitrary named subset invariants.
  let domains ← (c.vars.zip fvs).filterMapM fun (v, x) => do
    if v.defn?.isSome then return none
    let some predicate := v.fact? | return none
    let fact := (replaceUses c.uses ufs predicate).beta #[x]
    return some (v.role == .output, fact)
  let atoms0 := sourceAtoms ++ domains.map (·.2)
  let facts := domains.zipIdx.map fun (_, i) => EF.atom (sourceAtoms.size + i)
  let outputFacts := domains.zipIdx.filterMap fun ((output, _), i) => if output then some (EF.atom (sourceAtoms.size + i)) else none
  -- Keep source definitions in dependency order. Substitution below
  -- visits them last first, since each mentions only earlier outputs.
  let varFv (x : Name) : Option Expr := (c.vars.findIdx? (·.name == x)).map (fvs[·]!)
  let roots ← match c.evaluationDefs? with
    | some definitions => definitions.mapM fun (d, e) => do
      return (d, (← Lean.Core.betaReduce (replaceUses c.uses ufs e)).beta fvs)
    | none => pure (full.defs.map fun (d, _, e) => (d, e))
  let defined := roots.filterMap fun (d, e) => (varFv d).map (d, ·, e)
  -- Variable definitions keep their lookup boundary; admit each lowered
  -- root before substituting them into its callers.
  for expression in atoms0 ++ defined.map (·.2.2) do
    let expression ← computableDecisions (← unfoldDefined expression (keepRelationObligations := true))
    if (← expressionDepthM (expressionLayer · recInfos) expression).isNone then
      return .error (notEnumerableMsg subject s!"an expression exceeds the evaluator's limit of {maxEvalDepth} levels or {maxEvalNodes} nodes")
  let substDefs (e : Expr) : MetaM Expr := defined.foldrM (init := e) fun (_, fv, de) acc => do
    acc.replaceFVar fv <$> mkAppM ``Enum.definedValue #[de]
  -- Each index reads its element type's unspecified value out of range,
  -- and which atoms, a type's facts too, have one (`Atoms.readsIndex`).
  let atoms ← atoms0.mapM fun a => do readIndexes (← computableDecisions (← unfoldDefined (← substDefs a) (keepRelationObligations := true)))
  let atomIndexed := atoms.map (·.2)
  let atoms := atoms.map (·.1)
  -- And each defined output's definition, which `same` reads, and whose
  -- unspecified values and functions are enumerated as the atoms' are,
  -- as the `fren` command's are.
  let defExprs ← defined.mapM fun (_, fv, _) => do readIndexes (← computableDecisions (← unfoldDefined (← substDefs fv) (keepRelationObligations := true)))
  let defIndexed := defExprs.map (·.2)
  let defExprs := defExprs.map (·.1)
  let scanned := atoms ++ defExprs
  -- The uninterpreted functions that the atoms apply, whose interpretations
  -- are enumerated, but not of one with a contract, which constrains them
  -- (`check::enumerable`).
  -- Nor of a generic function without a body, whose instances are
  -- functions of their own.
  for u in c.uses do
    if scanned.any fun e => (e.find? (·.isConstOf u)).isSome then
      if let some a := st.abstracts.foldl (init := none) fun acc _ a =>
          if a.placeholder == u && !a.typeParams.isEmpty then some a else acc then
        return .error (notEnumerableMsg subject (genericNotEnumerable a.path))
  let abstractOf (u : Name) := st.abstracts.foldl (init := none) fun acc _ a => if a.placeholder == u then some a else acc
  let applied := fns.filterMap fun (u, x, _, _) =>
    if scanned.any (·.containsFVar x.fvarId!) then (abstractOf u).map (·.path) else none
  if let some f := contractBlocker? applied fun f => ((st.contracts.get? f).map (·.posts.size)).getD 0 then
    return .error (notEnumerableMsg subject (contractNotEnumerable f))
  -- Keep absent metadata shallow here. Core expands it under its type
  -- budget; PTy.plain would recurse before admission.
  let mut used : Array (Name × Expr × Bool × FunVar) := #[]
  for (u, x, _, nat) in fns do
    if scanned.any (·.containsFVar x.fvarId!) then
      let some a := abstractOf u | continue
      used := used.push (a.path, x, nat,
        { name := a.path, params := a.ptys.1.map (fun p => ({ ty := p.ty } : Core.PTy)), result := a.ptys.2 })
  if let some f := used.find? (fun f => needsSemanticFilter st.shapeOf f.2.2.2.result) then
    return .error (notEnumerableMsg subject
      s!"the result type of `{Core.showPath f.1}` has a named invariant that cannot be enumerated as an unconstrained function table")
  -- A quantifier ranges over its guard's domain, or its type's values up
  -- to the bound (`Reqs/Check#quantifiers-up-to-the-bound`).
  let quantified := mayBeUnknown (← scanned.mapM hasQuantifier)
  -- Nor of a recursive function whose body indexes a sequence, which Lean
  -- evaluates out of range by its own default, through the recursive
  -- functions it applies.
  let recs := st.defined.foldl (init := #[]) fun acc _ d => if d.recursive then acc.push d else acc
  let mentions (e : Expr) (d : DefinedInfo) : Bool :=
    (e.find? fun x => x.isConstOf d.decl || d.solver?.any x.isConstOf).isSome
  let mut work := recs.filter fun d => scanned.any (mentions · d)
  let mut seen : NameSet := {}
  let mut recIndexed := false
  while !work.isEmpty do
    let d := work.back!
    work := work.pop
    if seen.contains d.decl then continue
    seen := seen.insert d.decl
    if let some b := d.recBody? then
      if (← expressionDepthM (expressionLayer · recInfos) b).isNone then
        return .error (notEnumerableMsg subject s!"an expression exceeds the evaluator's limit of {maxEvalDepth} levels or {maxEvalNodes} nodes")
      if (b.find? fun x => x.isAppOfArity ``Fren.Seq.nth 4 && !isUnspecified x).isSome then recIndexed := true
      work := work ++ recs.filter (mentions b ·)
  if recIndexed then
    return .error (notEnumerableMsg subject recursiveIndexWhy)
  -- The abstract types become `Nat`, and their `Inhabited` instances `Nat`'s.
  let mut absTys : Array (Expr × Name) := #[]
  let mut absInsts : Array Expr := #[]
  for u in ufs do
    let t ← inferType u
    if t.isSort then
      let path := st.abstracts.foldl (init := Name.anonymous) fun acc _ a =>
        if c.uses[ufs.idxOf u]? == some a.placeholder then a.path else acc
      absTys := absTys.push (u, path)
    else if t.isAppOf ``Inhabited then absInsts := absInsts.push u
  let natTy (e : Expr) : Expr :=
    (e.replaceFVars (absTys.map (·.1)) (absTys.map fun _ => mkConst ``Nat)).replaceFVars absInsts
      (absInsts.map fun _ => mkConst ``instInhabitedNat)
  -- The hidden slots: each type whose unspecified value is read.
  let unspec := scanned.foldl (init := #[]) fun acc a =>
    (unspecifiedIn a).foldl (fun acc u =>
      if acc.any (fun v => hiddenTy (v.getArg! 0) == hiddenTy (u.getArg! 0)) then acc else acc.push u) acc
  let ptyOfLean (t : Expr) : Option Core.PTy :=
    match absTys.find? (·.1 == t) with
    | some (_, p) => some { ty := .abstract p }
    | none => (coreTyOf st t).map fun ty => ({ ty } : Core.PTy)
  let mut hidden : Array (Name × Core.PTy) := #[]
  for u in unspec, k in [0:unspec.size] do
    let some pt := ptyOfLean (u.getArg! 0)
      | return .error (notEnumerableMsg subject (notEnumerableWhy none "`?`"))
    hidden := hidden.push (.mkNum `«[][0]» k, pt)
  let vars := c.vars.map fun v =>
    ({ sig := { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
       pty := if v.fact?.isSome then v.ptype else { ty := v.ptype.ty }
       defined := v.defn?.isSome } : SlotVar)
  let (space, values, shapes, fslots) ← match spaceOf st.shapeOf n vars hidden (used.map (·.2.2.2)) (if testing then testCount else 0) (hash c.path) with
    | .ok r => pure r
    | .error (x, why) => return .error (if why == tooManyMarker then tooManyMsg subject (maxBehaviours + 1) n (estimated := true) else notEnumerableMsg subject (notEnumerableWhy x why))
  let determinism := ks.contains .determinism && ecomp.vars.any (·.isDet)
  let count := space.behaviours determinism fslots
  if !withinLimit count then return .error (tooManyMsg subject count n (estimated := fslots.any (·.count > maxBehaviours)))
  -- Each slot's Lean type and values: a variable's, its second copy's, or
  -- an unspecified value's.
  let own := c.vars.filter (·.defn?.isNone)
  let copied := own.filter fun v => (Core.Symbol.ofRole v.role).copied
  let slotTys := own.map (·.type) ++ copied.map (·.type) ++ unspec.map (hiddenTy <| ·.getArg! 0)
  -- The `j`th value of the slot `i`, as a Lean term, built when first
  -- read: a slot of a collection can have tens of thousands of values, of
  -- which the search reads most only through the decoder (`decoderOf`).
  let slotValCache ← IO.mkRef ({} : Std.HashMap (Nat × Nat) Expr)
  let slotVal (i j : Nat) : MetaM (Option Expr) := do
    if let some e := (← slotValCache.get)[(i, j)]? then return some e
    let some t := slotTys[i]? | return none
    let some v := values[i]?.bind (·[j]?) | return none
    let e ← valueExpr (natTy t) v
    slotValCache.modify (·.insert (i, j) e)
    return some e
  let slotSize (i : Nat) : Nat := if i < slotTys.size then (values[i]?.map (·.size)).getD 0 else 0
  let slotVals (i : Nat) : MetaM (Array Expr) :=
    (List.range (slotSize i)).toArray.filterMapM (slotVal i)
  -- The locals that the slots stand for: the variables', then the hidden
  -- slots', which replace the unspecified values.
  withLocalDeclsD (unspec.map fun u => (`u, fun _ => pure (natTy (hiddenTy (u.getArg! 0))))) fun hfvs => do
  let ownFvs := own.map fun v => (varFv v.name).get!
  let slotFvs := ownFvs ++ hfvs
  let slotIdx := (List.range own.size).toArray ++ (List.range hfvs.size).toArray.map (· + own.size + copied.size)
  let tableBase := c.decl ++ `_enum_table
  -- Each function's parameters' and results' values and its tables, once
  -- (`mkArrayChunked`), and as its interpretation in the assignment `env`.
  let funData ← (used.zip fslots).mapM fun ((_, x, nat, _), f) => do
    forallTelescope (natTy (← inferType x)) fun args res => do
      let res := if nat then mkConst ``Int else res
      let ptys ← args.mapM inferType
      let ps ← (ptys.zip f.params).mapM fun (t, vs) => do mkArrayChunked tableBase t (← vs.toList.mapM (valueExpr t))
      let rs ← f.results.toList.mapM (valueExpr res)
      let d ← if let r :: _ := rs then pure r else mkAppOptM ``Inhabited.default #[some res, none]
      let natArr (xs : List Nat) := mkArrayChunked tableBase (mkConst ``Nat) (xs.map mkNatLit)
      return (ps, ← mkArrayChunked tableBase res rs, d, ← natArr f.tables.toList, ← natArr (f.params.map (·.size)).toList)
  let interpreted (env : Expr) : MetaM (Array Expr) := ((used.zip fslots).zip funData).mapM fun (((_, x, nat, _), f), (ps, rs, d, tables, sizes)) => do
    forallTelescope (natTy (← inferType x)) fun args res => do
      let res := if nat then mkConst ``Int else res
      let idx ← (ps.zip args).mapM fun (p, a) => mkAppM ``Enum.index #[p, a]
      let body := mkAppN (mkConst ``Enum.apply) #[res, rs, d, tables, env,
        mkNatLit f.slot, sizes, ← mkArrayLit (mkConst ``Nat) idx.toList]
      mkLambdaFVars args body
  -- Each slot's decoder of its values, which the compiled code reads at run
  -- time from the search's own (`decoderOf`), a recursive type's as deeply
  -- as its values nest; the values of a type that has no decoder are
  -- written into the code instead, once (`mkArrayChunked`).
  let slotDecs ← (slotTys.zip values).mapM fun (t, vs) =>
    decoderOf (natTy t) (vs.foldl (fun m v => max m (evalDepth v)) 0)
  let slotTables ← (slotTys.zip slotDecs).zipIdx.mapM fun ((t, dec?), i) => do
    if dec?.isSome then pure none else some <$> mkArrayChunked tableBase (natTy t) (← slotVals i).toList
  let tablesTy ← mkAppM ``Array #[← mkAppM ``Array #[evalTy]]
  -- `e` over the slots' values `tables` and the assignment `env`, or, if
  -- `at?` gives one, with each slot's value in that assignment written in.
  let overWith (tables env : Expr) (at? : Option (Array Nat)) (e : Expr) : MetaM Expr := do
    let e := unspec.zip hfvs |>.foldl (init := e) fun acc (u, h) => replaceUnspecified acc u h
    let e := (e.replaceFVars (used.map (·.2.1)) (← interpreted env)).headBeta
    let e ← Lean.Core.betaReduce e
    let e := natTy e
    let picks ← slotFvs.zipIdx.mapM fun (_, j) => do
      let i := slotIdx[j]!
      let t := natTy slotTys[i]!
      if let some a := at? then
        if let some v ← slotVal i (a.getD i 0) then return v
      let d : MetaM Expr := do
        if let some v ← slotVal i 0 then pure v else mkAppOptM ``Inhabited.default #[some t, none]
      match slotDecs[i]!, slotTables[i]! with
      | some dec, _ =>
        if slotSize i == 0 then discard d
        mkAppOptM ``Enum.pickE #[some t, some dec, some tables, some env, some (mkNatLit i)]
      | none, some table => return mkApp5 (mkConst ``Enum.pick) t table (← d) env (mkNatLit i)
      | none, none => d
    let e ← computableDecisions (e.replaceFVars slotFvs picks)
    -- Boolean definitions can carry elaboration-time classical decisions.
    -- Rebuild those decisions after substituting the finite interpretation,
    -- including decisions nested inside values compared by an outer atom.
    Meta.transform e (post := fun x => do
      if x.isAppOfArity ``Decidable.decide 2 then
        let p := x.getAppArgs[0]!
        -- A quantified one is evaluated by `partialDecide` instead.
        if ← hasQuantifier p then return .done x
        return .done (mkApp2 (mkConst ``Decidable.decide) p (← decidableOf p))
      return .done x)
  let arrNat := mkApp (mkConst ``Array [0]) (mkConst ``Nat)
  let decideOf (p : Expr) : MetaM Expr := do
    return mkApp2 (mkConst ``Decidable.decide) p (← decidableOf p)
  try
    -- Each compiled function takes the slots' values first, which are the
    -- search's own, applied once.
    let fn1 (body : Expr → Expr → MetaM Expr) : MetaM Expr :=
      withLocalDeclD `tables tablesTy fun tables => withLocalDeclD `env arrNat fun env => do
        mkLambdaFVars #[tables, env] (← body tables env)
    let fnTy ← mkArrow tablesTy (← mkArrow arrNat (mkConst ``Bool))
    -- The values of a quantified type up to the bound, and whether they
    -- are all of its values; one with too many is an error.
    let domainError ← IO.mkRef (none : Option Core.Msg)
    let domainValues (ty : Expr) : MetaM (Array Expr × Bool) := do
      let some pt := ptyOfLean ty | throwError "a quantified type has no declared counterpart: {ty}"
      match Core.Enumeration.shapeOf st.shapeOf n pt with
      | .ok shape =>
        if shape.estimate n > maxBehaviours then
          domainError.set (some (quantifiedTooManyMsg subject n))
          return (#[], false)
        return (← (shape.ordered n).toArray.mapM fun (v, _) => valueExpr ty v, shape.exhausted n)
      | .error why =>
        domainError.set (some (notEnumerableMsg subject (notEnumerableWhy none why)))
        return (#[], false)
    let compileWork ← IO.mkRef maxEvalNodes
    let recursiveCache ← IO.mkRef #[]
    let domain : PartialEnv := {
      values := domainValues
      base := c.decl ++ `_enum_domain
      compileWork? := some compileWork
      recursiveCache? := some recursiveCache }
    -- The same, with every index out of range unknown, as `knownOf` has
    -- it of what has no quantifier.
    let strictDomain : PartialEnv := { domain with known? := some (knownOf decideOf) }
    let recNames := st.defined.toArray.flatMap fun (_, d) =>
      if d.recursive then #[d.decl] ++ d.solver?.toArray else #[]
    let resourceDomain (base : PartialEnv) (tables env : Expr) : PartialEnv :=
      let base := { base with recursiveNames := recNames, recursiveInfos := recInfos }
      { base with recursiveCall? := some (boundedRecursiveCall base fun body => do
          overWith tables env none (← computableDecisions (replaceUses c.uses ufs body))) }
    -- An atom's truth, three-valued, over the slots' values and the
    -- assignment.
    let optionBool := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
    let truthTy ← mkArrow tablesTy (← mkArrow arrNat optionBool)
    let evalFns ← atoms.mapM fun a => fn1 fun tables env => do
      let e ← overWith tables env none a
      partialDecide (resourceDomain domain tables env) e
    if let some msg ← domainError.get then return .error msg
    -- Whether each atom, and each defined output, that has an index is
    -- unknown in an assignment with the indexes out of range unknown, but
    -- known as the search reads them: with a quantifier, as the `fren`
    -- command evaluates it, through each instance.
    let knownFn (e : Expr) : MetaM Expr := fn1 fun tables env => do
      let x ← overWith tables env none e
      unless (resourceDomain domain tables env).hasRecursion x || (← hasQuantifier x) do return ← overWith tables env none (← knownOf decideOf e)
      let strictDomain := resourceDomain strictDomain tables env
      let domain := resourceDomain domain tables env
      let (strict, normal) ← if ← isProp x then pure (← partialDecide strictDomain x, ← partialDecide domain x)
        else pure (← partialValue strictDomain x, ← partialValue domain x)
      return mkApp2 (mkConst ``or) (← mkAppM ``Option.isSome #[strict])
        (mkApp (mkConst ``not) (← mkAppM ``Option.isSome #[normal]))
    let atomKnownFns ← (atoms.zip atomIndexed).filterMapM fun (a, i) => if i then some <$> knownFn a else pure none
    let atomKnownAt := (atomIndexed.foldl (init := (#[], 0)) fun (acc, j) i =>
      if i then (acc.push (some j), j + 1) else (acc.push none, j)).1
    let defKnownFns ← (defExprs.zip defIndexed).filterMapM fun (d, i) => if i then some <$> knownFn d else pure none
    let defKnownAt := (defIndexed.foldl (init := (#[], 0)) fun (acc, j) i =>
      if i then (acc.push (some j), j + 1) else (acc.push none, j)).1
    -- Whether a defined output is the same in two assignments, unknown
    -- where a quantifier leaves its value unknown in either.
    let sameFns ← defExprs.mapM fun de => withLocalDeclD `tables tablesTy fun tables =>
      withLocalDeclD `e₁ arrNat fun e₁ => withLocalDeclD `e₂ arrNat fun e₂ => do
        let a ← overWith tables e₁ none de
        let b ← overWith tables e₂ none de
        let da := resourceDomain domain tables e₁
        let db := resourceDomain domain tables e₂
        mkLambdaFVars #[tables, e₁, e₂] (← if ← isProp a then do
            mkAppM ``Enum.iffLazy #[← partialDecide da a,
              ← withLocalDeclD `_ (mkConst ``Unit) fun u => do mkLambdaFVars #[u] (← partialDecide db b)]
          else valueComparison ``Enum.sameValue #[← partialValue da a, ← partialValue db b])
    if let some msg ← domainError.get then return .error msg
    -- Only syntactically unconditional `some` callbacks certify totality;
    -- a depth check, lookup or recursive call keeps the partial backend.
    let total ← (evalFns ++ sameFns).allM fun fn =>
      lambdaTelescope fn fun _ body => return body.isAppOf ``Option.some
    let sameTy ← mkArrow tablesTy (← mkArrow arrNat (← mkArrow arrNat optionBool))
    -- Compiled at once, with `batch` (`Enum.Compiled`).
    let batchFn ← withLocalDeclD `f (← mkArrow (mkConst ``Unit) arrNat) fun f =>
      mkLambdaFVars #[f] (mkApp f (mkConst ``Unit.unit))
    let compiled ← Enum.compileAll (mkAppN (mkConst ``Enum.Compiled.mk)
      #[← mkArrayLit truthTy evalFns.toList, ← mkArrayLit fnTy atomKnownFns.toList,
        ← mkArrayLit fnTy defKnownFns.toList, ← mkArrayLit sameTy sameFns.toList, batchFn])
    let evals := compiled.truths.map (· values)
    let atomKnown := compiled.atomKnown.map (· values)
    let defKnown := compiled.defKnown.map (· values)
    let sames := compiled.sames.map (· values)
    -- What each atom reads: the slots of the locals it mentions, and the
    -- defined outputs it mentions.
    let slotsOf (a : Expr) : Array Nat :=
      let a := unspec.zip hfvs |>.foldl (init := a) fun acc (u, h) => replaceUnspecified acc u h
      (slotFvs.zipIdx.filter fun (x, _) => a.containsFVar x.fvarId!).map (fun (_, j) => slotIdx[j]!)
        ++ (used.zip fslots).filterMap fun ((_, x, _, _), f) => if a.containsFVar x.fvarId! then some f.slot else none
    let atomSlots := atoms.map slotsOf
    let atomDefs := atoms0.map fun a => defined.filterMap fun (d, fv, _) => if a.containsFVar fv.fvarId! then some d else none
    -- `eval`, `known` and `truth?` from one evaluation (`Atoms.ofTruth`).
    let ats : Atoms := { Atoms.ofTruth atomSlots fun k env => evals[k]! env with
      defs := atomDefs
      unknownReason := if quantified then undecidedQuantifierReason else
        Core.evaluationDepthReason maxEvalDepth
      batch := compiled.batch
      total := total
      sameDefined := fun d e₁ e₂ => match defined.findIdx? (·.1 == d) with
        | some i => sames[i]! e₁ e₂ == some true
        | none => true
      sameKnown := fun d e₁ e₂ => match defined.findIdx? (·.1 == d) with
        | some i => (sames[i]! e₁ e₂).isSome
        | none => true
      defSlots := fun d => match defined.findIdx? (·.1 == d) with
        | some i => slotsOf defExprs[i]!
        | none => #[]
      readsIndex := fun k => atomIndexed[k]!
      defReadsIndex := fun d => match defined.findIdx? (·.1 == d) with
        | some i => defIndexed[i]!
        | none => false
      unknown := fun k env => match atomKnownAt[k]?.join with
        | some j => !atomKnown[j]! env
        | none => false
      defUnknown := fun d env => match (defined.findIdx? (·.1 == d)).bind (defKnownAt[·]?.join) with
        | some j => !defKnown[j]! env
        | none => false }
    let varTy (x : Name) : Expr :=
      let base := (Fren.Core.unprimed? x).getD x
      ((c.vars.find? (·.name == base)).map (·.type)).getD (mkConst ``Bool)
    let renderSlot (s j : Nat) : MetaM String := do
      let some v ← slotVal s j | return "?"
      Fren.render slotTys[s]! v
    -- A defined output's value in `env`: its definition, over the
    -- assignment, with the functions' interpretations and the unspecified
    -- values, read back to a value of its type.
    let defValue (d : Name) (env : Array Nat) : MetaM (Option String) := do
      let some i := defined.findIdx? (·.1 == d) | return none
      let envE ← mkArrayLit (mkConst ``Nat) (env.toList.map mkNatLit)
      -- Its value, with the slots' values in `env` written in, evaluated to
      -- an `EVal` and shown as a slot's value is (`encoderOf`).
      let v ← overWith (← mkArrayLit (← mkAppM ``Array #[evalTy]) []) envE (some env) defExprs[i]!
      let ty := natTy (varTy d)
      if let some enc ← encoderOf ty then
        if let some ev := (← try compileValues EVal evalTy #[mkApp enc v] catch _ => pure #[])[0]? then
          if !Enum.hasUnread ev then return some (← Fren.render (varTy d) (← valueExpr ty ev))
      -- A recursive type's: reduced, each closed string, integer and `Bool`
      -- within it evaluated first, which reduction would leave as bytes or
      -- reach only through a deep recursion.
      let v ← Meta.transform v (pre := fun x => do
        if x.hasFVar || x.hasMVar || x matches .lit _ then return .continue
        let t ← inferType x
        if t.isConstOf ``String then
          let some str := (← try compileValues String (mkConst ``String) #[x] catch _ => pure #[])[0]?
            | return .continue
          return .done (mkStrLit str)
        if t.isConstOf ``Int && !(x.int?.isSome) then
          let some k := (← try compileValues Int (mkConst ``Int) #[x] catch _ => pure #[])[0]?
            | return .continue
          return .done (← intExpr k)
        if t.isConstOf ``Bool && !(x.isConstOf ``Bool.true || x.isConstOf ``Bool.false) then
          let some b := (← try compileValues Bool (mkConst ``Bool) #[x] catch _ => pure #[])[0]?
            | return .continue
          return .done (mkConst (if b then ``Bool.true else ``Bool.false))
        return .continue)
      -- With a quantifier, its value is known only if every quantifier
      -- that it reads is decided, as the `fren` command shows it.
      let v ← if !(← hasQuantifier v) then pure v else do
        let known ← if ← isProp v then partialDecide domain v else partialValue domain v
        let known ← withTransparency .all <| Meta.reduce known
        let known := known.consumeMData
        unless known.isAppOfArity ``Option.some 2 do return none
        pure known.appArg!
      let v ← withTransparency .all <| Meta.reduce v
      return some (← Fren.render (varTy d) (← normInts v))
    -- The variant of each value of a slot whose type is an enumeration,
    -- as the solver's backend names it.
    let enumVals ← slotTys.zipIdx.mapM fun (t, i) => do
      if (st.enumOf? t).isSome then some <$> slotVals i else pure none
    let variantOf (s j : Nat) : Option Core.Variant := do
      let v ← enumVals[s]?.join.bind (·[j]?)
      let e ← st.enumOf? (slotTys[s]?.getD (mkConst ``Bool))
      let .const c _ := v.getAppFn | none
      let idx ← e.ctorIdx? c
      return { name := s!"{e.path.getString!}::{e.variants[idx]!}", arity := (e.payloads[idx]?.map (·.size)).getD 0 }
    let ecomp := { ecomp with typesInterpreted := ecomp.typesInterpreted || !used.isEmpty || !unspec.isEmpty }
    let raw ← Core.checkComp (fun _ => backend space ats renderSlot defValue (if testing then some (hash c.path) else none)
      variantOf facts outputFacts) ecomp ks
    let exact := exhaustedAll shapes n (List.range space.names.size).toArray && fslots.all (·.exhausted)
    let outputsExact := exhaustedAll shapes n space.outputs
    return .ok { results := raw.map (classify n exact outputsExact (indexed := atomIndexed.any id)), bound := n, exact }
  catch ex =>
    return .error (failureMsg s!"enumerating {subject}" (← (← addMessageContext ex.toMessageData).toString) ex.isRuntime)

/-- Enumerates the checks of `c` set to enumeration
(`Reqs/Check#checking-by-enumeration`), as `checkComp`'s hook
(`EnumHook`), those also set to testing tested beyond the bound too
(`Reqs/Check#enumeration-then-testing`), as the `fren` command does. -/
def enumerate (c : CompInfo) (full : Core.Comp Expr) (fvs ufs : Array Expr) (fns : Array (Name × Expr × Nat × Bool))
    (kinds : Array CheckKind) : MetaM (Except Core.Msg Enumerated) := do
  let run (t : Core.Tested) (testing : Bool) : MetaM (Except Core.Msg (Option Enumerated)) := do
    if !t.any then return .ok none
    -- Every failure of this procedure's enumeration is its own error, a
    -- recursion depth or a heartbeat limit among them, which a plain
    -- `catch` lets through: those would drop the verdicts of every
    -- procedure after it in the file (`tryCatchRuntimeEx`).
    tryCatchRuntimeEx (do return (← enumerateOnly c full fvs ufs fns kinds t testing).map some)
      fun ex => do
        return .error (failureMsg s!"enumerating {← subjectOf c}"
          (← (← addMessageContext ex.toMessageData).toString) ex.isRuntime)
  match ← run (c.enumerated.minus c.tested) false with
  | .error m => return .error m
  | .ok a =>
  match ← run (c.enumerated.inter c.tested) true with
  | .error m => return .error m
  | .ok b =>
  return .ok (Enumerated.merge c.enumSize a b c.enumerated.covers)

end Enumerate

end Fren
