-- keep-sorted start
import Fren.Check
import Fren.Elab.TypeTerms
import Fren.PartialEval
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
  let ty := ty.consumeMData
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
    let (c, ts) ←
      if let some e := s.enumOfDecl? d then do
        pure (e.ctorConst idx, (← e.payloadsAt targs)[idx]?.getD #[])
      else if let some r := s.recordOfDecl? d then do
        pure (mkConst r.ctor, (← r.fieldsAt targs).map (·.2))
      else if let some n := s.newtypeOfDecl? d then pure (mkConst n.ctor, #[n.under])
      else pure (mkConst .anonymous, #[])
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
    (kinds : Array CheckKind) (t : Core.Tested) (testing : Bool) : MetaM (Except Core.Msg Enumerated) := do
  let st ← getState
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
  -- The defined outputs, by their definitions, the last first, since each
  -- mentions only earlier ones.
  let varFv (x : Name) : Option Expr := (c.vars.findIdx? (·.name == x)).map (fvs[·]!)
  let defined := full.defs.filterMap fun (d, _, e) => (varFv d).map (d, ·, e)
  let substDefs (e : Expr) : Expr := defined.foldr (init := e) fun (_, fv, de) acc => acc.replaceFVar fv de
  -- Each index reads its element type's unspecified value out of range,
  -- and which atoms, a type's facts too, have one (`Atoms.readsIndex`).
  let atoms ← atoms0.mapM fun a => do readIndexes (← specializeRecursions (← computableDecisions (← unfoldDefined (substDefs a) (keepRelationObligations := true))))
  let atomIndexed := atoms.map (·.2)
  let atoms := atoms.map (·.1)
  -- And each defined output's definition, which `same` reads, and whose
  -- unspecified values and functions are enumerated as the atoms' are,
  -- as the `fren` command's are.
  let defExprs ← defined.mapM fun (_, fv, _) => do readIndexes (← specializeRecursions (← computableDecisions (← unfoldDefined (substDefs fv) (keepRelationObligations := true))))
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
  let mut used : Array (Name × Expr × Bool × FunVar) := #[]
  for (u, x, _, nat) in fns do
    if scanned.any (·.containsFVar x.fvarId!) then
      let some a := abstractOf u | continue
      used := used.push (a.path, x, nat,
        { name := a.path, params := a.ptys.1.map (Core.PTy.plain ·.ty), result := a.ptys.2 })
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
    let t := t.consumeMData
    match absTys.find? (·.1 == t) with
    | some (_, p) => some (Core.PTy.plain (.abstract p))
    | none => (coreTyOf st t).map Core.PTy.plain
  let mut hidden : Array (Name × Core.PTy) := #[]
  for u in unspec, k in [0:unspec.size] do
    let some pt := ptyOfLean (u.getArg! 0)
      | return .error (notEnumerableMsg subject (notEnumerableWhy none "`?`"))
    hidden := hidden.push (.mkNum `«[][0]» k, pt)
  let vars := c.vars.map fun v =>
    ({ sig := { name := v.name, role := v.role, isPub := v.isPub, isDet := v.isDet }
       pty := if v.fact?.isSome then v.ptype else Core.PTy.plain v.ptype.ty
       defined := v.defn?.isSome } : SlotVar)
  let (space, values, shapes, fslots) ← match spaceOf st.shapeOf n vars hidden (used.map (·.2.2.2)) (if testing then testCount else 0) (hash c.path) with
    | .ok r => pure r
    | .error (x, why) => return .error (if why == tooManyMarker then tooManyMsg subject (maxBehaviours + 1) n (estimated := true) else notEnumerableMsg subject (notEnumerableWhy x why))
  let determinism := ks.contains .determinism && ecomp.vars.any (·.isDet)
  let count := space.behaviours determinism fslots
  if !withinLimit count then return .error (tooManyMsg subject count n)
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
    let e := e.replaceFVars slotFvs picks
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
    let domain : PartialEnv := { values := domainValues, base := c.decl ++ `_enum_domain }
    -- The same, with every index out of range unknown, as `knownOf` has
    -- it of what has no quantifier.
    let strictDomain : PartialEnv := { domain with known? := some (knownOf decideOf) }
    -- An atom's truth, three-valued, over the slots' values and the
    -- assignment.
    let optionBool := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
    let truthTy ← mkArrow tablesTy (← mkArrow arrNat optionBool)
    let evalFns ← atoms.mapM fun a => fn1 fun tables env => do
      let e ← overWith tables env none a
      if ← hasQuantifier e then partialDecide domain e else mkAppM ``Option.some #[← decideOf e]
    if let some msg ← domainError.get then return .error msg
    -- Whether each atom, and each defined output, that has an index is
    -- unknown in an assignment with the indexes out of range unknown, but
    -- known as the search reads them: with a quantifier, as the `fren`
    -- command evaluates it, through each instance.
    let knownFn (e : Expr) : MetaM Expr := fn1 fun tables env => do
      let x ← overWith tables env none e
      unless ← hasQuantifier x do return ← overWith tables env none (← knownOf decideOf e)
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
    let sameFns ← defined.mapM fun (_, _, de) => withLocalDeclD `tables tablesTy fun tables =>
      withLocalDeclD `e₁ arrNat fun e₁ => withLocalDeclD `e₂ arrNat fun e₂ => do
        let (de, _) ← readIndexes (← unfoldDefined de (keepRelationObligations := true))
        let a ← overWith tables e₁ none de
        let b ← overWith tables e₂ none de
        mkLambdaFVars #[tables, e₁, e₂] (← if !(← hasQuantifier a) then mkAppM ``Option.some #[← decideOf (← mkEq a b)]
          else if ← isProp a then do
            mkAppM ``Enum.iffLazy #[← partialDecide domain a,
              ← withLocalDeclD `_ (mkConst ``Unit) fun u => do mkLambdaFVars #[u] (← partialDecide domain b)]
          else mkAppM ``Enum.sameValue #[← partialValue domain a, ← partialValue domain b])
    if let some msg ← domainError.get then return .error msg
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
      batch := compiled.batch
      total := !quantified
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
