-- keep-sorted start
import Fren.Model
import FrenCore.Check
import FrenCore.Enumeration
import FrenCore.Names
-- keep-sorted end

/-!
# Values known with every index out of range unknown

What the Lean-hosted front end knows of a formula's value where an index
may be out of range, as the `fren` command's evaluator has it
(`Interp.outOfRange`): enumeration's search reads each index out of range
as the unspecified value of its type (`Fren.Enumerate`), and the
confirmation of a model (`Fren.confirmModel`) reads it as unknown.
-/

open Lean Meta

namespace Fren

/-- `q[i]`, or `d` out of range: an index as enumeration reads it, `d`
being the unspecified value of `α`, `Fren.Seq.nth ∅ 0`, which its hidden
slot's replaces, so that every index out of range is `[][0]`, as the `fren`
command's `Interp.outOfRange` makes it (`Reqs/Check#searching`). -/
def Enum.nthOr.{u} {α : Type u} [Inhabited α] (q : Seq α) (i : Int) (d : α) : α :=
  if 0 ≤ i ∧ i < q.len then q.nth i else d

/-- The integer that `e` is, as the solver or `toExpr` writes one. -/
def intValue? (e : Expr) : Option Int :=
  e.int? <|> e.nat?.map Int.ofNat <|> e.rawNatLit?.map Int.ofNat <|> match_expr e with
    | Int.ofNat n => n.rawNatLit? <|> n.nat? |>.map Int.ofNat
    | Int.negSucc n => (n.rawNatLit? <|> n.nat?).map fun k => -((k : Int) + 1)
    | _ => none

namespace Enumerate

/-- The integer `i` as a literal, as Lean writes it. -/
def intExpr (i : Int) : MetaM Expr :=
  -- `mkIntLit` is the literal that `mkNumeral` and `Neg.neg` make, without
  -- synthesizing their instances.
  return mkIntLit i

/-- Whether `e` is the unspecified value of a type, `Fren.Seq.nth ∅ 0`:
not another index of `∅`, which is another point of the unknown function. -/
def isUnspecified (e : Expr) : Bool :=
  e.isAppOfArity ``Fren.Seq.nth 4 && (e.getArg! 2).isAppOf ``EmptyCollection.emptyCollection
    && (e.getArg! 3).int? == some 0

/-- `e` with each index `Fren.Seq.nth q i` read as `Enum.nthOr q i (Fren.Seq.nth ∅ 0)`,
whose value out of range is its element type's unspecified value, and
whether it has one; with `unspecified`, that value too, an index of the
empty sequence, which a table or `match` where no row or arm is taken
reads (`Reqs/Generated#matches`). -/
def readIndexes (e : Expr) (unspecified := false) : MetaM (Expr × Bool) := do
  let found ← IO.mkRef false
  let e ← Meta.transform e (post := fun x => do
    unless x.isAppOfArity ``Fren.Seq.nth 4 && (unspecified || !isUnspecified x) do return .done x
    found.set true
    let .const _ lvls := x.getAppFn | return .done x
    let #[α, inst, q, i] := x.getAppArgs | return .done x
    -- A proposition where no row or arm is taken, which has no decision:
    -- as `Bool`'s, which does, and is unknown alike.
    if unspecified && α.isProp && isUnspecified x then
      let bool := mkConst ``Bool
      let emptyB ← mkAppOptM ``EmptyCollection.emptyCollection #[some (mkApp (mkConst ``Fren.Seq [0]) bool), none]
      let instB := mkConst ``instInhabitedBool
      let unspecB := mkApp4 (mkConst ``Fren.Seq.nth [0]) bool instB emptyB (← mkNumeral (mkConst ``Int) 0)
      let read := mkAppN (mkConst ``Fren.Enum.nthOr [0]) #[bool, instB, emptyB, ← mkNumeral (mkConst ``Int) 0, unspecB]
      return .done (mkApp3 (mkConst ``Eq [1]) bool read (mkConst ``Bool.true))
    let empty ← mkAppOptM ``EmptyCollection.emptyCollection #[some (mkApp (mkConst ``Fren.Seq lvls) α), none]
    let unspec := mkApp4 (mkConst ``Fren.Seq.nth lvls) α inst empty (← mkNumeral (mkConst ``Int) 0)
    return .done (mkAppN (mkConst ``Fren.Enum.nthOr lvls) #[α, inst, q, i, unspec]))
  return (e, ← found.get)

/-- Whether `e` has an index as enumeration reads it (`Enum.nthOr`). -/
def hasIndex (e : Expr) : Bool := (e.find? (·.isAppOfArity ``Fren.Enum.nthOr 5)).isSome

/-- `e` without the casts from `Nat` to `Int` around it, which the `fren`
command, whose expressions are untyped, does not have. -/
partial def uncast (e : Expr) : Expr :=
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Nat.cast, #[_, _, x] | some ``NatCast.natCast, #[_, _, x] => uncast x
  | some ``Int.ofNat, #[x] => if (intValue? e).isSome then e else uncast x
  | _, _ => e

/-- The integer literal or constant that `e` is, at `Int` or `Nat`, through
casts (`uncast`). -/
def countLit? (e : Expr) : Option Int := intValue? (uncast e)

/-- `e` with each value of a newtype read as its underlying value, through
newtypes of newtypes, as the `fren` command, which erases newtypes, reads it:
the newtype's field of its constructor, `(Ms.mk x).0`, is `x`, and of an
`if`, `(if c then a else b).0`, is `if c then a.0 else b.0`. The Lean-hosted
front end writes a newtype's arithmetic and comparisons over these fields. -/
partial def unwrapNewtypes (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  let st ← getState
  let .const f _ := e.getAppFn | return ← e.withApp fun fn args => return mkAppN fn (← args.mapM unwrapNewtypes)
  let args := e.getAppArgs
  if let some info ← getProjectionFnInfo? f then
    if args.size == info.numParams + 1 then
      if let some n := st.newtypeOfDecl? info.ctorName.getPrefix then
        -- The field's argument read first, so that a newtype of a newtype,
        -- `(Mm.mk (Ms.mk x)).0.0`, is read to `x`, through any depth.
        let x ← unwrapNewtypes args.back!.consumeMData
        if x.isAppOf info.ctorName then return ← unwrapNewtypes x.appArg!
        if x.isAppOfArity ``ite 5 then
          let #[_, c, d, a, b] := x.getAppArgs | return e
          let .const _ lvls := x.getAppFn | return e
          let field (y : Expr) := mkAppN (mkConst f (e.getAppFn.constLevels!)) (args.pop.push y)
          return mkAppN (mkConst ``ite lvls) #[n.under, c, d, ← unwrapNewtypes (field a), ← unwrapNewtypes (field b)]
        return mkAppN e.getAppFn ((← args.pop.mapM unwrapNewtypes).push x)
  return mkAppN e.getAppFn (← args.mapM unwrapNewtypes)

/-- `a` and `b`, of the type `α`, as their fields if `α` is a newtype,
through newtypes of newtypes, and the type of those. -/
partial def underNewtype (α a b : Expr) : MetaM (Expr × Expr × Expr) := do
  let st ← getState
  let some n := st.newtypeOf? α | return (α, a, b)
  let some d := α.getAppFn.constName? | return (α, a, b)
  let some info := getStructureInfo? (← getEnv) d | return (α, a, b)
  let some field := info.fieldNames[0]? | return (α, a, b)
  let proj (x : Expr) : MetaM Expr := mkAppM (d ++ field) #[x]
  underNewtype n.under (← proj a) (← proj b)

/-- The conditions of `e`, a sum, at `Int` or `Nat`, of `if p then 1 else 0`
and of integer literals and constants that are not negative, if it is one:
each `p`, and each integer `k` as `k` conditions that are `true`, but at
most two, which decide a count compared with 1 as more do (`FrenCli`'s
`Ex.indicators?`). Casts from `Nat` to `Int` are looked through. -/
partial def indicators (e : Expr) : Option (Array (Bool ⊕ Expr)) :=
  let e := uncast e
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``HAdd.hAdd, #[_, _, _, _, a, b] => do return (← indicators a) ++ (← indicators b)
  | some ``ite, #[_, p, _, x, y] => if countLit? x == some 1 && countLit? y == some 0 then some #[.inr p] else none
  | _, _ => match countLit? e with
    | some k => if 0 ≤ k then some ((List.replicate (min k.toNat 2) (Sum.inl true)).toArray) else none
    | none => none

/-- Whether `e`'s value is known with every index out of range unknown,
as a `Bool` over `e`'s locals (`Atoms.unknown`), as the `fren` command's
evaluator has it (`Interp.outOfRange`): an index is known where its parts
are and it is in range; `and`, `or`, `not` and implication by the strong
Kleene connectives (`Core.Enumeration.andTruth`), and `iff` where both
sides are; an `if` where its condition and the branch it takes are, or
where both branches are and are equal (`Core.iteKnown`); a count of
conditions compared with 1, as a cardinality operation is written, where
its unknown conditions cannot change it (`Core.Cardinality.holds?`); any
other application where its arguments are (`Core.appliedKnown`), the last
arm of a complete `match` among them (`Fren.lastArm`). An index under a
binder is not analysed, and is never known. `decide` gives each
proposition's value. -/
partial def knownOf (decideOf : Expr → MetaM Expr) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  let tt := mkConst ``Bool.true
  let ff := mkConst ``Bool.false
  if !hasIndex e then return tt
  let and2 (a b : Expr) := mkApp2 (mkConst ``and) a b
  let not1 (a : Expr) := mkApp (mkConst ``not) a
  let go := knownOf decideOf
  let optBool := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
  -- The truth whose value is `p`, a `Bool`, where `k` says it is known.
  let truth (k p : Expr) : MetaM Expr := do
    mkAppM ``cond #[k, ← mkAppOptM ``Option.some #[mkConst ``Bool, p], ← mkAppOptM ``Option.none #[mkConst ``Bool]]
  let isSome (t : Expr) : Expr := mkApp2 (mkConst ``Option.isSome [0]) (mkConst ``Bool) t
  -- By the strong Kleene connectives that the `fren` command's evaluator
  -- uses (`check::partial_and`); `pa` and `pb` are the sides' values as
  -- `Bool`s.
  let kleeneAnd (ka pa kb pb : Expr) : MetaM Expr :=
    return isSome (mkApp2 (mkConst ``Core.Enumeration.andTruth) (← truth ka pa) (← truth kb pb))
  let kleeneOr (ka pa kb pb : Expr) : MetaM Expr :=
    return isSome (mkApp2 (mkConst ``Core.Enumeration.orTruth) (← truth ka pa) (← truth kb pb))
  -- `a = 1` or `a ≤ 1` (`c`), where `a` is a sum of `if p then 1 else 0`,
  -- as a cardinality operation is written, or one written out: known
  -- where the unknown conditions cannot change the count's comparison
  -- (`Core.Cardinality.holds?`), as the `fren` command has it
  -- (`Ex.countOfOne?`).
  let countKnown (c : Core.Cardinality) (α a one : Expr) : MetaM (Option Expr) := do
    -- At a newtype, as `=` compares its values, the sides' fields, which
    -- the `fren` command, which erases newtypes, compares.
    let (α, a, one) ← underNewtype α a one
    let (a, one) := (← unwrapNewtypes a, ← unwrapNewtypes one)
    unless (α.isConstOf ``Int || α.isConstOf ``Nat) && countLit? one == some 1 do return none
    let some leaves := indicators a | return none
    let ops ← leaves.mapM fun
      | .inl k => mkAppOptM ``Option.some #[mkConst ``Bool, mkConst (if k then ``Bool.true else ``Bool.false)]
      | .inr p => do
        let v ← mkAppOptM ``Option.some #[mkConst ``Bool, ← decideOf p]
        mkAppM ``cond #[← go p, v, ← mkAppOptM ``Option.none #[mkConst ``Bool]]
    let cE := mkConst (if c == .exactlyOne then ``Core.Cardinality.exactlyOne else ``Core.Cardinality.atMostOne)
    let r := mkApp2 (mkConst ``Core.Cardinality.holds?) cE (← mkListLit optBool ops.toList)
    return some (← mkAppM ``Option.isSome #[r])
  -- Any other application: known where its arguments are, as evaluation
  -- is strict (`model::known_application`).
  let generic : MetaM Expr := do
    if e.isApp && !hasIndex e.getAppFn then
      let args := e.getAppArgs
      if args.any fun a => (a.isLambda || a.isForall || a.isLet) && hasIndex a then return ff
      return mkApp2 (mkConst ``Core.appliedKnown) (← mkListLit (mkConst ``Bool) (← args.mapM go).toList) tt
    return ff
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Fren.Enum.nthOr, #[_, _, q, i, _] =>
    let len ← mkAppM ``Fren.Seq.len #[q]
    let inRange ← decideOf (← mkAppM ``And #[← mkAppM ``LE.le #[← intExpr 0, i], ← mkAppM ``LT.lt #[i, len]])
    return and2 (and2 (← go q) (← go i)) inRange
  | some ``And, #[a, b] => kleeneAnd (← go a) (← decideOf a) (← go b) (← decideOf b)
  | some ``Or, #[a, b] => kleeneOr (← go a) (← decideOf a) (← go b) (← decideOf b)
  | some ``Not, #[a] => go a
  | some ``Iff, #[a, b] => return and2 (← go a) (← go b)
  | some ``Decidable.decide, #[p, _] => go p
  | some ``and, #[a, b] => kleeneAnd (← go a) a (← go b) b
  | some ``or, #[a, b] => kleeneOr (← go a) a (← go b) b
  | some ``not, #[a] => go a
  | some ``ite, #[_, c, _, a, b] =>
    let (kc, ka, kb) := (← go c, ← go a, ← go b)
    let same ← try
        if ← isProp a then decideOf (← mkAppM ``Iff #[a, b]) else decideOf (← mkEq a b)
      catch _ => pure ff
    return mkApp4 (mkConst ``Core.iteKnown) (← truth kc (← decideOf c)) ka kb same
  | some ``Eq, #[α, a, one] =>
    if let some r ← countKnown .exactlyOne α a one then return r
    generic
  | some ``LE.le, #[α, _, a, one] =>
    if let some r ← countKnown .atMostOne α a one then return r
    generic
  -- `1 ≥ a` is `a ≤ 1` (`Reqs/Lang/Semantics#derived-forms`).
  | some ``GE.ge, #[α, _, one, a] =>
    if let some r ← countKnown .atMostOne α a one then return r
    generic
  | _, _ =>
    if let .forallE _ a b _ := e then
      if !b.hasLooseBVars && (← isProp a) then
        -- `a → b`, as `when a, b`: `not a or b`.
        let (ka, kb) := (← go a, ← go b)
        return ← kleeneOr ka (not1 (← decideOf a)) kb (← decideOf b)
      return ff
    generic

/-- A `Decidable` instance for the proposition `p`, built along its
connectives, so that a quantifier over a listed type, which is expanded
into as many conjuncts as it has instances, needs no search of the size
of the whole; each other proposition's is synthesized. -/
partial def decidableOf (p : Expr) : MetaM Expr := do
  match p.getAppFn.constName?, p.getAppArgs with
  | some ``And, #[a, b] => return mkApp4 (mkConst ``instDecidableAnd) a b (← decidableOf a) (← decidableOf b)
  | some ``Or, #[a, b] => return mkApp4 (mkConst ``instDecidableOr) a b (← decidableOf a) (← decidableOf b)
  | some ``Not, #[a] => return mkApp2 (mkConst ``instDecidableNot) a (← decidableOf a)
  | some ``Iff, #[a, b] => return mkApp4 (mkConst ``instDecidableIff) a b (← decidableOf a) (← decidableOf b)
  | _, _ =>
    if let .forallE _ a b _ := p then
      if !b.hasLooseBVars && (← isProp a) then
        return mkApp4 (mkConst ``instDecidableForall) a b (← decidableOf a) (← decidableOf b)
    synthInstance (mkApp (mkConst ``Decidable) p)

end Enumerate

end Fren
