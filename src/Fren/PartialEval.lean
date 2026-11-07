-- keep-sorted start
import Fren.Elab.TypeTerms
import Fren.Known
import Fren.Prelude
-- keep-sorted end

/-!
# Partial formula evaluation

Confirmation and enumeration share guarded quantifier evaluation and the
strong Kleene connectives (`Reqs/Models#how-the-front-ends-evaluate`). The
caller supplies unbounded domains: unknown to confirmation, and values up
to the search bound to enumeration.
-/

open Lean Meta

namespace Fren

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
  | none => let a := yes (); if a == no () then a else none

namespace Enumerate

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
  let ty := ty.consumeMData
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
  let ty := (← inferType x).consumeMData
  let toInt (e : Expr) : MetaM (Option Expr) := do
    let t := (← inferType e).consumeMData
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
    let collectionType := (← inferType collection).consumeMData
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

mutual
/-- The truth of the proposition `p`, an `Option Bool`, `none` where it is
unknown: by the strong Kleene connectives, and each quantifier over its
guard's domain or, without one, over `domain` of its type, which gives
its values up to the bound and whether they are all of its type's. -/
partial def partialDecide (domain : PartialEnv) (p : Expr) : MetaM Expr := do
  let p := p.consumeMData
  if p.isAppOfArity ``Fren.lastArm 4 then
    -- A guarded quantifier can already be known, even with an unknown
    -- index under its binder. Ask the same partial evaluator as its body,
    -- rather than the quantifier-free knownness check.
    return ← mkAppM ``Enum.ifKnown
      #[← partialKnown domain p.getAppArgs[2]!, ← partialDecide domain p.appArg!]
  if p.isAppOfArity ``Fren.typeObligation 2 then return ← partialDecide domain p.appArg!
  -- Preserve the count's truth even if a quantified condition has no
  -- partial outcome. Strictly lifting the numeric sum would lose it.
  if let some (c, leaves) ← countArgs? p then
    let operands ← leaves.mapM fun
      | .inl b => mkAppM ``Option.some #[toExpr b]
      | .inr q => partialDecide domain q
    let op := mkConst (if c == .exactlyOne then ``Core.Cardinality.exactlyOne else ``Core.Cardinality.atMostOne)
    return mkApp2 (mkConst ``Core.Cardinality.holds?) op
      (← mkListLit (mkApp (mkConst ``Option [0]) (mkConst ``Bool)) operands.toList)
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
    mkAppM name #[← partialDecide domain a, ← thunk (← partialDecide domain b)]
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
    if ← hasQuantifier p then
      return ← liftArgs domain p fun q => do
        domain.wrap #[q] (← mkAppM ``Option.some #[mkApp2 (mkConst ``Decidable.decide) q (← decidableOf q)])
    domain.wrap #[p] (← mkAppM ``Option.some #[mkApp2 (mkConst ``Decidable.decide) p (← decidableOf p)])

/-- The value of `e`, which is not a proposition, as an `Option`, `none`
where it is unknown, as the `fren` command's evaluator has it: a
conditional whose condition is unknown has the value that its branches
share, and an application with an unknown argument has none. -/
partial def partialValue (domain : PartialEnv) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  unless ← hasQuantifier e do return ← domain.wrap #[e] (← mkAppM ``Option.some #[e])
  if e.isAppOfArity ``Fren.lastArm 4 then
    -- Boolean matches also have value-valued arms. Their scrutinee can
    -- still be a proposition, which generic argument lifting cannot read.
    return ← mkAppM ``Enum.ifKnown
      #[← partialKnown domain e.getAppArgs[2]!, ← partialValue domain e.appArg!]
  if e.isAppOfArity ``Decidable.decide 2 then return ← partialDecide domain e.getAppArgs[0]!
  if let .letE _ _ value body _ := e then return ← partialValue domain (body.instantiate1 value)
  let thunk (value : Expr) := withLocalDeclD `_ (mkConst ``Unit) fun u => mkLambdaFVars #[u] value
  if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    return ← mkAppM ``Enum.iteValue
      #[← partialDecide domain args[1]!, ← thunk (← partialValue domain args[3]!), ← thunk (← partialValue domain args[4]!)]
  liftArgs domain e fun x => do domain.wrap #[x] (← mkAppM ``Option.some #[x])

/-- Whether a strict marker's scrutinee has a partial outcome, including
when it is a quantified proposition rather than a Boolean decision. -/
partial def partialKnown (domain : PartialEnv) (e : Expr) : MetaM Expr := do
  -- Strict applications also retain erased type and instance arguments.
  -- Keep the quantifier-free check for these: wrapping a type in our
  -- value-level Option would have the wrong universe.
  if (!(← isProp e) && (← isType e)) || (← isProof e) || !(← hasQuantifier e) then
    return ← (domain.known?.map (· e)).getD (pure (mkConst ``Bool.true))
  let value ← if ← isProp e then partialDecide domain e else partialValue domain e
  mkAppM ``Option.isSome #[value]

/-- `leaf` of the application `e`, an `Option`, with each of its arguments
that has a quantifier evaluated first by `partialValue`: `none` if one is
unknown. -/
partial def liftArgs (domain : PartialEnv) (e : Expr) (leaf : Expr → MetaM Expr) : MetaM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if ← hasQuantifier fn then throwError "a quantifier in a function position cannot be enumerated: {e}"
  let some i ← (List.range args.size).findM? (fun i => hasQuantifier args[i]!) | leaf e
  let arg := args[i]!
  let ty ← inferType arg
  if (← isProp arg) || (← isProp ty) then throwError "a quantifier in a proposition's argument cannot be enumerated: {e}"
  let value ← partialValue domain arg
  withLocalDeclD `v ty fun x => do
    let e' := mkAppN fn (args.set! i x)
    unless ← isTypeCorrect e' do throwError "a quantifier in a dependent argument cannot be enumerated: {e}"
    mkAppM ``Option.bind #[value, ← mkLambdaFVars #[x] (← liftArgs domain e' leaf)]
end

end Enumerate

end Fren
