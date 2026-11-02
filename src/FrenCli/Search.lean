-- keep-sorted start
import FrenCli.Eval
import FrenCli.Verdicts
import Std.Data.HashMap
-- keep-sorted end

/-!
# Searching for behaviours (`Reqs/Eval#searching-for-behaviours`)

A random search for values of variables that make a set of constraints
(`Eval.Atom`) true. Each variable's candidates are tried in a random order,
a branch is abandoned as soon as a constraint is `false`, and a variable
that runs out of candidates goes back to the last variable that its
failure depends on (backjumping). The search is incomplete, but whatever it returns has been
evaluated.
-/

open Lean

namespace FrenCli.Eval

/-- SplitMix64. -/
structure Rng where
  s : UInt64
  deriving Inhabited

@[inline] def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev R := StateM Rng

def rand : R UInt64 := modifyGet Rng.next

/-- Uniform in `[0, n)`, for `n > 0`. -/
def below (n : Nat) : R Nat := do
  let r ← rand
  let n := max n 1
  -- `r.toNat % n`, without a `Nat` as large as `r`.
  return if n < UInt64.size then (r % n.toUInt64).toNat else r.toNat % n

/-- Fisher–Yates: each `i` from the last index down to `0` swaps with a
random `j ≤ i`, drawn as `below (i + 1)` draws it. The generator is
threaded through a loop rather than the state monad, so that a draw
allocates nothing; it draws the same values in the same order. -/
def shuffle (xs : Array α) : R (Array α) := modifyGet fun g => loop xs xs.size g
where
  loop (xs : Array α) (i : Nat) (g : Rng) : Array α × Rng :=
    match i with
    | 0 => (xs, g)
    | i + 1 =>
      let (r, g) := g.next
      -- `below (i + 1)`; `i + 1` is at least 1, so its `max` is itself.
      let n := i + 1
      let j := if n < UInt64.size then (r % n.toUInt64).toNat else r.toNat % n
      loop (xs.swapIfInBounds i j) i g

def mix (h : UInt64) (x : UInt64) : UInt64 := (Rng.next ⟨h ^^^ (x * 0x2545F4914F6CDD1D)⟩).1

/-! ## Interpretations -/

/-- A random interpretation: how many values each abstract type has, and
a seed that fixes each function's value at each argument. -/
structure World where
  seed : UInt64
  sizes : NameMap Nat := {}
  deriving Inhabited

def World.size (w : World) (sort : Name) : Nat := (w.sizes.find? sort).getD 1

def World.random (sp : Spec) : R World := do
  let seed ← rand
  let mut sizes := {}
  for s in sp.sorts do sizes := sizes.insert s ((← below 3) + 1)
  return { seed, sizes }

/-- A value of `ty` chosen by `h`: small, so that functions' values are
like the values that constraints mention. -/
partial def valueOf (sp : Spec) (w : World) (h : UInt64) (depth : Nat := 2) : VTy → Val
  | .bool => .bool (h % 2 == 0)
  | .int => .int ((h % 7).toNat - 3 : Int)
  | .nat => .int (h % 4).toNat
  | .string => .str (#["", "a", "b"][(h % 3).toNat]!)
  | .set t => if h % 2 == 0 then .set #[] else Val.setOf #[valueOf sp w (mix h 1) depth t]
  | .seq t => if h % 2 == 0 then .seq #[] else .seq #[valueOf sp w (mix h 1) depth t]
  | .rel a b => if h % 2 == 0 then .set #[] else Val.setOf #[.pair (valueOf sp w (mix h 1) depth a) (valueOf sp w (mix h 2) depth b)]
  | .abstract s => .abs s ((h % (w.size s).toUInt64).toNat)
  | .newtype _ u => valueOf sp w h depth u
  -- Never asked for: every type a value is made for is an instance's.
  | .param _ => .bool false
  | .data p targs => Id.run do
    let some d := sp.data.find? p | return .ctor p 0 #[]
    -- Below the depth, only constructors without the type in their fields.
    let ok := if depth == 0 then d.ctors.filter (·.fields.all fun (_, t) => match t with | .data q _ => q != p | _ => true) else d.ctors
    let cs := if ok.isEmpty then d.ctors else ok
    let i := (h % cs.size.toUInt64).toNat
    let c := cs[i]!
    let idx := (d.ctors.findIdx? (·.name == c.name)).getD 0
    let args := c.fields.mapIdx fun k (_, t) => valueOf sp w (mix h (k.toUInt64 + 1)) (depth - 1) (t.subst targs)
    return .ctor p idx args

partial def hashVal : Val → UInt64
  | .bool b => if b then 1 else 2
  | .int i => mix 3 (hash i)
  | .str s => mix 4 (hash s)
  | .set ms => ms.foldl (fun h a => mix h (hashVal a)) 5
  | .pair a b => mix (mix 6 (hashVal a)) (hashVal b)
  | .seq es => es.foldl (fun h a => mix h (hashVal a)) 7
  | .abs s k => mix (hash s) k.toUInt64
  | .ctor t i args => args.foldl (fun h a => mix h (hashVal a)) (mix (hash t) i.toUInt64)

/-- A value of `ty`, of the declared type `t`, chosen by `h`, as `valueOf`
chooses one: the first of a few choices that is a value of `t`
(`typeHolds`), or else, for an integer type whose pattern has a bound, a
bound of its first alternative that has one. -/
def typedValueOf (sp : Spec) (w : World) (h : UInt64) (ty : VTy) (t : Fren.Core.PTy) : Val := Id.run do
  let shapes := sp.shapes.find?
  for k in [0:16] do
    let v := valueOf sp w (if k == 0 then h else mix h k.toUInt64) 2 ty
    if typeHolds shapes t v then return v
  let bound : Fren.Core.Pat → Option Int
    | .int lo hi => lo <|> hi
    | .or ps => ps.findSome? fun
      | .int lo hi => lo <|> hi
      | _ => none
    | _ => none
  match t.pat?.bind bound with
  | some i => return .int i
  | none => return valueOf sp w h 2 ty

/-- The value of the function `f` at `args` in the interpretation `w`:
random, but where the arguments meet `f`'s preconditions, the first of a
few random values that meets its postconditions, and none if none does
(`Reqs/Eval#searching-for-behaviours`), each a value of its result
type, as declared (`typedValueOf`). The clauses are evaluated with the
other functions' values, to the depth `depth`, beyond which they are not
checked. -/
partial def World.value (sp : Spec) (w : World) (f : Name) (args : Array Val) (depth : Nat := 3) : Option Val := do
  let (_, r) ← sp.funs.find? f
  let h := args.foldl (fun h a => mix h (hashVal a)) (mix w.seed (hash f))
  -- An instance of a generic function has the function's declared result
  -- type and contract, at its type arguments (`Spec.instanceOf`).
  let base := (sp.instanceOf.find? f).getD f
  -- Its result is a value of its declared type (`Reqs/Lang/Items#uninterpreted-functions`).
  let valueAt (h : UInt64) : Val := match sp.results.find? base with
    | some t => typedValueOf sp w h r t
    | none => valueOf sp w h 2 r
  let contract := sp.contracts.find? base
  let others : Interp := { defs := sp.defs.find?, shapes := sp.shapes.find?, recDefs := sp.recDefs.find?, fn := fun g as => if depth == 0 then none else w.value sp g as (depth - 1) }
  let checkPosts := contract.any fun (ps, pres, _) =>
    pres.all (·.eval others (fun _ => none) (ps.zip args).toList == some (.bool true))
  -- The first of 16 random candidates that meets the contract, each made
  -- only if those before it do not.
  (List.range 16).findSome? fun k =>
    let v := valueAt (if k == 0 then h else mix h k.toUInt64)
    let I : Interp := { defs := sp.defs.find?, shapes := sp.shapes.find?, recDefs := sp.recDefs.find?, fn := fun g as =>
      if (g == f || g == base) && as == args then some v else if depth == 0 then none else w.value sp g as (depth - 1) }
    let member := (sp.results.find? base).all fun t =>
      (Ex.typed t #[] (.lit v)).eval I (fun _ => none) == some (.bool true)
    if member && (!checkPosts || contract.all fun (ps, _, posts) =>
      posts.all (·.eval I (fun _ => none) (ps.zip args).toList == some (.bool true))) then some v else none

/-- `sp.shapes`, in a hash map, in which `typeHolds` looks up a type more
cheaply than in a `NameMap`, at each instance of a quantifier. It has the
same entries. -/
def Spec.shapeMap (sp : Spec) : Std.HashMap Name Fren.Core.DataShape := sp.shapes.foldl (·.insert · ·) {}

/-- The interpretation that `w` gives, where `shapes?` is `sp.shapeMap`, if
it is given, built once for many interpretations. -/
def World.interp (sp : Spec) (w : World) (shapes? : Option (Std.HashMap Name Fren.Core.DataShape) := none) : Interp where
  defs := sp.defs.find?
  fn f args := w.value sp f args
  recDefs := sp.recDefs.find?
  matchMemo p s := do return (← (← sp.matchMemo[p]?)[s]?).get
  shapes p := match shapes? with
    | some m => m[p]?
    | none => sp.shapes.find? p

/-! ## Candidates -/

/-- The integers that bound the literal and range patterns of `p`. -/
partial def Pat.lits : Pat → Array Int
  | .int lo hi => lo.toArray ++ hi.toArray
  | .ctor _ ps | .alts ps => ps.flatMap Pat.lits
  | _ => #[]

/-- The string literals of the patterns of `p`. -/
partial def Pat.strLits : Pat → Array String
  | .str s => #[s]
  | .ctor _ ps | .alts ps => ps.flatMap Pat.strLits
  | _ => #[]

partial def Ex.lits : Ex → Array Int
  | .lit (.int i) => #[i]
  | .lit _ | .var _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => #[]
  | .memo lets e => e.lits ++ lets.flatMap (·.lits)
  | .lifted lets e => e.lits ++ lets.flatten.flatMap (·.lits)
  | .dispatch _ m => m.lits
  | .not a | .neg a | .field a _ | .pre _ _ _ a => a.lits
  | .bin _ a b | .when _ a b => a.lits ++ b.lits
  | .ite c a b => c.lits ++ a.lits ++ b.lits
  | .app _ args | .cardinality _ args | .ctor _ _ args => args.flatMap (·.lits)
  | .method _ r args => r.lits ++ args.flatMap (·.lits)
  | .matches r _ _ => r.lits
  | .setLit es => es.flatMap (·.lits)
  | .pair a b | .index a b _ _ => a.lits ++ b.lits
  | .seqLit es => es.flatMap (·.lits)
  | .card e => e.lits
  | .match e arms .. => e.lits ++ arms.flatMap fun (p, g?, b) => p.lits ++ (g?.map (·.lits)).getD #[] ++ b.lits
  | .update e fs => e.lits ++ fs.flatMap (·.2.lits)
  | .quant _ _ _ _ ds _ b => b.lits ++ ds.flatMap (·.toArray.flatMap (·.lits))
  | .range lo hi => lo.lits ++ hi.lits
  | .table _ rows _ => rows.flatMap fun (_, c?, v) => (c?.map (·.lits)).getD #[] ++ v.lits
  | .const _ e => e.lits
  -- The bounds of the patterns of the type, which the values must meet.
  | .typed _ is e => is ++ e.lits

/-- The expressions that `e`, a constraint over the search's environment
(`Ex.slot`), equates the variable at index `x` with. -/
partial def Ex.equated (x : Nat) : Ex → Array Ex
  | .bin .eq (.slot y) e | .bin .iff (.slot y) e => (if y == x then #[e] else #[]) ++ e.equated x
  | .bin .eq e (.slot y) | .bin .iff e (.slot y) => (if y == x then #[e] else #[]) ++ e.equated x
  | .lit _ | .var _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => #[]
  | .memo lets e => e.equated x ++ lets.flatMap (·.equated x)
  | .lifted lets e => e.equated x ++ lets.flatten.flatMap (·.equated x)
  | .dispatch _ m => m.equated x
  | .not a | .neg a | .field a _ | .pre _ _ _ a => a.equated x
  | .bin _ a b | .when _ a b => a.equated x ++ b.equated x
  | .ite c a b => c.equated x ++ a.equated x ++ b.equated x
  | .app _ args | .cardinality _ args | .ctor _ _ args => args.flatMap (·.equated x)
  | .method _ r args => r.equated x ++ args.flatMap (·.equated x)
  | .matches r _ _ => r.equated x
  | .setLit es => es.flatMap (·.equated x)
  | .pair a b | .index a b _ _ => a.equated x ++ b.equated x
  | .seqLit es => es.flatMap (·.equated x)
  | .card e => e.equated x
  | .match e arms .. => e.equated x ++ arms.flatMap fun (_, g?, b) => (g?.map (·.equated x)).getD #[] ++ b.equated x
  | .update e fs => e.equated x ++ fs.flatMap (·.2.equated x)
  | .quant _ _ _ _ ds _ b => b.equated x ++ ds.flatMap (·.toArray.flatMap (·.equated x))
  | .range lo hi => lo.equated x ++ hi.equated x
  | .table _ rows _ => rows.flatMap fun (_, c?, v) => (c?.map (·.equated x)).getD #[] ++ v.equated x
  | .const .. => #[]
  | .typed _ _ e => e.equated x

/-- The small sets of the candidates `elems` of their elements: the empty
set and singletons (`smallValues`). -/
def smallSets (elems : Array Val) : Array Val := #[.set #[]] ++ (elems.extract 0 4).map (Val.setOf #[·])

/-- The small sequences of the candidates `elems` of their elements: the
empty sequence, singletons and pairs (`smallValues`). -/
def smallSeqs (elems : Array Val) : Array Val :=
  let vs := elems.extract 0 3
  #[.seq #[]] ++ vs.map (Val.seq #[·]) ++ (vs.zip (vs.extract 1)).map fun (a, b) => .seq #[a, b]

/-- All of `each`, if they are at most `cap`; otherwise the first `cap` of
them taken in turn, the first of each, then the second of each, and so on,
so that each has some within `cap` (`smallValues`). -/
def smallInterleaved (cap : Nat) (each : Array (Array Val)) : Array Val := Id.run do
  if each.foldl (· + ·.size) 0 ≤ cap then return each.flatten
  let mut out := #[]
  for k in [0:cap] do
    for vs in each do
      if let some v := vs[k]? then out := out.push v
    if out.size ≥ cap then break
  return out.extract 0 cap

/-- `smallValues`, with the values of each type at each depth computed
once, however many fields have that type: a pure function of them. -/
partial def smallValuesMemo (sp : Spec) (w : World) (ints : Array Int) (strs : Array String) (cap : Nat)
    (depth : Nat) (ty : VTy) : StateM (Std.HashMap (Nat × VTy) (Array Val)) (Array Val) := do
  if let some vs := (← get)[(depth, ty)]? then return vs
  let go := smallValuesMemo sp w ints strs cap
  let vs ← match ty with
    | .bool => pure #[.bool false, .bool true]
    | .int => pure (ints.map .int)
    | .nat => pure ((ints.filter (0 ≤ ·)).map .int)
    -- The strings of the constraints (`stringsOf`) first, so that sets
    -- and sequences of strings, which take the first few, have them; then a
    -- few others. Constraints that equate a variable with a string give the
    -- rest.
    | .string => pure ((strs ++ #["", "a", "b"].filter (!strs.contains ·)).map .str)
    -- The empty set and singletons; constraints that equate a variable with a
    -- set give the others.
    | .set t => pure (smallSets (← go depth t))
    -- The empty sequence, singletons and pairs of candidates, so that
    -- indexes at `0` and `1` have something to read.
    | .seq t => pure (smallSeqs (← go depth t))
    -- The empty relation, single pairs, and a chain of pairs, so that
    -- `closure` has something to close.
    | .rel a b => do
      let as := (← go depth a).extract 0 3
      let bs := (← go depth b).extract 0 3
      let pairs := as.flatMap fun x => bs.map (Val.pair x ·)
      let mut out := #[.set #[]] ++ (pairs.extract 0 6).map (Val.setOf #[·])
      if a == b && as.size ≥ 3 then
        out := out.push (Val.setOf #[.pair as[0]! as[1]!, .pair as[1]! as[2]!])
      pure out
    | .abstract s => pure ((Array.range (w.size s)).map (.abs s))
    | .newtype _ u => go depth u
    | .param _ => pure #[]
    -- Each variant's, taken in turn, so that each has some within `cap`.
    | .data p targs =>
      match sp.data.find? p with
      | none => pure #[]
      | some d => do
        let mut each : Array (Array Val) := #[]
        for c in d.ctors, idx in [0:d.ctors.size] do
          if depth == 0 && !c.fields.isEmpty then continue
          let mut combos : Array (Array Val) := #[#[]]
          for (_, t) in c.fields do
            let vs ← go (depth - 1) (t.subst targs)
            -- The first `cap` of the combinations, in order, each made
            -- only if it is among them.
            let mut next := #[]
            for pre in combos do
              for v in vs do
                if next.size ≥ cap then break
                next := next.push (pre.push v)
            combos := next
          each := each.push (combos.map (.ctor p idx ·))
        pure (smallInterleaved cap each)
  modify (·.insert (depth, ty) vs)
  return vs

/-- Every value of `ty` up to `depth`, at most `cap` of them. -/
def smallValues (sp : Spec) (w : World) (ints : Array Int) (strs : Array String) (cap : Nat) (depth : Nat)
    (ty : VTy) : Array Val :=
  (smallValuesMemo sp w ints strs cap depth ty).run' {}

/-- Whether `smallValues` reads its integers for `ty`: whether an `Int` or
a `Nat` can be reached from it, through elements and fields. Otherwise it
returns the same values whatever the integers are, since it reads them
only at those types. A datatype already being looked at, in `seen`, adds
no type that it does not add the first time. -/
partial def VTy.readsInts (sp : Spec) (seen : List Name := []) : VTy → Bool
  | .int | .nat => true
  | .bool | .string | .abstract _ => false
  | .set t | .seq t => t.readsInts sp seen
  | .rel a b => a.readsInts sp seen || b.readsInts sp seen
  -- A newtype's values are its underlying type's (`smallValues`).
  | .newtype _ u => u.readsInts sp seen
  | .data p targs =>
    -- An instance's arguments are among its parts (`lang::parts`).
    targs.any (·.readsInts sp seen) || if seen.contains p then false else
      match sp.data.find? p with
      | some d => d.ctors.any (·.fields.any (·.2.readsInts sp (p :: seen)))
      | none => false
  | .param _ => false

/-- Whether `smallValues` reads the world for `ty`: whether an abstract
type, whose values the world gives, can be reached from it, through
elements and fields, as for `VTy.readsInts`. Otherwise it returns the same
values in every world. -/
partial def VTy.readsSorts (sp : Spec) (seen : List Name := []) : VTy → Bool
  | .abstract _ => true
  | .int | .nat | .bool | .string | .param _ => false
  | .set t | .seq t | .newtype _ t => t.readsSorts sp seen
  | .rel a b => a.readsSorts sp seen || b.readsSorts sp seen
  | .data p targs =>
    targs.any (·.readsSorts sp seen) || if seen.contains p then false else
      match sp.data.find? p with
      | some d => d.ctors.any (·.fields.any (·.2.readsSorts sp (p :: seen)))
      | none => false

/-- The variables of `e`. -/
partial def Ex.vars : Ex → Array Name
  | .var n => #[n]
  | .lit _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => #[]
  | .memo lets e => e.vars ++ lets.flatMap (·.vars)
  | .lifted lets e => e.vars ++ lets.flatten.flatMap (·.vars)
  | .dispatch _ m => m.vars
  | .not a | .neg a | .field a _ | .card a | .pre _ _ _ a => a.vars
  | .bin _ a b | .when _ a b | .pair a b | .index a b _ _ => a.vars ++ b.vars
  | .ite c a b => c.vars ++ a.vars ++ b.vars
  | .app _ args | .cardinality _ args | .ctor _ _ args | .setLit args | .seqLit args => args.flatMap (·.vars)
  | .method _ r args => r.vars ++ args.flatMap (·.vars)
  | .matches r _ _ => r.vars
  | .match e arms .. => e.vars ++ arms.flatMap fun (_, g?, b) => (g?.map (·.vars)).getD #[] ++ b.vars
  | .update e fs => e.vars ++ fs.flatMap (·.2.vars)
  | .quant _ _ _ _ ds _ b => b.vars ++ ds.flatMap (·.toArray.flatMap (·.vars))
  | .range lo hi => lo.vars ++ hi.vars
  | .table _ rows _ => rows.flatMap fun (_, c?, v) => (c?.map (·.vars)).getD #[] ++ v.vars
  | .const .. => #[]
  | .typed _ _ e => e.vars

/-- What a search of a problem computes from its variables and
constraints alone, before it reads the environment or draws a random
number (`Problem.prepare`). -/
structure Prepared where
  /-- The names of the search's environment: the variables to choose,
  then those of the constraints. -/
  names : Array Name
  /-- Each name's index in `names`. -/
  index : Std.HashMap Name Nat
  /-- The constraints that mention each name, by index. -/
  byVar : Array (Array Nat)
  /-- The constraints, each variable read as its slot (`Ex.slot`). -/
  full : Array Ex
  /-- What is evaluated of each constraint (`Ex.compile`), likewise. -/
  run : Array Ex
  /-- The slots that each constraint reads (`Ex.slots`). -/
  fullSlots : Array (Array Nat)
  /-- Each variable to choose's slot. -/
  varSlot : Array Nat
  /-- For each variable to choose, what the constraints equate it with,
  compiled and as written, and the slots that those expressions read,
  computed when a search first reaches it. -/
  equated : Array (Thunk (Array (Ex × Ex) × Array Nat))

structure Problem where
  /-- The variables to choose, in order, with their types. -/
  vars : Array (Name × VTy)
  /-- What must hold. -/
  atoms : Array Atom
  /-- The integers that the constraints mention, and their neighbours. -/
  ints : Array Int := #[]
  /-- The strings that the constraints mention or match (`stringsOf`). -/
  strs : Array String := #[]
  /-- `Problem.prepare` of this problem, with the shapes of the
  interpretations that it is searched under, if it is searched more than
  once: a function of `vars` and `atoms`, so that each search need not
  compute it again. -/
  prepared? : Option (Thunk Prepared) := none
  /-- For some types, `Problem.fixedPool?`'s values in every world, with
  these `strs`, computed once for the problems that share them
  (`Spec.fixedPools`). -/
  fixedPools : Std.HashMap VTy (Thunk (Array Val)) := {}
  deriving Inhabited

abbrev Env := Std.HashMap Name Val

def Env.look (env : Env) : Look := fun n => env[n]?

/-- The values of a search's variables, by index (`Ex.slot`), as far as
they are known. -/
abbrev Slots := Array (Option Val)

/-- The values of type `ty` that `Problem.candidates` starts from, if they
do not depend on its random integers: `ty` is not a sequence, whose longer
candidates have the lengths of those integers, nor a set, whose larger
candidates are random, and `smallValues` does not read them
(`VTy.readsInts`). Then they are the same at every call of a search, which
computes them once. -/
def Problem.fixedPool? (sp : Spec) (w : World) (p : Problem) (ty : VTy) : Option (Array Val) :=
  match ty with
  | .seq _ | .set _ => none
  | _ => if ty.readsInts sp then none else some (smallValues sp w p.ints p.strs 24 2 ty)

/-- The pool of each of `tys` whose `Problem.fixedPool?` is the same in
every world and for any integers, with the strings `strs`: those that
are not sequences or sets, and from which `smallValues` reads neither the
integers nor the world (`VTy.readsInts`, `VTy.readsSorts`). Each is
computed when a search first needs it, once for every problem whose
strings are `strs` (`Problem.fixedPools`). -/
def Spec.fixedPools (sp : Spec) (strs : Array String) (tys : Array VTy) : Std.HashMap VTy (Thunk (Array Val)) :=
  tys.foldl (init := {}) fun m ty => match ty with
    | .seq _ | .set _ => m
    | _ =>
      if m.contains ty || ty.readsInts sp || ty.readsSorts sp then m
      else m.insert ty (Thunk.mk fun _ => smallValues sp default #[] strs 24 2 ty)

/-- `Problem.fixedPool? sp w p ty`, from `p.fixedPools` where it has it. -/
def Problem.fixedPoolIn (sp : Spec) (w : World) (p : Problem) (ty : VTy) : Option (Array Val) :=
  match p.fixedPools[ty]? with
  | some pool => some pool.get
  | none => p.fixedPool? sp w ty

/-- A condition on a search's environment under which an expression's value
is surely unknown (`Ex.unknownIf`): that slot `k` has no value, or one or
both of two conditions holds. -/
inductive UnknownIf where
  | never
  | slot (k : Nat)
  | any (a b : UnknownIf)
  | all (a b : UnknownIf)
  deriving Inhabited

def UnknownIf.or : UnknownIf → UnknownIf → UnknownIf
  | .never, b => b
  | a, .never => a
  | a, b => .any a b

def UnknownIf.and : UnknownIf → UnknownIf → UnknownIf
  | .never, _ | _, .never => .never
  | a, b => .all a b

/-- Whether the condition holds in `slots`. It allocates nothing, so it is
cheaper than evaluating the expression. -/
def UnknownIf.holds (slots : Slots) : UnknownIf → Bool
  | .never => false
  | .slot k => if h : k < slots.size then slots[k].isNone else true
  | .any a b => a.holds slots || b.holds slots
  | .all a b => a.holds slots && b.holds slots

/-- A condition under which `e` evaluates to `none` (`Ex.eval`), whatever
the interpretation, the look-up of names and the binders of `match` arms
are, since it reads only the slots. By the cases of `Ex.eval`:
- `.slot k` is `none` exactly when slot `k` has no value or is out of
  range.
- `and`, `or` and `when` are `none` when both operands are: `kleeneAnd`
  and `kleeneOr` of two `none`s are `none`, and so is `notV none`.
- The other operators (`binV`), and every expression that evaluates its
  operands in `Option`'s `do`, are `none` when any operand is.
- `ite c a b` is `none` when both branches are, and when `c` and one
  branch are, since with an unknown condition it has a value only where
  both branches have the same one.
- A quantifier over listed types, which has instances, folds `kleeneAnd`
  or `kleeneOr`, from a known value, over its body's values. Each is
  `none` under the body's condition, which no binder affects, and then so
  is the fold. An unbounded quantifier's domain may be empty, which gives
  it a value, so it gets `never`.
- Everything else, such as a table or a constant, gets `never`. -/
partial def Ex.unknownIf : Ex → UnknownIf
  | .slot k => .slot k
  | .not a | .neg a | .field a _ | .card a | .matches a _ _ | .match a .. | .dispatch _ a => a.unknownIf
  | .bin .and a b | .bin .or a b | .when _ a b => a.unknownIf.and b.unknownIf
  | .bin _ a b | .pair a b | .index a b _ _ => a.unknownIf.or b.unknownIf
  | .ite c a b =>
    let (c, a, b) := (c.unknownIf, a.unknownIf, b.unknownIf)
    (a.and b).or (c.and (a.or b))
  | .app _ args | .ctor _ _ args | .setLit args | .seqLit args => args.foldl (fun u a => u.or a.unknownIf) .never
  | .method _ r args => args.foldl (fun u a => u.or a.unknownIf) r.unknownIf
  | .quant _ _ _ _ ds _ body =>
    -- Every domain is a nonempty literal: a listed type's values.
    if ds.all (fun | some (.lit (.seq vs)) => !vs.isEmpty | _ => false) then body.unknownIf else .never
  | _ => .never

/-- The values that a variable of type `ty` takes, other than those that the
constraints equate it with (`Reqs/Eval#searching-for-behaviours`).
`fixed?` is `Problem.fixedPool? sp w p ty`. Two random integers are added
to `p.ints` where they are read: without `fixed?`, which is always the
case for a sequence. A search draws each variable's pool once, from a
generator of its own, and shuffles it at each visit (`Problem.search`). -/
def Problem.pool (sp : Spec) (w : World) (p : Problem) (ty : VTy) (fixed? : Option (Array Val)) : R (Array Val) := do
  let pool ← match fixed? with
    | some pool => pure pool
    | none => do
      let r₁ ← below 41
      let r₂ ← below 41
      let ints := (p.ints.push ((r₁ : Int) - 20)).push ((r₂ : Int) - 20)
      -- A sequence's or a set's elements' values, from which its own are
      -- made, computed once.
      let elems? := match ty with
        | .seq t | .set t => some (smallValues sp w ints p.strs 24 2 t)
        | _ => none
      let mut pool := match ty, elems? with
        | .seq _, some elems => smallSeqs elems
        | .set _, some elems => smallSets elems
        | _, _ => smallValues sp w ints p.strs 24 2 ty
      -- Longer sequences, of the lengths that the constraints mention.
      if let (.seq _, some elems) := (ty, elems?) then
        unless elems.isEmpty do
          for n in (ints.filterMap fun i => if 3 ≤ i && i ≤ 4 then some i.toNat else none).toList.eraseDups do
            for _ in [0:6] do
              pool := pool.push (.seq (← (Array.range n).mapM fun _ => do return elems[← below elems.size]!))
      -- Larger sets: a few of two, three and four candidates of the elements.
      if let (.set _, some elems) := (ty, elems?) then
        if elems.size ≥ 2 then
          -- Each with its key, computed once.
          let keyed := elems.map fun v => (Thunk.mk fun _ => v.setKey, v)
          for n in [2, 3, 4] do
            for _ in [0:4] do
              pool := pool.push (Val.setOfKeyed (← (Array.range n).mapM fun _ => do return keyed[← below keyed.size]!))
      pure pool
  return pool

/-- The candidates for a variable of type `ty`: the values that `equated`,
what the constraints equate it with, each with its `Ex.unknownIf`, have in
the search's environment `slots`, then the rest of its `pool`
(`Problem.pool`). An equated expression whose condition holds evaluates
to `none`, which gives no candidate, so it is not evaluated. -/
def candidatesIn (I : Interp) (slots : Slots) (ty : VTy) (equated : Array (Ex × UnknownIf)) (pool : Array Val) :
    Array Val := Id.run do
  let eqs := equated.filterMap fun (e, u) => if u.holds slots then none else e.eval I (fun _ => none) [] slots
  if eqs.isEmpty then return pool
  -- A `Nat` is at least 0, whatever a constraint equates it with.
  let eqs := if ty == .nat then eqs.filter (fun | .int i => 0 ≤ i | _ => false) else eqs
  let eqs := eqs.foldl (fun acc v => if acc.contains v then acc else acc.push v) #[]
  return eqs ++ pool.filter (!eqs.contains ·)

/-- Whether `e`, a constraint over the search's environment, is `true`,
`false` or unknown in `slots`. -/
def holdsIn (I : Interp) (slots : Slots) (e : Ex) : Option Bool :=
  match e.eval I (fun _ => none) [] slots with
  | some (.bool b) => some b
  | _ => none

/-- The slots that `e` reads (`Ex.slot`), each as often as it occurs. -/
partial def Ex.slots : Ex → Array Nat
  | .slot k => #[k]
  | .lit _ | .var _ | .bound _ | .boundAt _ | .shared _ | .known _ => #[]
  | .memo lets e => lets.flatMap (·.slots) ++ e.slots
  | .lifted lets e => lets.flatten.flatMap (·.slots) ++ e.slots
  | .dispatch _ m => m.slots
  | .not a | .neg a | .field a _ | .card a | .matches a _ _ | .const _ a => a.slots
  | .bin _ a b | .when _ a b | .pair a b | .index a b _ _ => a.slots ++ b.slots
  | .ite c a b => c.slots ++ a.slots ++ b.slots
  | .app _ args | .cardinality _ args | .ctor _ _ args | .setLit args | .seqLit args => args.flatMap (·.slots)
  | .method _ r args => r.slots ++ args.flatMap (·.slots)
  | .match e arms .. => e.slots ++ arms.flatMap fun (_, g?, b) => (g?.map (·.slots)).getD #[] ++ b.slots
  | .update e fs => e.slots ++ fs.flatMap (·.2.slots)
  | .quant _ _ _ _ ds _ b => ds.flatMap (·.toArray.flatMap (·.slots)) ++ b.slots
  | .range lo hi => lo.slots ++ hi.slots
  | .table _ rows _ => rows.flatMap fun (_, c?, v) => (c?.map (·.slots)).getD #[] ++ v.slots
  | .pre _ _ gs e => gs.flatMap (·.2.slots) ++ e.slots
  | .typed _ _ e => e.slots

/-- What `Problem.search` computes of `p` before it reads its environment,
compiled with `shapes`: the names of its environment and their indexes,
the constraints that mention each name, and the constraints compiled. -/
def Problem.prepare (shapes : Name → Option Fren.Core.DataShape) (p : Problem) : Prepared :=
  -- The names of the environment: the variables to choose, then those of
  -- the constraints; and the constraints that mention each, by index.
  let (names, index, byVar) := Id.run do
    let mut names : Array Name := #[]
    let mut index : Std.HashMap Name Nat := {}
    let mut byVar : Array (Array Nat) := #[]
    for (x, _) in p.vars do
      unless index.contains x do
        index := index.insert x names.size
        names := names.push x
        byVar := byVar.push #[]
    for a in p.atoms, k in [0:p.atoms.size] do
      for n in a.e.vars do
        let x := a.pfx ++ n
        let j ← match index[x]? with
          | some j => pure j
          | none =>
            index := index.insert x names.size
            names := names.push x
            byVar := byVar.push #[]
            pure (names.size - 1)
        byVar := byVar.modify j fun ks => if ks.back? == some k then ks else ks.push k
    return (names, index, byVar)
  -- Every name looked up here was given an index above: each variable to
  -- choose, and each variable `pfx.n` of a constraint.
  let full := p.atoms.map fun a => a.e.substVars fun n => .slot index[a.pfx ++ n]!
  -- What is evaluated (`Ex.compile`), compiled with `shapes`, or as the
  -- atom was for searches like this one; what is read of the constraints
  -- is read of `full`.
  let run := p.atoms.map fun a =>
    ((a.run?.map (·.get)).getD (a.e.compile shapes (some []))).substVars fun n => .slot index[a.pfx ++ n]!
  let varSlot := p.vars.map fun (x, _) => index[x]!
  { names, index, byVar, full, run, varSlot
    fullSlots := full.map (·.slots)
    equated := varSlot.map fun x => Thunk.mk fun _ =>
      let es := full.flatMap fun e => e.equated x
      (es.map fun e => (e.compile shapes (some []), e), es.flatMap (·.slots)) }

/-- Values for `p.vars`, extending `env`, that make every constraint
`true` under `I`, within `budget` steps, each step a candidate tried, and
the steps it took. `w` gives the candidates of the abstract types.

The constraints are compiled once per search: each variable `x` of a
constraint nested at `pfx` is read as the full name `pfx.x`, and each full
name, and each variable to choose, gets an index in the search's
environment (`Slots`), so that evaluation reads a variable without looking
up its name. Compiling changes no value: `.slot k` evaluates to the value
of the `k`th name, which is what `.var` of that name evaluated to in the
environment keyed by name, and the same names get values in the same
order. The environment is changed in place: a value is set before a
branch and cleared after it, so that each branch starts from the
environment that its parent had.

A branch is viable while no constraint is `false`. Extending a viable
environment with a value for `x` can change only the constraints that
mention `x` and are not yet known to be true, so only they are evaluated
again, which gives the same answer as evaluating them all, since evaluation
is monotone (`FrenCli.Eval`). Those that become true are marked so for the
branch and unmarked after it. A constraint whose `Ex.unknownIf` holds is
unknown, so it is not evaluated: it would neither make the branch
unviable nor become true. If a constraint is `false` in `env` itself, it
stays so, and the search finds nothing, at once.

The search draws one random number, from which it draws each variable's
pool (`Problem.pool`), once, and the pool's order at each visit, from the
values chosen before it. So a variable's candidates, but for their order,
are a function of the values of the variables that the expressions it is
equated with read. With `backjump`, a variable that runs out of
candidates goes back to the last variable in its conflict set
(`resumesAt`), not to the one before it (`Reqs/Eval#backjumping`). Each
rejection of a candidate reads only variables in the conflict set, and so
do the candidates themselves, but for their order. So no value of a
variable that it goes back past would let any of them through. The search
tries the candidates that backtracking would try, in the same order, but
for those, and finds the same values in no more steps, drawing the same
random numbers. -/
partial def Problem.search (sp : Spec) (w : World) (I : Interp) (p : Problem) (env : Env) (budget : Nat := 4000)
    (backjump := true) : R (Option Env × Nat) := do
  let seed ← rand
  let { names, byVar, full, run, fullSlots, varSlot, equated, .. } :=
    (p.prepared?.map (·.get)).getD (p.prepare I.shapes)
  -- When each constraint is surely unknown, so that it need not be evaluated.
  let unknown := full.map (·.unknownIf)
  let slots : Slots := names.map (env[·]?)
  -- Each constraint's value in `env`. A constraint that is `true` stays
  -- so on that branch (evaluation is monotone), and is not evaluated again;
  -- one that is `false` stays so on every branch.
  let atRoot := run.map (holdsIn I slots ·)
  if atRoot.any (· == some false) then return (none, 0)
  let rootTrue := atRoot.map (· == some true)
  -- For each slot, the set of the variables to choose that it is: the
  -- first position that names it, if the search chooses it.
  let slotBit : Array Nat := Id.run do
    let mut bits := Array.replicate names.size 0
    for x in varSlot.reverse, i in (List.range varSlot.size).reverse do
      bits := bits.set! x (if slots[x]!.isSome then 0 else 1 <<< i)
    return bits
  let readsOf (ks : Array Nat) : Nat := ks.foldl (fun acc k => acc ||| slotBit[k]!) 0
  -- The set of the variables that each constraint reads.
  let reads := fullSlots.map readsOf
  -- The first constraint that becomes `false` when the variable `x`, by
  -- index, gets its value in `slots`, or those that become `true`.
  let viable (slots : Slots) (x : Nat) (known : Array Bool) : Except Nat (Array Nat) := Id.run do
    let mut newly := #[]
    for k in byVar[x]! do
      if known[k]! || unknown[k]!.holds slots then continue
      match holdsIn I slots run[k]! with
      | some false => return .error k
      | some true => newly := newly.push k
      | none => pure ()
    return .ok newly
  -- What the constraints equate each variable with (`Prepared.equated`),
  -- and the set of the variables that those expressions read, computed
  -- when the search first reaches it.
  let eqsOf : Array (Thunk (Array (Ex × UnknownIf))) :=
    equated.map fun t => Thunk.mk fun _ => t.get.1.map fun (c, e) => (c, e.unknownIf)
  let eqReadsOf : Array (Thunk Nat) := equated.map fun t => Thunk.mk fun _ => readsOf t.get.2
  -- Each variable's pool, likewise.
  let pools : Array (Thunk (Array Val)) := p.vars.mapIdx fun i (_, ty) => Thunk.mk fun _ =>
    (p.pool sp w ty (p.fixedPoolIn sp w ty)).run' ⟨mix seed i.toUInt64⟩
  -- Returns whether it found values, the conflict set if it did not, and
  -- the steps left, with `slots` and `known` as they were given if it did
  -- not, and with the values found if it did. Every member of the
  -- conflict set is before `i`. Without steps left, the conflict set is
  -- empty, and nothing is tried.
  let rec go (i : Nat) (h : UInt64) (slots : Slots) (known : Array Bool) (left : Nat) :
      Bool × Nat × Slots × Array Bool × Nat := Id.run do
    if left == 0 then return (false, 0, slots, known, 0)
    if hi : i < p.vars.size then
      let (_, ty) := p.vars[i]
      let x := varSlot[i]!
      if slots[x]!.isSome then return go (i + 1) h slots known left
      let eqs := (eqsOf[i]!).get
      let eqReads := (eqReadsOf[i]!).get
      -- The pool, in an order drawn from the values chosen so far.
      let pool := (shuffle (pools[i]!).get).run' ⟨mix h i.toUInt64⟩
      let mut left := left
      let mut slots := slots
      let mut known := known
      let mut rejections : List Nat := []
      for v in candidatesIn I slots ty eqs pool do
        if left == 0 then break
        left := left - 1
        slots := slots.set! x (some v)
        match viable slots x known with
        | .error k => rejections := reads[k]! :: rejections
        | .ok newly =>
          for k in newly do known := known.set! k true
          let (found, c, slots', known', l) := go (i + 1) (mix h (hashVal v)) slots known left
          slots := slots'
          known := known'
          left := l
          if found then return (true, 0, slots, known, left)
          for k in newly do known := known.set! k false
          if left == 0 then break
          if backjump && !resumesAt c i then return (false, c, slots.set! x none, known, left)
          rejections := c :: rejections
      if left == 0 then return (false, 0, slots.set! x none, known, 0)
      return (false, conflictOf i eqReads rejections, slots.set! x none, known, left)
    else
      match (run.zip known).zipIdx.find? fun ((e, t), _) => !(t || holdsIn I slots e == some true) with
      | none => return (true, 0, slots, known, left)
      | some (_, k) => return (false, conflictOf i 0 [reads[k]!], slots, known, left)
  let (found, _, slots, _, left) := go 0 seed slots rootTrue budget
  if !found then return (none, budget - left)
  -- The values found, added in the order of `p.vars`, the order in which
  -- the search chose them.
  return (some <| p.vars.zipIdx.foldl (init := env) fun env ((x, _), i) =>
    if env.contains x then env else match slots[varSlot[i]!]! with
      | some v => env.insert x v
      | none => env, budget - left)

/-- Values for `p.vars`, extending `env`, that make every constraint
`true` under `I`, within `budget` steps (`Problem.search`). -/
def Problem.solve (sp : Spec) (w : World) (I : Interp) (p : Problem) (env : Env) (budget : Nat := 4000) :
    R (Option Env) :=
  (·.1) <$> p.search sp w I env budget

/-- The integers that `atoms` mention, their neighbours, and a few small
ones. -/
def intsOf (atoms : Array Atom) : Array Int := Id.run do
  let mut out : Array Int := #[-1, 0, 1, 2]
  for a in atoms do
    for i in a.e.lits do
      for j in [i - 1, i, i + 1] do
        unless out.contains j do out := out.push j
  return out

/-- The strings in `v`, a value of a literal or constant. -/
partial def Val.strs : Val → Array String
  | .str s => #[s]
  | .set ms | .seq ms => ms.flatMap (·.strs)
  | .pair a b => a.strs ++ b.strs
  | .ctor _ _ args => args.flatMap (·.strs)
  | _ => #[]

/-- The string literals of `e`, and the patterns of its `matches?`, which
are not literals of strings that it constrains. -/
partial def Ex.strLits : Ex → Array String × Array String
  | .lit v => (v.strs, #[])
  | .var _ | .slot _ | .bound _ | .boundAt _ | .shared _ | .known _ => (#[], #[])
  | .memo lets e => join (lets.push e)
  | .lifted lets e => join (lets.flatten.push e)
  | .dispatch _ m => m.strLits
  | .method .matches r #[.lit (.str p)] | .matches r p _ => let (ls, ps) := r.strLits; (ls, ps.push p)
  | .not a | .neg a | .field a _ | .card a | .pre _ _ _ a => a.strLits
  | .bin _ a b | .when _ a b | .pair a b | .index a b _ _ => join #[a, b]
  | .ite c a b => join #[c, a, b]
  | .app _ args | .cardinality _ args | .ctor _ _ args | .setLit args | .seqLit args => join args
  | .method _ r args => join (#[r] ++ args)
  | .match e arms .. =>
    let (ls, ps) := join (#[e] ++ arms.flatMap fun (_, g?, b) => g?.toArray.push b)
    (ls ++ arms.flatMap (·.1.strLits), ps)
  | .update e fs => join (#[e] ++ fs.map (·.2))
  | .quant _ _ _ _ ds _ b => join (ds.flatMap (·.toArray) |>.push b)
  | .range lo hi => join #[lo, hi]
  | .table _ rows _ => join (rows.flatMap fun (_, c?, v) => c?.toArray.push v)
  | .const _ e => e.strLits
  | .typed _ _ e => e.strLits
where
  join (es : Array Ex) : Array String × Array String :=
    es.foldl (fun (ls, ps) e => let (l, p) := e.strLits; (ls ++ l, ps ++ p)) (#[], #[])

/-- A random string that matches `r`, if one was found within `fuel`
steps: each repetition repeats at most twice. -/
partial def Re.sample (fuel : Nat := 40) : Fren.Core.Re → R (Option (List Char))
  | .none => return none
  | .str cs => return some cs
  | .any => return some ['a']
  | .cls false rs => do
    let some (lo, hi) := rs[← below rs.length]? | return none
    return some [Char.ofNat (lo.toNat + (← below (hi.toNat - lo.toNat + 1)))]
  | .cls true rs => do
    -- One of a few characters outside the ranges, at random.
    let out := ['a', 'A', '0', ' ', '.', '-', '_', '?', '\''].filter (!Fren.Core.inRanges rs ·)
    return out[← below out.length]?.map ([·])
  | .union a b => do
    let (x, y) := if (← below 2) == 0 then (a, b) else (b, a)
    match ← Re.sample fuel x with
    | some cs => return some cs
    | none => Re.sample fuel y
  | .cat a b => do
    let some xs ← Re.sample fuel a | return none
    let some ys ← Re.sample fuel b | return none
    return some (xs ++ ys)
  | .star a => do
    let mut out := []
    let n ← if fuel == 0 then pure 0 else below 3
    for _ in [0:n] do
      let some cs ← Re.sample (fuel - 1) a | break
      out := out ++ cs
    return some out

/-- The strings that `atoms` mention, each also with `"a"` before and after
it, and, if it is short, its proper suffixes; and a few random strings that
match each of their patterns, each also followed by `"a"`
(`Reqs/Eval#searching-for-behaviours`). -/
def stringsOf (atoms : Array Atom) : R (Array String) := do
  let (lits, pats) := atoms.foldl (fun (ls, ps) a => let (l, p) := a.e.strLits; (ls ++ l, ps ++ p)) (#[], #[])
  let mut out : Array String := #[]
  let add (out : Array String) (s : String) := if out.contains s then out else out.push s
  for s in lits do
    for t in [s, "a" ++ s, s ++ "a"] do out := add out t
    -- What remains after a short literal's first characters, such as the
    -- `:*` of `::*`.
    if s.length ≤ 6 then
      for k in [1:s.length] do out := add out (s.drop k).toString
  for p in pats do
    let .ok r := Fren.Core.parseRe p | continue
    for _ in [0:8] do
      if let some cs ← Re.sample 40 r then
        for t in [String.ofList cs, String.ofList cs ++ "a"] do out := add out t
  return out

/-- `sp`, remembering whether each of `strs`, and each string that a
string's candidates add (`smallValues`), matches each pattern of
`atoms` that parses (`Spec.matchMemo`). Each answer is a thunk of
`Fren.Core.Re.matches` of the pattern's parse, which is the pattern that
`Ex.matches` holds (`lowerExpr`), so it is the answer that matching
gives, computed at most once. -/
def Spec.withMatchMemo (sp : Spec) (atoms : Array Atom) (strs : Array String) : Spec := Id.run do
  let pats := atoms.foldl (fun ps a => ps ++ a.e.strLits.2) #[]
  let strs := strs ++ #["", "a", "b"]
  let mut memo := sp.matchMemo
  for p in pats do
    if memo.contains p then continue
    let .ok re := Fren.Core.parseRe p | continue
    memo := memo.insert p (strs.foldl (init := {}) fun m s => m.insert s (Thunk.mk fun _ => re.matches s))
  return { sp with matchMemo := memo }

/-- `sp`, with the body of each structural recursion compiled
(`Ex.compile`) for interpretations whose shapes are `shapes`, as every
search's are (`World.interp`). An application binds the parameters in a
frame of their own, the first innermost (`paramFrame`), so the body reads
each by its position there, as `Ex.compile` resolves a binder that its
scope names; it gives the same value from that frame as the body did. -/
def Spec.withCompiledRecs (sp : Spec) (shapes : Name → Option Fren.Core.DataShape) : Spec :=
  { sp with recDefs := sp.recDefs.foldl (init := sp.recDefs) fun m f (ps, b) => m.insert f (ps, b.compile shapes (some ps.toList)) }

/-- The defined outputs of `c` that the inputs alone give, in an order in
which each mentions only inputs and earlier such outputs. Members may
come in any order, so a definition may mention an output defined after
it: each pass adds those whose definitions mention only what is known,
until one adds none. -/
def Comp.earlyDefs (c : Comp) : Array Name := Id.run do
  let mut known := (c.vars.filter (·.role == .input)).map (·.name)
  let mut out := #[]
  for _ in [0:c.defs.size] do
    let before := out.size
    for (d, e) in c.defs do
      if !out.contains d && e.vars.all known.contains then
        known := known.push d
        out := out.push d
    if out.size == before then break
  return out

/-- The variables of `c` nested at `pfx` in the order the search chooses
them (`Reqs/Eval#searching-for-behaviours`): its inputs, the defined
outputs that they give, each call's variables, then its other
outputs. -/
partial def Spec.order (sp : Spec) (c : Comp) (pfx : Name := .anonymous) : Array (Name × VTy) :=
  let early := c.earlyDefs
  let own (keep : Var → Bool) := c.vars.filter keep |>.map fun v => (pfx ++ v.name, v.ty)
  own (·.role == .input) ++ own (fun v => early.contains v.name)
    ++ c.insts.flatMap (fun i => match sp.comp? i.comp with
      | some d => sp.order d (pfx ++ i.name)
      | none => #[])
    ++ own fun v => v.role == .output && !early.contains v.name

end FrenCli.Eval
