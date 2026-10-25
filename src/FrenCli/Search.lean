-- keep-sorted start
import FrenCli.Eval
import Std.Data.HashMap
-- keep-sorted end

/-!
# Searching for behaviours (`Reqs/Eval#searching-for-behaviours`)

A random, backtracking search for values of variables that make a set of
constraints (`Eval.Atom`) true. Each variable's candidates are tried in a
random order, and a branch is abandoned as soon as a constraint is
`false`. The search is incomplete, but whatever it returns has been
evaluated.
-/

open Lean

namespace FrenCli.Eval

/-- SplitMix64. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (g : Rng) : UInt64 × Rng :=
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
random `j ≤ i`. -/
def shuffle (xs : Array α) : R (Array α) := do
  let mut xs := xs
  let mut i := xs.size
  while i > 0 do
    i := i - 1
    let j ← below (i + 1)
    xs := xs.swapIfInBounds i j
  return xs

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
  | .data p => Id.run do
    let some d := sp.data.find? p | return .ctor p 0 #[]
    -- Below the depth, only constructors without the type in their fields.
    let ok := if depth == 0 then d.ctors.filter (·.fields.all (·.2 != .data p)) else d.ctors
    let cs := if ok.isEmpty then d.ctors else ok
    let i := (h % cs.size.toUInt64).toNat
    let c := cs[i]!
    let idx := (d.ctors.findIdx? (·.name == c.name)).getD 0
    let args := c.fields.mapIdx fun k (_, t) => valueOf sp w (mix h (k.toUInt64 + 1)) (depth - 1) t
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

def World.interp (sp : Spec) (w : World) : Interp where
  fn f args := do
    let (_, r) ← sp.funs.find? f
    let h := args.foldl (fun h a => mix h (hashVal a)) (mix w.seed (hash f))
    return valueOf sp w h 2 r

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
  | .lit _ | .var _ | .slot _ | .bound _ => #[]
  | .not a | .neg a | .field a _ => a.lits
  | .bin _ a b | .when _ a b => a.lits ++ b.lits
  | .ite c a b => c.lits ++ a.lits ++ b.lits
  | .app _ args | .cardinality _ args | .ctor _ _ args => args.flatMap (·.lits)
  | .method _ r args => r.lits ++ args.flatMap (·.lits)
  | .matches r _ _ => r.lits
  | .setLit es => es.flatMap (·.lits)
  | .pair a b | .index a b _ => a.lits ++ b.lits
  | .seqLit es => es.flatMap (·.lits)
  | .card e => e.lits
  | .match e arms => e.lits ++ arms.flatMap fun (p, b) => p.lits ++ b.lits
  | .update e fs => e.lits ++ fs.flatMap (·.2.lits)

/-- The expressions that `e`, a constraint over the search's environment
(`Ex.slot`), equates the variable at index `x` with. -/
partial def Ex.equated (x : Nat) : Ex → Array Ex
  | .bin .eq (.slot y) e | .bin .iff (.slot y) e => (if y == x then #[e] else #[]) ++ e.equated x
  | .bin .eq e (.slot y) | .bin .iff e (.slot y) => (if y == x then #[e] else #[]) ++ e.equated x
  | .lit _ | .var _ | .slot _ | .bound _ => #[]
  | .not a | .neg a | .field a _ => a.equated x
  | .bin _ a b | .when _ a b => a.equated x ++ b.equated x
  | .ite c a b => c.equated x ++ a.equated x ++ b.equated x
  | .app _ args | .cardinality _ args | .ctor _ _ args => args.flatMap (·.equated x)
  | .method _ r args => r.equated x ++ args.flatMap (·.equated x)
  | .matches r _ _ => r.equated x
  | .setLit es => es.flatMap (·.equated x)
  | .pair a b | .index a b _ => a.equated x ++ b.equated x
  | .seqLit es => es.flatMap (·.equated x)
  | .card e => e.equated x
  | .match e arms => e.equated x ++ arms.flatMap (·.2.equated x)
  | .update e fs => e.equated x ++ fs.flatMap (·.2.equated x)

/-- Every value of `ty` up to `depth`, at most `cap` of them. -/
partial def smallValues (sp : Spec) (w : World) (ints : Array Int) (strs : Array String) (cap : Nat) (depth : Nat) :
    VTy → Array Val
  | .bool => #[.bool false, .bool true]
  | .int => ints.map .int
  | .nat => (ints.filter (0 ≤ ·)).map .int
  -- The strings of the constraints (`stringsOf`) first, so that sets
  -- and sequences of strings, which take the first few, have them; then a
  -- few others. Constraints that equate a variable with a string give the
  -- rest.
  | .string => (strs ++ #["", "a", "b"].filter (!strs.contains ·)).map .str
  -- The empty set and singletons; constraints that equate a variable with a
  -- set give the others.
  | .set t => #[.set #[]] ++ ((smallValues sp w ints strs cap depth t).extract 0 4).map (Val.setOf #[·])
  -- The empty sequence, singletons and pairs of candidates, so that
  -- indexes at `0` and `1` have something to read.
  | .seq t => Id.run do
    let vs := (smallValues sp w ints strs cap depth t).extract 0 3
    return #[.seq #[]] ++ vs.map (Val.seq #[·]) ++ (vs.zip (vs.extract 1)).map fun (a, b) => .seq #[a, b]
  -- The empty relation, single pairs, and a chain of pairs, so that
  -- `closure` has something to close.
  | .rel a b => Id.run do
    let as := (smallValues sp w ints strs cap depth a).extract 0 3
    let bs := (smallValues sp w ints strs cap depth b).extract 0 3
    let pairs := as.flatMap fun x => bs.map (Val.pair x ·)
    let mut out := #[.set #[]] ++ (pairs.extract 0 6).map (Val.setOf #[·])
    if a == b && as.size ≥ 3 then
      out := out.push (Val.setOf #[.pair as[0]! as[1]!, .pair as[1]! as[2]!])
    return out
  | .abstract s => (Array.range (w.size s)).map (.abs s)
  | .data p => Id.run do
    let some d := sp.data.find? p | return #[]
    let mut out := #[]
    for c in d.ctors, idx in [0:d.ctors.size] do
      if depth == 0 && !c.fields.isEmpty then continue
      let mut combos : Array (Array Val) := #[#[]]
      for (_, t) in c.fields do
        let vs := smallValues sp w ints strs cap (depth - 1) t
        combos := (combos.flatMap fun pre => vs.map pre.push).extract 0 cap
      out := out ++ combos.map (.ctor p idx ·)
    return out.extract 0 cap

/-- The variables of `e`. -/
partial def Ex.vars : Ex → Array Name
  | .var n => #[n]
  | .lit _ | .slot _ | .bound _ => #[]
  | .not a | .neg a | .field a _ | .card a => a.vars
  | .bin _ a b | .when _ a b | .pair a b | .index a b _ => a.vars ++ b.vars
  | .ite c a b => c.vars ++ a.vars ++ b.vars
  | .app _ args | .cardinality _ args | .ctor _ _ args | .setLit args | .seqLit args => args.flatMap (·.vars)
  | .method _ r args => r.vars ++ args.flatMap (·.vars)
  | .matches r _ _ => r.vars
  | .match e arms => e.vars ++ arms.flatMap (·.2.vars)
  | .update e fs => e.vars ++ fs.flatMap (·.2.vars)

structure Problem where
  /-- The variables to choose, in order, with their types. -/
  vars : Array (Name × VTy)
  /-- What must hold. -/
  atoms : Array Atom
  /-- The integers that the constraints mention, and their neighbours. -/
  ints : Array Int := #[]
  /-- The strings that the constraints mention or match (`stringsOf`). -/
  strs : Array String := #[]

abbrev Env := Std.HashMap Name Val

def Env.look (env : Env) : Look := fun n => env[n]?

/-- The values of a search's variables, by index (`Ex.slot`), as far as
they are known. -/
abbrev Slots := Array (Option Val)

/-- The candidates for a variable of type `ty`, given `equated`, what the
constraints equate it with, over the search's environment `slots`. -/
def Problem.candidates (sp : Spec) (w : World) (I : Interp) (p : Problem) (slots : Slots) (ty : VTy)
    (equated : Array Ex) : R (Array Val) := do
  -- Values that a constraint equates the variable with, first.
  let eqs := equated.filterMap (·.eval I (fun _ => none) [] slots)
  let mut ints := p.ints
  for _ in [0:2] do ints := ints.push (((← below 41) : Int) - 20)
  let mut pool := smallValues sp w ints p.strs 24 2 ty
  -- Longer sequences, of the lengths that the constraints mention.
  if let .seq t := ty then
    let elems := smallValues sp w ints p.strs 24 2 t
    unless elems.isEmpty do
      for n in (ints.filterMap fun i => if 3 ≤ i && i ≤ 4 then some i.toNat else none).toList.eraseDups do
        for _ in [0:6] do
          pool := pool.push (.seq (← (Array.range n).mapM fun _ => do return elems[← below elems.size]!))
  pool ← shuffle pool
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

/-- Values for `p.vars`, extending `env`, that make every constraint
`true` under `I`, within `budget` steps. `w` gives the candidates of the
abstract types.

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
branch and unmarked after it. -/
partial def Problem.solve (sp : Spec) (w : World) (I : Interp) (p : Problem) (env : Env) (budget : Nat := 4000) :
    R (Option Env) := do
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
  let varSlot := p.vars.map fun (x, _) => index[x]!
  let slots : Slots := names.map (env[·]?)
  -- Each constraint's value in `env`. A constraint that is `true` stays
  -- so on that branch (evaluation is monotone), and is not evaluated again.
  let atRoot := full.map (holdsIn I slots ·)
  let rootViable := !atRoot.any (· == some false)
  let rootTrue := atRoot.map (· == some true)
  -- The constraints that become `true` when the variable `x`, by index,
  -- gets its value in `slots`, or `none` if one becomes `false`.
  let viable (slots : Slots) (x : Nat) (known : Array Bool) : Option (Array Nat) := Id.run do
    if !rootViable then
      return if full.any (holdsIn I slots · == some false) then none else some #[]
    let mut newly := #[]
    for k in byVar[x]! do
      if known[k]! then continue
      match holdsIn I slots full[k]! with
      | some false => return none
      | some true => newly := newly.push k
      | none => pure ()
    return some newly
  -- What the constraints equate each variable with, computed when the
  -- search first reaches it.
  let equated : Array (Thunk (Array Ex)) := varSlot.map fun x => Thunk.mk fun _ => full.flatMap (·.equated x)
  -- Returns whether it found values, with `slots` and `known` as they were
  -- given if it did not, and with the values found if it did.
  let rec go (i : Nat) (slots : Slots) (known : Array Bool) (left : Nat) : R (Bool × Slots × Array Bool × Nat) := do
    if left == 0 then return (false, slots, known, 0)
    if h : i < p.vars.size then
      let (_, ty) := p.vars[i]
      let x := varSlot[i]!
      if slots[x]!.isSome then return ← go (i + 1) slots known left
      let mut left := left
      let mut slots := slots
      let mut known := known
      for v in ← p.candidates sp w I slots ty (equated[i]?.map (·.get) |>.getD #[]) do
        if left == 0 then break
        left := left - 1
        slots := slots.set! x (some v)
        if let some newly := viable slots x known then
          for k in newly do known := known.set! k true
          let (found, slots', known', l) ← go (i + 1) slots known left
          slots := slots'
          known := known'
          left := l
          if found then return (true, slots, known, left)
          for k in newly do known := known.set! k false
      return (false, slots.set! x none, known, left)
    else
      let all := (full.zip known).all fun (e, t) => t || holdsIn I slots e == some true
      return (all, slots, known, left)
  let (found, slots, _, _) ← go 0 slots rootTrue budget
  if !found then return none
  -- The values found, added in the order of `p.vars`, the order in which
  -- the search chose them.
  return some <| p.vars.zipIdx.foldl (init := env) fun env ((x, _), i) =>
    if env.contains x then env else match slots[varSlot[i]!]! with
      | some v => env.insert x v
      | none => env

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
  | .var _ | .slot _ | .bound _ => (#[], #[])
  | .method .matches r #[.lit (.str p)] | .matches r p _ => let (ls, ps) := r.strLits; (ls, ps.push p)
  | .not a | .neg a | .field a _ | .card a => a.strLits
  | .bin _ a b | .when _ a b | .pair a b | .index a b _ => join #[a, b]
  | .ite c a b => join #[c, a, b]
  | .app _ args | .cardinality _ args | .ctor _ _ args | .setLit args | .seqLit args => join args
  | .method _ r args => join (#[r] ++ args)
  | .match e arms =>
    let (ls, ps) := join (#[e] ++ arms.map (·.2))
    (ls ++ arms.flatMap (·.1.strLits), ps)
  | .update e fs => join (#[e] ++ fs.map (·.2))
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
outputs that they give, each instance's variables, then its other
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
