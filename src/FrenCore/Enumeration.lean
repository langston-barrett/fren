-- keep-sorted start
import FrenCore.Check
import FrenCore.Evidence
import FrenCore.PatternTypes
-- keep-sorted end

/-!
# Checking by enumeration (`Reqs/Check#checking-by-enumeration`)

A size-ordered enumerator of values, in the style of SmallCheck: each type
is unfolded, for a size bound `n`, into a `Shape`, a finite tree, whose
values of size at most `n` `Shape.vals` lists, each once, and `Shape.ordered`
lists smallest first. A procedure's checks are then decided by the shared
check algorithms (`Fren.Core.checkComp`) with a backend (`backend`) that
answers each query by searching the assignments of its variables, smallest
first and fairly (`search`): by the largest size of a variable's value, then
in the order of the variables and of each one's values. The formulas are
`EF`s, over *atoms*, the formulas of the procedure, which each front end
evaluates in its own terms: the `fren` command with its evaluator, and the
Lean-hosted front end by Lean's evaluation of the generated propositions.
So the two front ends ask the same queries, search them in the same order
and report the same first model.
-/

namespace Fren.Core.Enumeration

open Lean (Name)

/-! ## Values and shapes -/

/-- A value as the enumerator builds it: a `Bool`, an integer, the `k`th
value of an abstract type, or the variant `idx` of an enumeration, with its
payload, or a record or newtype, as its one constructor `0`, with its
fields. -/
inductive EVal where
  | bool (b : Bool)
  | int (i : Int)
  | abs (k : Nat)
  | ctor (idx : Nat) (args : List EVal)
  deriving Inhabited, Repr

/-- The value as a value of a pattern, if it has no abstract value in it. -/
partial def EVal.toPVal? : EVal → Option PVal
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .abs _ => none
  | .ctor idx args => do return .ctor idx (← args.mapM EVal.toPVal?).toArray

/-- Whether a declared constraint needs semantic evaluation beyond Shape's
literal-pattern filters. Function-result tables with such constraints require
an additional world filter; frontends must not silently use unconstrained tables. -/
partial def needsSemanticFilter (shapeOf : Name → Option DataShape) (t : PTy) (seen : List Name := []) : Bool :=
  let own := !t.invariants.isEmpty && (t.invariants.size != 1 || t.pat?.isNone)
  let nested := t.elems.any (needsSemanticFilter shapeOf · seen)
  let fields := match t.ty with
    | .record path _ | .enum path _ | .newtype path _ =>
      !seen.contains path && ((shapeOf path).any fun shape => (shape.inst t.parts).parts.any
        (·.any (needsSemanticFilter shapeOf · (path :: seen))))
    | _ => false
  own || nested || fields

mutual
/-- A type, unfolded for a size bound: a finite tree, whose recursive
enumerations are unfolded as deep as the bound allows
(`Reqs/Check#sizes-and-order`). -/
inductive Shape where
  | bool
  /-- `Int`: `i` has size `|i|`. -/
  | int
  /-- `Nat`: `k` has size `k`. -/
  | nat
  /-- A finite integer pattern type: its integers, in increasing order, each
  of size 0. -/
  | ints (vs : List Int)
  /-- An abstract type: its `k`th value has size `k`. -/
  | abstract
  /-- An enumeration: a variant without a payload has size 0, and one with
  a payload one more than the largest of its values'. -/
  | ctors (cs : Ctors)
  /-- A record, or a newtype: the largest size of its fields. -/
  | record (fs : Shapes)
  /-- A pattern type of the shape `s`: its values that `keep` keeps. -/
  | filter (s : Shape) (keep : EVal → Bool)
  /-- No values: a payload beyond the bound. -/
  | empty

/-- The shapes of a payload's values, or of a record's fields. -/
inductive Shapes where
  | nil
  | cons (s : Shape) (rest : Shapes)

/-- The variants of an enumeration, each with the shapes of its payload. -/
inductive Ctors where
  | nil
  | cons (payload : Shapes) (rest : Ctors)
end

instance : Inhabited Shape := ⟨.empty⟩

/-- The product of `xs` and `rest`, the first varying slowest, with the
largest of the sizes. -/
def prodWith (xs : List (EVal × Nat)) (rest : List (List EVal × Nat)) : List (List EVal × Nat) :=
  xs.flatMap fun (v, k) => rest.map fun (vs, l) => (v :: vs, max k l)

/-- What kind of value a size is of (`check::value_size`). -/
inductive SizeKind where
  | bool
  | int
  | nat
  /-- An integer of a finite integer pattern type. -/
  | finiteInt
  | abstract
  /-- A variant without a payload. -/
  | nullary
  /-- A variant with a payload. -/
  | variant
  /-- A record or a newtype. -/
  | record
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The size of a value (`check::value_size`): of an integer `i`, its
magnitude, and of a `Nat` or the `i`th value of an abstract type, `i`;
of a variant with a payload, one more than `largest`, the largest of its
payload's values' sizes, and of a record, `largest`, its fields'; and of
anything else 0. -/
def valueSize : SizeKind → Int → Nat → Nat
  | .int, i, _ => i.natAbs
  | .nat, i, _ => i.toNat
  | .abstract, i, _ => i.toNat
  | .variant, _, largest => largest + 1
  | .record, _, largest => largest
  | _, _, _ => 0

/-- The integers of size at most `n`, by size: `0, 1, -1, 2, -2, ...`. -/
def intsUpTo (n : Nat) : List Int :=
  (List.range (n + 1)).flatMap fun (k : Nat) => if k = 0 then [(0 : Int)] else [(k : Int), -(k : Int)]

mutual
/-- Every value of `s` of size at most `n`, each with its size, once, in
the structural order: variants in order, and payloads and fields by their
values' order, the first varying slowest (`Reqs/Check#sizes-and-order`). -/
def Shape.vals : Shape → Nat → List (EVal × Nat)
  | .bool, _ => [(.bool false, valueSize .bool 0 0), (.bool true, valueSize .bool 1 0)]
  | .int, n => (intsUpTo n).map fun i => (.int i, valueSize .int i 0)
  | .nat, n => (List.range (n + 1)).map fun (k : Nat) => (.int (k : Int), valueSize .nat k 0)
  | .ints vs, _ => vs.map fun i => (.int i, valueSize .finiteInt i 0)
  | .abstract, n => (List.range (n + 1)).map fun (k : Nat) => (.abs k, valueSize .abstract k 0)
  | .ctors cs, n => cs.vals 0 n
  | .record fs, n => (fs.vals n).map fun (vs, k) => (.ctor 0 vs, valueSize .record 0 k)
  | .filter s keep, n => (s.vals n).filter fun (v, _) => keep v
  | .empty, _ => []

/-- Every combination of values of `ss` of sizes at most `n`, with the
largest of their sizes. -/
def Shapes.vals : Shapes → Nat → List (List EVal × Nat)
  | .nil, _ => [([], 0)]
  | .cons s rest, n => prodWith (s.vals n) (rest.vals n)

/-- Every value of the variants `cs`, the first numbered `i`, of size at
most `n`. -/
def Ctors.vals : Ctors → Nat → Nat → List (EVal × Nat)
  | .nil, _, _ => []
  | .cons .nil rest, i, n => (.ctor i [], valueSize .nullary i 0) :: rest.vals (i + 1) n
  | .cons ps rest, i, n =>
    (match n with
      | 0 => []
      | m + 1 => (ps.vals m).map fun (vs, k) => (.ctor i vs, valueSize .variant i k)) ++ rest.vals (i + 1) n
end

/-- Every value of `s` of size at most `n`, smallest first, and in the
structural order among those of a size (`Reqs/Check#sizes-and-order`). -/
def Shape.ordered (s : Shape) (n : Nat) : List (EVal × Nat) :=
  let vs := s.vals n
  (List.range (n + 1)).flatMap fun k => vs.filter (·.2 == k)

mutual
/-- Whether every value of `s` has size at most `n`, so that `Shape.vals`
lists every value of the type it stands for: `s` has no value of size
`n + 1`, being finite, and, if it was unfolded for the bound `n`, no
variant was cut off. -/
def Shape.exhausted : Shape → Nat → Bool
  | .bool, _ | .ints _, _ | .empty, _ => true
  | .int, _ | .nat, _ | .abstract, _ => false
  | .ctors cs, n => cs.exhausted n
  | .record fs, n => fs.exhausted n
  | .filter s _, n => s.exhausted n

def Shapes.exhausted : Shapes → Nat → Bool
  | .nil, _ => true
  | .cons s rest, n => s.exhausted n && rest.exhausted n

def Ctors.exhausted : Ctors → Nat → Bool
  | .nil, _ => true
  | .cons .nil rest, n => rest.exhausted n
  | .cons ps rest, n => (match n with | 0 => false | m + 1 => ps.exhausted m) && rest.exhausted n
end

/-! ## Shapes of declared types -/

/-- Why a type cannot be enumerated (`Reqs/Check#enumerable-types`). -/
def notEnumerable (t : PTy) : String :=
  s!"`{if t.text.isEmpty then t.ty.show else t.text}`"

/-- The shape of the declared type `t` for the bound `n`
(`Reqs/Check#enumerable-types`): `Bool`, `Int`, `Nat`, enumerations,
records, newtypes, instances of generic types, pattern types and abstract
types are enumerable; strings, sets, relations and sequences are not, nor
any type with one within it. `shapes` gives what is known of each record,
newtype and enumeration. A recursive enumeration is unfolded `n` deep. -/
partial def shapeOf (shapes : Name → Option DataShape) (n : Nat) (t : PTy) : Except String Shape := do
  let keep (p : Pat) : EVal → Bool := fun v => match v.toPVal? with
    | some pv => p.matchesVal pv
    | none => true
  let base : Shape ← match t.ty with
    | .bool => pure .bool
    | .int | .nat =>
      let nat := t.ty == .nat
      match t.pat? with
      | none => pure (if nat then .nat else .int)
      | some p =>
        -- A finite integer pattern type: all of its integers, of size 0.
        match p.intCount? (if nat then some 0 else none), Pat.intValues? p with
        | some _, some vs => return .ints (vs.toList.filter fun i => !nat || 0 ≤ i)
        -- A `Nat` pattern bounded only above, as `Nat is ..=5`: from 0 to
        -- its largest bound.
        | some _, none =>
          let top := (p.bounds.foldl max 0).toNat
          return .ints (((List.range (top + 1)).map fun (k : Nat) => (k : Int)).filter fun i => p.matchesVal (.int i))
        | _, _ => pure (if nat then .nat else .int)
    | .abstract _ => pure .abstract
    | .enum p _ | .record p _ | .newtype p _ =>
      let some d := shapes p | throw (notEnumerable t)
      let d := d.inst t.parts
      let parts (m : Nat) (ts : Array PTy) : Except String Shapes :=
        ts.toList.foldrM (init := .nil) fun pt acc => return .cons (← shapeOf shapes m pt) acc
      if d.isRecord || d.isNewtype then
        pure (.record (← parts n (d.parts[0]?.getD #[])))
      else
        let cs ← d.parts.toList.foldrM (init := Ctors.nil) fun ts acc => do
          if ts.isEmpty then return .cons .nil acc
          match n with
          -- Beyond the bound: a payload of no values, which still marks
          -- the variant as having one.
          | 0 => return .cons (.cons .empty .nil) acc
          | m + 1 => return .cons (← parts m ts) acc
        pure (.ctors cs)
    | _ => throw (notEnumerable t)
  -- A pattern type that is not a finite integer one: its base's values that match.
  match t.pat?, base with
  | some _, .ints _ => return base
  | some p, s => return .filter s (keep p)
  | none, s => return s

/-- How many values of size at most `n` a shape has. -/
def Shape.count (s : Shape) (n : Nat) : Nat := (s.vals n).length

/-! ## Random values, for testing beyond the bound -/

/-- How many variants there are. -/
def Ctors.size : Ctors → Nat
  | .nil => 0
  | .cons _ rest => rest.size + 1

/-- A step of SplitMix64: the next state and a number. -/
def splitMix (state : UInt64) : UInt64 × UInt64 :=
  let s := state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

/-- A number below `n`, and the next state; 0 if `n` is 0. -/
def below (state : UInt64) (n : Nat) : Nat × UInt64 :=
  let (s, z) := splitMix state
  (if n == 0 then 0 else z.toNat % n, s)

mutual
/-- A random value of `s`, of size at most `m`, with its size, from the
state `st`; `none` where none was found in a few tries. -/
partial def Shape.random (s : Shape) (m : Nat) (st : UInt64) : Option (EVal × Nat) × UInt64 :=
  match s with
  | .bool => let (b, st) := below st 2; (some (.bool (b == 1), 0), st)
  | .int =>
    let (k, st) := below st (m + 1)
    let (neg, st) := below st 2
    let i : Int := if neg == 1 then -(k : Int) else k
    (some (.int i, valueSize .int i 0), st)
  | .nat => let (k, st) := below st (m + 1); (some (.int k, valueSize .nat k 0), st)
  | .ints vs => let (k, st) := below st vs.length; ((vs[k]?).map fun i => (.int i, 0), st)
  | .abstract => let (k, st) := below st (m + 1); (some (.abs k, valueSize .abstract k 0), st)
  | .ctors cs =>
    let (k, st) := below st cs.size
    cs.random k 0 m st
  | .record fs =>
    let (r, st) := fs.random m st
    (r.map fun (vs, k) => (.ctor 0 vs, valueSize .record 0 k), st)
  | .filter s keep =>
    let rec go (tries : Nat) (st : UInt64) : Option (EVal × Nat) × UInt64 :=
      match tries with
      | 0 => (none, st)
      | t + 1 =>
        let (r, st) := s.random m st
        match r with
        | some (v, k) => if keep v then (some (v, k), st) else go t st
        | none => go t st
    go 8 st
  | .empty => (none, st)

/-- Random values of each of `ss`, with the largest of their sizes. -/
partial def Shapes.random (ss : Shapes) (m : Nat) (st : UInt64) : Option (List EVal × Nat) × UInt64 :=
  match ss with
  | .nil => (some ([], 0), st)
  | .cons s rest =>
    let (a, st) := s.random m st
    let (b, st) := rest.random m st
    ((do let (v, k) ← a; let (vs, l) ← b; return (v :: vs, max k l)), st)

/-- A random value of the `k`th of the variants `cs`, the first numbered
`i`. -/
partial def Ctors.random (cs : Ctors) (k i m : Nat) (st : UInt64) : Option (EVal × Nat) × UInt64 :=
  match cs, k with
  | .nil, _ => (none, st)
  | .cons .nil _, 0 => (some (.ctor i [], valueSize .nullary i 0), st)
  | .cons ps _, 0 =>
    match m with
    | 0 => (none, st)
    | m' + 1 =>
      let (r, st) := ps.random m' st
      (r.map fun (vs, l) => (.ctor i vs, valueSize .variant i l), st)
  | .cons _ rest, k + 1 => rest.random k (i + 1) m st
end

/-- The largest size of the values that testing draws, beyond the bound `n`. -/
def testSize (n : Nat) : Nat := 10 * (n + 1)

/-- How many random tests a check set to `"enumerated+random"` runs. -/
def testCount : Nat := 100

/-- Up to `count` random values of the declared type `t` of size more than
the bound `n`, at most `testSize n`, from the state `st`, for testing
beyond the bound (`Reqs/Check#enumeration-then-testing`): none for a type
whose values are all within the bound. -/
def extrasOf (shapes : Name → Option DataShape) (n : Nat) (t : PTy) (count : Nat) (st : UInt64) :
    Array (EVal × Nat) := Id.run do
  let m := testSize n
  let .ok s := shapeOf shapes m t | return #[]
  let mut out := #[]
  let mut st := st
  for _ in [0:count] do
    -- A few tries for a value beyond the bound.
    for _ in [0:8] do
      let (r, st') := s.random m st
      st := st'
      if let some (v, k) := r then
        if k > n then
          out := out.push (v, k)
          break
  return out

/-! ## Formulas -/

/-- A formula of the check algorithms, as enumeration evaluates it: over
the procedure's formulas, its *atoms*, which a front end evaluates, and
over its variables' *slots*, each holding the position of its value in its
slot's values (`Space`). -/
inductive EF where
  /-- The procedure's `k`th atom. -/
  | atom (k : Nat)
  | tt
  | ff
  | not (f : EF)
  | conj (fs : Array EF)
  /-- `∃ outputs, f`, over the procedure's own outputs that are not
  defined. -/
  | exOutputs (f : EF)
  /-- The slot `x` holds the value `v`. -/
  | pin (x v : Nat)
  /-- The slot `x` holds one of the values `vs`: a variant's tester. -/
  | oneOf (x : Nat) (vs : List Nat)
  /-- `f` over the second copy of the variables. -/
  | primed (f : EF)
  /-- `x = x'`, for the variable `x`. -/
  | same (x : Name)
  deriving Inhabited, BEq, Hashable

/-- Where enumeration searches: a slot for each variable whose value is
enumerated, the procedure's own and its calls' that are not defined
outputs, in their order, then one for the second copy of each that
determinism copies, and last one for each type whose unspecified value
some atom reads, which an interpretation gives
(`Reqs/Check#checking-by-enumeration`). -/
structure Space where
  /-- Each slot's variable; a hidden slot's name is its type's. -/
  names : Array Name
  /-- The sizes of each slot's values, smallest first (`Shape.ordered`). -/
  sizes : Array (Array Nat)
  /-- The second copy of each slot, if determinism copies it. -/
  primeOf : Array (Option Nat)
  /-- The slots of the procedure's own outputs that are not defined, which
  `∃ outputs` ranges over. -/
  outputs : Array Nat
  /-- How many of the slots, at the end, are hidden: an interpretation's,
  not a variable's. -/
  hidden : Nat := 0
  /-- The bound. -/
  bound : Nat
  deriving Inhabited

/-- What a front end says of its atoms: the slots that each reads, the
defined outputs that each mentions, and how to evaluate each. -/
structure Atoms where
  slots : Array (Array Nat)
  defs : Array (Array Name) := #[]
  eval : Nat → Array Nat → Bool
  /-- Whether the defined output `d` has the same value in two
  assignments. -/
  sameDefined : Name → Array Nat → Array Nat → Bool := fun _ _ _ => true
  /-- The slots that each defined output's definition reads, through the
  definitions of the defined outputs that it mentions too. -/
  defSlots : Name → Array Nat := fun _ => #[]

instance : Inhabited Atoms := ⟨{ slots := #[], eval := fun _ _ => false }⟩

def Space.slotOf? (sp : Space) (n : Name) : Option Nat := sp.names.idxOf? n

/-- `env` with each copied slot holding its second copy's value. -/
def Space.primedEnv (sp : Space) (env : Array Nat) : Array Nat :=
  env.mapIdx fun i v => match sp.primeOf[i]?.join with
    | some p => env.getD p 0
    | none => v

/-- The slots that `f` reads, perhaps more than once. -/
def EF.slots (sp : Space) (ats : Atoms) : EF → List Nat
  | .atom k => (ats.slots[k]?.getD #[]).toList
  | .tt | .ff => []
  | .not f => f.slots sp ats
  | .conj fs => (fs.attach.toList.map fun ⟨f, _⟩ => f.slots sp ats).flatten
  | .exOutputs f => (f.slots sp ats).filter (!sp.outputs.contains ·)
  | .pin x _ => [x]
  | .oneOf x _ => [x]
  | .primed f => (f.slots sp ats).map fun x => (sp.primeOf[x]?.join).getD x
  | .same x => match sp.slotOf? x with
    | some s => s :: (sp.primeOf[s]?.join).toList
    | none =>
      -- A defined output: the slots that its definition reads, and their
      -- second copies.
      let ss := (ats.defSlots x).toList
      ss ++ ss.filterMap (sp.primeOf[·]?.join)

/-- `xs` without repeats, in order of first occurrence. -/
def dedup (xs : List Nat) : List Nat := xs.foldl (fun a x => if a.contains x then a else a ++ [x]) []

/-- The defined outputs that `f` mentions, each with whether it is the
second copy's. -/
partial def EF.defsOf (ats : Atoms) : EF → Array (Name × Bool)
  | .atom k => (ats.defs[k]?.getD #[]).map (·, false)
  | .not f | .exOutputs f => f.defsOf ats
  | .conj fs => fs.flatMap (·.defsOf ats)
  | .primed f => (f.defsOf ats).map fun (d, _) => (d, true)
  | .same x => #[(x, false), (x, true)]
  | _ => #[]

/-! ## Searching -/

/-- Every choice of a value for each of a list of slots, of `lims` values
each, in order, the last varying fastest (`check::fair_order`). -/
def lexAll : List Nat → List (List Nat)
  | [] => [[]]
  | l :: ls => (List.range l).flatMap fun j => (lexAll ls).map (j :: ·)

/-- The first choice, after `pre`, of a value for each of the slots with
`lims` values each, in the order of `lexAll`, each of whose prefixes `ok`
accepts as it is made: a prefix that `ok` refuses is not extended
(`check::search_first`). -/
def dfs (ok : List Nat → Bool) (pre : List Nat) : List Nat → Option (List Nat)
  | [] => some pre
  | l :: ls => (List.range l).findSome? fun j => if ok (pre ++ [j]) then dfs ok (pre ++ [j]) ls else none

/-- `base` with the slots `slots` holding the values `choice`. -/
def setAll (base : Array Nat) (slots choice : List Nat) : Array Nat :=
  (slots.zip choice).foldl (fun e (s, j) => e.set! s j) base

/-- After how many of `slots` are chosen a part that reads `ss` can be
tried: once the last of them is; 0 if it reads none of them. -/
def readyAt (slots ss : List Nat) : Nat :=
  ss.foldl (fun m s => if slots.contains s then max m (slots.idxOf s + 1) else m) 0

/-- Whether the parts `parts`, each with where it can be tried
(`readyAt`), that can be tried once `choice` is made, and not before,
hold in `base` with `slots` holding `choice`: each part is tried once,
as soon as it can be (`check::pruning`). -/
def newlyHold (base : Array Nat) (slots : List Nat) (parts : List (Nat × (Array Nat → Bool))) (choice : List Nat) : Bool :=
  let ready := parts.filter (·.1 == choice.length)
  ready.isEmpty || (let e := setAll base slots choice; ready.all (·.2 e))

/-- The first choice of values for `slots`, of `lims` values each, in the
order of `lexAll`, with which `base` makes `parts` true, each part tried
as soon as the slots it reads are chosen (`dfs`); `base` with it. -/
def firstChoice (base : Array Nat) (slots lims : List Nat) (parts : List (List Nat × (Array Nat → Bool))) :
    Option (Array Nat) :=
  let ps := parts.map fun (ss, f) => (readyAt slots ss, f)
  if newlyHold base slots ps [] then (dfs (newlyHold base slots ps) [] lims).map (setAll base slots) else none

/-- How many of the slot `s`'s values have size at most `k`: they are
smallest first, so these are the first. -/
def Space.within (sp : Space) (s k : Nat) : Nat :=
  ((sp.sizes[s]?.getD #[]).toList.takeWhile (· ≤ k)).length

/-- The value of `f` in `env`. -/
def EF.eval (sp : Space) (ats : Atoms) (env : Array Nat) : EF → Bool
  | .atom k => ats.eval k env
  | .tt => true
  | .ff => false
  | .not f => !f.eval sp ats env
  | .conj fs => fs.attach.all fun ⟨f, _⟩ => f.eval sp ats env
  | .exOutputs (.conj fs) =>
    -- Some values of the outputs make `f` true: searched with each
    -- conjunct tried as soon as it can be.
    let outs := sp.outputs.toList.filter fun o => (EF.conj fs).slots sp ats |>.contains o
    let lims := outs.map fun s => (sp.sizes[s]?.getD #[]).size
    (firstChoice env outs lims (fs.attach.toList.map fun ⟨g, _⟩ => (g.slots sp ats, fun e => g.eval sp ats e))).isSome
  | .exOutputs f =>
    let outs := sp.outputs.toList.filter fun o => (f.slots sp ats).contains o
    let lims := outs.map fun s => (sp.sizes[s]?.getD #[]).size
    (firstChoice env outs lims [(f.slots sp ats, fun e => f.eval sp ats e)]).isSome
  | .pin x v => env[x]? == some v
  | .oneOf x vs => (env[x]?.map vs.contains).getD false
  | .primed f => f.eval sp ats (sp.primedEnv env)
  | .same x => match sp.slotOf? x with
    | some s => match sp.primeOf[s]?.join with
      | some p => env[s]? == env[p]?
      | none => true
    | none => ats.sameDefined x env (sp.primedEnv env)

/-- The slots that `parts` read, in order. -/
def slotsOf (sp : Space) (ats : Atoms) (parts : Array EF) : List Nat :=
  (dedup (parts.toList.flatMap (·.slots sp ats))).mergeSort

/-- Each of `parts`, with the slots it reads, as a function of an
assignment. -/
def partsOf (sp : Space) (ats : Atoms) (parts : Array EF) : List (List Nat × (Array Nat → Bool)) :=
  parts.toList.map fun f => (f.slots sp ats, fun e => f.eval sp ats e)

/-- The size of the `j`th value of the slot `s`. -/
def Space.sizeAt (sp : Space) (s j : Nat) : Nat := (sp.sizes[s]?.getD #[])[j]?.getD 0

/-- That some of `slots` holds a value of size `k`, in an assignment: the
part that makes an assignment's level `k`. -/
def Space.levelPart (sp : Space) (slots : List Nat) (k : Nat) : List Nat × (Array Nat → Bool) :=
  (slots, fun e => slots.any fun s => sp.sizeAt s (e[s]?.getD 0) == k)

/-- The level of the choice `a` of values for `slots`: the largest size of
its values (`check::fair_order`). -/
def Space.levelOf (sp : Space) (slots a : List Nat) : Nat :=
  (slots.zip a).foldl (fun m (p : Nat × Nat) => max m (sp.sizeAt p.1 p.2)) 0

/-- The assignments of the slots `slots`, `lims k` values each at the
level `k`, by level, from 0 to `bound`, and in the order of `lexAll` within
a level, where `atLevel k` says that one is of level `k`
(`check::fair_order`). -/
def fairList (bound : Nat) (lims : Nat → List Nat) (atLevel : Nat → List Nat → Bool) : List (List Nat) :=
  (List.range (bound + 1)).flatMap fun k => (lexAll (lims k)).filter (atLevel k)

/-- The fair order of the assignments of `slots` up to the bound, set in
`base`: by level, the largest size of their values, then in the order of
the slots and of each slot's values, the last varying fastest. -/
def Space.fairList (sp : Space) (base : Array Nat) (slots : List Nat) : List (List Nat) :=
  Fren.Core.Enumeration.fairList sp.bound (fun k => slots.map (sp.within · k))
    (fun k a => (sp.levelPart slots k).2 (setAll base slots a))

/-- The first assignment of the slots that `parts` read that makes them
all true, smallest first and fairly (`Reqs/Check#searching`): the first
of `Space.fairList` (`check::search_first`), each level searched with
`firstChoice`. With the level. -/
def search (sp : Space) (ats : Atoms) (parts : Array EF) : Option (Array Nat × Nat) :=
  let ps := partsOf sp ats parts
  let slots := slotsOf sp ats parts
  let env0 := Array.replicate sp.names.size 0
  if slots.isEmpty then
    if ps.all (·.2 env0) then some (env0, 0) else none
  else
    (List.range (sp.bound + 1)).findSome? fun k =>
      (firstChoice env0 slots (slots.map (sp.within · k)) (ps ++ [sp.levelPart slots k])).map (·, k)

/-- Testing beyond the bound (`Reqs/Check#enumeration-then-testing`): for
each of `testCount` tests, an assignment of the slots that `parts` read,
each slot's value one of its random values beyond the bound, the `t`th for
test `t` (a second copy's, another), or, for a slot whose values are all
within it, one drawn from `seed`; the first that makes them all true. -/
def testSearch (sp : Space) (ats : Atoms) (parts : Array EF) (seed : UInt64) : Option (Array Nat) := Id.run do
  let ps := partsOf sp ats parts
  let slots := slotsOf sp ats parts
  let primes := sp.primeOf.filterMap id
  let mut st := seed
  for t in [0:testCount] do
    let mut env := Array.replicate sp.names.size 0
    for s in slots do
      let all := (sp.sizes[s]?.getD #[]).size
      let within := sp.within s sp.bound
      let extra := all - within
      if extra > 0 then
        let k := if primes.contains s then (t + extra / 2 + 1) % extra else t % extra
        env := env.set! s (within + k)
      else
        let (j, st') := below st all
        st := st'
        env := env.set! s j
    if ps.all (·.2 env) then return some env
  return none

/-- The answer to a query (`check::enumerated_answer`): the search's
model up to the bound, if it found one, else, if `testing`, testing's
beyond it; with whether it is testing's. -/
def answerOf (found? : Option α) (testing : Bool) (test : Unit → Option α) : Option (α × Bool) :=
  match found? with
  | some a => some (a, false)
  | none => if testing then (test ()).map (·, true) else none

/-! ## The backend -/

/-- A value of a model: its slot and the position of its value there, if
it is enumerated rather than a defined output's, and the value as Fren
writes it. -/
structure EV where
  at? : Option (Nat × Nat)
  shown : String
  /-- Exact assignment, including hidden function tables, for observations. -/
  environment? : Option (Array Nat) := none
  deriving Inhabited

/-- The checks' backend over the space `sp`, whose atoms are `ats`
(`Reqs/Check#checking-by-enumeration`): each query is answered by `search`,
`unsat` if no assignment within the bound refutes it, nor, with
`testing?`'s seed, any of `testSearch`'s, and otherwise `sat` with the
first that does, which gives the slots it reads, but the hidden
ones, and the defined outputs that its formulas mention, as `render` and
`defValue` show them. -/
def backend [Monad m] (sp : Space) (ats : Atoms) (render : Nat → Nat → m String)
    (defValue : Name → Array Nat → m (Option String)) (testing? : Option UInt64 := none)
    (variantOf : Nat → Nat → Option Variant := fun _ _ => none)
    (facts : Array EF := #[]) (outputFacts : Array EF := #[]) : Backend m EF EV where
  query hyps goal _ := do
    -- Type-domain facts hold in each copy, independently of named clauses.
    let domain := facts ++ facts.map EF.primed
    let parts := (domain ++ hyps.map (·.2)).push (.not goal)
    let found := answerOf ((search sp ats parts).map (·.1)) testing?.isSome fun _ =>
      testSearch sp ats parts (testing?.getD 0)
    match found with
    | none => return .unsat
    | some (env, _) =>
      let slots := slotsOf sp ats parts
      let shown ← (slots.toArray.filter (· < sp.names.size - sp.hidden)).mapM fun x => do
        return (sp.names[x]!, ({ at? := some (x, env[x]!), shown := ← render x env[x]! } : EV))
      let defs := (parts.flatMap (·.defsOf ats)).foldl (init := #[]) fun acc d => if acc.contains d then acc else acc.push d
      let defd ← defs.filterMapM fun (d, primed) => do
        let e := if primed then sp.primedEnv env else env
        return (← defValue d e).map fun v => (if primed then primed' d else d, ({ at? := none, shown := v } : EV))
      return .sat (shown ++ defd ++ #[(Lean.Name.mkSimple "#member_model", { at? := none, shown := "", environment? := some env })])
  modelBool? := some fun model formula => pure do
    let (_, token) ← model.find? (·.1 == Lean.Name.mkSimple "#member_model")
    let env ← token.environment?
    return formula.eval sp ats env
  falseF := .ff
  notF := .not
  conj := .conj
  existsOutputs f := pure (.exOutputs (if outputFacts.isEmpty then f else .conj (outputFacts.push f)))
  pin _ v := pure (v.at?.map fun (x, j) => .pin x j)
  -- That the slot holds a value of the same variant: one of those of its
  -- values that are.
  pinVariant _ v := pure do
    let (x, j) ← v.at?
    let k ← variantOf x j
    let n := (sp.sizes[x]?.getD #[]).size
    return (k, .oneOf x ((List.range n).filter fun i => variantOf x i == some k))
  render _ v := pure v.shown
  prime := .primed
  samePrimed := .same
  -- Defined outputs are computed, never enumerated.
  subst _ f := f
where
  primed' (n : Name) : Name := Fren.Core.primed n

/-- `c` with each formula an atom, numbered in the order of its fields, and
the formulas, in that order: each front end evaluates its own. A
definition's equation, and its term, always hold: defined outputs are
computed, not enumerated. The questions about tables, `match`es and
applications are atoms too; those about indexes are not enumerated
(`check::by_evidence`). -/
def _root_.Fren.Core.Comp.atoms (c : Comp F) : Comp EF × Array F := Id.run do
  let mut fs : Array F := #[]
  let mut next := 0
  let mut out : Comp EF := { path := c.path, vars := c.vars, assumes := #[], reqs := #[], expects := #[], triggers := #[]
                             typesInterpreted := c.typesInterpreted, fn? := c.fn?, inhabitation := c.inhabitation }
  let mut named : Array (Array (Name × EF)) := #[]
  for xs in #[c.assumes, c.reqs, c.expects, c.covers, c.triggers, c.posts] do
    let mut ys := #[]
    for (n, f) in xs do
      fs := fs.push f
      ys := ys.push (n, EF.atom next)
      next := next + 1
    named := named.push ys
  let mut insts := #[]
  for i in c.insts do
    fs := fs.push i.bindings
    let b := EF.atom next
    fs := fs.push i.behaviour
    let h := EF.atom (next + 1)
    next := next + 2
    let mut as := #[]
    for (n, f) in i.assumes do
      fs := fs.push f
      as := as.push (n, EF.atom next)
      next := next + 1
    insts := insts.push { name := i.name, comp := i.comp, bindings := b, behaviour := h, assumes := as, typed := i.typed }
  let mut tables := #[]
  for t in c.tables do
    fs := fs.push t.site.goal
    tables := tables.push { t with site := { t.site with goal := EF.atom next } }
    next := next + 1
  let mut groups := #[]
  for group in c.branchGroups do
    let mut members := #[]
    for member in group.members do
      fs := fs.push member.formula
      let formula := EF.atom next
      next := next + 1
      let value ← match member.valueFormula? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      let guard ← match member.evaluationGuard? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      members := members.push {
        name := member.name
        formula := formula
        valueFormula? := value
        evaluationGuard? := guard
        range? := member.range?
        text := member.text
      }
    let guard ← match group.guard? with
      | none => pure none
      | some f => do
        fs := fs.push f
        let atom := some (EF.atom next)
        next := next + 1
        pure atom
    groups := groups.push { owner := group.owner, kind := group.kind, members, guard? := guard }
  let mut observations := #[]
  for group in c.memberGroups do
    let mut members := #[]
    for member in group.members do
      fs := fs.push member.formula
      let formula := EF.atom next
      next := next + 1
      let value ← match member.valueFormula? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      let guard ← match member.evaluationGuard? with
        | none => pure none
        | some f => do
          fs := fs.push f
          let result := some (EF.atom next)
          next := next + 1
          pure result
      members := members.push {
        name := member.name
        formula := formula
        valueFormula? := value
        evaluationGuard? := guard
        range? := member.range?
        text := member.text
      }
    observations := observations.push { owner := group.owner, op := group.op, wanted := group.wanted, members }
  out := { out with assumes := named[0]!, reqs := named[1]!, expects := named[2]!, covers := named[3]!, triggers := named[4]!
                    posts := named[5]!, insts, tables, branchGroups := groups, memberGroups := observations
                    defs := c.defs.map fun (d, _, _) => (d, .tt, .tt) }
  return (out, fs)

/-! ## Which checks, and their verdicts -/

/-- How a check is run, given its evidence (`check::by_evidence`). -/
inductive Method where
  | solver
  | testing
  | enumeration
  /-- Enumeration, then testing where enumeration is not complete. -/
  | enumerationThenTesting
  | skipped
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The checks that enumeration decides: all but definedness, of indexes,
which only sequences have, and of values of pattern types, and the
postconditions of defined functions, which only their bodies have
(`check::by_evidence`). -/
def enumerable (kind : CheckKind) : Bool :=
  !(kind == .definedness || kind == .postcondition)

/-- How a check of kind `kind` is run, given its evidence, and whether it
is the definedness of a value given where a pattern type is declared,
which the solver always checks (`check::by_evidence`). -/
def methodOf (kind : CheckKind) (ev : Evidence) (obligation : Bool := false) : Method :=
  if obligation then .solver
  else if ev.enumerated then
    if !enumerable kind then .skipped
    else if ev.tested then .enumerationThenTesting
    else .enumeration
  else if ev.tested then (if kind.untestable then .skipped else .testing)
  else .solver

/-- `c` with only the checks of `t`, those that enumeration decides, and
the kinds of check to run of them. -/
def _root_.Fren.Core.Comp.only (t : Tested) (c : Comp F) (kinds : Array CheckKind) : Comp F × Array CheckKind :=
  ({ c with
      expects := c.expects.filter (t.props.contains ·.1)
      covers := c.covers.filter (t.props.contains ·.1)
      triggers := c.triggers.filter (t.props.contains ·.1)
      insts := c.insts.map fun i => if t.insts.contains i.name then i else { i with assumes := #[] }
      vars := c.vars.map fun v => if t.dets.contains v.name then v else { v with isDet := false }
      indexes := #[], posts := #[]
      tables := c.tables.filter fun s => t.props.contains s.site.prop || t.insts.contains s.site.prop },
    kinds.filter fun k => enumerable k && (k != .realizable || t.realizable) && (k != .redundancy || t.redundancy))

/-- Of the checks that enumeration decides (`enumerable`), whether one
passes on a proof, rather than on a model (`Reqs/Check#verdict-families`). -/
def provesFamily (kind : CheckKind) : Bool :=
  kind == .realizable || kind == .expect || kind == .inst || kind == .determinism || kind == .completeness
    || kind == .disjointness || kind == .precondition

/-- What enumeration within the bound shows of a check
(`check::enumerated_verdict`): `exact` when every slot's values are all of
its type's, and `outputsExact` when every output's are, so that a
realizability conflict, whose input is pinned, is decided. A verdict that
rests on an `unsat` answer is otherwise only bounded: a pass that holds
for every behaviour up to the bound, or, for a check that fails on `unsat`,
inconclusive. -/
def enumeratedVerdict (kind : CheckKind) (verdict : Verdict) (conflict exact outputsExact : Bool) : Verdict × Bool :=
  if exact then (verdict, false)
  else match verdict with
    | .pass => (.pass, provesFamily kind)
    | .fail =>
      if kind == .realizable then (if conflict && outputsExact then (.fail, false) else (.inconclusive, true))
      else if provesFamily kind then (.fail, false)
      else (.inconclusive, true)
    | .inconclusive => (.inconclusive, false)

/-- `r`, a result of enumeration within the bound `n`, with its verdict as
`enumeratedVerdict` gives it, marked bounded if it is. -/
def classify (n : Nat) (exact outputsExact : Bool) (r : CheckResult) : CheckResult :=
  -- A bounded search does not prove properties of all admitted models.
  -- Keep its concrete evidence, but not unqualified global explanations.
  let r := if exact then r else { r with clashes := #[], branchConflicts := #[], explanationPremises := #[] }
  let conflict := r.detail matches .conflict ..
  let (verdict, bounded) := enumeratedVerdict r.kind r.verdict conflict exact outputsExact
  if !bounded then { r with verdict } else
  if verdict == .inconclusive then
    let why := match r.kind, r.detail with
      | .realizable, .vacuousAssumptions _ => s!"no input meets the assumptions up to size {n}, but a larger one may"
      | .realizable, _ => s!"no outputs up to size {n}, but larger ones may exist"
      | _, _ => s!"no witness up to size {n}, but a larger one may exist"
    { r with verdict, detail := .unknown why, bounded? := some n }
  else { r with verdict, bounded? := some n }

/-! ## The space of a procedure -/

/-- The most assignments that enumeration searches for a procedure
(`check::enumeration_limit`). -/
def maxBehaviours : Nat := 65536

/-- Whether a procedure whose enumeration would search `count` assignments
is enumerated (`check::enumeration_limit`). -/
def withinLimit (count : Nat) : Bool := count ≤ maxBehaviours

/-- A variable for `spaceOf`: its signature, its declared type, and whether
it is a defined output. -/
structure SlotVar where
  sig : VarSig
  pty : PTy
  defined : Bool := false
  deriving Inhabited

/-- An uninterpreted function, for `spaceOf`: its name, and its
parameters' and result's declared types. -/
structure FunVar where
  name : Name
  params : Array PTy
  result : PTy
  deriving Inhabited

/-- The hidden slot of an uninterpreted function: its interpretations, each
a table from the tuples of its arguments up to the bound, the first
varying slowest, to its results up to the bound, numbered in base `results.size`,
the first tuple's digit the least significant; listed by the largest size of
their results, then by number (`Reqs/Check#searching`). -/
structure FunSlot where
  name : Name
  slot : Nat
  /-- Each parameter's values up to the bound. -/
  params : Array (Array EVal)
  results : Array EVal
  /-- The number of the table that each of the slot's values is. -/
  tables : Array Nat
  /-- Every interpretation of the function is among them. -/
  exhausted : Bool
  /-- How many interpretations there are up to the bound. -/
  count : Nat
  deriving Inhabited

/-- The position of the tuple of arguments at the positions `idx` in their
parameters' values, of sizes `sizes`, the first varying slowest; `none` if
one is not among them. -/
def tupleIndex (sizes idx : Array Nat) : Option Nat :=
  (sizes.zip idx).foldlM (init := 0) fun acc (k, i) => if i < k then some (acc * k + i) else none

/-- The result, by its position among the results, of `results` many, that
the table numbered `table` gives the tuple at position `pos`. -/
def tableEntry (results table pos : Nat) : Nat :=
  if results == 0 then 0 else (table / results ^ pos) % results

/-- The tables from `domain` tuples to results whose sizes are `sizes`,
each with its size, the largest of its results', smallest first, then by
number; none if there are more than `limit`. -/
def tablesBySize (domain : Nat) (sizes : Array Nat) (limit : Nat) : Option (Array (Nat × Nat)) :=
  let r := sizes.size
  let count := r ^ domain
  if count > limit then none else
  let tables := (List.range count).toArray.map fun j =>
    (j, (List.range domain).foldl (init := 0) fun m p => max m (sizes[tableEntry r j p]!))
  some (tables.qsort fun a b => a.2 < b.2 || (a.2 == b.2 && a.1 < b.1))

/-- The space of a procedure for the bound `n` (`Space`), with each slot's
values, smallest first, then, if `tests` is not 0, as many random values
beyond the bound (`extrasOf`), and its shape, and the slots of its
uninterpreted functions `funs`, after the others; or the variable whose type is not
enumerable, and why. `hidden` are the types whose unspecified values some
atom reads, each with what names it. -/
def spaceOf (shapes : Name → Option DataShape) (n : Nat) (vars : Array SlotVar) (hidden : Array (Name × PTy))
    (funs : Array FunVar := #[]) (tests : Nat := 0) (seed : UInt64 := 0) :
    Except (Option Name × String) (Space × Array (Array EVal) × Array Shape × Array FunSlot) := do
  let own := vars.filter (!·.defined)
  let copied := own.filter fun v => (Symbol.ofRole v.sig.role).copied
  let all := own.map (fun v => (v.sig.name, v.pty)) ++ copied.map (fun v => (primed v.sig.name, v.pty)) ++ hidden
  let visible := own.size + copied.size
  let shapesOf ← all.zipIdx.mapM fun ((x, t), i) => match shapeOf shapes n t with
    | .ok s => pure s
    | .error why => throw (if i < visible then some x else none, why)
  -- With testing, each slot's values are followed by random ones beyond
  -- the bound; a second copy has its original's.
  let extras := all.zipIdx.map fun ((_, t), i) =>
    if tests == 0 then #[] else extrasOf shapes n t tests (splitMix (seed + i.toUInt64 * 0x2545F4914F6CDD1D)).2
  let ordered : Array (List (EVal × Nat)) := (shapesOf.zip extras).zipIdx.map fun ((sh, ex), i) =>
    let ex := if own.size ≤ i && i < visible then
        (own.findIdx? (fun (v : SlotVar) => v.sig.name == copied[i - own.size]!.sig.name)).map (extras[·]!) |>.getD ex
      else ex
    sh.ordered n ++ ex.toList
  let primeOf := (List.range (all.size + funs.size)).toArray.map fun i =>
    if h : i < own.size then
      (copied.findIdx? (·.sig.name == own[i].sig.name)).map (own.size + ·)
    else none
  let outputs := (List.range own.size).toArray.filter fun i => own[i]!.sig.role == .output
  -- Each function's slot, after the others.
  let mut fslots : Array FunSlot := #[]
  let mut fsizes : Array (Array Nat) := #[]
  for f in funs, k in [0:funs.size] do
    let shape (t : PTy) := match shapeOf shapes n t with
      | .ok s => pure s
      | .error why => throw (none, why)
    let ps ← f.params.mapM shape
    let r ← shape f.result
    let params := ps.map fun s => (s.ordered n).toArray
    let results := (r.ordered n).toArray
    let domain := params.foldl (· * ·.size) 1
    -- More interpretations than the limit: the slot holds none, and
    -- `Space.behaviours` counts them all (`interpretations`).
    let tables := (tablesBySize domain (results.map (·.2)) maxBehaviours).getD #[]
    fslots := fslots.push { name := f.name, slot := all.size + k, params := params.map (·.map (·.1)), results := results.map (·.1)
                            tables := tables.map (·.1), exhausted := ps.all (·.exhausted n) && r.exhausted n
                            count := results.size ^ domain }
    fsizes := fsizes.push (tables.map (·.2))
  let sp : Space := { names := all.map (·.1) ++ funs.map (·.name), sizes := ordered.map (·.toArray.map (·.2)) ++ fsizes
                      primeOf, outputs, hidden := hidden.size + funs.size, bound := n }
  return (sp, ordered.map (·.toArray.map (·.1)), shapesOf, fslots)

/-- How many assignments the enumeration of a procedure searches, at
most: the product of its variables' and hidden slots' counts, its
functions' interpretations among them, and, if determinism is checked,
of their second copies' too
(`check::enumeration_limit`). -/
def Space.behaviours (sp : Space) (determinism : Bool) (funs : Array FunSlot := #[]) : Nat :=
  let primes := sp.primeOf.filterMap id
  (List.range sp.names.size).foldl (init := 1) fun acc i =>
    if !determinism && primes.contains i then acc
    else match funs.find? (·.slot == i) with
      | some f => acc * f.count
      -- Not the random values beyond the bound, which testing draws from.
      | none => acc * sp.within i sp.bound

/-- Whether every slot of `slots` holds every value of its type within the
bound. -/
def exhaustedAll (shapes : Array Shape) (n : Nat) (slots : Array Nat) : Bool :=
  slots.all fun i => (shapes[i]?.map (·.exhausted n)).getD true

/-- What enumerating a procedure found: its results, each marked bounded
as `classify` says, and the bound. -/
structure Enumerated where
  results : Array CheckResult := #[]
  bound : Nat := 0
  /-- Every slot's values are all of its type's: the results are decided. -/
  exact : Bool := true
  /-- Some checks were tested beyond the bound too. -/
  tested : Bool := false
  deriving Inhabited

/-- The results of enumerating the checks of `alone`, without testing, and
of `both`, with testing beyond the bound, together; `keep` selects the
results to report. -/
def Enumerated.merge (n : Nat) (alone both : Option Enumerated) (keep : CheckResult → Bool) : Enumerated :=
  { results := ((alone.map (·.results)).getD #[] ++ (both.map (·.results)).getD #[]).filter keep, bound := n
    exact := (alone.map (·.exact)).getD true && (both.map (·.exact)).getD true
    tested := both.any (!·.exact) }


/-! ## Messages -/

/-- A procedure, or a global expectation, `subject`, written as it is shown,
whose enumeration would search more than `maxBehaviours` assignments
(`F0644`). -/
def tooManyMsg (subject : String) (count n : Nat) : Msg :=
  { code? := some "F0644", headline := s!"{subject} has {count} behaviours up to size {n}, too many to enumerate"
    label? := some "too many behaviours"
    notes := #[s!"note: enumeration searches at most {maxBehaviours} behaviours, counting a second copy of each for determinism",
      "help: lower `fren.enumeration.size`, or have the solver check it"] }

/-- Why a component that applies the generic function `f`, which has no
body, cannot be enumerated (`check::enumerable`): each instance is a
function of its own, which enumeration does not enumerate. -/
def genericNotEnumerable (f : Name) : String :=
  s!"it applies the generic function `{showComp f}`, which has no body"

/-- `subject` cannot be enumerated, for the reason `why` (`F0645`). -/
def notEnumerableMsg (subject why : String) : Msg :=
  { code? := some "F0645", headline := s!"{subject} cannot be enumerated: {why}", label? := some "not enumerable"
    notes := #["note: enumeration needs every variable's type to be enumerable, and no uninterpreted function with a contract or type parameters, nor unbounded quantifier",
      "help: have the solver or testing check it"] }

/-- The checks of `subject` that enumeration decided only up to the bound
`n` (`F0646`): `passed` of them hold for every behaviour up to size `n`,
and `tests` random tests found no counterexample beyond it, if they ran. -/
def boundedMsg (subject : String) (passed n : Nat) (tests : Option Nat := none) : Msg :=
  let testing := match tests with
    | some t => s!", and for {t} random tests"
    | none => ""
  { code? := some "F0646"
    headline := s!"{passed} {if passed == 1 then "check" else "checks"} of {subject} {if passed == 1 then "holds" else "hold"} \
      for every behaviour up to size {n}{testing}"
    notes := #["note: not every behaviour was enumerated, so this is weaker than a proof"] }

/-- Why the slot `x` cannot be enumerated, its type's `why` (`notEnumerable`):
a variable's, or a hidden slot's, the type of a table or `match`. -/
def notEnumerableWhy (x? : Option Name) (why : String) : String :=
  match x? with
  | none => s!"a table or `match` has a value of the type {why}, which is not enumerable"
  | some x => s!"`{x}` has the type {why}, which is not enumerable"

/-- The message about the checks that hold up to the bound, if any
(`F0646`), of `e`'s results, of a procedure shown as `subject`, whose
checks of `tested` were tested beyond the bound too. -/
def Enumerated.boundedMsg? (e : Enumerated) (subject : String) (tested : Tested) : Option Msg :=
  let bounded := e.results.filter fun r => r.verdict == .pass && r.bounded?.isSome
  if bounded.isEmpty then none
  else some (boundedMsg subject bounded.size e.bound
    (if e.tested && bounded.any tested.covers then some testCount else none))

/-- The size bound, `fren.enumeration.size`, is too large (`F0154`). -/
def sizeTooLargeMsg (n : Nat) : Msg :=
  { code? := some "F0154", headline := s!"enumeration size {n} is too large", label? := some s!"more than {maxSize}"
    notes := #[s!"note: `fren.enumeration.size` is at most {maxSize}"] }
where
  maxSize : Nat := 64

/-- The default size bound (`fren.enumeration.size`). -/
def defaultSize : Nat := 3

/-- The largest size bound. -/
def maxSize : Nat := 64

end Fren.Core.Enumeration
