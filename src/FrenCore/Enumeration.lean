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
lists smallest first. A component's checks are then decided by the shared
check algorithms (`Fren.Core.checkComp`) with a backend (`backend`) that
answers each query by searching the assignments of its variables, smallest
first and fairly (`search`): by the largest size of a variable's value, then
in the order of the variables and of each one's values. The formulas are
`EF`s, over *atoms*, the formulas of the component, which each front end
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

/-! ## Formulas -/

/-- A formula of the check algorithms, as enumeration evaluates it: over
the component's formulas, its *atoms*, which a front end evaluates, and
over its variables' *slots*, each holding the position of its value in its
slot's values (`Space`). -/
inductive EF where
  /-- The component's `k`th atom. -/
  | atom (k : Nat)
  | tt
  | ff
  | not (f : EF)
  | conj (fs : Array EF)
  /-- `∃ outputs, f`, over the component's own outputs that are not
  defined. -/
  | exOutputs (f : EF)
  /-- The slot `x` holds the value `v`. -/
  | pin (x v : Nat)
  /-- `f` over the second copy of the variables. -/
  | primed (f : EF)
  /-- `x = x'`, for the variable `x`. -/
  | same (x : Name)
  deriving Inhabited, BEq, Hashable

/-- Where enumeration searches: a slot for each variable whose value is
enumerated, the component's own and its instances' that are not defined
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
  /-- The slots of the component's own outputs that are not defined, which
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

instance : Inhabited Atoms := ⟨{ slots := #[], eval := fun _ _ => false }⟩

def Space.slotOf? (sp : Space) (n : Name) : Option Nat := sp.names.idxOf? n

/-- `env` with each copied slot holding its second copy's value. -/
def Space.primedEnv (sp : Space) (env : Array Nat) : Array Nat := Id.run do
  let mut out := env
  for x in [0:sp.primeOf.size] do
    if let some p := sp.primeOf[x]! then out := out.set! x (env[p]!)
  return out

/-- The slots that `f` reads. -/
partial def EF.slots (sp : Space) (ats : Atoms) : EF → Array Nat
  | .atom k => ats.slots[k]?.getD #[]
  | .tt | .ff => #[]
  | .not f => f.slots sp ats
  | .conj fs => fs.foldl (init := #[]) fun acc f => (f.slots sp ats).foldl (fun a x => if a.contains x then a else a.push x) acc
  | .exOutputs f => (f.slots sp ats).filter (!sp.outputs.contains ·)
  | .pin x _ => #[x]
  | .primed f => (f.slots sp ats).map fun x => (sp.primeOf[x]?.join).getD x
  | .same x => match sp.slotOf? x with
    | some s => #[s] ++ (sp.primeOf[s]?.join).toArray
    | none =>
      -- A defined output: the slots of the atoms that mention it.
      let ss := (List.range ats.defs.size).toArray.filter (ats.defs[·]!.contains x) |>.flatMap (ats.slots[·]!)
      ss ++ ss.filterMap (sp.primeOf[·]?.join)

/-- The defined outputs that `f` mentions, each with whether it is the
second copy's. -/
partial def EF.defsOf (ats : Atoms) : EF → Array (Name × Bool)
  | .atom k => (ats.defs[k]?.getD #[]).map (·, false)
  | .not f | .exOutputs f => f.defsOf ats
  | .conj fs => fs.flatMap (·.defsOf ats)
  | .primed f => (f.defsOf ats).map fun (d, _) => (d, true)
  | .same x => #[(x, false), (x, true)]
  | _ => #[]

/-- The values of the slots `slots`, in order, the last varying fastest,
that make `parts` true, each part tried as soon as the slots it reads are
set: the first, among those whose values are within the `lim`th of each
slot's, `none` if none. Other slots keep their values in `env`. -/
partial def firstSat (slots : Array Nat) (parts : Array (Array Nat × (Array Nat → Bool)))
    (env : Array Nat) (lim : Nat → Nat) : Option (Array Nat) :=
  -- Each part at the position of the last of its slots, or before any.
  let pos (p : Array Nat × (Array Nat → Bool)) : Option Nat :=
    p.1.foldl (init := none) fun acc s => match slots.idxOf? s, acc with
      | some i, some j => some (max i j)
      | some i, none => some i
      | none, acc => acc
  let byPos : Array (Array (Array Nat → Bool)) :=
    parts.foldl (init := Array.replicate slots.size #[]) fun acc p => match pos p with
      | some i => acc.modify i (·.push p.2)
      | none => acc
  let early := parts.filter (pos · |>.isNone) |>.map (·.2)
  let rec go (i : Nat) (env : Array Nat) : Option (Array Nat) :=
    if h : i < slots.size then
      let s := slots[i]
      let rec try_ (j : Nat) : Option (Array Nat) :=
        if j < lim s then
          let env := env.set! s j
          if byPos[i]!.all (· env) then
            match go (i + 1) env with
            | some r => some r
            | none => try_ (j + 1)
          else try_ (j + 1)
        else none
      try_ 0
    else some env
  if early.all (· env) then go 0 env else none

/-- How many of the slot `s`'s values have size at most `k`: they are
smallest first, so these are the first. -/
def Space.within (sp : Space) (s k : Nat) : Nat :=
  ((sp.sizes[s]?.getD #[]).toList.takeWhile (· ≤ k)).length

/-- The value of `f` in `env`. -/
partial def EF.eval (sp : Space) (ats : Atoms) (env : Array Nat) : EF → Bool
  | .atom k => ats.eval k env
  | .tt => true
  | .ff => false
  | .not f => !f.eval sp ats env
  | .conj fs => fs.all (·.eval sp ats env)
  | .exOutputs f =>
    -- Some values of the outputs, within the bound, make `f` true: searched
    -- with each conjunct tried as soon as it can be.
    let parts := (match f with | .conj fs => fs | f => #[f]).map fun (g : EF) => (g.slots sp ats, fun e => g.eval sp ats e)
    let outs := sp.outputs.filter fun o => parts.any (·.1.contains o)
    -- The conjuncts that read no output need not wait for them.
    (firstSat outs parts env fun s => (sp.sizes[s]?.getD #[]).size).isSome
  | .pin x v => env[x]? == some v
  | .primed f => f.eval sp ats (sp.primedEnv env)
  | .same x => match sp.slotOf? x with
    | some s => match sp.primeOf[s]?.join with
      | some p => env[s]? == env[p]?
      | none => true
    | none => ats.sameDefined x env (sp.primedEnv env)

/-- The first assignment of the slots that `parts` read that makes them
all true, smallest first and fairly (`Reqs/Check#sizes-and-order`): for
each level `k` from 0 to the bound, the assignments whose largest size is
`k`, in the order of the slots and of each slot's values, the last
varying fastest. With the level, if one is found. -/
def search (sp : Space) (ats : Atoms) (parts : Array EF) : Option (Array Nat × Nat) := Id.run do
  let ps := parts.map fun f => (f.slots sp ats, fun e => f.eval sp ats e)
  let slots := (ps.foldl (init := #[]) fun acc (ss, _) => ss.foldl (fun a s => if a.contains s then a else a.push s) acc).qsort (· < ·)
  let env0 := Array.replicate sp.names.size 0
  if slots.isEmpty then
    return if ps.all (·.2 env0) then some (env0, 0) else none
  let sizeAt (s j : Nat) := (sp.sizes[s]?.getD #[])[j]?.getD 0
  for k in [0:sp.bound + 1] do
    -- Only levels that some slot's value has.
    unless slots.any (fun s => (sp.sizes[s]?.getD #[]).contains k) do continue
    -- The assignments of level `k`: within `k`, and some value of size `k`.
    let level := (slots, fun (e : Array Nat) => slots.any fun s => sizeAt s e[s]! == k)
    if let some env := firstSat slots (ps.push level) env0 (sp.within · k) then return some (env, k)
  return none

/-! ## The backend -/

/-- A value of a model: its slot and the position of its value there, if
it is enumerated rather than a defined output's, and the value as Fren
writes it. -/
structure EV where
  at? : Option (Nat × Nat)
  shown : String
  deriving Inhabited

/-- The checks' backend over the space `sp`, whose atoms are `ats`
(`Reqs/Check#checking-by-enumeration`): each query is answered by `search`,
`unsat` if no assignment within the bound refutes it, and otherwise `sat`
with the first that does, which gives the slots it reads, but the hidden
ones, and the defined outputs that its formulas mention, as `render` and
`defValue` show them. -/
def backend [Monad m] (sp : Space) (ats : Atoms) (render : Nat → Nat → m String)
    (defValue : Name → Array Nat → m (Option String)) : Backend m EF EV where
  query hyps goal _ := do
    let parts := (hyps.map (·.2)).push (.not goal)
    match search sp ats parts with
    | none => return .unsat
    | some (env, _) =>
      let slots := parts.foldl (init := #[]) fun acc f =>
        (f.slots sp ats).foldl (fun a x => if a.contains x then a else a.push x) acc
      let shown ← ((slots.qsort (· < ·)).filter (· < sp.names.size - sp.hidden)).mapM fun x => do
        return (sp.names[x]!, ({ at? := some (x, env[x]!), shown := ← render x env[x]! } : EV))
      let defs := (parts.flatMap (·.defsOf ats)).foldl (init := #[]) fun acc d => if acc.contains d then acc else acc.push d
      let defd ← defs.filterMapM fun (d, primed) => do
        let e := if primed then sp.primedEnv env else env
        return (← defValue d e).map fun v => (if primed then primed' d else d, ({ at? := none, shown := v } : EV))
      return .sat (shown ++ defd)
  falseF := .ff
  notF := .not
  conj := .conj
  existsOutputs f := pure (.exOutputs f)
  pin _ v := pure (v.at?.map fun (x, j) => .pin x j)
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
                             typesInterpreted := c.typesInterpreted, fn? := c.fn? }
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
  out := { out with assumes := named[0]!, reqs := named[1]!, expects := named[2]!, covers := named[3]!, triggers := named[4]!
                    posts := named[5]!, insts, tables, defs := c.defs.map fun (d, _, _) => (d, .tt, .tt) }
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

/-- How a check of kind `kind` is run, given its evidence
(`check::by_evidence`). -/
def methodOf (kind : CheckKind) (ev : Evidence) : Method :=
  if ev.enumerated then
    if !enumerable kind then .skipped
    else if ev.tested && !kind.untestable then .enumerationThenTesting
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

/-! ## Enumeration then testing -/

/-- The verdict of a check whose evidence is `"enumerated+tested"`, from
enumeration's, whether that is bounded, and testing's, if testing ran
(`check::combined_evidence`): enumeration's counterexample, or its decided
verdict, stands; otherwise testing's counterexample fails the check, and
testing's pass passes one that enumeration left inconclusive. With whether
the result is testing's. -/
def combinedVerdict (enumerated : Verdict) (bounded : Bool) (tested? : Option Verdict) : Verdict × Bool :=
  if enumerated == .fail || !bounded then (enumerated, false)
  else match tested? with
    | some .fail => (.fail, true)
    | some .pass => if enumerated == .inconclusive then (.pass, true) else (enumerated, false)
    | _ => (enumerated, false)

/-- The result of a check whose evidence is `"enumerated+tested"`, from
enumeration's `e` and testing's `t?` (`combinedVerdict`). -/
def combine (e : CheckResult) (t? : Option CheckResult) : CheckResult :=
  match combinedVerdict e.verdict e.bounded?.isSome (t?.map (·.verdict)), t? with
  | (_, true), some t => t
  | (v, _), _ => { e with verdict := v }

/-! ## The space of a component -/

/-- The most assignments that enumeration searches for a component
(`check::enumeration_limit`). -/
def maxBehaviours : Nat := 65536

/-- Whether a component whose enumeration would search `count` assignments
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

/-- The space of a component for the bound `n` (`Space`), with each slot's
values, smallest first, and its shape, and the slots of its uninterpreted
functions `funs`, after the others; or the variable whose type is not
enumerable, and why. `hidden` are the types whose unspecified values some
atom reads, each with what names it. -/
def spaceOf (shapes : Name → Option DataShape) (n : Nat) (vars : Array SlotVar) (hidden : Array (Name × PTy))
    (funs : Array FunVar := #[]) :
    Except (Option Name × String) (Space × Array (Array EVal) × Array Shape × Array FunSlot) := do
  let own := vars.filter (!·.defined)
  let copied := own.filter fun v => (Symbol.ofRole v.sig.role).copied
  let all := own.map (fun v => (v.sig.name, v.pty)) ++ copied.map (fun v => (primed v.sig.name, v.pty)) ++ hidden
  let visible := own.size + copied.size
  let shapesOf ← all.zipIdx.mapM fun ((x, t), i) => match shapeOf shapes n t with
    | .ok s => pure s
    | .error why => throw (if i < visible then some x else none, why)
  let ordered := shapesOf.map (·.ordered n)
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

/-- How many assignments the enumeration of a component searches, at
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
      | none => acc * (sp.sizes[i]!.size)

/-- Whether every slot of `slots` holds every value of its type within the
bound. -/
def exhaustedAll (shapes : Array Shape) (n : Nat) (slots : Array Nat) : Bool :=
  slots.all fun i => (shapes[i]?.map (·.exhausted n)).getD true

/-- What enumerating a component found: its results, each marked bounded
as `classify` says, and the bound. -/
structure Enumerated where
  results : Array CheckResult := #[]
  bound : Nat := 0
  /-- Every slot's values are all of its type's: the results are decided. -/
  exact : Bool := true
  deriving Inhabited

/-! ## Messages -/

/-- A component, or a global expectation, `subject`, written as it is shown,
whose enumeration would search more than `maxBehaviours` assignments
(`F0644`). -/
def tooManyMsg (subject : String) (count n : Nat) : Msg :=
  { code? := some "F0644", headline := s!"{subject} has {count} behaviours up to size {n}, too many to enumerate"
    label? := some "too many behaviours"
    notes := #[s!"note: enumeration searches at most {maxBehaviours} behaviours, counting a second copy of each for determinism",
      "help: lower `fren.enumeration.size`, or have the solver check it"] }

/-- `subject` cannot be enumerated, for the reason `why` (`F0645`). -/
def notEnumerableMsg (subject why : String) : Msg :=
  { code? := some "F0645", headline := s!"{subject} cannot be enumerated: {why}", label? := some "not enumerable"
    notes := #["note: enumeration needs every variable's type to be enumerable, and no uninterpreted function with a contract, nor unbounded quantifier",
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
