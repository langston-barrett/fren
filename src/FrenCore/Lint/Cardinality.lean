-- keep-sorted start
import FrenCore.Lint.Operators
-- keep-sorted end

/-!
# Cardinality and ordered enumeration lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Cardinality, ordered enumerations and newtypes -/

/-- What an elaborator knows of an expression that the lints of ordered
enumerations and newtypes read. -/
inductive NodeFact where
  /-- A variant of the ordered enumeration `enum`, the one at `pos`,
  from 0, of its `count`. -/
  | ordinal (enum : String) (pos count : Nat)
  /-- `Ms(e)`, which builds a value of the newtype `newtype`, where
  `synthesizes` says that `e` has a type of its own, rather than one taken
  from where it is written, as `[]` and `{}` do. -/
  | wraps (newtype : String) (synthesizes : Bool)
  /-- `x.0`, which reads the field of a value of the newtype `newtype`. -/
  | unwraps (newtype : String)
  /-- An `and` whose operands give a definedness obligation: an index, a
  table, or a name whose definition gives one (`Reqs/Lang/Expressions#sequences`). -/
  | obligations
  /-- An equation or a disequation whose operands are `Nat`s. -/
  | natOperands
  deriving Inhabited, BEq, Repr

/-- Whether the text at `i` in `src` starts with `s`. -/
def startsWithAt (src : Array Char) (i : Nat) (s : String) : Bool :=
  (s.foldl (init := (true, i)) fun (ok, k) c => (ok && src[k]? == some c, k + 1)).1

/-- Whether `n` applies a cardinality operator, `some true` for
`exactly_one?` and `some false` for `at_most_one?`: their names are
reserved, so an application written with one is theirs. -/
def cardinalityCall? (src : Array Char) (n : BNode α) : Option Bool :=
  if n.kind != .atom then none
  else if startsWithAt src n.range.start "exactly_one?(" then some true
  else if startsWithAt src n.range.start "at_most_one?(" then some false
  else none

def cardinalityName (exactly : Bool) : String := if exactly then "exactly_one?" else "at_most_one?"

/-- Whether `nonminimal_bool` fires on a cardinality operator of `n`
arguments, and whether its fix is the argument, rather than `true`
(`lint::nonminimal_cardinality`). -/
def nonminimalCardinality (exactly : Bool) (n : Nat) : Bool × Bool := (decide (n = 1), exactly)

/-- Whether `eq_op` fires on the argument `arg` of a cardinality operator,
as written, or `none` for a literal, from the arguments before it that are
not literals (`lint::eq_op_cardinality`). -/
def eqOpCardinality [DecidableEq β] (earlier : List β) (arg : Option β) : Bool :=
  match arg with
  | some x => earlier.contains x
  | none => false

/-- `eq_op` on the argument `arg` of a cardinality operator, written the
same as an earlier one. -/
def eqOpCardinalityMsg (exactly : Bool) (arg : String) : Msg :=
  { code? := some Lint.eqOp.code, headline := s!"`{arg}` is an argument of `{cardinalityName exactly}` more than once"
    label? := some "written the same as an earlier argument"
    notes := #[s!"note: the call holds only where `{arg}` is `false`, so one of the two is probably not the one meant"] }

/-- `nonminimal_bool` and `eq_op` on `n`, a cardinality operator, in
`slot` within `parent` (`lint::nonminimal_cardinality`,
`lint::eq_op_cardinality`). -/
def cardinalityAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let exactly ← cardinalityCall? src n
  let (single, operand) := nonminimalCardinality exactly n.kids.size
  if let (true, some a) := (single, n.kids[0]?) then
    let fixed := if operand then placed src n slot parent (a.text src) else "true"
    let label := if operand then s!"`{cardinalityName exactly}` of one argument is that argument"
      else s!"`{cardinalityName exactly}` of one argument always holds"
    return { lint := .nonminimalBool, ref := n.ref
             msg := { code? := some Lint.nonminimalBool.code, headline := "this `Bool` expression can be simpler"
                      label? := some label, fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] } }
  -- A literal is left to the lints of constants.
  let forms := n.kids.map fun k => if k.kind matches .lit _ then none else some (writtenForm (textOf src k.range))
  let j? := (List.range forms.size).find? fun j => eqOpCardinality ((forms.extract 0 j).toList.filterMap id) forms[j]!
  let k ← n.kids[← j?]?
  return { lint := .eqOp, ref := k.ref, msg := eqOpCardinalityMsg exactly (textOf src k.range) }

/-- The operands of the run of `op`, `and` or `or`, that `n` is the top
of, in order: through each left operand that is an `op` not in
parentheses, as `conjuncts` reads a run of `and`. -/
partial def runOperands (op : String) (src : Array Char) (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .bin o, #[l, r] =>
    if o != op then #[n] else
    (if l.kind == .bin op && !enclosed src n.range l.range then runOperands op src l else #[l]).push r
  | _, _ => #[n]

/-- Whether `n`, an `op` in `slot` within `parent`, is the top of its run
of `op`: not the left operand of another, outside parentheses. -/
def runTop (op : String) (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Bool :=
  n.kind == .bin op && !(slot.any (fun s => s.outer == (BKind.bin op).prec && !s.right) && !enclosed src parent n.range)

/-- A conjunct `not (first and second)`, of operands `β`, where
`obligation` says that the `and` gives a definedness obligation
(`lint::PairNegation`). -/
structure PairNeg (β : Type) where
  first : β
  second : β
  obligation : Bool

/-- Whether `manual_at_most_one` fires on the conjuncts `ps`, and whether its
fix is `exactly_one?` rather than `at_most_one?`, where `disj` is the
disjunction beside them, if any (`lint::manual_at_most_one`), of conjuncts
`γ` read by `first`, `second` and `obligation`: they name three different
operands or more, none twice in one conjunct, and negate each pair of two
different ones, and no `and` gives an obligation; the fix is
`exactly_one?` if `disj` has exactly the operands they name. -/
def manualAtMostOne [DecidableEq β] (first second : γ → β) (obligation : γ → Bool) (ps : List γ) (disj : List β) :
    Bool × Bool :=
  let os := ps.flatMap fun p => [first p, second p]
  let negated (x y : β) := ps.any fun p => first p == x && second p == y
  (os.any (fun x => os.any fun y => os.any fun z => x != y && x != z && y != z)
      && ps.all (fun p => first p != second p)
      && os.all (fun x => os.all fun y => x == y || negated x y || negated y x)
      && !ps.any obligation,
    disj.any (fun _ => true) && disj.all (os.contains ·) && os.all (disj.contains ·))

/-- `manual_at_most_one`'s message, whose fix is `fixed`, at `range`, the
conjuncts with the parentheses around the disjunction, or none but a note
if a comment within them would be lost (`commented`). -/
def manualAtMostOneMsg (exactly : Bool) (n : Nat) (fixed : String) (range : Range) (commented : Bool) : Msg :=
  { code? := some Lint.manualAtMostOne.code, headline := s!"this is `{cardinalityName exactly}` of {n} operands"
    label? := some (if exactly then s!"says that one of {n} operands holds, and negates each pair" else s!"negates each pair of {n} operands")
    notes := if commented then #[s!"help: write `{fixed}`",
      "note: `fren fix` leaves this, since the call would lose the comment within the conjuncts"] else #[]
    fixes := if commented then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed, range? := some range }] }

/-- `manual_at_most_one` on `n`, an `and` in `slot` within `parent`, if it
is the top of a run of `and` (`lint::manual_at_most_one`): one report for
each longest run of adjacent conjuncts `not (a and b)`, not in
parentheses, with the disjunction of their operands just before or after
it, if there is one. The message is reported from the first conjunct it
replaces to the last. -/
def manualAtMostOneAt [Inhabited α] (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) :
    Array (OpReport α) := Id.run do
  unless runTop "and" src n slot parent do return #[]
  let cs := runOperands "and" src n
  let bare (k : BNode α) := !enclosed src n.range k.range
  let form (k : BNode α) := writtenForm (textOf src k.range)
  let pair? (k : BNode α) : Option (BNode α × BNode α) := do
    guard (bare k)
    let (.not, #[i]) := (k.kind, k.kids) | none
    let (.bin "and", #[a, b]) := (i.kind, i.kids) | none
    pure (a, b)
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    if (pair? cs[i]!).isNone then
      i := i + 1
      continue
    let mut j := i
    while j + 1 < cs.size && (pair? cs[j + 1]!).isSome do j := j + 1
    let pairs := (cs.extract i (j + 1)).filterMap pair?
    -- Each conjunct, its operands as written, and whether its `and` gives
    -- an obligation, as the elaborator says.
    let model := (cs.extract i (j + 1)).toList.filterMap fun c => do
      let (a, b) ← pair? c
      pure ({ first := form a, second := form b
              obligation := c.kids.any fun k => fact? k.ref == some .obligations } : PairNeg String)
    -- The operands, each once, in the order they are first written.
    let dedup (ks : Array (BNode α)) := ks.foldl (init := (#[] : Array (BNode α))) fun acc k =>
      if acc.any (form · == form k) then acc else acc.push k
    let ops := dedup (pairs.flatMap fun (a, b) => #[a, b])
    -- The disjunction just before or after, in the parentheses that an
    -- operand of `and` needs, if the fix is `exactly_one?` with it.
    let disj? (k : Nat) : Option (Array (BNode α)) := do
      let c ← cs[k]?
      guard (c.kind == .bin "or")
      let ds := runOperands "or" src c
      guard (manualAtMostOne PairNeg.first PairNeg.second PairNeg.obligation model (ds.toList.map form)).2
      pure ds
    let (first, last, disjunction?) := match (if i > 0 then disj? (i - 1) else none), disj? (j + 1) with
      | some ds, _ => (i - 1, j, some ds)
      | none, some ds => (i, j + 1, some ds)
      | none, none => (i, j, none)
    let (fires, exactly) := manualAtMostOne PairNeg.first PairNeg.second PairNeg.obligation model ((disjunction?.getD #[]).toList.map form)
    if fires then
      let args := (dedup (disjunction?.getD ops)).map fun o => textOf src o.range
      let fixed := s!"{cardinalityName exactly}({", ".intercalate args.toList})"
      let range : Range := { start := (withParensIn src n.range cs[first]!.range).start
                             stop := (withParensIn src n.range cs[last]!.range).stop }
      let commented := hasComment (textOf src range)
      out := out.push { lint := .manualAtMostOne, ref := cs[first]!.ref, last? := some cs[last]!.ref
                        msg := manualAtMostOneMsg exactly ops.size fixed range commented }
    i := j + 1
  return out

/-- The variant of an ordered enumeration that `k` is, if it is one, as
its enumeration, its position and the number of variants. -/
def ordinalOf? (fact? : α → Option NodeFact) (k : BNode α) : Option (String × Nat × Nat) :=
  match fact? k.ref with
  | some (.ordinal e p c) => some (e, p, c)
  | _ => none

/-- The comparison and the position of the variant that `manual_ordering`'s
fix is, if it fires on a test that an operand is one of the variants at
`named` of an ordered enumeration of `count`, or, if `negated`, none of
them (`lint::manual_ordering`): where they are two or more, but not all,
and the first variants, the fix compares with the last of them, and where
they are the last, with the first of them. -/
def manualOrdering (count : Nat) (named : List Nat) (negated : Bool) : Option (Comparison × Nat) :=
  let has (v : Nat) := named.contains v
  let k := ((List.range count).filter has).length
  if k < 2 || k ≥ count then none
  else if (List.range count).all (fun v => has v == decide (v < k)) then some (if negated then .gt else .le, k - 1)
  else if (List.range count).all (fun v => has v == decide (count - k ≤ v)) then
    some (if negated then .lt else .ge, count - k)
  else none

/-- `manual_ordering`'s message, whose fix is `fixed`, from whether the
variants are the first of the enumeration, and whether the test is that
the operand is none of them. -/
def manualOrderingMsg (fixed : String) (first negated : Bool) (named : Nat) : Msg :=
  { code? := some Lint.manualOrdering.code, headline := s!"this is `{fixed}`"
    label? := some s!"{if negated then "excludes" else "names"} the {if first then "first" else "last"} {named} variants of an ordered enumeration"
    notes := #["note: they differ once a variant is added among those named: the comparison takes it in, and the test does not"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `manual_ordering` on `n`, in `slot` within `parent`, where `x` is the
operand and `vs` the variants it is tested against, and `negated` says
that the test is that it is none of them (`lint::manual_ordering`). -/
def manualOrderingOf? (src : Array Char) (fact? : α → Option NodeFact) (n x : BNode α) (vs : Array (BNode α))
    (negated : Bool) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let ords ← vs.mapM (ordinalOf? fact?)
  let (e, _, count) ← ords[0]?
  guard (ords.all fun (e', _, c) => e' == e && c == count)
  let ps := ords.map (·.2.1)
  let (c, target) ← manualOrdering count ps.toList negated
  let first := c matches .le | .gt
  let k ← (ps.findIdx? (· == target)).bind (vs[·]?)
  let fixed := placed src n slot parent (binText c.op (x.text src) (k.text src))
  let named := ((List.range count).filter (ps.contains ·)).length
  return { lint := .manualOrdering, ref := n.ref, msg := manualOrderingMsg fixed first negated named }

/-- `manual_ordering` on `n`, in `slot` within `parent`: `x in {...}`, or
at the top of a run of `or` of `x = V`, or of `and` of `x != V`
(`lint::manual_ordering`). -/
def manualOrderingAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  match n.kind, n.kids with
  | .bin "in", #[x, s] =>
    guard (s.kind == .atom && startsWithAt src s.range.start "{")
    manualOrderingOf? src fact? n x s.kids false slot parent
  | .bin op, _ =>
    let cmp ← if op == "or" then some "=" else if op == "and" then some "!=" else none
    guard (runTop op src n slot parent)
    let ds := runOperands op src n
    let eqs ← ds.mapM fun d => match d.kind, d.kids with
      | .bin c, #[l, r] => if c == cmp && !enclosed src n.range d.range then some (l, r) else none
      | _, _ => none
    let (x, _) ← eqs[0]?
    guard (eqs.all fun (l, _) => writtenForm (textOf src l.range) == writtenForm (textOf src x.range))
    manualOrderingOf? src fact? n x (eqs.map (·.2)) (op == "and") slot parent
  | _, _ => none

end Fren.Core
