-- fren-covers: lang::coincidence, lang::closed, lint::written_scopes, lint::ifs_same_cond_taken, lint::manual_at_most_one_defined
-- keep-sorted start
import FrenCli.Eval
import FrenCli.Search
import Reqs.Lang
-- keep-sorted end

/-!
# The binary's evaluator against the dynamic semantics (`Reqs/Lang/Semantics`)

The binary's evaluator, `Ex.eval`, and the semantics' `lang::eval`, as Lean
generates it, agree on random expressions, each generated as a pair: the
binary's `Ex` and the semantics' `Expr`, in a random behaviour. The
expressions are over integers, `Bool`s, strings, sequences of integers, an
enumeration `E { A(Int), B }` and a record `R(Int, Bool)`: literals,
variables, `+` and `-`, the comparisons, the connectives, conditionals,
cardinality, indexing in and out of range, constructions, field reads,
`match`es over `E` and over integers, with binders and guards, tables, the
constant `C0` and the defined function `f(n)`, which both inline, and
applications of the uninterpreted function `u` (`Call`) and of the
structural recursion `r(n)` (`Recur`). The binary's interpretation and the
semantics' are built from the same graphs: `u`'s, at random points, and
`r`'s, whose body is `n + 1`, at some of the integers. The primitive
operations, `*`, `div`, `mod` and `++` of strings, are left out: the
semantics takes them from its interpretation. Where the semantics finds an
expression well-defined, the binary gives it the same value; where the
binary does not know it, the semantics finds it undefined. The binary may
know more, by its Kleene connectives, and by evaluating `r`'s body where
the semantics' finite graph has no point.

Each expression is also evaluated in the behaviour with a variable that it
does not mention rebound, which the coincidence lemma (`lang::coincidence`)
says changes nothing, and, where it mentions nothing, in the empty
environment, which `lang::closed` says changes nothing either. Each is
compiled too (`Ex.compile`), which keeps its value in every interpretation,
one with values for the indexes out of range among them, and compiled
again, and so does each integer one checked to be of a subset type,
directly or as the field of a record, or compared with the bound name of
a quantifier over one. Compiling a structural recursion's body, as
testing does, keeps the value of its applications (`compiledRecursion`),
and a pattern that `Pat.mayMatchCtor` says matches no variant of an index
matches none (`mayMatchCtorSound`), which `Ex.dispatch` rests on. Last,
expressions of the semantics alone are evaluated under interpretations
that differ in the functions that they do not mention. Both lemmas are
proved in `Impls/Semantics.lean`; these tests cross-check the proofs'
statements against the generated code.
-/

namespace Fren.Test.Semantics

open FrenCli.Eval (Ex Op Val Pat)
open Fren.Generated

/-- A pseudo-random state: a linear congruential generator. -/
abbrev R := StateM Nat

def next (n : Nat) : R Nat := modifyGet fun s =>
  let s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  ((s / 65536) % n, s)

/-- A small integer, from `-5` to `5`. -/
def small : R Int := do
  let n ← next 11
  return (n : Int) - 5

inductive Ty where
  | int | bool | str | seq | e | r
  deriving BEq, Inhabited

/-- What an expression may mention: the behaviour's variables, the
parameter `n` of `f`, `C0`, `f`, `u` and `r`, and the binders of the arms
around it. -/
structure Scope where
  vars : Bool := true
  param : Bool := false
  const : Bool := true
  fn : Bool := true
  apps : Bool := true
  binders : List Lean.Name := []

abbrev Pair := Ex × (lang.Expr String)

/-- A list expression of `es`. -/
def list : List (lang.Expr String) → (lang.Expr String)
  | [] => .Nil
  | e :: es => .Cons e (list es)

def intLit (k : Int) : Pair := (.lit (.int k), .Literal (.Integer k))
def boolLit (b : Bool) : Pair := (.lit (.bool b), .Literal (lang.truth b))
def trueE : lang.Expr String := .Literal .True

/-- The binary operator `op` as the semantics has it, with its derived forms
translated (`Reqs/Lang/Semantics#derived-forms`). -/
def binE (op : Op) (a b : lang.Expr String) : lang.Expr String :=
  match op with
  | .and => .And a b
  | .or => .Or a b
  | .iff | .eq => .Binary .Eq a b
  | .ne => .Unary .Not (.Binary .Eq a b)
  | .lt => .Binary .Lt a b
  | .le => .Binary .Le a b
  | .gt => .Binary .Lt b a
  | .ge => .Binary .Le b a
  | .add => .Binary .Add a b
  | .sub => .Binary .Sub a b
  | _ => .NoMatch

def bin (op : Op) (a b : Pair) : Pair := (.bin op a.1 b.1, binE op a.2 b.2)

def pick {α : Type} [Inhabited α] (xs : Array α) : R α := do return xs[← next xs.size]!

/-- `e` with the parameter `n` replaced by `a`: an application of `f`, as the
binary inlines it. -/
partial def subst (a : Ex) : Ex → Ex
  | .var n => if n == `n then a else .var n
  | .not x => .not (subst a x)
  | .neg x => .neg (subst a x)
  | .bin op x y => .bin op (subst a x) (subst a y)
  | .when g x y => .when g (subst a x) (subst a y)
  | .ite c x y => .ite (subst a c) (subst a x) (subst a y)
  | .cardinality c xs => .cardinality c (xs.map (subst a))
  | .index q i pos u => .index (subst a q) (subst a i) pos u
  | .seqLit xs => .seqLit (xs.map (subst a))
  | .ctor t i xs => .ctor t i (xs.map (subst a))
  | .field x i => .field (subst a x) i
  | .match s arms pos armPos u ps =>
    .match (subst a s) (arms.map fun (p, g, b) => (p, g.map (subst a), subst a b)) pos armPos u ps
  | .table pos rows u => .table pos (rows.map fun (k, c, v) => (k, c.map (subst a), subst a v)) u
  | e => e

/-- The program: `C0`'s and `f`'s bodies, as the binary and the semantics
hold them. -/
structure Prog where
  c0 : Pair
  f : Pair

/-- An arm, as both hold it. -/
abbrev Arm := (Pat × Option Ex × Ex) × (lang.Pattern String) × (lang.Expr String) × (lang.Expr String)

/-- A `match` of the semantics, from its scrutinee and arms. -/
def matchE (s : lang.Expr String) : List ((lang.Pattern String) × (lang.Expr String) × (lang.Expr String)) → (lang.Expr String)
  | [] => .NoMatch
  | (p, g, b) :: arms => .Match s p g b (matchE s arms)

mutual
/-- An expression of type `t`, at most `d` deep. -/
partial def gen (P : Prog) (sc : Scope) (t : Ty) (d : Nat) : R Pair := do
  if d = 0 then return ← genLeaf P sc t
  match t with
  | .int =>
    match ← next 11 with
    | 0 => let a ← gen P sc .int (d - 1); return (.neg a.1, .Unary .Neg a.2)
    | 1 => return bin (← pick #[Op.add, .sub]) (← gen P sc .int (d - 1)) (← gen P sc .int (d - 1))
    | 2 => genIte P sc t d
    | 3 =>
      let q ← gen P sc .seq (d - 1)
      let i ← gen P sc .int (d - 1)
      return (.index q.1 i.1 0 (FrenCli.Eval.unspecifiedFn .int), .Index q.2 i.2)
    | 4 =>
      let r ← gen P sc .r (d - 1)
      return (.field r.1 0, .Project r.2 "R" 0)
    | 5 => genMatch P sc t d
    | 6 => genIntMatch P sc t d
    | 7 => genTable P sc t d
    | 8 =>
      if sc.fn then
        let a ← gen P sc .int (d - 1)
        return (subst a.1 P.f.1, .Apply "f" (list [a.2]) (.Cons "n" .Nil) P.f.2)
      else genLeaf P sc t
    | 9 =>
      if sc.apps then
        let a ← gen P sc .int (d - 1)
        if (← next 2) = 0 then return (.app `u #[a.1], .Call "u" (list [a.2]))
        else return (.app `r #[a.1], .Recur "r" (list [a.2]))
      else genLeaf P sc t
    | _ => genLeaf P sc t
  | .bool =>
    match ← next 11 with
    | 0 => let a ← gen P sc .bool (d - 1); return (.not a.1, .Unary .Not a.2)
    | 1 => return bin (← pick #[Op.and, .or, .iff, .eq, .ne]) (← gen P sc .bool (d - 1)) (← gen P sc .bool (d - 1))
    | 2 => return bin (← pick #[Op.lt, .le, .gt, .ge, .eq, .ne]) (← gen P sc .int (d - 1)) (← gen P sc .int (d - 1))
    | 3 => return bin (← pick #[Op.eq, .ne]) (← gen P sc .str (d - 1)) (← gen P sc .str (d - 1))
    | 4 => return bin (← pick #[Op.eq, .ne]) (← gen P sc .e (d - 1)) (← gen P sc .e (d - 1))
    | 5 =>
      let g ← next 2
      let c ← gen P sc .bool (d - 1)
      let b ← gen P sc .bool (d - 1)
      -- `unless` where `g = 0`, and `when` otherwise.
      return (.when (g = 0) c.1 b.1, if g = 0 then .If c.2 trueE b.2 else .If c.2 b.2 trueE)
    | 6 => genIte P sc t d
    | 7 =>
      let c ← pick #[Fren.Core.Cardinality.atMostOne, .exactlyOne]
      let xs ← [0, 1, 2].mapM fun _ => gen P sc .bool (d - 1)
      return (.cardinality c (xs.map (·.1)).toArray,
        .Count (if c == .atMostOne then .AtMost else .Exactly) (list (xs.map (·.2))))
    | 8 => let r ← gen P sc .r (d - 1); return (.field r.1 1, .Project r.2 "R" 1)
    | 9 => genMatch P sc t d
    | _ => genTable P sc t d
  | .str =>
    match ← next 2 with
    | 0 => genIte P sc t d
    | _ => genLeaf P sc t
  | .seq =>
    let n ← next 4
    let xs ← (List.range n).mapM fun _ => gen P sc .int (d - 1)
    return (.seqLit (xs.map (·.1)).toArray, list (xs.map (·.2)))
  | .e =>
    if (← next 2) = 0 then
      let a ← gen P sc .int (d - 1)
      return (.ctor `E 0 #[a.1], .Construct "E::A" (list [a.2]))
    else genLeaf P sc t
  | .r =>
    let a ← gen P sc .int (d - 1)
    let b ← gen P sc .bool (d - 1)
    return (.ctor `R 0 #[a.1, b.1], .Construct "R" (list [a.2, b.2]))

partial def genLeaf (P : Prog) (sc : Scope) (t : Ty) : R Pair := do
  match t with
  | .int =>
    let bs := sc.binders
    let k ← next 5
    if k = 0 ∧ sc.vars then
      let x ← pick #["x", "y"]
      return (.var (Lean.Name.mkSimple x), .Var x)
    else if k = 1 ∧ sc.param then return (.var `n, .Var "n")
    else if k = 2 ∧ sc.const then return (.const `C0 P.c0.1, .Apply "C0" .Nil .Nil P.c0.2)
    else if k = 3 ∧ bs.length > 0 then
      let n := bs[← next bs.length]!
      return (.bound n, .Var n.toString)
    else return intLit (← small)
  | .bool =>
    let k ← next 2
    if k = 0 ∧ sc.vars then
      let p ← pick #["p", "q"]
      return (.var (Lean.Name.mkSimple p), .Var p)
    else return boolLit ((← next 2) = 0)
  | .str =>
    let s ← pick #["", "a", "b"]
    return (.lit (.str s), .Literal (.Text s))
  | .seq => return (.seqLit #[], .Nil)
  | .e => return (.ctor `E 1 #[], .Construct "E::B" .Nil)
  | .r => return (.ctor `R 0 #[(intLit 0).1, (boolLit true).1], .Construct "R" (list [(intLit 0).2, (boolLit true).2]))

partial def genIte (P : Prog) (sc : Scope) (t : Ty) (d : Nat) : R Pair := do
  let c ← gen P sc .bool (d - 1)
  let a ← gen P sc t (d - 1)
  let b ← gen P sc t (d - 1)
  return (.ite c.1 a.1 b.1, .If c.2 a.2 b.2)

/-- A guard, or none, and the semantics' guard, `true` where there is none. -/
partial def genGuard (P : Prog) (sc : Scope) (d : Nat) : R (Option Ex × (lang.Expr String)) := do
  if (← next 3) = 0 then
    let g ← gen P sc .bool (d - 1)
    return (some g.1, g.2)
  else return (none, trueE)

/-- A `match` over `E`, with one to three arms, which may not be exhaustive. -/
partial def genMatch (P : Prog) (sc : Scope) (t : Ty) (d : Nat) : R Pair := do
  let s ← gen P sc .e (d - 1)
  let y := Lean.Name.mkSimple s!"y{d}"
  let n ← next 3
  let arms : List Arm ← (List.range (n + 1)).mapM fun _ => do
    match ← next 5 with
    | 0 =>
      let sc' := { sc with binders := y :: sc.binders }
      let g ← genGuard P sc' d
      let b ← gen P sc' t (d - 1)
      return ((Pat.ctor 0 #[.bind y], g.1, b.1), .Variant "E::A" (.Cons (.Binder y.toString) .Nil), g.2, b.2)
    | 1 =>
      let g ← genGuard P sc d; let b ← gen P sc t (d - 1)
      return ((Pat.ctor 0 #[.wild], g.1, b.1), .Variant "E::A" (.Cons .Wildcard .Nil), g.2, b.2)
    | 2 =>
      let g ← genGuard P sc d; let b ← gen P sc t (d - 1)
      return ((Pat.ctor 1 #[], g.1, b.1), .Variant "E::B" .Nil, g.2, b.2)
    -- An or-pattern of both variants, which `Ex.dispatch` tries for each.
    | 3 =>
      let g ← genGuard P sc d; let b ← gen P sc t (d - 1)
      return ((Pat.alts #[.ctor 1 #[], .ctor 0 #[.wild]], g.1, b.1),
        .Or (.Variant "E::B" .Nil) (.Variant "E::A" (.Cons .Wildcard .Nil)), g.2, b.2)
    | _ =>
      let g ← genGuard P sc d; let b ← gen P sc t (d - 1)
      return ((Pat.wild, g.1, b.1), .Wildcard, g.2, b.2)
  return (.match s.1 (arms.map (·.1)).toArray 0 #[] none none, matchE s.2 (arms.map (·.2)))

/-- A `match` over an integer, with literal and range patterns. -/
partial def genIntMatch (P : Prog) (sc : Scope) (t : Ty) (d : Nat) : R Pair := do
  let s ← gen P sc .int (d - 1)
  let n ← next 3
  let arms : List Arm ← (List.range (n + 1)).mapM fun _ => do
    let lo ← small
    let w ← next 3
    let (p, q) : Pat × (lang.Pattern String) := match (← next 3) with
      | 0 => (Pat.int (some lo) (some lo), .Literal (.Integer lo))
      | 1 => (Pat.int (some lo) (some (lo + w)), .Between lo (lo + w))
      | _ => (Pat.wild, .Wildcard)
    let g ← genGuard P sc d
    let b ← gen P sc t (d - 1)
    return ((p, g.1, b.1), q, g.2, b.2)
  return (.match s.1 (arms.map (·.1)).toArray 0 #[] none none, matchE s.2 (arms.map (·.2)))

/-- A table of one to three rows, the last perhaps `_`. -/
partial def genTable (P : Prog) (sc : Scope) (t : Ty) (d : Nat) : R Pair := do
  let n ← next 3
  let rows ← (List.range (n + 1)).mapM fun k => do
    let v ← gen P sc t (d - 1)
    if k = n && (← next 2) = 0 then return ((k, (none : Option Ex), v.1), (none : Option (lang.Expr String)), v.2)
    let c ← gen P sc .bool (d - 1)
    return ((k, some c.1, v.1), some c.2, v.2)
  let tableE := rows.foldr (init := lang.Expr.NoMatch) fun (_, c, v) rest =>
    match c with
    | some c => .If c v rest
    | none => v
  return (.table 0 (rows.map (·.1)).toArray none, tableE)
end

/-- A program: `C0`, closed, and `f(n)`, which may apply `C0`. -/
def genProg : R Prog := do
  let none : Prog := ⟨intLit 0, intLit 0⟩
  let c0 ← gen none { vars := false, const := false, fn := false, apps := false } .int 2
  let P : Prog := ⟨c0, intLit 0⟩
  let f ← gen P { vars := false, param := true, fn := false, apps := false } .int 2
  return ⟨c0, f⟩

/-- A value of the binary's, as the semantics has it. -/
partial def toValue : Val → Option lang.Value
  | .bool b => some (lang.truth b)
  | .int i => some (.Integer i)
  | .str s => some (.Text s)
  | .seq vs => return listValue (← vs.toList.mapM toValue)
  | .ctor t i vs => do
    let name := if t == `E then (if i = 0 then "E::A" else "E::B") else t.toString
    return .Constructed name (listValue (← vs.toList.mapM toValue))
  | _ => none
where
  listValue : List lang.Value → lang.Value
    | [] => .Nil
    | v :: vs => .Cons v (listValue vs)

/-- One behaviour: each variable's value. -/
def behaviour : R (List (String × Val)) := do
  let ints ← ["x", "y"].mapM fun x => do return (x, Val.int (← small))
  let bools ← ["p", "q"].mapM fun x => do return (x, Val.bool ((← next 2) = 0))
  return ints ++ bools

/-- The environment of a behaviour. -/
def envOf (b : List (String × Val)) : lang.Env :=
  b.foldr (init := .Empty) fun (x, v) env =>
    .Bind x (match toValue v with | some w => .Defined w | none => .Undefined) env

def interp : lang.Interp := ⟨.Empty, .Empty, .Empty⟩

/-- Some of the integers from `-6` to `6`, each with a random value. -/
def genPoints : R (List (Int × Int)) := do
  let mut out := []
  for k in [0:13] do
    if (← next 4) != 0 then out := ((k : Int) - 6, ← small) :: out
  return out

/-- The graph of `g` at the points `pts`, in order. -/
def graphOf (g : String) (pts : List (Int × Int)) : lang.Graph :=
  pts.foldr (init := .Empty) fun (k, v) rest => .Point g (.Cons (.Integer k) .Nil) (.Integer v) rest

/-- The binary's interpretation of `u`, at the points `us`, and of `r`, by
its body `n + 1`. -/
def binaryInterp (us : List (Int × Int)) : FrenCli.Eval.Interp where
  fn f vs := if f == `u then (match vs with | #[.int k] => (us.lookup k).map .int | _ => none) else none
  recDefs f := if f == `r then some (#[`n], .bin .add (.bound `n) (.lit (.int 1))) else none

/-- The semantics' interpretation of `u`, at the points `us`, and of `r`, at
the integers `rs`, where it is their successor, as its body says. -/
def semanticInterp (us : List (Int × Int)) (rs : List Int) : lang.Interp :=
  ⟨graphOf "u" us, graphOf "r" (rs.map fun k => (k, k + 1)), .Empty⟩

/-- Whether `e` applies an uninterpreted function or a structural recursion. -/
def applies : lang.Expr String → Bool
  | .Call _ _ | .Recur _ _ => true
  | .Unary _ a | .Is a _ | .Project a _ _ | .Construct _ a | .Count _ a | .Apply _ a _ _ => applies a
  | .Binary _ a b | .And a b | .Or a b | .Cons a b | .Index a b | .Let _ a b | .Method _ a b => applies a || applies b
  | .If a b c => applies a || applies b || applies c
  | .Match a _ b c d => applies a || applies b || applies c || applies d
  | _ => false

/-- The subset type `Pos` of the integers, whose invariant is `pos?`. -/
def posTy : Fren.Core.PTy := { ty := .int, invariants := #[{ name := `pos, predicate := `pos? }] }

/-- The definition of `pos?(x) := x > 0`. -/
def posDefs (f : Lean.Name) : Option (Array Lean.Name × Ex × FrenCli.Eval.VTy) :=
  if f == `pos? then some (#[`x], .bin .gt (.bound `x) (.lit (.int 0)), .bool) else none

/-- The shape of the record `RP(Pos)`, whose field's type has an invariant
that only `Fren.Core.PTy.invariantFree`'s descent through shapes sees. -/
def posShapes (p : Lean.Name) : Option Fren.Core.DataShape :=
  if p == `RP then some { isRecord := true, parts := #[#[posTy]] } else none

/-- The problems found on 3000 random expressions. -/
def run : Array String := Id.run do
  let mut failures := #[]
  let mut seed := 2026
  let mut defined := 0
  let mut unknown := 0
  let mut rebound := 0
  let mut closedOnes := 0
  let mut applied := 0
  let mut typedKnown := 0
  for k in [0:3000] do
    let ((_, e, b, us, rs), s) := (do
      let P ← genProg
      let t := #[Ty.bool, .int, .str, .e][k % 4]!
      let e ← gen P {} t 4
      return (P, e, ← behaviour, ← genPoints, (← genPoints).map Prod.fst)).run seed
    seed := s
    let look : FrenCli.Eval.Look := fun n => b.lookup n.toString
    let env := envOf b
    let i := semanticInterp us rs
    let w := lang.eval i env e.2
    if applies e.2 then applied := applied + 1
    match e.1.eval (binaryInterp us) look, w with
    | some v, .Defined w =>
      defined := defined + 1
      unless toValue v == some w do
        failures := failures.push s!"{repr e.2} in {repr b} is {repr v} by `Ex.eval`, but {repr w} by `lang::eval`"
    | some _, .Undefined => unknown := unknown + 1
    | none, .Defined _ =>
      failures := failures.push s!"{repr e.2} in {repr b} is well-defined by `lang::eval`, but `Ex.eval` does not know it"
    | none, .Undefined => unknown := unknown + 1
    -- An expression that mentions nothing has one outcome in every environment.
    if lang.free_vars e.2 = ∅ then
      closedOnes := closedOnes + 1
      unless lang.eval i .Empty e.2 == w do
        failures := failures.push s!"{repr e.2} mentions nothing, but its outcome differs in the empty environment"
    -- Compiling, which folds the parts that are known, keeps the value in
    -- every interpretation, one that gives each index out of range a value
    -- too, as enumeration's does (`Ex.compile`, `Interp.outOfRange`).
    for I in [binaryInterp us, { binaryInterp us with outOfRange := fun _ => some (.int 7) }] do
      let once := e.1.compile (fun _ => none) none
      unless once.eval I look == e.1.eval I look do
        failures := failures.push s!"{repr e.2} in {repr b} changes its value when compiled"
      -- Compiling again, which sees through `.dispatch`, keeps it too.
      unless (once.compile (fun _ => none) none).eval I look == e.1.eval I look do
        failures := failures.push s!"{repr e.2} in {repr b} changes its value when compiled twice"
    -- So does compiling a check that an integer is of the subset type
    -- `Pos`, whose invariant is a definition of the interpretation, which
    -- compiling may not fold without (`Ex.compile.fold`), and quantifiers
    -- over a bound name of type `Pos`, whose domain, a literal or not,
    -- has a value that is not one.
    if k % 4 == 1 then
      let I := { binaryInterp us with defs := posDefs }
      if e.1.compile (fun _ => none) none matches .known (some (.int _)) then typedKnown := typedKnown + 1
      let vs : Array Val := #[.int ((k / 4 % 5 : Nat) - 2 : Int), .int 2]
      let quant (dom : Ex) (body : Ex) : Ex := .quant 0 0 (k / 4 % 2 == 0) #[`i] #[some dom] #[posTy] body
      let checks : Array (String × Ex) := #[
        ("checked to be of a subset type", .typed posTy #[] e.1),
        ("under a quantifier over a subset type", quant (.seqLit (vs.map .lit)) (.bin .le (.lit (.int 0)) e.1)),
        ("compared with a bound name of a subset type over a listed domain",
          quant (.lit (.seq vs)) (.bin .gt (.bound `i) e.1))]
      for (what, x) in checks do
        unless (x.compile (fun _ => none) none).eval I look == x.eval I look do
          failures := failures.push s!"{repr e.2} in {repr b}, {what}, changes its value when compiled"
      -- And a check that a record is of its type, whose field's type is
      -- `Pos`, which only the record's shape says (`posShapes`).
      let rp : Ex := .typed { ty := .record `RP [] } #[] (.ctor `RP 0 #[e.1])
      let I := { I with shapes := posShapes }
      unless (rp.compile posShapes none).eval I look == rp.eval I look do
        failures := failures.push s!"{repr e.2} in {repr b}, as the field of a record of a subset type, changes its value when compiled"
    -- A variable that the expression does not mention, rebound, changes nothing.
    for x in ["x", "y", "p", "q"] do
      unless decide (lang.Mention.Var x ∈ lang.free_vars e.2) do
        rebound := rebound + 1
        let env' := lang.Env.Bind x (.Defined (.Integer 7)) env
        unless lang.eval i env' e.2 == w do
          failures := failures.push s!"{repr e.2} in {repr b} changes when `{x}`, which it does not mention, is rebound"
  -- `lint::manual_at_most_one_defined`: of two well-defined `Bool`s, the
  -- `and` and the call of `at_most_one?` are both well-defined.
  let mut pairs := 0
  for k in [0:500] do
    let ((a, c), s) := (do
      let P ← genProg
      return (← gen P {} .bool 3, ← gen P {} .bool 3)).run seed
    seed := s
    let env := envOf (behaviour.run' seed)
    if (lang.eval interp env a.2) matches .Defined _ && (lang.eval interp env c.2) matches .Defined _ then
      pairs := pairs + 1
      unless (lang.eval interp env (.And a.2 c.2)) matches .Defined _
          && (lang.eval interp env (.Count .AtMost (list [a.2, c.2]))) matches .Defined _ do
        failures := failures.push s!"{repr a.2} and {repr c.2}: the `and` or the call is not well-defined"
    let _ := k
  if pairs < 100 then failures := failures.push s!"only {pairs} pairs of operands were well-defined"
  -- Each kind of outcome happens, so that the test is not vacuous.
  if defined < 1000 then failures := failures.push s!"only {defined} expressions were well-defined"
  if unknown < 50 then failures := failures.push s!"only {unknown} expressions were undefined"
  if rebound < 1000 then failures := failures.push s!"only {rebound} variables were rebound"
  if closedOnes < 100 then failures := failures.push s!"only {closedOnes} expressions mentioned nothing"
  if applied < 300 then failures := failures.push s!"only {applied} expressions applied `u` or `r`"
  if typedKnown < 50 then failures := failures.push s!"only {typedKnown} subset-type checks were of a known integer"
  return failures

/-- A random pattern, at most `d` deep, over `Bool`s, integers, strings
and variants of index 0 to 2 with up to two values. -/
partial def genPat (d : Nat) : R Pat := do
  match ← next (if d == 0 then 6 else 8) with
  | 0 => return .wild
  | 1 => return .bind `z
  | 2 => return .bool ((← next 2) == 0)
  | 3 => let lo ← small; return .int (some lo) (some (lo + (← next 3)))
  | 4 => return .str (if (← next 2) == 0 then "a" else "b")
  | 5 => return .ctor (← next 3) #[]
  | 6 => return .ctor (← next 3) (← (List.range (← next 3)).toArray.mapM fun _ => genPat (d - 1))
  | _ => return .alts (← (List.range (1 + (← next 3))).toArray.mapM fun _ => genPat (d - 1))

/-- A random value that `genPat`'s patterns may match. -/
partial def genVal (d : Nat) : R Val := do
  match ← next (if d == 0 then 4 else 5) with
  | 0 => return .bool ((← next 2) == 0)
  | 1 => return .int (← small)
  | 2 => return .str (if (← next 2) == 0 then "a" else "b")
  | 3 => return .ctor `E (← next 3) #[]
  | _ => return .ctor `E (← next 3) (← (List.range (← next 3)).toArray.mapM fun _ => genVal (d - 1))

/-- The premise of `firstCase_filter` that `Ex.dispatch` rests on: where
`Pat.mayMatchCtor idx p` is `false`, `p` matches no variant of index
`idx` (`Pat.matchInto`), on random patterns and values. -/
def mayMatchCtorSound : Array String := Id.run do
  let mut failures := #[]
  let mut seed := 11
  let mut excluded := 0
  let mut matched := 0
  for _ in [0:20000] do
    let ((p, v), s) := (do return (← genPat 3, ← genVal 2)).run seed
    seed := s
    let .ctor _ idx _ := v | continue
    let m := p.matchInto v #[]
    if m.isSome then matched := matched + 1
    if !p.mayMatchCtor idx then
      excluded := excluded + 1
      if m.isSome then failures := failures.push s!"a pattern that `mayMatchCtor {idx}` rules out matches a variant of index {idx}"
  if excluded < 1000 then failures := failures.push s!"only {excluded} patterns were ruled out"
  if matched < 1000 then failures := failures.push s!"only {matched} patterns matched"
  return failures

/-- The recursion `g(a, b)` of `compiledRecursion`: a `match` on `a`, an
`E`, whose first arm binds `b`, which shadows the parameter, the second
reads the parameter, and the third applies `g` again. -/
def gBody : Ex :=
  let a := Ex.bound `g.a
  let b := Ex.bound `g.b
  .match a #[
    (.ctor 0 #[.bind `g.b], some (.bin .gt b (.lit (.int 0))), .bin .add b (.lit (.int 1))),
    (.ctor 0 #[.wild], none, .bin .sub b (.lit (.int 1))),
    (.ctor 1 #[], none, .ite (.bin .gt b (.lit (.int 0)))
      (.bin .add (.app `g #[a, .bin .sub b (.lit (.int 1))]) (.lit (.int 1))) (.lit (.int 10)))]
    0 #[] none none

/-- `g`'s value, as its body says, at both arguments. -/
def gModel : Val → Int → Option Int
  | .ctor _ 0 #[.int k], b => some (if k > 0 then k + 1 else b - 1)
  | .ctor _ 1 #[], b => some (if b > 0 then b + 10 else 10)
  | _, _ => none

/-- Compiling a structural recursion's body, as testing does
(`Spec.withCompiledRecs`), keeps the value of every application of it:
with 0, 1 and 2 arguments, of either variant or neither. -/
def compiledRecursion : Array String := Id.run do
  let sp : FrenCli.Eval.Spec := { recDefs := ({} : Lean.NameMap _).insert `g (#[`g.a, `g.b], gBody) }
  let compiled := sp.withCompiledRecs fun _ => none
  let I : FrenCli.Eval.Interp := { recDefs := sp.recDefs.find? }
  let J : FrenCli.Eval.Interp := { recDefs := compiled.recDefs.find? }
  let mut failures := #[]
  let mut seed := 5
  let mut defined := 0
  unless compiled.recDefs.find? `g |>.any fun (_, b) => b matches .dispatch .. do
    failures := failures.push "`Spec.withCompiledRecs` did not compile `g`'s body"
  for _ in [0:2000] do
    let ((n, a, b), s) := (do
      let a : Val ← match ← next 3 with
        | 0 => pure (.ctor `E 0 #[.int (← small)])
        | 1 => pure (.ctor `E 1 #[])
        | _ => pure (.int (← small))
      return (← next 3, a, ← small)).run seed
    seed := s
    let args := #[Ex.lit a, .lit (.int b)].extract 0 n
    let e := Ex.app `g args
    let v := e.eval I (fun _ => none)
    unless (e.eval J fun _ => none) == v do
      failures := failures.push s!"`g` applied to {n} arguments changes its value when its body is compiled"
    if n == 2 then
      unless v == (gModel a b).map .int do
        failures := failures.push s!"`g` applied to two arguments has the value {repr v}, not {gModel a b}"
      if v.isSome then defined := defined + 1
  if defined < 300 then failures := failures.push s!"only {defined} applications of `g` had values"
  return failures

/-- `lint::written_scopes`: in an environment that binds `r` to a reply and
`v` to another value, the binder `v` of the reply's payload and the
variable `v` differ. -/
def writtenScopes : Bool :=
  let env : lang.Env := .Bind "r" (.Defined (.Constructed "Reply::Value" (.Cons (.Integer 1) .Nil)))
    (.Bind "v" (.Defined (.Integer 2)) .Empty)
  let inThen := lang.eval interp env (.Match (.Var "r") (.Variant "Reply::Value" (.Cons (.Binder "v") .Nil))
    trueE (.Var "v") .NoMatch)
  inThen == .Defined (.Integer 1) && inThen != lang.eval interp env (.Var "v")

#guard writtenScopes

/-- `lint::ifs_same_cond_taken`: `if p then a else if q then b else d`, for
each truth of `p` and `q`, has `b`'s outcome exactly where `p` is `false`
and `q` `true`, and where `p` and `q` have the same value, the outcome
that it has without the second test. -/
def ifsSameCondTaken : Bool :=
  let (a, b, d) : lang.Value × lang.Value × lang.Value := (.Integer 1, .Integer 2, .Integer 3)
  [false, true].all fun p => [false, true].all fun q =>
    let env : lang.Env := .Bind "p" (.Defined (lang.truth p)) (.Bind "q" (.Defined (lang.truth q)) .Empty)
    let chain := lang.eval interp env (.If (.Var "p") (.Literal a) (.If (.Var "q") (.Literal b) (.Literal d)))
    let without := lang.eval interp env (.If (.Var "p") (.Literal a) (.Literal d))
    chain == .Defined (if p then a else if q then b else d)
      && (chain == .Defined b) == (!p && q)
      && (p != q || chain == without)

#guard ifsSameCondTaken

/-! ## The coincidence lemma over interpretations

Expressions of the semantics alone, with applications of an uninterpreted
function `u` (`Call`), of a structural recursion `r` (`Recur`) and of a
defined function `f` whose body may apply either (`Apply`), are evaluated
under interpretations that agree on their structural recursions and
primitive operations, and differ in `u`. -/

/-- An integer expression over `x`, `y`, `n` (in a body), `u` and `r`. -/
partial def genL (inBody : Bool) : Nat → R (lang.Expr String)
  | 0 => do
    match ← next 4 with
    | 0 =>
      let x ← pick #["x", "y"]
      return .Var (if inBody then "n" else x)
    | _ => return .Literal (.Integer (← small))
  | d + 1 => do
    match ← next 8 with
    | 0 => return .Binary .Add (← genL inBody d) (← genL inBody d)
    | 1 => return .If (.Binary .Lt (← genL inBody d) (← genL inBody d)) (← genL inBody d) (← genL inBody d)
    | 2 => return .Call "u" (list [← genL inBody d])
    | 3 => return .Recur "r" (list [← genL inBody d])
    | 4 => if inBody then genL inBody d else
        return .Apply "f" (list [← genL inBody d]) (.Cons "n" .Nil) (← genL true d)
    | 5 => if inBody then genL inBody d else
        return .Let "z" (← genL inBody d) (.Binary .Add (.Var "z") (← genL inBody d))
    | _ => genL inBody 0

/-- A graph of `g` at the integers from `-6` to `6`, with random values. -/
def genGraph (g : String) : R lang.Graph := do
  let mut out := lang.Graph.Empty
  for k in [0:13] do
    if (← next 4) != 0 then
      out := .Point g (.Cons (.Integer ((k : Int) - 6)) .Nil) (.Integer (← small)) out
  return out

/-- The problems found on random expressions under varying interpretations. -/
def runInterp : Array String := Id.run do
  let mut failures := #[]
  let mut seed := 7
  let mut closedOnes := 0
  let mut agreeing := 0
  for _ in [0:2000] do
    let ((e, fs, gs, rs, b), s) := (do
      return (← genL false 4, ← genGraph "u", ← genGraph "u", ← genGraph "r", ← behaviour)).run seed
    seed := s
    let i : lang.Interp := ⟨fs, rs, .Empty⟩
    let j : lang.Interp := ⟨gs, rs, .Empty⟩
    let env := envOf b
    -- `lang::closed`: under any two such interpretations, in any environment.
    if lang.free_vars e = ∅ then
      closedOnes := closedOnes + 1
      unless lang.eval i env e == lang.eval j .Empty e do
        failures := failures.push s!"{repr e} mentions nothing, but its outcome differs between interpretations"
    -- `lang::coincidence`: where `u` is not mentioned, it may differ.
    if !decide (lang.Mention.Fn "u" ∈ lang.free_vars e) then
      agreeing := agreeing + 1
      unless lang.eval i env e == lang.eval j env e do
        failures := failures.push s!"{repr e} does not mention `u`, but its outcome depends on it"
  if closedOnes < 100 then failures := failures.push s!"only {closedOnes} expressions mentioned nothing"
  if agreeing < 300 then failures := failures.push s!"only {agreeing} expressions did not mention `u`"
  return failures

/-- The counterexample of the review of #391: a constant whose definition
applies a structural recursion mentions nothing, and has one outcome under
interpretations with the same recursions; one that applies an uninterpreted
function mentions it. -/
def constantOfRecursion : Bool :=
  let e : lang.Expr String := .Apply "C" .Nil .Nil (.Recur "r" .Nil)
  let rs : lang.Graph := .Point "r" .Nil .True .Empty
  let viaCall : lang.Expr String := .Apply "C" .Nil .Nil (.Call "u" .Nil)
  decide (lang.free_vars e = ∅)
    && lang.eval ⟨.Point "u" .Nil .False .Empty, rs, .Empty⟩ .Empty e == lang.eval ⟨.Empty, rs, .Empty⟩ .Empty e
    && decide (lang.Mention.Fn "u" ∈ lang.free_vars viaCall)

#guard constantOfRecursion

#eval show IO Unit from do
  let failures := run ++ runInterp ++ mayMatchCtorSound ++ compiledRecursion
  unless failures.isEmpty do
    throw (IO.userError s!"`lang::eval` and `Ex.eval` disagree:\n{"\n".intercalate (failures.toList.take 5)}")

end Fren.Test.Semantics
