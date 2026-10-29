-- fren-covers: lang::coincidence, lang::closed, lint::written_scopes, lint::manual_at_most_one_defined
-- keep-sorted start
import FrenCli.Eval
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
`match`es over `E` and over integers, with binders and guards, tables, and
the constant `C0` and the defined function `f(n)`, which both inline. The
primitive operations, `*`, `div`, `mod` and `++` of strings, are left out:
the semantics takes them from its interpretation. Where the semantics finds
an expression well-defined, the binary gives it the same value; where the
binary does not know it, the semantics finds it undefined. The binary may
know more, by its Kleene connectives.

Each expression is also evaluated in the behaviour with a variable that it
does not mention rebound, which the coincidence lemma (`lang::coincidence`)
says changes nothing, and, where it mentions nothing, in the empty
environment, which `lang::closed` says changes nothing either.
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
parameter `n` of `f`, `C0`, `f`, and the binders of the arms around it. -/
structure Scope where
  vars : Bool := true
  param : Bool := false
  const : Bool := true
  fn : Bool := true
  binders : List Lean.Name := []

abbrev Pair := Ex × lang.Expr

/-- A list expression of `es`. -/
def list : List lang.Expr → lang.Expr
  | [] => .Nil
  | e :: es => .Cons e (list es)

def intLit (k : Int) : Pair := (.lit (.int k), .Literal (.Integer k))
def boolLit (b : Bool) : Pair := (.lit (.bool b), .Literal (lang.truth b))
def trueE : lang.Expr := .Literal .True

/-- The binary operator `op` as the semantics has it, with its derived forms
translated (`Reqs/Lang/Semantics#derived-forms`). -/
def binE (op : Op) (a b : lang.Expr) : lang.Expr :=
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
  | .index q i pos => .index (subst a q) (subst a i) pos
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
abbrev Arm := (Pat × Option Ex × Ex) × lang.Pattern × lang.Expr × lang.Expr

/-- A `match` of the semantics, from its scrutinee and arms. -/
def matchE (s : lang.Expr) : List (lang.Pattern × lang.Expr × lang.Expr) → lang.Expr
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
      return (.index q.1 i.1 0, .Index q.2 i.2)
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
partial def genGuard (P : Prog) (sc : Scope) (d : Nat) : R (Option Ex × lang.Expr) := do
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
    match ← next 4 with
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
    let (p, q) : Pat × lang.Pattern := match (← next 3) with
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
    if k = n && (← next 2) = 0 then return ((k, (none : Option Ex), v.1), (none : Option lang.Expr), v.2)
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
  let c0 ← gen none { vars := false, const := false, fn := false } .int 2
  let P : Prog := ⟨c0, intLit 0⟩
  let f ← gen P { vars := false, param := true, fn := false } .int 2
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

def interp : lang.Interp := ⟨.Empty, .Empty⟩

/-- The problems found on 3000 random expressions. -/
def run : Array String := Id.run do
  let mut failures := #[]
  let mut seed := 2026
  let mut defined := 0
  let mut unknown := 0
  let mut rebound := 0
  let mut closedOnes := 0
  for k in [0:3000] do
    let ((_, e, b), s) := (do
      let P ← genProg
      let t := #[Ty.bool, .int, .str, .e][k % 4]!
      let e ← gen P {} t 4
      return (P, e, ← behaviour)).run seed
    seed := s
    let look : FrenCli.Eval.Look := fun n => b.lookup n.toString
    let env := envOf b
    let w := lang.eval interp env e.2
    match e.1.eval {} look, w with
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
      unless lang.eval interp .Empty e.2 == w do
        failures := failures.push s!"{repr e.2} mentions nothing, but its outcome differs in the empty environment"
    -- A variable that the expression does not mention, rebound, changes nothing.
    for x in ["x", "y", "p", "q"] do
      unless decide (lang.Mention.Var x ∈ lang.free_vars e.2) do
        rebound := rebound + 1
        let env' := lang.Env.Bind x (.Defined (.Integer 7)) env
        unless lang.eval interp env' e.2 == w do
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

#eval show IO Unit from do
  let failures := run
  unless failures.isEmpty do
    throw (IO.userError s!"`lang::eval` and `Ex.eval` disagree:\n{"\n".intercalate (failures.toList.take 5)}")

end Fren.Test.Semantics
