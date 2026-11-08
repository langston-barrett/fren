module

import scratch.expr.Codec
meta import scratch.expr.Codec

open ExprPrototype Fren

namespace ExprPrototype.Tests

def lit (n : Nat) : Expr p := .roll (.lit n)
def var (i : Nat) : Expr p := .roll (.var i)
def all (b : Expr p) : Expr p := .roll (.all b)
def arr (xs : Array (Expr p)) : Expr p := .roll (.array xs)
def letE (v b : Expr p) : Expr p := .roll (.letE v b)

/-- Intentional control: this shifts bound occurrences too. -/
def badShift (amount : Nat) (e : Expr p) : Expr p :=
  fold (fun | .var i => var (i + amount) | layer => .roll layer) e

/-- Intentional control: this fails to lift replacements under binders. -/
def badSubst (σ : Nat → Expr p) (e : Expr p) : Expr p :=
  fold (fun (layer : Layer p ((Nat → Expr p) → Expr p)) env =>
    match layer with
    | .var i => env i
    | layer => .roll (layer.mapChildren (fun _ child => child env))) e σ

def nodes (e : Expr p) : Nat := fold (fun layer => match layer with
  | .lit _ | .var _ => 1
  | .letE v b => 1 + v + b
  | .all b | .sugar _ b => 1 + b
  | .array xs => 1 + xs.foldl (· + ·) 0) e

/-- Finite test corpus, not the generator requested by #982. -/
def samples (p : Phase) : Array (Expr p) := Id.run do
  let atoms := #[lit 0, lit 7, var 0, var 1, var 2, var 5, arr #[]]
  let mut xs := atoms
  for a in atoms do
    xs := xs ++ #[all a, letE a (arr #[var 0, a]), arr #[a, all a, arr #[]]]
    if h : HasSugar p then xs := xs.push (.roll (.sugar h (all a)))
  xs := xs.push (all (letE (arr atoms) (all (arr xs))))
  return xs

def assert (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"prototype test failed: {name}")

def isOkEq [BEq α] (expected : α) : Except ε α → Bool
  | .ok actual => actual == expected
  | .error _ => false

def isErrorEq [BEq ε] (expected : ε) : Except ε α → Bool
  | .error actual => actual == expected
  | .ok _ => false

def isError : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

def checkPhase (p : Phase) : IO Nat := do
  let openBody : Expr p := all (arr #[var 0, var 1, all (arr #[var 0, var 1, var 2, var 3])])
  let shifted : Expr p := all (arr #[var 0, var 3, all (arr #[var 0, var 1, var 4, var 5])])
  assert "shift respects nested binders/arrays" (shift 2 0 openBody == shifted)
  assert "nonzero cutoff preserves nearer free indices"
    (shift 2 1 openBody == all (arr #[var 0, var 1, all (arr #[var 0, var 1, var 2, var 5])]))
  assert "wrong-cutoff control differs" (shift 2 1 openBody != shifted)
  assert "closed bound variable is unchanged" (shift 3 0 (all (var 0) : Expr p) == all (var 0))
  assert "bad-shift control is rejected by scope" (!scopeCheck 0 (badShift 1 (all (var 0) : Expr p)))
  assert "bad index zero at closed root" (!scopeCheck 0 (var 0 : Expr p))
  assert "bad index at exact context boundary" (!scopeCheck 2 (arr #[lit 3, var 2] : Expr p))
  assert "let value is outside its binder" (!scopeCheck 0 (letE (var 0) (var 0) : Expr p))
  assert "let body is inside its binder" (scopeCheck 0 (letE (lit 4) (all (arr #[var 0, var 1])) : Expr p))
  let replacement : Expr p := arr #[var 0, lit 9]
  let body : Expr p := letE (var 0) (all (arr #[var 0, var 1, var 2, var 3,
    all (arr #[var 0, var 1, var 2, var 3, var 4])]))
  let expected : Expr p := letE replacement (all (arr #[var 0, var 1, arr #[var 2, lit 9], var 2,
    all (arr #[var 0, var 1, var 2, arr #[var 3, lit 9], var 3])]))
  assert "substitution lifts open replacement and removes target slot" (substTop replacement body == expected)
  let env : Nat → Expr p := fun | 0 => replacement | i + 1 => var i
  assert "unlifted-substitution control differs" (badSubst env body != expected)
  assert "substitution result has remaining scope" (scopeCheck 1 expected)
  assert "raw malformed indices are handled totally" (substTop (lit 8) (var 99 : Expr p) == var 98)
  assert "array fold includes every nested child" (nodes (arr #[lit 1, all (var 0), arr #[lit 2, lit 3]] : Expr p) == 7)
  assert "let fold includes both value and body" (nodes (letE (lit 2) (all (var 0)) : Expr p) == 4)
  for e in samples p do
    assert "identity rename" (rename id e == e)
    assert "identity substitution" (subst var e == e)
    assert "zero shift" (shift 0 0 e == e)
    assert "shift composition" (shift 3 0 (shift 2 0 e) == shift 5 0 e)
    assert "fold reconstructs full tree" (fold Expr.roll e == e)
    for n in [:6] do
      if scopeCheck n e then
        assert "shift preserves enlarged scope" (scopeCheck (n + 2) (shift 2 0 e))
        assert "simultaneous closed substitution" (scopeCheck 0 (subst (fun _ => all (var 0)) e))
      if scopeCheck (n + 1) e then
        assert "closed top substitution" (scopeCheck n (substTop (all (var 0)) e))
  return (samples p).size

def traversalTests : IO Unit := do
  let visit (d x : Nat) : StateM (Array (Nat × Nat)) Nat := do
    modify (·.push (d, x))
    return x + 10
  let (mapped, seen) := (Layer.mapChildrenM visit (.letE 7 8 : Layer .high Nat)).run #[]
  assert "let traversal depth and order" (seen == #[(0, 7), (1, 8)] && mapped == .letE 17 18)
  let (_, seen) := (Layer.mapChildrenM visit (.all 9 : Layer .low Nat)).run #[]
  assert "quantifier traversal depth" (seen == #[(1, 9)])
  let (mapped, seen) := (Layer.mapChildrenM visit (.array #[3, 1, 4] : Layer .low Nat)).run #[]
  assert "array traversal preserves order" (seen == #[(0, 3), (0, 1), (0, 4)] && mapped == .array #[13, 11, 14])
  let (_, seen) := (Layer.mapChildrenM visit (.sugar rfl 9 : Layer .high Nat)).run #[]
  assert "gate adds no binder" (seen == #[(0, 9)])
  let (_, seen) := (Layer.mapChildrenM visit (.lit 2 : Layer .low Nat)).run #[]
  assert "literal has no children" seen.isEmpty
  let (_, seen) := (Layer.mapChildrenM visit (.var 2 : Layer .high Nat)).run #[]
  assert "variable has no children" seen.isEmpty
  let fail (d x : Nat) : Except String Nat := if x == 1 then .error s!"stop {d}" else .ok x
  assert "traversal propagates child failure"
    (isErrorEq "stop 0" (Layer.mapChildrenM fail (.array #[3, 1, 4] : Layer .low Nat)))
  -- State outside Except records whether traversal continued after failure.
  let stop (d x : Nat) : ExceptT String (StateM (Array Nat)) Nat := do
    modify (·.push x)
    if x == 1 then throw s!"stop {d}" else pure x
  let (result, trace) := ((Layer.mapChildrenM stop (.array #[3, 1, 4] : Layer .high Nat)).run).run #[]
  assert "array failure short circuits" (isErrorEq "stop 0" result && trace == #[3, 1])
  let (result, trace) := ((Layer.mapChildrenM stop (.letE 1 4 : Layer .high Nat)).run).run #[]
  assert "let failure short circuits before body" (isErrorEq "stop 0" result && trace == #[1])

def codecTests : IO Unit := do
  for layer in (#[.lit 4, .var 2, .letE 7 8, .all 1, .array #[], .array #[1, 2], .sugar rfl 3] : Array (Layer .high Nat)) do
    assert "high layer text roundtrip" (isOkEq layer (Sexp.decode (α := Layer .high Nat) (Sexp.encode layer)))
  for layer in (#[.lit 4, .var 2, .letE 7 8, .all 1, .array #[], .array #[1, 2]] : Array (Layer .low Nat)) do
    assert "low layer text roundtrip" (isOkEq layer (Sexp.decode (α := Layer .low Nat) (Sexp.encode layer)))
  assert "forbidden phase rejects sugar" (isError (Sexp.decode (α := Layer .low Nat) "(sugar 3)"))
  assert "wrong arity rejects" (isError (Sexp.decode (α := Layer .high Nat) "(let 1)"))
  assert "array child type rejects" (isError (Sexp.decode (α := Layer .high Nat) "(array (1 nope))"))
  assert "whole-tree encoding includes binders and array order"
    (Sexp.render (encodeExpr (letE (lit 4) (all (arr #[var 0, var 1])) : Expr .low)) ==
      "(let (lit 4) (all (array ((var 0) (var 1)))))")

end ExprPrototype.Tests

public def main : IO Unit := do
  let high ← ExprPrototype.Tests.checkPhase .high
  let low ← ExprPrototype.Tests.checkPhase .low
  ExprPrototype.Tests.traversalTests
  ExprPrototype.Tests.codecTests
  IO.println s!"expression prototype: passed; {high} high / {low} low corpus terms, both phases, binder/array/control/traversal/codec boundaries"
