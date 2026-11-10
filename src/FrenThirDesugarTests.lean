module

public import FrenThirDesugar
public import FrenHirToThir
public import FrenGen
public import Plausible

/-! Property tests of THIR desugaring on generated input of its own IR, under
Plausible. An input is a generated THIR module, well typed by construction or
carrying one injected fault, with parentheses then added around any of its
nodes (`FrenGen.Thir.parens`). The pass is total, so no property has a premise
and nothing is discarded; the census reports what the samples covered. -/

public section
namespace FrenThirDesugarTests
open FrenExpr FrenModule.Core FrenThirDesugar FrenGen.Thir Plausible
open scoped Plausible.Decorations
open Fren (Sexp)

/-- A generated module and the salt that places its added parentheses. -/
structure Input where
  case : Case
  salt : Nat

/-- The pass's input. -/
def Input.thir (i : Input) : Thir := parens i.salt i.case.thir

instance : Repr Input where
  reprPrec i _ := Fren.Sexp.pretty (i.thir.toSexp true)

/-- Plausible's own generator as the generator's source of choices. -/
def gen (fault : Option Fault) : Gen Input := Gen.sized fun size => do
  let pick (n : Nat) : Gen Nat := do
    let k ← Gen.choose Nat 0 (n - 1) (by omega)
    pure k.val
  let salt ← Gen.choose Nat 0 1000000 (by decide)
  return ⟨(← genCaseRetry pick size fault 8).1, salt.val⟩

structure WellTyped where
  input : Input

structure Faulty where
  input : Input

instance : Repr WellTyped := ⟨fun c n => reprPrec c.input n⟩
instance : Repr Faulty := ⟨fun c n => reprPrec c.input n⟩
instance : Shrinkable WellTyped := {}
instance : Shrinkable Faulty := {}
instance : Arbitrary WellTyped := ⟨(⟨·⟩) <$> gen none⟩
instance : Arbitrary Faulty where
  arbitrary := do
    let k ← Gen.choose Nat 0 (Fault.all.length - 1) (by decide)
    (⟨·⟩) <$> gen (Fault.all[k.val]?)

/-- The printed form without its parentheses: each `(paren header.. body)`
list is replaced by its body. This reads the printed tree only, not `ExprF`. -/
partial def unparen : Sexp → Sexp
  | .list items =>
    let items := items.map unparen
    if items[0]? == some (Sexp.symbol "paren") then items.back?.getD (.list items) else .list items
  | s => s

/-- The output is the input without its parentheses and is otherwise the same
tree: every other node, with its origin, its type and its children in order,
every signature, member and origin table. Faulty input included: the pass is
total and does not depend on typing. -/
def removesOnlyParens (i : Input) : Bool :=
  (desugar i.thir).toSexp true == unparen (i.thir.toSexp true)

/-- The same source with every parenthesis deleted, as HIR. -/
def unparenHir : Expr .hir → Expr .hir :=
  Expr.fold fun o a n => match n with
    | .paren _ e => e
    | n => ⟨o, a, n⟩

def unparenModule (m : Hir) : Hir :=
  ⟨m.id, m.items.map fun
    | .enum e os => .enum e os
    | .function f os => .function {f with body := unparenHir f.body} os
    | .check c os =>
      .check {c with members := c.members.map fun mem => {mem with body := unparenHir mem.body}} os⟩

/-- Desugaring commutes with typing: the output is exactly what the type
checker gives for the input's erasure with the parentheses deleted, node types
and decisions included. So the output of well-typed input is well typed. -/
def typedWithoutParens (i : Input) : Bool :=
  match FrenHirToThir.Pass.typeModule (unparenModule i.thir.eraseTypes) with
  | .ok typed => typed.toSexp true == (desugar i.thir).toSexp true
  | .error _ => false

/-- Where the parentheses were does not matter: the bodies are those of the
module as generated, before any parenthesis was added, origins included. -/
def blindToAdded (i : Input) : Bool :=
  (desugar i.thir).bodies.map (·.toSexp true) == (desugar i.case.thir).bodies.map (·.toSexp true)

/-- Each removed parenthesis removes one node, and scoping is unchanged
(a parenthesis binds nothing). -/
def countsAndScope (i : Input) : Bool :=
  let input := i.thir
  let output := desugar input
  (output.bodies.map (·.size)).toList ==
      (input.bodies.map fun e => e.size - parenNodes e).toList &&
    output.scoped == input.scoped

/-- Generator check, not the pass: adding parentheses keeps the module well
typed: the type checker recovers it exactly from its erasure. -/
def generatorSound (i : Input) : Bool :=
  match FrenHirToThir.Pass.typeModule i.thir.eraseTypes with
  | .ok typed => typed.toSexp true == i.thir.toSexp true
  | .error _ => false

private def property (label : String) (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 500, maxSize := 12, randomSeed := some 20261110}
  IO.println s!"{label}: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError s!"THIR desugaring property failed: {label}")

/-- What 200 seeded inputs covered: parentheses in all, those directly inside
another, those at a body's root, and bodies with none. -/
def census : IO Unit := do
  let mut parens := 0
  let mut nested := 0
  let mut root := 0
  let mut bare := 0
  let mut bodies := 0
  let mut nodes := 0
  for seed in [:200] do
    let input : Input := ⟨(seeded seed (seed % 13) none).1, seed * 7919⟩
    for body in input.thir.bodies do
      bodies := bodies + 1
      nodes := nodes + body.size
      let k := parenNodes body
      parens := parens + k
      if k == 0 then bare := bare + 1
      if let .paren _ inner := body.node then
        root := root + 1
        if let .paren _ _ := inner.node then nested := nested + 1
  unless parens > 0 && nested > 0 && root > 0 && bare > 0 do
    throw (IO.userError s!"THIR desugaring census lacks a form: {parens} {nested} {root} {bare}")
  IO.println s!"THIR desugaring census: 200 modules, {bodies} bodies, {nodes} nodes, {parens} parentheses \
    ({root} at a body's root, {nested} of those doubled), {bare} bodies without any; discarded=0"

/-- Properties over Plausible-generated modules of the pass's own input IR. -/
def run : IO Unit := do
  property "output is the input with only its parentheses removed (well-typed input)" <|
    ∀ c : WellTyped, removesOnlyParens c.input = true
  property "output is the input with only its parentheses removed (one injected fault)" <|
    ∀ c : Faulty, removesOnlyParens c.input = true
  property "desugaring commutes with typing: output is the typing of the parenthesis-free input" <|
    ∀ c : WellTyped, typedWithoutParens c.input = true
  property "added parentheses do not change the output's bodies" <|
    ∀ c : Faulty, blindToAdded c.input = true
  property "one node fewer for each parenthesis; scoping unchanged" <|
    ∀ c : Faulty, countsAndScope c.input = true
  property "generator check (not the pass): input with added parentheses is well typed" <|
    ∀ c : WellTyped, generatorSound c.input = true
  census

#print axioms FrenThirDesugar.desugarExpr_paren
#print axioms FrenThirDesugar.desugarExpr_keeps

end FrenThirDesugarTests
