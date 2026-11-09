module

public import FrenHirToThirTests.Printer
public import Plausible

/-! Property tests of the separated HIR→THIR pass on generated input of its
own IR, under Plausible. A case is a THIR module that is well typed by
construction, or one with a single injected fault; the HIR input is its
erasure. No property has a premise, so nothing is discarded; the census
reports what the samples covered. -/

public section
namespace FrenHirToThirTests
open FrenExpr FrenModule.Core FrenHirToThir.Pass FrenGen.Thir Plausible
open scoped Plausible.Decorations

instance : Repr Case where
  reprPrec c _ := Fren.Sexp.pretty (c.thir.toSexp true) ++
    s!"\nexpected: {repr c.expected}\nsource:\n{Printer.module c.hir}"

/-- Plausible's own generator as the generator's source of choices. -/
def gen (fault : Option Fault) : Gen Case := Gen.sized fun size => do
  let pick (n : Nat) : Gen Nat := do
    let k ← Gen.choose Nat 0 (n - 1) (by omega)
    pure k.val
  return (← genCaseRetry pick size fault 8).1

structure WellTyped where
  case : Case

structure Faulty where
  case : Case

instance : Repr WellTyped := ⟨fun c n => reprPrec c.case n⟩
instance : Repr Faulty := ⟨fun c n => reprPrec c.case n⟩
instance : Shrinkable WellTyped := {}
instance : Shrinkable Faulty := {}
instance : Arbitrary WellTyped := ⟨(⟨·⟩) <$> gen none⟩
instance : Arbitrary Faulty where
  arbitrary := do
    let k ← Gen.choose Nat 0 (Fault.all.length - 1) (by decide)
    (⟨·⟩) <$> gen (Fault.all[k.val]?)

/-- The reason the pass must give for an injected fault. -/
def _root_.FrenGen.Thir.Outcome.reason : Outcome → Reason
  | .mismatch e f => .mismatch e f
  | .notValue id => .notValue id
  | .notCallable id => .notCallable (.item id)
  | .arity e f => .arity e f
  | .dangling i => .danglingLocal i
  | .matchNotEnum f => .matchNotEnum f
  | .emptyMatch => .emptyMatch

def exact (a b : Thir) : Bool := a.toSexp true == b.toSexp true
def exactHir (a b : Hir) : Bool := a.toSexp true == b.toSexp true

/-- Typing recovers exactly the generated typing (every node's type and every
decision, origins included), and erasing the result gives back the input. -/
def recovers (c : Case) : Bool :=
  match typeModule c.hir with
  | .ok out => exact out c.thir && exactHir out.eraseTypes c.hir
  | .error _ => false

/-- A faulty case is rejected at the injected node with the injected reason;
a case whose fault found no site is well typed and recovered. -/
def rejects (c : Case) : Bool :=
  match c.expected with
  | some e => match typeModule c.hir with
    | .error got => got == ⟨e.item, e.origin, e.outcome.reason⟩
    | .ok _ => false
  | none => recovers c

/-- Origins are message data only: moving every origin up by `k` (with `k`
unnamed entries in front of each table) and renaming every origin moves the
outcome's origins by `k` and changes nothing else. -/
def shiftExpr (k : Nat) : Expr p → Expr p :=
  Expr.fold fun o a n => ⟨o + k, a, match n with
    | .letE b v e => .letE {b with origin := b.origin + k} v e
    | .matchE s arms => .matchE s (arms.map fun (pat, e) => ({pat with origin := pat.origin + k}, e))
    | n => n⟩

def shiftParam (k : Nat) (q : Param) : Param := {q with origin := q.origin + k}

def shiftTable (k : Nat) (os : Array Origin) : Array Origin :=
  Array.replicate k ({} : Origin) ++ os.map fun o => {o with name := some "renamed"}

def shiftItem (k : Nat) : Item (Expr p) → Item (Expr p)
  | .enum e os => .enum {e with origin := e.origin + k} (shiftTable k os)
  | .function f os =>
    let f' : Function (Expr p) := ⟨f.id, f.origin + k, f.params.map (shiftParam k), f.result,
      shiftExpr k f.body⟩
    .function f' (shiftTable k os)
  | .check c os =>
    let members := c.members.map fun mem =>
      ({mem with origin := mem.origin + k, body := shiftExpr k mem.body} : Member (Expr p))
    .check ⟨c.id, c.origin + k, c.params.map (shiftParam k), members⟩ (shiftTable k os)

def shiftModule (k : Nat) (m : Module (Expr p)) : Module (Expr p) := ⟨m.id, m.items.map (shiftItem k)⟩

def originBlind (k : Nat) (c : Case) : Bool :=
  match typeModule c.hir, typeModule (shiftModule k c.hir) with
  | .ok a, .ok b => exact (shiftModule k a) b
  | .error a, .error b => b == {a with origin := a.origin + k}
  | _, _ => false

/-- Generated input is well scoped exactly when no dangling local was injected. -/
def scopedUnlessDangling (c : Case) : Bool :=
  c.hir.scoped == (c.expected.map (·.fault) != some .dangling)

private def property (label : String) (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 500, maxSize := 12, randomSeed := some 20261109}
  IO.println s!"{label}: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError s!"HIR→THIR property failed: {label}")

/-- Properties over Plausible-generated modules of the pass's own input IR. -/
def runGenerated : IO Unit := do
  property "well-typed THIR erased to HIR: typing recovers it exactly; erasure law" <|
    ∀ c : WellTyped, recovers c.case = true
  property "one injected fault: rejected at that node with that reason" <|
    ∀ c : Faulty, rejects c.case = true
  property "origins and display names do not affect typing" <|
    ∀ (c : Faulty) (k : Nat), originBlind k c.case = true
  property "generator check (not the pass): input is well scoped unless a dangling local was injected" <|
    ∀ c : Faulty, scopedUnlessDangling c.case = true

end FrenHirToThirTests
