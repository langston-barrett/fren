module

public import FrenHirToThirTests.Properties
public import Plausible

/-! The separated pass against the existing checker, on the same generated
programs: print the HIR module as Fren source, parse and resolve it, read the
resolver's output into the IR core (which must give back the generated module)
and type it both ways. Both accept, with the same type at every node, or both
reject, with the same catalogue code at the same span. -/

public section
namespace FrenHirToThirTests
open FrenExpr FrenModule.Core FrenHirToThir.Pass FrenGen.Thir Plausible
open scoped Plausible.Decorations

/-- Every node's type, in postorder. -/
def postorder : Expr .thir → List Ty :=
  Expr.fold fun _ (ty : Ty) n => n.children.foldl (· ++ ·) [] ++ [ty]

/-- The legacy checker's value occurrences, in its postorder (callee
designators have no value type and are left out). -/
def legacyTypes (b : FrenModule.TypedBody) : List Ty :=
  b.occurrences.toList.filterMap fun o => match o.type with
    | .value ty => some ty
    | .callable _ => none

inductive Agreed where
  | accepted | rejected
  deriving BEq

def agreement (c : Case) (file : Nat) : Except String Agreed := do
  let source := Printer.module c.hir
  let doc ← (FrenParse.parseFile ⟨file⟩ source).mapError fun e =>
    s!"printed source does not parse: {repr e.diagnostic}\n{source}"
  let resolved ← (FrenAstToHir.resolve doc).mapError fun d =>
    s!"printed source does not resolve: {repr d}\n{source}"
  let lowered ← (FrenAstToHir.Lower.lower resolved).mapError fun d =>
    s!"resolver output does not lower: {repr d}\n{source}"
  unless lowered.same c.hir do throw s!"lowering does not give back the generated HIR\n{source}"
  match FrenHirToThir.check resolved, typeModule lowered with
  | .ok legacy, .ok core =>
    let ours := core.bodies.toList.map postorder
    let theirs := legacy.bodies.toList.map legacyTypes
    unless ours == theirs do throw s!"node types differ\n{source}"
    return .accepted
  | .error d, .error e =>
    unless d.code == e.code && some d.span == e.span lowered do
      throw s!"different errors: legacy {repr d}, core {repr e} at {repr (e.span lowered)}\n{source}"
    return .rejected
  | .ok _, .error e => throw s!"only the separated pass rejects: {repr e}\n{source}"
  | .error d, .ok _ => throw s!"only the legacy checker rejects: {repr d}\n{source}"

def agrees (c : Case) : Bool := (agreement c 91).isOk

structure PrintableFaulty where
  case : Case

instance : Repr PrintableFaulty := ⟨fun c n => reprPrec c.case n⟩
instance : Shrinkable PrintableFaulty := {}
instance : Arbitrary PrintableFaulty where
  arbitrary := do
    let faults := Fault.all.filter (·.printable)
    let k ← Gen.choose Nat 0 (faults.length - 1) (by decide)
    (⟨·⟩) <$> gen (faults[k.val]?)

private def property (label : String) (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 300, maxSize := 12, randomSeed := some 20261110}
  IO.println s!"{label}: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError s!"agreement property failed: {label}")

structure Census where
  samples : Nat := 0
  injected : Array Nat := Array.replicate Fault.all.length 0
  notInjected : Nat := 0
  forms : Array Nat := Array.replicate formNames.size 0
  nodes : Nat := 0
  accepted : Nat := 0
  rejected : Nat := 0
  deriving Repr

/-- A seeded census with the same generator: every property again, plus what
the samples covered. Fails if a form or a fault never occurs. -/
def census : IO Census := do
  let mut out : Census := {}
  for seed in [:240] do
    for fault in none :: Fault.all.map some do
      let (c, forms) := seeded seed (seed % 12) fault
      let nodes := (c.thir.bodies.toList.map Expr.size).sum
      out := {out with samples := out.samples + 1, nodes := out.nodes + nodes}
      out := {out with forms := (out.forms.zip forms).map fun (a, b) => a + b}
      match c.expected with
      | some e =>
        let i := (Fault.all.idxOf e.fault)
        out := {out with injected := out.injected.modify i (· + 1)}
      | none => if fault.isSome then out := {out with notInjected := out.notInjected + 1}
      unless rejects c && originBlind (seed % 5) c && scopedUnlessDangling c do
        throw (IO.userError s!"census: property failed for seed {seed}, fault {repr fault}")
      if fault.all (·.printable) then
        match agreement c 92 with
        | .ok .accepted => out := {out with accepted := out.accepted + 1}
        | .ok .rejected => out := {out with rejected := out.rejected + 1}
        | .error msg => throw (IO.userError s!"census: seed {seed}, fault {repr fault}: {msg}")
  unless out.forms.all (· > 0) && out.injected.all (· > 0) && out.accepted > 0 && out.rejected > 0 do
    throw (IO.userError s!"census became vacuous: {repr out}")
  return out

/-- Lowering reads the reference table and checks it against the tree: a
table with an entry missing, or with an entry of the wrong role, is refused. -/
def lowerControls : IO Unit := do
  let r ← resolved "mod m\nenum E { A }\nfn f(x: Int, b?): E := let y := x in match E::A { E::A => E::A }"
  let .ok hir := FrenAstToHir.Lower.lower r | throw (IO.userError "lowering refused resolver output")
  require hir.scoped "lowered HIR not scoped"
  require ((FrenAstToHir.Lower.lower {r with references := r.references.pop}).toOption.isNone)
    "lowering accepted a table with a missing entry"
  let wrongRole := r.references.map fun ref =>
    if ref.role == .pattern then {ref with role := .expression} else ref
  require ((FrenAstToHir.Lower.lower {r with references := wrongRole}).toOption.isNone)
    "lowering accepted a pattern entry with the wrong role"
  let wrongContext := r.references.map fun ref =>
    if ref.role == .expression then {ref with context := []} else ref
  require ((FrenAstToHir.Lower.lower {r with references := wrongContext}).toOption.isNone)
    "lowering accepted entries recorded in the wrong lexical context"

/-- Registered as the `typingProperties` job. -/
def runProperties : IO Unit := do
  lowerControls
  runGenerated
  property "well-typed: printed, parsed and resolved, lowering gives back the HIR; both checkers agree" <|
    ∀ c : WellTyped, agrees c.case = true
  property "printable fault: both checkers reject, same code and span" <|
    ∀ c : PrintableFaulty, agrees c.case = true
  let c ← census
  let forms := (formNames.zip c.forms).toList.map fun (n, k) => s!"{n}={k}"
  let faults := (Fault.all.zip c.injected.toList).map fun (f, k) => s!"{repr f}={k}"
  IO.println s!"HIR→THIR census: {c.samples} seeded cases ({c.nodes} nodes); forms: {", ".intercalate forms}; faults injected: {", ".intercalate faults}; fault with no site (typed as well-typed) = {c.notInjected}; checked against the existing checker: {c.accepted} accepted, {c.rejected} rejected; Plausible properties have no premises, discarded = 0"

end FrenHirToThirTests
