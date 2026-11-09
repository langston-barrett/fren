import Fren.Impl
import Fren.Literate
import Spec.Compiler.Thir
import FrenThirDesugar
import FrenEval

open Fren.Lang

#fren_md "Desugaring.md"

namespace Spec.Compiler.Desugaring
open FrenModule FrenAst

-- reference begin
/-- Input and output are the same actual evidence-carrying production type. -/
abbrev Program := FrenThirDesugar.Program

/-- The specified core transformation, independent of its implementation. -/
def Desugars (input output : Program) : Prop := output = input

/-- Graph of the actual resolved entrypoint, including admission. -/
def Produces (input : Resolved) (output : Program) : Prop :=
  FrenThirDesugar.fromResolved input = .ok output

def Rejects (input : Resolved) (failure : FrenHirToThir.StaticFailure) : Prop :=
  FrenHirToThir.checkWalking input = .error failure

/-- Entire records, including token tape, origins, ordering and proof boundary. -/
def Retains (input output : Program) : Prop :=
  output.input = input.input ∧ output.typed = input.typed

/-- Conditional scopes retain the lexical context in which their subject is read.
A later let must not reinterpret a guard's local indices in its extended context. -/
inductive Guard where
  | branch (context : TypeContext) (condition : Expr) (selected : Bool)
  | arm (context : TypeContext) (scrutinee : Expr) (pattern : Path)

/-- Every written child, with only explicit branches adding guards. -/
inductive ScopedChild (r : Resolved) (sigs : Array Signature) :
    TypeContext → Expr → TypeContext → Expr → List Guard → Prop where
  | paren : ScopedChild r sigs ctx (.paren o e c) ctx e []
  | unary : ScopedChild r sigs ctx (.unary tok op e) ctx e []
  | binaryLeft : ScopedChild r sigs ctx (.binary a tok op b) ctx a []
  | binaryRight : ScopedChild r sigs ctx (.binary a tok op b) ctx b []
  | callee : ScopedChild r sigs ctx (.call f o args commas c) ctx f []
  | argument : e ∈ args.toList → ScopedChild r sigs ctx (.call f o args commas c) ctx e []
  | condition : ScopedChild r sigs ctx (.ifE i b t yes e no) ctx b []
  | thenBranch : ScopedChild r sigs ctx (.ifE i b t yes e no) ctx yes [.branch ctx b true]
  | elseBranch : ScopedChild r sigs ctx (.ifE i b t yes e no) ctx no [.branch ctx b false]
  | letValue : ScopedChild r sigs ctx (.letE l name assign value i body) ctx value []
  | letBody : FrenHirToThir.HasValue r sigs ctx value vt →
      ScopedChild r sigs ctx (.letE l name assign value i body) ((name, vt) :: ctx) body []
  | scrutinee : ScopedChild r sigs ctx (.matchE m scrutinee o arms c) ctx scrutinee []
  | armBody : arm ∈ arms.toList → ScopedChild r sigs ctx
      (.matchE m scrutinee o arms c) ctx arm.2.2.1 [.arm ctx scrutinee arm.1]

/-- Root-to-site closure, with guards in outer-to-inner order. -/
inductive ScopedAt (r : Resolved) (sigs : Array Signature) :
    TypeContext → Expr → TypeContext → Expr → List Guard → Prop where
  | root : ScopedAt r sigs ctx e ctx e []
  | child : ScopedAt r sigs rootCtx root ctx parent guards →
      ScopedChild r sigs ctx parent childCtx childExpr added →
      ScopedAt r sigs rootCtx root childCtx childExpr (guards ++ added)

/-- An obligation candidate derives from written syntax, never a supplied table.
The body includes owner, full member, type, occurrences and source tokens. -/
def DomainSite (p : Program) (body : TypedBody) (ctx : TypeContext)
    (guards : List Guard) (left : Expr) (token : Token) (op : BinaryOp) (right : Expr) : Prop :=
  body ∈ p.typed.bodies.toList ∧ (op = .div ∨ op = .mod) ∧
    ScopedAt p.input p.typed.signatures body.context body.expression ctx
      (.binary left token op right) guards

/-- Ordered assumption or expectation bodies for an exact canonical block owner. -/
def Members (p : Program) (owner : FrenBase.ItemId) (kind : MemberKind) : Array TypedBody :=
  p.typed.bodies.filter fun b => b.owner == owner && b.member.any (fun m => m.kind == kind)

/-- Transfer shared static judgments in both directions; none is assumed proved. -/
def StaticPreservation (p q : Program) : Prop :=
  (Thir.BodyInventory p.input p.typed ↔ Thir.BodyInventory q.input q.typed) ∧
  (Thir.BodyTyping p.input p.typed ↔ Thir.BodyTyping q.input q.typed) ∧
  (Thir.OccurrenceTyping p.input p.typed ↔ Thir.OccurrenceTyping q.input q.typed) ∧
  (Thir.MatchCoverage p.input p.typed ↔ Thir.MatchCoverage q.input q.typed) ∧
  (Thir.Nonrecursive p.input p.typed ↔ Thir.Nonrecursive q.input q.typed)

def Evaluator (p : Program) : FrenEval.Program := ⟨p.input, p.typed, p.accepted⟩

/-- Equality includes selected body, values and both outer and inner failures. -/
def InterpretationPreservation (p q : Program) : Prop :=
  ∀ request values depth,
    FrenEval.evaluate (Evaluator p) request values depth =
      FrenEval.evaluate (Evaluator q) request values depth

/-- A bijection by exact site identity, rather than equality of a demand trace. -/
def ObligationPreservation (p q : Program) : Prop :=
  (∀ body ctx guards left token op right,
    DomainSite p body ctx guards left token op right ↔
      DomainSite q body ctx guards left token op right) ∧
  (∀ owner kind, Members p owner kind = Members q owner kind)

def PassContract : Prop := ∀ p q, Desugars p q →
  Retains p q ∧ StaticPreservation p q ∧
    InterpretationPreservation p q ∧ ObligationPreservation p q
-- reference end

/-- Every scoped edge has exactly the shared THIR child context. -/
theorem scoped_child_context {r sigs ctx parent childCtx child guards}
    (h : ScopedChild r sigs ctx parent childCtx child guards) :
    Thir.ChildContext r sigs ctx parent childCtx child := by
  cases h with
  | paren => exact .paren
  | unary => exact .unary
  | binaryLeft => exact .binaryLeft
  | binaryRight => exact .binaryRight
  | callee => exact .callee
  | argument h => exact .argument h
  | condition => exact .condition
  | thenBranch => exact .thenBranch
  | elseBranch => exact .elseBranch
  | letValue => exact .letValue
  | letBody h => exact .letBody h
  | scrutinee => exact .scrutinee
  | armBody h => exact .armBody h

theorem scoped_at_context {r sigs rootCtx root ctx expr guards}
    (h : ScopedAt r sigs rootCtx root ctx expr guards) :
    Thir.AtContext r sigs rootCtx root ctx expr := by
  induction h with
  | root => exact .root
  | child _ edge ih => exact .child ih (scoped_child_context edge)

/-- Universal producer law for the actual identity implementation. -/
theorem desugar_iff (p q : Program) : FrenThirDesugar.desugar p = q ↔ Desugars p q := by
  change p = q ↔ q = p
  exact eq_comm

theorem pass_contract : PassContract := by
  intro p q h
  cases h
  exact ⟨⟨rfl, rfl⟩, ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩,
    (by intro request values depth; rfl),
    ⟨(by intros; exact Iff.rfl), (by intros; rfl)⟩⟩

/-- Exact success domain, including the original resolved input. -/
theorem resolved_success (r : Resolved) (q : Program) :
    Produces r q ↔ q.input = r ∧ FrenHirToThir.checkWalking r = .ok q.typed := by
  unfold Produces FrenThirDesugar.fromResolved FrenThirDesugar.desugar
  split
  · rename_i d hd
    constructor
    · intro h; contradiction
    · rintro ⟨_, h⟩; rw [hd] at h; contradiction
  · rename_i typed ht
    constructor
    · intro h
      cases Except.ok.inj h
      exact ⟨rfl, ht⟩
    · rintro ⟨hi, h⟩
      have he := Except.ok.inj (ht.symm.trans h)
      rcases q with ⟨input, out, accepted⟩
      dsimp at hi he
      cases hi
      cases he
      rfl

theorem entry_total (p : Program) : Produces p.input p :=
  (resolved_success p.input p).2 ⟨rfl, p.accepted⟩

theorem produced_unique (r : Resolved) (p q : Program)
    (hp : Produces r p) (hq : Produces r q) : p = q :=
  FrenThirDesugar.deterministic r p q hp hq

theorem resolved_failure (r : Resolved) (d : FrenHirToThir.StaticFailure) :
    FrenThirDesugar.fromResolved r = .error d ↔ Rejects r d := by
  unfold FrenThirDesugar.fromResolved FrenThirDesugar.desugar Rejects
  split <;> simp_all

/-- Success iff type production and both validators succeed, with no extra gate. -/
theorem admission_domain (r : Resolved) (t : Typed) :
    (∃ q, Produces r q ∧ q.typed = t) ↔
      Thir.Produces r t ∧ FrenHirToThir.WalkingCoverage t ∧
        FrenHirToThir.WalkingNonrecursive t := by
  unfold Thir.Produces
  rw [← FrenHirToThir.walking_success]
  constructor
  · rintro ⟨q, h, ht⟩
    have success := ((resolved_success r q).1 h).2
    simpa [ht] using success
  · intro h
    exact ⟨⟨r, t, h⟩, (resolved_success r _).2 ⟨rfl, h⟩, rfl⟩

theorem failure_excludes_success (r : Resolved) (d : FrenHirToThir.StaticFailure)
    (h : Rejects r d) : ∀ q, ¬ Produces r q := by
  intro q success
  have hs := ((resolved_success r q).1 success).2
  change FrenHirToThir.checkWalking r = .error d at h
  rw [h] at hs
  contradiction

theorem resolved_projection (r : Resolved) :
    (FrenThirDesugar.fromResolved r).map (·.typed) = FrenHirToThir.checkWalking r := by
  unfold FrenThirDesugar.fromResolved
  split <;> simp_all [FrenThirDesugar.desugar, Except.map]

/-- The source API has exactly the checked source pipeline's typed/error result. -/
theorem source_projection (file : FrenSource.FileId) (source : String) :
    (FrenThirDesugar.fromSource file source).map (·.typed) =
      FrenHirToThir.checkWalkingSource file source := by
  unfold FrenThirDesugar.fromSource FrenHirToThir.checkWalkingSource FrenHirToThir.checkSource
  cases hp : FrenParse.parseFile file source with
  | error e => rfl
  | ok doc =>
    simp only [Except.mapError, Bind.bind, Except.bind]
    cases hr : FrenAstToHir.resolve doc with
    | error d => rfl
    | ok r =>
      dsimp only
      rw [resolved_projection]
      unfold FrenHirToThir.checkWalking
      cases hc : FrenHirToThir.check r with
      | error d => rfl
      | ok t =>
        cases hv : FrenHirToThir.validateWalking t with
        | error d => rfl
        | ok u =>
          cases u
          rfl

/-- Identity transfers any interpretation or static predicate over the full IR.
This does not assert that a particular declarative interpretation is sound. -/
theorem observation (p q : Program) (h : Desugars p q) {α : Sort _}
    (observe : Resolved → Typed → α) : observe p.input p.typed = observe q.input q.typed := by
  cases h
  rfl

/-- A concrete successful producer retains its exact admission/static evidence. -/
theorem output_static (r : Resolved) (q : Program) (h : Produces r q) :
    q.typed.resolved = r ∧ FrenHirToThir.Admitted r ∧
    Thir.Produces r q.typed ∧ FrenHirToThir.WalkingCoverage q.typed ∧
      FrenHirToThir.WalkingNonrecursive q.typed := by
  have hs := ((resolved_success r q).1 h).2
  have retained := FrenHirToThir.walking_retains r q.typed hs
  exact ⟨retained.1, retained.2, (FrenHirToThir.walking_success r q.typed).1 hs⟩

-- Structural controls cover branches, ordinary operands and unused definitions.
example (r : Resolved) (sigs : Array Signature) (ctx : TypeContext) (a b : Expr) (tok : Token) :
    ScopedChild r sigs ctx (.binary a tok .and b) ctx b [] := .binaryRight

example (r : Resolved) (sigs : Array Signature) (ctx : TypeContext) (a b condition : Expr) (tok : Token) :
    ¬ ScopedChild r sigs ctx (.binary a tok .and b) ctx b [.branch ctx condition true] := by
  intro h
  cases h

example (r : Resolved) (sigs : Array Signature) (ctx : TypeContext)
    (l name assign inside : Token) (value rest : Expr) :
    ScopedChild r sigs ctx (.letE l name assign value inside rest) ctx value [] := .letValue

example (r : Resolved) (sigs : Array Signature) (ctx : TypeContext) (i t e : Token) (b yes no : Expr) :
    ScopedChild r sigs ctx (.ifE i b t yes e no) ctx yes [.branch ctx b true] := .thenBranch

example (r : Resolved) (sigs : Array Signature) (ctx : TypeContext) (m o c : Token) (scrutinee : Expr)
    (arms : Array (Path × Token × Expr × Option Token)) (arm) (h : arm ∈ arms.toList) :
    ScopedChild r sigs ctx (.matchE m scrutinee o arms c) ctx arm.2.2.1
      [.arm ctx scrutinee arm.1] := .armBody h

/-- A branch guard keeps its incoming context across a subsequent let. -/
example (r : Resolved) (sigs : Array Signature) (ctx : TypeContext)
    (i t e l name assign inside : Token) (condition value rest no : Expr)
    (vt : FrenExpr.Ty) (h : FrenHirToThir.HasValue r sigs ctx value vt) :
    ScopedAt r sigs ctx (.ifE i condition t (.letE l name assign value inside rest) e no)
      ((name, vt) :: ctx) rest [.branch ctx condition true] :=
  .child (.child .root .thenBranch) (.letBody h)

-- These sites exist even when the operational interpreter skips their failures.
example (p : Program) (body : TypedBody) (left right : Expr) (b andTok divTok : Token)
    (hb : body ∈ p.typed.bodies.toList)
    (he : body.expression = .binary (.bool b false) andTok .and (.binary left divTok .div right)) :
    DomainSite p body body.context [] left divTok .div right := by
  refine ⟨hb, Or.inl rfl, ?_⟩
  rw [he]
  exact .child .root .binaryRight

example (p : Program) (body : TypedBody) (left right rest : Expr)
    (l name assign inside op : Token) (hb : body ∈ p.typed.bodies.toList)
    (he : body.expression = .letE l name assign (.binary left op .mod right) inside rest) :
    DomainSite p body body.context [] left op .mod right := by
  refine ⟨hb, Or.inr rfl, ?_⟩
  rw [he]
  exact .child .root .letValue

example (p : Program) (body : TypedBody) (condition left right no : Expr)
    (i t e op : Token) (hb : body ∈ p.typed.bodies.toList)
    (he : body.expression = .ifE i condition t (.binary left op .div right) e no) :
    DomainSite p body body.context [.branch body.context condition true] left op .div right := by
  refine ⟨hb, Or.inl rfl, ?_⟩
  rw [he]
  exact .child .root .thenBranch

private def controls : Bool := Id.run do
  let source := "mod retained\nfn f(d: Int): Int := if d != 0 then 1 div d else 0\n" ++
    "fn unused(d: Int): Int := let x := 1 div 0 in d\n" ++
    "expect block(d: Int) { expect goal: f(d) = 0 assume later: d = 0 }\n"
  let .ok p := FrenThirDesugar.fromSource ⟨73⟩ source | return false
  let q := FrenThirDesugar.desugar p
  let owner := FrenBase.ItemId.root.named "retained" |>.named "block"
  if q.typed != p.typed || q.input != p.input then return false
  if q.typed.bodies.size != 4 || q.typed.resolved.document.emit != source then return false
  let assumptions := Members q owner .assume
  let goals := Members q owner .expect
  if assumptions.size != 1 || goals.size != 1 then return false
  if (assumptions[0]?.bind (·.member)).map (·.label.text) != some "later" then return false
  if (goals[0]?.bind (·.member)).map (·.label.text) != some "goal" then return false
  -- Whole-record equality distinguishes dropped bodies, signatures and resolution.
  if q.typed == {p.typed with bodies := #[]} then return false
  if q.typed == {p.typed with signatures := #[]} then return false
  if q.input == {p.input with references := #[]} then return false
  let .ok otherOrigin := FrenThirDesugar.fromSource ⟨74⟩ source | return false
  if q.typed == otherOrigin.typed then return false
  let rejected := #["mod bad\nfn f(x: Int): Int := true",
    "mod bad\nenum E { A, B }\nfn f(x: E): Int := match x { E::A => 1, }",
    "mod bad\nfn f(x: Int): Int := f(x)", "mod bad\nfn f(x: Int): Int := (",
    "mod bad\nfn f(x: Int): Int := x unless true"]
  return rejected.all fun s => !(FrenThirDesugar.fromSource ⟨73⟩ s).isOk

#guard controls

#print axioms pass_contract
#print axioms resolved_success
#print axioms source_projection
#print axioms admission_domain
#print axioms scoped_at_context

end Spec.Compiler.Desugaring
