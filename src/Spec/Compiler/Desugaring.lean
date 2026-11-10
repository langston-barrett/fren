import Fren.Impl
import Fren.Literate
import Spec.Compiler.Thir
import FrenThirDesugar
import FrenWalking
import FrenEval

open Fren.Lang

#fren_md "Desugaring.md"

namespace Spec.Compiler.Desugaring
open FrenModule FrenAst

/-! ## The desugaring pass

`FrenThirDesugar.desugar` maps the THIR module to the desugared THIR module.
The contract below is stated over the production expression and module types
as relations of their own. They do not mention the production functions
(`step`, `desugarExpr`, `desugarItem`, `desugar`); the theorems then relate
the two. -/

section Pass
open FrenExpr FrenModule.Core

/-- `Erases e d`: `d` is `e` with its parentheses erased and everything else
kept. A parenthesis has whatever its body has, at any depth, so the result of
`((x))` is the result of `x`. Every other node relates to a node of the same
form with the same origin, the same type and the same data, over related
children in the same order. -/
inductive Erases : Expr .thir → Expr .dthir → Prop where
  | paren : Erases e d → Erases ⟨o, ty, .paren g e⟩ d
  | bool : Erases ⟨o, ty, .bool v⟩ ⟨o, ty, .bool v⟩
  | int : Erases ⟨o, ty, .int v⟩ ⟨o, ty, .int v⟩
  | var : Erases ⟨o, ty, .var i⟩ ⟨o, ty, .var i⟩
  | ctor : Erases ⟨o, ty, .ctor g k⟩ ⟨o, ty, .ctor g' k⟩
  | call {args : Array (Expr .thir)} {args' : Array (Expr .dthir)} :
      args'.size = args.size →
      (∀ i (h : i < args.size) (h' : i < args'.size), Erases args[i] args'[i]) →
      Erases ⟨o, ty, .call g callee args⟩ ⟨o, ty, .call g' callee args'⟩
  | unary : Erases e d → Erases ⟨o, ty, .unary op e⟩ ⟨o, ty, .unary op d⟩
  | binary : Erases l l' → Erases r r' →
      Erases ⟨o, ty, .binary op l r⟩ ⟨o, ty, .binary op l' r'⟩
  | ite : Erases c c' → Erases y y' → Erases n n' →
      Erases ⟨o, ty, .ite c y n⟩ ⟨o, ty, .ite c' y' n'⟩
  | letE : Erases v v' → Erases b b' →
      Erases ⟨o, ty, .letE x v b⟩ ⟨o, ty, .letE x v' b'⟩
  | matchE {o : OriginId} {ty : FrenExpr.Ty} {s : Expr .thir} {s' : Expr .dthir}
      {arms : Array (Pattern × Expr .thir)} {arms' : Array (Pattern × Expr .dthir)} :
      Erases s s' → arms'.size = arms.size →
      (∀ i (h : i < arms.size) (h' : i < arms'.size), arms'[i].1 = arms[i].1) →
      (∀ i (h : i < arms.size) (h' : i < arms'.size), Erases arms[i].2 arms'[i].2) →
      Erases ⟨o, ty, .matchE s arms⟩ ⟨o, ty, .matchE s' arms'⟩

/-- The production pass satisfies the specification. -/
theorem desugar_sound : (e : Expr .thir) → Erases e (FrenThirDesugar.desugarExpr e)
  | ⟨o, ty, n⟩ => by
    rw [FrenThirDesugar.desugarExpr_mk]
    cases n with
    | bool v => exact .bool
    | int v => exact .int
    | var i => exact .var
    | item g _ => exact absurd g (by decide)
    | ctor g id => exact .ctor
    | apply g _ _ => exact absurd g (by decide)
    | call g callee args =>
      exact .call (by simp) fun i h h' => by simpa using desugar_sound args[i]
    | unary op e => exact .unary (desugar_sound e)
    | binary op l r => exact .binary (desugar_sound l) (desugar_sound r)
    | ite c y n => exact .ite (desugar_sound c) (desugar_sound y) (desugar_sound n)
    | letE x v b => exact .letE (desugar_sound v) (desugar_sound b)
    | matchE s arms =>
      exact .matchE (desugar_sound s) (by simp) (fun i h h' => by simp)
        fun i h h' => by simpa using desugar_sound arms[i].2
    | paren g e => exact .paren (desugar_sound e)
termination_by e => sizeOf e
decreasing_by
  all_goals apply Expr.sizeOf_child
  all_goals first
    | (simp [ExprF.children]; done)
    | exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem _), rfl⟩)

/-- The specification determines the result: whatever it relates to an input
is the production pass's output. -/
theorem desugar_unique {e : Expr .thir} {d : Expr .dthir} (h : Erases e d) :
    d = FrenThirDesugar.desugarExpr e := by
  induction h with
  | paren _ ih => rw [FrenThirDesugar.desugarExpr_paren]; exact ih
  | bool | int | var | ctor => rw [FrenThirDesugar.desugarExpr_mk]; rfl
  | call hs _ ih =>
    rw [FrenThirDesugar.desugarExpr_mk]
    have : _ = Array.map FrenThirDesugar.desugarExpr _ :=
      Array.ext (by simpa using hs) fun i h1 h2 => by simpa using ih i (by simpa using h2) h1
    rw [this]; rfl
  | unary _ ih => rw [FrenThirDesugar.desugarExpr_mk]; subst ih; rfl
  | binary _ _ ih1 ih2 => rw [FrenThirDesugar.desugarExpr_mk]; subst ih1 ih2; rfl
  | ite _ _ _ ih1 ih2 ih3 => rw [FrenThirDesugar.desugarExpr_mk]; subst ih1 ih2 ih3; rfl
  | letE _ _ ih1 ih2 => rw [FrenThirDesugar.desugarExpr_mk]; subst ih1 ih2; rfl
  | @matchE o ty s s' arms arms' _ hs hp _ ihs ih =>
    rw [FrenThirDesugar.desugarExpr_mk]
    have : arms' = arms.map fun (c, e) => (c, FrenThirDesugar.desugarExpr e) :=
      Array.ext (by simpa using hs) fun i h1 h2 => by
        have h3 : i < arms.size := by simpa using h2
        exact Prod.ext (by simpa using hp i h3 h1) (by simpa using ih i h3 h1)
    subst ihs this; rfl

/-- The relation is exactly the graph of the production pass. -/
theorem erases_iff (e : Expr .thir) (d : Expr .dthir) :
    Erases e d ↔ d = FrenThirDesugar.desugarExpr e :=
  ⟨desugar_unique, fun h => h ▸ desugar_sound e⟩

/-- Nested parentheses: the result carries the origin and type of the
innermost body's result, not of any parenthesis. -/
example (o₁ o₂ o : OriginId) (t₁ t₂ ty : FrenExpr.Ty) (g₁ g₂) (i : Nat) :
    FrenThirDesugar.desugarExpr ⟨o₁, t₁, .paren g₁ ⟨o₂, t₂, .paren g₂ ⟨o, ty, .var i⟩⟩⟩ =
      ⟨o, ty, .var i⟩ :=
  (desugar_unique (.paren (.paren .var))).symm

/-- The output phase admits no parenthesis, so none can remain. -/
theorem output_has_no_paren (n : ExprF .dthir (Expr .dthir)) (g) (e) :
    n ≠ .paren g e :=
  fun _ => FrenThirDesugar.no_surface g

/-- One member: same kind, label and origin, over a related body. -/
def ErasesMember (m : Member (Expr .thir)) (m' : Member (Expr .dthir)) : Prop :=
  m'.kind = m.kind ∧ m'.label = m.label ∧ m'.origin = m.origin ∧ Erases m.body m'.body

/-- One item: an enum is unchanged; a function keeps its identity, origin,
parameters and result type over a related body; a check keeps its identity,
origin and parameters, and its members one for one in order. The origin table
is the same table. An item never changes kind. -/
def ErasesItem : Item (Expr .thir) → Item (Expr .dthir) → Prop
  | .enum e os, .enum e' os' => e' = e ∧ os' = os
  | .function f os, .function f' os' =>
    f'.id = f.id ∧ f'.origin = f.origin ∧ f'.params = f.params ∧ f'.result = f.result ∧
      Erases f.body f'.body ∧ os' = os
  | .check c os, .check c' os' =>
    c'.id = c.id ∧ c'.origin = c.origin ∧ c'.params = c.params ∧
      c'.members.size = c.members.size ∧
      (∀ i (h : i < c.members.size) (h' : i < c'.members.size),
        ErasesMember c.members[i] c'.members[i]) ∧ os' = os
  | _, _ => False

/-- The module: same identity, and items one for one in declaration order. -/
def ErasesModule (m : Thir) (d : FrenThirDesugar.Dthir) : Prop :=
  d.id = m.id ∧ d.items.size = m.items.size ∧
    ∀ i (h : i < m.items.size) (h' : i < d.items.size), ErasesItem m.items[i] d.items[i]

theorem item_sound (i : Item (Expr .thir)) : ErasesItem i (FrenThirDesugar.desugarItem i) := by
  cases i with
  | «enum» e os => exact ⟨rfl, rfl⟩
  | function f os => exact ⟨rfl, rfl, rfl, rfl, desugar_sound _, rfl⟩
  | check c os =>
    refine ⟨rfl, rfl, rfl, by simp, fun i h h' => ?_, rfl⟩
    simp only [Array.getElem_map]
    exact ⟨rfl, rfl, rfl, desugar_sound _⟩

theorem member_unique {m : Member (Expr .thir)} {m' : Member (Expr .dthir)}
    (h : ErasesMember m m') : m' = {m with body := FrenThirDesugar.desugarExpr m.body} := by
  obtain ⟨k, l, o, b⟩ := m
  obtain ⟨k', l', o', b'⟩ := m'
  obtain ⟨hk, hl, ho, hb⟩ := h
  dsimp only at hk hl ho hb
  subst hk hl ho
  rw [desugar_unique hb]

theorem item_unique {i : Item (Expr .thir)} {d : Item (Expr .dthir)} (h : ErasesItem i d) :
    d = FrenThirDesugar.desugarItem i := by
  cases i with
  | «enum» e os =>
    cases d with
    | «enum» e' os' => obtain ⟨rfl, rfl⟩ := h; rfl
    | function _ _ | check _ _ => exact h.elim
  | function f os =>
    cases d with
    | function f' os' =>
      obtain ⟨id, o, ps, res, b⟩ := f
      obtain ⟨id', o', ps', res', b'⟩ := f'
      obtain ⟨h1, h2, h3, h4, hb, rfl⟩ := h
      dsimp only at h1 h2 h3 h4 hb
      subst h1 h2 h3 h4
      rw [desugar_unique hb]; rfl
    | «enum» _ _ | check _ _ => exact h.elim
  | check c os =>
    cases d with
    | check c' os' =>
      obtain ⟨id, o, ps, ms⟩ := c
      obtain ⟨id', o', ps', ms'⟩ := c'
      obtain ⟨h1, h2, h3, hs, hm, rfl⟩ := h
      dsimp only at h1 h2 h3 hs hm
      subst h1 h2 h3
      have : ms' = ms.map fun m => {m with body := FrenThirDesugar.desugarExpr m.body} :=
        Array.ext (by simpa using hs) fun i h1 h2 => by
          have h3 : i < ms.size := by simpa using h2
          simpa using member_unique (hm i h3 h1)
      subst this; rfl
    | «enum» _ _ | function _ _ => exact h.elim

/-- The production pass satisfies the module specification. -/
theorem module_sound (m : Thir) : ErasesModule m (FrenThirDesugar.desugar m) := by
  refine ⟨rfl, by simp [FrenThirDesugar.desugar], fun i h h' => ?_⟩
  simp only [FrenThirDesugar.desugar, Array.getElem_map]
  exact item_sound _

/-- The module specification determines the output module. -/
theorem module_unique {m : Thir} {d : FrenThirDesugar.Dthir} (h : ErasesModule m d) :
    d = FrenThirDesugar.desugar m := by
  obtain ⟨id, items⟩ := d
  obtain ⟨hid, hs, hi⟩ := h
  dsimp only at hid hs hi
  subst hid
  have : items = m.items.map FrenThirDesugar.desugarItem :=
    Array.ext (by simpa using hs) fun i h1 h2 => by
      have h3 : i < m.items.size := by simpa using h2
      simpa using item_unique (hi i h3 h1)
  subst this; rfl

end Pass

/-! ## The legacy walking program

Later passes still take `FrenWalking.Program`. The definitions below state its
admission boundary and the source obligations MIR construction reads. -/

/-- The admitted walking program that later passes consume. -/
abbrev Program := FrenWalking.Program

/-- Graph of the actual resolved entrypoint, including admission. -/
def Produces (input : Resolved) (output : Program) : Prop :=
  FrenWalking.fromResolved input = .ok output

def Rejects (input : Resolved) (failure : FrenHirToThir.StaticFailure) : Prop :=
  FrenHirToThir.checkWalking input = .error failure

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
  body ∈ p.typed.bodies.toList ∧ (op = .div ∨ op = .rem) ∧
    ScopedAt p.input p.typed.signatures body.context body.expression ctx
      (.binary left token op right) guards

/-- Ordered assumption or expectation bodies for an exact canonical block owner. -/
def Members (p : Program) (owner : FrenBase.ItemId) (kind : MemberKind) : Array TypedBody :=
  p.typed.bodies.filter fun b => b.owner == owner && b.member.any (fun m => m.kind == kind)

def Evaluator (p : Program) : FrenEval.Program := ⟨p.input, p.typed, p.accepted⟩

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

/-- Exact success domain, including the original resolved input. -/
theorem resolved_success (r : Resolved) (q : Program) :
    Produces r q ↔ q.input = r ∧ FrenHirToThir.checkWalking r = .ok q.typed := by
  unfold Produces FrenWalking.fromResolved
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
  FrenWalking.deterministic r p q hp hq

theorem resolved_failure (r : Resolved) (d : FrenHirToThir.StaticFailure) :
    FrenWalking.fromResolved r = .error d ↔ Rejects r d := by
  unfold FrenWalking.fromResolved Rejects
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
    (FrenWalking.fromResolved r).map (·.typed) = FrenHirToThir.checkWalking r := by
  unfold FrenWalking.fromResolved
  split <;> simp_all [Except.map]

/-- The source API has exactly the checked source pipeline's typed/error result. -/
theorem source_projection (file : FrenSource.FileId) (source : String) :
    (FrenWalking.fromSource file source).map (·.typed) =
      FrenHirToThir.checkWalkingSource file source := by
  unfold FrenWalking.fromSource FrenHirToThir.checkWalkingSource FrenHirToThir.checkSource
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
    (he : body.expression = .letE l name assign (.binary left op .rem right) inside rest) :
    DomainSite p body body.context [] left op .rem right := by
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
  let .ok p := FrenWalking.fromSource ⟨73⟩ source | return false
  let owner := FrenBase.ItemId.root.named "retained" |>.named "block"
  if p.typed.bodies.size != 4 || p.typed.resolved.document.emit != source then return false
  let assumptions := Members p owner .assume
  let goals := Members p owner .expect
  if assumptions.size != 1 || goals.size != 1 then return false
  if (assumptions[0]?.bind (·.member)).map (·.label.text) != some "later" then return false
  if (goals[0]?.bind (·.member)).map (·.label.text) != some "goal" then return false
  -- Whole-record equality distinguishes dropped bodies, signatures and resolution.
  if p.typed == {p.typed with bodies := #[]} then return false
  if p.typed == {p.typed with signatures := #[]} then return false
  if p.input == {p.input with references := #[]} then return false
  let .ok otherOrigin := FrenWalking.fromSource ⟨74⟩ source | return false
  if p.typed == otherOrigin.typed then return false
  let rejected := #["mod bad\nfn f(x: Int): Int := true",
    "mod bad\nenum E { A, B }\nfn f(x: E): Int := match x { E::A => 1, }",
    "mod bad\nfn f(x: Int): Int := f(x)", "mod bad\nfn f(x: Int): Int := (",
    "mod bad\nfn f(x: Int): Int := x unless true"]
  return rejected.all fun s => !(FrenWalking.fromSource ⟨73⟩ s).isOk

#guard controls

#print axioms desugar_unique
#print axioms module_unique
#print axioms desugar_sound
#print axioms module_sound
#print axioms resolved_success
#print axioms source_projection
#print axioms admission_domain
#print axioms scoped_at_context

end Spec.Compiler.Desugaring
