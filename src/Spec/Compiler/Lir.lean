import Fren.Impl
import Fren.Literate
import Spec.Compiler.Mir
import FrenFlatToLir

open Fren.Lang

#fren_md "Lir.md"

namespace Spec.Compiler.Lir
open FrenModule FrenAst FrenLir

-- reference begin
abbrev Input := FrenWalking.Program

def Produces (p : Input) (out : Program) : Prop := FrenFlatToLir.produce p = .ok out

def Rejects (p : Input) (d : FrenDiag.Diagnostic) : Prop :=
  FrenFlatToLir.produce p = .error d

/-- Ordered correspondence with equal length and retained multiplicity. -/
inductive Pairs {α β : Type} (r : α → β → Prop) : List α → List β → Prop where
  | nil : Pairs r [] []
  | cons : r a b → Pairs r rest more → Pairs r (a :: rest) (b :: more)

/-- Unbounded sorting over the actual vocabulary, independent of checker fuel. -/
inductive Sorted (s : Typed) : TypeContext → Term → FrenExpr.Ty → Prop where
  | bool : Sorted s ctx (.bool b) .bool
  | int : Sorted s ctx (.int n) .int
  | constructor : FrenEval.Value.valid s (.enum owner ctor) = true →
      Sorted s ctx (.constructor owner ctor) (.enum owner)
  | local : ctx[i]?.map Prod.snd = some ty →
      Sorted s ctx (.local ty i component) (if component == .domain then .bool else ty)
  | unary : Sorted s ctx a ta → FrenExpr.unary op ta = some ty → Sorted s ctx (.unary op a) ty
  | binary : Sorted s ctx a ta → Sorted s ctx b tb → FrenExpr.binary op ta tb = some ty →
      Sorted s ctx (.binary op a b) ty
  | ite : Sorted s ctx c .bool → Sorted s ctx a ty → Sorted s ctx b ty → Sorted s ctx (.ite c a b) ty
  | app : sig ∈ s.signatures.toList →
      args.length = sig.parameters.size →
      (∀ (i : Nat) (a : Term) (param : TypedParameter), args[i]? = some a → sig.parameters[i]? = some param → Sorted s ctx a param.type) →
      Sorted s ctx (.app sig component args) (if component == .domain then .bool else sig.result)
  | letE : Sorted s ctx v ty → Sorted s ctx d .bool → Sorted s ((binder, ty) :: ctx) body result →
      Sorted s ctx (.letE binder ty v d body) result
  | at : origin.context = ctx → Sorted s ctx a ty → Sorted s ctx (.at origin a) ty

/-- Positional call values, but nearest-first lexical value/domain pairs. -/
abbrev Slots := List (FrenEval.Value × Bool)
abbrev Symbols := Signature → Component → List FrenEval.Value → FrenEval.Value
abbrev ZeroValues := BinaryOp → Int → Int

def Assigned (s : Typed) (ctx : TypeContext) (env : Slots) : Prop :=
  env.length = ctx.length ∧ ∀ (i : Nat) (token : Token) (ty : FrenExpr.Ty), ctx[i]? = some (token, ty) →
    ∃ (v : FrenEval.Value) (d : Bool), env[i]? = some (v, d) ∧ v.type = ty ∧ v.valid s = true

/-- Only zero-divisor values are arbitrary; verification must still reject them. -/
inductive Primitive (zero : ZeroValues) : BinaryOp → FrenEval.Value → FrenEval.Value → FrenEval.Value → Prop where
  | ordinary : FrenEval.binary op a b = .ok v → Primitive zero op a b v
  | divZero : Primitive zero .div (.int n) (.int 0) (.int (zero .div n))
  | remZero : Primitive zero .rem (.int n) (.int 0) (.int (zero .rem n))

/-- Interpretation, not a compiler or a bounded execution. Tags and contexts
are checked by Sorted/Assigned; origins do not change a term's value. -/
inductive Meaning (symbols : Symbols) (zero : ZeroValues) : Slots → Term → FrenEval.Value → Prop where
  | bool : Meaning symbols zero env (.bool b) (.bool b)
  | int : Meaning symbols zero env (.int n) (.int n)
  | constructor : Meaning symbols zero env (.constructor owner ctor) (.enum owner ctor)
  | local : env[i]? = some (v, d) → Meaning symbols zero env (.local ty i component)
      (if component == .domain then .bool d else v)
  | unary : Meaning symbols zero env a av → FrenEval.unary op av = .ok v →
      Meaning symbols zero env (.unary op a) v
  | binary : Meaning symbols zero env a av → Meaning symbols zero env b bv → Primitive zero op av bv v →
      Meaning symbols zero env (.binary op a b) v
  | iteTrue : Meaning symbols zero env c (.bool true) → Meaning symbols zero env a v →
      Meaning symbols zero env (.ite c a b) v
  | iteFalse : Meaning symbols zero env c (.bool false) → Meaning symbols zero env b v →
      Meaning symbols zero env (.ite c a b) v
  | app : args.length = values.length →
      (∀ (i : Nat) a v, args[i]? = some a → values[i]? = some v → Meaning symbols zero env a v) →
      Meaning symbols zero env (.app sig component args) (symbols sig component values)
  | letE : Meaning symbols zero env value v → Meaning symbols zero env domain (.bool d) →
      Meaning symbols zero ((v, d) :: env) body result →
      Meaning symbols zero env (.letE binder ty value domain body) result
  | at : Meaning symbols zero env a v → Meaning symbols zero env (.at origin a) v

/-- Verification is conjunctive for ordinary children and scoped for explicit
branches/binders. A false predicate is not an interpretation failure. -/
inductive Holds (symbols : Symbols) (zero : ZeroValues) : Slots → Verification → Prop where
  | empty : Holds symbols zero env .empty
  | check : Meaning symbols zero env condition (.bool true) → Holds symbols zero env (.check condition)
  | both : Holds symbols zero env a → Holds symbols zero env b → Holds symbols zero env (.both a b)
  | yes : Meaning symbols zero env c (.bool true) → Holds symbols zero env a →
      Holds symbols zero env (.branch c a b)
  | no : Meaning symbols zero env c (.bool false) → Holds symbols zero env b →
      Holds symbols zero env (.branch c a b)
  | letE : Meaning symbols zero env value v → Meaning symbols zero env domain (.bool d) →
      Holds symbols zero ((v, d) :: env) body →
      Holds symbols zero env (.letE binder ty value domain body)
  | at : Holds symbols zero env body → Holds symbols zero env (.at origin body)

/-- A guard records its incoming context, even beneath a later let. -/
inductive Frame where
  | guard (context : TypeContext) (condition : Term) (selected : Bool)
  | binder (context : TypeContext) (name : Token) (sort : FrenExpr.Ty) (value domain : Term)

/-- Static leaf address: child indices preserve multiplicity and left-to-right
order, even at equal formulas. Both branches are present, without evaluation. -/
inductive Site : TypeContext → Option Origin → Verification → List Nat → List Frame →
    TypeContext → Option Origin → Term → Prop where
  | check : Site ctx origin (.check c) [] [] ctx origin c
  | left : Site ctx origin a path frames leafCtx leafOrigin c →
      Site ctx origin (.both a b) (0 :: path) frames leafCtx leafOrigin c
  | right : Site ctx origin b path frames leafCtx leafOrigin c →
      Site ctx origin (.both a b) (1 :: path) frames leafCtx leafOrigin c
  | yes : Site ctx origin a path frames leafCtx leafOrigin c →
      Site ctx origin (.branch testTerm a b) (0 :: path) (.guard ctx testTerm true :: frames) leafCtx leafOrigin c
  | no : Site ctx origin b path frames leafCtx leafOrigin c →
      Site ctx origin (.branch testTerm a b) (1 :: path) (.guard ctx testTerm false :: frames) leafCtx leafOrigin c
  | letE : Site ((name, ty) :: ctx) origin body path frames leafCtx leafOrigin c →
      Site ctx origin (.letE name ty v d body) (0 :: path) (.binder ctx name ty v d :: frames)
        leafCtx leafOrigin c
  | at : Site ctx (some o) body path frames leafCtx leafOrigin c →
      Site ctx origin (.at o body) (0 :: path) frames leafCtx leafOrigin c

/-- Nonempty ordered match chain. The last written arm is the fallback;
source coverage and uniqueness, independently of typing, justify that choice. -/
inductive MatchChain : List (Term × Lowered) → Lowered → Prop where
  | last : MatchChain [(testTerm, arm)] arm
  | cons : MatchChain (next :: rest) tail →
      MatchChain ((testTerm, arm) :: next :: rest) (Lowered.branch ⟨testTerm, .empty⟩ arm tail)

def Mark (b : TypedBody) (ctx : TypeContext) (e : Expr) (v : Lowered) : Lowered :=
  v.mark ⟨b.owner, b.member, e, ctx⟩

/-- Syntax-directed relation over shared source objects and actual LIR.
No fuel, executable duplicate pass, type-only coverage premise or supplied
obligation list determines this relation. -/
inductive Lowers (s : Typed) (b : TypedBody) : TypeContext → Expr → Lowered → Prop where
  | bool : Lowers s b ctx (.bool tok x) (Mark b ctx (.bool tok x) ⟨.bool x, .empty⟩)
  | int : Lowers s b ctx (.integer tok x) (Mark b ctx (.integer tok x) ⟨.int x, .empty⟩)
  | local : FrenHirToThir.Selects s.resolved ctx path .expression (.local i) →
      ctx[i]?.map Prod.snd = some ty → Lowers s b ctx (.name path)
        (Mark b ctx (.name path) ⟨.local ty i .value, .check (.local ty i .domain)⟩)
  | constructor : FrenHirToThir.Selects s.resolved ctx path .expression (.item ctor) →
      FrenHirToThir.constructorType s.resolved ctor = some (.enum owner) →
      Lowers s b ctx (.name path) (Mark b ctx (.name path) ⟨.constructor owner ctor, .empty⟩)
  | paren : Lowers s b ctx e v → Lowers s b ctx (.paren o e c) (Mark b ctx (.paren o e c) v)
  | unary : Lowers s b ctx e v → Lowers s b ctx (.unary tok op e)
      (Mark b ctx (.unary tok op e) ⟨.unary op v.value, v.verification⟩)
  | binary : Lowers s b ctx a av → Lowers s b ctx c cv → Lowers s b ctx (.binary a tok op c)
      (Mark b ctx (.binary a tok op c) (Lowered.binary op av cv))
  | branch : Lowers s b ctx c cv → Lowers s b ctx a av → Lowers s b ctx n nv →
      Lowers s b ctx (.ifE i c t a e n) (Mark b ctx (.ifE i c t a e n) (Lowered.branch cv av nv))
  | letE : FrenHirToThir.HasValue s.resolved s.signatures ctx v ty →
      Lowers s b ctx v lowered → Lowers s b ((name, ty) :: ctx) body rest →
      Lowers s b ctx (.letE l name assign v inside body)
        (Mark b ctx (.letE l name assign v inside body) (Lowered.bind name ty lowered rest))
  | call : Thir.HasCallable s.resolved s.signatures ctx callee sig →
      args.size = values.length →
      (∀ (i : Nat) a v, args[i]? = some a → values[i]? = some v → Lowers s b ctx a v) →
      Lowers s b ctx (.call callee o args commas c)
        (Mark b ctx (.call callee o args commas c) (Lowered.call sig values))
  | matchE {ctorAt : Nat → FrenBase.ItemId} : Lowers s b ctx scrutinee v →
      FrenHirToThir.HasValue s.resolved s.signatures ctx scrutinee (.enum owner) →
      arms.size = branches.length →
      (∀ (i : Nat) arm pair, arms[i]? = some arm → branches[i]? = some pair →
        FrenHirToThir.Selects s.resolved ctx arm.1 .pattern (.item (ctorAt i)) ∧
        FrenHirToThir.constructorType s.resolved (ctorAt i) = some (.enum owner) ∧
        pair.1 = Term.binary .eq v.value (.constructor owner (ctorAt i))) →
      (∀ (i : Nat) arm pair, arms[i]? = some arm → branches[i]? = some pair →
        Lowers s b ctx arm.2.2.1 pair.2) →
      MatchChain branches selected →
      Lowers s b ctx (.matchE m scrutinee o arms c)
        (Mark b ctx (.matchE m scrutinee o arms c)
          ⟨selected.value, .both v.verification selected.verification⟩)

def BodyFor (s : Typed) (source : TypedBody) (out : Body) : Prop :=
  out.source = source ∧ Lowers s source source.context source.expression out.term ∧
    Sorted s source.context out.term.value source.type ∧ Sorted s source.context out.term.defined .bool

inductive DeclarationFor (s : Typed) : FrenMir.Declaration → Declaration → Prop where
  | enumeration : DeclarationFor s (.enumeration e) (.enumeration e)
  | function : BodyFor s f.definition b → DeclarationFor s (.function f) (.function f.signature b)
  | block : Pairs (BodyFor s) b.members.toList members.toList →
      DeclarationFor s (.block b) (.block b members)

inductive QuestionFor (s : Typed) : FrenMir.Question → Question → Prop where
  | sat : QuestionFor s .assumptionsSatisfiable .assumptionsSatisfiable
  | validity : BodyFor s g b → QuestionFor s (.validity g) (.validity b)

def RequestFor (s : Typed) (r : FrenMir.CheckRequest) (out : CheckRequest) : Prop :=
  out.source = r ∧ Pairs (BodyFor s) r.assumptions.toList out.assumptions.toList ∧
    QuestionFor s r.question out.question ∧
    Pairs (fun d b => BodyFor s d.root b) r.demand.toList out.demand.toList

def Constructs (p : Input) (out : Program) : Prop :=
  Mir.Constructs p out.mir ∧
    Pairs (DeclarationFor out.mir.source) out.mir.declarations.toList out.declarations.toList ∧
    Pairs (RequestFor out.mir.source) out.mir.requests.toList out.requests.toList

/-- The independent source judgment is strict at ordinary operands and lets,
and selects only explicit if/match branches. It is not raw lazy evaluation. -/
def SourceValue (p : Input) (b : TypedBody) (values : List FrenEval.Value) (v : FrenEval.Value) : Prop :=
  Mir.ValueOf p.typed (Mir.SourceDefinition p.typed) b.context b.expression values v

/-- Symbols are definitions, not freely assumed axioms. Only actual source
signature/body pairs and typed positional arguments are constrained. -/
def Models (p : Input) (symbols : Symbols) : Prop :=
  ∀ sig b, Mir.SourceDefinition p.typed sig b → ∀ args : List FrenEval.Value,
    Mir.Assignment p.typed b.context args.reverse →
    (symbols sig .domain args = .bool true ↔ ∃ v, SourceValue p b args.reverse v) ∧
    (symbols sig .domain args = .bool true ∨ symbols sig .domain args = .bool false) ∧
    (∀ v, SourceValue p b args.reverse v → symbols sig .value args = v)

/-- Root-restricted, two-way semantic correspondence on independently typed
assignments. No fabricated-expression functionality premise is assumed. -/
def BodyMeaning (p : Input) (b : Body) (symbols : Symbols) (zero : ZeroValues) : Prop :=
  ∀ values : List FrenEval.Value, Mir.Assignment p.typed b.source.context values →
    let env := values.map (fun v => (v, true))
    (Holds symbols zero env b.term.verification ↔ ∃ v, SourceValue p b.source values v) ∧
    (Holds symbols zero env b.term.verification → ∀ v,
      Meaning symbols zero env b.term.value v ↔ SourceValue p b.source values v)

def Root (out : Program) (b : Body) : Prop :=
  (∃ sig, Declaration.function sig b ∈ out.declarations.toList) ∨
    (∃ source members, Declaration.block source members ∈ out.declarations.toList ∧ b ∈ members.toList) ∨
    ∃ r ∈ out.requests.toList, b ∈ r.assumptions.toList ∨ b ∈ r.demand.toList ∨ r.question = .validity b

def AllTrue (symbols : Symbols) (zero : ZeroValues) (env : Slots) (bodies : Array Body) : Prop :=
  ∀ b ∈ bodies.toList, Meaning symbols zero env b.term.value (.bool true)

/-- Independent safety precedes question interpretation. No assumption proves
its own safety; all unused definition bodies are included. -/
def VerificationDomain (out : Program) (symbols : Symbols) (zero : ZeroValues) (r : CheckRequest) : Prop :=
  (∀ sig b, Declaration.function sig b ∈ out.declarations.toList → ∀ values,
    Mir.Assignment out.mir.source b.source.context values →
    Holds symbols zero (values.map (fun v => (v, true))) b.term.verification) ∧
  (∀ values, Mir.Assignment out.mir.source r.source.context values →
    ∀ b ∈ r.assumptions.toList, Holds symbols zero (values.map (fun v => (v, true))) b.term.verification) ∧
  (∀ values, Mir.Assignment out.mir.source r.source.context values →
    AllTrue symbols zero (values.map (fun v => (v, true))) r.assumptions →
    ∀ b ∈ r.demand.toList, Holds symbols zero (values.map (fun v => (v, true))) b.term.verification)

def QuestionMeaning (out : Program) (symbols : Symbols) (zero : ZeroValues) (r : CheckRequest) : Prop :=
  match r.question with
  | .assumptionsSatisfiable => ∃ values, Mir.Assignment out.mir.source r.source.context values ∧
      AllTrue symbols zero (values.map (fun v => (v, true))) r.assumptions
  | .validity goal => ∀ values, Mir.Assignment out.mir.source r.source.context values →
      AllTrue symbols zero (values.map (fun v => (v, true))) r.assumptions →
      Meaning symbols zero (values.map (fun v => (v, true))) goal.term.value (.bool true)

/-- Named obligations, not axioms or claims of universal producer soundness. -/
def PassContract : Prop := ∀ p out, Produces p out → Constructs p out

def InterpretationContract : Prop := ∀ p out, Produces p out → Constructs p out →
  Mir.AdmissionResidue p → ∀ symbols, Models p symbols → ∀ zero b, Root out b → BodyMeaning p b symbols zero

def RequestContract : Prop := ∀ p out, Produces p out → Constructs p out → Mir.AdmissionResidue p →
  ∀ symbols, Models p symbols → ∀ zero r, r ∈ out.requests.toList →
  Mir.VerificationDomain p.typed (Mir.SourceDefinition p.typed) r.source →
    VerificationDomain out symbols zero r ∧
    (QuestionMeaning out symbols zero r ↔ Mir.QuestionMeaning p.typed (Mir.SourceDefinition p.typed) r.source)
-- reference end

/-- Success retains the whole actual MIR and source, including typed occurrences. -/
theorem produced_boundary (p : Input) (out : Program) (h : Produces p out) :
    Mir.Produces p out.mir ∧ out.mir.source = p.typed ∧ out.wellFormed = true :=
  ⟨FrenFlatToLir.retains_mir p out h, FrenFlatToLir.retains_source p out h,
    FrenFlatToLir.wellFormed p out h⟩

theorem produced_unique (p : Input) (a b : Program) (ha : Produces p a) (hb : Produces p b) : a = b :=
  FrenFlatToLir.deterministic p a b ha hb

theorem failure_excludes_success (p : Input) (d : FrenDiag.Diagnostic) (h : Rejects p d) :
    ∀ out, ¬ Produces p out := by
  intro out success
  unfold Produces at success
  unfold Rejects at h
  rw [h] at success
  contradiction

theorem entry_success (file : FrenSource.FileId) (source : String) (out : Program) :
    FrenFlatToLir.fromSource file source = .ok out ↔
      ∃ p, FrenWalking.fromSource file source = .ok p ∧ Produces p out := by
  unfold FrenFlatToLir.fromSource
  cases hp : FrenWalking.fromSource file source with
  | error d => simp [Bind.bind, Except.bind]
  | ok p =>
    simp only [Bind.bind, Except.bind, Except.mapError, Produces]
    cases hc : FrenFlatToLir.produce p <;> simp [hc]

theorem entry_failure (file : FrenSource.FileId) (source : String) (d : FrenHirToThir.StaticFailure)
    (h : FrenWalking.fromSource file source = .error d) :
    FrenFlatToLir.fromSource file source = .error d := FrenFlatToLir.rejected file source d h

theorem ordinary_checks (op : BinaryOp) (a b : Lowered) (hd : op ≠ .div) (hm : op ≠ .rem) :
    (Lowered.binary op a b).verification = .both a.verification b.verification :=
  FrenLir.binary_verification op a b hd hm

theorem division_checks (a b : Lowered) :
    (Lowered.binary .div a b).verification =
      .both (.both a.verification b.verification) (.check (.binary .ne b.value (.int 0))) := rfl

theorem remainder_checks (a b : Lowered) :
    (Lowered.binary .rem a b).verification =
      .both (.both a.verification b.verification) (.check (.binary .ne b.value (.int 0))) := rfl

theorem branch_checks (c a b : Lowered) :
    (Lowered.branch c a b).verification = .both c.verification (.branch c.value a.verification b.verification) := rfl

theorem let_checks (name : Token) (ty : FrenExpr.Ty) (v body : Lowered) :
    (Lowered.bind name ty v body).verification =
      .both v.verification (.letE name ty v.value v.defined body.verification) := rfl

theorem call_checks (sig : Signature) (args : List Lowered) :
    (Lowered.call sig args).verification =
      .both (args.foldr (fun a rest => .both a.verification rest) .empty)
        (.check (.app sig .domain (args.map (·.value)))) := rfl

theorem summary_sound (h : Holds symbols zero env verification) :
    Meaning symbols zero env verification.formula (.bool true) := by
  induction h with
  | empty => exact .bool
  | check value => exact value
  | both _ _ ha hb => exact .binary ha hb (.ordinary rfl)
  | yes condition _ ih => exact .iteTrue condition ih
  | no condition _ ih => exact .iteFalse condition ih
  | letE value domain _ ih => exact .letE value domain ih
  | «at» _ ih => exact .at ih

theorem or_right_site (a b : Lowered)
    (site : Site ctx origin b.verification path frames leafCtx leafOrigin c) :
    Site ctx origin (Lowered.binary .or a b).verification (1 :: path) frames leafCtx leafOrigin c :=
  .right site

/-- An unused let's value site stays in the incoming context without a binder. -/
theorem let_value_site (name : Token) (ty : FrenExpr.Ty) (v body : Lowered)
    (site : Site ctx origin v.verification path frames leafCtx leafOrigin c) :
    Site ctx origin (Lowered.bind name ty v body).verification (0 :: path) frames leafCtx leafOrigin c :=
  .left site

/-- The ordinary Boolean right operand has no guard derived from the left value. -/
theorem and_right_site (a b : Lowered)
    (site : Site ctx origin b.verification path frames leafCtx leafOrigin c) :
    Site ctx origin (Lowered.binary .and a b).verification (1 :: path) frames leafCtx leafOrigin c :=
  .right site

theorem guarded_site (condition : Term)
    (site : Site ctx origin yes path frames leafCtx leafOrigin c) :
    Site ctx origin (.branch condition yes no) (0 :: path)
      (.guard ctx condition true :: frames) leafCtx leafOrigin c := .yes site

/-- Semantic conjunction is an actual constructor law, not a Boolean sample. -/
theorem holds_both : Holds symbols zero env (.both a b) ↔
    Holds symbols zero env a ∧ Holds symbols zero env b := by
  constructor
  · intro h; cases h with | both ha hb => exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩; exact .both ha hb

theorem holds_check_bool (value : Bool) :
    Holds symbols zero env (.check (.bool value)) ↔ value = true := by
  constructor
  · intro h
    cases h with | check value => cases value; rfl
  · intro h
    cases h
    exact .check .bool

/-- Boolean predicate leaves specialize the actual ordinary constructor,
independently of the Boolean values of its two operands. -/
theorem ordinary_bool_contract (a b leftValue rightValue : Bool) :
    Holds symbols zero env (Lowered.binary .and
      ⟨.bool leftValue, .check (.bool a)⟩ ⟨.bool rightValue, .check (.bool b)⟩).verification ↔
      a = true ∧ b = true := by
  change Holds symbols zero env (.both (.check (.bool a)) (.check (.bool b))) ↔ _
  rw [holds_both, holds_check_bool, holds_check_bool]

/-- A totalized value at zero cannot make the retained nonzero check true. -/
theorem zero_check_fails : ¬ Holds symbols zero env (.check (.binary .ne (.int 0) (.int 0))) := by
  intro h
  cases h with
  | check value =>
    cases value with
    | binary left right primitive =>
      cases left
      cases right
      cases primitive with
      | ordinary eq =>
        change Except.ok (FrenEval.Value.bool false) = .ok (.bool true) at eq
        contradiction

/-- A complete admitted-root contract witness can be supplied without assuming
any universal soundness or functionality result. -/
theorem literal_meaning (p : Input) (b : TypedBody) (token : Token) (x : Bool)
    (shape : b.expression = .bool token x) :
    BodyMeaning p ⟨b, Mark b b.context b.expression ⟨.bool x, .empty⟩⟩ symbols zero := by
  intro values assigned
  dsimp only
  constructor
  · constructor
    · intro _
      refine ⟨.bool x, ?_⟩
      unfold SourceValue
      rw [shape]
      exact .bool
    · intro _
      exact .at .empty
  · intro _ v
    constructor
    · intro value
      cases value with
      | «at» value =>
        cases value
        unfold SourceValue
        rw [shape]
        exact .bool
    · intro value
      unfold SourceValue at value
      rw [shape] at value
      cases value
      exact .at .bool

theorem literal_body_for (s : Typed) (b : TypedBody) (token : Token) (x : Bool)
    (shape : b.expression = .bool token x) (resultType : b.type = .bool) :
    BodyFor s b ⟨b, Mark b b.context b.expression ⟨.bool x, .empty⟩⟩ := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [shape]
    exact .bool
  · rw [resultType]
    exact .at rfl .bool
  · exact .at rfl .bool

/-- A constructive symbol interpretation for a nonempty class of definitions.
This proves a sufficient model condition rather than assuming its existence. -/
theorem true_definition_model (p : Input)
    (shape : ∀ sig b, Mir.SourceDefinition p.typed sig b → ∃ token, b.expression = .bool token true) :
    Models p (fun _ _ _ => .bool true) := by
  intro sig b present args _
  obtain ⟨token, h⟩ := shape sig b present
  have existsValue : SourceValue p b args.reverse (.bool true) := by
    unfold SourceValue
    rw [h]
    exact .bool
  refine ⟨⟨(fun _ => ⟨.bool true, existsValue⟩), (fun _ => rfl)⟩, Or.inl rfl, ?_⟩
  intro v value
  unfold SourceValue at value
  rw [h] at value
  cases value
  rfl

/-- Lexical extension never changes the context stored with an outer guard. -/
example (name : Token) (ty : FrenExpr.Ty) (value domain condition c : Term) :
    Site ctx origin (.branch condition (.letE name ty value domain (.check c)) .empty)
      [0, 0] [.guard ctx condition true, .binder ctx name ty value domain]
      ((name, ty) :: ctx) origin c := .yes (.letE .check)

theorem false_check : ¬ Holds symbols zero env (.check (.bool false)) := by
  intro h
  cases h with | check value => cases value

theorem unused_false_rejected (name : Token) (ty : FrenExpr.Ty) (body : Lowered) :
    ¬ Holds symbols zero env (Lowered.bind name ty ⟨.int 0, .check (.bool false)⟩ body).verification := by
  intro h
  exact false_check (holds_both.mp h).1

-- Concrete positive and negative interpretation controls over actual constructors.
example : Holds symbols zero env (Lowered.branch ⟨.bool false, .empty⟩
    ⟨.int 1, .check (.bool false)⟩ ⟨.int 0, .empty⟩).verification :=
  .both .empty (.no .bool .empty)

example : ¬ Holds symbols zero env (.both .empty (.check (.bool false))) := by
  intro h
  cases h with
  | both _ right => cases right with | check value => cases value

-- This runs the real admission and producer, then checks the exact source and
-- lowered shapes to which the universal literal/model witnesses above apply.
#eval show IO Unit from do
  let source := "mod lir_contracts\nfn fixed(x: Int): Bool := true\n" ++
    "expect c(x: Int) { expect false_goal: false assume later: true }\nexpect empty() {}\n"
  let .ok p := FrenWalking.fromSource ⟨211⟩ source
    | throw (IO.userError "LIR witness admission failed")
  let .ok out := FrenFlatToLir.produce p | throw (IO.userError "LIR witness lowering failed")
  unless out.wellFormed && out.mir.source == p.typed && out.requests.size == 3 do
    throw (IO.userError "LIR witness boundary differs")
  for declaration in out.declarations do
    let bodies := match declaration with
      | .enumeration _ => #[]
      | .function _ b => #[b]
      | .block _ bs => bs
    for b in bodies do
      match shape : b.source.expression with
      | .bool token x =>
        let expected : Body := ⟨b.source, Mark b.source b.source.context b.source.expression ⟨.bool x, .empty⟩⟩
        have _contract : BodyMeaning p expected (fun _ _ _ => .bool true) (fun _ _ => 0) :=
          literal_meaning p b.source token x shape
        unless b == expected && b.source.type == .bool do
          throw (IO.userError "LIR output fails the proved literal contract shape")
      | _ => throw (IO.userError "literal contract witness changed")
  unless p.typed.signatures.size == 1 && (p.typed.bodies.filter (·.member.isNone)).all (fun b =>
      match b.expression with | .bool _ true => true | _ => false) do
    throw (IO.userError "constructive true-definition model premise differs")
  let some validity := out.requests[1]? | throw (IO.userError "validity request absent")
  let .validity goal := validity.question | throw (IO.userError "goal polarity lost")
  unless (match goal.source.expression with | .bool _ false => true | _ => false) &&
      validity.assumptions.size == 1 && validity.demand.size == 2 &&
      validity.source.context.map (·.1.text) == ["x"] do
    throw (IO.userError "false goal or later assumption lost")
  for changed in #[{out with requests := out.requests.reverse},
      {out with requests := out.requests.modify 1 (fun r => {r with assumptions := #[]})},
      {out with declarations := out.declarations.extract 1 out.declarations.size}] do
    if changed.wellFormed then throw (IO.userError "LIR retention mutation admitted")
  for text in ["mod bad\nfn f(x: Int): Int := f(x)",
      "mod bad\nenum E { A }\nfn f(e: E): Bool := match e { E::A => true, E::A => false }"] do
    let .error rejected := FrenWalking.fromSource ⟨211⟩ text
      | throw (IO.userError "unsupported witness admitted")
    let .error actual := FrenFlatToLir.fromSource ⟨211⟩ text
      | throw (IO.userError "rejected witness lowered")
    unless reprStr actual == reprStr rejected do throw (IO.userError "admission failure changed")
  IO.println "LIR contract witness: 1 constant definition, false goal and later assumption, 3 ordered requests; literal BodyFor/BodyMeaning and constructive Models sufficient shapes; 3 retention mutants and duplicate-arm/recursive negatives rejected"

#print axioms produced_boundary
#print axioms entry_success
#print axioms ordinary_checks
#print axioms let_value_site
#print axioms and_right_site
#print axioms holds_both
#print axioms summary_sound
#print axioms literal_meaning
#print axioms literal_body_for
#print axioms true_definition_model
#print axioms unused_false_rejected
#print axioms zero_check_fails

end Spec.Compiler.Lir
