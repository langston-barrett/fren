import Fren.Impl
import Fren.Literate
import Spec.Compiler.Desugaring
import FrenThirToMir

open Fren.Lang

#fren_md "Mir.md"

namespace Spec.Compiler.Mir
open FrenModule FrenAst FrenMir

-- reference begin
abbrev Program := FrenWalking.Program

def Produces (p : Program) (t : Theory) : Prop := FrenThirToMir.produce p = .ok t

def Rejects (p : Program) (d : FrenDiag.Diagnostic) : Prop :=
  FrenThirToMir.produce p = .error d

/-- A definition is the complete signature/body pair, never an assumed goal. -/
def SourceDefinition (s : Typed) (sig : Signature) (body : TypedBody) : Prop :=
  sig ∈ s.signatures.toList ∧ body ∈ s.bodies.toList ∧
    body.owner = sig.id ∧ body.member = none

def TheoryDefinition (t : Theory) (sig : Signature) (body : TypedBody) : Prop :=
  Declaration.function ⟨sig, body⟩ ∈ t.declarations.toList

/-- Complete members, including source identities and duplicate-valued occurrences. -/
inductive MemberOrder (owner : FrenBase.ItemId) (ctx : TypeContext) :
    List Member → List TypedBody → Prop where
  | nil : MemberOrder owner ctx [] []
  | cons : Thir.BodyEntry body owner (some member) member.body ctx .bool →
      MemberOrder owner ctx members bodies →
      MemberOrder owner ctx (member :: members) (body :: bodies)

/-- Relation on the actual written declaration and actual MIR declaration. -/
inductive DeclarationFor (p : Program) : Decl → Declaration → Prop where
  | enumeration :
      DeclarationFor p (.enumDecl vis kw name o variants commas c)
        (.enumeration ⟨p.input.scope.id.named name.text,
          .enumDecl vis kw name o variants commas c,
          variants.map (fun v => ((p.input.scope.id.named name.text).named v.text, v))⟩)
  | function : SourceDefinition p.typed sig body → sig.id = p.input.scope.id.named name.text →
      FrenHirToThir.parameters p.input params = .ok sig.parameters →
      FrenHirToThir.annotation p.input result = .ok sig.result → sig.resultAnnotation = result →
      body.expression = expr → body.context = FrenHirToThir.parameterContext sig.parameters →
      body.type = sig.result →
      DeclarationFor p (.function vis kw name params colon result assign expr) (.function ⟨sig, body⟩)
  | block : FrenHirToThir.parameters p.input params = .ok typedParams →
      MemberOrder (p.input.scope.id.named name.text) (FrenHirToThir.parameterContext typedParams)
        members.toList
        (p.typed.bodies.filter (fun body => body.owner == p.input.scope.id.named name.text)).toList →
      DeclarationFor p (.expectation kw name params o members c)
        (.block ⟨p.input.scope.id.named name.text, .expectation kw name params o members c,
          typedParams, FrenHirToThir.parameterContext typedParams,
          p.typed.bodies.filter (fun body => body.owner == p.input.scope.id.named name.text)⟩)

/-- Every source declaration contributes once in order, except module headers. -/
inductive DeclarationOrder (p : Program) : List Decl → List Declaration → Prop where
  | nil : DeclarationOrder p [] []
  | moduleDecl : DeclarationOrder p ds out →
      DeclarationOrder p (.moduleDecl vis kw path :: ds) out
  | cons : DeclarationFor p d out → DeclarationOrder p ds rest →
      DeclarationOrder p (d :: ds) (out :: rest)

/-- Exact root membership includes unused functions and every owned member. -/
def TheoryRoot (t : Theory) (body : TypedBody) : Prop :=
  (∃ sig, TheoryDefinition t sig body) ∨
    ∃ b, Declaration.block b ∈ t.declarations.toList ∧ body ∈ b.members.toList

def RootInventory (p : Program) (t : Theory) : Prop :=
  ∀ body, body ∈ p.typed.bodies.toList ↔ TheoryRoot t body

def DefinitionInventory (p : Program) (t : Theory) : Prop :=
  ∀ sig body, SourceDefinition p.typed sig body ↔ TheoryDefinition t sig body

/-- Normative request fields; assumptions are selected by role over the full block. -/
def RequestFor (b : Block) (question : Question) (r : CheckRequest) : Prop :=
  r = ⟨b.owner, b.parameters, b.context,
    b.members.filter (fun m => m.member.any (·.kind == .assume)), question,
    match question with
    | .assumptionsSatisfiable =>
        (b.members.filter (fun m => m.member.any (·.kind == .assume))).map Demand.mk
    | .validity goal =>
        ((b.members.filter (fun m => m.member.any (·.kind == .assume))).map Demand.mk).push ⟨goal⟩⟩

/-- Indices retain multiplicity even if two members have equal Boolean values. -/
def BlockLayout (b : Block) (rs : Array CheckRequest) : Prop :=
  let goals := b.members.filter (fun m => m.member.any (·.kind == .expect))
  rs.size = 1 + goals.size ∧
    (∃ r, rs[0]? = some r ∧ RequestFor b .assumptionsSatisfiable r) ∧
    ∀ i : Fin goals.size, ∃ r, rs[i.val + 1]? = some r ∧ RequestFor b (.validity goals[i]) r

/-- Concatenation is by declaration order, not owner-table iteration. -/
inductive RequestOrder : List Declaration → List CheckRequest → Prop where
  | nil : RequestOrder [] []
  | enumeration : RequestOrder ds rs → RequestOrder (.enumeration e :: ds) rs
  | function : RequestOrder ds rs → RequestOrder (.function f :: ds) rs
  | block : BlockLayout b here.toArray → RequestOrder ds rest →
      RequestOrder (.block b :: ds) (here ++ rest)

def Constructs (p : Program) (t : Theory) : Prop :=
  t.source = p.typed ∧
    (∃ ds, p.input.document.root = .declarations ds ∧
      DeclarationOrder p ds.toList t.declarations.toList) ∧
    RootInventory p t ∧ DefinitionInventory p t ∧
    RequestOrder t.declarations.toList t.requests.toList

/-- The same scoped sites as Desugaring, now rooted in real MIR declarations. -/
def DomainSite (t : Theory) (body : TypedBody) (ctx : TypeContext)
    (guards : List Desugaring.Guard) (left : Expr) (token : Token) (op : BinaryOp) (right : Expr) : Prop :=
  TheoryRoot t body ∧ (op = .div ∨ op = .rem) ∧
    Desugaring.ScopedAt t.source.resolved t.source.signatures body.context body.expression ctx
      (.binary left token op right) guards

/-- Positional parameters and nearest-first local assignments are distinct. -/
def Assignment (s : Typed) (ctx : TypeContext) (env : List FrenEval.Value) : Prop :=
  env.length = ctx.length ∧ ∀ (i : Nat) (token : Token) (ty : FrenExpr.Ty), ctx[i]? = some (token, ty) →
    ∃ v : FrenEval.Value, env[i]? = some v ∧ v.type = ty ∧ v.valid s = true

/-- Defined-value meaning over production syntax, parameterized by definitions.
It is a judgment, not an executable compiler or a bounded evaluation trace. -/
inductive ValueOf (s : Typed) (defines : Signature → TypedBody → Prop) :
    TypeContext → Expr → List FrenEval.Value → FrenEval.Value → Prop where
  | bool : ValueOf s defines ctx (.bool token b) env (.bool b)
  | integer : ValueOf s defines ctx (.integer token n) env (.int n)
  | local : FrenHirToThir.Selects s.resolved ctx path .expression (.local i) → env[i]? = some v →
      ValueOf s defines ctx (.name path) env v
  | constructor {ctor : FrenBase.ItemId} : FrenHirToThir.Selects s.resolved ctx path .expression (.item ctor) →
      FrenHirToThir.constructorType s.resolved ctor = some (.enum owner) →
      ValueOf s defines ctx (.name path) env (.enum owner ctor)
  | paren : ValueOf s defines ctx e env v → ValueOf s defines ctx (.paren o e c) env v
  | unary : ValueOf s defines ctx e env v → FrenEval.unary op v = .ok result →
      ValueOf s defines ctx (.unary tok op e) env result
  | binary : ValueOf s defines ctx a env av → ValueOf s defines ctx b env bv →
      FrenEval.binary op av bv = .ok result → ValueOf s defines ctx (.binary a tok op b) env result
  | call {values : Array FrenEval.Value} : Thir.HasCallable s.resolved s.signatures ctx callee sig → defines sig body →
      body.context = FrenHirToThir.parameterContext sig.parameters → body.type = sig.result →
      args.size = values.size →
      (∀ i : Fin args.size, ∀ j : Fin values.size, i.val = j.val →
        ValueOf s defines ctx args[i] env values[j]) →
      Assignment s body.context values.toList.reverse →
      ValueOf s defines body.context body.expression values.toList.reverse result →
      ValueOf s defines ctx (.call callee o args commas c) env result
  | ifTrue : ValueOf s defines ctx condition env (.bool true) → ValueOf s defines ctx yes env v →
      ValueOf s defines ctx (.ifE i condition t yes e no) env v
  | ifFalse : ValueOf s defines ctx condition env (.bool false) → ValueOf s defines ctx no env v →
      ValueOf s defines ctx (.ifE i condition t yes e no) env v
  | letE : ValueOf s defines ctx value env v →
      ValueOf s defines ((name, v.type) :: ctx) body (v :: env) result →
      ValueOf s defines ctx (.letE l name assign value inside body) env result
  | matchE : ValueOf s defines ctx scrutinee env (.enum owner ctor) →
      arm ∈ arms.toList → FrenHirToThir.Selects s.resolved ctx arm.1 .pattern (.item ctor) →
      ValueOf s defines ctx arm.2.2.1 env result →
      ValueOf s defines ctx (.matchE m scrutinee o arms c) env result

/-- Static traversal visits both ordinary operands and unused let values.
A let body carries its actual bound value; explicit guards alone select branches. -/
inductive StaticAt (s : Typed) (defines : Signature → TypedBody → Prop) :
    TypeContext → Expr → List FrenEval.Value →
      TypeContext → Expr → List FrenEval.Value → List Desugaring.Guard → Prop where
  | root : StaticAt s defines ctx e env ctx e env []
  | ordinary : StaticAt s defines rootCtx root rootEnv ctx parent env guards →
      Desugaring.ScopedChild s.resolved s.signatures ctx parent ctx child [] →
      StaticAt s defines rootCtx root rootEnv ctx child env guards
  | letBody : StaticAt s defines rootCtx root rootEnv ctx
        (.letE l name assign value inside body) env guards →
      FrenHirToThir.HasValue s.resolved s.signatures ctx value ty →
      ValueOf s defines ctx value env v → v.type = ty →
      StaticAt s defines rootCtx root rootEnv ((name, ty) :: ctx) body (v :: env) guards
  | thenBranch : StaticAt s defines rootCtx root rootEnv ctx (.ifE i condition t yes e no) env guards →
      ValueOf s defines ctx condition env (.bool true) →
      StaticAt s defines rootCtx root rootEnv ctx yes env (guards ++ [.branch ctx condition true])
  | elseBranch : StaticAt s defines rootCtx root rootEnv ctx (.ifE i condition t yes e no) env guards →
      ValueOf s defines ctx condition env (.bool false) →
      StaticAt s defines rootCtx root rootEnv ctx no env (guards ++ [.branch ctx condition false])
  | armBody : StaticAt s defines rootCtx root rootEnv ctx (.matchE m scrutinee o arms c) env guards →
      arm ∈ arms.toList → ValueOf s defines ctx scrutinee env (.enum owner ctor) →
      FrenHirToThir.Selects s.resolved ctx arm.1 .pattern (.item ctor) →
      StaticAt s defines rootCtx root rootEnv ctx arm.2.2.1 env (guards ++ [.arm ctx scrutinee arm.1])

/-- Nonzero-divisor obligations at every statically applicable written site. -/
def BodySafe (s : Typed) (defines : Signature → TypedBody → Prop)
    (body : TypedBody) (args : Array FrenEval.Value) : Prop :=
  ∀ ctx env guards left token op right,
    StaticAt s defines body.context body.expression args.toList.reverse ctx
      (.binary left token op right) env guards → (op = .div ∨ op = .rem) →
    ∃ n : Int, ValueOf s defines ctx right env (.int n) ∧ n ≠ 0

def AllTrue (s : Typed) (defines : Signature → TypedBody → Prop)
    (bodies : Array TypedBody) (args : Array FrenEval.Value) : Prop :=
  ∀ body ∈ bodies.toList, ValueOf s defines body.context body.expression args.toList.reverse (.bool true)

/-- A sufficient verification domain with independently safe assumptions.
No mutually partial assumption is used to establish its own safety. -/
def VerificationDomain (s : Typed) (defines : Signature → TypedBody → Prop) (r : CheckRequest) : Prop :=
  (∀ sig body, defines sig body → ∀ args, Assignment s body.context args.toList.reverse →
    BodySafe s defines body args) ∧
  (∀ args, Assignment s r.context args.toList.reverse →
    ∀ body ∈ r.assumptions.toList, BodySafe s defines body args) ∧
  (∀ args, Assignment s r.context args.toList.reverse → AllTrue s defines r.assumptions args →
    ∀ body ∈ r.demand.toList, BodySafe s defines body.root args)

/-- Questions are formulas, not solver verdicts. Static verification is separate. -/
def QuestionMeaning (s : Typed) (defines : Signature → TypedBody → Prop) (r : CheckRequest) : Prop :=
  match r.question with
  | .assumptionsSatisfiable => ∃ args, Assignment s r.context args.toList.reverse ∧
      AllTrue s defines r.assumptions args
  | .validity goal => ∀ args, Assignment s r.context args.toList.reverse →
      AllTrue s defines r.assumptions args →
      ValueOf s defines goal.context goal.expression args.toList.reverse (.bool true)

/-- Functionality concerns retained body roots, whose descendants are covered by
shared static judgments. It says nothing about caller-fabricated expressions.
The same environment is used on both sides; uniqueness needs no type premise. -/
def SourceFunctionality (p : Program) : Prop :=
  ∀ body ∈ p.typed.bodies.toList, ∀ env a b,
    ValueOf p.typed (SourceDefinition p.typed) body.context body.expression env a →
    ValueOf p.typed (SourceDefinition p.typed) body.context body.expression env b → a = b

/-- Static source facts and uniqueness of defined values are explicit premises. -/
def SemanticDomain (p : Program) : Prop :=
  Thir.BodyInventory p.input p.typed ∧ Thir.BodyTyping p.input p.typed ∧
    Thir.OccurrenceInventory p.input p.typed ∧ Thir.OccurrenceTyping p.input p.typed ∧
    Thir.MatchCoverage p.input p.typed ∧ Thir.Nonrecursive p.input p.typed ∧
    SourceFunctionality p

def ConfirmedCounterexample (p : Program) (t : Theory) (r : CheckRequest)
    (args : Array FrenEval.Value) : Prop :=
  Produces p t ∧ Constructs p t ∧ SemanticDomain p ∧ r ∈ t.requests.toList ∧
    VerificationDomain p.typed (SourceDefinition p.typed) r ∧
    Assignment p.typed r.context args.toList.reverse ∧
    AllTrue p.typed (SourceDefinition p.typed) r.assumptions args ∧
    ∃ goal, r.question = .validity goal ∧
      ValueOf p.typed (SourceDefinition p.typed) goal.context goal.expression args.toList.reverse (.bool false)

/-- Universal producer correspondence remains a separately named obligation. -/
def PassContract : Prop := ∀ p t, Produces p t → Constructs p t
-- reference end

/-- Request layouts are proved on the helper actually used by the producer. -/
theorem block_layout (b : Block) : BlockLayout b b.requests := by
  dsimp only [BlockLayout]
  refine ⟨FrenMir.request_count b, ?_, ?_⟩
  · refine ⟨_, FrenMir.satisfiability_first b, ?_⟩
    rfl
  · intro i
    let g := (b.members.filter (fun m => m.member.any (·.kind == .expect)))[i]
    refine ⟨⟨b.owner, b.parameters, b.context, b.assumptions, .validity g,
      (b.assumptions.map Demand.mk).push ⟨g⟩⟩, ?_, ?_⟩
    · simp [Block.requests, Block.goals, Array.getElem?_append, i.isLt, g]
    · rfl

private theorem assembled_order (ds : List Declaration) :
    RequestOrder ds (ds.flatMap (fun d => (match d with | .block b => b.requests | _ => #[]).toList)) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih =>
    cases d with
    | enumeration e => exact .enumeration ih
    | function f => exact .function ih
    | block b => exact .block (by simpa using block_layout b) ih

theorem produced_request_order (p : Program) (t : Theory) (h : Produces p t) :
    RequestOrder t.declarations.toList t.requests.toList := by
  rw [FrenThirToMir.requests_from_blocks p t h]
  rw [Array.toList_flatMap]
  have hr := assembled_order t.declarations.toList
  apply Eq.mp ?_ hr
  apply congrArg (RequestOrder t.declarations.toList)
  apply congrArg (fun f => t.declarations.toList.flatMap f)
  funext d
  cases d <;> rfl

theorem produced_retains (p : Program) (t : Theory) (h : Produces p t) :
    t.source = p.typed ∧ FrenHirToThir.checkWalking p.input = .ok t.source :=
  ⟨FrenThirToMir.retains p t h, FrenThirToMir.admission p t h⟩

/-- Exact source success domain: admission followed by actual successful construction. -/
theorem entry_success (file : FrenSource.FileId) (source : String) (t : Theory) :
    FrenThirToMir.fromSource file source = .ok t ↔
      ∃ p, FrenWalking.fromSource file source = .ok p ∧ Produces p t := by
  unfold FrenThirToMir.fromSource
  cases hp : FrenWalking.fromSource file source with
  | error d => simp [Bind.bind, Except.bind]
  | ok p =>
    simp only [Bind.bind, Except.bind, Except.mapError, Produces]
    cases hc : FrenThirToMir.produce p <;> simp [hc]

/-- The whole concrete evaluator result is preserved at every operational depth. -/
theorem interpreter_preservation (p : Program) (t : Theory) (h : Produces p t)
    (request : FrenEval.Request) (values : Array FrenEval.Value) (depth : Nat) :
    FrenEval.evaluate ⟨p.input, t.source, FrenThirToMir.admission p t h⟩ request values depth =
      FrenEval.evaluate (Desugaring.Evaluator p) request values depth := by
  have hs := FrenThirToMir.retains p t h
  cases t with
  | mk source declarations requests =>
    dsimp only at hs
    cases hs
    rfl

theorem produced_unique (p : Program) (a b : Theory) (ha : Produces p a) (hb : Produces p b) : a = b :=
  FrenThirToMir.deterministic p a b ha hb

theorem failed_not_produced (p : Program) (d : FrenDiag.Diagnostic) (h : Rejects p d) :
    ∀ t, ¬ Produces p t := by
  intro t success
  unfold Produces at success
  unfold Rejects at h
  rw [h] at success
  contradiction

theorem entry_failure (file : FrenSource.FileId) (source : String)
    (d : FrenHirToThir.StaticFailure) (h : FrenWalking.fromSource file source = .error d) :
    FrenThirToMir.fromSource file source = .error d := FrenThirToMir.rejected file source d h

/-- Every actual request's hypotheses and context come from its own complete block. -/
theorem produced_request_context (p : Program) (t : Theory) (h : Produces p t)
    (r : CheckRequest) (hr : r ∈ t.requests) :
    ∃ b, Declaration.block b ∈ t.declarations ∧
      r.owner = b.owner ∧ r.parameters = b.parameters ∧ r.context = b.context ∧
      r.assumptions = b.assumptions := by
  obtain ⟨b, hb, hr⟩ := FrenThirToMir.request_from_block p t h r hr
  exact ⟨b, hb, FrenMir.request_context b r hr⟩

/-- Site preservation uses the explicit root-inventory premise, not value traces. -/
theorem domain_sites (p : Program) (t : Theory) (h : Produces p t) (roots : RootInventory p t) :
    ∀ body ctx guards left token op right,
      Desugaring.DomainSite p body ctx guards left token op right ↔
        DomainSite t body ctx guards left token op right := by
  intro body ctx guards left token op right
  have hs := FrenThirToMir.retains p t h
  have hi := (FrenHirToThir.walking_retains p.input p.typed p.accepted).1
  simp only [Desugaring.DomainSite, DomainSite, hs, hi, roots body]

/-- Equality of retained data transports every observation, including negative outcomes. -/
theorem source_observation (p : Program) (t : Theory) (h : Produces p t)
    {α : Sort _} (observe : Typed → α) : observe t.source = observe p.typed := by
  rw [FrenThirToMir.retains p t h]

/-- The semantic bridge has an exact premise: all and only real definitions. -/
theorem value_correspondence (p : Program) (t : Theory) (h : Produces p t)
    (definitions : DefinitionInventory p t) (ctx : TypeContext) (e : Expr) (env : List FrenEval.Value)
    (v : FrenEval.Value) :
    ValueOf p.typed (SourceDefinition p.typed) ctx e env v ↔
      ValueOf t.source (TheoryDefinition t) ctx e env v := by
  have hd : SourceDefinition p.typed = TheoryDefinition t :=
    funext fun sig => funext fun body => propext (definitions sig body)
  rw [FrenThirToMir.retains p t h, hd]

/-- This transports the static-safety premise as well as the question formula. -/
theorem check_correspondence (p : Program) (t : Theory) (h : Produces p t)
    (definitions : DefinitionInventory p t) (r : CheckRequest) :
    (VerificationDomain p.typed (SourceDefinition p.typed) r ∧
      QuestionMeaning p.typed (SourceDefinition p.typed) r) ↔
    (VerificationDomain t.source (TheoryDefinition t) r ∧
      QuestionMeaning t.source (TheoryDefinition t) r) := by
  have hd : SourceDefinition p.typed = TheoryDefinition t :=
    funext fun sig => funext fun body => propext (definitions sig body)
  rw [FrenThirToMir.retains p t h, hd]

/-- Static paths project to the shared scope relation, including original guard contexts. -/
theorem static_scopes (h : StaticAt s defines rootCtx root rootEnv ctx e env guards) :
    Desugaring.ScopedAt s.resolved s.signatures rootCtx root ctx e guards := by
  induction h with
  | root => exact .root
  | ordinary _ edge ih => simpa using Desugaring.ScopedAt.child ih edge
  | letBody _ typed _ _ ih => simpa using Desugaring.ScopedAt.child ih (.letBody typed)
  | thenBranch _ _ ih => exact .child ih .thenBranch
  | elseBranch _ _ ih => exact .child ih .elseBranch
  | armBody _ member _ _ ih => exact .child ih (.armBody member)

/-- An actual validity goal is a retained MIR root, not caller-invented syntax. -/
theorem produced_goal_root (p : Program) (t : Theory) (h : Produces p t)
    (r : CheckRequest) (hr : r ∈ t.requests.toList) (hq : r.question = .validity goal) :
    TheoryRoot t goal := by
  obtain ⟨b, hb, member⟩ := FrenThirToMir.request_from_block p t h r (by simpa using hr)
  simp only [Block.requests, Array.mem_append, Array.mem_singleton, Array.mem_map] at member
  rcases member with same | ⟨g, hg, same⟩
  · subst r
    cases hq
  · subst r
    cases Question.validity.inj hq
    exact Or.inr ⟨b, by simpa using hb, by
      have hm := (FrenMir.goals_exact b goal).mp hg
      simpa using hm.1⟩

/-- Confirmation establishes source-root membership before using functionality. -/
theorem counterexample_refutes (h : ConfirmedCounterexample p t r args) :
    ¬ QuestionMeaning p.typed (SourceDefinition p.typed) r := by
  rcases h with ⟨produced, constructed, domain, present, _, assignment, assumptions,
    goal, question, falseValue⟩
  have root := produced_goal_root p t produced r present question
  have sourceRoot := (constructed.2.2.1 goal).mpr root
  intro valid
  unfold QuestionMeaning at valid
  rw [question] at valid
  have trueValue := valid args assignment assumptions
  have unique := domain.2.2.2.2.2.2 goal sourceRoot _ _ _ trueValue falseValue
  cases unique

/-- Every observation of a specified request follows its exact relational fields. -/
theorem request_for_observation (h : RequestFor b question r) {α : Sort _}
    (observe : CheckRequest → α) :
    observe r = observe ⟨b.owner, b.parameters, b.context,
      b.members.filter (fun m => m.member.any (·.kind == .assume)), question,
      match question with
      | .assumptionsSatisfiable =>
          (b.members.filter (fun m => m.member.any (·.kind == .assume))).map Demand.mk
      | .validity goal =>
          ((b.members.filter (fun m => m.member.any (·.kind == .assume))).map Demand.mk).push ⟨goal⟩⟩ := by
  cases h
  cases question <;> rfl

-- Static obligations survive deciding ordinary operands and unused definitions.
example (s : Typed) (defines : Signature → TypedBody → Prop) (ctx : TypeContext)
    (env : List FrenEval.Value) (left right : Expr) (b andTok divTok : Token) :
    StaticAt s defines ctx (.binary (.bool b false) andTok .and (.binary left divTok .div right)) env
      ctx (.binary left divTok .div right) env [] := .ordinary .root .binaryRight

example (s : Typed) (defines : Signature → TypedBody → Prop) (ctx : TypeContext)
    (env : List FrenEval.Value) (left right rest : Expr) (l name assign inside op : Token) :
    StaticAt s defines ctx (.letE l name assign (.binary left op .rem right) inside rest) env
      ctx (.binary left op .rem right) env [] := .ordinary .root .letValue

-- These regressions prove a sufficient, executable non-vacuity condition for
-- the repaired functionality clause, then check it on actual admitted roots.
private def falseMatch : Expr → Bool
  | .matchE _ _ _ arms _ => match arms.toList with
    | [(_, _, .bool _ false, _)] => true
    | _ => false
  | _ => false

private theorem singleton_false_value
    (h : ValueOf s defines ctx
      (.matchE m scrutinee o #[(pattern, arrow, .bool token false, comma)] c) env v) :
    v = .bool false := by
  cases h with
  | matchE _ member _ value =>
    simp at member
    cases member
    cases value
    rfl

private theorem false_match_value (h : ValueOf s defines ctx expr env v)
    (shape : falseMatch expr = true) : v = .bool false := by
  unfold falseMatch at shape
  split at shape
  · rename_i m scrutinee o arms c
    split at shape
    · rename_i pattern arrow token comma armsEq
      have same : arms = #[(pattern, arrow, .bool token false, comma)] := by
        apply Array.toList_inj.mp
        exact armsEq
      rw [same] at h
      exact singleton_false_value h
    · contradiction
  · contradiction

private theorem source_functionality_of_false_matches (p : Program)
    (checked : p.typed.bodies.all (fun body => falseMatch body.expression) = true) :
    SourceFunctionality p := by
  intro body present env a b ha hb
  have shape : falseMatch body.expression = true :=
    (Array.all_eq_true'.mp checked) body (by simpa using present)
  exact (false_match_value ha shape).trans (false_match_value hb shape).symm

/-- The positive match class also has a value when its actual references select
local zero and the selected constructor, so uniqueness is not merely vacuous. -/
private theorem singleton_false_reachable
    (hs : FrenHirToThir.Selects s.resolved ctx scrutinee .expression (.local 0))
    (hp : FrenHirToThir.Selects s.resolved ctx pattern .pattern (.item ctor)) :
    ValueOf s defines ctx
      (.matchE m (.name scrutinee) o #[(pattern, arrow, .bool token false, comma)] c)
      [.enum owner ctor] (.bool false) :=
  .matchE (arm := (pattern, arrow, .bool token false, comma)) (.local hs rfl) (by simp) hp .bool

/-- Raw duplicate-arm syntax is ambiguous, but does not belong to the checked roots. -/
private theorem raw_duplicate_values
    (hs : ValueOf s defines ctx scrutinee env (.enum owner ctor))
    (hp : FrenHirToThir.Selects s.resolved ctx pattern .pattern (.item ctor)) :
    let yes := (pattern, arrow, Expr.bool token true, comma)
    let no := (pattern, arrow, Expr.bool token false, comma)
    let expr := Expr.matchE m scrutinee o #[yes, no] c
    falseMatch expr = false ∧ ValueOf s defines ctx expr env (.bool true) ∧
      ValueOf s defines ctx expr env (.bool false) ∧
      ∀ body : TypedBody, falseMatch body.expression = true → body.expression ≠ expr := by
  refine ⟨rfl, .matchE (arm := (pattern, arrow, .bool token true, comma)) hs (by simp) hp .bool,
    .matchE (arm := (pattern, arrow, .bool token false, comma)) hs (by simp) hp .bool, ?_⟩
  intro body shape same
  rw [same] at shape
  cases shape

#eval show IO Unit from do
  let source := "mod covered\nenum E { A }\n" ++
    "fn f(e: E): Bool := match e { E::A => false }\n" ++
    "expect c(e: E) { expect g: match e { E::A => false } }\n"
  let .ok p := FrenWalking.fromSource ⟨191⟩ source
    | throw (IO.userError "covered enum-match source rejected")
  let .ok t := FrenThirToMir.produce p | throw (IO.userError "covered enum MIR rejected")
  unless p.typed.bodies.size == 2 && p.typed.bodies.all (fun b => falseMatch b.expression) do
    throw (IO.userError "source functionality sufficient condition failed")
  let some body := p.typed.bodies[0]? | throw (IO.userError "enum function missing")
  let .matchE m scrutinee o arms c := body.expression | throw (IO.userError "match missing")
  let some arm := arms[0]? | throw (IO.userError "arm missing")
  let no := (arm.1, arm.2.1, Expr.bool arm.2.1 false, arm.2.2.2)
  let yes := (arm.1, arm.2.1, Expr.bool arm.2.1 true, arm.2.2.2)
  let duplicate := Expr.matchE m scrutinee o #[yes, no] c
  unless !falseMatch duplicate && !(p.typed.bodies.any (fun b => b.expression == duplicate)) do
    throw (IO.userError "fabricated duplicate admitted to the regression domain")
  let .name path := scrutinee | throw (IO.userError "expected local scrutinee")
  let some sr := p.typed.resolved.referenceAt path.head.slice
    | throw (IO.userError "scrutinee reference missing")
  let some pr := p.typed.resolved.referenceAt arm.1.head.slice
    | throw (IO.userError "pattern reference missing")
  unless sr.role == .expression && sr.target == .local 0 &&
      sr.context == body.context.map Prod.fst && pr.role == .pattern &&
      pr.context == body.context.map Prod.fst do
    throw (IO.userError "resolved match premises differ")
  let .item ctor := pr.target | throw (IO.userError "constructor target missing")
  let some (.enum owner) := FrenHirToThir.constructorType p.typed.resolved ctor
    | throw (IO.userError "constructor type missing")
  let value := FrenEval.Value.enum owner ctor
  unless value.valid p.typed do throw (IO.userError "enum assignment invalid")
  let .ok evaluation := FrenEval.evaluate (Desugaring.Evaluator p)
      ⟨p.input.scope.id.named "c", some "g"⟩ #[value] 20
    | throw (IO.userError "enum goal evaluation failed")
  unless (match evaluation.outcome with | .ok (.bool false) => true | _ => false) && t.requests.size == 2 do
    throw (IO.userError "enum goal is not a defined false validity request")
  let duplicateSource := source.replace "E::A => false" "E::A => false, E::A => true"
  let .error (.validation (.coverage _ actualOwner missing repeated)) :=
      FrenWalking.fromSource ⟨191⟩ duplicateSource
    | throw (IO.userError "duplicate arms did not reach coverage validation")
  unless actualOwner == owner && missing.isEmpty && repeated == #[ctor] do
    throw (IO.userError "wrong duplicate-arm coverage diagnostic")
  IO.println "MIR functionality regression: 2 admitted covered enum-match roots satisfy the proved functionality condition; defined false goal retained; fabricated and written duplicate-arm controls rejected"

-- This finite control uses real admission and production, then edits their raw output.
-- Printed records are only a decidable necessary observation, not an injective encoding theorem.
#eval show IO Unit from do
  let source := "mod contracts\n" ++
    "fn unused(x: Int): Int := let y := 1 div 0 in x\n" ++
    "fn ordinary(b?: Bool): Bool := b? or (1 % 0 = 0)\n" ++
    "fn guarded(d: Int): Int := if d != 0 then 1 div d else 0\n" ++
    "expect owned(x: Int, b?: Bool) { expect first: b? assume early: x >= 0 " ++
    "expect second: x <= 10 assume later: x <= 5 }\nexpect empty() {}\n"
  let .ok p := FrenWalking.fromSource ⟨91⟩ source
    | throw (IO.userError "MIR contract source was rejected")
  let .ok t := FrenThirToMir.produce p | throw (IO.userError "MIR contract producer failed")
  let some (Declaration.block b) := t.declarations[3]? | throw (IO.userError "owned block missing")
  let some first := b.members[0]? | throw (IO.userError "first goal missing")
  let some early := b.members[1]? | throw (IO.userError "early assumption missing")
  let some second := b.members[2]? | throw (IO.userError "second goal missing")
  let some later := b.members[3]? | throw (IO.userError "later assumption missing")
  let key := FrenBase.ItemId.root.named "contracts"
  unless b.owner == key.named "owned" && b.members.size == 4 &&
      b.parameters.map (·.written.name.text) == #["x", "b?"] &&
      b.context.map (·.1.text) == ["b?", "x"] do
    throw (IO.userError "owner/parameter/source member order changed")
  let assumptions := #[early, later]
  let sat : CheckRequest := ⟨b.owner, b.parameters, b.context, assumptions,
    .assumptionsSatisfiable, #[⟨early⟩, ⟨later⟩]⟩
  let valid := fun goal => (⟨b.owner, b.parameters, b.context, assumptions,
    .validity goal, #[⟨early⟩, ⟨later⟩, ⟨goal⟩]⟩ : CheckRequest)
  let some (Declaration.block empty) := t.declarations[4]? | throw (IO.userError "empty block missing")
  let emptySat : CheckRequest := ⟨key.named "empty", #[], [], #[], .assumptionsSatisfiable, #[]⟩
  let expected := #[sat, valid first, valid second, emptySat]
  let observes := fun rs : Array CheckRequest => rs.map reprStr == expected.map reprStr
  unless observes t.requests && empty.members.isEmpty do
    throw (IO.userError "ordered request contract failed")
  let changes : Array (String × (CheckRequest → CheckRequest)) := #[
    ("later assumption deleted", fun r => {r with assumptions := #[early]}),
    ("foreign owner", fun r => {r with owner := key.named "foreign"}),
    ("parameter order", fun r => {r with parameters := r.parameters.reverse}),
    ("local context", fun r => {r with context := r.context.reverse}),
    ("goal assumed", fun r => {r with assumptions := assumptions.push first}),
    ("goal changed", fun r => {r with question := .validity second}),
    ("satisfiability substituted", fun r => {r with question := .assumptionsSatisfiable}),
    ("demand erased", fun r => {r with demand := #[]}),
    ("goal demand erased", fun r => {r with demand := #[⟨early⟩, ⟨later⟩]})]
  for (label, change) in changes do
    if observes (t.requests.modify 1 change) then
      throw (IO.userError s!"request mutation admitted: {label}")
  for rs in #[t.requests.reverse, t.requests.pop, t.requests.push emptySat] do
    if observes rs then throw (IO.userError "request order/multiplicity mutant admitted")
  let definitions := fun ds : Array Declaration => ds.filterMap fun d => match d with
    | .function f => some (reprStr f.definition) | _ => none
  let written := (p.typed.bodies.filter (·.member.isNone)).map reprStr
  unless definitions t.declarations == written && written.size == 3 do
    throw (IO.userError "full unused definition roots lost")
  if definitions (t.declarations.extract 1 t.declarations.size) == written then
    throw (IO.userError "unused function deletion admitted")
  let .ok otherFile := FrenThirToMir.fromSource ⟨92⟩ source
    | throw (IO.userError "same source in second file rejected")
  if otherFile.requests.map reprStr == expected.map reprStr then
    throw (IO.userError "distinct source origins merged")
  IO.println "MIR contract controls: 3 complete definition roots, 4 ordered requests; 12 request mutants, unused definition deletion and foreign file substitution rejected"

#print axioms block_layout
#print axioms produced_request_order
#print axioms domain_sites
#print axioms value_correspondence
#print axioms check_correspondence
#print axioms counterexample_refutes
#print axioms interpreter_preservation
#print axioms produced_goal_root
#print axioms source_functionality_of_false_matches
#print axioms raw_duplicate_values
#print axioms singleton_false_reachable

end Spec.Compiler.Mir
