import Fren.Impl
import Fren.Literate
import Spec.Compiler.Lir
import FrenLirToOir

open Fren.Lang

#fren_md "Oir.md"

namespace Spec.Compiler.Oir
open FrenModule FrenAst FrenLir FrenOir

-- reference begin
abbrev Input := FrenThirDesugar.Program

def Produces (p : Input) (out : FrenOir.Program) : Prop :=
  FrenLirToOir.produce p = .ok out

def Rejects (p : Input) (failure : FrenLirToOir.Failure) : Prop :=
  FrenLirToOir.produce p = .error failure

inductive DomainFor (p : FrenLir.Program) : FrenExpr.Ty → Domain → Prop where
  | boolean : DomainFor p .bool .boolean
  | integer : DomainFor p .int .integer
  | enumeration : Declaration.enumeration e ∈ p.declarations.toList →
      DomainFor p (.enum e.id) (.enumeration e.id (e.constructors.map Prod.fst))

def ParametersFor (p : FrenLir.Program) (source : Array TypedParameter) (ps : Array FrenOir.Parameter) : Prop :=
  Lir.Pairs (fun s a => a.source = s ∧ DomainFor p s.type a.domain) source.toList ps.toList

/-- Ordered extraction judgment, without the implementation's depth bound.
Available paths are earlier checks; required paths are context prerequisites. -/
inductive Extracts : Verification → Option Origin → List Nat → List FrenOir.Frame →
    List (List Nat) → List (List Nat) → List FrenLirToOir.Leaf → Prop where
  | empty : Extracts .empty origin path frames available required []
  | check : Extracts (.check c) (some o) path frames available required [⟨o, path, frames, c, required⟩]
  | both : Extracts a origin (path ++ [0]) frames available required left →
      Extracts b origin (path ++ [1]) frames (available ++ left.map (·.path)) required right →
      Extracts (.both a b) origin path frames available required (left ++ right)
  | branch : Extracts a origin (path ++ [0]) (frames ++ [.guard c true]) available (required ++ available) yes →
      Extracts b origin (path ++ [1]) (frames ++ [.guard c false]) available (required ++ available) no →
      Extracts (.branch c a b) origin path frames available required (yes ++ no)
  | binding : Extracts body origin (path ++ [0]) (frames ++ [.binding name ty v d])
      available (required ++ available) leaves →
      Extracts (.letE name ty v d body) origin path frames available required leaves
  | at : Extracts body (some o) (path ++ [0]) frames available required leaves →
      Extracts (.at o body) origin path frames available required leaves

/-- Erase only redundant incoming type contexts, not frame order or terms. -/
inductive FramesFor : List Lir.Frame → List FrenOir.Frame → Prop where
  | nil : FramesFor [] []
  | guard : FramesFor rest out → FramesFor (.guard ctx c selected :: rest) (.guard c selected :: out)
  | binding : FramesFor rest out →
      FramesFor (.binder ctx name ty v d :: rest) (.binding name ty v d :: out)

def SiteFor (b : Body) (leaf : FrenLirToOir.Leaf) : Prop :=
  ∃ fs, Lir.Site b.source.context none b.term.verification leaf.path fs
    leaf.origin.context (some leaf.origin) leaf.condition ∧ FramesFor fs leaf.frames

/-- Structural application occurrence, including both components of every let. -/
inductive Uses (id : FrenBase.ItemId) : Term → Prop where
  | app {sig : Signature} : sig.id = id → Uses id (.app sig component args)
  | argument : a ∈ args → Uses id a → Uses id (.app sig component args)
  | unary : Uses id a → Uses id (.unary op a)
  | left : Uses id a → Uses id (.binary op a b)
  | right : Uses id b → Uses id (.binary op a b)
  | condition : Uses id c → Uses id (.ite c a b)
  | yes : Uses id a → Uses id (.ite c a b)
  | no : Uses id b → Uses id (.ite c a b)
  | value : Uses id v → Uses id (.letE name ty v d b)
  | domain : Uses id d → Uses id (.letE name ty v d b)
  | body : Uses id b → Uses id (.letE name ty v d b)
  | at : Uses id a → Uses id (.at origin a)

def QuestionEdges (q : FrenOir.Question) : List Dependency :=
  q.dependencies.toList.filter fun d => match d with | .question _ => true | _ => false

/-- Definition edges may repeat after the assumption update. Their support is
exact; neither a missing equation nor an unrelated symbol is permitted. -/
def DefinitionEdges (q : FrenOir.Question) : Prop :=
  ∀ id, Dependency.definition id ∈ q.dependencies.toList ↔ Uses id q.search

def AssumptionEdges (all : Array FrenOir.Question) (bs : Array Body) : List Dependency :=
  all.toList.filterMap fun q =>
    if q.kind == .assumptionDefinedness && bs.any (fun b => q.subject == some b.source)
    then some (.question q.id) else none

def Others (r : CheckRequest) (b : Body) : Array Body :=
  if FrenLirToOir.structurallyTotal b then #[] else r.assumptions.filter (fun a => a.source != b.source)

def AssumptionState (r : CheckRequest) (b : Body) : Readiness :=
  if (Others r b).all FrenLirToOir.structurallyTotal then .ready
  else .unresolved "mutually partial assumptions: contextual definedness dependency rule unresolved"

def RequestState (all : Array FrenOir.Question) (r : CheckRequest) : Readiness :=
  if (AssumptionEdges all r.assumptions).any (fun d => match d with
      | .question id => all[id]?.any (fun q => q.readiness != .ready) | _ => false) then
    .unresolved "mutually partial assumptions: contextual definedness dependency rule unresolved"
  else .ready

def LocalEdges (leaves : List FrenLirToOir.Leaf) (start index : Nat)
    (leaf : FrenLirToOir.Leaf) (edges : List Dependency) : Prop :=
  Lir.Pairs (fun path edge => ∃ i, i < index ∧
    (leaves[i]?.map (·.path)) = some path ∧ edge = .question (start + i)) leaf.prerequisites edges

def BodyQuestionFor (p : FrenLir.Program) (start : Nat) (leaves : List FrenLirToOir.Leaf)
    (kind : Kind) (ps : Array TypedParameter) (request : Option Nat) (b : Body)
    (hypotheses : Array Body) (edges : List Dependency) (state : Readiness)
    (entry : FrenLirToOir.Leaf × Nat) (q : FrenOir.Question) : Prop :=
  let leaf := entry.1
  q.id = start + entry.2 ∧ q.kind = kind ∧ q.owner = b.source.owner ∧
  ParametersFor p ps q.parameters ∧ q.context = b.source.context ∧ q.request = request ∧
  q.subject = some b.source ∧ q.origin = some leaf.origin ∧ q.path = leaf.path ∧
  q.frames = leaf.frames ∧ q.condition = leaf.condition ∧ q.hypotheses = hypotheses ∧
  q.readiness = state ∧ SiteFor b leaf ∧
  leaf.origin.owner = b.source.owner ∧ leaf.origin.member = b.source.member ∧
  (∃ o ∈ b.source.occurrences.toList,
    o.expression = leaf.origin.expression ∧ o.context = leaf.origin.context) ∧
  Lir.Sorted p.mir.source q.context q.search .bool ∧ DefinitionEdges q ∧
  ∃ localEdges, LocalEdges leaves start entry.2 leaf localEdges ∧
    QuestionEdges q = (if kind = .assumptionDefinedness then localEdges ++ edges else edges ++ localEdges)

def BodyGroup (p : FrenLir.Program) (start : Nat) (kind : Kind) (ps : Array TypedParameter)
    (request : Option Nat) (b : Body) (hypotheses : Array Body) (edges : List Dependency)
    (state : Readiness) (qs : List FrenOir.Question) : Prop :=
  ∃ leaves, Extracts b.term.verification none [] [] [] [] leaves ∧
    Lir.Pairs (BodyQuestionFor p start leaves kind ps request b hypotheses edges state) leaves.zipIdx qs

def SearchFor (p : FrenLir.Program) (index id : Nat) (r : CheckRequest) (kind : Kind)
    (subject : Option TypedBody) (condition : Term) (edges : List Dependency)
    (state : Readiness) (q : FrenOir.Question) : Prop :=
  q.id = id ∧ q.kind = kind ∧ q.owner = r.source.owner ∧
  ParametersFor p r.source.parameters q.parameters ∧ q.context = r.source.context ∧
  q.request = some index ∧ q.subject = subject ∧ q.origin = none ∧ q.path = [] ∧ q.frames = [] ∧
  q.hypotheses = r.assumptions ∧ q.condition = condition ∧ q.readiness = state ∧
  QuestionEdges q = edges ∧ DefinitionEdges q ∧ Lir.Sorted p.mir.source q.context q.search .bool

inductive AssumptionGroups (p : FrenLir.Program) (all : Array FrenOir.Question) (r : CheckRequest) :
    Nat → List Body → List FrenOir.Question → Prop where
  | nil : AssumptionGroups p all r start [] []
  | cons : BodyGroup p start .assumptionDefinedness r.source.parameters none b (Others r b)
      (AssumptionEdges all (Others r b)) (AssumptionState r b) first →
      AssumptionGroups p all r (start + first.length) rest more →
      AssumptionGroups p all r start (b :: rest) (first ++ more)

inductive RequestGroup (p : FrenLir.Program) (all : Array FrenOir.Question)
    (start index : Nat) (r : CheckRequest) : List FrenOir.Question → Prop where
  | sat : r.question = .assumptionsSatisfiable →
      AssumptionGroups p all r start r.assumptions.toList first →
      SearchFor p index (start + first.length) r .assumptionsSatisfiable none (.bool true)
        (AssumptionEdges all r.assumptions) (RequestState all r) q →
      RequestGroup p all start index r (first ++ [q])
  | validity : r.question = .validity goal →
      BodyGroup p start .goalDefinedness r.source.parameters (some index) goal r.assumptions
        (AssumptionEdges all r.assumptions) (RequestState all r) first →
      SearchFor p index (start + first.length) r .validity (some goal.source) goal.term.value
        (AssumptionEdges all r.assumptions ++ (List.range first.length).map (fun i => .question (start + i)))
        (RequestState all r) q → RequestGroup p all start index r (first ++ [q])

inductive RequestGroups (p : FrenLir.Program) (all : Array FrenOir.Question) :
    Nat → List (CheckRequest × Nat) → List FrenOir.Question → Prop where
  | nil : RequestGroups p all start [] []
  | cons : RequestGroup p all start index r first →
      RequestGroups p all (start + first.length) rest more →
      RequestGroups p all start ((r, index) :: rest) (first ++ more)

inductive DeclarationGroups (p : FrenLir.Program) (all : Array FrenOir.Question) :
    Nat → List Declaration → List FrenOir.Question → Prop where
  | nil : DeclarationGroups p all start [] []
  | enumeration : DeclarationGroups p all start rest qs →
      DeclarationGroups p all start (.enumeration e :: rest) qs
  | function : BodyGroup p start .functionDefinedness sig.parameters none b #[] [] .ready first →
      DeclarationGroups p all (start + first.length) rest more →
      DeclarationGroups p all start (.function sig b :: rest) (first ++ more)
  | block : RequestGroups p all start
      (p.requests.toList.zipIdx.filter (fun ri => ri.1.source.owner == block.owner)) first →
      DeclarationGroups p all (start + first.length) rest more →
      DeclarationGroups p all start (.block block members :: rest) (first ++ more)

/-- Complete output contract. Upstream LIR construction is a separate premise. -/
def Constructs (out : FrenOir.Program) : Prop :=
  out.enumerations = out.lir.declarations.filterMap (fun d => match d with
    | .enumeration e => some e | _ => none) ∧
  out.definitions = out.lir.declarations.filterMap (fun d => match d with
    | .function sig b => some ⟨sig, b⟩ | _ => none) ∧
  DeclarationGroups out.lir out.questions 0 out.lir.declarations.toList out.questions.toList ∧
  (∀ q ∈ out.questions.toList, ∀ id, Uses id q.search → ∃ d ∈ out.definitions.toList, d.signature.id = id)

/-- Meaning of active frames in their original environments. A false guard
has no active continuation; binding interprets value/domain before extending. -/
inductive Active (symbols : Lir.Symbols) (zero : Lir.ZeroValues) :
    Lir.Slots → List FrenOir.Frame → Lir.Slots → Prop where
  | nil : Active symbols zero env [] env
  | guard : Lir.Meaning symbols zero env c (.bool selected) → Active symbols zero env rest leaf →
      Active symbols zero env (.guard c selected :: rest) leaf
  | binding : Lir.Meaning symbols zero env v value → Lir.Meaning symbols zero env d (.bool domain) →
      Active symbols zero ((value, domain) :: env) rest leaf →
      Active symbols zero env (.binding name ty v d :: rest) leaf

def Assignment (out : FrenOir.Program) (q : FrenOir.Question) (values : List FrenEval.Value) : Prop :=
  Mir.Assignment out.lir.mir.source q.context values

def SearchHolds (symbols : Lir.Symbols) (zero : Lir.ZeroValues)
    (q : FrenOir.Question) (values : List FrenEval.Value) : Prop :=
  Lir.Meaning symbols zero (values.map (fun v => (v, true))) q.search (.bool true)

def Violation (symbols : Lir.Symbols) (zero : Lir.ZeroValues)
    (q : FrenOir.Question) (values : List FrenEval.Value) : Prop :=
  Lir.AllTrue symbols zero (values.map (fun v => (v, true))) q.hypotheses ∧
    ∃ leaf, Active symbols zero (values.map (fun v => (v, true))) q.frames leaf ∧
      Lir.Meaning symbols zero leaf q.condition (.bool false)

def ConditionValid (out : FrenOir.Program) (symbols : Lir.Symbols) (zero : Lir.ZeroValues)
    (q : FrenOir.Question) : Prop :=
  ∀ values, Assignment out q values →
    Lir.AllTrue symbols zero (values.map (fun v => (v, true))) q.hypotheses →
    ∀ leaf, Active symbols zero (values.map (fun v => (v, true))) q.frames leaf →
      Lir.Meaning symbols zero leaf q.condition (.bool true)

def QuestionTrue (out : FrenOir.Program) (symbols : Lir.Symbols) (zero : Lir.ZeroValues)
    (q : FrenOir.Question) : Prop :=
  if q.kind = .assumptionsSatisfiable then ∃ values, Assignment out q values ∧ SearchHolds symbols zero q values
  else ¬ ∃ values, Assignment out q values ∧ SearchHolds symbols zero q values

/-- Model equations use actual LIR bodies, with total parameter-domain slots. -/
def EquationsHold (out : FrenOir.Program) (symbols : Lir.Symbols) (zero : Lir.ZeroValues) : Prop :=
  ∀ d ∈ out.definitions.toList, ∀ args,
    Mir.Assignment out.lir.mir.source d.body.source.context args.reverse →
    Lir.Meaning symbols zero (args.reverse.map (fun v => (v, true))) d.value (symbols d.signature .value args) ∧
    Lir.Meaning symbols zero (args.reverse.map (fun v => (v, true))) d.domain (symbols d.signature .domain args)

def RequestMeaning (out : FrenOir.Program) (symbols : Lir.Symbols) (zero : Lir.ZeroValues)
    (index : Nat) : Prop :=
  ∃ q ∈ out.questions.toList, q.request = some index ∧
    (q.kind = .assumptionsSatisfiable ∨ q.kind = .validity) ∧ QuestionTrue out symbols zero q

/-- Named universal obligations, not assumed theorems. The sufficient LIR
domain is independent of OIR search results and does not assume this conclusion. -/
def PassContract : Prop := ∀ p out, Produces p out → Constructs out

def SearchContract : Prop := ∀ p out, Produces p out → Lir.Constructs p out.lir → Constructs out →
  Mir.SemanticDomain p → ∀ symbols, Lir.Models p symbols → ∀ zero,
  EquationsHold out symbols zero → ∀ q ∈ out.questions.toList, ∀ values, Assignment out q values →
    (SearchHolds symbols zero q values ↔
      if q.kind = .assumptionsSatisfiable then
        Lir.AllTrue symbols zero (values.map (fun v => (v, true))) q.hypotheses
      else Violation symbols zero q values)

def RequestContract : Prop := ∀ p out, Produces p out → Lir.Constructs p out.lir → Constructs out →
  Mir.SemanticDomain p → ∀ symbols, Lir.Models p symbols → ∀ zero,
  EquationsHold out symbols zero → ∀ index r, out.lir.requests[index]? = some r →
  Lir.VerificationDomain out.lir symbols zero r →
    (RequestMeaning out symbols zero index ↔ Lir.QuestionMeaning out.lir symbols zero r) ∧
    (∀ q ∈ out.questions.toList,
      q.kind = .functionDefinedness ∨ q.kind = .assumptionDefinedness ∧ q.owner = r.source.owner ∨
        q.kind = .goalDefinedness ∧ q.request = some index → ConditionValid out symbols zero q)
-- reference end

theorem produced_boundary (p : Input) (out : FrenOir.Program) (h : Produces p out) :
    Lir.Produces p out.lir ∧ out.lir.mir.source = p.typed ∧ out.lir.wellFormed = true :=
  ⟨FrenLirToOir.retains_lir p out h, FrenLirToOir.retains_source p out h,
    FrenLirToOir.scoped_input p out h⟩

theorem produced_unique (p : Input) (a b : FrenOir.Program) (ha : Produces p a) (hb : Produces p b) : a = b :=
  FrenLirToOir.deterministic p a b ha hb

theorem failure_excludes_success (p : Input) (failure : FrenLirToOir.Failure) (h : Rejects p failure) :
    ∀ out, ¬ Produces p out := by
  intro out success
  unfold Produces at success
  unfold Rejects at h
  rw [h] at success
  contradiction

theorem entry_success (file : FrenSource.FileId) (source : String) (out : FrenOir.Program) :
    FrenLirToOir.fromSource file source = .ok out ↔
      ∃ p, FrenThirDesugar.fromSource file source = .ok p ∧ Produces p out := by
  unfold FrenLirToOir.fromSource
  cases hp : FrenThirDesugar.fromSource file source with
  | error d => simp [Bind.bind, Except.bind, Except.mapError]
  | ok p =>
    simp only [Bind.bind, Except.bind, Except.mapError, Produces]
    cases hc : FrenLirToOir.produce p <;> simp [hc]

theorem retained_equations (p : Input) (out : FrenOir.Program) (h : Produces p out) :
    out.definitions = out.lir.declarations.filterMap (fun d => match d with
      | .function sig b => some ⟨sig, b⟩ | _ => none) := FrenLirToOir.retained_equations p out h

theorem search_polarity (q : FrenOir.Question) (h : q.kind ≠ .assumptionsSatisfiable) :
    q.search = .binary .and (conjunction (q.hypotheses.map (·.term.value)))
      (inScope q.frames (.unary .not q.condition)) := FrenOir.search_counterexample q h

/-- A zero-depth traversal is failure even for an empty tree. -/
theorem depth_failure : FrenLirToOir.walk 0 .empty none [] [] [] [] =
    .error (.resourceExhausted "verification traversal depth") := rfl

theorem unattributed_failure : FrenLirToOir.walk 1 (.check c) none [] [] [] [] =
    .error (.invalidInput "unattributed verification check") := rfl

theorem literal_extraction (o : Origin) (c : Term) :
    Extracts (.at o (.check c)) none [] [] [] [] [⟨o, [0], [], c, []⟩] := .at .check

theorem branch_extraction (o : Origin) (guard c : Term) :
    Extracts (.at o (.branch guard (.check c) .empty)) none [] [] [] []
      [⟨o, [0, 0], [.guard guard true], c, []⟩] := .at (.branch .check .empty)

/-- Both ordinary children remain, even when their conditions coincide. -/
theorem ordinary_extraction (o : Origin) (a b : Term) :
    FrenLirToOir.walk 3 (.at o (.both (.check a) (.check b))) none [] [] [] [] =
      .ok [⟨o, [0, 0], [], a, []⟩, ⟨o, [0, 1], [], b, []⟩] := rfl

theorem binding_extraction (o : Origin) (name : Token) (ty : FrenExpr.Ty) (v d a b : Term) :
    FrenLirToOir.walk 4 (.at o (.both (.check a) (.letE name ty v d (.check b)))) none [] [] [] [] =
      .ok [⟨o, [0, 0], [], a, []⟩,
        ⟨o, [0, 1, 0], [.binding name ty v d], b, [[0, 0]]⟩] := rfl

theorem active_nil : Active symbols zero env [] leaf ↔ leaf = env := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact .nil

theorem false_guard_inactive : ¬ Active symbols zero env (.guard (.bool false) true :: rest) leaf := by
  intro h
  cases h with | guard value _ => cases value

theorem meaning_not (x : Bool) :
    Lir.Meaning symbols zero env (.unary .not (.bool x)) (.bool (!x)) :=
  .unary .bool (by cases x <;> rfl)

theorem literal_search (q : FrenOir.Question) (x : Bool) (kind : q.kind ≠ .assumptionsSatisfiable)
    (hypotheses : q.hypotheses = #[]) (frames : q.frames = []) (condition : q.condition = .bool x) :
    Lir.Meaning symbols zero env q.search (.bool (!x)) := by
  rw [search_polarity q kind, hypotheses, frames, condition]
  simp only [Array.map_empty, conjunction, Array.foldr_empty, inScope, List.foldr_nil]
  exact .binary .bool (meaning_not x) (.ordinary (by cases x <;> rfl))

/-- Every successful bounded traversal has the unbounded ordered derivation.
This is not the converse depth-adequacy or whole-pass construction theorem. -/
theorem walk_extracts (depth : Nat) (tree : Verification) (origin : Option Origin)
    (path : List Nat) (frames : List FrenOir.Frame) (available required : List (List Nat))
    (leaves : List FrenLirToOir.Leaf)
    (h : FrenLirToOir.walk depth tree origin path frames available required = .ok leaves) :
    Extracts tree origin path frames available required leaves := by
  induction depth generalizing tree origin path frames available required leaves with
  | zero => simp [FrenLirToOir.walk] at h
  | succ n ih =>
    cases tree with
    | empty =>
      simp [FrenLirToOir.walk] at h
      cases h
      exact .empty
    | check c =>
      cases origin with
      | none => simp [FrenLirToOir.walk] at h
      | some o =>
        simp [FrenLirToOir.walk] at h
        cases h
        exact .check
    | both a b =>
      cases ha : FrenLirToOir.walk n a origin (path ++ [0]) frames available required with
      | error e => simp [FrenLirToOir.walk, ha, Bind.bind, Except.bind] at h
      | ok left =>
        cases hb : FrenLirToOir.walk n b origin (path ++ [1]) frames
            (available ++ left.map (·.path)) required with
        | error e => simp [FrenLirToOir.walk, ha, hb, Bind.bind, Except.bind] at h
        | ok right =>
          simp [FrenLirToOir.walk, ha, hb, Bind.bind, Except.bind] at h
          cases h
          exact .both (ih _ _ _ _ _ _ _ ha) (ih _ _ _ _ _ _ _ hb)
    | branch c a b =>
      cases ha : FrenLirToOir.walk n a origin (path ++ [0]) (frames ++ [.guard c true])
          available (required ++ available) with
      | error e => simp [FrenLirToOir.walk, ha, Bind.bind, Except.bind] at h
      | ok left =>
        cases hb : FrenLirToOir.walk n b origin (path ++ [1]) (frames ++ [.guard c false])
            available (required ++ available) with
        | error e => simp [FrenLirToOir.walk, ha, hb, Bind.bind, Except.bind] at h
        | ok right =>
          simp [FrenLirToOir.walk, ha, hb, Bind.bind, Except.bind] at h
          cases h
          exact .branch (ih _ _ _ _ _ _ _ ha) (ih _ _ _ _ _ _ _ hb)
    | letE name ty v d body => exact .binding (ih _ _ _ _ _ _ _ h)
    | «at» o body => exact .at (ih _ _ _ _ _ _ _ h)

/-- A nonempty class satisfying the entire OIR construction contract. These
are actual production records, used below against admitted empty-block output. -/
def EmptyRequest (owner : FrenBase.ItemId) : CheckRequest :=
  ⟨⟨owner, #[], [], #[], .assumptionsSatisfiable, #[]⟩,
    #[], .assumptionsSatisfiable, #[]⟩

def EmptyQuestion (owner : FrenBase.ItemId) : FrenOir.Question :=
  ⟨0, .assumptionsSatisfiable, owner, #[], [], some 0, none,
    none, [], #[], [], .bool true, #[], .ready⟩

def EmptyWitness (mir : FrenMir.Theory) (b : FrenMir.Block) : FrenOir.Program :=
  let block := {b with parameters := #[], context := [], members := #[]}
  ⟨⟨mir, #[.block block #[]], #[EmptyRequest b.owner]⟩, #[], #[], #[EmptyQuestion b.owner]⟩

theorem empty_witness_constructs (mir : FrenMir.Theory) (b : FrenMir.Block) :
    Constructs (EmptyWitness mir b) := by
  let out := EmptyWitness mir b
  have search : SearchFor out.lir 0 0 (EmptyRequest b.owner) .assumptionsSatisfiable none (.bool true)
      [] .ready (EmptyQuestion b.owner) := by
    dsimp [out, EmptyWitness, EmptyRequest, EmptyQuestion, SearchFor, ParametersFor, DefinitionEdges, QuestionEdges]
    refine ⟨rfl, rfl, rfl, .nil, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro id
      constructor
      · intro h; cases h
      · intro h
        simp only [FrenOir.Question.search, ite_true, Array.map_empty, conjunction, Array.foldr_empty] at h
        cases h
    · simpa only [FrenOir.Question.search, ite_true, Array.map_empty, conjunction, Array.foldr_empty]
        using (Lir.Sorted.bool (s := mir.source) (ctx := []) (b := true))
  change Constructs out
  refine ⟨rfl, rfl, ?_, ?_⟩
  · apply DeclarationGroups.block (first := [EmptyQuestion b.owner]) (more := [])
    · simp only [out, EmptyWitness, EmptyRequest, List.zipIdx_cons,
        List.zipIdx_nil, List.filter_cons, BEq.rfl, List.filter_nil, if_true]
      apply RequestGroups.cons (first := [EmptyQuestion b.owner]) (more := [])
      · apply RequestGroup.sat (first := [])
        · rfl
        · exact .nil
        · simpa [out, EmptyWitness, EmptyRequest, EmptyQuestion, AssumptionEdges, RequestState] using search
      · exact .nil
    · exact .nil
  · intro q present id used
    have same : q = EmptyQuestion b.owner := by simpa [out, EmptyWitness] using present
    rw [same] at used
    simp only [EmptyQuestion, FrenOir.Question.search, ite_true, Array.map_empty, conjunction, Array.foldr_empty] at used
    cases used

theorem empty_witness_sat (mir : FrenMir.Theory) (b : FrenMir.Block) :
    RequestMeaning (EmptyWitness mir b) symbols zero 0 := by
  refine ⟨EmptyQuestion b.owner, by simp [EmptyWitness], rfl, Or.inl rfl, ?_⟩
  simp only [QuestionTrue, EmptyQuestion, ite_true]
  simp only [Assignment, EmptyWitness, SearchHolds, EmptyQuestion, FrenOir.Question.search,
    ite_true, Array.map_empty, conjunction, Array.foldr_empty]
  refine ⟨[], ⟨rfl, ?_⟩, .bool⟩
  intro i token ty h
  simp at h

theorem wrong_condition_rejected (p : FrenLir.Program) (owner : FrenBase.ItemId) :
    ¬ SearchFor p 0 0 (EmptyRequest owner) .assumptionsSatisfiable none (.bool true) [] .ready
      {EmptyQuestion owner with condition := .bool false} := by
  simp [SearchFor, EmptyQuestion]

theorem wrong_frame_rejected (p : FrenLir.Program) (owner : FrenBase.ItemId) :
    ¬ SearchFor p 0 0 (EmptyRequest owner) .assumptionsSatisfiable none (.bool true) [] .ready
      {EmptyQuestion owner with frames := [.guard (.bool false) true]} := by
  simp [SearchFor, EmptyQuestion]

/-- A real nonempty obligation is valid for every environment and every
zero-divisor totalization, without assuming a semantic preservation theorem. -/
theorem constant_divisor_valid (out : FrenOir.Program) (q : FrenOir.Question) (origin : Origin)
    (condition : q.condition = .binary .ne (.at origin (.int 2)) (.int 0)) :
    ConditionValid out symbols zero q := by
  intro values _ _ leaf _
  rw [condition]
  exact .binary (.at .int) .int (.ordinary rfl)

/-- An outer guard is interpreted before a later lexical binding. -/
example (name : Token) (ty : FrenExpr.Ty) (v d c : Term)
    (value : Lir.Meaning symbols zero env v x) (domain : Lir.Meaning symbols zero env d (.bool wd))
    (guard : Lir.Meaning symbols zero env c (.bool true)) :
    Active symbols zero env [.guard c true, .binding name ty v d] ((x, wd) :: env) :=
  .guard guard (.binding value domain .nil)

theorem unresolved_not_ready (s : String) : Readiness.unresolved s ≠ .ready := by
  intro h
  cases h

theorem unknown_retained (q : FrenOir.Question) (s : String) : q.interpret (.unknown s) = .unknown s := rfl

/-- Composition consumes the upstream contracts; it does not prove them. -/
theorem request_to_source (lirContract : Lir.RequestContract) (oirContract : RequestContract)
    (p : Input) (out : FrenOir.Program) (produced : Produces p out)
    (lirConstructs : Lir.Constructs p out.lir) (oirConstructs : Constructs out)
    (semantic : Mir.SemanticDomain p) (model : Lir.Models p symbols)
    (equations : EquationsHold out symbols zero) (index : Nat) (r : CheckRequest)
    (atIndex : out.lir.requests[index]? = some r) (member : r ∈ out.lir.requests.toList)
    (safe : Mir.VerificationDomain p.typed (Mir.SourceDefinition p.typed) r.source) :
    RequestMeaning out symbols zero index ↔ Mir.QuestionMeaning p.typed (Mir.SourceDefinition p.typed) r.source := by
  have upstream := lirContract p out.lir (produced_boundary p out produced).1
    lirConstructs semantic symbols model zero r member safe
  exact ((oirContract p out produced lirConstructs oirConstructs semantic symbols model zero equations
    index r atIndex upstream.1).1).trans upstream.2

-- These are admitted actual-producer controls, not universal pass proofs.
#eval show IO Unit from do
  let .ok empty := FrenLirToOir.fromSource ⟨213⟩ "mod oir_contracts\nexpect empty() {}\n"
    | throw (IO.userError "empty OIR witness admission failed")
  let #[.block block _] := empty.lir.declarations
    | throw (IO.userError "empty witness declaration shape")
  let expected := EmptyWitness empty.lir.mir block
  have _constructed : Constructs expected := empty_witness_constructs empty.lir.mir block
  have _sat : RequestMeaning expected (fun _ _ _ => .bool true) (fun _ _ => 0) 0 :=
    empty_witness_sat empty.lir.mir block
  unless empty == expected do throw (IO.userError "admitted output differs from proved complete OIR witness")
  let .ok total := FrenLirToOir.fromSource ⟨213⟩ "mod oir_contracts\nfn total(x: Int): Int := 1 div 2\n"
    | throw (IO.userError "total division witness admission failed")
  let #[totalQuestion] := total.questions | throw (IO.userError "total divisor obligation missing")
  unless totalQuestion.kind == .functionDefinedness && totalQuestion.frames.isEmpty &&
      totalQuestion.hypotheses.isEmpty && totalQuestion.context.map (·.1.text) == ["x"] do
    throw (IO.userError "total divisor witness has an unexpected conditional context")
  match condition : totalQuestion.condition with
  | .binary .ne (.at origin (.int 2)) (.int 0) =>
    have _valid : ConditionValid total (fun _ _ _ => .bool true) (fun _ _ => 0) totalQuestion :=
      constant_divisor_valid total totalQuestion origin condition
    pure ()
  | _ => throw (IO.userError "actual total divisor condition differs from proved semantic witness")
  let source := "mod oir_contracts\nfn unused(d: Int): Int := let x := 1 div d in 0\n" ++
    "fn guarded(d: Int): Int := if d != 0 then 1 div d else 0\n" ++
    "expect c(n: Int, d: Int) { expect wrong: n div d = 0 assume later: d != 0 }\n"
  let .ok admitted := FrenThirDesugar.fromSource ⟨213⟩ source
    | throw (IO.userError "nonempty OIR witness admission failed")
  let .ok out := FrenLirToOir.produce admitted
    | throw (IO.userError "nonempty OIR witness generation failed")
  unless out.lir.mir.source == admitted.typed && out.definitions.size == 2 && out.lir.requests.size == 2 do
    throw (IO.userError "nonempty source/definition/request retention")
  let divisions := out.questions.filter (fun q => match q.condition with
    | .binary .ne _ (.int 0) => true | _ => false)
  let #[unused, guarded, goalDomain] := divisions
    | throw (IO.userError "static divisor inventory")
  unless unused.frames.isEmpty && unused.hypotheses.isEmpty && unused.request.isNone &&
      (match guarded.frames with | [.guard _ true] => true | _ => false) &&
      goalDomain.request == some 1 && goalDomain.hypotheses.size == 1 &&
      goalDomain.context.map (·.1.text) == ["d", "n"] && out.questions.all (fun q => q.readiness == .ready) do
    throw (IO.userError "unused/guarded/assumed contexts differ")
  let validity := out.questions.filter (fun q => q.kind == .validity)
  let #[q] := validity | throw (IO.userError "validity inventory")
  unless q.subject.any (fun b => b.member.any (·.label.text == "wrong")) &&
      q.hypotheses.all (fun b => b.source.member.any (fun m => m.kind == .assume && m.label.text == "later")) &&
      (QuestionEdges q).contains (.question goalDomain.id) do
    throw (IO.userError "false-capable goal, later assumption or domain dependency lost")
  let some request := out.lir.requests[1]? | throw (IO.userError "retained request absent")
  let .validity goal := request.question | throw (IO.userError "retained goal absent")
  -- The retained LIR request, rather than OIR output equality, is the oracle.
  let retained := fun changed : FrenOir.Question => changed.owner == request.source.owner &&
    changed.context == request.source.context && changed.hypotheses == request.assumptions &&
    changed.condition == goal.term.value && changed.frames.isEmpty
  unless retained q do throw (IO.userError "actual question violates the retained request contract")
  for changed in #[{q with hypotheses := #[]}, {q with condition := .bool true},
      {q with frames := [.guard (.bool false) true]}] do
    unless Term.infer 10000 out.lir.mir.source changed.context changed.search == some .bool && !retained changed do
      throw (IO.userError "well-sorted condition/hypothesis/context mutation survived")
  let .error (.admission _) := FrenLirToOir.fromSource ⟨213⟩ "mod bad\nfn f(x: Int): Int := false"
    | throw (IO.userError "typing failure confused with false goal")
  IO.println "OIR contract witnesses: admitted complete empty-block Constructs and existential Sat; admitted nonempty divisor ConditionValid proof for all assignments; 2 real definitions, 3 divisor sites, guarded/unused/later-assumption contexts, 2 ordered requests; 3 well-sorted record mutants rejected. No solver or universal pass proof."

#print axioms produced_boundary
#print axioms entry_success
#print axioms retained_equations
#print axioms ordinary_extraction
#print axioms binding_extraction
#print axioms false_guard_inactive
#print axioms literal_search
#print axioms walk_extracts
#print axioms empty_witness_constructs
#print axioms empty_witness_sat
#print axioms wrong_condition_rejected
#print axioms wrong_frame_rejected
#print axioms constant_divisor_valid
#print axioms request_to_source

end Spec.Compiler.Oir
