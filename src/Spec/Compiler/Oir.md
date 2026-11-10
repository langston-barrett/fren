# Obligations (OIR)

Obligation generation relates an admitted [LIR program](Lir.md) to ordered
logical questions. Each question retains its complete typed parameter domain,
owner, optional request and subject, source occurrence, lexical frames,
condition, hypotheses and prerequisites. A condition is an actual
`FrenLir.Term` of Bool sort; OIR introduces no second expression language.
Value preservation, static safety, satisfiability and validity are separate
judgments. A false expectation remains an admitted question.

## 1. Semantic objects and admission

`FrenOir.Program` contains `lir`, `enumerations`, `definitions` and
`questions`. A `Definition` pairs a canonical signature with its actual LIR
body. Its `value` and `domain` projections are the body's value term and
verification summary. Neither projection is an axiom that the body is total.
`Domain` is `boolean`, `integer`, or `enumeration owner constructors`.
`Parameter` retains the entire typed parameter together with that domain.

**Legality rules**

r[oir.terms.sorts]
`DomainFor` relates complete parameter domains to declared source types.
Bool has two values, Int all mathematical integers, and an enum exactly its
own canonical constructors in declaration order. `ParametersFor` preserves
written parameter order and multiplicity. Questions retain the nearest-first
body context, the reverse of that parameter order. Parameters have true local
domain components; this interpretation rule is not a block hypothesis.
Every question's search must satisfy the shared unbounded `Lir.Sorted`
judgment at Bool. Constructor identity, call signatures, local types, origin
contexts and binder scope have exactly the LIR sorting rules.

**Proof obligations**

r[oir.walking.input]
`Produces p out` is the actual `FrenLirToOir.produce` success relation on the
same evidence-carrying source program as LIR. It runs actual LIR production;
a caller-edited logical program or a successful scope audit is insufficient.
`Rejects` retains the exact generation failure. `fromSource` first performs
actual parsing, resolution, typing, coverage and non-recursion admission.
It distinguishes `SourceFailure.admission` from `SourceFailure.generation`.
Generation failures distinguish invalid input, unsupported equations,
resource exhaustion and a retained LIR lowering diagnostic. Traversal depth
is 10000; exhaustion cannot become an empty obligation list, ill-sorting,
false, or a successful verification result.

The source domain is the shared Bool/Int/payload-free nominal enum core,
nonrecursive named functions, lexical lets, explicit if and exhaustive
constructor matches, and global assumption/expectation blocks. Definitions
and blocks retain their complete LIR/MIR/source records. No source assertion,
local assumption, subset, closure, procedure relation or general quantifier
constructor is added. Mathematical quantification over parameters below is
part of the question's meaning.

## 2. Owned requests and prerequisite groups

A `Question` has fields `id`, `kind`, `owner`, `parameters`, `context`,
`request`, `subject`, `origin`, `path`, `hypotheses`, `frames`, `condition`,
`dependencies` and `readiness`. `Kind` is `functionDefinedness`,
`assumptionDefinedness`, `goalDefinedness`, `assumptionsSatisfiable`, or
`validity`. IDs are zero-based positions in the single question array.
`Dependency.question id` names an actual generated question;
`Dependency.definition id` names an actual definition equation pair.
A dependency is evidence still required, not a Boolean hypothesis.

**Proof obligations**

r[oir.walking.requests]
`DeclarationGroups`, `RequestGroups`, `RequestGroup`, `AssumptionGroups`
and `BodyGroup` specify the complete ordered inventory. Process declarations
in written order. Each function, including an unused one, emits its domain
leaves with no hypotheses or request index. For each block, process its
retained LIR requests in order: one Sat request, even for an empty block,
then one validity request for every written expectation. All and only the
block's assumptions apply, including assumptions written after the goal.
A goal, sibling goal or another block's assumption is never a premise.

At Sat, emit each assumption's domain group once, then the Sat search.
Validity reuses those assumption groups, emits the goal's domain leaves,
then the validity search. Domain questions retain their exact typed body and
leaf origin. Sat has condition true and no subject; validity has the actual
goal value and complete goal subject. Both have empty frames, no leaf origin
and empty path, and retain the source request index. Goal-domain questions
also retain that index; shared assumption and function groups have none.

`Constructs` requires exact ordered enumeration/definition inventories and
this full question layout, including multiplicity. `DefinitionEdges` requires
all and only symbols structurally used by the actual search, through every
argument, branch, let value, let domain and let body. Such symbols must have
real equation pairs in `definitions`. Repeated definition edges are allowed:
assumption-group construction checks dependencies before and after adding
its hypotheses. Question-edge lists retain their order and multiplicity.

r[oir.walking.dependencies]
For an assumption body whose actual `structurallyTotal` test succeeds,
`Others` is empty. This conservative syntactic recognizer follows true,
parameter/let domain slots, conjunction, both conditional branches and
lexical domain bindings. It does not guess divisor checks or applications
true, and is not a solver or general totality decision procedure.
For another body, `Others` retains every other assumption of that owner,
excluding the entire subject by source identity. Its domain questions depend
on every generated domain question of those others. If all others are
structurally total, the dependency rule is `ready`; otherwise it is
`unresolved` with the exact mutually-partial-assumptions reason in the formal
definitions. Sat, goal domains and validity depend on all assumption-domain
groups and retain their unresolved state. Validity additionally depends on
every question in its own goal-domain group.

`ready` describes support for the dependency rule; it establishes no question
and no equation. Cyclic partial-assumption edges are retained, with their
unresolved reason, rather than jointly discharged by contradiction. A single
partial assumption may use independently total siblings. For example,
`d != 0` can justify a sibling division check; two partial contradictory
assumptions cannot establish each other's safety. No rule here admits a
verified result for that unresolved dependency class.

<a id="static-traversal-guards-and-bindings"></a>

## 3. Static traversal, guards and bindings

**Proof obligations**

r[oir.walking.traversal]
`Extracts` is the unbounded ordered extraction judgment on actual
`Verification` trees and actual `Leaf` records. `empty` has no leaves;
`check` has one with its current origin, path, frames and prerequisites.
`both` concatenates both child lists, passing earlier leaf paths as available
checks to the right. `branch` retains both alternatives under positive and
negative guard frames. `letE` retains a value/domain binding frame around
its body. `at` sets the current source origin. Child indices append 0 then 1;
`at` and a binder append 0. A check without an origin has no derivation.

Both ordinary Boolean operands retain their obligations in the same incoming
context. A let value retains its checks before the binder, even when unused;
only the body is under that binder. Explicit if/match alternatives add guards.
Thus `false and (1 div 0 = 0)`, `true or (1 div 0 = 0)` and
`let x := 1 div 0 in 0` have unguarded divisor checks. In contrast,
`if false then 1 div 0 else 0` retains a false-guarded check, and
`if d != 0 then n div d else 0` checks its divisor under that explicit guard.
No execution trace or operand value selects the static inventory.

r[oir.walking.scope]
`SiteFor` relates each extracted leaf to the accepted LIR `Site` judgment,
including its exact path, source origin, leaf context and ordered frames.
`FramesFor` removes only the incoming type contexts that are redundant in
OIR's nested frame representation. A `guard condition positive` wraps a
search by conjunction with the condition or its negation. A
`binding binder type value domain` wraps it by the actual LIR let. Folding
outermost frames around innermost ones keeps an outer guard outside a later
binder. No shifting, hoisting or reinterpreting a guard at a shadowing slot
is permitted. A let interprets value/domain in the incoming environment,
then prepends their pair. Calls use positional callee arguments, without
caller locals, as in `Lir.Meaning`.

Entering a guard or binder adds all available earlier checks of that body to
the context prerequisites; earlier checks already required remain required.
These are question edges, never additional Boolean guards. Ordinary siblings
do not guard each other. `LocalEdges` requires every prerequisite to name an
earlier leaf in the same body group. Equal predicates at separate paths stay
separate diagnostic occurrences. Moving the division in
`let x := 1 div d in if d != 0 then x else 0` under the use's guard violates
this relation. Its original incoming divisor obligation remains required.

r[oir.walking.definedness]
Every written partiality obligation retained by LIR becomes its contextual
condition: division/remainder nonzero checks, local domain reads, callee
domain applications, argument checks and unused definition/value checks.
`Active` interprets the frame path using the same `Lir.Meaning`, `Slots`,
`Symbols` and `ZeroValues` as LIR. `ConditionValid` requires the leaf's true
condition for every well-typed assignment satisfying its hypotheses and
every active continuation of its frames. A false guard makes that continuation
inactive; it does not remove the occurrence. Earlier safety prerequisites
justify use of guards/bindings. An arbitrary value chosen for zero division
cannot establish its nonzero check. Undefinedness, a false condition and
failure to prove a condition are distinct.

Global assume and expect members have exactly the groups above. In this
admitted grammar the occurrence sets of written assert expressions, local
assume expressions and subset introduction/coercion are empty: neither AST
nor LIR has their constructors. An extension must add their source and LIR
rules before condition generation: assert and introduced subset predicates
require checks; local assumptions and established parameter predicates stay
in their lexical body contexts; invariant checks and partiality remain
retained. This interface supplies no implicit admission or erasure for them.

## 4. Interpretation and correspondence

**Dynamic semantics**

r[oir.meaning.search]
`Question.search` is the conjunction of the complete hypothesis values for
Sat. For every other kind it is that conjunction and the frame-wrapped
negation of the condition. Hypotheses stay outside all local frames.
`SearchHolds` interprets the search on nearest-first total parameter slots;
`Violation` independently requires true hypotheses, an active frame path and
a false leaf condition. `SearchContract` states the correspondence between
these judgments. `QuestionTrue` is existence of a typed satisfying assignment
for Sat and absence of such a counterexample for every other kind.

The empty conjunction is true, and the empty parameter tuple has one
assignment. Domains are complete, not finite search bounds. Contradictory
assumptions can make validity vacuous while Sat fails. Neither result proves
assumption definedness. No undefined assumption may be treated as false to
make validity pass or Sat fail.

**Proof obligations**

r[oir.contract.correspondence]
`EquationsHold` interprets each actual retained definition's value and domain
symbols by its LIR body, on typed positional arguments. It is separate from
`Lir.Models`, which relates those symbols to declarative source meanings.
`PassContract` states actual output construction. `SearchContract` states
formula/frame correspondence. `RequestContract` relates each main OIR
question in both directions to `Lir.QuestionMeaning`, and requires function,
owning-assumption and relevant goal-domain questions to be valid under the
independent sufficient `Lir.VerificationDomain`. These are named obligations,
not axioms or assumed universal producer theorems.

Their premises retain actual production, LIR construction, OIR construction,
`Mir.AdmissionResidue`, source-definition models and LIR equation meanings.
In particular, root-restricted source functionality/coverage, model existence,
LIR interpretation and sorting/checker correspondence are not consequences
of a finite OIR check. The source contract composes this request equivalence
with `Lir.RequestContract` and the MIR source request meaning; each upstream
contract must be established with its own premises. It never assumes OIR
soundness as an input Boolean or unrestricted source semantic functionality.
The sufficient independently safe LIR domain is stronger than the supported
single-partial-assumption rule; this theorem does not assert the converse
safety equivalence for all contextual assumption configurations.

The following block is compiled verbatim by the [chapter wrapper](Oir.lean).
It defines relations over production objects; none is a new runtime pass.

```lean
abbrev Input := FrenWalking.Program

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
  Mir.AdmissionResidue p → ∀ symbols, Lir.Models p symbols → ∀ zero,
  EquationsHold out symbols zero → ∀ q ∈ out.questions.toList, ∀ values, Assignment out q values →
    (SearchHolds symbols zero q values ↔
      if q.kind = .assumptionsSatisfiable then
        Lir.AllTrue symbols zero (values.map (fun v => (v, true))) q.hypotheses
      else Violation symbols zero q values)

def RequestContract : Prop := ∀ p out, Produces p out → Lir.Constructs p out.lir → Constructs out →
  Mir.AdmissionResidue p → ∀ symbols, Lir.Models p symbols → ∀ zero,
  EquationsHold out symbols zero → ∀ index r, out.lir.requests[index]? = some r →
  Lir.VerificationDomain out.lir symbols zero r →
    (RequestMeaning out symbols zero index ↔ Lir.QuestionMeaning out.lir symbols zero r) ∧
    (∀ q ∈ out.questions.toList,
      q.kind = .functionDefinedness ∨ q.kind = .assumptionDefinedness ∧ q.owner = r.source.owner ∨
        q.kind = .goalDefinedness ∧ q.request = some index → ConditionValid out symbols zero q)
```

## 5. Answers and source confirmation

**Proof obligations**

r[oir.walking.answers]
`Question.interpret` classifies raw search evidence only. Sat on the
assumption search gives a candidate witness; Unsat means that assumption
search is unsatisfiable. Sat on every negated-condition search gives a
candidate counterexample; Unsat gives no counterexample. Unknown,
unsupported and resource-exhausted answers retain their reasons and establish
neither polarity. No bounded failure to find a witness establishes Unsat.

A source verification result additionally requires all applicable domain,
definition and question dependencies, including function checks, to be
justified independently in their exact contexts. `readiness` must support
the dependency rule; it does not discharge any dependency. A vacuous validity
result cannot replace the separate Sat result, and unresolved results remain
unresolved. There is no aggregate-verdict constructor in OIR. Solver query
translation is governed by the separate [SMT chapter](Smt.md).

r[oir.walking.confirmation]
A model becomes a source witness or counterexample only after confirming its
complete typed assignment against retained source meanings, assumptions,
guards and static obligations. A validity counterexample has true, defined
assumptions and a defined false goal. A domain counterexample has a true
admissible context and active guard with a false domain condition, and must
be reported as that condition's failure. A Sat witness has true, defined
assumptions. Preserve canonical nominal values, owner, member label and source
span. Raw lazy evaluation can skip static obligations and is insufficient.
Unsupported or exhausted confirmation retains an unconfirmed candidate and
its reason. Confirming one assignment is not a universal preservation proof.

The constructor equations, contextual interpretation laws, admitted positive
cases and mutation controls in the wrapper are described with their exact
proof boundaries in the
[development coverage document](../../../docs/fren2-specification-coverage.md).

## 6. Logical primitives

These independent Fren1 facts specify truth-table and quantifier primitives.
They specialize negated-condition search, frame guards, retained operand
domains and the distinct Sat/validity quantifiers. They do not prove the
recursive extraction or request contracts. The procedure and
quantifier syntax below do not extend source admission.

**Dynamic semantics**

r[oir.primitive.polarity] oir_primitives::facts::polarity
A failed implication requires a true hypothesis and false goal.

r[oir.primitive.guards] oir_primitives::facts::{then_guard, else_guard}
The positive and negative branch guards give different conditional domains.

r[oir.primitive.operands] oir_primitives::facts::both_domains
Requiring both ordinary operand domains is independent of operand values.

r[oir.primitive.vacuity] oir_primitives::facts::vacuity
Contradictory hypotheses imply a goal without supplying a witness.

r[oir.primitive.quantifiers] oir_primitives::facts::witness_not_universal
Existence of a satisfying Boolean assignment does not imply all satisfy it.

```fren
pub mod oir_primitives

pub proc facts(assumption?, goal?, selected?, left_domain?, right_domain?, d: Int) {
    expect polarity: (not (when assumption?, goal?)) iff (assumption? and not goal?)
    expect then_guard: (when selected?, d != 0) iff (not selected? or d != 0)
    expect else_guard: (when not selected?, d != 0) iff (selected? or d != 0)
    expect both_domains: (not (left_domain? and right_domain?)) iff (not left_domain? or not right_domain?)
    expect vacuity: not (assumption? and not assumption?) or goal?
    expect witness_not_universal: (exists (b?: Bool), b? = goal?) and not (forall (b?: Bool), b? = goal?)
}

#fren_check
```

Changing `not goal?` to `goal?` on the right of `polarity` is deliberately
false at `assumption? = true, goal? = false`. Replacing `not selected?`
with `selected?` on the right of `then_guard` is false at
`selected? = false, d = 0`. These controls must actually fail the checker;
their counterexamples are primitive Fren1 results, not Fren2 solver models.
