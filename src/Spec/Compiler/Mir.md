# MIR and theory construction

MIR separates declarations that give expressions their meaning from owned
assumptions and questions about those expressions. This chapter relates the
actual [desugared THIR](Desugaring.md) to `FrenMir.Theory`, using the shared
[Language meanings](../Language/Expressions.md) and [THIR judgments](Thir.md).
Its domain is Bool, Int, payload-free nominal enums, nonrecursive named
functions, global checks and the expressions in the source grammar.

## 1. Semantic objects and admission

A program `p : FrenThirDesugar.Program` contains the resolved input, typed
output and evidence `checkWalking p.input = .ok p.typed`. A theory contains
`source : Typed`, ordered `declarations` and ordered `requests`. Its
declarations are enumerations, signature/body definitions and expectation
blocks. Its expressions are the actual retained syntax and typed occurrences.
A request is a question with its owner, ordered parameters, nearest-first
context, assumptions and static demand roots. It is not a verdict.

**Proof obligations**

r[mir.walking.admission]
`Produces p t` is exactly `FrenThirToMir.produce p = .ok t`; `Rejects p d`
is exactly its error with diagnostic `d`. The construction domain consists
of evidence-carrying admitted programs, rather than arbitrary edited `Typed`
records or successful type-only checks. Source entry succeeds exactly when
source admission produces a program and construction produces its theory.
Admission errors precede construction unchanged; conversion errors remain
explicit typing diagnostics. Neither kind of failure yields an empty theory.
This boundary adds no static validator or recursion rule.

r[mir.walking.retention]
For a produced theory, `t.source = p.typed`. The entire source document,
file, UTF-8 token tape, spans, canonical targets, roles, signatures, bodies
and occurrence contexts remain equal. Source declaration and member order
must satisfy `DeclarationOrder` and `MemberOrder`. Each written declaration
contributes once, except the module header; no lookup-table order may replace
written order. Equal values, names or types do not identify source occurrences.

## 2. Declarations, definitions and roots

`SourceDefinition` selects an actual signature and a complete non-member body
of that canonical function owner. `TheoryDefinition` selects the actual MIR
function declaration. `DefinitionInventory` relates those pairs in both
directions. An enum declaration keeps its written declaration and ordered
constructor/token pairs under its canonical enum identity.

**Proof obligations**

r[mir.walking.definitions]
`DeclarationFor` relates each source enum, function or block to its MIR
declaration. A function retains its parameter and result annotations, ordered
parameter types, exact result type, defining expression and complete typed
body. Definitions interpret calls; they are not arbitrary assumed axioms or
expectations awaiting proof. All unused functions remain declarations and
verification roots. Constructor ownership remains nominal even when names
coincide. Matches remain matches at this boundary.

r[mir.walking.contexts]
Each block and member retains its canonical owner and exact parameter context.
`MemberOrder` requires full member identity, Bool type, original expression
and context. A block exists even with no members. Parameters are written
left to right; assignments enter nearest-first contexts in reverse order.
A let value uses the incoming context; its body prepends one binder. A call
enters only its callee's parameter context with positional arguments.
Neither equal types nor equal spelling authorize reusing another context.

`TheoryRoot` consists of function definitions and every member of every
block. `RootInventory` equates this membership with all actual typed bodies.
This root inventory and the ordered declaration/member relations serve
different purposes: membership alone does not establish multiplicity or order.

## 3. Owned members and ordered questions

**Proof obligations**

r[mir.walking.members]
Every global block retains its written assume/expect members, labels, source
origins and parameters in order. Role is the written `MemberKind`, not the
truth of the member's body or its position in a previously checked prefix.

r[mir.walking.assumptions]
A request contains all and only its block's assumptions, including assumptions
written after its goal. They restrict that block's assignments. They do not
become global facts, definitions or proved goals. No unproved expectation
is an assumption for itself or for another request.

r[mir.walking.goals]
`RequestFor` fixes every field of a request. `BlockLayout` requires exactly
one initial assumption-satisfiability question followed by one validity
question for every expectation, in its original order. An index, rather
than just set membership, distinguishes repeated or equal-valued goals.
`RequestOrder` concatenates block layouts in declaration order; enum and
function declarations add no explicit satisfiability or validity request.
Their static obligations remain through the separate root inventory.

r[mir.walking.satisfiability]
An empty block still has one satisfiability request. A block with no
assumptions uses the empty conjunction, true. Unsatisfiable assumptions may
make every validity implication true while their separate satisfiability
question is false. This domain has no `when` trigger syntax; it does not
invent trigger-vacuity requests for each goal. These are the
[global checking rules](../../Reqs/Check.md#global-expectations) specialized
to blocks without procedure outputs or guarantees.

The following finite Fren definition gives the pointwise question matrix.
`QuestionMeaning` below quantifies the satisfiability row existentially and
the validity row universally over assignments of the declared types. Its
Boolean inputs stand for established defined meanings, not operational
failure codes or certificates of static safety.

r[mir.questions.pointwise] spec::mir::question_laws
At one assignment, satisfiability asks for the assumptions; validity asks
for their implication to the selected goal. They have different polarity.

```fren
pub mod spec
pub mod spec::mir

pub enum QuestionKind { AssumptionsSatisfiable, Validity }

pub fn question_at?(kind: QuestionKind, assumptions?, goal?) := match kind {
    QuestionKind::AssumptionsSatisfiable => assumptions?,
    QuestionKind::Validity => not assumptions? or goal?,
}

pub proc question_laws(assumptions?, goal?) {
    expect sat: question_at?(QuestionKind::AssumptionsSatisfiable, assumptions?, goal?) iff assumptions?
    expect valid: question_at?(QuestionKind::Validity, assumptions?, goal?) iff (not assumptions? or goal?)
    expect vacuous: when not assumptions?, question_at?(QuestionKind::Validity, assumptions?, goal?)
        and not question_at?(QuestionKind::AssumptionsSatisfiable, assumptions?, goal?)
    expect false_goal: when assumptions? and not goal?,
        not question_at?(QuestionKind::Validity, assumptions?, goal?)
}

#fren_check
```

## 4. Scoped definedness and interpretation

**Proof obligations**

r[mir.walking.partiality]
`DomainSite` uses the shared desugaring `ScopedAt` relation, with exact body,
lexical context, ordered guard path, operands, operator token and division/remainder
kind. MIR must retain these sites in both directions. Both ordinary Boolean
operands and every unused let value remain in the incoming static scope.
An if or match branch alone adds its explicit guard. Existing guards keep
the context in which their subject was read across later binders.

`ValueOf` is a defined-value judgment over the actual syntax, resolved
references, canonical definitions and local assignments. It uses the real
primitive integer and Boolean operations. Locals read their exact slot;
parentheses preserve values; calls use the selected definition, with all
positional arguments and no caller locals. A let binds its value once;
if and match use their selected branch. Both binary operands have defined
values in this judgment. Outside an operation's domain the Language assigns
an unspecified fixed value; `ValueOf` asserts only its specified defined
meaning, and supplies no equation for that outside-domain value.

`StaticAt` pairs structural traversal with local value environments. It
visits all ordinary children independently of short-circuit execution. A let
body extends the environment with its defined value. Explicit branch and arm
steps require the selected guard's value in its original environment.
`BodySafe` requires a nonzero integer divisor at every applicable division/remainder
site, using that site's environment. It records a mathematical requirement;
it does not claim that a solver has proved it.

`VerificationDomain` requires all named definitions safe for every typed
parameter assignment, all assumptions independently safe, and each request's
static demand roots safe under its assumptions. Thus an uncalled function
or unused written definition cannot lose its domain obligations. Undefined
assumptions cannot act as false filters. This is a sufficient domain using
independently justified assumptions; it supplies no dependency semantics for
mutually partial assumptions. Exhaustion, invalid data, unsupported cases,
unknown and solver resource limits are not Boolean values or proof evidence.

The following relations are compiled verbatim in the
[chapter wrapper](Mir.lean). They use production IR, the shared THIR judgments
and the scoped desugaring relations, without a second executable compiler.

```lean
abbrev Program := FrenThirDesugar.Program

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
```

## 5. Preservation and confirmation

**Proof obligations**

r[mir.walking.values]
Under `DefinitionInventory`, a produced theory has exactly the source
`ValueOf` judgments in both directions, at the same types, local assignments
and canonical identities. `value_correspondence` proves this conditional
law by equality of retained syntax and the definition relation. It does not
assume universal recursive type-checker or evaluator soundness.

r[mir.walking.check-correspondence]
Under the same definition inventory, `check_correspondence` transports both
`VerificationDomain` and `QuestionMeaning` for each corresponding request.
`domain_sites` additionally requires `RootInventory` and proves exact
bidirectional source-site retention. These premises must be established;
retaining an interpreter result alone cannot establish either inventory.
`Constructs` states the complete declaration, root, definition and request
contract of production; `PassContract` requires it for every successful
producer result.

`SemanticDomain` names the shared static judgments and `SourceFunctionality`:
uniqueness of defined values at actual retained body roots in their exact
lexical contexts. Match coverage constrains those roots and their descendants;
typing alone does not establish unique matching arms. This premise does not
quantify over caller-fabricated expressions. Uniqueness compares two derivations
in the same environment, including malformed assignments; confirmation separately
requires typed arguments. No additional environment premise is needed for
this uniqueness claim.

`ConfirmedCounterexample` requires actual producer evidence, `Constructs`,
this semantic domain, request membership, static verification, typed arguments,
true assumptions and the selected goal's defined false value.
`produced_goal_root` derives the goal's MIR-root membership from its actual
request. `counterexample_refutes` transports that membership through
`RootInventory` before applying source functionality to refute validity.
A solver's bare SAT answer supplies none of those missing premises, and is
not a confirmed source model.

The actual producer laws establish source retention, admission, uniqueness,
error exclusion, exact source-entry success, request ordering and request
contexts. `interpreter_preservation` equates complete evaluator results at
every depth, including failures. That operational equality neither selects
static obligations nor identifies finite exhaustion with undefinedness.
The [coverage inventory](../../../docs/fren2-specification-coverage.md)
records which universal correspondence obligations remain unproved.

## 6. Consequences

In a block with `expect goal: x <= 10` followed by `assume later: x <= 5`,
both requests contain `later`. The first asks whether some integer satisfies
`x <= 5`; the second asks whether every such integer satisfies `x <= 10`.
Changing `goal` to an assumption changes the ordered questions and their
meaning, rather than proving the original expectation.

The expression `false and (1 div 0 = 0)` can yield false under raw lazy value
evaluation, but its division site is unconditional for static verification.
The value in `let x := 1 div 0 in 3` also retains its unconditional site.
By contrast, `if d != 0 then 1 div d else 0` places division under the
positive guard, in the same context that interprets `d`. A later let cannot
reinterpret that guard's local index. These consequences follow from the
shared scope rules and `StaticAt`, independently of a particular execution.
