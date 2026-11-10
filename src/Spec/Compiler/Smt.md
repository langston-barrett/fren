# SMT queries

SMT encoding relates the admitted [OIR program](Oir.md) to one complete
SMT-LIB script per question. The retained OIR objects determine the domains,
equations, lexical context, assumptions and search polarity. The text grammar,
its interpretation, the producer envelope and the process answer are distinct
judgments. A raw answer is evidence about a search; source verification also
requires independent static safety, dependency discharge and model confirmation.

## 1. Sorts, names and admission

The source fragment is Bool, mathematical Int and payload-free nominal enums,
nonrecursive named definitions, local lets, explicit branches and exhaustive
constructor matches. Matching is already represented by LIR equality and `ite`.
There is no additional source expression language at this boundary. The
semantic values are the shared `FrenEval.Value`, contexts `TypeContext`,
terms `FrenLir.Term` and definitions `FrenOir.Definition`.

**Legality rules**

r[smt.encoding.sorts]
`SortFor` maps Bool to `Bool`, Int to `Int`, and each retained enumeration at
index i to `Ei`. Its values are exactly its own declared constructors, in
canonical order, with no payload. The integer domain is unbounded. A value
assignment satisfies `Oir.Assignment`; a local value/domain environment
satisfies `Lir.Assigned`. A domain component has Bool sort independently of
the associated value sort. A missing nominal declaration is invalid; an
empty nominal datatype is unsupported by the encoder.

r[smt.encoding.names]
`Symbol` has separate families: `Ei`, `Ci_j`, `Fiv`, `Fid`, `Pi`, `Liv` and
`Lid`. Enum and definition indices refer to their retained arrays; constructor
indices refer to that enum's constructor array. Function lookup requires the
whole canonical signature, including parameter/result types, rather than its
spelling alone. Parameter indices follow written order; local indices are
incoming environment lengths. Source names and source text never enter SMT
identifiers. Names are case sensitive decimal indexed symbols. Freshness is
required within an active scope; reuse in separate definitions or questions
is harmless. Canonical declaration identities and array uniqueness come from
the admitted source and upstream construction contracts.

**Proof obligations**

r[smt.encoding.admission]
`Produces` is actual `FrenOirToSmt.produce`, whose input is the shared admitted
source witness. It runs actual OIR production. `Rejects` preserves its upstream
failure. Hand-built OIR, scope checks or a supplied success flag are not public
admission paths. `Term.infer` checks origin context, local slot/type, canonical
constructor references, exact call signature, argument sorts/arity, operand
sorts, branch result agreement, let value sort and Bool domain. Its bounded
failure rejects upstream production. `ValidationContract` states the remaining
unbounded sorting correspondence of that actual checker on admitted source
metadata; it makes no claim about fabricated malformed `Typed` records.

The low-level `term`, `prelude` and `script` operations print supplied records;
they do not revalidate every sort, arity or duplicate identity. In particular,
a wrong-sort arithmetic term can print successfully. Only the admitted public
path and independently justified upstream construction contracts support the
well-sorted encoding claim. Open locals, absent enum/constructor/signature
references fail explicitly; missing/cyclic definition dependencies are
unsupported. Term and definition-dependency translation each use depth 10000;
exhaustion is a retained resource failure. No failed validation is a false source condition or an Unsat answer.

## 2. Terms and lexical interpretation

`ContextFor` binds a definition or query context to the actual
`parameterContext` of its ordered typed parameters, including binder tokens.
`Renders p env term text` is an unbounded grammar judgment on the actual LIR
term and concrete SMT text. `TermFor` additionally requires the same context
length and the shared `Lir.Sorted` judgment. `ParametersFor` retains written
order and `Names` reverses it for nearest-first local slots; each parameter's
domain name is the literal `true`. Parameters denote total values, independently
of block assumptions.

**Dynamic semantics**

r[smt.encoding.terms]
Boolean literals print `true`/`false`; negative integer literals print
`(- magnitude)` and other integers their magnitude. Constructors use `Ci_j`.
A local selects its slot's value or domain text. `at` erases only origin
metadata. Unary `not`/negation print `not`/`-`. The complete binary mapping is:

| LIR operator | SMT operator | Operand and result sorts |
| --- | --- | --- |
| and, or, iff | and, or, = | Bool × Bool → Bool |
| eq, ne | =, distinct | same sort × same sort → Bool |
| add, sub, mul, div, rem | +, -, *, div, mod | Int × Int → Int |
| lt, le, gt, ge | <, <=, >, >= | Int × Int → Bool |

`ite` requires a Bool condition and equal branch sorts. A call uses its exact
canonical definition index and component, with arguments in written order.
Zero-argument applications print the bare symbol. A local let emits simultaneous
value/domain bindings: both right-hand sides use the incoming environment;
only its body sees the extended pair. This preserves outer guards, shadowing
and unused value/domain terms. Static domain questions remain separate even
when an SMT Boolean result or conditional selects no undefined value.

r[smt.encoding.interpretation]
`Interprets` gives a name-environment judgment on emitted text, separately
from LIR's slot judgment `Meaning`. Its Boolean, integer, nominal constructor,
operator, conditional, application and simultaneous-let rules are below.
The binding rule admits only paired canonical local value/domain symbols.
`VariableName` excludes literals from the variable lookup rule. `Naming`
restricts environments to ordered parameters followed by generated lexical
pairs. `EnvironmentFor` relates names to the same value/domain slots; a
literal parameter domain requires true regardless of the name map.
`Model` requires the actual retained definition equations and typed, valid results for typed
arguments. Function components are interpreted by the same `Lir.Symbols` as
OIR; this supplies equations, never a totality axiom.

Signed division/remainder are Euclidean: for nonzero d, n = q*d+r and
0 ≤ r < |d|. At zero, SMT has total integer values parameterized by the same
`Lir.ZeroValues` as OIR. Those values establish no source definedness. The
independent nonzero-domain obligation must still be justified. Interpretation
is specified only with legal sorts and declared names; arbitrary raw strings
and arbitrary ill-typed symbol environments are outside that claim.

## 3. Definitions and complete scripts

**Proof obligations**

r[smt.encoding.declarations]
`PreludeFor` begins with `(set-logic ALL)`, then one datatype declaration per
enum in retained order. `DefinitionsFor` retains every definition, including
unused ones, in a stable topological order: choose the first pending definition
whose actual value and domain terms use only already defined functions.
Structural use includes calls in arguments, both branches and all let parts.
Reject missing/cyclic dependencies; do not drop them or introduce recursive
axioms. Each definition emits value then domain `define-fun` with ordered
parameters; its result sorts are the declared value sort and Bool, respectively.
Both bodies are the actual retained terms. `DefinitionFor` states these exact
equations and their sorting; general producer conformance is a proof obligation.

r[smt.encoding.query]
`QueryFor` appends one `declare-const Pi sort` per question parameter, then
exactly `(assert search)` and `(check-sat)`. Each ordinary script includes the complete
prelude and runs in its own solver process. The optional readback operation
is specified separately below. There are no selectors, `check-sat-assuming`,
cache or incremental context.
`Encoded` binds each actual output entry to the real `prelude`/`script`
operations, including errors. Its ordered correspondence retains every
question ID, owner, request, subject, origin, parameter, context, frame,
hypothesis, dependency and readiness field, without filtering nonanswers.

The search is the original `Question.search`. An assumption Sat question
asserts the conjunction of all its hypotheses. Every other question asserts
that conjunction and the condition's negation inside its original lexical
frames. Hypotheses remain outside those frames. Definitions give the symbol
interpretation; no goal or unresolved dependency becomes a premise.
Mutually partial assumptions retain unresolved readiness even at Unsat.

## 4. Formal judgments and preservation obligations

The definitions below are compiled in this chapter's Lean wrapper. They use
actual source, OIR and LIR objects rather than a duplicate executable encoder.
`EncodingContract` requires the independent grammar/sorting/declaration
relation for every successful actual script under OIR construction.
`InterpretationContract` states two-way term interpretation under typed
assignments, corresponding environments and actual model equations.
`SearchSatisfiable` quantifies over compatible models and typed assignments;
`AnswerSound` states the solver-trust obligation separately from protocol
recognition. Neither name is an axiom or an assertion that a proof exists.

```lean
abbrev Input := FrenWalking.Program

def Produces (p : Input) (out : FrenOirToSmt.Program) : Prop := produce p = .ok out

def Rejects (p : Input) (e : InputFailure) : Prop := produce p = .error e

/-- Exact public producer envelope, including per-question translation failures. -/
def Encoded (out : FrenOirToSmt.Program) : Prop :=
  Lir.Pairs (fun q entry => entry.question = q ∧
    entry.script = (prelude out.oir >>= fun text => script out.oir text q))
    out.oir.questions.toList out.queries.toList

inductive SortFor (p : FrenOir.Program) : FrenExpr.Ty → String → Prop where
  | boolean : SortFor p .bool "Bool"
  | integer : SortFor p .int "Int"
  | nominal : p.enumerations[i]? = some e →
      SortFor p (.enum e.id) (Symbol.sort i).render

def ContextFor (ps : Array TypedParameter) (ctx : TypeContext) : Prop :=
  ctx = FrenHirToThir.parameterContext ps

/-- Written parameter order; lexical environments reverse this list. -/
def Names (count : Nat) : List (String × String) :=
  ((List.range count).map (fun i => ((Symbol.parameter i).render, "true"))).reverse

def ParametersFor (p : FrenOir.Program) (ps : Array TypedParameter) (binders : List String) : Prop :=
  Lir.Pairs (fun entry text => ∃ sort, SortFor p entry.1.type sort ∧
    text = "(" ++ (Symbol.parameter entry.2).render ++ " " ++ sort ++ ")") ps.toList.zipIdx binders

/-- Finite operator vocabulary; no source token is an SMT operator. -/
def UnaryName : UnaryOp → String
  | .not => "not" | .neg => "-"

def BinaryName : BinaryOp → String
  | .and => "and" | .or => "or" | .iff | .eq => "=" | .ne => "distinct"
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "div" | .rem => "mod"
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

/-- Concrete-text grammar judgment on the actual LIR term, without fuel.
Typing is separate: a printable string need not be a legal SMT term. -/
inductive Renders (p : FrenOir.Program) : List (String × String) → Term → String → Prop where
  | bool {b : Bool} : Renders p env (.bool b) (if b then "true" else "false")
  | int : Renders p env (.int n) (integer n)
  | constructor : p.enumerations[i]? = some e → e.id = owner → e.constructors[j]? = some (ctor, name) →
      Renders p env (.constructor owner ctor) (Symbol.constructor i j).render
  | local : env[i]? = some (v, d) →
      Renders p env (.local ty i component) (if component == .domain then d else v)
  | unary : Renders p env a text →
      Renders p env (.unary op a) (application (UnaryName op) [text])
  | binary : Renders p env a left → Renders p env b right →
      Renders p env (.binary op a b) (application (BinaryName op) [left, right])
  | ite : Renders p env c testText → Renders p env a yes → Renders p env b no →
      Renders p env (.ite c a b) (application "ite" [testText, yes, no])
  | app : p.definitions[i]? = some d → d.signature = sig →
      args.length = texts.length →
      (∀ (i : Nat) (a : Term) (text : String), args[i]? = some a → texts[i]? = some text → Renders p env a text) →
      Renders p env (.app sig component args) (application (Symbol.function i component).render texts)
  | binding : Renders p env v value → Renders p env d domain →
      Renders p (((Symbol.local env.length .value).render, (Symbol.local env.length .domain).render) :: env) b body →
      Renders p env (.letE name ty v d b)
        ("(let ((" ++ (Symbol.local env.length .value).render ++ " " ++ value ++ ") (" ++
          (Symbol.local env.length .domain).render ++ " " ++ domain ++ ")) " ++ body ++ ")")
  | at : Renders p env a text → Renders p env (.at origin a) text

def TermFor (p : FrenOir.Program) (ctx : TypeContext) (env : List (String × String))
    (t : Term) (ty : FrenExpr.Ty) (text : String) : Prop :=
  env.length = ctx.length ∧ Lir.Sorted p.lir.mir.source ctx t ty ∧ Renders p env t text

/-- Declaration equations constrain real bodies, including unused definitions.
The ordering relation uses actual structural occurrences, not supplied edges. -/
def DefinitionFor (p : FrenOir.Program) (d : FrenOir.Definition) (component : Component) (line : String) : Prop :=
  ContextFor d.signature.parameters d.body.source.context ∧ ∃ i binders sort text, p.definitions[i]? = some d ∧ ParametersFor p d.signature.parameters binders ∧
    SortFor p (if component == .domain then .bool else d.signature.result) sort ∧
    TermFor p d.body.source.context (Names d.signature.parameters.size)
      (if component == .domain then d.domain else d.value)
      (if component == .domain then .bool else d.signature.result) text ∧
    line = "(define-fun " ++ (Symbol.function i component).render ++ " (" ++
      String.intercalate " " binders ++ ") " ++ sort ++ " " ++ text ++ ")"

inductive DefinitionsFor (p : FrenOir.Program) : List FrenOir.Definition → List FrenBase.ItemId → List String → Prop where
  | nil : DefinitionsFor p [] done []
  | cons : d ∈ pending →
      (∀ id, Oir.Uses id d.value ∨ Oir.Uses id d.domain → id ∈ done) →
      (∀ earlier ∈ pending.takeWhile (fun other => other.signature.id != d.signature.id),
        ∃ id, (Oir.Uses id earlier.value ∨ Oir.Uses id earlier.domain) ∧ id ∉ done) →
      DefinitionFor p d .value value → DefinitionFor p d .domain domain →
      DefinitionsFor p (pending.filter (fun other => other.signature.id != d.signature.id))
        (done ++ [d.signature.id]) rest →
      DefinitionsFor p pending done (value :: domain :: rest)

def EnumerationFor (entry : FrenMir.Enumeration × Nat) (line : String) : Prop :=
  ¬ entry.1.constructors.isEmpty ∧ line = "(declare-datatype " ++ (Symbol.sort entry.2).render ++ " (" ++
    String.intercalate " " ((List.range entry.1.constructors.size).map
      (fun j => "(" ++ (Symbol.constructor entry.2 j).render ++ ")")) ++ "))"

def PreludeFor (p : FrenOir.Program) (text : String) : Prop :=
  ∃ enums defs, Lir.Pairs EnumerationFor p.enumerations.toList.zipIdx enums ∧
    DefinitionsFor p p.definitions.toList [] defs ∧
    text = String.intercalate "\n" ("(set-logic ALL)" :: enums ++ defs) ++ "\n"

def QueryFor (p : FrenOir.Program) (q : FrenOir.Question) (text : String) : Prop :=
  ContextFor (q.parameters.map (·.source)) q.context ∧ ∃ pre declarations formula,
    PreludeFor p pre ∧
    Lir.Pairs (fun entry line => ∃ sort, SortFor p entry.1.source.type sort ∧
      line = "(declare-const " ++ (Symbol.parameter entry.2).render ++ " " ++ sort ++ ")")
      q.parameters.toList.zipIdx declarations ∧
    TermFor p q.context (Names q.parameters.size) q.search .bool formula ∧
    text = pre ++ String.intercalate "\n" declarations ++ "\n(assert " ++ formula ++ ")\n(check-sat)\n"

/-- Environments for the text interpretation are name maps, not LIR slots. -/
abbrev Environment := String → Option FrenEval.Value

def Extend (env : Environment) (name : String) (v : FrenEval.Value) : Environment :=
  fun key => if key = name then some v else env key

def VariableName (name : String) : Prop :=
  (∃ i, name = (Symbol.parameter i).render) ∨ ∃ i component, name = (Symbol.local i component).render

inductive Naming : List (String × String) → Prop where
  | parameters : Naming (Names count)
  | binding : Naming names →
      Naming (((Symbol.local names.length .value).render, (Symbol.local names.length .domain).render) :: names)

/-- SMT interpretation of emitted concrete text. Function arguments are
positional; simultaneous let RHSs use the incoming environment. -/
inductive Interprets (p : FrenOir.Program) (symbols : Lir.Symbols) (zero : Lir.ZeroValues) :
    Environment → String → FrenEval.Value → Prop where
  | bool {b : Bool} : Interprets p symbols zero env (if b then "true" else "false") (.bool b)
  | int : Interprets p symbols zero env (integer n) (.int n)
  | constructor : p.enumerations[i]? = some e → e.constructors[j]? = some (ctor, name) →
      Interprets p symbols zero env (Symbol.constructor i j).render (.enum e.id ctor)
  | name : VariableName name → env name = some v → Interprets p symbols zero env name v
  | unary : Interprets p symbols zero env text a → FrenEval.unary op a = .ok v →
      Interprets p symbols zero env (application (UnaryName op) [text]) v
  | binary : Interprets p symbols zero env left a → Interprets p symbols zero env right b →
      Lir.Primitive zero op a b v →
      Interprets p symbols zero env (application (BinaryName op) [left, right]) v
  | yes : Interprets p symbols zero env testText (.bool true) → Interprets p symbols zero env yes v →
      Interprets p symbols zero env (application "ite" [testText, yes, no]) v
  | no : Interprets p symbols zero env testText (.bool false) → Interprets p symbols zero env no v →
      Interprets p symbols zero env (application "ite" [testText, yes, no]) v
  | app : p.definitions[i]? = some d →
      texts.length = values.length →
      (∀ (i : Nat) (text : String) (v : FrenEval.Value), texts[i]? = some text → values[i]? = some v → Interprets p symbols zero env text v) →
      Interprets p symbols zero env (application (Symbol.function i component).render texts)
        (symbols d.signature component values)
  | binding : Interprets p symbols zero env value v → Interprets p symbols zero env domain (.bool wd) →
      Interprets p symbols zero
        (Extend (Extend env (Symbol.local i .value).render v) (Symbol.local i .domain).render (.bool wd)) body result →
      Interprets p symbols zero env
        ("(let ((" ++ (Symbol.local i .value).render ++ " " ++ value ++ ") (" ++
          (Symbol.local i .domain).render ++ " " ++ domain ++ ")) " ++ body ++ ")") result

def EnvironmentFor (env : Environment) (names : List (String × String)) (slots : Lir.Slots) : Prop :=
  Lir.Pairs (fun names slot => env names.1 = some slot.1 ∧
    (if names.2 = "true" then slot.2 = true else env names.2 = some (.bool slot.2))) names slots

def Model (p : FrenOir.Program) (symbols : Lir.Symbols) (zero : Lir.ZeroValues) : Prop :=
  Oir.EquationsHold p symbols zero ∧
    ∀ d ∈ p.definitions.toList, ∀ args,
      Mir.Assignment p.lir.mir.source d.body.source.context args.reverse →
      (symbols d.signature .value args).type = d.signature.result ∧
      (symbols d.signature .value args).valid p.lir.mir.source = true ∧
      ∃ wd, symbols d.signature .domain args = .bool wd

def SearchSatisfiable (p : FrenOir.Program) (q : FrenOir.Question) : Prop :=
  ∃ symbols zero values, Model p symbols zero ∧ Oir.Assignment p q values ∧ Oir.SearchHolds symbols zero q values

/-- Solver trust, encoding adequacy and model existence are hypotheses to be
justified separately; raw protocol classification supplies none of them. -/
def AnswerSound (p : FrenOir.Program) (q : FrenOir.Question) : Outcome → Prop
  | .sat => SearchSatisfiable p q
  | .unsat => ¬ SearchSatisfiable p q
  | _ => True

def EncodingContract : Prop := ∀ p out, Produces p out → Oir.Constructs out.oir →
  ∀ entry ∈ out.queries.toList, ∀ text, entry.script = .ok text → QueryFor out.oir entry.question text

def InterpretationContract : Prop := ∀ input out, Produces input out → Oir.Constructs out.oir →
  ∀ ctx names t ty text, Naming names → TermFor out.oir ctx names t ty text → ∀ symbols zero env slots,
  Model out.oir symbols zero → Lir.Assigned out.oir.lir.mir.source ctx slots → EnvironmentFor env names slots →
  ∀ v, Lir.Meaning symbols zero slots t v ↔ Interprets out.oir symbols zero env text v

/-- Actual bounded scope/name/arity checker, without a supplied wellformed flag. -/
def ValidationContract : Prop := ∀ input out, Produces input out → ∀ ctx t ty fuel,
  Term.infer fuel out.oir.lir.mir.source ctx t = some ty → Lir.Sorted out.oir.lir.mir.source ctx t ty

/-- Source-order assignment, independently of the model response's entry order. -/
def ModelAssignment (p : FrenOir.Program) (q : FrenOir.Question)
    (values : Array FrenEval.Value) : Prop :=
  values.size = q.parameters.size ∧ ∀ (i : Nat) (param : FrenOir.Parameter) (value : FrenEval.Value),
    q.parameters[i]? = some param → values[i]? = some value →
    value.type = param.source.type ∧ value.valid p.lir.mir.source = true

/-- The strict source judgment gives the body a Boolean value under the
assignment. Assignments are positional; the judgment's environment is nearest first. -/
def SourceBoolean (p : Input) (body : TypedBody) (values : Array FrenEval.Value)
    (value : Bool) : Prop :=
  Lir.SourceValue p body values.toList.reverse (.bool value)

/-- The static traversal of the question's source body under the assignment
reaches the division or remainder that the question retains, and the strict
source judgment gives its divisor there the value zero. The assignment is then
a witness against `Mir.BodySafe` of that body. -/
def DefinednessViolation (p : Input) (q : FrenOir.Question)
    (values : Array FrenEval.Value) : Prop :=
  ∃ body origin ctx env guards left token op right,
    q.subject = some body ∧ q.origin = some origin ∧
    origin.expression = .binary left token op right ∧ (op = .div ∨ op = .rem) ∧
    Mir.StaticAt p.typed (Mir.SourceDefinition p.typed) body.context body.expression
      values.toList.reverse ctx (.binary left token op right) env guards ∧
    Mir.ValueOf p.typed (Mir.SourceDefinition p.typed) ctx right env (.int 0)

/-- Concrete candidates do not discharge universal validity or domain questions. -/
def SourceCandidate (p : Input) (out : FrenOirToSmt.Program) (q : FrenOir.Question)
    (values : Array FrenEval.Value) (answer : Confirmation) : Prop :=
  Produces p out ∧ q ∈ out.oir.questions.toList ∧ q.readiness = .ready ∧
  ModelAssignment out.oir q values ∧
  (∀ hypothesis ∈ q.hypotheses.toList, SourceBoolean p hypothesis.source values true) ∧
  ((q.kind = .assumptionsSatisfiable ∧ answer = .witness) ∨
    (q.kind = .validity ∧ answer = .counterexample ∧
      ∃ body, q.subject = some body ∧ SourceBoolean p body values false) ∨
    (q.kind ∈ [FrenOir.Kind.functionDefinedness, .assumptionDefinedness, .goalDefinedness] ∧
      answer = .counterexample ∧ DefinednessViolation p q values))

/-- Decoder typing and source-observation correspondence are separate from the
universal SMT interpretation, strict-evaluation and evaluator-adequacy bridges. -/
def ReadbackContract : Prop := ∀ p out, Produces p out → ∀ entry ∈ out.queries.toList,
  ∀ text cap values, decodeModel out.oir entry.question text cap = .ok values →
    ModelAssignment out.oir entry.question values

/-- Every confirmed answer, at every evaluation depth, is a source candidate. -/
def ConfirmationContract : Prop := ∀ p out, Produces p out → Lir.Constructs p out.oir.lir →
  Oir.Constructs out.oir → Mir.AdmissionResidue p → ∀ index entry,
  out.queries[index]? = some entry → ∀ values depth answer,
  confirmAssignment p index values depth = answer →
  (answer = .witness ∨ answer = .counterexample) →
    SourceCandidate p out entry.question values answer

/-- Discharge names actual question checks and whole-definition safety, not
caller-provided readiness flags. -/
def DependenciesDischarged (out : FrenOirToSmt.Program) (report : Report) (q : FrenOir.Question) : Prop :=
  ∀ edge ∈ q.dependencies.toList, match edge with
  | .question id => ∃ r ∈ report.checks.toList, r.question.id = id ∧ r.status = .verified ∧
      r.question.kind ∈ [FrenOir.Kind.functionDefinedness, .assumptionDefinedness, .goalDefinedness]
  | .definition id => (∃ d ∈ out.oir.definitions.toList, d.signature.id = id) ∧
      ∀ r ∈ report.checks.toList, r.question.owner = id → r.question.kind = .functionDefinedness → r.status = .verified

/-- Independent inventory, polarity and source nonvacuity requirements.
Physical process identity, solver truth and semantic bridges remain trusted. -/
def VerifiedInventory (p : Input) (report : Report) : Prop :=
  ∃ out, Produces p out ∧ report.checks.map CheckResult.question = out.oir.questions ∧
    (∃ q ∈ out.oir.questions.toList, q.kind ≠ .assumptionsSatisfiable) ∧
    ∀ q ∈ out.oir.questions.toList, q.readiness = .ready ∧ DependenciesDischarged out report q ∧
      ∃ r ∈ report.checks.toList, r.question = q ∧ r.answerRef.isSome = true ∧
        ((q.kind = .assumptionsSatisfiable ∧ r.status = .witness ∧ r.modelRef.isSome = true ∧
          ∃ values, SourceCandidate p out q values .witness) ∨
         (q.kind ≠ .assumptionsSatisfiable ∧ r.status = .verified))

def CheckerContract : Prop := ∀ p command run, Mir.AdmissionResidue p →
  (summarize p command run).verdict = .verified → VerifiedInventory p (summarize p command run)
```

General source preservation additionally consumes the named MIR, LIR and OIR
contracts and their semantic/safety domains. Source-model existence, reverse
model readback, environment freshness, full checker correspondence, evaluator
adequacy and solver trust cannot be inferred from producer determinism,
`Encoded`, finitely many examples or a raw solver status. Their exact proof
inventory belongs in the [development coverage document](../../../docs/fren2-specification-coverage.md).

## 5. Process and response boundary

**Dynamic semantics**

r[smt.response.status]
`Outcome` is Sat, Unsat, Unknown, Unsupported, ResourceExhausted or Error,
with reasons on nonanswers. `classify` first recognizes a transport resource
limit, then requires a finished process, exit zero and empty trimmed stderr.
Only then does it accept exactly one trimmed stdout token: `sat`, `unsat`,
`unknown` or `unsupported`. Missing/multiple answers, diagnostics, malformed
output, transport/setup errors and nonzero exits are errors. An output containing
`unsat` alongside failure is never a proof. Unknown stays unknown under the
configured limits. Resource exhaustion and unsupported translation are
separate nonanswers.

r[smt.response.polarity]
Sat on an assumption search is a candidate witness; Unsat is an unsatisfiable
assumption search. Sat on every refutation is a candidate counterexample;
Unsat is no counterexample to that search. `Question.interpret` gives exactly
these raw evidence constructors. None is a confirmed source assignment or an
aggregate verified-source verdict. `solve` preserves this raw boundary;
`solveModels` additionally requests typed assignments. Confirmation requires
typed source values, true active
assumptions, the correct false goal, independently justified static safety and
all actual dependencies; a solver answer supplies none of those checks.

r[smt.response.limits]
`solve` retains one result per query, including translation failures. A
successful script receives a raw `Receipt` with command arguments, optional
exit code, both decoded streams, exact captured byte hex, elapsed time,
reason and outcome. Translation failures have no process receipt. The pinned
local cvc5 command sets `--lang=smt2`, `--tlimit-per` and `--rlimit-per`.
Default wall/solver limits are 2000/1000 ms, solver resources 1000000,
combined output 65536 bytes and input 1048576 bytes. The transport requires
positive bounds, wall at most 10000 ms and each byte bound at most 1048576.
It downloads nothing. Input overflow, wall timeout, output overflow and normal cancellation retain
resource reasons. Invalid UTF-8 is an error with raw captured hex retained;
it replaces any earlier resource reason when captured bytes fail decoding.
Invalid bounds and missing assets remain errors.

The transport, in Lean with a small C binding (`FrenOirToSmt.Process`), runs
the solver in a new session and reaps its owned process after completion,
failure and cancellation. It observes exit with `waitid`/`WNOWAIT` and keeps
the direct leader waitable through the last process-group signal, then reaps
it. The unreleased PID anchors that numeric group against reuse, including on
normal completion. Loss of ownership forbids a group signal. SIGINT, SIGTERM
and SIGHUP during a query cancel it unless inherited as ignored; an ignored
signal remains ignored (a background process may inherit ignored SIGINT).
After cleanup a recorded signal takes its
usual effect on the checking process. These are process ownership guarantees
of the transport, not guarantees under the checking process's sudden death,
escaped descendants or uninterruptible execution.

## 6. Typed model readback and source observation

**Dynamic semantics**

r[smt.model.protocol]
`solveModels` retains the original admitted source witness, produced program,
question order, limits and every raw result. A raw Sat answer alone permits a
second bounded request, using the same solver argv, limits and complete
original script. `modelScript` prefixes only the model-production option and
appends `get-value` for the literal `true` followed by every `Pi` in source
parameter order. Both physical receipts and the second request are retained.
No model request is issued for Unsat or any nonanswer. The ordinary `classify`
protocol is unchanged and rejects a model envelope as an ordinary answer.
`modelData` admits only exit-zero, empty-stderr, reason-free process receipts
whose ordinary classification is an invalid answer protocol. Model parsing
then independently requires Sat and the complete value response, rejecting
stdout diagnostics.

r[smt.model.values]
`decodeModel` accepts exactly one status and one list of bindings, with one
`(true true)` sentinel and exactly one entry for each generated parameter
symbol. Input order may differ; the returned assignment follows source order.
Foreign, missing, duplicate or extra symbols are errors. Bool accepts only
`true` or `false`; Int accepts a canonical decimal magnitude or `(- magnitude)`
with positive magnitude; enum values accept only the constructor of that
parameter's retained nominal owner. No coercion, totalization or default value
is supplied. Strings, comments, diagnostics, trailing expressions, partial
responses, wrong sorts and unknown constructors are errors. The byte cap is
checked before parsing, with nesting at most eight; transport overflow,
nonzero exit, invalid UTF-8 and all other bounded failures remain unconfirmed.
`ModelAssignment` specifies the typed source-order result;
`ReadbackContract` states its correspondence to the actual decoder.

r[smt.model.confirmation]
`confirmAssignment` regenerates the program from the original admitted source
and selects its exact question index. `solveModels` applies the same source
check to decoded assignments. The answer for a question and an assignment is
one of four statuses, read against the `SourceCandidate` relation of
`r[smt.model.candidate]`:

- *witness*: the question asks whether the assumptions are satisfiable, and
  the question and the assignment are a `SourceCandidate` with the answer
  witness.
- *counterexample*: the question is a validity or definedness question, and
  the question and the assignment are a `SourceCandidate` with the answer
  counterexample.
- *rejected*: confirmation decided against the candidate. The assignment has
  the wrong arity, a wrong type or a value outside its enum; or a hypothesis
  is false; or the goal of a validity question is true; or, for a definedness
  question, an unselected branch encloses the site or the divisor is not zero.
- *unconfirmed*: confirmation decided nothing.

A rejected or unconfirmed status carries its reason.

Witness and counterexample are the confirmed answers. `r[smt.model.bridges]`
requires each of them to be a `SourceCandidate` at every evaluation depth, so
a smaller depth bound never changes what a confirmed answer means. No contract
binds a rejected answer: like an unconfirmed one, it confirms nothing, and
`r[smt.checker.verdict]` reports both as unconfirmed.

A question is unconfirmed unless it is ready, every definition that it
references exists, and every prerequisite question exists, is ready and is a
definedness question. Dependencies are not discharged by a raw Unsat token.
A definedness question is unconfirmed unless it retains a division or
remainder as its origin and asks that the divisor differ from zero. A body
that a candidate consumes may contain division anywhere; only its value at the
assignment decides. An observation that has no value by the strict judgment,
that exhausts the evaluation depth or budget, or on which the interpreter and
the strict evaluation differ is unconfirmed. No per-question confirmation is
an aggregate verified-program verdict.

The procedure that computes these statuses is not part of this rule. The
[checker guide](../../../docs/fren2-checker.md) describes it under "How a
model is confirmed".

r[smt.model.candidate]
A confirmed answer is specified through the judgments of the earlier
chapters, not through the evaluators that compute it. `SourceBoolean` holds
of a body, an assignment and a Boolean when the strict source judgment of
`r[lir.meaning.symbols]` gives the body that Boolean value under the assignment.
`DefinednessViolation` holds of a question and an assignment when the static
traversal of `r[mir.walking.partiality]`, started at the question's source
body under the assignment, reaches the division or remainder that the question
retains as its origin, and the strict source judgment gives the divisor the
value zero in the environment of that site. The traversal passes into both
operands of every operator, into every call argument and into every let value,
condition and scrutinee without evaluating them. It passes into a let body
only when the strict judgment gives the let value a value, and into a branch
only when the strict judgment gives the condition or scrutinee the value that
selects it. Such an assignment is a witness against `BodySafe` of that body:
at a site that applies statically, the divisor is zero.

`SourceCandidate` holds of a produced question, an assignment and an answer
when the question is ready, the assignment has the types of the question's
parameters, every hypothesis is `SourceBoolean` true, and one of three cases
applies:

- the question asks whether the assumptions are satisfiable, and the answer is
  a witness;
- the question is a validity question, the answer is a counterexample, and its
  goal is `SourceBoolean` false; or
- the question is a definedness question, the answer is a counterexample, and
  the assignment is a `DefinednessViolation` of it.

A term on the path to a site may have a value by runtime demand and none by
the strict judgment, for example a let value `false and (1 div x = 1)` when
`x` is zero. The traversal does not then reach the let body, so no site in
that body has a `DefinednessViolation` under that assignment, and its
candidate is unconfirmed. The division inside the let value is itself a site
that the traversal reaches, and its candidate is confirmed.

None of the three cases mentions a model of the program's definitions. A
`SourceCandidate` is a statement about the source alone.

**Proof obligations**

r[smt.model.bridges]
`ConfirmationContract` states that, for a produced program whose LIR and OIR
are constructed as their chapters specify and whose source is in the semantic
domain of `r[mir.walking.check-correspondence]`, every witness or
counterexample that `confirmAssignment` returns, at any evaluation depth, is a
`SourceCandidate` of the question at that index. `confirmed_ready` proves a
part of it that does not depend on evaluation: a confirmed answer names an
entry of the regenerated program, and the question of that entry is ready.

The rest is open. Three obligations do not depend on evaluation and are
unproved: that the question of every entry is a member of the program's
questions; that an assignment which passes the arity, type and enum checks is
a `ModelAssignment`; and that the answer is paired with the kind of the
question, a witness with a satisfiability question and a counterexample with a
validity or definedness question. Three more need inductions that have not
been done: that a value of the strict evaluator is a value of the strict
source judgment; that the interpreter's value of a well-typed, nonrecursive
body that reaches no division or remainder is such a value too; and that the
path which confirmation follows to a definedness site is a static traversal
to that site, given the first induction for each term on the path.

A `SourceCandidate` does not by itself show that the produced question has a
violation in the sense of `r[oir.meaning.search]`, which is stated in a model.
That step is open as well, and has two obligations of its own. The first is
that the hypotheses of the question are all true in every `Model`; it needs
the LIR `InterpretationContract` and a proof that the symbols of every `Model`
satisfy the LIR `Models` relation. The second is model existence: without a
`Model`, a statement about every `Model` holds vacuously and refutes nothing.
For a definedness counterexample the step also needs the frames of the
question to be active at the site that the static traversal reaches.

General decoder correspondence, model existence, solver identity/trust and
recursive source/SMT preservation require independent justification. The MIR/LIR/OIR/SMT contracts and their
semantic domains remain premises of any universal source-soundness claim.
The nonzero-transport, wrong-model-sort, retained-operand and zero-divisor laws
constrain actual functions without supplying those recursive bridges.

## 7. Source checker reports

**Dynamic semantics**

r[smt.checker.entry]
`checkSource` parses and admits source text, and `check` accepts the admitted
program witness. Both invoke the actual producer, bounded solver, typed model
readback and source confirmation themselves. Neither accepts caller outcomes,
proof flags or a selected question subset. Input failures remain explicit.
`Report` retains the complete physical `ModelRun`; each `CheckResult` retains
the original question, owner, source-token byte span, reason and references to
its answer/model receipts. A process setup exception is inconclusive.

r[smt.checker.inventory]
`summarize` is the pure consumer of retained raw runs. It regenerates the
complete inventory from its admitted source argument and requires exact source,
OIR and ordered query equality, including all IDs, owners, contexts, assumptions,
frames, definitions, dependencies, readiness and translation errors. Missing,
duplicate, reordered, skipped and foreign outcomes cannot verify a program.
Every physical receipt records its request, limits, command and a distinct
run/question/phase binding. The consumer checks those fields, reclassifies the
complete protocol and checks successful output bytes against their retained hex.
Absent, stale and conflicting receipts fail these gates. Model decoding and
source confirmation are recomputed rather than trusting stored assignments or
confirmation labels. Source evaluation uses the requested depth capped at
10000; exhaustion remains unconfirmed. The bindings detect reuse within retained evidence; they
are not cryptographic authentication of editable records.

r[smt.checker.discharge]
Unsat discharges an ordinary counterexample search, conditionally on solver
truth and encoding adequacy. Unsat for an assumption-satisfiability search
instead marks an inconsistent context. Ready means the dependency rule is
supported; it does not mean discharged. Question dependencies require verified
definedness questions. Definition dependencies require the actual equations
and every global definedness question of that definition. A finite fixed point
resolves forward edges and blocks unresolved rules, cycles and unproved edges.
Goal and goal-definedness verification additionally requires the same owner's
confirmed source nonvacuity witness with identical hypotheses. An inconsistent
owner makes those Unsat goals vacuous. Static obligations include unused
bindings/definitions, both Boolean operands and scoped conditional/binder sites;
none are filtered by runtime demand or a solver's Boolean simplification.

r[smt.checker.verdict]
A report is verified only when it contains at least one obligation other than
nonvacuity and every complete inventory row is verified or a confirmed premise
witness, with correct question polarity. A confirmed source false-goal model
reports refutation. Bare Sat, unsupported definedness-site confirmation, model
rejection and evaluator failures remain unconfirmed. Conflicting source
counterexample and owner Unsat evidence is inconclusive. Unknown, unsupported,
resource, process/protocol failures, blocked dependencies and invalid evidence
are distinct row statuses. Inconsistent contexts remain distinct from these
failures. An empty inventory or only nonvacuity searches reports no-checks.

**Proof obligations**

r[smt.checker.boundary]
`DependenciesDischarged`, `VerifiedInventory` and `CheckerContract` state
complete inventory, dependency discharge, polarity and source witness
requirements independently of the consumer implementation. The checker
contract takes the semantic domain of `r[mir.walking.check-correspondence]`
as a premise, since each witness is a `SourceCandidate`. The stale-binding,
empty-inventory and all-positive-row laws constrain actual gates and verdicts. They are not a
universal proof of the checker contract. Positive execution relies on trusted
physical transport, solver identity/truth, encoding preservation, model
existence, static-domain adequacy and source evaluation. Existing universal
MIR/LIR/OIR/SMT and model/source bridges remain unproved; concrete reports do
not require those proofs as a new admission gate.

## 8. Primitive laws and examples

**Dynamic semantics**

r[smt.primitive.euclidean] smt_primitives::facts::{negative_dividend, negative_divisor, remainder, reconstruction}
The signed division and remainder examples use Euclidean integer semantics.

r[smt.primitive.refutation] smt_primitives::facts::refutation
A counterexample requires true assumptions and a false condition.

```fren
pub mod smt_primitives

pub proc facts(assumption?, condition?, n: Int) {
    expect negative_dividend: when n = -9, n div 2 = -5
    expect negative_divisor: when n = -9, n div (-2) = 5
    expect remainder: when n = -9, n mod (-2) = 1
    expect reconstruction: (n div (-2)) * (-2) + (n mod (-2)) = n
    expect refutation: (not (when assumption?, condition?)) iff (assumption? and not condition?)
}

#fren_check
```

**Examples**

For `expect c() { expect bad: false }`, the validity search is
`(and true (not false))`. The wrapper proves its rendering, sorting and
interpretation at true, and checks its exact script against actual admitted
production. Replacing the negated false condition with false gives
`(and true false)`, whose independently proved interpretation is false.
This distinguishes a real counterexample search from its polarity mutant
without asking a solver. A separate admitted definition and later assumption
exercise actual declaration and parameter order. These witnesses establish
instances, not the universal preservation or trust obligations.

## 9. Arm selection in confirmation

Confirmation of a match selects the arm of a constructor with
`FrenHirToThir.selectArm`, the function that the evaluator also calls.
It takes the first arm written for the constructor, which is the arm of the
[dynamic semantics](../Language/DynamicSemantics.md#r-dynamics.match.selection)
when
[no arm is repeated](../Language/Patterns.md#r-patterns.matching.dynamics);
the two can disagree on a typed match whose scrutinee's constructor has a
repeated arm, and that possible disagreement is open.

r[smt.selection.arm] smt_primitives::confirmation_pick::agrees
The arm that confirmation selects for a constructor is the arm that
[`select`](../Language/Patterns.md#r-patterns.matching.select) names for it.

```fren
use spec::names::{ArmF, ItemId}
use spec::surface::Snoc
use spec::types::Typing
use spec::patterns::select

pub fn confirmation_pick(arms: Snoc<ArmF<Typing>>, constructor: ItemId): (arm: Option<ArmF<Typing>>) {
    ensure agrees: arm = select(arms, constructor)
}
```
