import Fren.Impl
import Fren.Literate
import Spec.Compiler.Oir
import FrenOirToSmt
import Spec.Compiler.Thir

open Fren.Lang

#fren_md "Smt.md"

namespace Spec.Compiler.Smt
open FrenModule FrenAst FrenLir FrenOirToSmt

deriving instance DecidableEq for Outcome

-- reference begin
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
-- reference end

/-- The proved part of the confirmation contract: a confirmed answer names a
produced question that is ready. -/
theorem confirmed_ready (p : Input) (out : FrenOirToSmt.Program) (h : Produces p out)
    (index : Nat) (values : Array FrenEval.Value) (depth : Nat)
    (confirmed : confirmAssignment p index values depth = .witness ∨
      confirmAssignment p index values depth = .counterexample) :
    ∃ entry, out.queries[index]? = some entry ∧ entry.question.readiness = .ready :=
  FrenOirToSmt.confirmAssignment_ready p out h index values depth confirmed

theorem checker_stale_receipt (r : Receipt) (command : Array String) (request binding : String)
    (limits : Limits) (h : (r.binding == binding) = false) :
    receiptMatches r command request binding limits = false :=
  FrenOirToSmt.stale_receipt r command request binding limits h

theorem checker_empty : verdict #[] = .noChecks := FrenOirToSmt.empty_no_checks

theorem checker_verified_rows (rows : Array CheckResult) (h : verdict rows = .verified) :
    rows.all (fun r => r.status == .verified || r.status == .witness) = true :=
  FrenOirToSmt.verified_all rows h

theorem model_transport_nonzero (r : Receipt) (h : r.exitCode ≠ some 0) : modelData r = false :=
  FrenOirToSmt.model_nonzero r h

theorem strict_operand_retained (n : Nat) (t : Typed) (b : TypedBody) (env : FrenEval.Environment)
    (left right : Expr) (token : Token) (op : BinaryOp) (value : FrenEval.Value) (failure : String)
    (hl : strictWalk n t b env left = .ok value) (hr : strictWalk n t b env right = .error failure) :
    strictWalk (n + 1) t b env (.binary left token op right) = .error failure :=
  FrenOirToSmt.strict_operand n t b env left right token op value failure hl hr

theorem strict_division_by_zero (n : Nat) (t : Typed) (b : TypedBody) (env : FrenEval.Environment)
    (left right : Expr) (token : Token) (value : FrenEval.Value)
    (hl : strictWalk n t b env left = .ok value) (hr : strictWalk n t b env right = .ok (.int 0)) :
    (strictWalk (n + 1) t b env (.binary left token .div right)).isOk = false :=
  FrenOirToSmt.strict_div_zero n t b env left right token value hl hr

theorem strict_remainder_by_zero (n : Nat) (t : Typed) (b : TypedBody) (env : FrenEval.Environment)
    (left right : Expr) (token : Token) (value : FrenEval.Value)
    (hl : strictWalk n t b env left = .ok value) (hr : strictWalk n t b env right = .ok (.int 0)) :
    (strictWalk (n + 1) t b env (.binary left token .rem right)).isOk = false :=
  FrenOirToSmt.strict_mod_zero n t b env left right token value hl hr

theorem wrong_model_sort (p : FrenOir.Program) :
    modelValue p .bool (.list #[]) = .error "unsupported model value or wrong sort" :=
  FrenOirToSmt.wrong_bool p

theorem retains_oir (p : Input) (out : FrenOirToSmt.Program) (h : Produces p out) : Oir.Produces p out.oir :=
  FrenOirToSmt.retains_oir p out h

theorem admission (p : Input) (out : FrenOirToSmt.Program) (h : Produces p out) :
    FrenHirToThir.checkWalking p.input = .ok out.oir.lir.mir.source :=
  FrenOirToSmt.admission p out h

theorem unique (p : Input) (a b : FrenOirToSmt.Program) (ha : Produces p a) (hb : Produces p b) : a = b :=
  FrenOirToSmt.deterministic p a b ha hb

theorem retains_questions (p : Input) (out : FrenOirToSmt.Program) (h : Produces p out) :
    out.queries.map Query.question = out.oir.questions := FrenOirToSmt.retains_questions p out h

theorem exact_encoding (p : Input) (out : FrenOirToSmt.Program) (h : Produces p out) : Encoded out := by
  unfold Produces produce at h
  cases ho : FrenLirToOir.produce p with
  | error e => simp [ho, Except.mapError, Bind.bind, Except.bind] at h
  | ok oir =>
    simp only [ho, Except.mapError, Bind.bind, Except.bind] at h
    cases Except.ok.inj h
    change Lir.Pairs (fun q (entry : Query) => entry.question = q ∧
      entry.script = (prelude oir >>= fun text => script oir text q))
      oir.questions.toList (oir.questions.map (fun q => ⟨q, prelude oir >>= fun text => script oir text q⟩)).toList
    simp only [Array.toList_map]
    generalize oir.questions.toList = qs
    induction qs with
    | nil => exact .nil
    | cons q qs ih => exact .cons ⟨rfl, rfl⟩ ih

theorem failure_excludes_success (p : Input) (e : InputFailure) (h : Rejects p e) : ∀ out, ¬ Produces p out := by
  intro out success
  unfold Rejects at h
  unfold Produces at success
  rw [h] at success
  contradiction

theorem local_translation (p : FrenOir.Program) (env : List (String × String)) (i : Nat)
    (found : env[i]? = some (v, d)) (ty : FrenExpr.Ty) (component : Component) :
    term (n + 1) p env (.local ty i component) = .ok (if component == .domain then d else v) := by
  cases component <;> simp only [term, found] <;> rfl

theorem binary_translation (p : FrenOir.Program) (env : List (String × String)) (op : BinaryOp)
    (left : term n p env a = .ok x) (right : term n p env b = .ok y) :
    term (n + 1) p env (.binary op a b) = .ok (application (BinaryName op) [x, y]) := by
  cases op <;> simp only [term, left, right, Bind.bind, Except.bind] <;> rfl

theorem open_local_rejected (p : FrenOir.Program) (ty : FrenExpr.Ty) :
    term (n + 1) p [] (.local ty 0 .value) = .error (.invalid "open logical local") := rfl

theorem wrong_local_sort (s : Typed) (name : Token) :
    Term.infer (n + 1) s [(name, .int)] (.local .bool 0 .value) = none := rfl

theorem wrong_operator_sort (s : Typed) :
    Term.infer 3 s [] (.binary .add (.bool true) (.int 1)) = none := rfl

theorem translation_depth (p : FrenOir.Program) (env : List (String × String)) (t : Term) :
    term 0 p env t = .error (.resourceExhausted "SMT term translation depth") := rfl

theorem rendered_components (i : Nat) :
    (Symbol.function i .value).render ≠ (Symbol.function i .domain).render := by
  simp [Symbol.render, toString]

/-- The production component and symbol that the chapter's `Component` and `Symbol` name. -/
def component : smt_primitives.Component → Component
  | .Value => .value
  | .Domain => .domain

def symbol : smt_primitives.Symbol → Symbol
  | .Nominal i => .sort i
  | .Constructor i j => .constructor i j
  | .Function i c => .function i (component c)
  | .Parameter i => .parameter i
  | .Local i c => .local i (component c)

theorem symbol_inj {a b : smt_primitives.Symbol} : symbol a = symbol b ↔ a = b := by
  rcases a with _ | _ | ⟨_, _ | _⟩ | _ | ⟨_, _ | _⟩ <;> rcases b with _ | _ | ⟨_, _ | _⟩ | _ | ⟨_, _ | _⟩ <;>
    simp [symbol, component]

/-- No rendered name is a word whose first character is not a family letter. -/
theorem render_ne (s : Symbol) (text : String)
    (front : ∀ c rest, text.toList = c :: rest → c ∉ ['E', 'C', 'F', 'P', 'L']) : s.render ≠ text := by
  intro h
  obtain ⟨c, rest, chars, member⟩ := s.render_front
  exact front c rest (h ▸ chars) member

theorem render_ne_true (s : Symbol) : s.render ≠ "true" :=
  render_ne s "true" (by simp)

--@ reference: smt.names.rendering
open smt_primitives in
impl rendered_proof: rendered for (left right : smt_primitives.Symbol) {
  left := left, right := right, same? := (symbol left).render == (symbol right).render
} by
  intro left right _
  simp [fren_spec, symbol_inj]

--@ reference: smt.names.reserved
open smt_primitives in
impl spelled_proof: spelled for (s : smt_primitives.Symbol) (text : String) {
  symbol := s, text := text, rendered? := text == (symbol s).render
} by
  intro s text _
  simp +contextual [fren_spec, Fren.Str.lit, render_ne]

--@ reference: smt.names.binding
open smt_primitives in
impl binding_proof: binding for (count length : Nat) (bound : smt_primitives.Symbol) {
  count := count, length := length, bound := bound,
  distinct? := (symbol (.Local length .Value)).render != (symbol (.Local length .Domain)).render,
  clash? := (symbol bound).render == (symbol (.Local length .Value)).render ||
    (symbol bound).render == (symbol (.Local length .Domain)).render
} by
  intro count length bound _
  simp [fren_spec, symbol_inj]

/-- The names of an environment are those of an active scope: `count`
parameters below the locals that lets have bound, each at the index of the
environment's length when it was bound. -/
def Scoped (count : Nat) (names : List (String × String)) : Prop :=
  count ≤ names.length ∧ ∀ entry ∈ names,
    (∃ i, i < count ∧ entry = ((Symbol.parameter i).render, "true")) ∨
    ∃ i, count ≤ i ∧ i < names.length ∧
      entry = ((Symbol.local i .value).render, (Symbol.local i .domain).render)

--@ reference: smt.names.scope
theorem active_iff {count length : Nat} {s : smt_primitives.Symbol} :
    smt_primitives.active? count length s = true ↔
      (∃ i, i < count ∧ s = .Parameter i) ∨ ∃ i c, count ≤ i ∧ i < length ∧ s = .Local i c := by
  open smt_primitives.Symbol in
  cases s <;> simp [smt_primitives.active?, Nominal.x0, Constructor.x0, Constructor.x1, Function.x0, Function.x1,
    Parameter.x0, Local.x0]

--@ reference: smt.names.scope
theorem Naming.scoped (h : Naming names) : ∃ count, Scoped count names := by
  induction h with
  | @parameters count => exact ⟨count, by simp [Names], fun entry member => .inl (by simpa [Names, eq_comm] using member)⟩
  | @binding names _ ih =>
    obtain ⟨count, le, all⟩ := ih
    refine ⟨count, Nat.le_succ_of_le le, fun entry member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact .inr ⟨names.length, le, Nat.lt_succ_self _, rfl⟩
    · exact (all entry member).imp_right fun ⟨i, low, high, eq⟩ => ⟨i, low, Nat.lt_succ_of_lt high, eq⟩

--@ reference: smt.names.fresh
theorem Naming.fresh (h : Naming names) (member : entry ∈ names) (c : Component) :
    entry.1 ≠ (Symbol.local names.length c).render ∧ entry.2 ≠ (Symbol.local names.length c).render := by
  obtain ⟨count, _, all⟩ := h.scoped
  rcases all entry member with ⟨i, _, rfl⟩ | ⟨i, _, high, rfl⟩
  · exact ⟨by simp, (render_ne_true _).symm⟩
  · simp [Nat.ne_of_lt high]

/-- A correspondence survives a change of relation that agrees on the listed entries. -/
theorem pairs_congr {r r' : α → β → Prop} (h : Lir.Pairs r as bs) (agree : ∀ a ∈ as, ∀ b, r a b → r' a b) :
    Lir.Pairs r' as bs := by
  induction h with
  | nil => exact .nil
  | cons head _ ih =>
    exact .cons (agree _ List.mem_cons_self _ head) (ih fun a member => agree a (List.mem_cons_of_mem _ member))

--@ reference: smt.names.fresh
theorem active_fresh {count length : Nat} {s : smt_primitives.Symbol}
    (h : smt_primitives.active? count length s = true) (c : Component) :
    (symbol s).render ≠ (Symbol.local length c).render := by
  rcases active_iff.mp h with ⟨i, _, rfl⟩ | ⟨i, _, _, high, rfl⟩
  · simp [symbol]
  · simp [symbol, Nat.ne_of_lt high]

/-- `grind` uses the injectivity of rendering without unfolding it. -/
example (i j : Nat) (h : (Symbol.parameter i).render = (Symbol.local j .value).render) : False := by grind
example (i j : Nat) (h : (Symbol.function i .domain).render = (Symbol.function j .domain).render) : i = j := by
  grind

--@ reference: smt.names.fresh
/-- A let captures no name of its environment: every earlier entry reads the
same values after the binding as before it, and the new entry reads the bound pair. -/
theorem Naming.extend {env : Environment} (h : Naming names) (environment : EnvironmentFor env names slots) :
    EnvironmentFor
      (Extend (Extend env (Symbol.local names.length .value).render v) (Symbol.local names.length .domain).render (.bool wd))
      (((Symbol.local names.length .value).render, (Symbol.local names.length .domain).render) :: names)
      ((v, wd) :: slots) := by
  refine .cons (by simp [Extend, render_ne_true]) (pairs_congr environment fun entry member slot => ?_)
  have value := h.fresh member .value
  have domain := h.fresh member .domain
  simp [Extend, value, domain]

theorem nonzero_not_unsat (code : Int) (h : code ≠ 0) :
    classify (some code) "unsat" "" "finished" "" = .error "solver exited unsuccessfully" :=
  classify_nonzero code h

theorem multiple_answers_rejected : classify (some 0) "sat\nunsat" "" "finished" "" =
    .error "invalid solver answer protocol" := by native_decide

theorem unknown_not_proof : classify (some 0) "unknown" "" "finished" "" =
    .unknown "cvc5 returned unknown under the configured limits" := by native_decide

theorem polarity (q : FrenOir.Question) (h : q.kind ≠ .assumptionsSatisfiable) :
    q.interpret .sat = .candidateCounterexample ∧ q.interpret .unsat = .noCounterexample := by
  cases hk : q.kind <;> simp only [FrenOir.Question.interpret, hk]
  all_goals first | exact ⟨rfl, rfl⟩ | exact (h hk).elim

/-- Nonempty, independently interpreted encoding witness: the false goal's
refutation is true, irrespective of definitions or zero totalization. -/
theorem false_goal_render (p : FrenOir.Program) (origin : Origin) :
    Renders p [] (.binary .and (.bool true) (.unary .not (.at origin (.bool false)))) "(and true (not false))" :=
  .binary .bool (.unary (.at .bool))

theorem false_goal_model (p : FrenOir.Program) :
    Interprets p symbols zero (fun _ => none) "(and true (not false))" (.bool true) :=
  .binary (op := .and) (.bool (b := true)) (.unary (op := .not) (.bool (b := false)) rfl) (.ordinary rfl)

theorem false_goal_sorted (s : Typed) (origin : Origin) (context : origin.context = []) :
    Lir.Sorted s [] (.binary .and (.bool true) (.unary .not (.at origin (.bool false)))) .bool :=
  .binary .bool (.unary (.at context .bool) rfl) rfl

theorem empty_model (p : FrenOir.Program) (empty : p.definitions = #[]) :
    Model p symbols zero := by
  constructor
  · intro d member
    simp [empty] at member
  · intro d member
    simp [empty] at member

theorem false_goal_satisfiable (p : FrenOir.Program) (q : FrenOir.Question) (origin : Origin)
    (empty : p.definitions = #[]) (context : q.context = [])
    (search : q.search = .binary .and (.bool true) (.unary .not (.at origin (.bool false)))) :
    SearchSatisfiable p q := by
  refine ⟨(fun _ _ _ => .bool true), (fun _ _ => 0), [], empty_model p empty, ?_, ?_⟩
  · simp only [Oir.Assignment, Mir.Assignment, context, List.length_nil]
    refine ⟨True.intro, ?_⟩
    intro i token ty h
    simp at h
  · unfold Oir.SearchHolds
    rw [search]
    exact .binary .bool (.unary (.at .bool) rfl) (.ordinary rfl)

/-- The parameter-domain literal cannot be overridden by the name map. -/
theorem parameter_domain_total (env : Environment) (v : FrenEval.Value) :
    ¬ EnvironmentFor env [("P0", "true")] [(v, false)] := by
  intro h
  cases h with
  | cons first _ => simp at first

/-- Full script relation for the admitted no-parameter false-goal shape. -/
theorem false_goal_query (p : FrenOir.Program) (q : FrenOir.Question) (origin : Origin)
    (enums : p.enumerations = #[]) (defs : p.definitions = #[])
    (params : q.parameters = #[]) (context : q.context = []) (originContext : origin.context = [])
    (search : q.search = .binary .and (.bool true) (.unary .not (.at origin (.bool false)))) :
    QueryFor p q "(set-logic ALL)\n\n(assert (and true (not false)))\n(check-sat)\n" := by
  refine ⟨?_, ?_⟩
  · simp [ContextFor, params, context, FrenHirToThir.parameterContext]
  · refine ⟨"(set-logic ALL)\n", [], "(and true (not false))", ?_, ?_, ?_, rfl⟩
    · refine ⟨[], [], ?_, ?_, rfl⟩
      · simp only [enums, Array.toList_empty, List.zipIdx_nil]
        exact .nil
      · rw [defs]
        exact .nil
    · simp only [params, Array.toList_empty, List.zipIdx_nil]
      exact .nil
    · simp only [TermFor, params, Array.size_empty, Names, List.range_zero, List.map_nil, List.reverse_nil,
        List.length_nil, context, search]
      exact ⟨True.intro, false_goal_sorted p.lir.mir.source origin originContext, false_goal_render p origin⟩

/-- Independent negative meaning: the polarity mutant denotes false. -/
theorem flipped_goal_model (p : FrenOir.Program) :
    Interprets p symbols zero (fun _ => none) "(and true false)" (.bool false) :=
  .binary (op := .and) (.bool (b := true)) (.bool (b := false)) (.ordinary rfl)

#eval show IO Unit from do
  let source := "mod smt_contracts\nfn fixed(x: Int): Bool := true\n" ++
    "expect c(x: Int) { expect bad: false assume later: true }\n"
  let .ok admitted := FrenWalking.fromSource ⟨215⟩ source
    | throw (IO.userError "SMT witness admission failed")
  let .ok out := produce admitted | throw (IO.userError "SMT witness production failed")
  unless out.oir.definitions.size == 1 && out.queries.size == out.oir.questions.size do
    throw (IO.userError "SMT definition/question retention")
  let qs := out.queries.filter (fun q => q.question.kind == .validity)
  let #[entry] := qs | throw (IO.userError "SMT validity inventory")
  let .ok text := entry.script | throw (IO.userError "SMT witness translation failed")
  unless entry.question.context.map (·.1.text) == ["x"] && entry.question.hypotheses.size == 1 &&
      text.endsWith "\n(assert (and (and true true) (not false)))\n(check-sat)\n" &&
      text.contains "(declare-const P0 Int)" &&
      text.contains "(define-fun F0v ((P0 Int)) Bool true)" &&
      text.contains "(define-fun F0d ((P0 Int)) Bool true)" do
    throw (IO.userError "SMT independent definition/sort/assumption/polarity oracle")
  let .ok falseOut := FrenOirToSmt.fromSource ⟨215⟩ "mod false_goal\nexpect c() { expect bad: false }\n"
    | throw (IO.userError "false witness rejected")
  let #[_, q] := falseOut.queries | throw (IO.userError "false witness questions")
  let .at origin (.bool false) := q.question.condition | throw (IO.userError "false goal origin missing")
  let expected : Term := .binary .and (.bool true) (.unary .not (.at origin (.bool false)))
  unless q.question.search == expected && q.script.toOption == some "(set-logic ALL)\n\n(assert (and true (not false)))\n(check-sat)\n" do
    throw (IO.userError "proved false-goal witness differs from actual producer")
  have _render := false_goal_render falseOut.oir origin
  have _meaning := false_goal_model (symbols := fun _ _ _ => .bool true) (zero := fun _ _ => 0) falseOut.oir
  match empty : falseOut.oir.definitions.toList with
  | [] =>
    match context : q.question.context with
    | [] =>
      match search : q.question.search with
      | .binary .and (.bool true) (.unary .not (.at actualOrigin (.bool false))) =>
        have _sat : SearchSatisfiable falseOut.oir q.question :=
          false_goal_satisfiable falseOut.oir q.question actualOrigin (Array.toList_inj.mp empty) context search
        match originContext : actualOrigin.context with
        | [] =>
          have _sorted := false_goal_sorted falseOut.oir.lir.mir.source actualOrigin originContext
          match enums : falseOut.oir.enumerations.toList with
          | [] =>
            match params : q.question.parameters.toList with
            | [] =>
              have _query := false_goal_query falseOut.oir q.question actualOrigin
                (Array.toList_inj.mp enums) (Array.toList_inj.mp empty) (Array.toList_inj.mp params)
                context originContext search
              pure ()
            | _ => throw (IO.userError "parameters outside proved QueryFor witness")
          | _ => throw (IO.userError "enums outside proved QueryFor witness")
        | _ => throw (IO.userError "origin context outside proved sorting witness")
      | _ => throw (IO.userError "search outside proved model witness")
    | _ => throw (IO.userError "context outside proved model witness")
  | _ => throw (IO.userError "definitions outside proved model witness")
  let .ok pre := prelude out.oir | throw (IO.userError "prelude rejected")
  let changed := {q.question with condition := .bool true}
  unless (script falseOut.oir "(set-logic ALL)\n" changed).toOption ==
      some "(set-logic ALL)\n\n(assert (and true (not true)))\n(check-sat)\n" do
    throw (IO.userError "changed condition did not change search")
  let some definition := out.oir.definitions[0]? | throw (IO.userError "definition missing")
  let signature := definition.signature
  for args in [[], [.bool true]] do
    unless Term.infer 3 out.oir.lir.mir.source [] (.app signature .value args) == none do
      throw (IO.userError "actual signature arity/argument-sort check lost")
  unless Term.infer 3 out.oir.lir.mir.source [] (.app signature .value [.int 2]) == some .bool do
    throw (IO.userError "valid canonical call rejected")
  let .error (.invalid _) := functionName {out.oir with definitions := #[]} definition.signature .value
    | throw (IO.userError "missing canonical signature printed")
  let .error (.invalid _) := enumIndex out.oir entry.question.owner
    | throw (IO.userError "missing nominal owner printed")
  unless Term.infer 3 out.oir.lir.mir.source [] (.binary .add (.bool true) (.int 1)) == none &&
      (term 3 out.oir [] (.binary .add (.bool true) (.int 1))).isOk do
    throw (IO.userError "low-level printer/admission boundary changed")
  let .ok nominal := FrenOirToSmt.fromSource ⟨215⟩
      "mod nominal\nenum A { One }\nenum B { One }\nexpect c(a: A, b: B) { expect good: a = A::One }\n"
    | throw (IO.userError "nominal witness admission failed")
  let #[first, second] := nominal.oir.enumerations | throw (IO.userError "nominal inventory")
  let some (ctor, _) := first.constructors[0]? | throw (IO.userError "nominal constructor missing")
  unless Term.infer 2 nominal.oir.lir.mir.source [] (.constructor first.id ctor) == some (.enum first.id) &&
      Term.infer 2 nominal.oir.lir.mir.source [] (.constructor second.id ctor) == none &&
      (term 2 nominal.oir [] (.constructor second.id ctor)).isOk == false do
    throw (IO.userError "cross-owner constructor confused with same spelling")
  unless pre.startsWith "(set-logic ALL)\n" do throw (IO.userError "logic prefix missing")
  IO.println "SMT contracts: admitted false-goal encoding with independent Renders/Sorted/Interprets proofs; retained real definition and later assumption; exact sort/polarity/declaration oracle; wrong operator and missing canonical references distinguished from raw printing. No solver run or source-model confirmation."

#print axioms confirmed_ready
#print axioms model_transport_nonzero
#print axioms strict_operand_retained
#print axioms strict_division_by_zero
#print axioms strict_remainder_by_zero
#print axioms wrong_model_sort
#print axioms exact_encoding
#print axioms local_translation
#print axioms binary_translation
#print axioms wrong_local_sort
#print axioms rendered_components
#print axioms nonzero_not_unsat
#print axioms multiple_answers_rejected
#print axioms unknown_not_proof
#print axioms false_goal_render
#print axioms false_goal_model
#print axioms empty_model
#print axioms false_goal_satisfiable
#print axioms false_goal_query
#print axioms parameter_domain_total
#print axioms flipped_goal_model
#print axioms symbol_inj
#print axioms render_ne
#print axioms active_iff
#print axioms active_fresh
#print axioms Naming.scoped
#print axioms Naming.fresh
#print axioms Naming.extend

open smt_primitives in
interp confirmation_pick := fun arms c => Spec.Compiler.Thir.pickArm arms c by
  intro arms constructor
  simp only [smt_primitives.confirmation_pick.agrees]
  exact Spec.Compiler.Thir.pickArm_eq_select arms constructor

end Spec.Compiler.Smt
