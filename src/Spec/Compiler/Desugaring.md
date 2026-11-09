# Desugaring

Desugaring relates a typed source program to the typed core program consumed
by [MIR construction](Mir.md). This chapter's source domain is the
[Language core](../Language/Types.md): Bool, Int, payload-free nominal enums,
nonrecursive named functions, checks, literals, names, parentheses, operators,
calls, if, let and constructor matches. Those forms already are core forms.
The transformation on this domain is identity on the complete typed program.

## Semantic objects and judgments

The input and output carrier is the actual `FrenThirDesugar.Program`:
`input : FrenModule.Resolved`, `typed : FrenModule.Typed` and evidence
`checkWalking input = .ok typed`. `Typed` retains the resolved document,
signatures and ordered typed bodies. Each body retains its canonical owner,
optional complete assumption/expectation member, expression, nearest-first
parameter context, type and ordered occurrence data. Each occurrence retains
its expression, exact binder-token/type context and value or callable type.
The resolved document retains syntax, token tape and source spans; references
retain canonical targets, roles and the lexical contexts of written names.
Equality below is equality of these actual records, including origins.

`Desugars p q` is the specified core relation. `Produces r q` is the graph
of the actual admission entrypoint; `Rejects r d` states its exact rejected
resolved input and static failure. These judgments distinguish a transformation
of an admitted program from an attempt to admit raw resolved data.

**Proof obligations**

r[desugaring.walking.input]
A program must carry actual producer evidence. A caller-supplied `Typed`,
occurrence table or validation Boolean does not establish admission.
For resolved input `r`, a successful result with typed data `t` exists exactly
when the actual type checker produces `t` and both coverage and non-recursion
validators accept it. This is `admission_domain` in the chapter wrapper.

r[desugaring.walking.identity]
`Desugars p q` holds exactly when `q = p`. For every admitted input, the actual
`desugar` implements this relation, is total and deterministic, and preserves
all retained data and their order. It cannot delete an unused function,
operand, let definition or check member, nor change a member's kind or label.
No new source origin, canonical identity or local context is invented.

r[desugaring.walking.boundary]
`fromResolved r = .ok q` holds exactly when `q.input = r` and
`checkWalking r = .ok q.typed`. Its error result is exactly `Rejects r d`,
with the same failure payload. Type errors, coverage errors and recursive-call
errors remain distinct. `fromSource` first parses and resolves; it maps a
parse error to the typing diagnostic with detail `expected ` followed by the
parser's expected text and the same span, maps a resolver diagnostic to a
typing failure unchanged, then uses `fromResolved`. No rejected input becomes
a desugared success. `source_projection` proves equality of its typed/error
projection with `checkWalkingSource`. The grammar excludes ensure, where,
unless, unnamed match parameters, lambda matches and tables; this relation
supplies no rule admitting any of them.

## Static contexts and source obligations

The shared [THIR judgments](Thir.md#shared-judgments-and-pass-interface)
`BodyInventory`, `BodyTyping`, `OccurrenceTyping`, `MatchCoverage` and
`Nonrecursive` refer to actual syntax and contexts. `StaticPreservation`
transports each judgment in both directions. In particular, transferring a
typing judgment does not assert that the type checker satisfies it on all
inputs. Admission includes the actual validators; their recursive semantic
correspondence is a separate contract.

`Guard` records an if condition and polarity, or a match scrutinee and written
constructor pattern, together with the context in which that subject is read.
The pattern's target comes from the retained resolved input. A guard is a
scoped hypothesis, not evidence that the condition holds or is defined.
`ScopedChild` and `ScopedAt` define the structural traversal of source
obligations. Their context projection is the shared `ChildContext` and
`AtContext`; `scoped_child_context` and `scoped_at_context` prove this direction.

r[desugaring.walking.static]
The output retains actual type-production, coverage and non-recursion
validation evidence. All shared static judgments hold of the output exactly
when they hold of the input. Every written child participates in obligation
traversal. Ordinary Boolean operands add no guard. An unused let definition
uses the incoming context; only its body extends that context. An if condition
and match scrutinee use the incoming guards; each branch or arm adds only its
explicit guard. Existing guards keep their original lexical contexts across
later binders. All named definitions and check members remain roots.

r[desugaring.contract.obligations]
`DomainSite` identifies each written division/remainder obligation by its full
body, lexical context, ordered guard path, operands, operator token and kind.
The required integer domain is nonzero divisor, as defined by
[expression domains](../Language/Expressions.md#definedness-and-source-verification).
`ObligationPreservation` preserves these sites in both directions by exact
identity. It also preserves the ordered assumption and expectation arrays for
each canonical owner, including full member data. All of a block's assumptions
remain available to its expectations, regardless of written position; no
assumption becomes a goal or a global unconditional fact. Retaining an
obligation does not prove its domain or its hypotheses. This relation does not
settle dependencies among mutually partial assumptions or assign solver
verdicts. Empty blocks and declarations are retained by `Retains`, even when
neither member array nor a domain site mentions them.

The following definitions are compiled verbatim in the
[chapter wrapper](Desugaring.lean); they use production IR and the shared THIR
judgments, without an alternative executable compiler.

```lean
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
```

## Interpretation preservation

**Proof obligations**

r[desugaring.walking.evaluation]
`InterpretationPreservation` equates the actual `FrenEval.evaluate` result for
every request, argument array and operational depth. Equality includes the
selected complete body and outcome; invalid requests, invalid arguments,
undefined operations, exhaustion and unsupported cases retain their failure
kind and payload. No argument-validity premise discards the negative domain.
Default depth is also unchanged because its complete input is unchanged.
Exhaustion remains an operational outcome, distinct from semantic undefinedness.

`pass_contract` proves retention, static transfer, interpreter correspondence
and source-obligation-site preservation for the specified identity relation.
`desugar_iff` binds that relation to the actual production API. The more general
`observation` law transfers any interpretation or predicate of the full retained
resolved/typed pair: once a declarative interpretation is defined, identity
preserves it without replacing its semantics with an evaluator trace. Neither
this law nor concrete evaluation establishes universal source verification.
An interpreter may skip an ordinary Boolean operand or ignore an unused let's
failure; its demand trace does not remove the site's static obligation.

A transformation admitting additional sugar must define each form using its
Language semantics, relate the complete input/output IR, preserve typing in
the exact contexts, and establish value and scoped-obligation correspondence.
A table expansion must retain table kind and disjointness obligations when
translated to a match. The identity relation above applies only to the stated
core domain and provides no correspondence theorem for such expansions.

## Example

The constructor targets, operands and source origins in this program are
retained exactly. `bounded` stays an assumption in `waits`; `at_most` stays
its expectation. Both match arms remain written bodies, independently of
which arm a particular execution selects.

```fren
pub mod desugar_example

pub enum Light { Red, Green }

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => base + 30,
    Light::Green => base,
}

expect waits(l: Light, base: Int) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}

#fren_check
```

For a partial expression, `if d != 0 then 1 div d else 0` has a division site
under the positive condition guard. `false and (1 div 0 = 0)` has an unguarded
division site, as does the value in `let x := 1 div 0 in 3`. Identity retains
all three sites even if a particular execution returns a value. These cases
separate interpretation from obligation preservation.

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
