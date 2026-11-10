# Logical lowering (LIR)

Logical lowering represents source values as first-order terms and retains
verification information separately. A false Boolean value and an unmet
well-definedness obligation have different meanings. This chapter relates
the actual LIR to the [MIR theory](Mir.md) and shared
[expression semantics](../Language/DenotationalSemantics.md).

## 1. Semantic objects and admission

The source domain is Bool, mathematical Int, payload-free nominal enums,
nonrecursive named expression-bodied functions and global assume/expect
members. Expressions are literals, resolved names, parentheses, unary and
binary operations, calls, lets, conditionals and exhaustive constructor
matches. Function parameters are positional; lexical contexts are nearest
first. The shared [THIR judgments](Thir.md) distinguish typing, exact
occurrence inventories, match coverage and nonrecursion.

The actual `FrenLir.Program` contains its complete `mir`, ordered
`declarations` and ordered `requests`. A `Body` pairs the complete source
`TypedBody` with a `Lowered` value/verification pair. Enumerations retain
nominal constructor identities; function declarations retain signatures and
bodies; blocks retain their MIR block and ordered lowered members.

**Proof obligations**

r[lir.walking.input]
`Produces p out` means exactly `FrenFlatToLir.produce p = .ok out`, where
`p : FrenWalking.Program` carries actual admission evidence.
`Rejects p d` means exactly its error diagnostic. The producer reconstructs
MIR from that witness; it has no public unchecked theory entry. Source entry
succeeds exactly when source admission and this producer both succeed.
Admission failures propagate unchanged. Missing lexical occurrences,
references or signatures, unsupported operands, empty matches, exhausted
lowering depth and failed output checks are errors. An error is neither an
empty program nor false, validity, satisfiability or a solver unknown result.

## 2. Terms, sorts and interpretation

**Syntax**

The following constructors are the actual `FrenLir.Term` vocabulary.
`Component` is `value` or `domain`.

| Constructor | Components and meaning |
| --- | --- |
| `bool`, `int` | Boolean and mathematical integer literals |
| `constructor` | Canonical enum owner and constructor identity |
| `local` | Source type, nearest-first slot and component |
| `unary`, `binary` | Actual source operator and ordered operands |
| `ite` | Boolean condition and two alternatives |
| `app` | Complete canonical signature, component and positional arguments |
| `letE` | Binder token, type, incoming value/domain and scoped body |
| `at` | Exact source origin and enclosed term |

**Legality rules**

r[lir.terms.sorts]
`Sorted s ctx term ty` is the unbounded sort judgment below. Constructor
values name declared constructors of their exact nominal owner. A local
slot must have the recorded source type; its domain component has Bool
sort. Applications use a signature of `s` and exactly its parameter sorts
in written order. An `ite` has a Boolean condition and equal alternative
sorts. A let checks its value and Boolean domain in the incoming context,
then its body with the binder prepended. An origin's recorded context must
equal the context of its term. Equal display names or types never identify
lexical slots or canonical symbols.

`Body.wellSorted` is the production bounded checker: it checks value and
domain sorts and all origin owner/member/occurrence data, using depth 10000.
`Program.wellFormed` also checks declaration, member and request retention.

r[lir.terms.constructors] spec::lir::constructor_sort::rule
A constructor term `constructor owner c` has a sort in `s` exactly when
`enum owner c` is a valid value of `s`: `owner` is an enumeration item of
the scope, `c` is a constructor item of the scope, and the parent of `c` is
`owner`. Its sort is then `enum owner`, in every context.

```fren
pub mod spec
pub mod spec::lir

-- The implementation decides `valid?` by `FrenEval.Value.valid` on the value
-- `enum owner c`, and `sorted?` by asking the production checker
-- `FrenLir.Term.infer` whether `constructor owner c` has the sort `enum owner`.
pub proc constructor_sort(valid?): (sorted?) {
    ensure rule: sorted? iff valid?
}
```

r[lir.terms.checker]
Write `infer(n, s, Γ, t)` for the production function
`FrenLir.Term.infer n s Γ t`, whose first argument bounds the depth of the
term that it reads. The checker and the judgment agree as follows.

```text
 infer(n, s, Γ, t) = some τ
---------------------------- (sound)
       Sorted s Γ t τ

            Sorted s Γ t τ
--------------------------------------- (complete)
 ∃ n. ∀ m ≥ n. infer(m, s, Γ, t) = some τ

 Sorted s Γ t τ     Sorted s Γ t τ'
------------------------------------ (unique)
              τ = τ'

 Produces p out     Root out b     s = out.mir.source     Γ = b.source.context
------------------------------------------------------------------------------- (roots)
 Sorted s Γ b.term.value b.source.type     Sorted s Γ b.term.defined Bool
```

So `Sorted s Γ t τ` holds exactly when some depth bound makes the checker
return `τ`, and a bound that is too small makes the checker return nothing,
never another sort. Rule (roots) is the sorting half of `BodyFor` for every
root body of a successful production. It rests on `Body.wellSorted`, which
`Program.wellFormed` requires of each root at depth 10000: an output with a
root deeper than that is rejected, not accepted unsorted.

The wrapper `Spec.Compiler.Lir.Sorting` proves these rules of the production
functions themselves. `infer_sorted` is (sound), `sorted_infer` is
(complete), `sorted_iff_infer` joins them, `sorted_unique` is (unique), and
`produced_sorted` is (roots), through `wellSorted_sorted` and
`wellFormed_root`. The `impl` `constructor_sort` binds
`lir.terms.constructors`. The other cases of the judgment are recursive in
the term, and a Fren `proc` cannot yet range over `FrenLir.Term`, so those
cases are bound by the theorems and not by an `impl`.

These rules cover sorts only. The origin data that `Body.wellSorted` also
checks has no declarative rule yet. Neither a true checker result nor a
type-only source derivation proves universal semantic correspondence or
unique match coverage.

**Dynamic semantics**

r[lir.meaning.values]
`Meaning symbols zero env term value` interprets actual terms. `Slots` pairs
each nearest-first value with its domain Boolean. `Assigned` relates slots
to source tokens, types and valid nominal values. Parameters start with true
domains; a let binds its interpreted value and domain together. The let's
value/domain expressions use the incoming environment; its body uses the
extended one. Applications pass ordinary positional values to the selected
symbol component, without caller locals. `at` preserves meaning.

`Primitive` uses the actual strict mathematical primitives. Only division
and remainder by zero have values supplied by `ZeroValues`; no choice of
those values discharges a nonzero-divisor check. Integers do not overflow.
Enum identity includes both owner and constructor. `Meaning` is a relation,
with no execution fuel or proof-search timeout result.

r[lir.meaning.symbols]
`SourceValue` uses the shared MIR defined-value judgment on an actual source
body. It traverses both ordinary operands and unused let values, selecting
only explicit branches. It is distinct from the raw lazy evaluator.
`Models` constrains symbols by actual signature/body definitions and typed
positional assignments: the domain is Boolean and true exactly when the
source body has a defined value; each such value equals the value symbol.
No unproved goal supplies an equation or domain fact. Functionality is
required only for actual covered roots through `Mir.AdmissionResidue`, never
for arbitrary fabricated expressions. Typing alone does not exclude duplicate
matching arms. A concrete sufficient constant-definition model and literal
body correspondence have universal Lean proofs in the wrapper.

## 3. Lowering and retained verification

**Proof obligations**

r[lir.lowering.forms]
`Lowers s body ctx expression lowered` relates shared source expressions
to actual marked values and verification trees. Each constructor fixes its
children, their order, lexical contexts, resolved targets and output shape.
Calls retain their canonical callable and ordered arguments. A local read
retains its domain check. Parentheses retain their source origin even when
they do not change the value. A match lowers every written arm in order.
`MatchChain` tests preceding constructors and uses the final arm as fallback;
source coverage, nominal validity and uniqueness justify that fallback.
There is no fabricated default value or default domain. The relation can be
stated on raw syntax, but semantic laws restrict it to actual admitted roots
with the independent shared static premises.

r[lir.walking.demand]
`Verification` has exactly `empty`, `check`, `both`, `branch`, `letE` and
`at`. A check is a proof obligation, never an asserted hypothesis.
`Lowers` retains every written ordinary operand and unused let value.
`Holds` gives verification its scoped conjunctive meaning. The actual
`Verification.formula` summarizes this same tree as a Bool term; it neither
proves checks nor generates OIR conditions. `summary_sound` proves that
satisfied verification gives a true summary.

For every ordinary binary operator, both operands contribute verification
in the incoming context. This includes `and`, `or`, `iff`, equality and
inequality, independently of their values. Division and remainder append a
nonzero-divisor check after those two operand trees. Calls retain all
argument verification in order and then the definition-domain application.
An unused function remains a declaration with its complete verification tree.
A let first retains its value's checks outside the binder, then retains its
body under that binder with exact value/domain binding, even if unused.
A conditional retains its condition checks, then both written alternatives
under the condition and its negation. Only explicit if/match branches supply
conditional scopes. An ordinary Boolean operand cannot guard its sibling.

For example, `let x := 1 div 0 in 0` has an unmet incoming obligation;
`false and (1 div 0 = 0)` also has one. `if false then 1 div 0 else 0`
retains that written check under a false guard, so it is inactive.
The raw value evaluator may return 0 or false on the first two expressions;
that observation does not establish source well-definedness.

Local assert/assume expressions and subset syntax have no constructors in
this admitted AST or LIR. Their occurrence sets in this domain are empty;
this chapter does not silently add or erase such forms. Global assume and
expect members are real retained bodies, as specified below. An extension
admitting local assertions, assumptions or subset introduction/coercion must
retain their context-bearing checks through condition generation: prove an
introduced value's predicate, scope established parameter predicates to the
body, preserve invariant checks and do not hoist obligations globally or use
a goal to prove itself. That extension needs its own source and IR rules.

## 4. Occurrences, roots and owned requests

**Proof obligations**

r[lir.walking.retention]
`BodyFor` retains the entire typed source body and requires the lowering
and sorting judgments. `DeclarationFor`, `QuestionFor` and `RequestFor`
relate complete actual records. `Pairs` preserves ordered length and
multiplicity; `Constructs` composes these relations with `Mir.Constructs`.
This includes every unused definition, block member, label, owner, parameter,
context, occurrence, file identity, token tape and span. Exact canonical
identities and written declaration order replace neither by spelling nor by
hash-map iteration. `Root` also includes the copies retained by requests.

r[lir.walking.attribution]
`Site` addresses every retained check by its child-index path, leaf origin,
lexical context and outer-to-inner `Frame` list. It visits both children of
`both` and both alternatives of `branch` without interpreting a guard.
Index 0 precedes index 1; distinct paths remain distinct even for equal
formulas. `at` changes the current origin to that written occurrence. A
binder prepends its token/type for its body only. Every guard and binder
records its incoming context, so an outer guard cannot be reinterpreted at
an inner shadowing slot. Actual lowering marks each written value occurrence;
synthetic match tests retain their marked source children.

r[lir.walking.requests]
Each LIR request retains its entire MIR source request, all lowered
assumptions, its question and its demand roots. The MIR order is one initial
assumption-satisfiability question, then one validity question per written
expectation, for each block in declaration order. All and only that block's
assumptions apply, including later ones. A goal is never a premise for
itself or a sibling, and another block's assumptions never enter its scope.
Equal-valued written members still occupy separate positions.

`VerificationDomain` requires independently safe assumptions, every function
definition on typed assignments, and demand roots under the block's true
assumptions. It is a sufficient domain. Mutually partial assumptions do not
establish each other's safety by this rule. Once that domain is established,
`QuestionMeaning` asks for some assignment satisfying the assumptions for
Sat, or every such assignment satisfying the goal for validity. Empty
assumptions mean true. Contradictory assumptions can make validity vacuous
while Sat fails; an undefined assumption cannot be treated as false.
`RequestContract` states both the domain and question correspondence with
MIR, under the explicitly named source and symbol premises.

r[lir.walking.sharing]
There is no global reference-table constructor in this LIR. Open terms stay
under lexical lets, with their exact value/domain pairs. Sharing must
preserve both `Meaning` and the scoped verification sites, not just value
equality. A future closed-term table must be well sorted, free of lexical
slots and acyclic with references only to earlier entries. It must retain
distinct source check occurrences and must not hoist a partial operation's
obligation out of its branch. Quantifiers, closure specialization, recursive
unfolding and a shared-table schema require separate source/IR extensions.

## 5. Composing judgments and pass laws

**Proof obligations**

r[lir.contract.relations]
The following definitions are the exact compiled reference block in the
wrapper, in namespace `Spec.Compiler.Lir`. They use production datatypes,
primitive decisions and shared source judgments. `PassContract`,
`InterpretationContract` and `RequestContract` name universal obligations;
they are not axioms or assertions that those obligations have been proved.
`BodyMeaning` relates verification in both directions and values only where
verification holds, at actual typed root assignments, for every zero-value
choice. Symbol-model existence is a separate obligation from this conditional
correspondence. It cannot be inferred from an assumed functionality Boolean.

```lean
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
```

The wrapper proves exact admission/success factorization, failure exclusion,
retention and deterministic production. Its `ordinary_checks`,
`division_checks`, `remainder_checks`, `branch_checks`, `let_checks` and
`call_checks` equations concern the actual constructors. `let_value_site`,
`and_right_site`, `or_right_site` and `guarded_site` preserve static contexts
without consulting a value trace. `literal_body_for`, `literal_meaning` and
`true_definition_model` give constructive sufficient witnesses. Their scope
and the remaining universal proof obligations are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).

## 6. Verification algebra and examples

**Dynamic semantics**

r[lir.verification.algebra] spec::lir::verification_laws
For Boolean check leaves, ordinary conjunction requires both predicates;
an explicit conditional requires its condition's domain and the selected
branch's predicate; binding requires the value's predicate even when its body
ignores the value. These finite algebra laws specialize the verification
constructors. They do not replace `Lowers`, source judgments or root inventory.

```fren
pub proc verification_laws(selected?, condition_wd?, left_wd?, right_wd?, value_wd?, body_wd?) {
    expect ordinary: (left_wd? and right_wd?) iff (not (not left_wd? or not right_wd?))
    expect conditional: (condition_wd? and (if selected? then left_wd? else right_wd?)) iff (
        condition_wd? and (when selected?, left_wd?) and (when not selected?, right_wd?)
        )
    expect unused_value: when value_wd? and body_wd?, value_wd?
}

#fren_check
```

**Examples**

In `fn f(d: Int): Int := if d != 0 then 10 div d else 0`, the local
slot is `(Int, 0)`. The definition's tree retains the condition's local
domain and the division's nonzero check under the true guard. At `d = 0`
that division check is inactive. Replacing the conditional by an ordinary
`and` around a Boolean division comparison removes the branch guard and
requires the division to be defined even when the left Boolean is false.

For `expect c(x: Int) { expect g: false assume later: true }`, lowering
retains the assumption-satisfiability request and the false validity goal,
both with `later`, and keeps their independent verification roots. A true
summary for the false literal establishes definedness; it does not make the
goal true. Turning the goal into a premise would incorrectly hide the failure.
