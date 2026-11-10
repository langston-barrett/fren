import Fren.Impl
import Fren.Literate
import Fren.Trace
import FrenWalking
import FrenBase.Binding
import FrenExpr
import Spec.Language.Types
import Spec.Language.Patterns
import FrenHirToThir.Coverage
import Spec.Language.StaticSemantics
import FrenHirToThir.Termination

open Fren.Lang

#fren_md "Thir.md"

#fren_check

namespace Spec.Compiler.Thir

/-- Same concrete successful-producer relation established by actual admission.
The public Resolved structure alone remains insufficient evidence. -/
def Admitted (input : FrenModule.Resolved) : Prop :=
  FrenHirToThir.Admitted input

/-- Nominal key equality uses the real canonical API, not a display string. -/
theorem nominal_key (a b : FrenBase.ItemId) : (a == b) = true ↔ a = b :=
  FrenBase.ItemId.beq_eq_true_iff a b

#check FrenHirToThir.check_retains
#check FrenHirToThir.erasure
#check FrenHirToThir.deterministic
#check FrenHirToThir.TypingSound
#check FrenHirToThir.validateWalking_iff
#check FrenHirToThir.walking_success
#check FrenHirToThir.walking_failure_iff
#check FrenHirToThir.walking_retains
#check FrenHirToThir.walking_deterministic

-- reference begin
/-- Immediate written children and their exact lexical type contexts. -/
inductive ChildContext (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr → FrenModule.TypeContext → FrenAst.Expr → Prop where
  | paren : ChildContext r sigs ctx (.paren o e c) ctx e
  | unary : ChildContext r sigs ctx (.unary tok op e) ctx e
  | binaryLeft : ChildContext r sigs ctx (.binary a tok op b) ctx a
  | binaryRight : ChildContext r sigs ctx (.binary a tok op b) ctx b
  | callee : ChildContext r sigs ctx (.call f o args commas c) ctx f
  | argument : e ∈ args.toList → ChildContext r sigs ctx (.call f o args commas c) ctx e
  | condition : ChildContext r sigs ctx (.ifE i b t yes e no) ctx b
  | thenBranch : ChildContext r sigs ctx (.ifE i b t yes e no) ctx yes
  | elseBranch : ChildContext r sigs ctx (.ifE i b t yes e no) ctx no
  | letValue : ChildContext r sigs ctx (.letE l name assign value i body) ctx value
  | letBody : FrenHirToThir.HasValue r sigs ctx value vt →
      ChildContext r sigs ctx (.letE l name assign value i body) ((name, vt) :: ctx) body
  | scrutinee : ChildContext r sigs ctx (.matchE m scrutinee o arms c) ctx scrutinee
  | armBody : arm ∈ arms.toList →
      ChildContext r sigs ctx (.matchE m scrutinee o arms c) ctx arm.2.2.1

/-- Reflexive structural closure, with context changes carried at every step. -/
inductive AtContext (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr → FrenModule.TypeContext → FrenAst.Expr → Prop where
  | root : AtContext r sigs ctx e ctx e
  | child : AtContext r sigs rootCtx root ctx parent →
      ChildContext r sigs ctx parent childCtx childExpr →
      AtContext r sigs rootCtx root childCtx childExpr

/-- The actual successful type-only producer, rather than a supplied verdict. -/
def Produces (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  FrenHirToThir.check input = .ok out

/-- The recursive body judgment is over the retained production AST. -/
def BodyTyping (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList,
    FrenHirToThir.HasValue input out.signatures body.context body.expression body.type

/-- Callable meaning propagates through retained callee parentheses. -/
inductive HasCallable (input : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr → FrenModule.Signature → Prop where
  | name : FrenHirToThir.Selects input ctx path .expression (.item sig.id) →
      FrenHirToThir.signatureAt sigs sig.id = some sig →
      HasCallable input sigs ctx (.name path) sig
  | paren : HasCallable input sigs ctx e sig →
      HasCallable input sigs ctx (.paren o e c) sig

def OccurrenceMeaning (input : FrenModule.Resolved) (sigs : Array FrenModule.Signature)
    (occurrence : FrenModule.TypedOccurrence) : Prop :=
  match occurrence.type with
  | .value ty => FrenHirToThir.HasValue input sigs occurrence.context occurrence.expression ty
  | .callable sig => HasCallable input sigs occurrence.context occurrence.expression sig

/-- Ordered immediate children. Pattern paths and binder tokens are not expressions. -/
inductive WrittenChildren (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenModule.TypeContext → FrenAst.Expr →
      List (FrenModule.TypeContext × FrenAst.Expr) → Prop where
  | bool : WrittenChildren r sigs ctx (.bool t b) []
  | integer : WrittenChildren r sigs ctx (.integer t n) []
  | name : WrittenChildren r sigs ctx (.name p) []
  | paren : WrittenChildren r sigs ctx (.paren o e c) [(ctx, e)]
  | unary : WrittenChildren r sigs ctx (.unary t op e) [(ctx, e)]
  | binary : WrittenChildren r sigs ctx (.binary a t op b) [(ctx, a), (ctx, b)]
  | call : WrittenChildren r sigs ctx (.call f o args commas c)
      ((ctx, f) :: args.toList.map (ctx, ·))
  | ifE : WrittenChildren r sigs ctx (.ifE i b t yes e no)
      [(ctx, b), (ctx, yes), (ctx, no)]
  | letE : FrenHirToThir.HasValue r sigs ctx value vt →
      WrittenChildren r sigs ctx (.letE l name assign value i body)
        [(ctx, value), ((name, vt) :: ctx, body)]
  | matchE : WrittenChildren r sigs ctx (.matchE m scrutinee o arms c)
      ((ctx, scrutinee) :: arms.toList.map (fun arm => (ctx, arm.2.2.1)))

mutual
  /-- One entry per structural visit, after all ordered child entries. No key deduplication. -/
  inductive OccurrenceOrder (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
      FrenModule.TypeContext → FrenAst.Expr → List FrenModule.TypedOccurrence → Prop where
    | node : WrittenChildren r sigs ctx expr children →
        OccurrenceForest r sigs children nodes →
        OccurrenceOrder r sigs ctx expr (nodes ++ [⟨expr, ctx, ty⟩])

  /-- Child subtrees concatenate in written order, retaining their multiplicities. -/
  inductive OccurrenceForest (r : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
      List (FrenModule.TypeContext × FrenAst.Expr) → List FrenModule.TypedOccurrence → Prop where
    | nil : OccurrenceForest r sigs [] []
    | cons : OccurrenceOrder r sigs ctx expr first →
        OccurrenceForest r sigs rest remaining →
        OccurrenceForest r sigs ((ctx, expr) :: rest) (first ++ remaining)
end

/-- Exact per-body source inventory, including multiplicity and postorder. -/
def OccurrenceInventory (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList,
    OccurrenceOrder input out.signatures body.context body.expression body.occurrences.toList

/-- Both source-to-output coverage and soundness of every output entry. -/
def OccurrenceTyping (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  (∀ body ∈ out.bodies.toList, ∀ ctx expr,
    AtContext input out.signatures body.context body.expression ctx expr →
    ∃ occurrence ∈ body.occurrences.toList,
      occurrence.expression = expr ∧ occurrence.context = ctx ∧
      OccurrenceMeaning input out.signatures occurrence) ∧
  (∀ body ∈ out.bodies.toList, ∀ occurrence ∈ body.occurrences.toList,
    AtContext input out.signatures body.context body.expression
      occurrence.context occurrence.expression ∧
    OccurrenceMeaning input out.signatures occurrence)

/-- Every call written in a body has a name as its callee. `HasValue` types no
other call, so `OccurrenceTyping` implies this. -/
def NamedCallees (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList, ∀ ctx callee o args commas c,
    AtContext input out.signatures body.context body.expression ctx
      (.call callee o args commas c) →
    ∃ path, callee = .name path

/-- Source declarations determine body owner, result type and parameter context. -/
inductive DeclaresBody (input : FrenModule.Resolved) (sigs : Array FrenModule.Signature) :
    FrenBase.ItemId → Option FrenAst.Member → FrenAst.Expr →
      FrenModule.TypeContext → FrenExpr.Ty → Prop where
  | function : input.document.root = .declarations decls →
      FrenAst.Decl.function vis keyword name params colon result assign expr ∈ decls.toList →
      FrenHirToThir.signatureAt sigs (input.scope.id.named name.text) = some sig →
      DeclaresBody input sigs sig.id none expr
        (FrenHirToThir.parameterContext sig.parameters) sig.result
  | member : input.document.root = .declarations decls →
      FrenAst.Decl.expectation keyword name params openTok members closeTok ∈ decls.toList →
      member ∈ members.toList → FrenHirToThir.parameters input params = .ok typedParams →
      DeclaresBody input sigs (input.scope.id.named name.text) (some member) member.body
        (FrenHirToThir.parameterContext typedParams) .bool

def BodyEntry (body : FrenModule.TypedBody) (owner : FrenBase.ItemId)
    (member : Option FrenAst.Member) (expr : FrenAst.Expr)
    (ctx : FrenModule.TypeContext) (ty : FrenExpr.Ty) : Prop :=
  body.owner = owner ∧ body.member = member ∧ body.expression = expr ∧
    body.context = ctx ∧ body.type = ty

/-- Every source body occurs once, including unused functions and every member. -/
def BodyInventory (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  (∀ body ∈ out.bodies.toList,
    DeclaresBody input out.signatures body.owner body.member body.expression body.context body.type) ∧
  (∀ owner member expr ctx ty, DeclaresBody input out.signatures owner member expr ctx ty →
    ∃ i : Fin out.bodies.size, BodyEntry out.bodies[i] owner member expr ctx ty ∧
      ∀ j : Fin out.bodies.size, BodyEntry out.bodies[j] owner member expr ctx ty → j = i)

def TypePassContract : Prop := ∀ input out, Produces input out →
  FrenHirToThir.Admitted input ∧ out.resolved = input ∧
    FrenHirToThir.signatures input = .ok out.signatures ∧
    BodyInventory input out ∧ BodyTyping input out ∧
    OccurrenceInventory input out ∧ OccurrenceTyping input out

/-- Coverage quantifies over actual AST descendants, not just a supplied table. -/
def MatchCoverage (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList, ∀ ctx m scrutinee o arms c,
    AtContext input out.signatures body.context body.expression ctx
      (.matchE m scrutinee o arms c) →
    ∃ owner, FrenHirToThir.HasValue input out.signatures ctx scrutinee (.enum owner) ∧
      (∀ item ∈ input.scope.items.toList,
        item.kind = .constructor → item.id.parent = some owner →
        ∃ j : Fin arms.size,
          FrenHirToThir.Selects input ctx arms[j].1 .pattern (.item item.id) ∧
          ∀ k : Fin arms.size,
            FrenHirToThir.Selects input ctx arms[k].1 .pattern (.item item.id) → k = j) ∧
      (∀ arm ∈ arms.toList, ∃ item ∈ input.scope.items.toList,
        item.kind = .constructor ∧ item.id.parent = some owner ∧
        FrenHirToThir.Selects input ctx arm.1 .pattern (.item item.id))

def Calls (input : FrenModule.Resolved) (out : FrenModule.Typed)
    (caller callee : FrenBase.ItemId) : Prop :=
  ∃ body ∈ out.bodies.toList, body.owner = caller ∧ body.member = none ∧
    ∃ ctx path o args commas c,
      AtContext input out.signatures body.context body.expression ctx
        (.call (.name path) o args commas c) ∧
      FrenHirToThir.Selects input ctx path .expression (.item callee)

inductive CallPath (edge : FrenBase.ItemId → FrenBase.ItemId → Prop) :
    FrenBase.ItemId → FrenBase.ItemId → Prop where
  | one : edge a b → CallPath edge a b
  | more : edge a b → CallPath edge b c → CallPath edge a c

def Nonrecursive (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ item, ¬ CallPath (Calls input out) item item

/-- These are correspondence obligations, not aliases for validator success. -/
def CoverageContract : Prop := ∀ input out, Produces input out →
  (FrenHirToThir.WalkingCoverage out ↔ MatchCoverage input out)

def NonrecursionContract : Prop := ∀ input out, Produces input out →
  (FrenHirToThir.WalkingNonrecursive out ↔ Nonrecursive input out)
-- reference end

/-- Admission and erasure are proved independently of recursive soundness. -/
theorem produced_retains (input : FrenModule.Resolved) (out : FrenModule.Typed)
    (h : Produces input out) : FrenHirToThir.Admitted input ∧ out.resolved = input :=
  ⟨(FrenHirToThir.check_retains input out h).2,
    (FrenHirToThir.check_retains input out h).1⟩

theorem produced_unique (input : FrenModule.Resolved) (a b : FrenModule.Typed)
    (ha : Produces input a) (hb : Produces input b) : a = b :=
  FrenHirToThir.deterministic input a b ha hb

theorem failed_not_produced (input : FrenModule.Resolved) (d : FrenDiag.Diagnostic)
    (h : FrenHirToThir.check input = .error d) : ∀ out, ¬ Produces input out := by
  intro out success
  change FrenHirToThir.check input = .ok out at success
  rw [h] at success
  contradiction

theorem static_factorization (input : FrenModule.Resolved) (out : FrenModule.Typed) :
    FrenHirToThir.checkWalking input = .ok out ↔
      Produces input out ∧ FrenHirToThir.WalkingCoverage out ∧
        FrenHirToThir.WalkingNonrecursive out :=
  FrenHirToThir.walking_success input out

theorem body_contract_iff : (∀ input out, Produces input out → BodyTyping input out) ↔
    FrenHirToThir.TypingSound := Iff.rfl

/-- The root is last, independently of how its descendants are typed. -/
theorem order_root_last (h : OccurrenceOrder r sigs ctx expr nodes) :
    ∃ children ty, nodes = children ++ [⟨expr, ctx, ty⟩] := by
  cases h
  exact ⟨_, _, rfl⟩

theorem order_integer_iff :
    OccurrenceOrder r sigs ctx (.integer token n) nodes ↔
      ∃ ty, nodes = [⟨.integer token n, ctx, ty⟩] := by
  constructor
  · intro h
    cases h with
    | node children forest =>
      cases children
      cases forest
      exact ⟨_, rfl⟩
  · rintro ⟨ty, rfl⟩
    exact .node .integer .nil

/-- A structural law for all literal operands, tokens, contexts and inputs. -/
theorem order_integer_add_iff :
    OccurrenceOrder r sigs ctx (.binary (.integer a x) op .add (.integer b y)) nodes ↔
      ∃ lt rt ty, nodes = [⟨.integer a x, ctx, lt⟩, ⟨.integer b y, ctx, rt⟩,
        ⟨.binary (.integer a x) op .add (.integer b y), ctx, ty⟩] := by
  constructor
  · intro h
    cases h with
    | node children forest =>
      cases children
      cases forest with
      | cons left rest =>
        cases rest with
        | cons right rest =>
          cases rest
          obtain ⟨lt, hl⟩ := order_integer_iff.mp left
          obtain ⟨rt, hr⟩ := order_integer_iff.mp right
          subst hl; subst hr
          exact ⟨lt, rt, _, rfl⟩
  · rintro ⟨lt, rt, ty, rfl⟩
    exact .node .binary (.cons (.node .integer .nil)
      (.cons (.node .integer .nil) .nil))

theorem meaning_integer_iff :
    OccurrenceMeaning r sigs ⟨.integer token n, ctx, ty⟩ ↔ ty = .value .int := by
  cases ty with
  | value value =>
    constructor
    · intro h
      cases h
      rfl
    · intro h
      cases h
      exact FrenHirToThir.HasValue.integer
  | callable sig =>
    constructor
    · intro h
      cases h
    · intro h
      cases h

theorem meaning_integer_add_iff :
    OccurrenceMeaning r sigs
      ⟨.binary (.integer a x) op .add (.integer b y), ctx, ty⟩ ↔ ty = .value .int := by
  cases ty with
  | value value =>
    constructor
    · intro h
      cases h with
      | binary left right result =>
        cases left
        cases right
        cases result
        rfl
    · intro h
      cases h
      exact FrenHirToThir.HasValue.binary .integer .integer rfl
  | callable sig =>
    constructor
    · intro h
      cases h
    · intro h
      cases h

/-- This exact primitive table law follows from the structural and semantic relations. -/
theorem integer_add_table_iff :
    (OccurrenceOrder r sigs ctx (.binary (.integer a x) op .add (.integer b y)) nodes ∧
      ∀ occurrence ∈ nodes, OccurrenceMeaning r sigs occurrence) ↔
    nodes = [⟨.integer a x, ctx, .value .int⟩, ⟨.integer b y, ctx, .value .int⟩,
      ⟨.binary (.integer a x) op .add (.integer b y), ctx, .value .int⟩] := by
  constructor
  · rintro ⟨order, sound⟩
    obtain ⟨lt, rt, ty, rfl⟩ := order_integer_add_iff.mp order
    have hl := meaning_integer_iff.mp (sound ⟨.integer a x, ctx, lt⟩ (by simp))
    have hr := meaning_integer_iff.mp (sound ⟨.integer b y, ctx, rt⟩ (by simp))
    have ht := meaning_integer_add_iff.mp (sound ⟨.binary (.integer a x) op .add (.integer b y), ctx, ty⟩ (by simp))
    subst lt; subst rt; subst ty
    rfl
  · intro h
    subst nodes
    constructor
    · exact order_integer_add_iff.mpr ⟨_, _, _, rfl⟩
    · intro occurrence member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact meaning_integer_iff.mpr rfl
      · exact meaning_integer_iff.mpr rfl
      · exact meaning_integer_add_iff.mpr rfl

/-- Actual inference admits the exact table for every integer addition leaf pair. -/
theorem infer_integer_add (fuel : Nat) (r : FrenModule.Resolved)
    (sigs : Array FrenModule.Signature) (ctx : FrenModule.TypeContext)
    (a op b : FrenAst.Token) (x y : Nat) :
    FrenHirToThir.infer (fuel + 2) r sigs ctx
      (.binary (.integer a x) op .add (.integer b y)) false =
      .ok ⟨.value .int, #[⟨.integer a x, ctx, .value .int⟩,
        ⟨.integer b y, ctx, .value .int⟩,
        ⟨.binary (.integer a x) op .add (.integer b y), ctx, .value .int⟩]⟩ := by
  rfl

/-- A genuine producer result satisfies both relations in this primitive case. -/
theorem inferred_integer_add_contract
    (h : FrenHirToThir.infer (fuel + 2) r sigs ctx
      (.binary (.integer a x) op .add (.integer b y)) false = .ok result) :
    OccurrenceOrder r sigs ctx (.binary (.integer a x) op .add (.integer b y))
      result.occurrences.toList ∧
    ∀ occurrence ∈ result.occurrences.toList, OccurrenceMeaning r sigs occurrence := by
  rw [infer_integer_add] at h
  cases Except.ok.inj h
  exact integer_add_table_iff.mpr rfl

/-- A decidable projection of the contract, used on raw production outputs below. -/
private def occurrenceView (o : FrenModule.TypedOccurrence) :=
  (o.expression.tokens, o.context, match o.type with
    | .value ty => some ty
    | .callable _ => none)

private def integerAddView (body : FrenModule.TypedBody) : Bool :=
  match body.expression with
  | .binary (.integer a x) _op .add (.integer b y) =>
    decide (body.occurrences.toList.map occurrenceView =
      ([⟨.integer a x, body.context, .value .int⟩,
        ⟨.integer b y, body.context, .value .int⟩,
        ⟨body.expression, body.context, .value .int⟩] : List FrenModule.TypedOccurrence).map
          occurrenceView)
  | _ => false

/-- Rejection by this projection refutes the full occurrence contract for this body. -/
private theorem integer_add_view_required
    (shape : body.expression = .binary (.integer a x) op .add (.integer b y))
    (order : OccurrenceOrder r sigs body.context body.expression body.occurrences.toList)
    (sound : ∀ occurrence ∈ body.occurrences.toList, OccurrenceMeaning r sigs occurrence) :
    integerAddView body = true := by
  have exactTable := integer_add_table_iff.mp ⟨shape ▸ order, sound⟩
  simp [integerAddView, shape, exactTable]

/-- The whole output contract entails the tested projection for every such body. -/
private theorem output_integer_add_view_required
    (inventory : OccurrenceInventory input out) (typing : OccurrenceTyping input out)
    (member : body ∈ out.bodies.toList)
    (shape : body.expression = .binary (.integer a x) op .add (.integer b y)) :
    integerAddView body = true := by
  exact integer_add_view_required shape (inventory body member)
    (fun occurrence present => (typing.2 body member occurrence present).2)

/-- The production lookup uses the full token sequence, scoped to this body. -/
theorem lookup_tokens (body : FrenModule.TypedBody) (a b : FrenAst.Expr)
    (h : a.tokens = b.tokens) :
    FrenHirToThir.occurrenceType body a = FrenHirToThir.occurrenceType body b := by
  simp only [FrenHirToThir.occurrenceType, h]

-- The checks use actual parse/resolve/type output, then edit its raw occurrence array.
-- The proved projection above is necessary; these finite checks do not prove TypePassContract.
#eval show IO Unit from do
  let source := "pub mod inventory\n\npub fn f(unused: Int): Int := 1 + 2\n\npub fn g(unused: Int): Int := 1 + 2\n"
  let out ← match FrenHirToThir.checkSource ⟨83⟩ source with
    | .ok out => pure out
    | .error d => throw (IO.userError s!"occurrence control source rejected: {repr d}")
  unless out.bodies.size == 2 do throw (IO.userError "occurrence control bodies missing")
  for body in out.bodies do
    unless integerAddView body do throw (IO.userError "valid occurrence inventory rejected")
    let some first := body.occurrences[0]? | throw (IO.userError "missing first occurrence")
    let some second := body.occurrences[1]? | throw (IO.userError "missing second occurrence")
    let wrongType := { first with «type» := .value .bool }
    let wrongContext := { first with context := [(out.resolved.scope.name, .bool)] }
    let mutations := #[
      ("surplus wrong type", body.occurrences.push wrongType),
      ("surplus wrong context", body.occurrences.push wrongContext),
      ("duplicate", body.occurrences.push first),
      ("deleted", body.occurrences.pop),
      ("wrong type", body.occurrences.set! 0 wrongType),
      ("wrong context", body.occurrences.set! 0 wrongContext),
      ("child order", (body.occurrences.set! 0 second).set! 1 first)]
    for (label, occurrences) in mutations do
      if integerAddView { body with occurrences } then
        throw (IO.userError s!"occurrence mutation admitted: {label}")
  let some firstBody := out.bodies[0]? | throw (IO.userError "missing first body")
  let some secondBody := out.bodies[1]? | throw (IO.userError "missing second body")
  if integerAddView { firstBody with occurrences := secondBody.occurrences } then
    throw (IO.userError "another owner's source sites admitted")
  IO.println "occurrence controls: 2 production tables accepted; 14 raw mutations and cross-owner substitution rejected"

-- Focused accepted-resolver input and source anchor, not a typing verdict.
private def enumArithmetic :=
  "pub mod bad\n\npub enum Light { Red, Green }\n\n" ++
  "pub fn f(l: Light): Int := l + 1\n"

#guard match FrenParse.parseFile ⟨37⟩ enumArithmetic with
  | .ok doc => match FrenAstToHir.resolve doc with
    | .ok result =>
      let light := FrenBase.ItemId.named (FrenBase.ItemId.named .root "bad") "Light"
      result.references.any (fun r => r.role == .annotation && r.target == .item light) &&
      result.references.any (fun r => r.role == .expression && r.target == .local 0 &&
        r.written.anchor.text == "l" && r.context.map (·.text) == ["l"] &&
        r.written.anchor.span.file == ⟨37⟩ &&
        r.written.anchor.span.start == 71 && r.written.anchor.span.stop == 72)
    | .error _ => false
  | .error _ => false

-- Display collisions are possible in the base API: rendering is not a key.
private def dotted := FrenBase.ItemId.named .root "bad.Light"
private def nested := FrenBase.ItemId.named (FrenBase.ItemId.named .root "bad") "Light"
#guard dotted.render == nested.render
#guard dotted != nested
#guard FrenBase.ItemId.named nested "Red" !=
  FrenBase.ItemId.named (FrenBase.ItemId.named (FrenBase.ItemId.named .root "bad") "Signal") "Red"


/-! ## Correspondence with Core typing -/

/-- Production contexts list the Core's entries nearest first. -/
def nearest {α : Type} : spec.surface.Snoc α → List α
  | .Empty => []
  | .Extend earlier x => x :: nearest earlier

/-- The level-to-index refinement: the Core entry at level `level` is the
production entry at nearest-first index `|xs| - 1 - level`. -/
theorem lookup_nearest {α : Type} [Inhabited α] (xs : spec.surface.Snoc α) (level : Nat)
    (bound : level < spec.names.length _ xs) :
    spec.names.lookup _ xs level =
      FrenBase.Binding.lookup (nearest xs) (spec.names.length _ xs - 1 - level) := by
  induction xs with
  | Empty => simp [spec.names.length] at bound
  | Extend earlier x ih =>
    simp only [spec.names.length] at bound ⊢
    simp only [spec.names.lookup, nearest]
    by_cases h : level = spec.names.length _ earlier
    · subst h; simp
    · have lt : level < spec.names.length _ earlier := by omega
      have eq : spec.names.length _ earlier + 1 - 1 - level =
          (spec.names.length _ earlier - 1 - level) + 1 := by omega
      simp only [Int.natCast_inj, h, if_false, eq, FrenBase.Binding.lookup_older]
      exact ih lt

/-- The Core's types as the generic production type carrier. -/
def coreType : spec.names.Ty → FrenExpr.ValueType (Fren.Seq String)
  | .Boolean => .bool
  | .Integer => .int
  | .Nominal owner => .enum owner

def coreUnary : spec.surface.UnaryOp → FrenAst.UnaryOp
  | .Neg => .neg | .Not => .not

def coreBinary : spec.surface.BinaryOp → FrenAst.BinaryOp
  | .Add => .add | .Sub => .sub | .Mul => .mul | .Div => .div | .Rem => .rem
  | .Lt => .lt | .Le => .le | .Gt => .gt | .Ge => .ge
  | .And => .and | .Or => .or | .Iff => .iff | .Eq => .eq | .Ne => .ne

/-- The Core unary rule agrees with the actual generic primitive. -/
theorem core_unary (op : spec.surface.UnaryOp) (operand result : spec.names.Ty) :
    @FrenExpr.unary (Fren.Seq String) ⟨fun x y => decide (x = y)⟩
      (coreUnary op) (coreType operand) = some (coreType result) ↔
        spec.types.unary_type? op operand result := by
  cases op <;> cases operand <;> cases result <;>
    simp [coreType, coreUnary, FrenExpr.unary, FrenExpr.unaryOperand,
      FrenExpr.ValueType.compatible, fren_spec]

/-- Every operator and nominal identity is covered; there is no bounded enum domain. -/
theorem core_binary (op : spec.surface.BinaryOp) (left right result : spec.names.Ty) :
    @FrenExpr.binary (Fren.Seq String) ⟨fun x y => decide (x = y)⟩
      (coreBinary op) (coreType left) (coreType right) = some (coreType result) ↔
        spec.types.binary_type? op left right result := by
  cases op <;> cases left <;> cases right <;> cases result <;>
    simp [coreType, coreBinary, FrenExpr.binary, FrenExpr.binaryOperand,
      FrenExpr.binaryResult, FrenExpr.ValueType.compatible, fren_spec, eq_comm]

/-- These adapters change only the contracts' finite tags, not the deciding
implementation. Int equality atoms instantiate the same generic production
primitive that the walker instantiates with canonical ItemId. -/
def primitiveType : spec.thir.ValueKind → Int → FrenExpr.ValueType Int
  | .Boolean, _ => .bool
  | .Integer, _ => .int
  | .Nominal, id => .enum id

def primitiveKind : FrenExpr.ValueType Int → spec.thir.ValueKind
  | .bool => .Boolean | .int => .Integer | .enum _ => .Nominal

def primitiveUnary : spec.thir.UnaryTag → FrenAst.UnaryOp
  | .Neg => .neg | .Not => .not

def primitiveBinary : spec.thir.BinaryTag → FrenAst.BinaryOp
  | .Add => .add | .Sub => .sub | .Mul => .mul | .Div => .div | .Rem => .rem
  | .Lt => .lt | .Le => .le | .Gt => .gt | .Ge => .ge
  | .And => .and | .Or => .or | .Iff => .iff | .Eq => .eq | .Ne => .ne

impl compatibility: thir::compatible for
    (left right : spec.thir.ValueKind) (left_id right_id : Int) {
  left := left, right := right, left_id := left_id, right_id := right_id,
  same? := (primitiveType left left_id).compatible (primitiveType right right_id)
} by
  intro left right left_id right_id _
  cases left <;> cases right <;>
    simp [fren_spec, primitiveType, FrenExpr.ValueType.compatible, beq_iff_eq]

impl unary: thir::unary for (op : spec.thir.UnaryTag) (operand : spec.thir.ValueKind) {
  op := op, operand := operand,
  accepted? := (FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).isSome,
  result := primitiveKind ((FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).getD .bool)
} by
  intro op operand _
  cases op <;> cases operand <;>
    simp [fren_spec, primitiveUnary, primitiveType, primitiveKind, FrenExpr.unary,
      FrenExpr.unaryOperand, FrenExpr.ValueType.compatible]

impl binary: thir::binary for
    (op : spec.thir.BinaryTag) (left right : spec.thir.ValueKind) (left_id right_id : Int) {
  op := op, left := left, right := right, left_id := left_id, right_id := right_id,
  accepted? := (FrenExpr.binary (primitiveBinary op) (primitiveType left left_id)
    (primitiveType right right_id)).isSome,
  result := primitiveKind ((FrenExpr.binary (primitiveBinary op) (primitiveType left left_id)
    (primitiveType right right_id)).getD .bool)
} by
  intro op left right left_id right_id _
  cases op <;> cases left <;> cases right <;>
    simp [fren_spec, primitiveBinary, primitiveType, primitiveKind, FrenExpr.binary,
      FrenExpr.binaryOperand, FrenExpr.binaryResult, FrenExpr.ValueType.compatible, beq_iff_eq]
  all_goals by_cases h : left_id = right_id <;> simp_all [primitiveKind, eq_comm]

/-! ## The typed module

`thir.module.items` and `thir.module.errors`, stated over the production
module types without the module-level function `typeModule`. What typing one
item gives is `typeItem`; the rules say how a module's result is made of its
items' results, and the theorems relate `typeModule` to that. -/

section TypedModule
open FrenExpr FrenModule.Core FrenHirToThir.Pass

/-- The signatures every item of a module is typed against. -/
def moduleSignatures (m : Hir) : Array (FrenBase.ItemId × Array FrenExpr.Ty × FrenExpr.Ty) :=
  m.functions.map fun f => (f.id, f.params.map (·.type), f.result)

/-- One item typed alone. Of the rest of the module it reads the signatures
and the constructor owners, and no other item's body, members or origins. -/
def Alone (m : Hir) (item : Item (FrenExpr.Expr .hir)) : Result (Item (FrenExpr.Expr .thir)) :=
  typeItem (moduleSignatures m) m.ctorOwner item

/-- The error of a failing result. -/
def errorOf {α : Type} : Result α → Option TypeError
  | .error e => some e
  | .ok _ => none

/-- The module rule. A typed module is the result exactly when every item,
typed alone, gives the item at the same position. A list of errors is the
result exactly when it is nonempty and holds, in declaration order, the error
of each item that fails when typed alone. -/
def ModuleResult (m : Hir) : Except (Array TypeError) Thir → Prop
  | .ok t => t.id = m.id ∧ m.items.toList.map (Alone m) = t.items.toList.map .ok
  | .error es => es ≠ #[] ∧ es.toList = m.items.toList.filterMap fun item => errorOf (Alone m item)

private theorem all_ok {α : Type} : ∀ rs : List (Result α),
    rs.filterMap errorOf = [] → rs = (rs.filterMap (·.toOption)).map .ok
  | [], _ => rfl
  | .ok a :: rs, h => by
    have h' : rs.filterMap errorOf = [] := by simpa [errorOf] using h
    simpa [Except.toOption] using all_ok rs h'
  | .error e :: rs, h => by simp [errorOf] at h

private theorem ok_toOption {α : Type} (l : List α) :
    (l.map (Except.ok : α → Result α)).filterMap (·.toOption) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [Except.toOption] using ih

private theorem typeModule_eq (m : Hir) : typeModule m =
    if ((m.items.map (Alone m)).filterMap errorOf).isEmpty then
      .ok ⟨m.id, (m.items.map (Alone m)).filterMap (·.toOption)⟩
    else .error ((m.items.map (Alone m)).filterMap errorOf) := by
  have h : (fun r : Result (Item (FrenExpr.Expr .thir)) =>
      match r with | .error e => some e | .ok _ => none) = errorOf := by
    funext r; cases r <;> rfl
  unfold typeModule
  simp only [← h]
  rfl

/-- The production checker's result satisfies the module rule. -/
theorem typed_module_sound (m : Hir) : ModuleResult m (typeModule m) := by
  rw [typeModule_eq]
  split
  · rename_i h
    refine ⟨rfl, ?_⟩
    have h' : (m.items.toList.map (Alone m)).filterMap errorOf = [] := by
      simpa [Array.isEmpty_iff, ← Array.toList_eq_nil_iff] using h
    simpa using all_ok _ h'
  · rename_i h
    refine ⟨fun he => h (by rw [he]; rfl), by simp [Function.comp_def]⟩

/-- The module rule determines the result. -/
theorem typed_module_unique {m : Hir} {r : Except (Array TypeError) Thir}
    (h : ModuleResult m r) : r = typeModule m := by
  rw [typeModule_eq]
  cases r with
  | ok t =>
    obtain ⟨hid, hs⟩ := h
    have hl : (m.items.map (Alone m)).toList = t.items.toList.map .ok := by simpa using hs
    have he : ((m.items.map (Alone m)).filterMap errorOf).toList = [] := by
      rw [Array.toList_filterMap, hl]; simp [errorOf]
    have hi : ((m.items.map (Alone m)).filterMap (·.toOption)).toList = t.items.toList := by
      rw [Array.toList_filterMap, hl]; exact ok_toOption _
    rw [if_pos (by simpa [Array.isEmpty_iff, ← Array.toList_eq_nil_iff] using he)]
    obtain ⟨id, items⟩ := t
    dsimp only at hid hi
    subst hid
    rw [Array.toList_inj.mp hi]
  | error es =>
    obtain ⟨hne, hs⟩ := h
    have he : (m.items.map (Alone m)).filterMap errorOf = es :=
      Array.toList_inj.mp (by rw [hs]; simp [Function.comp_def])
    rw [he, if_neg (by simpa [Array.isEmpty_iff] using hne)]

/-- An error in one item neither hides nor changes the error of another: each
failing item's own error is in the module's result. -/
theorem item_error_reported {m : Hir} {es : Array TypeError} (h : typeModule m = .error es)
    {item : Item (FrenExpr.Expr .hir)} (hi : item ∈ m.items.toList) {e : TypeError}
    (he : Alone m item = .error e) : e ∈ es := by
  have hs := (h ▸ typed_module_sound m : ModuleResult m (.error es)).2
  have : e ∈ es.toList := by
    rw [hs, List.mem_filterMap]
    exact ⟨item, hi, by rw [he]; rfl⟩
  simpa using this

/-- Every reported error is the error of an item typed alone. -/
theorem reported_error_alone {m : Hir} {es : Array TypeError} (h : typeModule m = .error es)
    {e : TypeError} (he : e ∈ es) :
    ∃ item ∈ m.items.toList, errorOf (Alone m item) = some e := by
  have hs := (h ▸ typed_module_sound m : ModuleResult m (.error es)).2
  have : e ∈ es.toList := by simpa using he
  rw [hs, List.mem_filterMap] at this
  exact this

/-- An item's result reads the rest of the module through its signatures and
constructor owners alone: modules that agree on both give the item the same
result, whatever their other bodies and members are. -/
theorem alone_reads_signatures {m m' : Hir} (hs : moduleSignatures m = moduleSignatures m')
    (hc : m.ctorOwner = m'.ctorOwner) (item : Item (FrenExpr.Expr .hir)) :
    Alone m item = Alone m' item := by
  unfold Alone; rw [hs, hc]

/-- Parameters come first: a signature error is the item's error, whatever
its body or members are. -/
theorem function_params_first (sigs co) (f : Function (FrenExpr.Expr .hir)) (os : Array Origin)
    (e : TypeError) (h : checkParams f.id f.params = .error e) :
    typeItem sigs co (.function f os) = .error e := by
  simp [typeItem, h, bind, Except.bind]

theorem check_params_first (sigs co) (c : Check (FrenExpr.Expr .hir)) (os : Array Origin)
    (e : TypeError) (h : checkParams c.id c.params = .error e) :
    typeItem sigs co (.check c os) = .error e := by
  simp [typeItem, h, bind, Except.bind]

end TypedModule

#print axioms typed_module_sound
#print axioms typed_module_unique

section Algorithmic
open spec.surface spec.names spec.types spec.algorithmic
open Spec.Language.NamesAndScope (lookup_bound)

/-- `thir.algorithmic.first-arm`: bodies typed alike agree with the first. -/
theorem first_arm_typed (arms : Snoc (ArmF Typing)) (ctx : Snoc Ty) (ty : Ty)
    (hne : arms ≠ .Empty) (h : arm_bodies? arms ctx ty = true) :
    first_body arms = some ⟨ctx, ty⟩ := by
  induction arms with
  | Empty => exact absurd rfl hne
  | Extend earlier arm ih =>
    simp only [arm_bodies?, decide_eq_true_eq] at h
    cases earlier with
    | Empty =>
      rcases arm with ⟨c, ⟨bc, bt⟩⟩
      simp only at h
      simp [first_body, h.1.1, h.1.2]
    | Extend e a => simp only [first_body] at ih ⊢; rw [ih (by simp) h.2]

theorem first_body_nonempty (arms : Snoc (ArmF Typing)) (first : Typing)
    (h : first_body arms = some first) : arms ≠ .Empty := by
  intro e; subst e; simp [first_body] at h

/-! ### Outcomes of the sequences -/

theorem expect_blamed (premise : Premise) (expected found : Ty) (rest : Outcome)
    (h : outcome_type rest = none) :
    outcome_type (expect_type premise expected found rest) = none := by
  unfold expect_type
  split <;> simp_all [outcome_type]

theorem outcome_typed (ty : Ty) : outcome_type (.Typed ty) = some ty := rfl

theorem outcome_expect (premise : Premise) (expected found : Ty) (rest : Outcome) :
    outcome_type (expect_type premise expected found rest) =
      if found = expected then outcome_type rest else none := by
  unfold expect_type
  split <;> simp [outcome_type]

theorem outcome_local (ctx : Snoc Ty) (level : Int) :
    outcome_type (judge_local ctx level) = lookup _ ctx level := by
  unfold judge_local
  cases lookup _ ctx level <;> simp [outcome_type]

theorem judge_arguments_blamed (args : Snoc Typing) (params : Snoc Ty) (rest : Outcome)
    (h : outcome_type rest = none) : outcome_type (judge_arguments args params rest) = none := by
  induction args generalizing params rest with
  | Empty => simpa [judge_arguments] using h
  | Extend earlier arg ih =>
    cases params with
    | Empty => simpa [judge_arguments] using h
    | Extend earlier_params param =>
      simp only [judge_arguments]
      exact ih earlier_params _ (expect_blamed _ _ _ _ h)

/-- `thir.algorithmic.sequences`: accepted arguments leave the rest as it was. -/
theorem arguments_accepted (args : Snoc Typing) (params : Snoc Ty) (rest : Outcome)
    (h : argument_types? args params = true) :
    length _ args = length _ params ∧ judge_arguments args params rest = rest := by
  induction args generalizing params rest with
  | Empty =>
    cases params with
    | Empty => simp [length, judge_arguments]
    | Extend _ _ => simp [argument_types?] at h
  | Extend earlier arg ih =>
    cases params with
    | Empty => simp [argument_types?] at h
    | Extend earlier_params param =>
      simp only [argument_types?, decide_eq_true_eq] at h
      obtain ⟨hl, hj⟩ := ih earlier_params rest h.2
      simp [length, judge_arguments, expect_type, h.1, hl, hj]

/-- `thir.algorithmic.sequences`: a rejected argument blames a premise. -/
theorem arguments_rejected (args : Snoc Typing) (params : Snoc Ty) (rest : Outcome)
    (hl : length _ args = length _ params) (h : argument_types? args params = false) :
    outcome_type (judge_arguments args params rest) = none := by
  induction args generalizing params rest with
  | Empty =>
    cases params with
    | Empty => simp [argument_types?] at h
    | Extend _ _ => simp [length] at hl
  | Extend earlier arg ih =>
    cases params with
    | Empty => simp [length] at hl
    | Extend earlier_params param =>
      simp [length] at hl
      simp only [judge_arguments]
      by_cases ht : arg.ty = param
      · have hr : argument_types? earlier earlier_params = false := by
          simpa [argument_types?, ht] using h
        exact ih earlier_params _ hl hr
      · exact judge_arguments_blamed _ _ _ (by simp [expect_type, ht, outcome_type])

/-- An arm either satisfies both of its premises or blames one. -/
theorem judge_arm_cases (symb : Snoc Entry) (owner : Fren.Seq String) (common : Ty) (index : Int)
    (arm : ArmF Typing) (rest : Outcome) :
    (entry symb arm.constructor = some (.Constructor owner) ∧ arm.body.ty = common ∧
      judge_arm symb owner common index arm rest = rest) ∨
    outcome_type (judge_arm symb owner common index arm rest) = none := by
  cases he : entry symb arm.constructor with
  | none => right; simp [judge_arm, he, outcome_type]
  | some kind =>
    cases kind with
    | Constructor found =>
      by_cases hf : found = owner
      · by_cases hb : arm.body.ty = common
        · left; simp [judge_arm, he, expect_type, hf, hb]
        · right; simp [judge_arm, he, expect_type, hf, hb, outcome_type]
      · right; simp [judge_arm, he, expect_type, hf, outcome_type]
    | _ => right; simp [judge_arm, he, outcome_type]

theorem judge_arms_blamed (symb : Snoc Entry) (owner : Fren.Seq String) (common : Ty)
    (arms : Snoc (ArmF Typing)) (rest : Outcome) (h : outcome_type rest = none) :
    outcome_type (judge_arms symb owner common arms rest) = none := by
  induction arms generalizing rest with
  | Empty => simpa [judge_arms] using h
  | Extend earlier arm ih =>
    simp only [judge_arms]
    apply ih
    rcases judge_arm_cases symb owner common (length _ earlier) arm rest with ⟨_, _, hj⟩ | hn
    · rw [hj]; exact h
    · exact hn

/-- `thir.algorithmic.sequences`: accepted arms leave the rest as it was. -/
theorem arms_accepted (symb : Snoc Entry) (owner : Fren.Seq String) (common : Ty)
    (arms : Snoc (ArmF Typing)) (ctx : Snoc Ty) (rest : Outcome)
    (hp : arm_patterns? symb arms owner = true) (hb : arm_bodies? arms ctx common = true) :
    arms_in_context? arms ctx = true ∧ judge_arms symb owner common arms rest = rest := by
  induction arms generalizing rest with
  | Empty => simp [arms_in_context?, judge_arms]
  | Extend earlier arm ih =>
    simp only [arm_patterns?, decide_eq_true_eq] at hp
    simp only [arm_bodies?, decide_eq_true_eq] at hb
    obtain ⟨hc, hj⟩ := ih rest hp.2 hb.2
    simp [arms_in_context?, judge_arms, judge_arm, expect_type, hp.1, hb.1.1, hb.1.2, hc, hj]

/-- `thir.algorithmic.sequences`: a rejected arm blames a premise. -/
theorem arms_rejected (symb : Snoc Entry) (owner : Fren.Seq String) (common : Ty)
    (arms : Snoc (ArmF Typing)) (ctx : Snoc Ty) (rest : Outcome)
    (hc : arms_in_context? arms ctx = true)
    (h : ¬(arm_patterns? symb arms owner = true ∧ arm_bodies? arms ctx common = true)) :
    outcome_type (judge_arms symb owner common arms rest) = none := by
  induction arms generalizing rest with
  | Empty => exact absurd (by simp [arm_patterns?, arm_bodies?]) h
  | Extend earlier arm ih =>
    simp only [arms_in_context?, decide_eq_true_eq] at hc
    simp only [judge_arms]
    rcases judge_arm_cases symb owner common (length _ earlier) arm rest with ⟨he, hb, hj⟩ | hn
    · rw [hj]
      apply ih rest hc.2
      intro hpb
      apply h
      simp [arm_patterns?, arm_bodies?, he, hb, hc.1, hpb.1, hpb.2]
    · exact judge_arms_blamed symb owner common earlier _ hn

/-! ### Agreement of one layer -/

theorem synth_layer_core (symb : Snoc Entry) (ctx : Snoc Ty) (form : CoreF Typing) :
    synth_layer symb ctx (.Core form) = synth_core symb ctx form := by
  simp [synth_layer, synth_core, placed?, judge_layer, fren_spec]

/-- `thir.algorithmic.agreement`, sound, for the lift. -/
theorem synth_core_sound (symb : Snoc Entry) (ctx : Snoc Ty) (form : CoreF Typing) (ty : Ty)
    (h : synth_core symb ctx form = some ty) : rule? symb ctx form ty = true := by
  cases form with
  | Unary op operand =>
    cases op <;> simp [synth_core, provided, placed_core?, judge_core, judge_unary, outcome_expect, unary_operand, fren_spec] at h <;>
      simp [rule?, unary_rule?, unary_type?, fren_spec] <;> simp_all
  | Binary op left right =>
    cases op <;> simp [synth_core, provided, placed_core?, judge_core, judge_binary, outcome_expect, binary_operand, binary_output, integer_binary?, comparison?, boolean_binary?,
      fren_spec] at h <;>
      simp [rule?, binary_rule?, binary_type?, integer_binary?, comparison?, boolean_binary?,
        fren_spec] <;> simp_all
  | Constructor item =>
    cases hE : entry symb item with
    | none =>
      simp [synth_core, provided, placed_core?, judge_core, judge_constructor, outcome_type, hE,
        fren_spec] at h
    | some kind =>
      cases kind <;> simp [synth_core, provided, placed_core?, judge_core, judge_constructor,
        outcome_type, hE, fren_spec] at h <;>
        simp [rule?, constructor_rule?, hE, fren_spec] <;> simp_all
  | Call item args =>
    by_cases hp : placed_core? ctx (.Call item args) = true
    · have h' : outcome_type (judge_call symb item args) = some ty := by
        simpa [synth_core, provided, hp, judge_core] using h
      simp [placed_core?, fren_spec] at hp
      cases hE : entry symb item with
      | none => simp [judge_call, hE, outcome_type] at h'
      | some kind =>
        cases kind with
        | Function sig =>
          by_cases hlen : length _ args = length _ sig.params
          · cases hat : argument_types? args sig.params with
            | false =>
              have hn := arguments_rejected args sig.params (.Typed sig.result) hlen hat
              simp [judge_call, hE, hlen, hn] at h'
            | true =>
              have hj := (arguments_accepted args sig.params (.Typed sig.result) hat).2
              simp [judge_call, hE, hlen, hj, outcome_type] at h'
              simp [rule?, call_rule?, hE, hat, hp, h', fren_spec]
          · simp [judge_call, hE, hlen, outcome_type] at h'
        | _ => simp [judge_call, hE, outcome_type] at h'
    · simp [synth_core, provided, hp] at h
  | Match scrutinee arms =>
    rcases scrutinee with ⟨sc, sty⟩
    by_cases hp : placed_core? ctx (.Match ⟨sc, sty⟩ arms) = true
    · have h' : outcome_type (judge_match symb ⟨sc, sty⟩ arms) = some ty := by
        simpa [synth_core, provided, hp, judge_core] using h
      simp [placed_core?, fren_spec] at hp
      obtain ⟨hsc, hin⟩ := hp
      cases sty with
      | Nominal owner =>
        cases hf : first_body arms with
        | none => simp [judge_match, hf, outcome_type] at h'
        | some first =>
          have hne := first_body_nonempty arms first hf
          simp only [judge_match, hf] at h'
          by_cases hpb : arm_patterns? symb arms owner = true ∧
              arm_bodies? arms ctx first.ty = true
          · rw [(arms_accepted symb owner first.ty arms ctx _ hpb.1 hpb.2).2] at h'
            simp [outcome_type] at h'
            subst h'
            simp [rule?, match_rule?, fren_spec, hsc, hpb.1, hpb.2, hne]
          · rw [arms_rejected symb owner first.ty arms ctx _ hin hpb] at h'
            cases h'
      | _ => simp [outcome_type] at h'
    · simp [synth_core, provided, hp] at h
  | Let annotation value body =>
    cases annotation <;>
      simp [synth_core, provided, placed_core?, judge_core, judge_let, outcome_expect, fren_spec] at h <;>
      simp [rule?, let_rule?, let_annotated_rule?, fren_spec] <;> simp_all
  | _ =>
    simp [synth_core, provided, placed_core?, judge_core, judge_local, judge_if, outcome_expect, outcome_local, fren_spec] at h <;>
      simp [rule?, boolean_rule?, integer_rule?, local_rule?, if_rule?, fren_spec] <;> simp_all

/-- `thir.algorithmic.agreement`, complete, for the lift. -/
theorem synth_core_complete (symb : Snoc Entry) (ctx : Snoc Ty) (form : CoreF Typing) (ty : Ty)
    (h : rule? symb ctx form ty = true) : synth_core symb ctx form = some ty := by
  cases form with
  | Unary op operand =>
    cases op <;> simp [rule?, unary_rule?, unary_type?, fren_spec] at h <;>
      simp [synth_core, provided, placed_core?, judge_core, judge_unary, outcome_expect, unary_operand, fren_spec] <;> simp_all
  | Binary op left right =>
    cases op <;> simp [rule?, binary_rule?, binary_type?, integer_binary?, comparison?,
      boolean_binary?, fren_spec] at h <;>
      simp [synth_core, provided, placed_core?, judge_core, judge_binary, outcome_expect, binary_operand, binary_output, integer_binary?, comparison?,
        boolean_binary?, fren_spec] <;> simp_all
  | Constructor item =>
    cases hE : entry symb item with
    | none => simp [rule?, constructor_rule?, hE, fren_spec] at h
    | some kind =>
      cases kind <;> simp [rule?, constructor_rule?, hE, fren_spec] at h <;>
        simp [synth_core, provided, placed_core?, judge_core, judge_constructor, outcome_type,
          hE, fren_spec] <;> simp_all
  | Call item args =>
    cases hE : entry symb item with
    | none => simp [rule?, call_rule?, hE, fren_spec] at h
    | some kind =>
      cases kind with
      | Function sig =>
        simp [rule?, call_rule?, hE, fren_spec] at h
        obtain ⟨⟨hty, hin⟩, hat⟩ := h
        obtain ⟨hlen, hj⟩ := arguments_accepted args sig.params (.Typed sig.result) hat
        simp [synth_core, provided, placed_core?, judge_core, judge_call, hE, hlen, hj,
          outcome_type, hin, hty, fren_spec]
      | _ => simp [rule?, call_rule?, hE, fren_spec] at h
  | Match scrutinee arms =>
    rcases scrutinee with ⟨sc, sty⟩
    cases sty <;> simp [rule?, match_rule?, fren_spec] at h
    rename_i owner
    have hf := first_arm_typed arms ctx ty h.1.1.2 h.1.2
    obtain ⟨hin, hj⟩ := arms_accepted symb owner ty arms ctx (.Typed ty) h.2 h.1.2
    simp [synth_core, provided, placed_core?, judge_core, judge_match, hf, hj, hin,
      outcome_type, h.1.1.1, fren_spec]
  | Let annotation value body =>
    cases annotation <;> simp [rule?, let_rule?, let_annotated_rule?, fren_spec] at h <;>
      simp [synth_core, provided, placed_core?, judge_core, judge_let, outcome_expect, fren_spec] <;> simp_all
  | _ =>
    simp [rule?, boolean_rule?, integer_rule?, local_rule?, if_rule?, fren_spec] at h <;>
      simp [synth_core, provided, placed_core?, judge_core, judge_local, judge_if, outcome_expect, outcome_local, fren_spec] <;> simp_all

/-! ### The lift to tables -/

theorem lookup_grow {α : Type} [Inhabited α] (xs : Snoc α) (x y : α) (p : Int)
    (h : lookup _ xs p = some y) : lookup _ (.Extend xs x) p = some y := by
  have hb := lookup_bound xs p y h
  simp only [lookup]
  split
  · omega
  · exact h

theorem typing_at_grow (rows : Snoc Row) (r : Row) (p : Int) (t : Typing)
    (h : typing_at rows p = some t) : typing_at (.Extend rows r) p = some t := by
  simp only [typing_at] at h ⊢
  cases hl : lookup _ rows p with
  | none => simp [hl] at h
  | some row => rw [lookup_grow rows r row p hl]; simpa [hl] using h

theorem annotate_arguments_grow (rows : Snoc Row) (r : Row) (args : Snoc Int) (ts : Snoc Typing)
    (h : annotate_arguments rows args = some ts) :
    annotate_arguments (.Extend rows r) args = some ts := by
  induction args generalizing ts with
  | Empty => simpa [annotate_arguments] using h
  | Extend earlier arg ih =>
    simp only [annotate_arguments] at h ⊢
    cases h1 : annotate_arguments rows earlier with
    | none => simp [h1] at h
    | some typed =>
      cases h2 : typing_at rows arg with
      | none => simp [h1, h2] at h
      | some c => rw [ih typed h1, typing_at_grow rows r arg c h2]; simpa [h1, h2] using h

theorem annotate_arms_grow (rows : Snoc Row) (r : Row) (arms : Snoc (ArmF Int))
    (ts : Snoc (ArmF Typing)) (h : annotate_arms rows arms = some ts) :
    annotate_arms (.Extend rows r) arms = some ts := by
  induction arms generalizing ts with
  | Empty => simpa [annotate_arms] using h
  | Extend earlier arm ih =>
    simp only [annotate_arms] at h ⊢
    cases h1 : annotate_arms rows earlier with
    | none => simp [h1] at h
    | some typed =>
      cases h2 : typing_at rows arm.body with
      | none => simp [h1, h2] at h
      | some c => rw [ih typed h1, typing_at_grow rows r arm.body c h2]; simpa [h1, h2] using h

/-- A layer annotated over a table is annotated alike over a longer one. -/
theorem annotate_grow (rows : Snoc Row) (r : Row) (form : CoreF Int) (typed : CoreF Typing)
    (h : annotate rows form = some typed) : annotate (.Extend rows r) form = some typed := by
  cases form with
  | Unary op a =>
    simp only [annotate] at h ⊢
    cases h1 : typing_at rows a with
    | none => simp [h1] at h
    | some c => rw [typing_at_grow rows r a c h1]; simpa [h1] using h
  | Binary op a b =>
    simp only [annotate] at h ⊢
    cases h1 : typing_at rows a with
    | none => simp [h1] at h
    | some c =>
      cases h2 : typing_at rows b with
      | none => simp [h1, h2] at h
      | some d =>
        rw [typing_at_grow rows r a c h1, typing_at_grow rows r b d h2]; simpa [h1, h2] using h
  | Call item args =>
    simp only [annotate] at h ⊢
    cases h1 : annotate_arguments rows args with
    | none => simp [h1] at h
    | some ts => rw [annotate_arguments_grow rows r args ts h1]; simpa [h1] using h
  | Let annotation a b =>
    simp only [annotate] at h ⊢
    cases h1 : typing_at rows a with
    | none => simp [h1] at h
    | some c =>
      cases h2 : typing_at rows b with
      | none => simp [h1, h2] at h
      | some d =>
        rw [typing_at_grow rows r a c h1, typing_at_grow rows r b d h2]; simpa [h1, h2] using h
  | If a b c =>
    simp only [annotate] at h ⊢
    cases h1 : typing_at rows a with
    | none => simp [h1] at h
    | some x =>
      cases h2 : typing_at rows b with
      | none => simp [h1, h2] at h
      | some y =>
        cases h3 : typing_at rows c with
        | none => simp [h1, h2, h3] at h
        | some z =>
          rw [typing_at_grow rows r a x h1, typing_at_grow rows r b y h2,
            typing_at_grow rows r c z h3]
          simpa [h1, h2, h3] using h
  | Match a arms =>
    simp only [annotate] at h ⊢
    cases h1 : typing_at rows a with
    | none => simp [h1] at h
    | some x =>
      cases h2 : annotate_arms rows arms with
      | none => simp [h1, h2] at h
      | some ts =>
        rw [typing_at_grow rows r a x h1, annotate_arms_grow rows r arms ts h2]
        simpa [h1, h2] using h
  | _ => simpa [annotate] using h

/-- Every row of a valid Core table satisfies its rule over the whole table. -/
theorem core_rows_layer (symb : Snoc Entry) (rows : Snoc Row)
    (hv : rows_valid? symb rows = true) :
    ∀ p r, lookup _ rows p = some r →
      ∃ typed, annotate rows r.form = some typed ∧ rule? symb r.ctx typed r.ty = true := by
  induction rows with
  | Empty => intro p r h; simp [lookup] at h
  | Extend earlier last ih =>
    simp only [rows_valid?, decide_eq_true_eq] at hv
    intro p r h
    simp only [lookup] at h
    split at h
    · have := Option.some.inj h; subst this
      have hl := hv.2
      cases ha : annotate earlier last.form with
      | none => simp [ha] at hl
      | some form =>
        simp only [ha] at hl
        exact ⟨form, annotate_grow earlier last last.form form ha, hl⟩
    · obtain ⟨t, h1, h2⟩ := ih hv.1.1 p r h
      exact ⟨t, annotate_grow earlier last r.form t h1, h2⟩

/-- The valid part of `thir.algorithmic.preservation`. -/
theorem desugar_valid (symb : Snoc Entry) (rows : Snoc HirRow)
    (hv : hir_rows_valid? symb rows = true) :
    ∃ core, desugar_rows rows = some core ∧ rows_valid? symb core = true := by
  induction rows with
  | Empty => exact ⟨.Empty, by simp [desugar_rows], by simp [rows_valid?]⟩
  | Extend earlier row ih =>
    simp only [hir_rows_valid?, decide_eq_true_eq] at hv
    obtain ⟨core, hd, hc⟩ := ih hv.1.1
    have h2 := hv.2
    have hctx := hv.1.2
    simp only [hd] at h2
    rcases row with ⟨form, rc, rt⟩
    simp only at h2 hctx
    cases form with
    | Core f =>
      simp only [hir_annotate] at h2
      cases ha : annotate core f with
      | none => simp [ha] at h2
      | some typed =>
        simp only [ha] at h2
        have h3 : synth_core symb rc typed = some rt := by
          rw [← synth_layer_core]; exact of_decide_eq_true h2
        have hr := synth_core_sound symb rc typed rt h3
        exact ⟨.Extend core ⟨f, rc, rt⟩, by simp [desugar_rows, core_row, hd],
          by simp [rows_valid?, hc, hctx, ha, hr]⟩
    | Paren body =>
      simp only [hir_annotate] at h2
      cases hl : lookup _ core body with
      | none => simp [typing_at, hl] at h2
      | some d =>
        simp [typing_at, hl, synth_layer, provided, placed?, outcome_type, fren_spec] at h2
        obtain ⟨typed, ha, hr⟩ := core_rows_layer symb core hc body d hl
        rw [h2.1, h2.2] at hr
        exact ⟨.Extend core ⟨d.form, rc, rt⟩, by simp [desugar_rows, core_row, hd, hl],
          by simp [rows_valid?, hc, hctx, ha, hr]⟩

/-- Desugaring keeps each row's context and type. -/
theorem desugar_extend (rows : Snoc HirRow) (core : Snoc Row) (base : Snoc Ty)
    (hd : desugar_rows rows = some core) (h : hir_rows_extend? rows base = true) :
    rows_extend? core base = true := by
  induction rows generalizing core with
  | Empty => simp [desugar_rows] at hd; subst hd; simp [rows_extend?]
  | Extend earlier row ih =>
    simp only [hir_rows_extend?, decide_eq_true_eq] at h
    simp only [desugar_rows] at hd
    cases hd' : desugar_rows earlier with
    | none => simp [hd'] at hd
    | some c =>
      rcases row with ⟨form, rc, rt⟩
      cases form with
      | Core f =>
        simp [hd', core_row] at hd; subst hd
        simp [rows_extend?, ih c hd' h.2]; exact h.1
      | Paren body =>
        cases hl : lookup _ c body with
        | none => simp [hd', hl] at hd
        | some d =>
          simp [hd', hl, core_row] at hd; subst hd
          simp [rows_extend?, ih c hd' h.2]; exact h.1

theorem desugar_length (rows : Snoc HirRow) (core : Snoc Row)
    (hd : desugar_rows rows = some core) : length _ core = length _ rows := by
  induction rows generalizing core with
  | Empty => simp [desugar_rows] at hd; subst hd; simp [length]
  | Extend earlier row ih =>
    simp only [desugar_rows] at hd
    cases hd' : desugar_rows earlier with
    | none => simp [hd'] at hd
    | some c =>
      rcases row with ⟨form, rc, rt⟩
      cases form with
      | Core f =>
        simp [hd', core_row] at hd; subst hd
        simp [length, ih c hd']
      | Paren body =>
        cases hl : lookup _ c body with
        | none => simp [hd', hl] at hd
        | some d =>
          simp [hd', hl, core_row] at hd; subst hd
          simp [length, ih c hd']

theorem desugar_root (earlier : Snoc HirRow) (row : HirRow) (core : Snoc Row)
    (hd : desugar_rows (.Extend earlier row) = some core) :
    ∃ c f, core = .Extend c ⟨f, row.ctx, row.ty⟩ := by
  simp only [desugar_rows] at hd
  cases hd' : desugar_rows earlier with
  | none => simp [hd'] at hd
  | some c =>
    rcases row with ⟨form, rc, rt⟩
    cases form with
    | Core f => simp [hd', core_row] at hd; exact ⟨c, f, hd.symm⟩
    | Paren body =>
      cases hl : lookup _ c body with
      | none => simp [hd', hl] at hd
      | some d => simp [hd', hl, core_row] at hd; exact ⟨c, d.form, hd.symm⟩

/-- `thir.algorithmic.preservation`. -/
theorem desugaring_preserves_typing (symb : Snoc Entry) (rows : Snoc HirRow) (ctx : Snoc Ty)
    (ty : Ty) (h : synthesis? symb rows ctx ty = true) :
    desugared_derivation? symb rows ctx ty = true := by
  cases rows with
  | Empty => simp [synthesis?, fren_spec] at h
  | Extend earlier root =>
    simp only [synthesis?, decide_eq_true_eq] at h
    obtain ⟨core, hd, hc⟩ := desugar_valid symb _ h.1.1.2
    have he := desugar_extend _ core ctx hd h.1.2
    obtain ⟨c, f, hcore⟩ := desugar_root earlier root core hd
    have hroot := h.2
    simp [fren_spec] at hroot
    subst hcore
    simp only [desugared_derivation?, hd, derivation?, decide_eq_true_eq]
    exact ⟨⟨⟨⟨h.1.1.1.1, h.1.1.1.2⟩, hc⟩, he⟩, by simp [fren_spec, hroot]⟩

/-- `thir.algorithmic.reflection`. -/
theorem desugaring_reflects_typing (symb : Snoc Entry) (rows : Snoc HirRow) (core : Snoc Row)
    (hp : parens_faithful? rows = true) (hd : desugar_rows rows = some core)
    (hc : rows_valid? symb core = true) : hir_rows_valid? symb rows = true := by
  induction rows generalizing core with
  | Empty => simp [hir_rows_valid?]
  | Extend earlier row ih =>
    simp only [parens_faithful?, decide_eq_true_eq] at hp
    simp only [desugar_rows] at hd
    cases hd' : desugar_rows earlier with
    | none => simp [hd'] at hd
    | some c =>
      have hp2 := hp.2
      rcases row with ⟨form, rc, rt⟩
      cases form with
      | Core f =>
        simp [hd', core_row] at hd; subst hd
        simp only [rows_valid?, decide_eq_true_eq] at hc
        have hl := hc.2
        cases ha : annotate c f with
        | none => simp [ha] at hl
        | some typed =>
          simp only [ha] at hl
          have hs := synth_core_complete symb rc typed rt hl
          have hctx : ctx_ok? symb rc = true := hc.1.2
          have hs' : synth_layer symb rc (.Core typed) = some rt := by
            rw [synth_layer_core]; exact hs
          simp [hir_rows_valid?, ih c hp.1 hd' hc.1.1, hd', hir_annotate, ha, hs', hctx]
      | Paren body =>
        cases hl : lookup _ c body with
        | none => simp [hd', hl] at hd
        | some d =>
          simp [hd', hl, core_row] at hd; subst hd
          simp only [rows_valid?, decide_eq_true_eq] at hc
          have hctx : ctx_ok? symb rc = true := hc.1.2
          simp [hd'] at hp2
          simp [hir_rows_valid?, ih c hp.1 hd' hc.1.1, hd', hir_annotate, hp2, synth_layer,
            provided, placed?, outcome_type, hctx, fren_spec]

/-- A valid table's parentheses are faithful: half of `thir.algorithmic.reflection`. -/
theorem hir_valid_faithful (symb : Snoc Entry) (rows : Snoc HirRow)
    (hv : hir_rows_valid? symb rows = true) : parens_faithful? rows = true := by
  induction rows with
  | Empty => simp [parens_faithful?]
  | Extend earlier row ih =>
    simp only [hir_rows_valid?, decide_eq_true_eq] at hv
    have h2 := hv.2
    rcases row with ⟨form, rc, rt⟩
    cases hd : desugar_rows earlier with
    | none => simp [hd] at h2
    | some core =>
      cases form with
      | Core f => simp [parens_faithful?, ih hv.1.1]
      | Paren body =>
        simp only [hd, hir_annotate] at h2
        cases ht : typing_at core body with
        | none => simp [ht] at h2
        | some typed =>
          rcases typed with ⟨tc, tt⟩
          simp [ht, synth_layer, provided, placed?, outcome_type, fren_spec] at h2
          simp [parens_faithful?, ih hv.1.1, hd, ht, h2.1, h2.2]

/-- `thir.algorithmic.unique`. -/
theorem hir_table_unique (symb : Snoc Entry) (left right : Snoc HirRow)
    (hl : hir_rows_valid? symb left = true) (hr : hir_rows_valid? symb right = true)
    (shape : hir_same_shape? left right = true) : left = right := by
  induction left generalizing right with
  | Empty =>
    cases right with
    | Empty => rfl
    | Extend _ _ => simp [hir_same_shape?] at shape
  | Extend earlier l ih =>
    cases right with
    | Empty => simp [hir_same_shape?] at shape
    | Extend rearlier r =>
      simp only [hir_same_shape?, decide_eq_true_eq] at shape
      obtain ⟨⟨hform, hcontext⟩, hrest⟩ := shape
      simp only [hir_rows_valid?, decide_eq_true_eq] at hl hr
      have heq := ih rearlier hl.1.1 hr.1.1 hrest
      subst heq
      rcases l with ⟨lf, lc, lt⟩
      rcases r with ⟨rf, rc, rt⟩
      simp only at hform hcontext
      subst hform; subst hcontext
      have hl2 := hl.2
      have hr2 := hr.2
      simp only at hl2 hr2
      cases hd : desugar_rows earlier with
      | none => simp [hd] at hl2
      | some core =>
        cases ha : hir_annotate core lf with
        | none => simp [hd, ha] at hl2
        | some form =>
          simp only [hd, ha, decide_eq_true_eq] at hl2 hr2
          have := hl2.symm.trans hr2
          simp at this
          rw [this]

/-- `thir.algorithmic.expression-sound`: the commuting square, by `types.derivation.unique-expression`. -/
theorem expression_sound_typing (symb : Snoc Entry) (ctx : Snoc Ty) (hir : Snoc HirRow)
    (core : Snoc Row) (pairs : Snoc Pair) (a b : Ty) (hs : synthesis? symb hir ctx a = true)
    (hc : derivation? symb core ctx b = true) (ha : desugars_alike? hir core pairs = true) :
    a = b := by
  have hd := desugaring_preserves_typing symb hir ctx a hs
  simp only [desugared_derivation?] at hd
  simp only [desugars_alike?] at ha
  cases hr : desugar_rows hir with
  | none => simp [hr] at hd
  | some desugared =>
    simp only [hr] at hd ha
    exact Spec.Language.Types.expression_unique symb ctx desugared core pairs a b
      (of_decide_eq_true hd) hc (of_decide_eq_true ha)

/-! ### The production operator modes -/

theorem algorithmic_unary_operand (op : UnaryOp) :
    coreType (unary_operand op) = FrenExpr.unaryOperand (coreUnary op) := by
  cases op <;> simp [coreType, coreUnary, FrenExpr.unaryOperand, fren_spec]

theorem algorithmic_binary_operand (op : BinaryOp) (left : Ty) :
    coreType (binary_operand op left) = FrenExpr.binaryOperand (coreBinary op) (coreType left) := by
  cases op <;> simp [coreType, coreBinary, binary_operand, FrenExpr.binaryOperand, integer_binary?,
    comparison?, boolean_binary?, fren_spec]

theorem algorithmic_binary_output (op : BinaryOp) :
    coreType (binary_output op) = FrenExpr.binaryResult (coreBinary op) := by
  cases op <;> simp [coreType, coreBinary, binary_output, FrenExpr.binaryResult, integer_binary?,
    fren_spec]

/-! ### The production checker's outcomes -/

/-- A type of this chapter as a production type, under a naming of the nominal types. -/
def prodType (ι : Fren.Seq String → FrenBase.ItemId) : Ty → FrenExpr.Ty
  | .Boolean => .bool
  | .Integer => .int
  | .Nominal owner => .enum (ι owner)

/-- What a production result decides: the type of the node, or the blamed origin and reason. -/
def verdict (r : FrenHirToThir.Pass.Result (FrenExpr.Expr .thir)) :
    Except (FrenExpr.OriginId × FrenHirToThir.Pass.Reason) FrenExpr.Ty :=
  match r with
  | .ok e => .ok e.ann
  | .error e => .error (e.origin, e.reason)

/-- The production reading of an outcome, where `site` gives the origin of each premise.
Only a type and a mismatch are read; the other faults belong to forms whose production
correspondence is open (`thir.algorithmic.production`). -/
def produced (ι : Fren.Seq String → FrenBase.ItemId) (site : Premise → FrenExpr.OriginId) :
    Outcome → Option (Except (FrenExpr.OriginId × FrenHirToThir.Pass.Reason) FrenExpr.Ty)
  | .Typed ty => some (.ok (prodType ι ty))
  | .Blamed premise (.Mismatch expected found) =>
    some (.error (site premise, .mismatch (prodType ι expected) (prodType ι found)))
  | .Blamed _ _ => none

theorem prodType_compatible (ι : Fren.Seq String → FrenBase.ItemId)
    (hι : Function.Injective ι) (a b : Ty) :
    (prodType ι a).compatible (prodType ι b) = true ↔ a = b := by
  rw [FrenExpr.ValueType.compatible_iff]
  cases a <;> cases b <;> simp [prodType, hι.eq_iff]

theorem prodType_unary_operand (ι : Fren.Seq String → FrenBase.ItemId) (op : UnaryOp) :
    prodType ι (unary_operand op) = FrenExpr.unaryOperand (coreUnary op) := by
  cases op <;> simp [prodType, coreUnary, FrenExpr.unaryOperand, fren_spec]

theorem prodType_binary_operand (ι : Fren.Seq String → FrenBase.ItemId) (op : BinaryOp)
    (left : Ty) :
    prodType ι (binary_operand op left) =
      FrenExpr.binaryOperand (coreBinary op) (prodType ι left) := by
  cases op <;> simp [prodType, coreBinary, binary_operand, FrenExpr.binaryOperand,
    integer_binary?, comparison?, boolean_binary?, fren_spec]

theorem prodType_binary_output (ι : Fren.Seq String → FrenBase.ItemId) (op : BinaryOp) :
    prodType ι (binary_output op) = FrenExpr.binaryResult (coreBinary op) := by
  cases op <;> simp [prodType, coreBinary, binary_output, FrenExpr.binaryResult,
    integer_binary?, fren_spec]

/-- `thir.algorithmic.step`, unary: `step` returns the outcome of `judge_unary`,
blaming the operand at its origin. -/
theorem step_unary (ι : Fren.Seq String → FrenBase.ItemId) (hι : Function.Injective ι)
    (env : FrenHirToThir.Pass.Env) (o : FrenExpr.OriginId) (a : FrenExpr.Ann .hir)
    (op : UnaryOp) (operand : Typing) (child : FrenHirToThir.Pass.Typing)
    (ctx : FrenHirToThir.Pass.Ctx) (te : FrenExpr.Expr .thir) (site : Premise → FrenExpr.OriginId)
    (hc : child ctx = .ok te) (ht : te.ann = prodType ι operand.ty)
    (hs : site .Operand = te.origin) :
    produced ι site (judge_unary op operand) =
      some (verdict (FrenHirToThir.Pass.step env o a (.unary (coreUnary op) child) ctx)) := by
  have hv : verdict (FrenHirToThir.Pass.step env o a (.unary (coreUnary op) child) ctx) =
      match FrenExpr.unary (coreUnary op) te.ann with
      | some ty => .ok ty
      | none => .error (te.origin, .mismatch (FrenExpr.unaryOperand (coreUnary op)) te.ann) := by
    simp only [FrenHirToThir.Pass.step, hc, Bind.bind, Except.bind]
    cases FrenExpr.unary (coreUnary op) te.ann <;> rfl
  rw [hv, ht]
  simp only [FrenExpr.unary, ← prodType_unary_operand ι, judge_unary, expect_type]
  by_cases h : operand.ty = unary_operand op
  · simp [h, (prodType_compatible ι hι _ _).2, produced]
  · have hn : (prodType ι operand.ty).compatible (prodType ι (unary_operand op)) = false :=
      Bool.eq_false_iff.2 fun hh => h ((prodType_compatible ι hι _ _).1 hh)
    simp [h, hn, produced, hs]


theorem expect_prodType (ι : Fren.Seq String → FrenBase.ItemId) (hι : Function.Injective ι)
    (env : FrenHirToThir.Pass.Env) (o : FrenExpr.OriginId) (expected found : Ty) :
    env.expect o (prodType ι expected) (prodType ι found) =
      if found = expected then .ok ()
      else .error ⟨env.item, o, .mismatch (prodType ι expected) (prodType ι found)⟩ := by
  unfold FrenHirToThir.Pass.Env.expect FrenHirToThir.Pass.Env.fail
  by_cases h : found = expected
  · simp [h, (prodType_compatible ι hι _ _).2]
  · have hn : (prodType ι found).compatible (prodType ι expected) = false :=
      Bool.eq_false_iff.2 fun hh => h ((prodType_compatible ι hι _ _).1 hh)
    simp [h, hn]

/-- `thir.algorithmic.step`, binary: `step` returns the outcome of `judge_binary`,
blaming the left and then the right operand at its origin. -/
theorem step_binary (ι : Fren.Seq String → FrenBase.ItemId) (hι : Function.Injective ι)
    (env : FrenHirToThir.Pass.Env) (o : FrenExpr.OriginId) (a : FrenExpr.Ann .hir)
    (op : BinaryOp) (left right : Typing) (l r : FrenHirToThir.Pass.Typing)
    (ctx : FrenHirToThir.Pass.Ctx) (tl tr : FrenExpr.Expr .thir)
    (site : Premise → FrenExpr.OriginId)
    (hl : l ctx = .ok tl) (hr : r ctx = .ok tr)
    (htl : tl.ann = prodType ι left.ty) (htr : tr.ann = prodType ι right.ty)
    (hsl : site .Left = tl.origin) (hsr : site .Right = tr.origin) :
    produced ι site (judge_binary op left right) =
      some (verdict (FrenHirToThir.Pass.step env o a (.binary (coreBinary op) l r) ctx)) := by
  simp only [FrenHirToThir.Pass.step, hl, hr, Bind.bind, Except.bind, htl, htr,
    ← prodType_binary_operand ι, expect_prodType ι hι, FrenExpr.binary, judge_binary, expect_type]
  by_cases h1 : left.ty = binary_operand op left.ty
  · by_cases h2 : right.ty = binary_operand op left.ty
    · simp [← h1, h2, (prodType_compatible ι hι _ _).2, produced, ← prodType_binary_output ι]
      rfl
    · have hn : (prodType ι right.ty).compatible (prodType ι left.ty) = false :=
        Bool.eq_false_iff.2 fun hh => h2 (h1 ▸ (prodType_compatible ι hι _ _).1 hh)
      have h2' : ¬right.ty = left.ty := fun hh => h2 (hh.trans h1)
      simp [← h1, h2', hn, produced, hsr]
      rfl
  · simp [h1, produced, hsl]
    rfl

/-- `thir.algorithmic.step`, conditional: `step` returns the outcome of `judge_if`,
blaming the condition and then the second branch at its origin. -/
theorem step_if (ι : Fren.Seq String → FrenBase.ItemId) (hι : Function.Injective ι)
    (env : FrenHirToThir.Pass.Env) (o : FrenExpr.OriginId) (a : FrenExpr.Ann .hir)
    (condition then_branch else_branch : Typing) (c y n : FrenHirToThir.Pass.Typing)
    (ctx : FrenHirToThir.Pass.Ctx) (tc ty tn : FrenExpr.Expr .thir)
    (site : Premise → FrenExpr.OriginId)
    (hc : c ctx = .ok tc) (hy : y ctx = .ok ty) (hn : n ctx = .ok tn)
    (htc : tc.ann = prodType ι condition.ty) (hty : ty.ann = prodType ι then_branch.ty)
    (htn : tn.ann = prodType ι else_branch.ty)
    (hsc : site .Condition = tc.origin) (hsn : site .ElseBranch = tn.origin) :
    produced ι site (judge_if condition then_branch else_branch) =
      some (verdict (FrenHirToThir.Pass.step env o a (.ite c y n) ctx)) := by
  have hb : (FrenExpr.ValueType.bool : FrenExpr.Ty) = prodType ι .Boolean := rfl
  simp only [FrenHirToThir.Pass.step, hc, hy, hn, Bind.bind, Except.bind, htc, hty, htn, hb,
    expect_prodType ι hι, judge_if, expect_type]
  by_cases h1 : condition.ty = .Boolean
  · by_cases h2 : else_branch.ty = then_branch.ty
    · simp [h1, h2, produced]
      rfl
    · simp [h1, h2, produced, hsn]
      rfl
  · simp [h1, produced, hsc]
    rfl

/-- `thir.algorithmic.step`, binding: `step` returns the outcome of `judge_let`, where
the binder is annotated `Bool` exactly when it carries the suffix, blaming the binder. -/
theorem step_let (ι : Fren.Seq String → FrenBase.ItemId) (hι : Function.Injective ι)
    (env : FrenHirToThir.Pass.Env) (o : FrenExpr.OriginId) (a : FrenExpr.Ann .hir)
    (value body : Typing) (b : FrenExpr.Binder) (v e : FrenHirToThir.Pass.Typing)
    (ctx : FrenHirToThir.Pass.Ctx) (tv te : FrenExpr.Expr .thir)
    (site : Premise → FrenExpr.OriginId)
    (hv : v ctx = .ok tv) (he : e (tv.ann :: ctx) = .ok te)
    (htv : tv.ann = prodType ι value.ty) (hte : te.ann = prodType ι body.ty)
    (hs : site .Binder = b.origin) :
    produced ι site (judge_let (if b.suffix = true then some .Boolean else none) value body) =
      some (verdict (FrenHirToThir.Pass.step env o a (.letE b v e) ctx)) := by
  have hb : (FrenExpr.ValueType.bool : FrenExpr.Ty) = prodType ι .Boolean := rfl
  simp only [FrenHirToThir.Pass.step, hv, Bind.bind, Except.bind, he]
  rw [htv, hb]
  simp only [expect_prodType ι hι, judge_let, expect_type]
  by_cases h1 : b.suffix = true
  · by_cases h2 : value.ty = .Boolean
    · simp [h1, h2, produced, ← hte]
      rfl
    · simp [h1, h2, produced, hs]
      rfl
  · simp [h1, produced, ← hte]
    rfl

/-- `thir.algorithmic.step`, parentheses: `step` returns the outcome of `judge_paren`. -/
theorem step_paren (ι : Fren.Seq String → FrenBase.ItemId) (symb : Snoc Entry) (rc : Snoc Ty)
    (env : FrenHirToThir.Pass.Env) (o : FrenExpr.OriginId) (a : FrenExpr.Ann .hir)
    (g : FrenExpr.Phase.Surface .hir) (inner : Typing) (e : FrenHirToThir.Pass.Typing)
    (ctx : FrenHirToThir.Pass.Ctx) (te : FrenExpr.Expr .thir)
    (site : Premise → FrenExpr.OriginId)
    (he : e ctx = .ok te) (hte : te.ann = prodType ι inner.ty) :
    produced ι site (judge_layer symb rc (.Paren inner)) =
      some (verdict (FrenHirToThir.Pass.step env o a (.paren g e) ctx)) := by
  simp only [FrenHirToThir.Pass.step, he, Bind.bind, Except.bind, produced, ← hte]
  rfl

/-- `thir.algorithmic.step`, bodies: `typeBody` returns the outcome of `judge_body`,
blaming the body at its origin. -/
theorem body_checked (ι : Fren.Seq String → FrenBase.ItemId) (hι : Function.Injective ι)
    (env : FrenHirToThir.Pass.Env) (ctx : FrenHirToThir.Pass.Ctx) (expected found : Ty)
    (body : FrenExpr.Expr .hir) (out : FrenExpr.Expr .thir)
    (site : Premise → FrenExpr.OriginId)
    (hf : FrenExpr.Expr.fold (FrenHirToThir.Pass.step env) body ctx = .ok out)
    (ht : out.ann = prodType ι found) (hs : site .Whole = out.origin) :
    produced ι site (judge_body expected found) =
      some (verdict (FrenHirToThir.Pass.typeBody env ctx (prodType ι expected) body)) := by
  simp only [FrenHirToThir.Pass.typeBody, hf, Bind.bind, Except.bind, ht,
    expect_prodType ι hι, judge_body, expect_type]
  by_cases h : found = expected
  · subst h
    simp [produced, verdict, pure, Except.pure, ht]
  · simp [h, produced, verdict, hs]

end Algorithmic

section CoverageCorrespondence

open spec.surface spec.names spec.types spec.patterns Spec.Language.Patterns

def ofList {α : Type} (l : List α) : Snoc α := l.foldl .Extend .Empty

theorem uncovered_toList {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    toList (uncovered _ cs arms) =
      (toList cs).filter (fun c => decide (c ∉ (toList arms).map (·.constructor))) := by
  induction cs with
  | Empty => simp [uncovered, toList]
  | Extend earlier last ih =>
    have hp := occurrences_pos_iff arms last
    have hn := occurrences_nonneg arms last
    simp only [uncovered, toList, List.filter_append, ← ih]
    by_cases h : occurrences _ arms last = 0
    · have : ∀ x ∈ toList arms, ¬ x.constructor = last := fun x hx hc => by
        have := hp.2 (List.mem_map.2 ⟨x, hx, hc⟩); omega
      simp [h, toList, List.filter_cons]
      exact this
    · have : ∃ x ∈ toList arms, x.constructor = last := List.mem_map.1 (hp.1 (by omega))
      simp [h, List.filter_cons]
      exact this

theorem production_missing_eq {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    (@FrenHirToThir.coverage (Fren.Seq String) ⟨fun x y => decide (x = y)⟩ (toList cs).toArray
      ((toList arms).map (·.constructor)).toArray).1.toList = toList (uncovered _ cs arms) := by
  rw [uncovered_toList]
  simp [FrenHirToThir.coverage]
  apply List.filter_congr
  intro c _
  by_cases h : c ∈ (toList arms).map (·.constructor) <;> simp_all

theorem repeats_fold {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) :
    ((toList arms).map (·.constructor)).foldl
      (fun (acc : List (Fren.Seq String) × List (Fren.Seq String)) t =>
        (acc.1 ++ [t], if acc.1.contains t then acc.2 ++ [t] else acc.2)) ([], []) =
      ((toList arms).map (·.constructor), toList (repeats _ arms)) := by
  induction arms with
  | Empty => simp [toList, repeats]
  | Extend earlier last ih =>
    have hp := occurrences_pos_iff earlier last.constructor
    have hn := occurrences_nonneg earlier last.constructor
    simp only [toList, List.map_append, List.foldl_append, ih, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, repeats]
    by_cases h : 0 < occurrences _ earlier last.constructor
    · have hm := hp.1 h
      simp [h, hm, toList]
    · have hm : last.constructor ∉ (toList earlier).map (·.constructor) := fun m => h (hp.2 m)
      simp [h, hm]

theorem fold_arrays (ts : List (Fren.Seq String)) (s r : Array (Fren.Seq String)) :
    (ts.foldl (fun (x : Array (Fren.Seq String) × Array (Fren.Seq String)) t =>
        (x.fst.push t, if x.fst.contains t = true then x.snd.push t else x.snd)) (s, r)).2.toList =
    (ts.foldl (fun (acc : List (Fren.Seq String) × List (Fren.Seq String)) t =>
        (acc.1 ++ [t], if acc.1.contains t then acc.2 ++ [t] else acc.2)) (s.toList, r.toList)).2 := by
  induction ts generalizing s r with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have := ih (s.push t) (if s.contains t = true then r.push t else r)
    rw [this]
    by_cases h : s.contains t = true
    · have hm : t ∈ s := by simpa using h
      simp [hm]
    · have hm : t ∉ s := by simpa using h
      simp [hm]

theorem production_repeated_eq {E : Type} [Inhabited E] (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    (@FrenHirToThir.coverage (Fren.Seq String) ⟨fun x y => decide (x = y)⟩ (toList cs).toArray
      ((toList arms).map (·.constructor)).toArray).2.toList = toList (repeats _ arms) := by
  have := repeats_fold arms
  simp only [FrenHirToThir.coverage]
  rw [← Array.foldl_toList, List.toList_toArray, fold_arrays]
  have h2 := congrArg Prod.snd this
  simpa using h2

theorem ofList_toList {α : Type} (s : Snoc α) : ofList (toList s) = s := by
  induction s with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [ofList] at ih
    simp only [toList, ofList, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]

/-- The production check, read through the adapters: the inventory and the written
patterns go in as arrays and the two lists come back as snoc sequences. -/
def productionCoverage {E : Type} (cs : Snoc (Fren.Seq String)) (arms : Snoc (ArmF E)) :
    Array (Fren.Seq String) × Array (Fren.Seq String) :=
  @FrenHirToThir.coverage (Fren.Seq String) ⟨fun x y => decide (x = y)⟩ (toList cs).toArray
    ((toList arms).map (·.constructor)).toArray

interp thir::production_missing := fun cs arms => ofList (productionCoverage cs arms).1.toList by
  intro constructors arms
  simp only [spec.thir.production_missing.agrees]
  have := production_missing_eq constructors arms
  simp only [productionCoverage, this, ofList_toList]
interp thir::production_repeated := fun arms => ofList (productionCoverage Snoc.Empty arms).2.toList by
  intro arms
  simp only [spec.thir.production_repeated.agrees]
  have := production_repeated_eq Snoc.Empty arms
  simp only [productionCoverage, this, ofList_toList]

/-- The arm that a constructor selects, as the evaluator and confirmation compute it. -/
def pickArm {E : Type} (arms : Snoc (ArmF E)) (c : Fren.Seq String) : Option (ArmF E) :=
  @FrenHirToThir.selectArm (Fren.Seq String) (ArmF E) ⟨fun x y => decide (x = y)⟩
    (toList arms).toArray (fun a => some a.constructor) c

theorem pickArm_eq_select {E : Type} [Inhabited E] (arms : Snoc (ArmF E)) (c : Fren.Seq String) :
    pickArm arms c = select _ arms c := by
  induction arms with
  | Empty => simp [pickArm, FrenHirToThir.selectArm, toList, select]
  | Extend earlier last ih =>
    have ih' := ih
    simp only [pickArm, FrenHirToThir.selectArm, List.find?_toArray] at ih' ⊢
    simp only [toList, List.find?_append, select, ← ih']
    cases hf : (toList earlier).find? (fun a => some a.constructor == some c) with
    | some f => simp
    | none =>
      by_cases h : last.constructor = c <;> simp [h]

end CoverageCorrespondence

section TerminationCorrespondence

open spec.surface spec.names spec.types spec.statics Spec.Language.Patterns

/-- The specification's item identities, with the equality that decides `=`. -/
abbrev itemBEq : BEq (Fren.Seq String) := ⟨fun x y => decide (x = y)⟩

attribute [local instance] itemBEq

/-- A size of the specification, as production holds it. -/
def prodSize : Size → FrenHirToThir.Termination.Size
  | .Same => .same
  | .Smaller => .smaller
  | .Unknown => .unknown

/-- A level of the specification is an integer; no negative level is bound. -/
def prodLevel : Option Int → Option Nat
  | some level => if 0 ≤ level then some level.toNat else none
  | none => none

/-- The written calls of the specification, as production holds them. -/
def prodCalls : spec.statics.Calls → FrenHirToThir.Termination.Calls (Fren.Seq String)
  | .Leaf => .leaf
  | .Both left right => .both (prodCalls left) (prodCalls right)
  | .Call callee arguments => .call callee ((toList arguments).map prodLevel)
  | .Let value body => .bind (prodLevel value) (prodCalls body)

/-- A function of the specification, as production judges it. -/
def prodFunction (function : Function) : FrenHirToThir.Termination.Function (Fren.Seq String) Ty :=
  ⟨function.item, toList function.parameters, decide (function.mark = .Unchecked),
    prodCalls function.body⟩

/-- A choice of decreasing parameters, as production holds it. Each chosen level of
`choices` is nonnegative, which `choices_eq` proves. -/
def prodChoice (choice : Snoc Chosen) : List (Fren.Seq String × Nat) :=
  (toList choice).map fun entry => (entry.function, entry.parameter.toNat)

theorem length_toList {α : Type} [Inhabited α] (xs : Snoc α) :
    length α xs = (toList xs).length := by
  induction xs with
  | Empty => rfl
  | Extend earlier last ih => simp [length, toList, ih]

theorem lookup_toList {α : Type} [Inhabited α] (xs : Snoc α) (level : Nat) :
    lookup α xs level = (toList xs)[level]? := by
  induction xs with
  | Empty => simp [lookup, toList]
  | Extend earlier last ih =>
    simp only [lookup, toList, ih, length_toList, List.getElem?_append]
    by_cases h : level = (toList earlier).length
    · simp [h]
    · have : ¬ ((level : Int) = ((toList earlier).length : Nat)) := by omega
      rw [if_neg this]
      by_cases hl : level < (toList earlier).length
      · simp [hl]
      · have : level - (toList earlier).length ≠ 0 := by omega
        simp [hl, this]

theorem prodSize_eq_smaller (size : Size) : prodSize size = .smaller ↔ size = .Smaller := by
  cases size <;> simp [prodSize]

theorem local_size_eq (sizes : Snoc Size) (level : Option Int) :
    prodSize (local_size sizes level) =
      FrenHirToThir.Termination.localSize ((toList sizes).map prodSize) (prodLevel level) := by
  cases level with
  | none => rfl
  | some index =>
    by_cases h : 0 ≤ index
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
      simp only [local_size, lookup_toList, prodLevel, h, if_true, Int.toNat_natCast,
        FrenHirToThir.Termination.localSize, List.getElem?_map]
      cases (toList sizes)[n]? <;> rfl
    · have := Spec.Language.NamesAndScope.lookup_none sizes index (fun hb => h hb.1)
      simp [local_size, this, prodLevel, h, FrenHirToThir.Termination.localSize, prodSize]

theorem parameter_sizes_eq (parameters : Snoc Ty) (decreasing : Nat) :
    (toList (parameter_sizes parameters decreasing)).map prodSize =
      FrenHirToThir.Termination.parameterSizes (toList parameters) decreasing := by
  induction parameters with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [FrenHirToThir.Termination.parameterSizes] at ih
    simp only [parameter_sizes, toList, List.map_append, ih, FrenHirToThir.Termination.parameterSizes,
      List.length_append, List.length_cons, List.length_nil, List.range_succ, length_toList]
    by_cases h : (toList earlier).length = decreasing
    · simp [h, prodSize]
    · have : ¬ (((toList earlier).length : Int) = decreasing) := by omega
      simp [h, this, prodSize]

theorem argument_guarded_eq (sizes : Snoc Size) (arguments : Snoc (Option Int)) (parameter : Nat) :
    argument_guarded? sizes arguments parameter =
      FrenHirToThir.Termination.argumentGuarded ((toList sizes).map prodSize) ((toList arguments).map prodLevel)
        parameter := by
  simp only [argument_guarded?, lookup_toList, FrenHirToThir.Termination.argumentGuarded, List.getElem?_map]
  cases (toList arguments)[parameter]? with
  | none => simp
  | some argument =>
    simp only [Fren.Prelude.Option.some.x0, ↓reduceIte, Option.map_some, ← local_size_eq]
    generalize local_size sizes argument = size
    cases size <;> simp [prodSize]

theorem chosen_eq (choice : Snoc Chosen) (item : Fren.Seq String)
    (h : ∀ entry ∈ toList choice, 0 ≤ entry.parameter) :
    chosen choice item = (FrenHirToThir.Termination.chosen (prodChoice choice) item).map Int.ofNat := by
  induction choice with
  | Empty => rfl
  | Extend earlier last ih =>
    have hl := h last (by simp [toList])
    have := ih fun entry he => h entry (by simp [toList, he])
    simp only [prodChoice] at this
    simp only [chosen, prodChoice, toList, List.map_append, List.map_cons, List.map_nil,
      FrenHirToThir.Termination.chosen_append, this]
    by_cases hi : last.function = item
    · simp [hi, Int.toNat_of_nonneg hl]
    · simp [hi]

theorem calls_guarded_eq (choice : Snoc Chosen) (calls : spec.statics.Calls)
    (h : ∀ entry ∈ toList choice, 0 ≤ entry.parameter) (sizes : Snoc Size) :
    calls_guarded? choice sizes calls =
      FrenHirToThir.Termination.callsGuarded (prodChoice choice) ((toList sizes).map prodSize) (prodCalls calls) := by
  induction calls generalizing sizes with
  | Leaf => rfl
  | Both left right ihl ihr =>
    simp [calls_guarded?, prodCalls, FrenHirToThir.Termination.callsGuarded, ihl, ihr]
  | Call callee arguments =>
    simp only [calls_guarded?, prodCalls, FrenHirToThir.Termination.callsGuarded, chosen_eq choice callee h]
    cases FrenHirToThir.Termination.chosen (prodChoice choice) callee with
    | none => simp
    | some parameter => simpa using argument_guarded_eq sizes arguments parameter
  | Let value body ih =>
    simp only [calls_guarded?, prodCalls, FrenHirToThir.Termination.callsGuarded, ih, toList, List.map_append,
      List.map_cons, List.map_nil, local_size_eq]

theorem body_guarded_eq (choice : Snoc Chosen) (function : Function)
    (h : ∀ entry ∈ toList choice, 0 ≤ entry.parameter) :
    body_guarded? choice function =
      FrenHirToThir.Termination.bodyGuarded (prodChoice choice) (prodFunction function) := by
  simp only [body_guarded?, FrenHirToThir.Termination.bodyGuarded, prodFunction, chosen_eq choice function.item h]
  cases FrenHirToThir.Termination.chosen (prodChoice choice) function.item with
  | none => simp
  | some parameter =>
    simp [calls_guarded_eq choice function.body h, parameter_sizes_eq]

theorem choice_guarded_eq (choice : Snoc Chosen) (group : Snoc Function)
    (h : ∀ entry ∈ toList choice, 0 ≤ entry.parameter) :
    choice_guarded? choice group =
      FrenHirToThir.Termination.choiceGuarded (prodChoice choice) ((toList group).map prodFunction) := by
  induction group with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [FrenHirToThir.Termination.choiceGuarded] at ih
    simp only [choice_guarded?, FrenHirToThir.Termination.choiceGuarded, toList, List.map_append, List.all_append,
      List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, ih,
      body_guarded_eq choice last h, Bool.decide_and, Bool.decide_eq_true]
    exact Bool.and_comm _ _

theorem extended_choices_toList (onto found : Snoc (Snoc Chosen)) (entry : Chosen) :
    toList (extended_choices onto found entry) =
      toList onto ++ (toList found).map (Snoc.Extend · entry) := by
  induction found with
  | Empty => simp [extended_choices, toList]
  | Extend earlier last ih => simp [extended_choices, toList, ih]

theorem parameter_choices_toList (found : Snoc (Snoc Chosen)) (item : Fren.Seq String)
    (candidates : Snoc Ty) :
    toList (parameter_choices found item candidates) =
      (List.range (toList candidates).length).flatMap fun level =>
        (toList found).map (Snoc.Extend · ⟨item, level⟩) := by
  induction candidates with
  | Empty => simp [parameter_choices, toList]
  | Extend fewer last ih =>
    simp [parameter_choices, toList, extended_choices_toList, ih, List.range_succ,
      length_toList]

theorem choices_eq (group : Snoc Function) :
    (toList (choices group)).map prodChoice = FrenHirToThir.Termination.choices ((toList group).map prodFunction) ∧
      ∀ choice ∈ toList (choices group), ∀ entry ∈ toList choice, 0 ≤ entry.parameter := by
  induction group with
  | Empty => simp [choices, toList, prodChoice, FrenHirToThir.Termination.choices]
  | Extend earlier last ih =>
    constructor
    · simp only [choices, parameter_choices_toList, toList, List.map_append, List.map_cons,
        List.map_nil, FrenHirToThir.Termination.choices_append, ← ih.1, List.map_flatMap, List.map_map]
      simp [prodFunction, prodChoice, toList, Function.comp_def]
    · intro choice hc entry he
      simp only [choices, parameter_choices_toList, List.mem_flatMap, List.mem_map] at hc
      obtain ⟨level, -, prior, hp, rfl⟩ := hc
      simp only [toList, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ih.2 prior hp entry he
      · exact Int.natCast_nonneg level

theorem some_guarded_eq (candidates : Snoc (Snoc Chosen)) (group : Snoc Function)
    (h : ∀ choice ∈ toList candidates, ∀ entry ∈ toList choice, 0 ≤ entry.parameter) :
    some_guarded? candidates group =
      ((toList candidates).map prodChoice).any
        (FrenHirToThir.Termination.choiceGuarded · ((toList group).map prodFunction)) := by
  induction candidates with
  | Empty => rfl
  | Extend earlier last ih =>
    have := ih fun choice hc => h choice (by simp [toList, hc])
    simp only [some_guarded?, toList, List.map_append, List.any_append, List.map_cons,
      List.map_nil, List.any_cons, List.any_nil, Bool.or_false, this,
      choice_guarded_eq last group (h last (by simp [toList])), Bool.decide_or,
      Bool.decide_eq_true]
    exact Bool.or_comm _ _

theorem structural_eq (group : Snoc Function) :
    structural? group = FrenHirToThir.Termination.structural ((toList group).map prodFunction) := by
  obtain ⟨hc, hn⟩ := choices_eq group
  simp only [structural?, some_guarded_eq (choices group) group hn, hc, FrenHirToThir.Termination.structural,
    Bool.decide_eq_true]

theorem opted_out_eq (covered : Snoc Function) :
    opted_out? covered = FrenHirToThir.Termination.optedOut ((toList covered).map prodFunction) := by
  induction covered with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [FrenHirToThir.Termination.optedOut] at ih
    simp only [opted_out?, FrenHirToThir.Termination.optedOut, toList, List.map_append, List.any_append,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, ih,
      Bool.decide_or, Bool.decide_eq_true]
    exact Bool.or_comm _ _

theorem group_passes_eq (group : Snoc Function) :
    group_passes? group = FrenHirToThir.Termination.groupPassesNow ((toList group).map prodFunction) := by
  rw [← FrenHirToThir.Termination.groupPasses_eq_now]
  rw [FrenHirToThir.Termination.groupPasses, ← structural_eq, ← opted_out_eq]
  simp [group_passes?]

theorem passes_alone_eq (function : Function) :
    passes_alone? function = FrenHirToThir.Termination.passesAlone (prodFunction function) := by
  simp [passes_alone?, opted_out?, FrenHirToThir.Termination.passesAlone, prodFunction]

/-- The production judgment of a group, read through the adapters. `judgeRecursion`
calls this function on the group that it extracts. -/
def productionGroupPasses (group : Snoc Function) : Bool :=
  FrenHirToThir.Termination.groupPassesNow ((toList group).map prodFunction)

interp thir::production_group_passes? := fun group => productionGroupPasses group by
  intro group
  simp only [spec.thir.production_group_passes?.agrees, productionGroupPasses, group_passes_eq]
interp thir::production_structural? := fun group =>
    FrenHirToThir.Termination.structural ((toList group).map prodFunction) by
  intro group
  simp only [spec.thir.production_structural?.agrees, structural_eq]
interp thir::production_passes_alone? := fun function =>
    FrenHirToThir.Termination.passesAlone (prodFunction function) by
  intro function
  simp only [spec.thir.production_passes_alone?.agrees, passes_alone_eq]

end TerminationCorrespondence

end Spec.Compiler.Thir

open spec.surface spec.names spec.types spec.algorithmic in
impl first_arm_proof: first_arm for (arms : Snoc (ArmF Typing)) (ctx : Snoc Ty) (ty : Ty) {
  arms := arms, ctx := ctx, ty := ty, holds? := true
} by
  intro arms ctx ty _
  simp only [first_arm.ensures, first_arm.ensure.output, first_arm.ensure.typed]
  refine ⟨trivial, ?_⟩
  by_cases hne : arms = .Empty
  · simp [first_typed?, hne]
  · cases hb : arm_bodies? arms ctx ty with
    | false => simp [first_typed?, hb]
    | true => simp [first_typed?, Spec.Compiler.Thir.first_arm_typed arms ctx ty hne hb]

open spec.surface spec.names spec.types spec.algorithmic in
impl desugaring_preserves_proof: desugaring_preserves for (symb : Snoc Entry)
    (rows : Snoc HirRow) (ctx : Snoc Ty) (ty : Ty) {
  symb := symb, rows := rows, ctx := ctx, ty := ty, holds? := true
} by
  intro symb rows ctx ty _
  simp only [desugaring_preserves.ensures, desugaring_preserves.ensure.output,
    desugaring_preserves.ensure.typed]
  exact ⟨trivial, Spec.Compiler.Thir.desugaring_preserves_typing symb rows ctx ty⟩

open spec.surface spec.names spec.types spec.algorithmic in
impl desugaring_keeps_rows_proof: desugaring_keeps_rows for (rows : Snoc HirRow) {
  rows := rows, holds? := true
} by
  intro rows _
  simp only [desugaring_keeps_rows.ensures, desugaring_keeps_rows.ensure.output,
    desugaring_keeps_rows.ensure.same]
  refine ⟨trivial, ?_⟩
  cases hd : desugar_rows rows with
  | none => simp
  | some core =>
    simp
    intro h
    rw [← h]
    exact Spec.Compiler.Thir.desugar_length rows core hd

open spec.surface spec.names spec.types spec.algorithmic in
impl desugaring_reflects_proof: desugaring_reflects for (symb : Snoc Entry)
    (rows : Snoc HirRow) {
  symb := symb, rows := rows, holds? := true
} by
  intro symb rows _
  simp only [desugaring_reflects.ensures, desugaring_reflects.ensure.output,
    desugaring_reflects.ensure.exact]
  refine ⟨trivial, ?_⟩
  have hiff : hir_rows_valid? symb rows = true ↔
      (desugared_valid? symb rows = true ∧ parens_faithful? rows = true) := by
    constructor
    · intro hv
      obtain ⟨core, hd, hc⟩ := Spec.Compiler.Thir.desugar_valid symb rows hv
      exact ⟨by simp [desugared_valid?, hd, hc],
        Spec.Compiler.Thir.hir_valid_faithful symb rows hv⟩
    · intro h
      cases hd : desugar_rows rows with
      | none => simp [desugared_valid?, hd] at h
      | some core =>
        exact Spec.Compiler.Thir.desugaring_reflects_typing symb rows core h.2 hd
          (by simpa [desugared_valid?, hd] using h.1)
  simpa using hiff

open spec.surface spec.names spec.types spec.algorithmic in
impl arguments_judged_proof: arguments_judged for (args : Snoc Typing) (params : Snoc Ty)
    (rest : Outcome) {
  args := args, params := params, rest := rest, holds? := true
} by
  intro args params rest _
  simp only [arguments_judged.ensures, arguments_judged.ensure.output,
    arguments_judged.ensure.accepted, arguments_judged.ensure.rejected]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    have := Spec.Compiler.Thir.arguments_accepted args params rest h
    simp [this.1, this.2]
  · intro h
    have := Spec.Compiler.Thir.arguments_rejected args params rest (by simpa using h.1)
      (by simpa using h.2)
    simp [this]

open spec.surface spec.names spec.types spec.algorithmic in
impl arms_judged_proof: arms_judged for (symb : Snoc Entry) (owner : Fren.Seq String) (common : Ty)
    (arms : Snoc (ArmF Typing)) (ctx : Snoc Ty) (rest : Outcome) {
  symb := symb, owner := owner, common := common, arms := arms, ctx := ctx, rest := rest,
  holds? := true
} by
  intro symb owner common arms ctx rest _
  simp only [arms_judged.ensures, arms_judged.ensure.output, arms_judged.ensure.accepted,
    arms_judged.ensure.rejected]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    have := Spec.Compiler.Thir.arms_accepted symb owner common arms ctx rest h.1 h.2
    simp [this.1, this.2]
  · intro h
    have := Spec.Compiler.Thir.arms_rejected symb owner common arms ctx rest h.1 h.2
    simp [this]

open spec.surface spec.names spec.types spec.algorithmic in
impl match_agrees_proof: match_agrees for (symb : Snoc Entry) (ctx : Snoc Ty)
    (scrutinee : Typing) (arms : Snoc (ArmF Typing)) (ty : Ty) {
  symb := symb, ctx := ctx, scrutinee := scrutinee, arms := arms, ty := ty, holds? := true
} by
  intro symb ctx scrutinee arms ty _
  simp only [match_agrees.ensures, match_agrees.ensure.output, match_agrees.ensure.exact]
  refine ⟨trivial, ?_⟩
  have hiff : synth_layer symb ctx (.Core (.Match scrutinee arms)) = some ty ↔
      rule? symb ctx (.Match scrutinee arms) ty = true := by
    rw [Spec.Compiler.Thir.synth_layer_core]
    exact ⟨Spec.Compiler.Thir.synth_core_sound symb ctx _ ty,
      Spec.Compiler.Thir.synth_core_complete symb ctx _ ty⟩
  simpa using hiff

open spec.surface spec.names spec.types spec.algorithmic in
impl expression_sound_proof: expression_sound for (symb : Snoc Entry) (ctx : Snoc Ty)
    (hir : Snoc HirRow) (core : Snoc Row) (pairs : Snoc Pair) (a b : Ty) {
  symb := symb, ctx := ctx, hir := hir, core := core, pairs := pairs, a := a, b := b,
  holds? := true
} by
  intro symb ctx hir core pairs a b _
  simp only [expression_sound.ensures, expression_sound.ensure.output,
    expression_sound.ensure.agrees]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Compiler.Thir.expression_sound_typing symb ctx hir core pairs a b h.1.1 h.1.2 h.2

open spec.surface spec.names spec.types spec.algorithmic in
impl expression_unique_proof: expression_unique for (symb : Snoc Entry) (ctx : Snoc Ty)
    (left right : Snoc HirRow) (pairs : Snoc Pair) (a b : Ty) {
  symb := symb, ctx := ctx, left := left, right := right, pairs := pairs, a := a, b := b,
  holds? := true
} by
  intro symb ctx left right pairs a b _
  simp only [expression_unique.ensures, expression_unique.ensure.output,
    expression_unique.ensure.unique]
  refine ⟨trivial, ?_⟩
  intro h
  have hr := Spec.Compiler.Thir.desugaring_preserves_typing symb right ctx b h.1.2
  have ha := h.2
  simp only [desugarings_alike?] at ha
  simp only [desugared_derivation?] at hr
  cases hd : desugar_rows right with
  | none => simp [hd] at ha
  | some core =>
    simp only [hd] at ha hr
    exact Spec.Compiler.Thir.expression_sound_typing symb ctx left core pairs a b h.1.1
      (of_decide_eq_true hr) (of_decide_eq_true ha)

open spec.surface spec.names spec.types spec.algorithmic in
impl judged_examples_proof: judged_examples { holds? := true } by
  intro _
  simp only [judged_examples.ensures, judged_examples.ensure.output,
    judged_examples.ensure.literal, judged_examples.ensure.unbound,
    judged_examples.ensure.not_value, judged_examples.ensure.operand,
    judged_examples.ensure.left, judged_examples.ensure.right, judged_examples.ensure.equality,
    judged_examples.ensure.arity, judged_examples.ensure.argument,
    judged_examples.ensure.not_callable, judged_examples.ensure.local_callee,
    judged_examples.ensure.binder, judged_examples.ensure.condition,
    judged_examples.ensure.else_branch, judged_examples.ensure.scrutinee,
    judged_examples.ensure.no_arms, judged_examples.ensure.foreign_pattern,
    judged_examples.ensure.pattern, judged_examples.ensure.later_body,
    judged_examples.ensure.paren, judged_examples.ensure.body]
  decide

open spec.surface spec.names spec.types spec.algorithmic in
impl paren_true_proof: paren_true { holds? := true } by
  intro _
  simp only [paren_true.ensures, paren_true.ensure.output, paren_true.ensure.accepted,
    paren_true.ensure.desugared, paren_true.ensure.preserved, paren_true.ensure.smaller,
    paren_true.ensure.alike]
  decide

open spec.surface spec.names spec.types spec.algorithmic in
impl synthesis_unique_proof: synthesis_unique for (symb : Snoc Entry)
    (left right : Snoc HirRow) {
  symb := symb, left := left, right := right, holds? := true
} by
  intro symb left right _
  simp only [synthesis_unique.ensures, synthesis_unique.ensure.output,
    synthesis_unique.ensure.equal]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Compiler.Thir.hir_table_unique symb left right h.1.1 h.1.2 h.2

open spec.surface spec.names spec.types spec.algorithmic in
impl unfaithful_paren_proof: unfaithful_paren { holds? := true } by
  intro _
  simp only [unfaithful_paren.ensures, unfaithful_paren.ensure.output,
    unfaithful_paren.ensure.desugaring_valid, unfaithful_paren.ensure.table_invalid,
    unfaithful_paren.ensure.excluded]
  decide

set_option fren.requireEvidence "trusted" in
#fren_trace
