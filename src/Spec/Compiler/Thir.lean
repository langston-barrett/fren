import Fren.Impl
import Fren.Literate
import Fren.Trace
import FrenWalking
import FrenBase.Binding
import FrenExpr
import Spec.Language.Types

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
def nearest {α : Type} : spec.types.Snoc α → List α
  | .Empty => []
  | .Extend earlier x => x :: nearest earlier

/-- The level-to-index refinement: the Core entry at level `level` is the
production entry at nearest-first index `|xs| - 1 - level`. -/
theorem lookup_nearest {α : Type} [Inhabited α] (xs : spec.types.Snoc α) (level : Nat)
    (bound : level < spec.types.length _ xs) :
    spec.types.lookup _ xs level =
      FrenBase.Binding.lookup (nearest xs) (spec.types.length _ xs - 1 - level) := by
  induction xs with
  | Empty => simp [spec.types.length] at bound
  | Extend earlier x ih =>
    simp only [spec.types.length] at bound ⊢
    simp only [spec.types.lookup, nearest]
    by_cases h : level = spec.types.length _ earlier
    · subst h; simp
    · have lt : level < spec.types.length _ earlier := by omega
      have eq : spec.types.length _ earlier + 1 - 1 - level =
          (spec.types.length _ earlier - 1 - level) + 1 := by omega
      simp only [Int.natCast_inj, h, if_false, eq, FrenBase.Binding.lookup_older]
      exact ih lt

/-- The Core's types as the generic production type carrier. -/
def coreType : spec.types.Ty → FrenExpr.ValueType (Fren.Seq String)
  | .Boolean => .bool
  | .Integer => .int
  | .Nominal owner => .enum owner

def coreUnary : spec.surface.UnaryOp → FrenAst.UnaryOp
  | .Neg => .neg | .Not => .not

def coreBinary : spec.surface.BinaryOp → FrenAst.BinaryOp
  | .Add => .add | .Sub => .sub | .Mul => .mul | .Div => .div | .Mod => .mod
  | .Lt => .lt | .Le => .le | .Gt => .gt | .Ge => .ge
  | .And => .and | .Or => .or | .Iff => .iff | .Eq => .eq | .Ne => .ne

/-- The Core unary rule agrees with the actual generic primitive. -/
theorem core_unary (op : spec.surface.UnaryOp) (operand result : spec.types.Ty) :
    @FrenExpr.unary (Fren.Seq String) ⟨fun x y => decide (x = y)⟩
      (coreUnary op) (coreType operand) = some (coreType result) ↔
        spec.types.unary_type? op operand result := by
  cases op <;> cases operand <;> cases result <;>
    simp [coreType, coreUnary, FrenExpr.unary, FrenExpr.unaryOperand,
      FrenExpr.ValueType.compatible, fren_spec]

/-- Every operator and nominal identity is covered; there is no bounded enum domain. -/
theorem core_binary (op : spec.surface.BinaryOp) (left right result : spec.types.Ty) :
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
  | .Add => .add | .Sub => .sub | .Mul => .mul | .Div => .div | .Mod => .mod
  | .Lt => .lt | .Le => .le | .Gt => .gt | .Ge => .ge
  | .And => .and | .Or => .or | .Iff => .iff | .Eq => .eq | .Ne => .ne

impl compatibility: compatible for
    (left right : spec.thir.ValueKind) (left_id right_id : Int) {
  left := left, right := right, left_id := left_id, right_id := right_id,
  same? := (primitiveType left left_id).compatible (primitiveType right right_id)
} by
  intro left right left_id right_id _
  cases left <;> cases right <;>
    simp [fren_spec, primitiveType, FrenExpr.ValueType.compatible, beq_iff_eq]

impl unary: unary for (op : spec.thir.UnaryTag) (operand : spec.thir.ValueKind) {
  op := op, operand := operand,
  accepted? := (FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).isSome,
  result := primitiveKind ((FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).getD .bool)
} by
  intro op operand _
  cases op <;> cases operand <;>
    simp [fren_spec, primitiveUnary, primitiveType, primitiveKind, FrenExpr.unary,
      FrenExpr.unaryOperand, FrenExpr.ValueType.compatible]

impl binary: binary for
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

end Spec.Compiler.Thir

set_option fren.requireEvidence "trusted" in
#fren_trace
