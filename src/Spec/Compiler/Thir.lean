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

/-- `thir.algorithmic.sound`, for the lift. -/
theorem synth_core_sound (symb : Snoc Entry) (ctx : Snoc Ty) (form : CoreF Typing) (ty : Ty)
    (h : synth_core symb ctx form = some ty) : rule? symb ctx form ty = true := by
  cases form with
  | Unary op operand =>
    cases op <;> simp [synth_core, provided, checked?, unary_operand, fren_spec] at h <;>
      simp [rule?, unary_rule?, unary_type?, fren_spec] <;> simp_all
  | Binary op left right =>
    cases op <;> simp [synth_core, provided, checked?, synthesized?, binary_operand, binary_output,
      integer_binary?, comparison?, boolean_binary?, fren_spec] at h <;>
      simp [rule?, binary_rule?, binary_type?, integer_binary?, comparison?, boolean_binary?,
        fren_spec] <;> simp_all
  | Constructor item =>
    cases hE : entry symb item with
    | none => simp [synth_core, hE, fren_spec] at h
    | some kind =>
      cases kind <;> simp [synth_core, hE, fren_spec] at h <;>
        simp [rule?, constructor_rule?, hE, fren_spec] <;> simp_all
  | Call item args =>
    cases hE : entry symb item with
    | none => simp [synth_core, hE, fren_spec] at h
    | some kind =>
      cases kind <;> simp [synth_core, provided, hE, fren_spec] at h <;>
        simp [rule?, call_rule?, hE, fren_spec] <;> simp_all
  | Match scrutinee arms =>
    rcases scrutinee with ⟨sc, sty⟩
    cases hf : first_body arms with
    | none => cases sty <;> simp [synth_core, hf, fren_spec] at h
    | some first =>
      have hne := first_body_nonempty arms first hf
      cases sty <;> simp [synth_core, provided, synthesized?, hf, fren_spec] at h
      obtain ⟨⟨⟨hs, hp⟩, hb⟩, ht⟩ := h
      subst ht
      simp [rule?, match_rule?, fren_spec, hs, hp, hb, hne]
  | Let annotation value body =>
    cases annotation <;>
      simp [synth_core, provided, value_typed?, checked?, synthesized?, fren_spec] at h <;>
      simp [rule?, let_rule?, let_annotated_rule?, fren_spec] <;> simp_all
  | _ =>
    simp [synth_core, provided, checked?, synthesized?, fren_spec] at h <;>
      simp [rule?, boolean_rule?, integer_rule?, local_rule?, if_rule?, fren_spec] <;> simp_all

/-- `thir.algorithmic.complete`, for the lift. -/
theorem synth_core_complete (symb : Snoc Entry) (ctx : Snoc Ty) (form : CoreF Typing) (ty : Ty)
    (h : rule? symb ctx form ty = true) : synth_core symb ctx form = some ty := by
  cases form with
  | Unary op operand =>
    cases op <;> simp [rule?, unary_rule?, unary_type?, fren_spec] at h <;>
      simp [synth_core, provided, checked?, unary_operand, fren_spec] <;> simp_all
  | Binary op left right =>
    cases op <;> simp [rule?, binary_rule?, binary_type?, integer_binary?, comparison?,
      boolean_binary?, fren_spec] at h <;>
      simp [synth_core, provided, checked?, synthesized?, binary_operand, binary_output,
        integer_binary?, comparison?, boolean_binary?, fren_spec] <;> simp_all
  | Constructor item =>
    cases hE : entry symb item with
    | none => simp [rule?, constructor_rule?, hE, fren_spec] at h
    | some kind =>
      cases kind <;> simp [rule?, constructor_rule?, hE, fren_spec] at h <;>
        simp [synth_core, hE, fren_spec] <;> simp_all
  | Call item args =>
    cases hE : entry symb item with
    | none => simp [rule?, call_rule?, hE, fren_spec] at h
    | some kind =>
      cases kind <;> simp [rule?, call_rule?, hE, fren_spec] at h <;>
        simp [synth_core, provided, hE, fren_spec] <;> simp_all
  | Match scrutinee arms =>
    rcases scrutinee with ⟨sc, sty⟩
    cases sty <;> simp [rule?, match_rule?, fren_spec] at h
    have hf := first_arm_typed arms ctx ty h.1.1.2 h.1.2
    simp [synth_core, provided, synthesized?, hf, fren_spec]
    simp_all
  | Let annotation value body =>
    cases annotation <;> simp [rule?, let_rule?, let_annotated_rule?, fren_spec] at h <;>
      simp [synth_core, provided, value_typed?, checked?, synthesized?, fren_spec] <;> simp_all
  | _ =>
    simp [rule?, boolean_rule?, integer_rule?, local_rule?, if_rule?, fren_spec] at h <;>
      simp [synth_core, provided, checked?, synthesized?, fren_spec] <;> simp_all

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
        simp only [ha, check_layer?, synth_layer, decide_eq_true_eq] at h2
        have hr := synth_core_sound symb rc typed rt h2
        exact ⟨.Extend core ⟨f, rc, rt⟩, by simp [desugar_rows, core_row, hd],
          by simp [rows_valid?, hc, hctx, ha, hr]⟩
    | Paren body =>
      simp only [hir_annotate] at h2
      cases hl : lookup _ core body with
      | none => simp [typing_at, hl] at h2
      | some d =>
        simp [typing_at, hl, check_layer?, synth_layer, provided, synthesized?, fren_spec] at h2
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
          simp [hir_rows_valid?, ih c hp.1 hd' hc.1.1, hd', hir_annotate, ha, check_layer?,
            synth_layer, hs, hctx]
      | Paren body =>
        cases hl : lookup _ c body with
        | none => simp [hd', hl] at hd
        | some d =>
          simp [hd', hl, core_row] at hd; subst hd
          simp only [rows_valid?, decide_eq_true_eq] at hc
          have hctx : ctx_ok? symb rc = true := hc.1.2
          simp [hd'] at hp2
          simp [hir_rows_valid?, ih c hp.1 hd' hc.1.1, hd', hir_annotate, hp2, check_layer?,
            synth_layer, provided, synthesized?, hctx, fren_spec]

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
          simp only [hd, ha, check_layer?, decide_eq_true_eq] at hl2 hr2
          have := hl2.symm.trans hr2
          simp at this
          rw [this]

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

end Algorithmic

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
    desugaring_reflects.ensure.typed]
  refine ⟨trivial, ?_⟩
  intro h
  cases hd : desugar_rows rows with
  | none => simp [desugared_valid?, hd] at h
  | some core =>
    exact Spec.Compiler.Thir.desugaring_reflects_typing symb rows core h.1 hd
      (by simpa [desugared_valid?, hd] using h.2)

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
