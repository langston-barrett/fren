import Fren.Impl
import Fren.Literate
import FrenHirToThir

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

/-- Every written value or callee occurrence has the exact context and meaning. -/
def OccurrenceTyping (input : FrenModule.Resolved) (out : FrenModule.Typed) : Prop :=
  ∀ body ∈ out.bodies.toList, ∀ ctx expr,
    AtContext input out.signatures body.context body.expression ctx expr →
    ∃ occurrence ∈ body.occurrences.toList,
      occurrence.expression = expr ∧ occurrence.context = ctx ∧
      match occurrence.type with
      | .value ty => FrenHirToThir.HasValue input out.signatures ctx expr ty
      | .callable sig => ∃ path,
          expr = .name path ∧ FrenHirToThir.Selects input ctx path .expression (.item sig.id) ∧
          FrenHirToThir.signatureAt out.signatures sig.id = some sig

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
    BodyInventory input out ∧ BodyTyping input out ∧ OccurrenceTyping input out

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

end Spec.Compiler.Thir
