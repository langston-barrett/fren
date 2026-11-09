module

public import FrenOir

public section
namespace FrenLirToOir
open FrenLir FrenOir FrenModule

inductive Failure where
  | invalidInput (reason : String)
  | unsupported (reason : String)
  | resourceExhausted (reason : String)
  | lowering (diagnostic : FrenDiag.Diagnostic)
  deriving Repr

abbrev Result := Except Failure

structure Leaf where
  origin : Origin
  path : List Nat
  frames : List Frame
  condition : Term
  prerequisites : List (List Nat)
  deriving Repr, BEq

/-- `available` contains earlier checks of this body. At guard/binding entry
we conservatively retain them as context prerequisites. Ordinary siblings do
not become Boolean guards. Paths distinguish equal conditions/occurrences. -/
@[expose] def walk : Nat → Verification → Option Origin → List Nat → List Frame →
    List (List Nat) → List (List Nat) → Result (List Leaf)
  | 0, _, _, _, _, _, _ => .error (.resourceExhausted "verification traversal depth")
  | n + 1, tree, origin, path, frames, available, required => do
    match tree with
    | .empty => return []
    | .check c =>
      let some o := origin | throw (.invalidInput "unattributed verification check")
      return [⟨o, path, frames, c, required⟩]
    | .both a b =>
      let left ← walk n a origin (path ++ [0]) frames available required
      let right ← walk n b origin (path ++ [1]) frames (available ++ left.map (·.path)) required
      return left ++ right
    | .branch c a b =>
      let yes ← walk n a origin (path ++ [0]) (frames ++ [.guard c true]) available (required ++ available)
      let no ← walk n b origin (path ++ [1]) (frames ++ [.guard c false]) available (required ++ available)
      return yes ++ no
    | .letE name ty v d body =>
      walk n body origin (path ++ [0]) (frames ++ [.binding name ty v d]) available (required ++ available)
    | .at o body => walk n body (some o) (path ++ [0]) frames available required

/-- All applications in both components, including unused binding values and
domains, refer to real definition equations. Exhaustion is an explicit error. -/
def applications : Nat → Term → Result (List FrenBase.ItemId)
  | 0, _ => .error (.resourceExhausted "term dependency traversal depth")
  | n + 1, term => do
    let visit := applications n
    match term with
    | .bool _ | .int _ | .constructor .. | .local .. => return []
    | .unary _ a | .at _ a => visit a
    | .binary _ a b => return (← visit a) ++ (← visit b)
    | .ite c a b => return (← visit c) ++ (← visit a) ++ (← visit b)
    | .app sig _ args => return sig.id :: (← args.mapM visit).flatten
    | .letE _ _ v d b => return (← visit v) ++ (← visit d) ++ (← visit b)

@[expose] def leaves (b : Body) : Result (List Leaf) :=
  walk 10000 b.term.verification none [] [] [] []

/-- A deliberately small sufficient test for structurally total domains. Free
parameters are total values. Locals use the actual let-domain component;
applications/divisor conditions are not guessed true. This is not a solver. -/
def knownTrue : Nat → List Bool → Term → Bool
  | 0, _, _ => false
  | n + 1, slots, term =>
    match term with
    | .bool true => true
    | .local _ i .domain => slots[i]?.getD false
    | .at _ a => knownTrue n slots a
    | .binary .and a b => knownTrue n slots a && knownTrue n slots b
    | .ite _ a b => knownTrue n slots a && knownTrue n slots b
    | .letE _ _ _ d b => knownTrue n (knownTrue n slots d :: slots) b
    | _ => false

@[expose] def structurallyTotal (b : Body) : Bool :=
  knownTrue 10000 (b.source.context.map (fun _ => true)) b.term.defined

theorem walk_both (n : Nat) (a b : Verification) (o : Option Origin)
    (path : List Nat) (frames : List Frame) (available required : List (List Nat)) :
    walk (n + 1) (.both a b) o path frames available required = (do
      let left ← walk n a o (path ++ [0]) frames available required
      let right ← walk n b o (path ++ [1]) frames (available ++ left.map (·.path)) required
      pure (left ++ right)) := rfl

theorem walk_check (n : Nat) (c : Term) (o : Origin) (path : List Nat)
    (frames : List Frame) (available required : List (List Nat)) :
    walk (n + 1) (.check c) (some o) path frames available required =
      .ok [⟨o, path, frames, c, required⟩] := rfl

theorem walk_empty (n : Nat) (o : Option Origin) (p : List Nat) (f : List Frame)
    (a r : List (List Nat)) : walk (n + 1) .empty o p f a r = .ok [] := rfl

theorem walk_at (n : Nat) (o : Origin) (old : Option Origin) (v : Verification)
    (p : List Nat) (f : List Frame) (a r : List (List Nat)) :
    walk (n + 1) (.at o v) old p f a r = walk n v (some o) (p ++ [0]) f a r := rfl

theorem walk_binding (n : Nat) (name : FrenAst.Token) (ty : FrenExpr.Ty) (v d : Term)
    (body : Verification) (o : Option Origin) (p : List Nat) (f : List Frame) (a r : List (List Nat)) :
    walk (n + 1) (.letE name ty v d body) o p f a r =
      walk n body o (p ++ [0]) (f ++ [.binding name ty v d]) a (r ++ a) := rfl

theorem walk_branch (n : Nat) (c : Term) (yes no : Verification) (o : Option Origin)
    (p : List Nat) (f : List Frame) (a r : List (List Nat)) :
    walk (n + 1) (.branch c yes no) o p f a r = (do
      let left ← walk n yes o (p ++ [0]) (f ++ [.guard c true]) a (r ++ a)
      let right ← walk n no o (p ++ [1]) (f ++ [.guard c false]) a (r ++ a)
      pure (left ++ right)) := rfl

end FrenLirToOir
