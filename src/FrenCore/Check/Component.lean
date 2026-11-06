-- keep-sorted start
import FrenCore.Check.Types
-- keep-sorted end

/-!
# Procedures and evaluation sites

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

structure VarSig where
  name : Name
  role : Role
  /-- Shown in counterexamples. -/
  isPub : Bool
  /-- A `det` variable. -/
  isDet : Bool := false
  deriving Inhabited

/-- Universally quantified: not chosen by the procedure (`Role.isUniversal`). -/
def VarSig.isIn (v : VarSig) : Bool := v.role.isUniversal

/-- The name of the second copy of variable `n`, for `determinism`: `n#'`,
whose text, unescaped, is `copySymbol` of `n`'s. No Fren identifier
contains `#`, so it is no variable's name (`cli::query_symbols`); `n'`
was, since an identifier may contain `'`. -/
def primed : Name → Name
  | .str p s => .str p (s ++ "#'")
  | n => .str n "#'"

/-- The variable that `n` is the second copy of (`primed`), if it is one. -/
def unprimed? (n : Name) : Option Name :=
  match n with
  | .str p s => if s.endsWith "#'" then some (.str p (s.dropEnd 2).toString) else none
  | _ => none

/-- A call, with formulas over the calling procedure's variables. -/
structure Inst (F : Type) where
  name : Name
  comp : Name
  bindings : F
  /-- The called procedure's assumptions, requirements and calls. -/
  behaviour : F
  /-- The called procedure's assumptions, each an obligation, after the
  constraints of its inputs' types (`Reqs/Check#call-assumptions`). -/
  assumes : Array (Name × F)
  /-- Which of `assumes` are its inputs' types' constraints, each with its
  type, as written. -/
  typed : Array (Name × String) := #[]

/-- Where an index or a table is written, which gives the hypotheses of its
definedness query (`check::definedness`), and of the questions about its
rows (`check::completeness`, `check::disjointness`). -/
inductive IndexPlace where
  | assume
  /-- A requirement, expectation, cover goal or definition. -/
  | prop
  /-- A binding of the call at this position. -/
  | binding (k : Nat)
  /-- The body or a postcondition of a function, or the value of a
  constant: the function's preconditions, and the conditions around it,
  which its goal already has. -/
  | body
  deriving Inhabited, BEq, Repr

/-- An index `q[i]` of a constraint, with the formula that it is in range
where it is evaluated: its guard implies its bounds. -/
structure IndexSite (F : Type) where
  /-- The constraint, the defined output, or the call whose binding it is in. -/
  prop : Name
  /-- Which index of it, in order. -/
  k : Nat
  place : IndexPlace
  goal : F
  /-- For a value given where a subset type is declared, rather than an
  index: that type, as written (`Reqs/Check#subset-types`). -/
  subsetTy? : Option String := none
  /-- Distributed Boolean clauses cannot justify their own evaluation sites. -/
  excludeSelf : Bool := false
  deriving Inhabited

/-- A question about the cases of a table or a `match` (`TableGoal`), where
it is written: its site's goal is the question, under its guard. -/
structure TableSite (F : Type) where
  /-- Its place, the item it is in, and which of the item's questions
  about its tables it is, in order. -/
  site : IndexSite F
  goal : TableGoal
  deriving Inhabited

/-- The check that answers a question about a split's cases, or about an
application's arguments. -/
def TableGoal.kind : TableGoal → CheckKind
  | .completeness _ => .completeness
  | .disjointness .. => .disjointness
  | .precondition .. => .precondition
  | .reachability .. => .reachability

/-- The rows that a question is about, for `disjointness`. -/
def TableGoal.rows? : TableGoal → Option (Nat × Nat)
  | .disjointness _ i j => some (i, j)
  | _ => none

/-- The function and precondition that a question is about, for
`precondition`. -/
def TableGoal.target? : TableGoal → Option (Name × Name)
  | .precondition f p => some (f, p)
  | _ => none

/-- A procedure, with its items as backend formulas over its variables. -/
structure Comp (F : Type) where
  path : Name
  vars : Array VarSig
  assumes : Array (Name × F)
  reqs : Array (Name × F)
  expects : Array (Name × F)
  covers : Array (Name × F) := #[]
  insts : Array (Inst F) := #[]
  /-- The triggers of the `ensure`s and `expect`s that have one. -/
  triggers : Array (Name × F)
  /-- Each defined output, with the equation `d = e` and its definition
  `e`, each mentioning only earlier ones (`check::definitions`). -/
  defs : Array (Name × F × F) := #[]
  indexes : Array (IndexSite F) := #[]
  /-- Some variable's type, its own or a call's, is or contains an
  abstract type. -/
  typesInterpreted : Bool := false
  /-- A declaration checks existence in every interpretation. With no variable
  interpretation, a direct satisfiability witness answers the same question. -/
  inhabitation : Bool := false
  /-- The questions about the cases of its tables and `match`es, and about
  the arguments of its applications of functions with preconditions. -/
  tables : Array (TableSite F) := #[]
  /-- For the body of a defined function: its postconditions, each a claim
  over its parameters (`check::postcondition`); its preconditions are its
  `assumes`. -/
  posts : Array (Name × F) := #[]
  /-- This function is checked by simultaneous Hoare induction. -/
  recursive : Bool := false
  /-- For the body or contract of a function: the function, which the
  results of `postcondition` name. -/
  fn? : Option Name := none
  /-- For the contract of a generic function without a body: it is checked
  once, at its type parameters, for every type (`F0653`). -/
  generic : Bool := false
  /-- Source Boolean groups, whose owners match named assumptions or requirements. -/
  branchGroups : Array (BranchGroup F) := #[]
  memberGroups : Array (MemberGroup F) := #[]
  /-- For an expectation of a trait: the trait's laws, each a closed
  formula, which every query with the assumptions and calls among its
  hypotheses has before them (`Comp.hyps`), but realizability's, which sees
  the item without them (`Comp.forKind`, `check::query_hypotheses`). -/
  laws : Array (Name × F) := #[]
  /-- The trait whose laws `laws` are. -/
  lawsOf : Name := .anonymous

end Fren.Core
