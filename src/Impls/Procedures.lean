-- keep-sorted start
import FrenCore.FnBlocks
import FrenCore.Procedures
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Function blocks (`Reqs/Lang/Items#function-blocks`) -/

namespace Fren.Impls

def toFnMemberKind : Fren.Core.FnMember → lang.FnMemberKind
  | .use => .Use
  | .assumption => .Assumption
  | .exists => .Exists
  | .let => .Let
  | .define => .Define
  | .call => .Call
  | .guarantee => .Guarantee
  | .claim => .Claim
  | .evidence => .Evidence

def toFnVerdict : Fren.Core.FnVerdict → lang.FnVerdict
  | .accepted => .Accepted
  | .notFunctions => .NotFunctions
  | .notYet => .NotYet

-- For every member of a function's block, written `det` or not: whether
-- the block takes it, as both front ends decide it.
impl fn_member: lang::fn_member for (m : Fren.Core.FnMember) (d : Bool) {
  member := toFnMemberKind m,
  det? := d,
  verdict := toFnVerdict (Fren.Core.fnMemberVerdict m d),
} by
  intro m d _
  cases m <;> cases d <;> simp [fren_spec, toFnMemberKind, toFnVerdict, Fren.Core.fnMemberVerdict]


/-! ## The order of a block's errors (`Reqs/Lang/Procedures#the-keyword-of-an-assumption`) -/

open Fren.Core (BlockCheck firstBlockError? firstItemError? firstPartError?)

def toBlockCheck : BlockCheck → lang.BlockCheck
  | .modifier => .Modifier
  | .syntax => .Syntax
  | .rejected => .Rejected

def ofBlockCheck : lang.BlockCheck → BlockCheck
  | .Modifier => .modifier
  | .Syntax => .syntax
  | .Rejected => .rejected

/-- The errors of a part, each of its kind, that `part_error`'s flags say
it has, in the order `order` of the kinds. -/
def partErrorsIn (order : List BlockCheck) (m s r : Bool) : List (BlockCheck × BlockCheck) :=
  order.filterMap fun kind =>
    let b := match kind with
      | .modifier => m | .syntax => s | .rejected => r
    if b then some (kind, kind) else none

/-- The errors of a part in the order the kinds are reported, which
`firstPartError?` must not rely on. -/
def partErrors (m s r : Bool) : List (BlockCheck × BlockCheck) := partErrorsIn BlockCheck.inOrder m s r

-- For every set of a part's errors, listed against the order they are
-- reported in, so that `firstPartError?` must choose among them: the one
-- that both front ends report.
impl part_error: lang::part_error for (m s r : Bool) {
  «modifier?» := m,
  «syntax?» := s,
  «rejected?» := r,
  reported := (firstPartError? (partErrors m s r).reverse).map toBlockCheck,
} by
  intro m s r
  cases m <;> cases s <;> cases r <;> decide

/-- `firstPartError?` reports the same error of a part whatever the order
of its list: the order the kinds are reported in, its reverse, and the
order in which the front ends list a clause's errors, an error of its own
syntax and of how it is written before whether the block takes it, after
an evidence setting's. -/
theorem firstPartError_any_order (m s r : Bool) :
    firstPartError? (partErrors m s r) = firstPartError? (partErrors m s r).reverse ∧
    firstPartError? (partErrors m s r) = firstPartError? (partErrorsIn [.syntax, .rejected, .modifier] m s r) := by
  cases m <;> cases s <;> cases r <;> decide

-- For the errors reported of two parts, the earlier and the later: the
-- one that both front ends report of the two, by `firstBlockError?`.
impl block_errors: lang::block_errors for (e l : Option lang.BlockCheck) {
  earlier := e,
  later := l,
  reported := (firstBlockError? [(e.map fun c => [(ofBlockCheck c, c)]).getD [], (l.map fun c => [(ofBlockCheck c, c)]).getD []]),
  «from_earlier?» := e.isSome,
} by
  intro e l
  rcases e with _ | ⟨_ | _ | _⟩ <;> rcases l with _ | ⟨_ | _ | _⟩ <;> decide

open Fren.Core (ClauseForm ClauseWord bareClauseMsg clauseKeywordError? clauseSyntaxError? preconditionReport?
  assumeRenamedMsg requireInGlobalMsg)

def toClauseWord : ClauseWord → lang.ClauseWord
  | .require => .Require
  | .assume => .Assume
  | .ensure => .Ensure
  | .expect => .Expect
  | .cover => .Cover

-- For each clause, in either block, read or not, and if read however it is
-- written: whether it has an error of its keyword and of how it is written,
-- as both front ends find them with `clauseKeywordError?` and
-- `clauseSyntaxError?`.
impl clause_errors: lang::clause_errors for (w : ClauseWord) (g r l b : Bool) {
  word := toClauseWord w,
  «global?» := g,
  «read?» := r,
  «labelled?» := l,
  «block_root?» := b,
  «keyword?» := (clauseKeywordError? g w).isSome,
  «syntax?» := (clauseSyntaxError? w (if r then some ⟨l, b⟩ else none)).isSome,
} by
  intro w g r l b
  cases w <;> cases g <;> cases r <;> cases l <;> cases b <;> decide

/-- What an item reports first, by `firstItemError?`'s choice between an
error of its syntax and one of a clause's keyword. -/
def toItemError : Option Bool → lang.ItemError
  | some true => .Syntax
  | some false => .Keyword
  | none => .NoError

open Fren.Core (ItemShape itemError?)

def toItemShape : ItemShape Unit → lang.ItemShape
  | .done => .End
  | .clause w g _ rest => .Clause (toClauseWord w) g (toItemShape rest)
  | .member m rest => .Member (toItemShape m) (toItemShape rest)

/-- An item of the shape `s` has a keyword error, as both front ends find
them (`ItemShape.keywordErrors`), iff some clause of it is written with the
other block's keyword, as `lang::any_wrong_keyword?` says. -/
theorem keywordErrors_any_wrong (s : ItemShape Unit) :
    (!s.keywordErrors.isEmpty) = lang.«any_wrong_keyword?» (toItemShape s) := by
  induction s with
  | done => simp [ItemShape.keywordErrors, toItemShape, fren_spec]
  | clause w g a rest ih =>
    cases w <;> cases g <;>
      simp_all [ItemShape.keywordErrors, toItemShape, toClauseWord, clauseKeywordError?, preconditionReport?, fren_spec,
        Fren.Core.ClauseWord.precondition?]
  | member m rest ihm ihr =>
    -- `simp_all` rewrites with it from the context.
    have _ : ∀ (a b : List (Fren.Core.Msg × Unit)), (a ++ b).isEmpty = (a.isEmpty && b.isEmpty) := by
      intro a b; cases a <;> cases b <;> rfl
    simp_all [ItemShape.keywordErrors, toItemShape, fren_spec]

-- For an item with an error of its syntax or not, and clauses of any
-- shape: whether it has a keyword error, and what both front ends report
-- first, by `itemError?`, whose syntax error stands for `true` and keyword
-- error for `false`.
impl item_error: lang::item_error for (sy : Bool) (s : ItemShape Unit) {
  «syntax?» := sy,
  shape := toItemShape s,
  «keyword?» := !s.keywordErrors.isEmpty,
  reported := toItemError (itemError? (if sy then some true else none) s (fun _ _ => false)),
} by
  intro sy s
  have h := keywordErrors_any_wrong s
  cases hk : s.keywordErrors <;> cases sy <;>
    simp_all [fren_spec, itemError?, Fren.Core.firstItemError?, toItemError]

end Fren.Impls
