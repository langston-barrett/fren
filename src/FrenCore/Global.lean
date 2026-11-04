-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Global expectations

A global expectation (`Reqs/Lang/Global`) is written like a procedure: its
parameters, then a block of `assume`, `use`, `let`, `call`, `expect` and
`cover` members. The members that a block accepts are a pure function
over plain data, so that the requirements can state it
(`lang::block_member`).
-/

namespace Fren.Core

/-! ## Members -/

/-- A member of a global expectation's block, or a result in its
signature (`lang::BlockMember`). -/
inductive BlockMember where
  | result
  | «exists»
  | «let»
  /-- `out r := e`. -/
  | define
  | assume
  /-- `require n: e`, a procedure's or a function's precondition. Both
  front ends report it before they ask `blockMemberReport?`, with
  `preconditionReport?`'s message of its own, which names `assume`; it is
  here so that `lang::block_member` states that the block does not accept
  it. -/
  | require
  | ensure
  | expect
  | cover
  | call
  | refines
  | use
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a global expectation's block accepts the member `m`, written
with `det` if `det` (`lang::block_member`): it constrains nothing and has
no outputs, so only assumptions, definitions, calls, claims and imports. -/
def blockMemberAccepted (m : BlockMember) (det : Bool) : Bool :=
  !det && match m with
    | .let | .assume | .expect | .cover | .call | .refines | .use => true
    | .result | .exists | .define | .require | .ensure => false

/-- How a message names the member `m`. -/
def BlockMember.text : BlockMember → String
  | .result => "results"
  | .exists => "`exists` members"
  | .let => "`let` members"
  | .define => "`out` members"
  | .assume => "`assume` members"
  | .require => "`require` members"
  | .ensure => "`ensure` members"
  | .expect => "`expect` members"
  | .cover => "`cover` members"
  | .call => "calls"
  | .refines => "refinement claims"
  | .use => "`use` members"

/-- A member that a global expectation's block does not accept (`F0417`):
`m`, or with `det`, any member written with `det`. -/
def blockMemberMsg (m : BlockMember) (det : Bool) : Msg :=
  { code? := some "F0417"
    headline := if det then "global expectations have no `det` members" else s!"global expectations have no {m.text}"
    label? := some "not allowed in a global expectation"
    notes := #["note: a global expectation constrains nothing: its block has `assume`, `use`, `let`, `call`, \
      `expect`, `refines` and `cover` members only",
      "help: state what the procedures guarantee in the procedures, and claim what follows with `expect`"] }

/-- What both front ends report for the member `m` of a global expectation's
block, written with `det` if `det`, before any other check of it
(`lang::block_member`): nothing if the block accepts it, and otherwise
`blockMemberMsg`, `F0417`. -/
def blockMemberReport? (m : BlockMember) (det : Bool) : Option Msg :=
  if blockMemberAccepted m det then none else some (blockMemberMsg m det)

/-! ## The keyword of a precondition -/

/-- A word that starts a clause about a block's inputs: `require` or
`assume` (`lang::PreconditionWord`). -/
inductive PreconditionWord where
  | require
  | assume
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The keyword of the clauses that constrain a block's inputs: `assume`
in a global expectation's block, if `global`, and `require` in a
procedure's or a function's (`lang::precondition_word`). -/
def preconditionKeyword (global : Bool) : String := if global then "assume" else "require"

/-- The keyword of `preconditionKeyword global`, in code, after its article,
as messages name a clause: "an `assume`" or "a `require`". -/
def aPrecondition (global : Bool) : String :=
  s!"{if global then "an" else "a"} `{preconditionKeyword global}`"

/-- `assume` where a procedure's or a function's precondition is written
`require` (`F0169`), with the fix that writes it so. -/
def assumeRenamedMsg : Msg :=
  { code? := some "F0169", headline := "a precondition is written `require`, not `assume`"
    label? := some "write `require`"
    notes := #["note: `assume` starts a global expectation's assumptions; a procedure's or a function's precondition is a `require`"]
    fixes := #[{ msg := "write `require`", replacement := "require" }] }

/-- `require` in a global expectation's block (`F0417`), a member that it
does not accept: its assumptions are written `assume`, which the fix
writes instead. -/
def requireInGlobalMsg : Msg :=
  { code? := some "F0417", headline := "global expectations have no `require` members"
    label? := some "write `assume`"
    notes := #["note: `require` starts a procedure's or a function's precondition; a global expectation's assumptions are `assume`s"]
    fixes := #[{ msg := "write `assume`", replacement := "assume" }] }

/-- What both front ends report for a clause that starts with `w`, in a
global expectation's block if `global`, and otherwise in a procedure's or
a function's (`lang::precondition_word`): nothing if `w` is the block's
`preconditionKeyword`; `F0169` for `assume` in a procedure or a
function; `F0417` for `require` in a global expectation, a member that its
block does not accept. Either is reported at the keyword, whose fix writes
the block's keyword instead, once the item is read, if it has no error of
its syntax (`firstItemError?`, `lang::item_error`). -/
def preconditionReport? (global : Bool) (w : PreconditionWord) : Option Msg :=
  match global, w with
  | false, .assume => some assumeRenamedMsg
  | true, .require => some requireInGlobalMsg
  | _, _ => none

end Fren.Core
