-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Global expectations, and the form before parameters

A global expectation (`Reqs/Lang/Global`) is written like a procedure: its
parameters, then a block of `assume`, `use`, `let`, `call`, `expect` and
`cover` members. The form that quantified over behaviours, `expect n:
forall (a: c) (m: M), E`, is an error (`F0416`)
(`Reqs/Lang/Global#migration`). The members that a block accepts are a
pure function over plain data, so that the requirements can state it
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
  | ensure
  | expect
  | cover
  | call
  | use
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a global expectation's block accepts the member `m`, written
with `det` if `det` (`lang::block_member`): it constrains nothing and has
no outputs, so only assumptions, definitions, calls, claims and imports. -/
def blockMemberAccepted (m : BlockMember) (det : Bool) : Bool :=
  !det && match m with
    | .let | .assume | .expect | .cover | .call | .use => true
    | .result | .exists | .define | .ensure => false

/-- How a message names the member `m`. -/
def BlockMember.text : BlockMember → String
  | .result => "results"
  | .exists => "`exists` members"
  | .let => "`let` members"
  | .define => "`out` members"
  | .assume => "`assume` members"
  | .ensure => "`ensure` members"
  | .expect => "`expect` members"
  | .cover => "`cover` members"
  | .call => "calls"
  | .use => "`use` members"

/-- A member that a global expectation's block does not accept (`F0417`):
`m`, or with `det`, any member written with `det`. -/
def blockMemberMsg (m : BlockMember) (det : Bool) : Msg :=
  { code? := some "F0417"
    headline := if det then "global expectations have no `det` members" else s!"global expectations have no {m.text}"
    label? := some "not allowed in a global expectation"
    notes := #["note: a global expectation constrains nothing: its block has `assume`, `use`, `let`, `call`, \
      `expect` and `cover` members only",
      "help: state what the procedures guarantee in the procedures, and claim what follows with `expect`"] }

/-! ## The form before parameters -/

/-- A global expectation written as before global expectations had
parameters, with a binder of its leading `forall` over the behaviours of a
procedure (`F0416`). -/
def oldGlobalMsg : Msg :=
  { code? := some "F0416", headline := "global expectations are written with parameters and calls"
    label? := some "a binder over the behaviours of a procedure"
    notes := #["note: a global expectation takes parameters, and relates procedures by calling them",
      "help: write each binder `a: p` as parameters for `p`'s parameters and a call of `p`, and assume what `p` assumes, \
        as in `expect n(a_x: Int) { assume a_ok: a_x > 0  call a := p(a_x)  expect n: a.y > 0 }`"] }

end Fren.Core
