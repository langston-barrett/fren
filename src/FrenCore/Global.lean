-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Global expectations, and the migration from `forall`

A global expectation (`Reqs/Lang/Global`) is written like a procedure: its
parameters, then a block of `assume`, `use`, `let`, `call`, `expect` and
`cover` members. The form that quantified over behaviours, `expect n:
forall (a: c) (m: M), E`, is an error (`F0416`), whose fix writes it as a
block: each binder over behaviours becomes a parameter for each of its
procedure's parameters and a call, each binder over values a parameter,
and the procedures' assumptions `assume` members, so that it means what it
did (`Reqs/Lang/Global#migration`). These are pure functions over plain
data, so that the requirements can state them (`lang::block_member`,
`lang::callee_fix`, `lang::migrated_param`).
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

/-! ## The migration from `forall` -/

/-- What the fix of an old global expectation needs to know of the
procedure of one of its binders over behaviours (`lang::Callee`): its
module, and whether its assumptions mention none of its own variables but
its parameters, and declare no name that a parameter has. -/
structure Callee where
  module : String
  closed : Bool
  deriving Inhabited, BEq, Repr

/-- Whether the fix can copy the parameters' types and the assumptions of
`c`, with its `use` members, into a global expectation in `module`
(`lang::callee_fix`): what they mention then resolves there as it does in
`c`. -/
def calleeFixable (module : String) (c : Callee) : Bool := c.module == module && c.closed

/-- The name of the parameter that the fix declares for the parameter `x`
of a binder `w` (`lang::migrated_param`): `w_x`, so `a_ready?` for `a`'s
`ready?`. It names an assumption of `w`'s procedure the same way. -/
def migratedParam (w x : String) : String := w ++ "_" ++ x

/-- Whether the old global expectation has a fix (`Reqs/Lang/Global#migration`):
each binder's procedure is fixable from its `module`, and each name that
the fix declares is `fresh`. -/
def globalFixOffered (module : String) (callees : Array Callee) (fresh : Array Bool) : Bool :=
  callees.all (calleeFixable module) && fresh.all id

/-- The text of the global expectation that an old one migrates to: `head`
(`expect n`), the parameters `params`, each as written, on one line if it
fits in 100 characters and otherwise one to a line, then a block, indented
by `indent` plus 4, of the imports, the assumptions, the calls, and
`expect n: body`,
whose lines after its first keep their indentation relative to it. -/
def globalBlockText (indent : Nat) (head : String) (params : Array String) (uses assumes calls : Array String)
    (claim : String) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  let inner := pad ++ "    "
  let flat := head ++ "(" ++ ", ".intercalate params.toList ++ ") {"
  let sig := if (pad ++ flat).length ≤ 100 || params.isEmpty then flat
    else head ++ "(\n" ++ String.join (params.toList.map (inner ++ · ++ ",\n")) ++ pad ++ ") {"
  -- Each member's lines after its first keep their indentation relative
  -- to it.
  let member (m : String) : String :=
    let ls := m.splitOn "\n"
    "\n".intercalate (ls.headD "" :: (ls.drop 1).map fun l => if l.trimAscii.isEmpty then "" else inner ++ l)
  let lines := (uses ++ assumes ++ calls ++ #[claim]).toList.map fun m => inner ++ member m ++ "\n"
  sig ++ "\n" ++ String.join lines ++ pad ++ "}"

/-- An old global expectation, which quantified over behaviours with
`forall` (`F0416`): `fixed?` is the block it migrates to, if it has one. -/
def oldGlobalMsg (fixed? : Option String) : Msg :=
  { code? := some "F0416", headline := "global expectations are written with parameters and calls"
    label? := some "a binder over the behaviours of a procedure"
    notes := #["note: a global expectation takes parameters, and relates procedures by calling them, as in \
      `expect n(x: T) { call a := p(x) ... }`"]
      ++ (if fixed?.isNone then #["note: a procedure it binds is in another module, or its assumptions mention \
        variables other than its parameters, or a name the fix would declare is taken, so it has no fix"] else #[])
    fixes := fixed?.toArray.map fun replacement =>
      { msg := "write it with parameters and calls, assuming what its procedures assume", replacement } }

end Fren.Core
