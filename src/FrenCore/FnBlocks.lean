-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Functions with blocks

A function may be written with a named result and a block of members, as a
procedure is (`Reqs/Lang/Items#function-blocks`): `fn f(x: Int): (r: Int) {
assume ...; let ...; out r := e; ensure ... }`. Both front ends lower it to
a function with a body and a contract: its `out` member's expression is the
body, its `assume`s and `ensure`s the contract, and its result and `let`s
local definitions, `r := f(x)` and `y := e`, of each expression that
mentions them. The contract written after the signature, as functions were
written before blocks, is an error whose fix writes the block (`F0164`).
-/

namespace Fren.Core

/-- What a member of a function's block is (`lang::FnMemberKind`). -/
inductive FnMember where
  | use
  | assumption
  | «exists»
  | «let»
  | define
  | call
  | guarantee
  /-- `expect` and `cover`. -/
  | claim
  | evidence
  deriving Inhabited, DecidableEq, Repr

/-- Whether a function's block takes a member (`lang::FnVerdict`). -/
inductive FnVerdict where
  | accepted
  /-- Not a function's (`F0442`). -/
  | notFunctions
  /-- Not yet (`F0443`). -/
  | notYet
  deriving Inhabited, DecidableEq, Repr

/-- Whether a function's block takes the member `m`, written `det` if
`det` (`lang::fn_member`): `assume`, `let`, `out` and `ensure`, none of
them `det`, since every value of a function is determined; not yet `use`
and claims. -/
def fnMemberVerdict (m : FnMember) (det : Bool) : FnVerdict :=
  match m with
  | .use | .claim => .notYet
  | .exists | .call | .evidence => .notFunctions
  | _ => if det then .notFunctions else .accepted

/-- The local definitions that an expression needs, of `defs`, in order:
each that it mentions, and transitively each that those mention
(`lang::fn_definitions`). `mentions e` are the names that `e` mentions. -/
def neededDefs {α : Type} (defs : Array (String × α)) (mentions : α → Array String)
    (mentioned : Array String) : Array Nat := Id.run do
  -- Each round adds a definition or changes nothing, so as many rounds
  -- as definitions reach every one needed.
  let mut need := mentioned
  for _ in [0:defs.size] do
    for (n, d) in defs do
      if need.contains n then
        for m in mentions d do
          if !need.contains m then need := need.push m
  return (defs.mapIdx fun i (n, _) => (i, n)).filterMap fun (i, n) => if need.contains n then some i else none

/-- A name for the result of a function migrated to a block, that `taken`
does not have: `r`, or `r?` for a `Bool`, then `result`, `value`, … -/
def fnResultName (bool : Bool) (taken : Array String) : String :=
  let base := ["r", "result", "value", "out_value"].find? (fun n => !taken.contains n && !taken.contains (n ++ "?"))
  (base.getD "fn_result") ++ (if bool then "?" else "")

/-- A function's contract written after its signature, as functions were
written before blocks (`F0164`): `fixed` is the function written with a
block, if it is known. -/
def fnClausesMsg (fixed? : Option (Range × String)) : Msg :=
  { code? := some "F0164", headline := "a function's contract is written in its block"
    label? := some "a clause after the signature"
    notes := #["note: a function with a contract is written `fn f(x: T): (r: U) { assume ... out r := e ensure ... }`, \
      its body the `out` member that defines its result"]
    fixes := fixed?.toArray.map fun (r, replacement) => { msg := "write it with a block", replacement, range? := some r } }

/-- A member that a function's block does not take (`F0442`): `what` is
its kind, such as "`exists`". -/
def fnMemberMsg (what : String) : Msg :=
  { code? := some "F0442", headline := s!"a function's block takes no {what}"
    label? := some "not a function's member"
    notes := #["note: a function's value is determined by its arguments: its block takes `assume`, `let`, `out` \
      and `ensure`, and no `exists`, `call` or `det`"] }

/-- A `use`, an `expect` or a `cover` in a function's block (`F0443`):
`kw` is its keyword. -/
def fnClaimMsg (kw : String) : Msg :=
  { code? := some "F0443", headline := s!"a function's block takes no `{kw}` yet"
    label? := some "not yet a function's member"
    notes := #[if kw == "use" then "note: write the `use` in the function's module"
      else "note: a function's claims are not checked yet; state it of a procedure that applies the function"] }

/-- The error of the member `m` of a function's block, written `det` if
`det` and with the keyword `kw`, if the block does not take it
(`fnMemberVerdict`). -/
def fnMemberMsg? (m : FnMember) (det : Bool) (kw : String) : Option Msg :=
  match fnMemberVerdict m det with
  | .accepted => none
  | .notYet => some (fnClaimMsg kw)
  | .notFunctions => some (fnMemberMsg (if det then "`det`" else if m == .evidence then "evidence setting" else s!"`{kw}`"))

/-- `out x := e` in a function's block, where `x` is not its result
`r` (`F0444`). -/
def fnOutMsg (x r : String) : Msg :=
  { code? := some "F0444", headline := s!"`{x}` is not the function's result"
    label? := some "not the result"
    notes := #[s!"note: `out` defines the function's result, `{r}`; a local definition is written `let {x} := e`"] }

/-- A function with more than one result (`F0445`), which Fren does not
take yet. -/
def fnResultsMsg : Msg :=
  { code? := some "F0445", headline := "a function has one result for now"
    label? := some "a second result"
    notes := #["note: a function with several results is not supported yet; return a record instead"] }

/-- A precondition or the body of a function's block that mentions its
result `r`, itself or through a `let` (`F0165`): the result is the
function's value, which neither determines. -/
def fnResultMentionMsg (r : String) : Msg :=
  { code? := some "F0165", headline := s!"`{r}` is the function's value, which this does not mention"
    label? := some "mentions the result"
    notes := #[s!"note: `{r}` is what the function gives: its body defines it, and its postconditions state what it is; \
      its preconditions, which say where it may be applied, and its body do not mention it"] }

end Fren.Core
