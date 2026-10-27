-- keep-sorted start
import FrenCore.Names
import FrenCore.Patterns
-- keep-sorted end

/-!
# Structural recursion (`lang::structural_recursion`)

Whether a defined function's uses of itself in its own body are a
structural recursion over a recursive enumeration: one parameter, the
*decreasing* one, is the same at every recursive application, and there its
argument is a binder that a `match` arm bound from a payload of that
parameter, directly or nested. Both front ends read the body into a list of
uses, and decide by `recursion`.
-/

namespace Fren.Core

/-- Where a recursive application's argument at one position comes from,
relative to the function's parameter at that same position. -/
inductive RecArg where
  /-- A binder that a `match` arm bound from a payload of the parameter,
  directly or nested: a value smaller than the parameter's. -/
  | payload
  /-- The parameter itself. -/
  | itself
  /-- Another name: another parameter, a `let`'s name, or a binder bound
  from something else. -/
  | name
  /-- Any other expression. -/
  | expr
  deriving DecidableEq, Repr, Inhabited

/-- How the function is used in its own body. -/
inductive RecForm where
  /-- Applied, outside any closure. -/
  | applied
  /-- Applied within a closure's body. -/
  | inClosure
  /-- Named as a function argument, without being applied. -/
  | passed
  deriving DecidableEq, Repr, Inhabited

/-- A use of the function in its own body: its form, and for an
application, where each argument comes from. -/
structure RecUse where
  form : RecForm
  args : List RecArg := []
  deriving DecidableEq, Repr, Inhabited

/-- Whether the use `u` is an application whose argument at position `i` is
a payload of the parameter there. -/
def RecUse.decreasesAt (u : RecUse) (i : Nat) : Bool :=
  u.form == .applied && u.args[i]? == some .payload

/-- What a function's uses of itself are. -/
inductive Recursion where
  /-- It does not use itself. -/
  | notRecursive
  /-- A structural recursion, decreasing at the parameter at this position. -/
  | structural (i : Nat)
  /-- No position decreases at every use. The use is the first by which every
  position has failed, and the position the first whose first failure is
  that use: the diagnostic names that use, and why its argument at that
  position is not a payload. -/
  | notStructural (use pos : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The index of the first of `uses` that does not decrease at position `i`. -/
def firstFailure (uses : List RecUse) (i : Nat) : Option Nat := uses.findIdx? (!·.decreasesAt i)

/-- What the uses `uses` of a function of `n` parameters are
(`lang::structural_recursion`): the decreasing parameter is the first
position at which every use decreases. -/
def recursion (n : Nat) (uses : List RecUse) : Recursion :=
  if uses.isEmpty then .notRecursive
  else match (List.range n).find? (firstFailure uses · |>.isNone) with
    | some i => .structural i
    | none =>
      let fs := (List.range n).map fun i => (firstFailure uses i).getD 0
      let k := fs.foldl max 0
      .notStructural k (fs.idxOf k)

/-! ## Kinds and encodings (`lang::recursive_encoding`) -/

/-- An occurrence, in a structural recursion's body, of a parameter or of a
binder bound from a payload of one. -/
inductive Occurrence where
  /-- A recursive payload as a recursive application's argument, at the
  position whose payload it is. -/
  | recursed
  /-- The parameter itself, as the scrutinee of a `match`. -/
  | matched
  /-- Any other: a recursive payload or the parameter otherwise used, or a
  `match` on the parameter that looks into a payload with a variant's
  pattern. -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- An occurrence of the parameter at `pos`, or of a payload of it. -/
structure PayloadOcc where
  pos : Nat
  occ : Occurrence
  deriving DecidableEq, Repr, Inhabited

/-- How the solver knows a defined function. -/
inductive Encoding where
  /-- Not recursive: its body, unfolded at each application. -/
  | unfolded
  /-- A catamorphism: SMT-LIB's `define-fun-rec`. -/
  | defineFunRec
  /-- A paramorphism: uninterpreted, with one-step unfolding where the
  constructor is known. -/
  | opaque
  deriving DecidableEq, Repr, Inhabited

/-- How the solver knows a defined function whose uses of itself are
`r`, with the occurrences `occs` (`lang::recursive_encoding`): a structural
recursion is a catamorphism when no occurrence at its decreasing parameter
is other than a recursive application's argument or the scrutinee of a
`match`. -/
def recursiveEncoding (r : Recursion) (occs : List PayloadOcc) : Encoding :=
  match r with
  | .structural i => if occs.any (fun o => o.pos == i && o.occ == .other) then .opaque else .defineFunRec
  | _ => .unfolded

/-- Whether the pattern `p` is a variant's, or an or-pattern with one. -/
partial def Pat.hasVariant : Pat → Bool
  | .ctor .. => true
  | .or ps => ps.any Pat.hasVariant
  | _ => false

/-- Whether the pattern `p` looks into a variant's payload with a variant's
pattern, as `Expr::Add(Expr::Neg(x), y)` does. -/
partial def Pat.looksIntoPayload : Pat → Bool
  | .ctor _ ps => ps.any Pat.hasVariant
  | .or ps => ps.any Pat.looksIntoPayload
  | _ => false

/-- The kind of a structural recursion, as its message names it. -/
def Encoding.kindText : Encoding → String
  | .defineFunRec => "a catamorphism"
  | .opaque => "a paramorphism"
  | .unfolded => "not recursive"

/-- A defined function's application of itself that is not structural
recursion: `f` is the function, `param` the parameter at the position whose
argument is reported, `arg` that argument's origin, and `form` the use's
form. -/
def nonStructuralMsg (f param : Lean.Name) (form : RecForm) (arg : RecArg) : Msg :=
  let why := match form, arg with
    | .passed, _ => s!"`{showPath f}` is passed as a function, not applied"
    | .inClosure, _ => s!"`{showPath f}` is applied within a closure"
    | .applied, .itself => s!"the argument is the parameter `{param}` itself"
    | .applied, .name => s!"the argument is not bound from a payload of `{param}`"
    | .applied, .expr => s!"the argument is an expression, not a payload of `{param}`"
    | .applied, .payload => s!"the argument is a payload of `{param}`"
  { code? := some "F0447", headline := s!"defined function `{showPath f}` is not structurally recursive"
    label? := some why
    notes := #["note: a defined function may apply itself only to a payload of a variant that a `match` on a parameter bound, at the same parameter in every application",
      "help: match on the parameter, and apply the function to a binder of the arm's pattern"] }

/-- A defined function that is a structural recursion, which is not yet
supported (#279). -/
def structuralUnsupportedMsg (f param : Lean.Name) (enc : Encoding) : Msg :=
  { code? := some "F0448", headline := s!"recursive defined functions are not yet supported: `{showPath f}` is {enc.kindText}"
    label? := some s!"`{showPath f}` recurses structurally on `{param}`"
    notes := #["note: this application is structural recursion, which a later version of Fren will accept",
      "help: state the function's values by quantified equations on an uninterpreted function, or one layer at a time"] }

end Fren.Core
