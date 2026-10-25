-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# Refinement (`Reqs/Lang/Refinement`)

The rules of `refine r: c refines a` that both front ends share: which
variables of `a` the interface accepts, which bindings the refinement may
have and what they may mention, which checks run on the refinement, and
the messages.
-/

open Lean

namespace Fren.Core

/-- Whether `c` has the variable of `a` in the interface
(`refinement::interface`): an input as an input, an output as a public
output, of the same type. -/
def interfaceAccepted (input inConcrete concreteInput concretePub sameType : Bool) : Bool :=
  inConcrete && sameType && (if input then concreteInput else !concreteInput && concretePub)

/-- Whether the names `bound` of a refinement's bindings are accepted, where
`vars` are the abstract comp's variables (`refinement::binding`): each is
a variable, bound once. -/
def refineBindingsAccepted (vars bound : Array Name) : Bool :=
  bound.all vars.contains && repeatsOf bound == 0

/-- Checks the names bound by a refinement of `abstract`, whose variables
are `vars` (`refineBindingsAccepted`), explaining the first problem with
the index of its binding. -/
def checkRefineBindings (abstract : Name) (vars bound : Array Name) : Except (Nat × Msg) Unit := do
  if refineBindingsAccepted vars bound then return
  let a := showComp abstract
  let again := repeatsAt bound
  for b in bound, i in [0:bound.size] do
    unless vars.contains b do
      throw (i, { code? := some "F0413", headline := s!"`{a}` has no variable `{b}`", label? := some "unknown variable"
                  notes := #[s!"note: a refinement binds variables of the refined component; those of `{a}` are {showNameList vars}"]
                  fixes := similarFixes "a variable with a similar name exists" b vars })
    if again.contains i then
      throw (i, { code? := some "F0414", headline := s!"variable `{b}` of `{a}` is bound multiple times"
                  label? := some "bound again here"
                  notes := #["note: a refinement binds each variable of the refined component at most once"] })
  throw (0, Msg.internal s!"the bindings of a refinement of `{a}` are rejected without a reason")

/-- Whether a binding of a refinement may mention a variable of the
concrete comp (`refinement::mention`): an input always, a public output
only in the binding of an output. -/
def refineMentionOk (input concreteInput concretePub : Bool) : Bool :=
  concreteInput || (!input && concretePub)

/-- Where a refinement's binding is: the comps, and whether it binds an
input of `abstract`. -/
structure RefineBinding where
  concrete : Name
  abstract : Name
  input : Bool
  deriving Inhabited

/-- Whether the variable `n` of the concrete comp, of role `role`, may be
mentioned in the binding `rb` (`refineMentionOk`). -/
def RefineBinding.checkMention (rb : RefineBinding) (role : Role) (isPub : Bool) (n : Name) : Except Msg Unit := do
  if refineMentionOk rb.input (role == .input) isPub then return
  let c := showComp rb.concrete
  if !isPub then
    throw { code? := some "F0415", headline := s!"`{n}` is private to `{c}`", label? := some "private"
            notes := #[s!"note: a refinement's bindings see only the `in`s and `pub out`s of `{c}`",
              s!"help: to mention it, declare it `pub out` in `{c}`"] }
  throw { code? := some "F0415"
          headline := s!"a binding of an input of `{showComp rb.abstract}` may only mention `in` variables of `{c}`, but `{n}` is an `out`"
          label? := some "an `out`"
          notes := #[s!"note: the inputs of `{showComp rb.abstract}` are chosen by the environment, before `{c}` chooses its outputs",
            "help: bind an output of the refined component to it instead"] }

/-- Whether a check of kind `k` runs on a refinement (`refinement::checks`). -/
def refinementRuns : CheckKind → Bool
  | .inst | .expect | .definedness => true
  | _ => false

/-- A variable of the abstract comp that the concrete comp lacks, or has
with another role or type (`refinement::interface`). -/
def interfaceMsg (concrete abstract x : Name) (why : String) : Msg :=
  { code? := some "F0412"
    headline := s!"`{showComp concrete}` cannot refine `{showComp abstract}`: {why}"
    label? := some s!"`{x}` does not match"
    notes := #[s!"note: each input of `{showComp abstract}` must be an input of `{showComp concrete}`, and each output a public output, of the same type",
      s!"help: or bind it to an expression over the variables of `{showComp concrete}`, as in `\{ {x} := ... }`"] }

end Fren.Core
