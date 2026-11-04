-- keep-sorted start
import FrenCore.Lint.Arithmetic
import FrenCore.Lint.Bools
import FrenCore.Lint.Cardinality
import FrenCore.Lint.Closures
import FrenCore.Lint.Collections
import FrenCore.Lint.Expressions
import FrenCore.Lint.Imports
import FrenCore.Lint.Integers
import FrenCore.Lint.Items
import FrenCore.Lint.Literals
import FrenCore.Lint.Matches
import FrenCore.Lint.Methods
import FrenCore.Lint.Model
import FrenCore.Lint.Naming
import FrenCore.Lint.OperatorChecks
import FrenCore.Lint.Operators
import FrenCore.Lint.PatternTests
import FrenCore.Lint.Quantifiers
import FrenCore.Lint.Settings
import FrenCore.Lint.Text
import FrenCore.Lint.Tree
import FrenCore.Lint.Variants
-- keep-sorted end

/-!
# Lints

Lints (`Reqs/Lint`) as pure functions, shared by both front ends: their
levels, how settings combine, the import and naming lints, unused
variables, dead code, simpler `Bool` expressions, and expectations. Each
front end records what happened while elaborating a file (`UseRecord`,
`UsedName`, `ExpectationRecord`) and calls `importReports` and
`expectationReports` at its end.

A new lint is a constructor of `Lint` and a line of `Lint.info`, each in
its sorted place, an explanation `FrenCore/Codes/CODE.md`, and a row of
the table in `Reqs/Lint.md`; `Lint.all`, the Lean options
(`Fren.Lint`) and the note that lists the lints follow from them. So
lints added at once merge cleanly.
-/


open Lean

namespace Fren.Core


/-- The messages of the operator and method lints in `n`, which is in
`slot` within `parent`, outermost first, where `inElse` says that `n` is
the `else` branch of a conditional, `inClamp` that it is that of a clamp
(`manualClampAt?`), and `chain` that `membership_chain` reads the chain of
`or` or `and` that it is in, if it is one (`membershipChainOf`). -/
partial def opReportsIn [Inhabited α] (src : Array Char) (boolEq : α → Bool) (ordered? : α → Option Ordered)
    (variant? : α → Option String) (isAbs : α → Bool) (mentioned : α → List Mention) (fact? : α → Option NodeFact)
    (fcx : ForallCx) (n : BNode α) (slot : Option Slot) (parent : Range) (inElse inClamp : Bool := false) (chain : Bool := false)
    (delimited : Bool := false) : Array (OpReport α) :=
  let slots := n.kind.slots
  -- Whether `membership_chain` reads the chain of `or` or `and` that `n`
  -- is in: decided at its top, an operand of no operator of its kind.
  let chain := match n.kind with
    | .bin op => if op != "or" && op != "and" then false
      else if slot.any (·.outer == (BKind.bin op).prec) then chain
      else membershipChainOf src variant? (op == "and") n
    | _ => false
  let clamp := if n.kind == .ite then manualClampAt? src ordered? n slot parent else none
  let own := match n.kind with
    | .bin op =>
      let operands := (n.kids.zip slots).filterMap fun (k, s) => s.bind (elseExtendsAt? src n k ·)
      (if op == "and" || op == "or" then
          (doubleComparisonAt? src n slot parent (op == "and")).toArray
            ++ (contradictoryAt? src variant? n (op == "and")).toArray
            ++ (redundantAt? src n slot parent (op == "and")).toArray
            ++ (overlyComplexAt? src n slot parent (op == "and")).toArray
            ++ manualForallAt src variant? fcx n (if delimited then some delimitedSlot else slot) parent
        else #[])
        ++ (boolEqualityAt? src boolEq n slot parent).toArray ++ (manualMethodAt? src n slot parent).toArray
        ++ (identityOpAt? src n slot parent).toArray ++ (suspiciousUnaryAt? src n).toArray
        ++ (erasingOpAt? src n).toArray ++ (firstEmptyAt? src n slot parent).toArray
        ++ (invalidUpcastAt? src isAbs n).toArray ++ (absurdOrderedAt? src fact? n).toArray
        ++ (manualOrderingAt? src fact? n slot parent).toArray ++ (manualRemEuclidAt? src n slot parent).toArray
        ++ (moduloOneAt? src n).toArray ++ operands ++ precedenceAt src n
        ++ (if op == "and" then chainableAt src n slot parent ++ manualAtMostOneAt src fact? n slot parent else #[])
        ++ (if op == "and" || op == "or" then manualPatternTestAt src variant? fact? n (op == "and") chain slot parent
          else #[])
    | .ite =>
      (needlessBoolAssignAt? src n slot parent).toArray ++ (branchesSharingAt? src mentioned n slot parent).toArray
        ++ (if inElse then #[] else ifsSameCondAt src n)
        ++ clamp.toArray ++ (manualAbsAt? src ordered? n slot parent).toArray
        ++ (manualAbsDiffAt? src ordered? n slot parent).toArray
        -- The inner conditional of a clamp is the clamp's, not a `min` or `max` of its own.
        ++ (if inClamp then #[] else (manualMinMaxAt? src ordered? n slot parent).toArray)
    | .method _ => (methodCallAt? src n slot parent).toArray ++ (minOrMaxAt? src fact? n slot parent).toArray
        ++ (minMaxAt? src n).toArray ++ (eqOpMethodAt? src n).toArray
    | .chain ops => (contradictoryChainAt? src n ops).toArray
    | .atom => (cardinalityAt? src n slot parent).toArray ++ (roundtripAt? src fact? n slot parent).toArray
    | _ => #[]
  -- A receiver needs parentheses as an operand does.
  let receiver := match n.kind, n.kids[0]? with
    | .method _, _ => true
    | .atom, some k => isReceiverOf src n k
    | _, _ => false
  let slots := if receiver then #[some receiverSlot] else if n.kind matches .method _ | .atom then #[] else slots
  -- The other parts of an atom, its arguments, fields and elements, are
  -- delimited (`delimitedSlot`).
  let atomic := n.kind matches .method _ | .atom
  own ++ (n.kids.mapIdx fun i k =>
    opReportsIn src boolEq ordered? variant? isAbs mentioned fact? fcx k (slots[i]?.join) n.range (n.kind == .ite && i == 2)
      (clamp.isSome && i == 2) chain (atomic && !(receiver && i == 0))).flatten

/-- The messages of the operator and method lints in an expression written
in `src` (`Reqs/Lint/Complexity/Comparisons`), where `boolEq` says whether a
comparison compares `Bool`s, `ordered?` what type an ordering compares,
`variant?` which variant without a payload a path is, if it is one, `isAbs` whether an expression is a call of `abs`, `mentioned` what
an expression mentions, for the conditions and the operands of `*`, and
`fact?` what is known of an expression of an ordered enumeration or a
newtype; `fcx` is what `manual_forall` needs to know of the
constraint. -/
def opReports [Inhabited α] (src : Array Char) (boolEq : α → Bool) (ordered? : α → Option Ordered)
    (variant? : α → Option String) (isAbs : α → Bool) (mentioned : α → List Mention) (fact? : α → Option NodeFact)
    (fcx : ForallCx) (root : BNode α) : Array (OpReport α) :=
  opReportsIn (upTo src root.range) boolEq ordered? variant? isAbs mentioned fact? fcx root none root.range

end Fren.Core
