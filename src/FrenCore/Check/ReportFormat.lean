-- keep-sorted start
import FrenCore.Check.Evidence
import FrenCore.Text
-- keep-sorted end

/-!
# Shared formatting for check reports

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-! ## Reporting

Message text shared by both front ends (`view`). -/

/-- The severity of a check's result (`view::severity`): passes are silent,
and a redundant constraint is only a warning. -/
def severity? : CheckKind → Verdict → Option Severity
  | _, .pass => none
  | .redundancy, .fail => some .warning
  | _, .fail => some .error
  | _, .inconclusive => some .warning

/-- A result's own severity (`view::severity`), which `impl severity`
binds: from its kind and verdict alone, so a refuted model's result is a
warning, as any inconclusive one is. Its only message, though, is the
internal error that reports the model, an error, in place of the warning
(`messages`, `Reqs/View#check-results`). -/
def CheckResult.severity? (r : CheckResult) : Option Severity :=
  Fren.Core.severity? r.kind r.verdict

/-- The most severe of the severities of a run's results, `none` if there
are none, for the exit code (`cli::worst_severity`). -/
def worst (sevs : Array Severity) : Option Severity :=
  if sevs.any (· == .error) then some .error
  else if sevs.any (· == .warning) then some .warning
  else none

structure Message where
  severity : Severity
  /-- The procedure item the message is about, or `none` for the procedure itself. -/
  item? : Option Name
  /-- Point at the item's `when`/`unless` condition rather than its name. -/
  atTrigger : Bool := false
  /-- Point at the item's index with this number, in order, rather than its name. -/
  atIndex? : Option Nat := none
  /-- Point at the place of the item's question about its tables with this
  number, in order, rather than its name. -/
  atSite? : Option Nat := none
  /-- Explicit source member range for a Boolean block explanation. -/
  atRange? : Option Range := none
  msg : Msg
  deriving Inhabited

def Message.text (m : Message) : String := m.msg.text

def showNames (ns : Array Name) : String :=
  ", ".intercalate (ns.toList.map fun n => s!"`{n.toString (escape := false)}`")

def showAssignment (a : Assignment) : String :=
  if a.isEmpty then "(any values)" else ", ".intercalate (a.toList.map fun (n, v) => s!"{n} = {v}")

/-- `` `a`, `b` and `c` ``: names in prose. -/
def showNamesAnd (ns : Array Name) : String :=
  match ns.toList.map (fun n => s!"`{n.toString (escape := false)}`") |>.reverse with
  | [] => ""
  | [n] => n
  | last :: rest => s!"{", ".intercalate rest.reverse} and {last}"

/-- The note of a realizability conflict (`Reqs/View#check-results`): the
input, or the arguments of a function (`what`), one variable to a line,
and then what no outputs satisfy, `unmet`. -/
def conflictNote (what : String) (input : Assignment) (unmet : String) : String :=
  if input.isEmpty then s!"note: {unmet}"
  else s!"note: for the {what}\n" ++ String.join (input.toList.map fun (n, v) => s!"    {n} = {v}\n") ++ unmet

/-- `, _` for each of `k` values of a payload after its first
(`view::wildcards`). -/
def furtherWildcards (k : Nat) : String := String.join (List.replicate k ", _")

/-- One `_` for each of `arity` values of a payload, separated by `, `,
as a pattern of the variant writes them (`view::wildcards`). -/
def wildcards (arity : Nat) : String := if arity = 0 then "" else "_" ++ furtherWildcards (arity - 1)

/-- The wildcards of what a clash note says is forced: of its variant's
payload, and none of a value (`view::clash_text`). -/
def Forced.blanks : Forced → String
  | .value _ => ""
  | .variant k => wildcards k.arity

/-- The variant `k` as a pattern that its values match: `E::C` without a
payload, else `E::C(_)`, with one `_` for each value of the payload
(`view::clash_text`). -/
def Variant.pattern (k : Variant) : String :=
  if k.arity = 0 then k.name else s!"{k.name}({wildcards k.arity})"

/-- What a clash note says is forced of the output `o` (`view::clash_text`):
`o = v` of a whole value `v`, and `o is P` of a variant, `P` the pattern
of its values. -/
def forcedText (o : String) : Forced → String
  | .value v => s!"{o} = {v}"
  | .variant k => s!"{o} is {k.pattern}"

/-- The headline of a clash note (`view::clash_text`): the guarantee
`g` forces `f` of the output `o`, and the `count` others of its conflict,
named as the list `others`, force `f'`. -/
def clashLine (g o : String) (f : Forced) (others : String) (f' : Forced) (count : Nat) : String :=
  s!"`{g}` forces {forcedText o f}, but {others}{if count = 1 then " forces " else " force "}{forcedText o f'}"

/-- The headline of a clash note (`Reqs/View#check-results`), at its
guarantee, with the rest of the core named `rest`. -/
def clashText (cl : Clash) (rest : Array Name) : String :=
  clashLine cl.guarantee.getString! (toString cl.output) cl.forced (showNamesAnd rest) cl.restForced rest.size

/-- The note at a guarantee of a realizability conflict's core
(`Reqs/View#check-results`), one at each: its clash, if it has one
(`clashText`); else the other guarantees of the core, `others`, that it
conflicts with; or, in a core of one, that it is false for the input that
the error's note gives. `rest` names a clash's others. -/
def memberText (clash? : Option Clash) (others : Array Name) (rest : Clash → Array Name) : String :=
  match clash? with
  | some cl => clashText cl (rest cl)
  | none => if others.isEmpty then "is false for this input" else s!"conflicts with {showNamesAnd others}"

/-- The case that a question about a split is about, as a message names
it, from 1. -/
def caseText : Option TableGoal → String
  | some (.reachability .match j) => s!"arm {j + 1}"
  | some (.reachability .table j) => s!"row {j + 1}"
  | some (.reachability .tableMatch j) => s!"arm {j + 1}"
  | _ => "a case"

/-- The split that a question is about, as a message names it. -/
def splitText : Option TableGoal → String
  | some (.reachability .match _) | some (.completeness .match) => "a `match`"
  | _ => "a table"

/-- Rows `i` and `j`, counted from 0, as a message names them, from 1:
arms, of a table over a scrutinee (`arms`). -/
def rowsText (rows? : Option (Nat × Nat)) (arms : Bool := false) : String :=
  let what := if arms then "arms" else "rows"
  match rows? with
  | some (i, j) => s!"{what} {i + 1} and {j + 1}"
  | none => s!"two {what}"

/-- The name of a clause of a contract, without its function's
(`Comp.fn?`). -/
def clauseName (n : Name) : Name := Name.mkSimple n.getString!


/-- The subject of the messages about a procedure at `path`, as both front
ends show it: a global expectation, `global`, by its module and the name
of its first expectation, `first?`. -/
def subjectOf (path : Name) (global : Bool) (first? : Option Name) : String :=
  s!"`{showComp (if global then path ++ first?.getD .anonymous else path)}`"

/-- A check's kind, as a message names its check. -/
def kindName : CheckKind → String
  | .realizable => "realizability" | .inst => "call" | .expect => "expectation" | .cover => "cover"
  | .vacuity => "vacuity" | .redundancy => "redundancy" | .determinism => "determinism"
  | .definedness => "definedness" | .completeness => "completeness" | .disjointness => "disjointness"
  | .precondition => "precondition" | .postcondition => "postcondition"
  | .reachability => "reachability"

inductive Advice where
  | raiseTimeout
  | namesConstructs
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What an inconclusive result advises (`view::inconclusive_advice`):
in the decidable core, the solver reached a time or resource limit. -/
def inconclusiveAdvice (decidable : Bool) : Advice :=
  if decidable then .raiseTimeout else .namesConstructs

end Fren.Core
