-- keep-sorted start
import FrenCore.Lint.Bools
import FrenCore.Lint.Naming
import FrenCore.Mentions
-- keep-sorted end

/-!
# Item, member and variable lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Unused variables -/

/-- The message of `unused_variables` for a variable of a procedure, or
with `global`, of a global expectation, that nothing mentions. -/
def unusedVariableMsg (n : Name) (global : Bool) (output : Bool) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused variable `{n}`", label? := some "never mentioned"
    notes := (if output then #["note: nothing constrains it, so it can take any value"]
        else #[s!"note: nothing in its {if global then "global expectation" else "procedure"} depends on it"])
      ++ #["help: remove it, or mention it in a constraint"] }

/-- A parameter of a defined function that its body never mentions. -/
def unusedParamMsg (n : Name) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused parameter `{n}`", label? := some "never mentioned"
    notes := #["note: the function's value does not depend on it", "help: remove it, or mention it in the body"] }

/-- A name of a `let` or `where` clause that neither its body nor a later
definition of the clause mentions. -/
def unusedDefinitionMsg (n : Name) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused definition `{n}`", label? := some "never mentioned"
    notes := #["note: a definition that nothing mentions has no effect",
      "help: remove it, or mention it in the body or a later definition"] }

/-- A bound name of a `forall` (`all`) or an `exists` that its body never
mentions. -/
def unusedBoundMsg (n : Name) (all : Bool) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused bound name `{n}`", label? := some "never mentioned"
    notes := #[s!"note: the body does not depend on it, so the `{if all then "forall" else "exists"}` over it is its body",
      "help: remove it, or mention it in the body"] }

/-- The variables, or binders, of `declared` that `mentioned` does not
contain, in order. -/
def unmentioned (declared : Array (Name × α)) (mentioned : Array Name) : Array (Name × α) :=
  declared.filter fun (n, _) => !mentioned.contains n

/-! ## Dead code -/

/-- Whether an item is dead (`lint::dead_item`). -/
def deadItem (what : Named) (isPub : Bool) (nUses : Nat) : Bool :=
  match what with
  | .enumeration | .record | .abstractType | .typeAlias | .function | .constant => !isPub && nUses == 0
  | _ => false

/-- A private enumeration, record, abstract type, function or constant declared in
the file being elaborated, with the level of `dead_code` there. -/
structure ItemRecord where
  what : Named
  path : Name
  level : LevelInEffect
  /-- For a defined function, the level of `single_call_fn` there. -/
  singleCall? : Option LevelInEffect := none
  deriving Inhabited, Repr

/-- The item that a resolved path uses: an enumeration for its variants. -/
def Resolved.usedItem : Resolved → Name
  | .item i => i.path
  | .variant e _ => e.path

def deadCodeMsg (what : Named) (n : Name) : Msg :=
  { code? := some Lint.deadCode.code, headline := s!"{what.describe} `{n.getString!}` is never used"
    label? := some "never used"
    notes := #["note: it is private, and nothing in this file uses it", "help: remove it, or make it `pub`"] }

/-- The `dead_code` messages of a file's items, given the items that paths
in it resolve to or through. -/
def deadCodeReports (items : Array (ItemRecord × α)) (used : Array Name) : Array (LintReport α) :=
  items.filterMap fun (i, ref) =>
    if deadItem i.what false (used.count i.path) then
      some { lint := .deadCode, level := i.level, ref, msg := deadCodeMsg i.what i.path }
    else none

/-- Whether `single_call_fn` fires on a function, `defined` if it has a
body, applied `nUses` times in its file (`lint::single_call_fn`). -/
def singleCallFn (defined isPub : Bool) (nUses : Nat) : Bool := defined && !isPub && nUses == 1

def singleCallFnMsg (n : Name) : Msg :=
  { code? := some Lint.singleCallFn.code, headline := s!"function `{n.getString!}` is applied only once"
    label? := some "applied once"
    notes := #["note: it is private, and only one path in this file applies it",
      "help: write its body in place of the application, with the arguments in place of the parameters"] }

/-- The `single_call_fn` messages of a file's defined functions, counting
uses as `deadCodeReports` does. -/
def singleCallReports (items : Array (ItemRecord × α)) (used : Array Name) : Array (LintReport α) :=
  items.filterMap fun (i, ref) => i.singleCall?.bind fun level =>
    if singleCallFn true false (used.count i.path) then
      some { lint := .singleCallFn, level, ref, msg := singleCallFnMsg i.path }
    else none

/-! ## Procedures that only claim -/

/-- Whether `proc_without_outputs` fires on a procedure, from whether it is
`pub`, its results and members, each with whether it is written with
`det`, and the paths in its file that resolve to it
(`lint::proc_without_outputs`): a private procedure that nothing in its
file names, whose every result and member a global expectation's block
accepts (`blockMemberAccepted`), so that it has no results. -/
def procWithoutOutputs (isPub : Bool) (members : List (BlockMember × Bool)) (nUses : Nat) : Bool :=
  !isPub && nUses == 0 && members.all fun (m, det) => blockMemberAccepted m det

/-- `proc_without_outputs`'s message. It has no fix: writing `expect` in
place of `proc` would break a call of the procedure in another file that
enters its module, and any module may be entered, the root module too. -/
def procWithoutOutputsMsg (n : Name) : Msg :=
  { code? := some Lint.procWithoutOutputs.code, headline := s!"procedure `{n.getString!}` has no outputs"
    label? := some "constrains nothing"
    notes := #["note: it has no results, and each of its members is one a global expectation accepts, \
        and nothing in this file calls, refines or names it, so it is a claim about its parameters",
      "help: write it as a global expectation, `expect` in place of `proc` and `assume` in place of each `require`, unless another file calls it"] }

/-- A procedure that `proc_without_outputs` may fire on, once the file's
paths are known: its path, whether it is `pub`, its results and members,
and the level of the lint at it. -/
structure ProcRecord where
  path : Name
  isPub : Bool
  members : List (BlockMember × Bool)
  level : LevelInEffect
  deriving Inhabited, Repr

/-- The `proc_without_outputs` messages of a file's procedures, given the
items that paths in it resolve to: its calls, refinements and claims. -/
def procWithoutOutputsReports (procs : Array (ProcRecord × α)) (used : Array Name) : Array (LintReport α) :=
  procs.filterMap fun (p, ref) =>
    if procWithoutOutputs p.isPub p.members (used.count p.path) then
      some { lint := .procWithoutOutputs, level := p.level, ref, msg := procWithoutOutputsMsg p.path }
    else none

/-- Whether `assertions_on_constants` fires on a constraint, where
`mentioned` is what its expression mentions
(`lint::assertions_on_constants`). -/
def assertionOnConstant (mentioned : List Mention) : Bool := mentioned.isEmpty

/-- A constraint, an `assume`, `ensure` or `expect`, or a cover goal, that mentions no
variable, where `literal?` is its value if it is written `true` or
`false`. -/
def assertionOnConstantMsg (kind : String) (literal? : Option Bool) : Msg :=
  let what := match kind with
    | "assume" => "assumption"
    | "ensure" => "guarantee"
    | "cover" => "cover goal"
    | "precondition" => "precondition"
    | "postcondition" => "postcondition"
    | _ => "expectation"
  let (label, note) := match literal?, kind with
    | some true, "assume" => ("always `true`", "it rules out no input")
    | some true, "ensure" => ("always `true`", "it constrains nothing")
    | some true, "precondition" => ("always `true`", "it rules out no argument")
    | some true, "postcondition" => ("always `true`", "it says nothing of the function")
    | some true, _ => ("always `true`", "it claims nothing")
    | some false, "assume" => ("always `false`", "no input meets it, so every guarantee holds vacuously")
    | some false, "ensure" => ("always `false`", "no behaviour meets it, so the procedure is not realizable")
    | some false, "precondition" => ("always `false`", "no argument meets it, so every application of the function fails its precondition check")
    | some false, "postcondition" => ("always `false`", "no value meets it, so the function's contract cannot hold")
    | some false, _ => ("always `false`", "it always fails")
    | none, _ => ("the same in every behaviour",
      "it is either always true, and says nothing, or always false")
  { code? := some Lint.assertionsOnConstants.code, headline := s!"this {what} mentions no variable"
    label? := some label, notes := #[s!"note: {note}"] }

/-! ## Contract clauses about other names -/

/-- Whether the mention `m` of a clause of the contract of the function `f`,
with the parameters `params`, is of `f`'s own (`lint::own_mention?`): a
parameter, read whole or by a field (`q` or `q.len`), or applied, as a
function parameter is, or `f` itself. The result is `f` applied to its
parameters, which mentions what that mentions. -/
def ownMention (f : String) (params : List String) : Mention → Bool
  | .var x => params.any fun p => x == p || Fren.Str.startsWith x (p ++ ".")
  | .fn g => g == f || params.contains g

/-- Whether `contract_mentions_nothing` fires on a clause of the contract
of the function `f`, with the parameters `params`, where `mentioned` is what
the clause mentions (`lint::contract_mentions_nothing`): it mentions
something, but nothing of `f`'s own. A clause that mentions nothing is
`assertions_on_constants`'s. -/
def contractMentionsNothing (mentioned : List Mention) (f : String) (params : List String) : Bool :=
  !mentioned.isEmpty && !mentioned.any (ownMention f params)

/-- The precondition, if `post` is false, or the postcondition `clause` of
the function `f`, that mentions `mentioned` but nothing of `f`'s own. A leaf
of a labelled conjunction is named by its path, as `both.other`, since it
is reported at the conjunction. -/
def contractMentionsNothingMsg (post : Bool) (clause f : String) (mentioned : List Mention) : Msg :=
  let what := if post then "postcondition" else "precondition"
  { code? := some Lint.contractMentionsNothing.code, headline := s!"the {what} `{clause}` says nothing about `{f}`"
    label? := some s!"mentions no parameter of `{f}`{if post then ", nor its value" else ""}"
    notes := #[s!"note: it mentions only {describeMentions mentioned}",
      "help: state it in the contract of what it is about, or as a global expectation"] }

/-! ## Restricted settings and paths -/

/-- Whether `allow_attributes` fires on a `set_option` of a lint or group
to `requested`, and whether its fix applies, from whether the setting is
of `unfulfilled_lint_expectations` itself (`lint::allow_attributes`). -/
def allowAttributes (requested : LintLevel) (unfulfilled : Bool) : Bool × Bool :=
  (requested == .allow, requested == .allow && !unfulfilled)

/-- A `set_option` of `t` to `"allow"`, fixed to `"expect"` if `fixable`. -/
def allowAttributesMsg (t : LintTarget) (fixable : Bool) : Msg :=
  { code? := some Lint.allowAttributes.code, headline := s!"`{t.name}` is allowed rather than expected"
    label? := some "`allow`"
    notes := #[s!"note: `\"expect\"` silences {if t matches .group _ then "its lints" else "it"} too, and `unfulfilled_lint_expectations` reports the setting once nothing needs it"]
      ++ (if fixable then #[] else #["note: for `unfulfilled_lint_expectations`, `\"expect\"` means `\"allow\"`, so it is never fulfilled"])
    fixes := if fixable then #[{ msg := "expect it instead", replacement := "\"expect\"" }] else #[] }

/-- Whether `absolute_paths` fires on a path of `nSegments` segments, in an
expression, pattern or type, to an item or a variant
(`lint::absolute_paths`). -/
def absolutePath (nSegments : Nat) : Bool := nSegments ≥ 3

/-- `absolute_paths` for the path `segs` to `r`, if it is long. -/
def absolutePathMsg? (segs : Array Name) (r : Resolved) : Option Msg := do
  guard (absolutePath segs.size)
  let (target, rest) := match r with
    | .variant en idx => (en.path, s!"{en.path.getString!}::{nameText en.variants[idx]!}")
    | .item i => (i.path, i.path.getString!)
  some { code? := some Lint.absolutePaths.code
         headline := s!"`{"::".intercalate (segs.map nameText).toList}` is a path of {segs.size} segments"
         label? := some "a long path"
         notes := #[s!"help: import it with `use {showPath target}`, and write `{rest}`"] }

/-! ## Trailing commas -/

/-- Whether `unnecessary_trailing_comma` fires on a comma after the last
element of a list, from whether a line ends between it and the `}` or `]` that
closes the list (`lint::unnecessary_trailing_comma`). -/
def unnecessaryTrailingComma (lineBreak : Bool) : Bool := !lineBreak

/-- The commas among `toks` that `unnecessary_trailing_comma` reports, by
index: each followed by a `}` or `]`, which only a trailing comma is: a
list in parentheses has none.
Each token is its text, and whether a line ends before it. -/
def trailingCommas (toks : Array (String × Bool)) : Array Nat :=
  (Array.range toks.size).filter fun i =>
    toks[i]!.1 == "," && toks[i + 1]?.any fun (t, lineBreak) =>
      (t == "}" || t == "]" || t == ")") && unnecessaryTrailingComma lineBreak

/-- A trailing comma on the line of the `closer` of its list. -/
def unnecessaryTrailingCommaMsg (closer : String) : Msg :=
  { code? := some Lint.unnecessaryTrailingComma.code, headline := s!"unnecessary trailing comma before `{closer}`"
    label? := some "trailing comma"
    notes := #[s!"note: a list ends with a comma only where its `{closer}` starts a line, so that an element is added by adding a line"]
    fixes := #[{ msg := "remove the comma", replacement := "" }] }

/-! ## Record literals -/

/-- Whether `inconsistent_struct_constructor` fires on a record literal,
from whether its fields are written in the order its record declares them
(`lint::inconsistent_struct_constructor`). -/
def inconsistentStructConstructor (inOrder : Bool) : Bool := !inOrder

/-- The record literal written at `outer` in `src`, whose fields, named
`given`, are written at `fields`, with its fields in the order `declared`,
if `inconsistent_struct_constructor` fires on it: each field keeps its
text, and the text between fields stays where it is. The fix is `none`
where that text has a comment, which would no longer be by its field. -/
def reorderedFields? (src : Array Char) (outer : Range) (fields : Array Range) (given declared : Array Name) :
    Option (Option String) := do
  let order := declared.filterMap given.idxOf?
  guard (order.size == fields.size && fields.size > 0)
  guard (inconsistentStructConstructor (order == Array.range order.size))
  let before := textOf src { start := outer.start, stop := fields[0]!.start }
  let between := (Array.range fields.size).map fun k =>
    textOf src { start := fields[k]!.stop, stop := if k + 1 < fields.size then fields[k + 1]!.start else outer.stop }
  if hasComment before || between.any hasComment then return none
  let mut text := before
  for k in [0:fields.size] do
    text := text ++ textOf src fields[order[k]!]! ++ between[k]!
  return some text

/-- A record literal of the record `r`, whose fields are not in the order
`declared`, as the text of its fix, if it has one. -/
def inconsistentStructConstructorMsg (r : Name) (declared : Array Name) (fixed? : Option String) : Msg :=
  { code? := some Lint.inconsistentStructConstructor.code
    headline := s!"the fields of this literal are not in the order `{nameText r}` declares them"
    label? := some "fields out of order"
    notes := #[s!"note: `{nameText r}` declares {proseList (declared.map nameText)}, in this order"]
      ++ (if fixed?.isNone then #["note: a comment between the fields would not stay by its field, so this has no fix"] else #[])
    fixes := fixed?.toArray.map fun replacement => { msg := "write them in that order", replacement } }

/-! ## The order of members -/

/-- A member of a procedure's block, by its place in the order that
`arbitrary_source_item_ordering` asks for (`lint::MemberKind`). A
`set_option fren.evidence ... in` is part of the member after it. -/
inductive MemberKind where
  | use
  | assumption
  | «exists»
  | «let»
  /-- `out r := e`, the definition of a result, in the place of `let`. -/
  | define
  | call
  | guarantee
  | expectation
  | cover
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Its place in the order (`lint::rank`). -/
def MemberKind.rank : MemberKind → Nat
  | .use => 0
  | .assumption => 1
  | .exists => 2
  | .let => 3
  | .define => 3
  | .call => 4
  | .guarantee => 5
  | .expectation => 6
  | .cover => 7

def MemberKind.describe : MemberKind → String
  | .use => "a `use`"
  | .assumption => "an assumption"
  | .exists => "an `exists`"
  | .let => "a `let`"
  | .define => "a result's definition"
  | .call => "a call"
  | .guarantee => "a guarantee"
  | .expectation => "an expectation"
  | .cover => "a cover goal"

/-- Whether `arbitrary_source_item_ordering` fires on a member of kind
`second` written right after one of kind `first`
(`lint::arbitrary_source_item_ordering`). -/
def outOfOrder (first second : MemberKind) : Bool := first.rank > second.rank

/-- The first member that `arbitrary_source_item_ordering` fires on, if
any: the members before it are in order, so the one just before it is of
the latest kind among them. -/
def firstOutOfOrder? (kinds : Array MemberKind) : Option Nat :=
  (List.range kinds.size).find? fun i => i > 0 && outOfOrder kinds[i - 1]! kinds[i]!

/-- Whether the order keeps a member's mention of another after the
other's declaration, where `earlier` says the other is written before it:
the kinds are put in order, and the members of one kind stay in the order
they are written in (`lint::arbitrary_source_item_ordering`). -/
def mentionKept (mentioner mentioned : MemberKind) (earlier : Bool) : Bool :=
  mentioned.rank < mentioner.rank || (mentioned.rank == mentioner.rank && earlier)

/-- Whether the order keeps each mention after what it mentions, where a
mention `(i, j)` is of the member at `j` by the definition or a binding of
the one at `i` (`lint::arbitrary_source_item_ordering`). -/
def keepsMentions (kinds : Array MemberKind) (mentions : List (Nat × Nat)) : Bool :=
  mentions.all fun (i, j) => i == j || match kinds[i]?, kinds[j]? with
    | some a, some b => mentionKept a b (j < i)
    | _, _ => false

/-- The members of a procedure in order, as indices: by kind, and as written
within a kind. -/
def canonicalOrder (kinds : Array MemberKind) : Array Nat :=
  let rank (i : Nat) := (kinds[i]?.map (·.rank)).getD 0
  ((List.range kinds.size).mergeSort fun i j => rank i < rank j || (rank i == rank j && i ≤ j)).toArray

/-- Just after the end of the line that `i` is on in `src`, if only
whitespace and a line comment follow `i` on it. -/
def lineRestEnd? (src : Array Char) (i : Nat) : Option Nat := do
  let nl ← (List.range' i (src.size - i)).find? (src[·]! == '\n')
  let rest := (textOf src { start := i, stop := nl }).trimAscii.toString
  if rest.isEmpty || rest.startsWith "--" then some (nl + 1) else none

/-- The whole lines that each member is written on, from the line after the
`{` of its procedure, or after the previous member's last line, to the end
of its own last line: the comments above it are its own. `none` unless
each member starts its line, and only a comment follows it on its last
one. `openStop` is just after the `{`. -/
def memberLines? (src : Array Char) (openStop : Nat) (members : Array Range) : Option (Array Range) := do
  let mut start ← lineRestEnd? src openStop
  let mut out := #[]
  for m in members do
    let before := (textOf src { start, stop := m.start }).splitOn "\n"
    unless (before.getLast?.getD "").all (fun c => c == ' ' || c == '\t') do failure
    let stop ← lineRestEnd? src m.stop
    out := out.push { start, stop }
    start := stop
  return out

/-- The blank lines that `text`, whole lines, starts with, and the rest. -/
def splitBlankLines (text : String) : String × String :=
  let lines := text.splitOn "\n"
  let blank := lines.takeWhile (·.all (·.isWhitespace))
  -- The last piece is what follows the last newline, which is empty.
  let n := min blank.length (lines.length - 1)
  ("".intercalate (lines.take n |>.map (· ++ "\n")), "\n".intercalate (lines.drop n))

/-- The fix of `arbitrary_source_item_ordering`: the lines of the members,
in order, in place of the lines they are written on. Each member moves with
the blank lines before it, but the first keeps none: the blank lines of the
member that comes first go to the member written first. `mentions[i]` are
the members that member `i`'s definition or bindings mention. `none` unless the order keeps each mention after its
declaration (`mentionKept`), and the members are a line apart
(`memberLines?`). -/
def memberOrderFix? (src : Array Char) (openStop : Nat) (members : Array Range) (kinds : Array MemberKind)
    (mentions : Array (Array Nat)) : Option (Range × String) := do
  guard <| keepsMentions kinds (mentions.zipIdx.toList.flatMap fun (ms, i) => ms.toList.map (i, ·))
  let lines ← memberLines? src openStop members
  let first ← lines[0]?
  let last ← lines.back?
  let parts := lines.map fun r => splitBlankLines (textOf src r)
  let order := canonicalOrder kinds
  let head := order[0]?.getD 0
  let blankOf (k : Nat) := (parts[if k == head then 0 else if k == 0 then head else k]!).1
  let text := String.join (order.toList.map fun k => blankOf k ++ parts[k]!.2)
  return ({ start := first.start, stop := last.stop }, text)

/-- A member of kind `member` written after one of kind `before`, in a
global expectation's block if `global`. -/
def memberOrderMsg (member before : MemberKind) (global : Bool := false) : Msg :=
  { code? := some Lint.arbitrarySourceItemOrdering.code, headline := s!"{member.describe} after {before.describe}"
    label? := some "out of order"
    -- Each branch names its block's keyword by `preconditionKeyword`, so
    -- that the keyword is written in one place.
    notes := #[if global then
        s!"note: the members of a global expectation are written `use`, `{preconditionKeyword global}`, `let`, `call`, `expect`, then `cover`"
      else s!"note: the members of a procedure are written `use`, `{preconditionKeyword global}`, `exists`, `let` and `out`, `call`, `ensure`, `expect`, then `cover`"] }

/-! ## Unused assumptions -/

/-- Whether `unused_assumption` fires on an assumption, from the number of
variables it mentions, whether all are inputs, whether one of them, or an
uninterpreted function it applies, is used in the procedure, and whether
one is read in the file (`lint::unused_assumption`). -/
def unusedAssumption (nMentioned : Nat) (allInputs mentioned read : Bool) : Bool :=
  nMentioned > 0 && allInputs && !mentioned && !read

/-- An uninterpreted function, as what links assumptions for
`unused_assumption`, beside variables: its path after a number, which no
variable's name has. -/
def fnLink (path : Name) : Name := Name.mkNum .anonymous 0 ++ path

/-- The assumptions, by their positions, that `markUsed` marks, given the
links `ms` of each, as many rounds as `fuel` allows: each round marks the
first assumption not yet in `out` that links one of `used`, and adds its
links to `used`, until there is none. -/
def markUsed [DecidableEq α] (ms : List (List α)) : Nat → List α → List Nat → List Nat
  | 0, _, out => out
  | fuel + 1, used, out =>
    match (List.range ms.length).find? fun i => !out.contains i && (ms.getD i []).any used.contains with
    | none => out
    | some i => markUsed ms fuel (used ++ ms.getD i []) (i :: out)

/-- Which of the assumptions, given the variables each mentions and the
uninterpreted functions each applies (`fnLink`), are used
(`lint::reached`): those that mention one of `used`, or one that a used
assumption mentions, transitively, since they constrain the same values.
Each round of `markUsed` marks one more assumption, or none. -/
def usedAssumptions [DecidableEq α] (mentions : Array (Array α)) (used : Array α) : Array Bool :=
  let ms := mentions.toList.map (·.toList)
  let marked := markUsed ms ms.length used.toList []
  (List.range ms.length).toArray.map (marked.contains ·)

/-- An assumption that `unused_assumption` may fire on: its procedure, its
name, the inputs it mentions, those and the uninterpreted functions it
applies (`fnLink`), and the level of the lint at the procedure. It fires
unless the file reads one of its links, or one that a used assumption of
the procedure mentions. -/
structure AssumptionRecord where
  component : Name
  name : Name
  inputs : Array Name
  links : Array Name
  level : LevelInEffect
  deriving Inhabited, Repr

def unusedAssumptionMsg (name : Name) (inputs linked : Array Name) : Msg :=
  let show_ (ns : Array Name) := ", ".intercalate (ns.toList.map (s!"`{·}`"))
  let together := if linked.isEmpty then #[] else
    #[s!"note: it is linked to {show_ linked}, reported too, which may need it: remove them together"]
  { code? := some Lint.unusedAssumption.code
    headline := s!"the assumption `{name}` constrains only parameters that nothing uses"
    label? := some "constrains only unused parameters"
    notes := #[s!"note: no guarantee, expectation, definition, argument or binding mentions {show_ inputs}, \
        nor does another assumption tie them to a used variable"] ++ together ++
      #["help: remove the assumption and its parameters, or use them"] }

/-- The messages of `unused_assumption`, given the parameters that the
file's calls, those in global expectations among them, give values: each
read's procedure and parameter. A `refines` claim reads none, since it
introduces none of its abstraction's assumptions
(`Reqs/Lang/Refinement`). An assumption is read when it mentions a read
parameter, or one that a read assumption of its procedure mentions. Each
message names the other reported assumptions linked to it. -/
def unusedAssumptionReports (rs : Array (AssumptionRecord × α)) (reads : Array (Name × Name)) :
    Array (LintReport α) :=
  let reported := rs.filter fun (r, _) =>
    let same := (rs.filter (·.1.component == r.component)).map (·.1)
    let used := usedAssumptions (same.map (·.links)) ((reads.filter (·.1 == r.component)).map (·.2))
    let read := (same.findIdx? (·.name == r.name)).any (used[·]!)
    unusedAssumption r.inputs.size true false read
  reported.map fun (r, ref) =>
    let others := (reported.filter fun (o, _) => o.component == r.component && o.name != r.name).map (·.1)
    let linked := usedAssumptions (others.map (·.links)) r.links
    let names := (others.zip linked).filterMap fun (o, l) => if l then some o.name else none
    { lint := .unusedAssumption, level := r.level, ref, msg := unusedAssumptionMsg r.name r.inputs names }

/-! ## Unrelated binders -/

/-- The groups of `binders` that `atoms`, the names each atom mentions,
relate: two binders are in one group when an atom mentions both, or each
is in one group with a third. A binder that no atom mentions is in none. -/
def binderGroups (binders : Array Name) (atoms : Array (Array Name)) : Array (Array Name) := Id.run do
  let mut groups : Array (Array Name) := #[]
  for a in atoms do
    let bs := binders.filter a.contains
    if bs.isEmpty then continue
    let (joined, rest) := groups.partition fun g => g.any bs.contains
    let merged := joined.foldl (· ++ ·) bs
    groups := rest.push (binders.filter merged.contains)
  return groups

/-- The atoms of `n`, a `Bool` expression: its operands through `and`
(`lint::unrelated_binders`). -/
partial def BNode.atoms (n : BNode α) : Array (BNode α) :=
  match n.kind with
  | .bin "and" => n.kids.flatMap (·.atoms)
  | _ => #[n]

/-- Whether `unrelated_binders` fires on a global expectation, from the
number of groups of its binders (`lint::unrelated_binders`). -/
def unrelatedBinders (nGroups : Nat) : Bool := nGroups ≥ 2

def unrelatedBindersMsg (name : String) (groups : Array (Array Name)) : Msg :=
  let show_ (g : Array Name) := ", ".intercalate (g.toList.map (s!"`{·}`"))
  { code? := some Lint.unrelatedBinders.code
    headline := s!"the calls of `{name}` fall into {groups.size} groups that nothing relates"
    label? := some s!"{groups.size} claims in one"
    notes := #[s!"note: no atom, argument or parameter relates a call of {show_ groups[0]!} and one of {show_ groups[1]!}",
      "help: relate the calls, or write one global expectation for each group"] }

/-! ## Record literals -/

/-- Whether `unnecessary_struct_initialization` fires on a record literal
of `n` fields, from whether each field's value reads that field of some
`r`, `r` is written the same in each, is a value rather than a call,
and has the record's type (`lint::unnecessary_struct_initialization`). -/
def unnecessaryStructInit (n : Nat) (readsOwn same value sameType : Bool) : Bool :=
  n > 0 && readsOwn && same && value && sameType

def unnecessaryStructInitMsg (r : String) : Msg :=
  { code? := some Lint.unnecessaryStructInitialization.code, headline := s!"this record literal is `{r}`"
    label? := some s!"copies each field of `{r}`"
    fixes := #[{ msg := s!"write `{r}`", replacement := r }] }

end Fren.Core
