-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Str
-- keep-sorted end

/-!
# Procedures, and the migration from components

A procedure (`Reqs/Lang/Procedures`) declares its inputs as parameters and
its public outputs as named results, and its other members in its block.
Components, which declared every variable as a member (`in x: T`,
`pub out y: U`), are migrated to procedures by the fixes of the parse
errors `F0158`, `F0159` and `F0160`, and their instances (`inst w: c { x
:= e }`) to calls (`call w := c(e)`) by the fix of `F0420`, which needs
the order of the callee's parameters (`Reqs/Lang/Procedures#migration`).
Both are pure functions here, over plain data, so that the requirements can
state them (`lang::migrated_member`, `lang::argument_order`).
-/

namespace Fren.Core

/-! ## Where a component's member goes -/

/-- What a member of a component declared (`lang::OldMember`). -/
inductive OldMember where
  /-- `in x: T`. -/
  | input
  /-- `[pub] [det] out x: T [:= e]`. -/
  | output (isPub isDet defined : Bool)
  /-- Anything else: a constraint, an instance, a `use`. -/
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Where a member of a component goes in the procedure that it is
migrated to (`lang::Placement`). -/
inductive Placement where
  /-- A parameter, in the order of the inputs. -/
  | param
  /-- A result, in the order of the public outputs. -/
  | result
  /-- A result, and in its place the member `out x := e` that defines it. -/
  | resultDefined
  /-- The member `exists x: T`. -/
  | «exists»
  /-- The member `let x: T := e`. -/
  | «let»
  /-- The member as it is. -/
  | kept
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Where a member of a component goes (`lang::migrated_member`): an input
is a parameter, a public output a result, defined in the block if it has a
definition, and a private output is chosen by the system, as `exists`, or
defined, as `let`. `det` stays where the output goes. -/
def placement : OldMember → Placement
  | .input => .param
  | .output true _ false => .result
  | .output true _ true => .resultDefined
  | .output false _ false => .exists
  | .output false _ true => .let
  | .other => .kept

/-- The members of a component that become its parameters, in order: its
inputs (`lang::migrated_params`). -/
def paramsOf (ms : List OldMember) : List Nat :=
  (List.range ms.length).filter fun i => ms[i]? == some .input

/-- The members of a component that become its results, in order: its
public outputs (`lang::migrated_params`). -/
def resultsOf (ms : List OldMember) : List Nat :=
  (List.range ms.length).filter fun i => match ms[i]? with
    | some (.output true _ _) => true
    | _ => false

/-! ## A call's arguments -/

/-- Whether a call gives each parameter of the called procedure an argument
(`call::Arity`). -/
inductive CallArity where
  | fits
  | tooMany
  | tooFew
  deriving Inhabited, DecidableEq, Repr

/-- Whether a call with `nArgs` arguments gives each of `nParams` parameters
one (`call::arguments`). -/
def callArity (nParams nArgs : Nat) : CallArity :=
  if nArgs == nParams then .fits else if nArgs > nParams then .tooMany else .tooFew

/-- What a call binds, if its arguments fit the called procedure's
parameters `params`: each parameter to the argument in its position
(`call::arguments`). Both front ends and the evaluator bind a call's
arguments so. -/
def callBindings {α : Type} (params : Array String) (args : Array α) : Option (Array (String × α)) :=
  if callArity params.size args.size == .fits then some (params.zip args) else none

/-! ## The order of an instance's bindings, as a call's arguments -/

/-- The arguments of a call, in the order of the callee's parameters
`params`, from an instance's bindings, by name (`lang::argument_order`):
each parameter's binding, if every parameter is bound exactly once and
nothing else is bound; otherwise `none`. -/
def argumentOrder {α : Type} (params : List String) (bindings : List (String × α)) : Option (List α) :=
  if bindings.length == params.length && params.all (fun p => (bindings.filter (·.1 == p)).length == 1)
  then params.mapM fun p => (bindings.find? (·.1 == p)).map (·.2)
  else none

/-! ## The text of a migrated component -/

/-- A variable member of a component, for the text of its migration: where
it is in the source, as offsets. -/
structure OldVar where
  /-- An input, rather than an output. -/
  isIn : Bool
  isPub : Bool
  isDet : Bool
  /-- From its first token, or its evidence setting's, to its last. -/
  range : Range
  /-- Its own first token, after any evidence setting. -/
  kwStart : Nat
  /-- Its name, as written. -/
  nameStart : Nat
  /-- The end of its name and type, before any definition. -/
  declStop : Nat
  /-- Where its `:=` starts, if it is defined. -/
  defnStart? : Option Nat
  /-- Its name, without the `!` of shadowing. -/
  name : String
  deriving Inhabited, Repr

/-- The text of `src` from `a` to `b`. -/
private def slice (src : Array Char) (a b : Nat) : String := String.ofList (src.extract a b).toList

/-- Where the line containing `i` starts. -/
private def lineStartOf (src : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j > 0 && src[j - 1]! != '\n' do j := j - 1
  return j

/-- Where the line containing `i` ends: its newline, or the end. -/
private def lineEndOf (src : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < src.size && src[j]! != '\n' do j := j + 1
  return j

private def blank (s : String) : Bool := s.all fun c => c == ' ' || c == '\t' || c == '\r'

/-- A comment, alone on its line, or after a member. -/
private def isComment (s : String) : Bool := (s.trimAscii.toString).startsWith "--"

/-- A comment that says something of another line, or of the file: a test's
expected message (`--~`) or setting (`--@`), which does not move with the
member below it. -/
private def isAnnotation (s : String) : Bool :=
  let t := s.trimAscii.toString
  t.startsWith "--~" || t.startsWith "--@"

/-- A member that moves out of the block: the range it leaves, its
trailing comment and that comment's column, and the comment lines just
above it, which move with it. -/
private structure Moved where
  removal : Range := { start := 0, stop := 0 }
  comment? : Option (String × Nat) := none
  above : Array String := #[]

/-- The range that `r`, a member, leaves when it moves out of the block
that opens at `open`: its lines, with any comment after it and the
comment lines just above it, if it is alone on them; otherwise itself and
the spaces after it. -/
private def moved (src : Array Char) (open_ : Nat) (r : Range) : Moved := Id.run do
  let ls := lineStartOf src r.start
  let le := lineEndOf src r.stop
  let before := slice src ls r.start
  let after := slice src r.stop le
  if ls > open_ && blank before && (blank after || isComment after) then
    let comment? := if blank after then none else
      let trimmed := after.trimAsciiStart.toString
      some (trimmed.trimAsciiEnd.toString, r.stop - ls + (after.length - trimmed.length))
    -- The comment lines just above it, after the `{`.
    let mut start := ls
    let mut above := #[]
    while start > 0 do
      let ps := lineStartOf src (start - 1)
      if ps ≤ open_ then break
      let line := slice src ps (start - 1)
      unless isComment line && !isAnnotation line do break
      above := #[line.trimAscii.toString] ++ above
      start := ps
    return { removal := { start, stop := min src.size (le + 1) }, comment?, above }
  let mut stop := r.stop
  while stop < src.size && (src[stop]! == ' ' || src[stop]! == '\t') do stop := stop + 1
  -- One that ends its line takes the spaces before it instead.
  let mut start := r.start
  if stop == src.size || src[stop]! == '\n' then
    stop := r.stop
    while start > 0 && (src[start - 1]! == ' ' || src[start - 1]! == '\t') do start := start - 1
  return { removal := { start, stop } }

/-- A parameter or result list: on one line if no element has a comment
and the line fits, else one element to a line, each indented by `indent`
plus 4, with a trailing comma and its comments, which keep their column
where they fit (`fmt::comment_column`). `prefix` is the text of the line
before the list, for its width. -/
private def listText (indent : Nat) (prefix_ suffix : String) (items : Array (String × Moved)) : String :=
  let flat := ", ".intercalate (items.map (·.1)).toList
  let commented := items.any fun (_, m) => m.comment?.isSome || !m.above.isEmpty
  if !commented && (prefix_ ++ "(" ++ flat ++ ")" ++ suffix).length ≤ 100 then "(" ++ flat ++ ")"
  else
    let pad := String.ofList (List.replicate (indent + 4) ' ')
    let lines := items.toList.map fun (t, m) =>
      let above := m.above.toList.map (pad ++ · ++ "\n")
      let code := pad ++ t ++ ","
      let line := match m.comment? with
        | some (c, col) => code ++ String.ofList (List.replicate ((max col (code.length + 2)) - code.length) ' ') ++ c
        | none => code
      String.join above ++ line ++ "\n"
    "(\n" ++ String.join lines ++ String.ofList (List.replicate indent ' ') ++ ")"

/-- The lines of a block, with the blank lines that the members leave
removed: those after its `{`, before its `}`, and all but one of each run.
A block left with no members is `{}`. -/
private def tidyBlock (body : String) : String :=
  let lines := body.splitOn "\n"
  if lines.length ≤ 1 then
    -- `{ ... }` on one line.
    let inner := ((body.drop 1).dropEnd 1).toString
    if blank inner then "{}" else body
  else
    let first := lines.head!
    let last := lines.getLast!
    let middle := (lines.drop 1).dropLast
    if middle.all blank && blank ((first.drop 1).toString) && blank ((last.dropEnd 1).toString) then "{}" else
    let middle := (middle.dropWhile blank).reverse.dropWhile blank |>.reverse
    let middle := middle.foldl (init := ([] : List String)) fun acc l =>
      if blank l && acc.getLast?.any blank then acc else acc ++ [l]
    "\n".intercalate (first :: middle ++ [last])

/-- The range that the member at `r` leaves when it moves out of the block
whose `{` is at `open_`: its lines, with any comment after it and the
comment lines just above it, if it is alone on them. -/
def memberRemoval (src : Array Char) (open_ : Nat) (r : Range) : Range := (moved src open_ r).removal

/-- The text of the procedure that a component migrates to (`F0158`), in
place of the component from `start`, its `pub` or `comp`, to the end of
its `}` at `stop`: `comp` at `compTok` is `proc`, its inputs `vars` are
parameters and its public outputs results, in order; a public output's
definition is the member `out x := e` in its place; and a private output
is `exists` or `let`, in place (`lang::migrated_member`). The block keeps
everything else as written. -/
def procText (src : Array Char) (start : Nat) (compTok : Range) (openBrace : Nat) (stop : Nat)
    (vars : Array OldVar) : String := Id.run do
  let indent := start - lineStartOf src start
  -- Where each variable goes (`lang::migrated_member`), and the order of
  -- the parameters and results (`lang::migrated_params`).
  let olds := vars.toList.map fun v => if v.isIn then OldMember.input else .output v.isPub v.isDet v.defnStart?.isSome
  let mut params : Array (String × Moved) := #[]
  let mut results : Array (String × Moved) := #[]
  let mut edits : Array (Range × String) := #[]
  for i in paramsOf olds do
    let v := vars[i]!
    let m := moved src openBrace v.range
    params := params.push (slice src v.nameStart v.declStop, m)
    edits := edits.push (m.removal, "")
  for i in resultsOf olds do
    let v := vars[i]!
    let evidence := if v.range.start < v.kwStart then (slice src v.range.start v.kwStart).trimAscii.toString ++ " " else ""
    let text := evidence ++ (if v.isDet then "det " else "") ++ slice src v.nameStart v.declStop
    match placement olds[i]!, v.defnStart? with
    | .resultDefined, some d =>
      results := results.push (text, {})
      edits := edits.push ({ start := v.range.start, stop := d }, s!"out {v.name} ")
    | _, _ =>
      let m := moved src openBrace v.range
      results := results.push (text, m)
      edits := edits.push (m.removal, "")
  for v in vars, o in olds do
    let kw := match placement o with
      | .exists => some "exists "
      | .let => some "let "
      | _ => none
    if let some kw := kw then
      edits := edits.push ({ start := v.kwStart, stop := v.nameStart }, (if v.isDet then "det " else "") ++ kw)
  let head := slice src start compTok.start ++ "proc" ++ (slice src compTok.stop openBrace).trimAsciiEnd.toString
  let paramList := listText indent (String.ofList (List.replicate indent ' ') ++ head) "" params
  let lastLine := ((head ++ paramList).splitOn "\n").getLast!
  let resultList := if results.isEmpty then "" else
    ": " ++ listText indent (String.ofList (List.replicate indent ' ') ++ lastLine ++ ": ") " {" results
  -- The block, from its `{`, with the edits made.
  let block := src.extract openBrace stop
  let sorted := edits.qsort fun (a, _) (b, _) => a.start < b.start
  let mut out := ""
  let mut pos := 0
  for (r, t) in sorted do
    let a := r.start - openBrace
    if a < pos then continue
    out := out ++ String.ofList (block.extract pos a).toList ++ t
    pos := r.stop - openBrace
  out := out ++ String.ofList (block.extract pos block.size).toList
  return head ++ paramList ++ resultList ++ " " ++ tidyBlock out

/-- The text of the call that an instance migrates to (`F0420`): `call w
:= c(a, b)`, with `args` in the order of the callee's parameters, on one
line, or with `vertical`, one to a line, indented by `indent` plus 4, with
a trailing comma, as the instance's bindings were. -/
def callText (indent : Nat) (w path : String) (args : List String) (vertical : Bool) : String :=
  if vertical && !args.isEmpty then
    let pad := String.ofList (List.replicate (indent + 4) ' ')
    s!"call {w} := {path}(\n" ++ String.join (args.map fun a => pad ++ a ++ ",\n") ++ String.ofList (List.replicate indent ' ') ++ ")"
  else s!"call {w} := {path}({", ".intercalate args})"

/-! ## Messages -/

/-- A component, written as components were before procedures (`F0158`):
`fixed` is the procedure it migrates to, if it is known. -/
def compSyntaxMsg (fixed? : Option String) : Msg :=
  { code? := some "F0158", headline := "components are written as procedures"
    label? := some "`comp`"
    notes := #["note: a procedure is written `proc p(x: T): (y: U) { ... }`: its inputs are parameters, its public outputs \
      are named results, and its private outputs are `exists` or `let` members"]
    fixes := fixed?.toArray.map fun replacement => { msg := "write it as a procedure", replacement } }

/-- An `in` member of a procedure (`F0159`), whose fix makes it a
parameter. -/
def inputMemberMsg (fix? : Option (Range × String)) : Msg :=
  { code? := some "F0159", headline := "inputs are written as parameters"
    label? := some "an `in` member"
    notes := #["note: a procedure's inputs are its parameters, as in `proc p(x: T) { ... }`"]
    fixes := fix?.toArray.map fun (r, replacement) => { msg := "make it a parameter", replacement, range? := some r } }

/-- An output declared as components declared them, `[pub] [det] out x: T
[:= e]`, in a procedure (`F0160`): public, it is a result; private, it is
`exists`, or `let` if it is defined. -/
def outputMemberMsg (isPub defined : Bool) (fix? : Option (Range × String)) : Msg :=
  let (headline, help) :=
    if isPub then ("public outputs are written as results", "make it a result")
    else if defined then ("a private output with a definition is written `let`", "write `let`")
    else ("a private output is written `exists`", "write `exists`")
  { code? := some "F0160", headline, label? := some "an `out` declaration"
    notes := #["note: a procedure's public outputs are its named results, as in `proc p(x: T): (y: U) { ... }`, \
      defined, if at all, by `out y := e`; a private output is `exists z: V`, or `let z: V := e` with a definition"]
    fixes := fix?.toArray.map fun (r, replacement) => { msg := help, replacement, range? := some r } }

/-- An instance, written as instances were before calls (`F0420`), of the
procedure `callee`: `fixed` is the call it migrates to, if its bindings
bind each of `callee`'s parameters once (`lang::argument_order`). -/
def instSyntaxMsg (callee : String) (fixed? : Option String) : Msg :=
  { code? := some "F0420", headline := "instances are written as calls"
    label? := some "`inst`"
    notes := #[s!"note: a call is written `call w := {callee}(a, b)`, with an argument for each of `{callee}`'s parameters, in order"]
      ++ (if fixed?.isNone then #[s!"note: it does not bind each parameter of `{callee}` exactly once, so it has no fix"] else #[])
    fixes := fixed?.toArray.map fun replacement =>
      { msg := s!"write it as a call, with the arguments in the order of `{callee}`'s parameters", replacement } }

/-- A result defined by more than one `out` member (`F0421`). -/
def resultDefinedTwiceMsg (r : String) : Msg :=
  { code? := some "F0421", headline := s!"result `{r}` is defined more than once"
    label? := some "defined again here"
    notes := #["note: a result is defined by one `out` member at most, or is chosen by the system"] }

/-- A call with `given` arguments, of a procedure with `params`
(`F0408`, `F0409`). -/
def callArityMsg (callee : String) (params : Array String) (given : Nat) : Msg :=
  let n := params.size
  let takes := if n == 0 then "takes no arguments"
    else s!"takes {n} argument{if n == 1 then "" else "s"}, {", ".intercalate (params.toList.map fun p => s!"`{p}`")}"
  if given > n then
    { code? := some "F0408", headline := s!"too many arguments: `{callee}` {takes}"
      label? := some s!"{given} arguments", notes := #["note: a call gives one argument for each parameter, in order"] }
  else
    let missing := params.extract given n
    { code? := some "F0409", headline := s!"too few arguments: `{callee}` {takes}"
      label? := some s!"{given} argument{if given == 1 then "" else "s"}"
      notes := #["note: a call gives one argument for each parameter, in order",
        s!"help: add {", ".intercalate (missing.toList.map fun p => s!"`{p}`")}"] }

end Fren.Core
