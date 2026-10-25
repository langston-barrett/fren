-- keep-sorted start
import FrenCore.Names
import FrenCore.Simplify
-- keep-sorted end

/-!
# Lints

Lints (`Reqs/Lint`) as pure functions, shared by both front ends: their
levels, how settings combine, the import and naming lints, unused
variables, dead code, simpler `Bool` expressions, and expectations. Each
front end records what happened while elaborating a file (`UseRecord`,
`UsedName`, `ExpectationRecord`) and calls `importReports` and
`expectationReports` at its end.
-/

open Lean

namespace Fren.Core

inductive LintLevel where
  | allow
  | expect
  | warn
  | deny
  | forbid
  deriving Inhabited, BEq, DecidableEq, Repr

def LintLevel.all : Array LintLevel := #[.allow, .expect, .warn, .deny, .forbid]

def LintLevel.name : LintLevel → String
  | .allow => "allow"
  | .expect => "expect"
  | .warn => "warn"
  | .deny => "deny"
  | .forbid => "forbid"

def LintLevel.ofName? (s : String) : Option LintLevel := LintLevel.all.find? (·.name == s)

/-- The severity of a lint's message (`lint::severity`); `none` if it is
not reported. -/
def LintLevel.severity? : LintLevel → Option Severity
  | .allow | .expect => none
  | .warn => some .warning
  | .deny | .forbid => some .error

inductive Lint where
  | unusedImports
  | globImports
  | nonSnakeCase
  | nonCamelCaseTypes
  | nonUpperCaseConstants
  | unfulfilledExpectations
  | unusedVariables
  | deadCode
  | nonminimalBool
  | undecidable
  | lengthZero
  | cardZero
  | singletonMembership
  | membershipChain
  | constantOutput
  | definableOutput
  | indexAfterUse
  deriving Inhabited, BEq, DecidableEq, Repr

def Lint.all : Array Lint :=
  #[.unusedImports, .globImports, .nonSnakeCase, .nonCamelCaseTypes, .nonUpperCaseConstants, .unfulfilledExpectations,
    .unusedVariables, .deadCode, .nonminimalBool, .undecidable, .lengthZero, .cardZero,
    .singletonMembership, .membershipChain, .constantOutput, .definableOutput, .indexAfterUse]

def Lint.name : Lint → String
  | .unusedImports => "unused_imports"
  | .globImports => "glob_imports"
  | .nonSnakeCase => "non_snake_case"
  | .nonCamelCaseTypes => "non_camel_case_types"
  | .nonUpperCaseConstants => "non_upper_case_constants"
  | .unfulfilledExpectations => "unfulfilled_lint_expectations"
  | .unusedVariables => "unused_variables"
  | .deadCode => "dead_code"
  | .nonminimalBool => "nonminimal_bool"
  | .undecidable => "undecidable"
  | .lengthZero => "length_zero"
  | .cardZero => "card_zero"
  | .singletonMembership => "singleton_membership"
  | .membershipChain => "membership_chain"
  | .constantOutput => "constant_output"
  | .definableOutput => "definable_output"
  | .indexAfterUse => "index_after_use"

def Lint.code : Lint → String
  | .unusedImports => "F0701"
  | .globImports => "F0702"
  | .nonSnakeCase => "F0703"
  | .nonCamelCaseTypes => "F0704"
  | .nonUpperCaseConstants => "F0705"
  | .unfulfilledExpectations => "F0706"
  | .unusedVariables => "F0710"
  | .deadCode => "F0711"
  | .nonminimalBool => "F0712"
  -- `F0713` was `shadowed_constants`, which explicit shadowing replaced
  -- (`F0217`); it is not reused.
  | .undecidable => "F0714"
  | .lengthZero => "F0715"
  | .cardZero => "F0716"
  | .singletonMembership => "F0717"
  | .membershipChain => "F0718"
  | .constantOutput => "F0719"
  | .definableOutput => "F0720"
  | .indexAfterUse => "F0721"

/-- `undecidable` is denied, so that a spec opts out of decidability
explicitly (`Reqs/Lang/Decidability`); `membership_chain` and
`definable_output` are allowed, since they would fire on much that reads
well as it is. -/
def Lint.default : Lint → LintLevel
  | .undecidable => .deny
  | .membershipChain | .definableOutput => .allow
  | _ => .warn

def Lint.ofName? (s : String) : Option Lint := Lint.all.find? (·.name == s)

/-- The Lean option that sets the lint's level, `fren.lint.NAME`. -/
def Lint.option (l : Lint) : Name := `fren.lint ++ Name.mkSimple l.name

/-- `fren.lint.NAME` as written in `set_option`. -/
def Lint.optionString (l : Lint) : String := s!"fren.lint.{l.name}"

/-- One setting of a lint's level (`lint::setting`): whether it is
accepted, and the level after it. -/
def setLevel (current requested : LintLevel) : Bool × LintLevel :=
  let ok := current != .forbid || requested == .forbid
  (ok, if ok then requested else current)

/-- The level of a lint from its default, the command line and a setting
in the file (`lint::effective`), and whether that setting is an error. -/
def effectiveLevel (dflt : LintLevel) (cli? src? : Option LintLevel) : LintLevel × Bool :=
  let afterCli := match cli? with
    | some c => (setLevel dflt c).2
    | none => dflt
  match src? with
  | some s => let (ok, l) := setLevel afterCli s; (l, !ok)
  | none => (afterCli, false)

/-- The level of a lint at some place, and where it comes from. -/
structure LevelInEffect where
  level : LintLevel
  /-- Set by the command line or a `set_option`, rather than the default. -/
  isSet : Bool := false
  /-- At `expect`: the expectation, an index into the file's expectations.
  `expect` with no expectation, as from options outside a Lean file, means
  `allow`. -/
  expectation? : Option Nat := none
  deriving Inhabited, Repr

def LevelInEffect.ofDefault (l : Lint) : LevelInEffect := { level := l.default }

/-- The level that decides what happens: `expect` without an expectation
is `allow`. -/
def LevelInEffect.effective (l : LevelInEffect) : LintLevel :=
  if l.level == .expect && l.expectation?.isNone then .allow else l.level

/-- The levels of every lint at some place. -/
abbrev Levels := Array (Lint × LevelInEffect)

def Levels.defaults : Levels := Lint.all.map fun l => (l, .ofDefault l)

def Levels.get (ls : Levels) (l : Lint) : LevelInEffect :=
  ((ls.find? (·.1 == l)).map (·.2)).getD (.ofDefault l)

def Levels.set (ls : Levels) (l : Lint) (v : LevelInEffect) : Levels :=
  if ls.any (·.1 == l) then ls.map fun (l', v') => (l', if l' == l then v else v') else ls.push (l, v)

/-- The levels set by command-line flags, in order: the last flag for a
lint wins, except that `forbid` always wins. -/
def Levels.ofFlags (flags : Array (Lint × LintLevel)) : Levels :=
  flags.foldl (init := Levels.defaults) fun ls (l, v) =>
    ls.set l { level := (setLevel (ls.get l).level v).2, isSet := true }

/-! ## Collections, outputs and indexes -/

/-- Whether `length_zero` and `card_zero` fire on `n OP bound`, with the
length `n` on the left, and whether the fix says that it is empty
(`lint::length_zero`). -/
def lengthZero (op : Comparison) (bound : Int) : Bool × Bool :=
  match op with
  | .eq | .le => (bound == 0, true)
  | .gt => (bound == 0, false)
  | _ => (false, true)

/-- `n OP 0`, where `recv` is the text of the collection and `empty` that
of an empty one, such as `""`, `[]` or `{}`. -/
def lengthZeroMsg (card : Bool) (recv empty : String) (isEmpty : Bool) : Msg :=
  let m := if card then "card" else "len"
  let fixed := s!"{recv} {if isEmpty then "=" else "!="} {empty}"
  { code? := some (if card then "F0716" else "F0715"), headline := s!"say whether it is empty with `{empty}`, not `{m}`"
    label? := some "compares a length with 0"
    fixes := #[{ msg := s!"compare with `{empty}`", replacement := fixed }] }

/-- `x in {a}`, as the texts of `x` and `a`. -/
def singletonMembershipMsg (x a : String) : Msg :=
  { code? := some "F0717", headline := "membership in a set of one member is equality", label? := some "a set of one"
    fixes := #[{ msg := "write it as an equation", replacement := s!"{x} = {a}" }] }

/-- Whether `membership_chain` fires on `n` disjuncts, which all equate the
same left operand if `sameLeft` (`lint::membership_chain`). -/
def membershipChainFires (n : Nat) (sameLeft : Bool) : Bool := sameLeft && n ≥ 3

/-- `x = a or x = b or ...`, as the texts of `x` and the others. -/
def membershipChainMsg (x : String) (vals : Array String) : Msg :=
  { code? := some "F0718", headline := s!"this is `{x}` in a set of {vals.size}", label? := some "a chain of `or`"
    fixes := #[{ msg := "write it as a membership", replacement := s!"{x} in \{{", ".intercalate vals.toList}}" }] }

/-- Whether `constant_output` and `definable_output` fire on an output
(`lint::output_lints`). -/
def outputLints (defined : Bool) (nVariables nReqs : Nat) (equation : Bool) : Bool × Bool :=
  (defined && nVariables == 0, !defined && nReqs == 1 && equation)

def constantOutputMsg (x : Name) : Msg :=
  { code? := some "F0719", headline := s!"defined output `{x}` is the same in every behaviour"
    label? := some "mentions no variable"
    notes := #["help: make it a `const`, which is shared by every component"] }

def definableOutputMsg (x : Name) (req : Name) : Msg :=
  { code? := some "F0720", headline := s!"`{req}` could be the definition of `{x}`"
    label? := some "constrained by one equation"
    notes := #[s!"help: write the expression as `{x}`'s definition, `out {x} := ...`, and remove `{req}`"] }

/-- Whether `index_after_use` fires (`lint::index_after_use`). -/
def indexAfterUse (indexesLeft boundsRight : Bool) : Bool := indexesLeft && boundsRight

/-- `a and b`, as their texts, where `b` bounds what `a` indexes. -/
def indexAfterUseMsg (a b : String) : Msg :=
  { code? := some "F0721", headline := "the bound comes after the index it guards", label? := some "indexed before it is bounded"
    notes := #["note: in `a and b`, `b` is guarded by `a`, not the other way around, so the index may be out of range"]
    fixes := #[{ msg := "put the bound first, which does not change the meaning", replacement := s!"{b} and {a}" }] }

/-! ## Settings -/

/-- The note listing the lints, sorted by name. -/
def lintsNote : String :=
  s!"note: the lints are {", ".intercalate (((Lint.all.map (·.name)).qsort (· < ·)).map (s!"`{·}`")).toList}"

/-- The note for a lint that Fren had but removed, if `n` is one. -/
def removedLintNotes (n : String) : Array String :=
  if n == "shadowed_constants" then
    #["note: `shadowed_constants` was removed; shadowing without `!` is now an error (F0217)"]
  else #[]

def unknownLintMsg (n : String) : Msg :=
  { code? := some "F0707", headline := s!"unknown lint `{n}`", label? := some "no such lint"
    notes := removedLintNotes n ++ #[lintsNote]
    fixes := (similarStr n (Lint.all.map (·.name))).toArray.map fun s =>
      { msg := s!"a lint with a similar name exists: `{s}`", replacement := s!"fren.lint.{s}" } }

def invalidLevelMsg (v : String) : Msg :=
  { code? := some "F0708", headline := s!"invalid lint level `{v}`", label? := some "not a lint level"
    notes := #["note: a lint level is `\"allow\"`, `\"expect\"`, `\"warn\"`, `\"deny\"` or `\"forbid\"`"]
    fixes := (similarStr v (LintLevel.all.map (·.name))).toArray.map fun s =>
      { msg := s!"a level with a similar name exists: `\"{s}\"`", replacement := s!"\"{s}\"" } }

def forbiddenMsg (l : Lint) (requested : LintLevel) : Msg :=
  { code? := some "F0709", headline := s!"`{requested.name}` for `{l.name}` is incompatible with an earlier `forbid`"
    label? := some s!"cannot change the level of `{l.name}`"
    notes := #["note: once a lint is `forbid`, its level cannot be changed"] }

/-! ## Messages -/

/-- The note on the first message of each lint in a file: where its level
comes from. -/
def levelNotes (l : Lint) (lv : LevelInEffect) : Array String :=
  if lv.isSet then #[s!"note: `{l.name}` is set to `{lv.level.name}`"]
  else #[s!"note: `{l.name}` is `{lv.level.name}` by default",
    s!"help: to allow it, `set_option {l.optionString} \"allow\"`"]

/-- A lint's message, at a place where its level is `lv`. -/
structure LintReport (α : Type) where
  lint : Lint
  level : LevelInEffect
  /-- Where to report it, as the front end knows it. -/
  ref : α
  msg : Msg
  deriving Inhabited

/-- The messages that are reported, with the level note on the first of
each lint, and the severity of each; and the expectations that the others
fulfil. -/
def finishReports (rs : Array (LintReport α)) : Array (LintReport α × Severity) × Array Nat := Id.run do
  let mut out := #[]
  let mut fulfilled := #[]
  let mut noted : Array Lint := #[]
  for r in rs do
    match r.level.effective with
    | .allow => pure ()
    | .expect => fulfilled := fulfilled.push r.level.expectation?.get!
    | lv =>
      let msg := if noted.contains r.lint then r.msg else
        { r.msg with notes := r.msg.notes ++ levelNotes r.lint r.level }
      noted := noted.push r.lint
      out := out.push ({ r with msg }, lv.severity?.get!)
  return (out, fulfilled)

/-! ## Imports -/

/-- A `use` declared in the file being elaborated. -/
structure UseRecord where
  /-- Its scope: the module, or the path of the component containing it. -/
  module : Name
  /-- The full path of the imported item; for a glob, of the opened enum. -/
  target : Name
  glob : Bool
  /-- The levels of `unused_imports` and `glob_imports` at the `use`. -/
  unusedLevel : LevelInEffect
  globLevel : LevelInEffect
  deriving Inhabited, Repr

/-- A path's first segment `name`, in `module`, resolved through an
import of `target` (`glob` if by `use target::*`). -/
structure UsedName where
  module : Name
  target : Name
  glob : Bool
  name : Name
  deriving Inhabited, BEq, Repr

/-- The import that the first segment of a path in the scope `from_`
resolves through (`modules::resolve`), if it resolves through one: a named
import, or the enum opened by `*`. The `module` of the result is the scope
of that import: a component's imports shadow its module's scope. -/
def Table.importVia (t : Table) (from_ : Name) (segs : Array Name) : Option UsedName := do
  let n ← segs[0]?
  let comp := t.isComp from_ && (t.uses.getD from_ #[]).any (·.brings t n)
  if n == `self || (!comp && (t.declared? (t.moduleOf from_) n).isSome) then none
  let uses := if comp then t.uses.getD from_ #[] else t.uses.getD (t.moduleOf from_) #[]
  if let some u := uses.find? (fun u => !u.glob && u.target.getString! == n.toString) then
    return { module := u.scope, target := u.target, glob := false, name := n }
  let enums := uses.foldl (init := #[]) fun (acc : Array (Name × Name)) u =>
    if u.glob && !acc.any (·.1 == u.target) && ((t.enums.get? u.target).any (·.variants.contains n)) then
      acc.push (u.target, u.scope)
    else acc
  match enums with
  | #[(e, scope)] => return { module := scope, target := e, glob := true, name := n }
  | _ => none

/-- The import that the declaration `n`, written with `!` if `bang`, hides
a name through, if any: the declaration depends on it, so it counts as
used, by `unused_imports` and by a glob that `glob_imports` narrows
(`Reqs/Lint#unused-imports`). A local of `locals` that it hides instead
hides the import too, so the import is not needed. -/
def Table.shadowedImport? (t : Table) (scope : Name) (locals : Array (Name × String)) (n : Name) (bang : Bool) :
    Option UsedName :=
  if bang && !locals.any (·.1 == n) && (t.hidden? scope #[] n).isSome then t.importVia scope #[n] else none

/-- Whether a `use` is unused (`lint::unused_import`). -/
def unusedImport (glob : Bool) (nPaths : Nat) (first : Bool) : Bool :=
  nPaths == 0 || (glob && !first)

/-- The line on the messages of lints that `fren fix` fixes. -/
def fixHelp : String := "help: `fren fix` can fix this"

def unusedImportMsg (target : Name) (glob : Bool) (fixable : Bool := false) : Msg :=
  { code? := some (Lint.unusedImports.code)
    headline := s!"unused import `{showPath target}{if glob then "::*" else ""}`", label? := some "unused"
    notes := #["help: remove this `use`"] ++ (if fixable then #[fixHelp] else #[]) }

/-- `used`, without repeats, sorted as `fren fmt` sorts a group. -/
def sortedNames (used : Array Name) : Array Name :=
  let names := used.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
  names.qsort (·.toString < ·.toString)

def globImportMsg (enum : Name) (used : Array Name) (fixable : Bool := false) : Msg :=
  let used := sortedNames used
  let e := enum.getString!
  let named := match used.toList with
    | [v] => s!"`use {showPath enum}::{v}`"
    | vs => s!"`use {showPath enum}::\{{", ".intercalate (vs.map toString)}}`"
  let example_ := (used[0]?.map toString).getD "Variant"
  { code? := some (Lint.globImports.code)
    headline := s!"`use {showPath enum}::*` imports every variant of `{e}`", label? := some "glob import"
    notes := #["note: a name opened with `*` does not say where it comes from, and a variant added later can make a name ambiguous"]
      ++ (if used.isEmpty then #[] else #[s!"help: import the variants used here by name: {named}"])
      ++ #[s!"help: or write them qualified, as in `{e}::{example_}`"]
      ++ (if fixable && !used.isEmpty then #[fixHelp] else #[]) }

/-- The names that paths resolve through a `use`. -/
def UseRecord.hits (u : UseRecord) (used : Array UsedName) : Array UsedName :=
  used.filter fun x => x.module == u.module && x.target == u.target && x.glob == u.glob

/-- The names that paths resolve through the glob `u`, without repeats and
sorted. -/
def UseRecord.globNames (u : UseRecord) (used : Array UsedName) : Array Name :=
  sortedNames ((u.hits used).map (·.name))

/-- The import lints of a file, in the order of its `use`s, each at the
`ref` of its `use`. With `fixable`, the messages that `fren fix` would fix
say so. -/
def importReports (uses : Array (UseRecord × α)) (used : Array UsedName) (fixable : Bool := false) :
    Array (LintReport α) := Id.run do
  let mut out := #[]
  for (u, ref) in uses, i in [0:uses.size] do
    let first := !(uses.extract 0 i).any fun (u', _) => u'.module == u.module && u'.glob && u'.target == u.target
    let unused := unusedImport u.glob (u.hits used).size first
    if unused then
      out := out.push { lint := .unusedImports, level := u.unusedLevel, ref, msg := unusedImportMsg u.target u.glob fixable }
    if u.glob then
      -- An unused glob is removed rather than imported by name.
      let msg := globImportMsg u.target (u.globNames used) (fixable && !unused)
      out := out.push { lint := .globImports, level := u.globLevel, ref, msg }
  return out

/-! ## Fixes -/

/-- What `fren fix` does with a `use` (`lint::ImportFix`). -/
inductive ImportFix where
  | keep
  | remove
  | byName
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The fix of a `use` that is not in a group, from the lints that fire at
it and whether each is fixed (`lint::import_fix`). -/
def importFix (unused glob fixUnused fixGlob : Bool) (nUsed : Nat) : ImportFix :=
  if unused && fixUnused then .remove
  else if glob && fixGlob && !unused && nUsed > 0 then .byName
  else .keep

/-- Whether `fren fix` fixes lint `l`, from the lints given to `--only` and
to `--skip` (`lint::fix_selected`). -/
def fixSelected (only skip : Array Lint) (l : Lint) : Bool :=
  (only.isEmpty || only.contains l) && !skip.contains l

/-- The exit status of `fren fix` (`lint::fix_exit`). -/
def fixExit (check loaded allFixed : Bool) : UInt32 :=
  if !loaded then 2 else if check && !allFixed then 1 else 0

/-- The range to delete to remove `r` from `src`: with the rest of its line
if nothing else is on it. -/
def deletionRange (src : Array Char) (r : Range) : Range := Id.run do
  let blank (c : Char) := c == ' ' || c == '\t'
  let mut a := r.start
  while a > 0 && blank src[a - 1]! do a := a - 1
  let mut b := r.stop
  while b < src.size && blank src[b]! do b := b + 1
  let lineStart := a == 0 || src[a - 1]! == '\n'
  let lineEnd := b == src.size || src[b]! == '\n'
  if lineStart && lineEnd then
    return { start := a, stop := min src.size (b + 1) }
  -- What follows, such as a comment, moves to the start of the line.
  if lineStart then return { start := a, stop := b }
  return r

/-- `src` with `edits` applied. Of overlapping edits, the one that starts
first, or the longer of two that start together, wins. -/
def applyEdits (src : Array Char) (edits : Array (Range × String)) : String := Id.run do
  let sorted := edits.qsort fun (r, _) (r', _) => r.start < r'.start || (r.start == r'.start && r.stop > r'.stop)
  let mut out := ""
  let mut pos := 0
  for (r, s) in sorted do
    if r.start < pos then continue
    out := out ++ String.ofList (src.extract pos r.start).toList ++ s
    pos := r.stop
  return out ++ String.ofList (src.extract pos src.size).toList

/-! ## Naming conventions -/

inductive Case where
  | snake
  | camel
  | upper
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What a declared name names (`lint::Named`). -/
inductive Named where
  | module
  | component
  | variable
  /-- A field of a record. -/
  | field
  /-- A binder of a `match` pattern. -/
  | binder
  | function
  | instance
  | constraint
  | global
  | enumeration
  | variant
  | record
  | abstractType
  | constant
  deriving Inhabited, BEq, DecidableEq, Repr

def Named.describe : Named → String
  | .module => "module"
  | .component => "component"
  | .variable => "variable"
  | .field => "field"
  | .binder => "binder"
  | .function => "function"
  | .instance => "instance"
  | .constraint => "constraint"
  | .global => "global expectation"
  | .enumeration => "enum"
  | .variant => "variant"
  | .record => "record"
  | .abstractType => "abstract type"
  | .constant => "constant"

/-- The case of a name (`lint::naming_case`). -/
def Named.case : Named → Case
  | .enumeration | .variant | .record | .abstractType => .camel
  | .constant => .upper
  | _ => .snake

def Case.lint : Case → Lint
  | .snake => .nonSnakeCase
  | .camel => .nonCamelCaseTypes
  | .upper => .nonUpperCaseConstants

def Case.describe : Case → String
  | .snake => "a snake case"
  | .camel => "a camel case"
  | .upper => "an upper case"

/-- Whether a name is in a case, from its letters (`lint::in_case`). -/
def inCase (c : Case) (startsUpper hasUpper hasLower hasUnderscore : Bool) : Bool :=
  match c with
  | .snake => !hasUpper
  | .camel => startsUpper && !hasUnderscore
  | .upper => startsUpper && !hasLower

def isUpperAscii (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def isLowerAscii (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- The name without a variable's final `?`. -/
def baseName (s : String) : String := (s.dropEndWhile (· == '?')).toString

/-- Whether `s` is in case `c` (`lint::in_case`). A variable's final `?`
is neither a letter nor `_`, so it changes nothing. -/
def nameInCase (s : String) (c : Case) : Bool :=
  let cs := s.toList
  inCase c (cs.head?.any isUpperAscii) (cs.any isUpperAscii) (cs.any isLowerAscii) (cs.contains '_')

/-- The words of a name: split at `_` and before an uppercase letter that
follows a lowercase letter or a digit. -/
def words (s : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut prev : Option Char := none
  for c in s.toList do
    if c == '_' then
      out := out.push cur; cur := ""
    else
      if isUpperAscii c && prev.any (fun p => isLowerAscii p || p.isDigit) then
        out := out.push cur; cur := ""
      cur := cur.push c
    prev := some c
  return (out.push cur).toList.filter (!·.isEmpty)

/-- `s` converted to case `c`, keeping a final `?`. -/
def toCase (c : Case) (s : String) : String :=
  let q := String.ofList (s.toList.reverse.takeWhile (· == '?'))
  let ws := words (baseName s)
  let base := match c with
    | .snake => "_".intercalate (ws.map String.toLower)
    | .upper => "_".intercalate (ws.map String.toUpper)
    | .camel => String.join (ws.map fun w => (w.toLower.capitalize))
  base ++ q

/-- The naming lint for a declared name, if it is not in its case. -/
def namingMsg? (what : Named) (n : Name) : Option (Lint × Msg) :=
  let s := n.toString
  let c := what.case
  if nameInCase s c then none else
  let fixed := toCase c s
  let fixes := if fixed.isEmpty || fixed == s || (fixed.front.isDigit) || !nameInCase fixed c then #[]
    else #[{ msg := s!"rename it to `{fixed}`", replacement := fixed : Fix }]
  some (c.lint, {
    code? := some c.lint.code, headline := s!"{what.describe} `{s}` should have {c.describe} name"
    label? := some s!"not in {match c with | .snake => "snake_case" | .camel => "CamelCase" | .upper => "UPPER_CASE"}"
    fixes })

/-! ## Unused variables -/

/-- The message of `unused_variables` for a variable of a component
(`binder` false) or a binder of a global expectation. -/
def unusedVariableMsg (n : Name) (binder : Bool) (output : Bool) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused {if binder then "binder" else "variable"} `{n}`", label? := some "never mentioned"
    notes := (if binder then #[] else if output then #["note: nothing constrains it, so it can take any value"]
        else #["note: nothing in its component depends on it"])
      ++ #[s!"help: remove it, or mention it in {if binder then "the expectation" else "a constraint"}"] }

/-- A parameter of a defined function that its body never mentions. -/
def unusedParamMsg (n : Name) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused parameter `{n}`", label? := some "never mentioned"
    notes := #["note: the function's value does not depend on it", "help: remove it, or mention it in the body"] }

/-- The variables, or binders, of `declared` that `mentioned` does not
contain, in order. -/
def unmentioned (declared : Array (Name × α)) (mentioned : Array Name) : Array (Name × α) :=
  declared.filter fun (n, _) => !mentioned.contains n

/-! ## Dead code -/

/-- Whether an item is dead (`lint::dead_item`). -/
def deadItem (what : Named) (isPub : Bool) (nUses : Nat) : Bool :=
  match what with
  | .enumeration | .record | .abstractType | .function | .constant => !isPub && nUses == 0
  | _ => false

/-- A private enumeration, record, abstract type, function or constant declared in
the file being elaborated, with the level of `dead_code` there. -/
structure ItemRecord where
  what : Named
  path : Name
  level : LevelInEffect
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

/-! ## Simpler `Bool` expressions -/

/-! The rules, and the proof that they keep the meaning, are in
`FrenCore.Simplify`; this builds the text of the simpler form. -/

/-- The associativity of an operator (`lang::Assoc`). -/
inductive Assoc where
  | left
  | right
  | nonAssoc
  deriving Inhabited, BEq, Repr

/-- Whether an operand can be written without parentheses
(`lang::operand`). -/
def bareOperand (outer inner : Nat) (assoc : Assoc) (right : Bool) : Bool :=
  if inner > outer then true
  else if inner < outer then false
  else match assoc with
    | .left => !right
    | .right => right
    | .nonAssoc => false

/-- The shape of an expression, as `nonminimal_bool` sees it. `when` and
`unless` are `when`. -/
inductive BKind where
  | lit (b : Bool)
  | not
  | bin (op : String)
  | when
  | ite
  | neg
  | atom
  deriving Inhabited, BEq, Repr

/-- The precedence of an expression's outermost operator, as
`lang::operand` uses it. A conditional counts as binding most loosely,
since its `else` extends as far right as possible. -/
def BKind.prec : BKind → Nat
  | .when | .ite => 0
  | .bin "iff" => 1
  | .bin "or" => 2
  | .bin "and" => 3
  | .not => 4
  | .bin "+" | .bin "-" => 6
  | .bin "*" => 7
  | .bin _ => 5
  | .neg => 8
  | .lit _ | .atom => 9

def BKind.assoc : BKind → Assoc
  | .bin "or" | .bin "and" | .bin "+" | .bin "-" | .bin "*" => .left
  | .not | .neg | .when => .right
  | _ => .nonAssoc

/-- An expression: its shape, where it is written in the text given to
`simplerBools` (without parentheses around it), and its operands. -/
inductive BNode (α : Type) where
  | mk (kind : BKind) (range : Range) (ref : α) (kids : Array (BNode α))
  deriving Inhabited

/-- Where an operand is: the precedence and associativity of its
operator, and whether it is on the right; `none` where any expression can
be written, as for a branch of `if`. -/
structure Slot where
  outer : Nat
  assoc : Assoc
  right : Bool
  deriving Inhabited

def BKind.slots : BKind → Array (Option Slot)
  | .when => #[some ⟨0, .nonAssoc, false⟩, some ⟨0, .right, true⟩]
  | .ite => #[none, none, none]
  | .not => #[some ⟨4, .right, true⟩]
  | .neg => #[some ⟨8, .right, true⟩]
  | k@(.bin _) => #[some ⟨k.prec, k.assoc, false⟩, some ⟨k.prec, k.assoc, true⟩]
  | _ => #[]

/-- An expression, simplified: its text and precedence. -/
structure BText where
  text : String
  prec : Nat
  deriving Inhabited

/-- `t` in `slot`, in parentheses if it needs them there. -/
def BText.inSlot (t : BText) (slot : Option Slot) : String :=
  match slot with
  | some s => if bareOperand s.outer t.prec s.assoc s.right then t.text else s!"({t.text})"
  | none => t.text

/-- A report of `nonminimal_bool`: where, a label, and the simpler form. -/
structure BoolReport (α : Type) where
  ref : α
  range : Range
  label : String
  replacement : String
  deriving Inhabited

/-- `n` as an `Ex`, as deep as `Ex.simplerForm` looks: its operands and
theirs. Below that, and for what it does not look inside, an atom. -/
def BNode.toEx : Nat → BNode α → Ex
  | 0, _ => .atom 0
  | d + 1, .mk kind _ _ kids =>
    let k (i : Nat) := (kids[i]?.map (BNode.toEx d)).getD (.atom 0)
    match kind with
    | .lit b => .lit b
    | .not => .not (k 0)
    | .neg => .neg (k 0)
    | .bin op => match BinOp.ofOp? op with
      | some o => .bin o (k 0) (k 1)
      | none => .atom 0
    | .when => .when false (k 0) (k 1)
    | .ite => .ite (k 0) (k 1) (k 2)
    | .atom => .atom 0

/-- The text of a simpler form, from the simplified texts of the operands
and of theirs, as `Shape.build` builds the expression. -/
def Shape.text (rs : Array (BText × Array BText)) (s : Shape) : BText :=
  let get : Pick → BText
    | .kid i => (rs[i]?.map (·.1)).getD default
    | .grandkid i j => ((rs[i]?.map (·.2)).getD #[])[j]?.getD default
  let slot (outer : Nat) (assoc : Assoc) (right : Bool) : Option Slot := some ⟨outer, assoc, right⟩
  match s with
  | .same p => get p
  | .not p => { text := s!"not {(get p).inSlot (slot 4 .right true)}", prec := 4 }
  | .cmp c a b =>
    { text := s!"{(get a).inSlot (slot 5 .nonAssoc false)} {c.op} {(get b).inSlot (slot 5 .nonAssoc true)}", prec := 5 }

/-- Whether `r` is directly in parentheses within `outer`. -/
def enclosed (src : Array Char) (outer r : Range) : Bool := Id.run do
  let mut i := r.start
  while i > outer.start && src[i - 1]!.isWhitespace do i := i - 1
  let mut j := r.stop
  while j < outer.stop && src[j]!.isWhitespace do j := j + 1
  return i > outer.start && src[i - 1]! == '(' && j < outer.stop && src[j]! == ')'

def textOf (src : Array Char) (r : Range) : String := String.ofList (src.extract r.start r.stop).toList

/-- The simplified text of `n`, which is in `slot` within `parent`, and of
its operands, with the reports of `nonminimal_bool` in it, in order. -/
partial def simplifyNode (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) :
    StateM (Array (BoolReport α)) (BText × Array BText) := do
  let .mk kind range ref kids := n
  let mut results := #[]
  for k in kids, s in kind.slots do
    results := results.push (← simplifyNode src k s range)
  let kidRange (k : BNode α) : Range := match k with | .mk _ kr .. => kr
  -- The node as written, with its operands' simplified texts.
  let mut text := ""
  let mut pos := range.start
  let mut changed := false
  for k in kids, (t, _) in results, s in kind.slots do
    let kr := kidRange k
    let written := textOf src kr
    let t' := if t.text == written || enclosed src range kr then t.text else t.inSlot s
    if t' != written then changed := true
    text := text ++ textOf src { start := pos, stop := kr.start } ++ t'
    pos := kr.stop
  text := if changed then text ++ textOf src { start := pos, stop := range.stop } else textOf src range
  let own : BText := { text, prec := kind.prec }
  let kidTexts := results.map (·.1)
  -- Decided by the rules, from what `n` is as written, as `Ex.simp` does.
  match (n.toEx 3).simplerForm with
  | some (label, s) =>
    let t := s.text results
    let replacement := if enclosed src parent range then t.text else t.inSlot slot
    modify (·.push { ref, range, label, replacement })
    return (t, kidTexts)
  | none => return (own, kidTexts)

/-- The reports of `nonminimal_bool` in an expression written in `src`,
in the order they start, the outer of two that start together first: for
each, the simpler form, which replaces the expression's range. -/
def simplerBools (src : Array Char) (root : BNode α) : Array (BoolReport α) :=
  let range := match root with | .mk _ r .. => r
  let ((), out) := (do discard (simplifyNode src root none range) : StateM _ Unit).run #[]
  out.qsort fun a b => a.range.start < b.range.start || (a.range.start == b.range.start && a.range.stop > b.range.stop)

def nonminimalMsg (r : BoolReport α) (fixable : Bool := false) : Msg :=
  { code? := some Lint.nonminimalBool.code, headline := "this `Bool` expression can be simpler"
    label? := some r.label
    notes := if fixable then #[fixHelp] else #[]
    fixes := #[{ msg := s!"write `{r.replacement}`", replacement := r.replacement }] }

/-! ## Expectations -/

/-- A `set_option` to `expect`, with the level of
`unfulfilled_lint_expectations` there. -/
structure ExpectationRecord where
  lint : Lint
  level : LevelInEffect
  deriving Inhabited, Repr

/-- Whether an expectation is fulfilled (`lint::expectation`). -/
def expectationFulfilled (nFired : Nat) : Bool := nFired > 0

/-- Whether an unfulfilled expectation is reported (`lint::expectation`). -/
def expectationReported (nFired : Nat) (level : LintLevel) : Bool :=
  !expectationFulfilled nFired && level != .allow && level != .expect

def unfulfilledMsg (l : Lint) (fixable : Bool := false) : Msg :=
  { code? := some Lint.unfulfilledExpectations.code, headline := "this lint expectation is unfulfilled"
    label? := some s!"`{l.name}` never fires where this is in effect"
    notes := #[s!"note: `set_option {l.optionString} \"expect\"` expects `{l.name}` to fire where it is in effect",
      "help: remove this `set_option`"] ++ (if fixable then #[fixHelp] else #[]) }

/-- The messages for the expectations that nothing fulfilled, given the
indices of those fulfilled. -/
def expectationReports (exps : Array (ExpectationRecord × α)) (fulfilled : Array Nat) (fixable : Bool := false) :
    Array (LintReport α) :=
  (exps.mapIdx fun i (e, ref) => (i, e, ref)).filterMap fun (i, e, ref) =>
    if expectationReported (fulfilled.count i) e.level.effective then
      some { lint := .unfulfilledExpectations, level := e.level, ref, msg := unfulfilledMsg e.lint fixable }
    else none

end Fren.Core
