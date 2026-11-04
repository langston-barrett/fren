-- keep-sorted start
import FrenCore.Lint.Model
import FrenCore.Names
-- keep-sorted end

/-!
# Import lints and source edits

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Imports -/

/-- A `use` declared in the file being elaborated. -/
structure UseRecord where
  /-- Its scope: the module, or the path of the procedure containing it. -/
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
of that import: a procedure's imports shadow its module's scope. -/
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
(`Reqs/Lint/Unused#unused-imports`). A local of `locals` that it hides instead
hides the import too, so the import is not needed. -/
def Table.shadowedImport? (t : Table) (scope : Name) (locals : Locals) (n : Name) (bang : Bool) :
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

end Fren.Core
