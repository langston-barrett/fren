-- keep-sorted start
import FrenCore.Lint.Imports
-- keep-sorted end

/-!
# Lint settings, messages and expectations

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Settings -/

/-- The note listing the lints, sorted by name. -/
def lintsNote : String :=
  s!"note: the lints are {", ".intercalate (((Lint.all.map (·.name)).qsort (· < ·)).map (s!"`{·}`")).toList}"

/-- The note for a lint that Fren had but removed, if `n` is one. -/
def removedLintNotes (n : String) : Array String :=
  if n == "shadowed_constants" then
    #["note: `shadowed_constants` was removed; shadowing without `!` is now an error (F0217)"]
  else #[]

/-- The note listing the groups of lints, sorted by name. -/
def groupsNote : String :=
  s!"note: the groups of lints are {", ".intercalate (((Group.all.map (·.name)).qsort (· < ·)).map (s!"`{·}`")).toList}"

/-- The names of the lints and of the groups, sorted, so that of several
names equally close to an unknown one, the suggestion is the first by name
(`Reqs/Lint#setting-levels`). -/
def lintTargetNames : Array String := (Lint.all.map (·.name) ++ Group.all.map (·.name)).qsort (· < ·)

/-- The message of the fix that replaces an unknown name with `s`, the
name of a lint or a group. -/
def similarLintMsg (s : String) : String :=
  s!"a {if (Group.ofName? s).isSome then "group" else "lint"} with a similar name exists: `{s}`"

/-- The lints that Fren renamed, by their old names: `set_option` rejects
an old name, with its new one as the fix. -/
def renamedLints : List (String × String) :=
  [("case_split_reqs", "case_split_guarantees")]

def unknownLintMsg (n : String) : Msg :=
  match renamedLints.lookup n with
  | some new =>
    { code? := some "F0707", headline := s!"unknown lint `{n}`", label? := some "no such lint"
      notes := #[s!"note: `{n}` was renamed to `{new}`"]
      fixes := #[{ msg := s!"use the new name: `{new}`", replacement := s!"fren.lint.{new}" }] }
  | none =>
    { code? := some "F0707", headline := s!"unknown lint `{n}`", label? := some "no such lint"
      notes := removedLintNotes n ++ #[lintsNote, groupsNote]
      fixes := (similarStr n lintTargetNames).toArray.map fun s =>
        { msg := similarLintMsg s, replacement := s!"fren.lint.{s}" } }

def invalidLevelMsg (v : String) : Msg :=
  { code? := some "F0708", headline := s!"invalid lint level `{v}`", label? := some "not a lint level"
    notes := #["note: a lint level is `\"allow\"`, `\"expect\"`, `\"warn\"`, `\"deny\"` or `\"forbid\"`"]
    fixes := (similarStr v (LintLevel.all.map (·.name))).toArray.map fun s =>
      { msg := s!"a level with a similar name exists: `\"{s}\"`", replacement := s!"\"{s}\"" } }

/-- A setting of `t` to `requested` where its lint `l` is forbidden. -/
def forbiddenMsg (t : LintTarget) (l : Lint) (requested : LintLevel) : Msg :=
  match t with
  | .lint _ =>
    { code? := some "F0709", headline := s!"`{requested.name}` for `{l.name}` is incompatible with an earlier `forbid`"
      label? := some s!"cannot change the level of `{l.name}`"
      notes := #["note: once a lint is `forbid`, its level cannot be changed"] }
  | .group g =>
    { code? := some "F0709"
      headline := s!"`{requested.name}` for `{g.name}` is incompatible with an earlier `forbid` of `{l.name}`"
      label? := some s!"cannot change the level of `{l.name}`, which is in `{g.name}`"
      notes := #["note: once a lint is `forbid`, its level cannot be changed, so neither can its group's"] }

/-! ## Expectations -/

/-- A `set_option` to `expect`, with the level of
`unfulfilled_lint_expectations` there. -/
structure ExpectationRecord where
  /-- The lint expected, or the group, any of whose lints fulfils it. -/
  target : LintTarget
  level : LevelInEffect
  deriving Inhabited, Repr

/-- Whether an expectation is fulfilled (`lint::expectation`). -/
def expectationFulfilled (nFired : Nat) : Bool := nFired > 0

/-- Whether an unfulfilled expectation is reported (`lint::expectation`). -/
def expectationReported (nFired : Nat) (level : LintLevel) : Bool :=
  !expectationFulfilled nFired && level != .allow && level != .expect

def unfulfilledMsg (t : LintTarget) (fixable : Bool := false) : Msg :=
  let what := match t with
    | .lint l => s!"`{l.name}`"
    | .group g => s!"no lint of `{g.name}`"
  let expects := match t with
    | .lint l => s!"`{l.name}` to fire"
    | .group g => s!"some lint of `{g.name}` to fire"
  { code? := some Lint.unfulfilledExpectations.code, headline := "this lint expectation is unfulfilled"
    label? := some s!"{what} {if t matches .lint _ then "never fires" else "fires"} where this is in effect"
    notes := #[s!"note: `set_option {t.optionString} \"expect\"` expects {expects} where it is in effect",
      "help: remove this `set_option`"] ++ (if fixable then #[fixHelp] else #[]) }

/-- The messages for the expectations that nothing fulfilled, given the
indices of those fulfilled. -/
def expectationReports (exps : Array (ExpectationRecord × α)) (fulfilled : Array Nat) (fixable : Bool := false) :
    Array (LintReport α) :=
  (exps.mapIdx fun i (e, ref) => (i, e, ref)).filterMap fun (i, e, ref) =>
    if expectationReported (fulfilled.count i) e.level.effective then
      some { lint := .unfulfilledExpectations, level := e.level, ref, msg := unfulfilledMsg e.target fixable }
    else none

/-! ## Lint settings -/

/-- A `set_option` of a lint or group in the file: what it sets, to what,
the level of `unused_lint_setting` at it, and the last setting that
replaced it for one of its lints, if any. -/
structure SettingRecord where
  target : LintTarget
  requested : LintLevel
  level : LevelInEffect
  replacedBy? : Option (LintTarget × LintLevel) := none
  deriving Inhabited, Repr

/-- The lints whose level a later `set_option` reads at the setting: its
messages are about the setting itself. -/
def settingLints : Array Lint := #[.unfulfilledExpectations, .unusedLintSetting]

/-- Whether `unused_lint_setting` fires on a setting, from whether it is in
effect at an item, for some lint it sets, and whether it is to `expect`
(`lint::unused_lint_setting`). -/
def unusedLintSetting (seen expect : Bool) : Bool := !seen && !expect

/-- A setting that is in effect at no item: the setting that replaced it,
if it is not in effect at the end of the file. -/
def unusedSettingMsg (target : LintTarget) (requested : LintLevel) (replacedBy? : Option (LintTarget × LintLevel))
    (fixable : Bool) : Msg :=
  let help := #["help: remove this `set_option`"] ++ (if fixable then #[fixHelp] else #[])
  match replacedBy? with
  | none =>
    { code? := some Lint.unusedLintSetting.code, headline := "this lint setting is in effect at no item"
      label? := some "no item follows it", notes := help }
  | some (t, v) =>
    let by_ := s!"`set_option {t.optionString} \"{v.name}\"`"
    let undoes := if requested == .deny && v != .deny && v != .forbid then
        #[s!"note: {by_} undoes this `deny`: `{target.name}` is not an error at the items that follow"]
      else #[]
    { code? := some Lint.unusedLintSetting.code, headline := "this lint setting is replaced before any item"
      label? := some "replaced before any item"
      notes := #[s!"note: {by_} replaces it before any item"] ++ undoes ++ help }

/-- The messages of `unused_lint_setting` for the file's settings, given the
indices of those in effect at an item, and of those in effect at the end
of the file. -/
def unusedSettingReports (settings : Array (SettingRecord × α)) (seen atEnd : Array Nat) (fixable : Bool := false) :
    Array (LintReport α) :=
  (settings.mapIdx fun i (r, ref) => (i, r, ref)).filterMap fun (i, r, ref) =>
    if unusedLintSetting (seen.contains i) (r.requested == .expect) then
      let replacedBy? := if atEnd.contains i then none else r.replacedBy?
      some { lint := .unusedLintSetting, level := r.level, ref
             msg := unusedSettingMsg r.target r.requested replacedBy? fixable }
    else none

/-- `settings` after the setting of `target` to `requested`, given the
levels before it: each setting that it replaces for one of its lints
records it. -/
def SettingRecord.replace (settings : Array (SettingRecord × α)) (before : Lint → LevelInEffect)
    (target : LintTarget) (requested : LintLevel) : Array (SettingRecord × α) :=
  target.members.foldl (init := settings) fun ss l =>
    match (before l).setting? with
    | some i => ss.modify i fun (r, ref) => ({ r with replacedBy? := some (target, requested) }, ref)
    | none => ss

end Fren.Core
