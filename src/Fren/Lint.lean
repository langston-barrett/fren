-- keep-sorted start
import Fren.Model
import FrenCore.Lint
-- keep-sorted end

/-!
# Lints in Lean

The Lean side of `FrenCore.Lint` (`Reqs/Lint`). A lint's level is the Lean
option `fren.lint.NAME`, and a group's `fren.lint.GROUP`. `set_option` for
these options is elaborated here, before Lean's own elaborator: it rejects
levels that do not exist and changes to a forbidden lint, sets each lint of
a group, and gives each `"expect"` its expectation, as the hidden option
`fren.lint.NAME.expectation`. Since `set_option ... in`
is a `section`, both end with it.

Elaborators record what the lints need in the file's `LocalState`, and
`reportLints` reports them at the end of the file, or of a Markdown spec
(`Fren.Literate`).
-/

open Lean Elab Command

namespace Fren

register_option fren.lint.unused_imports : String := {
  defValue := "warn"
  descr := "the level of the lint `unused_imports`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.glob_imports : String := {
  defValue := "warn"
  descr := "the level of the lint `glob_imports`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.non_snake_case : String := {
  defValue := "warn"
  descr := "the level of the lint `non_snake_case`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.non_camel_case_types : String := {
  defValue := "warn"
  descr := "the level of the lint `non_camel_case_types`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.non_upper_case_constants : String := {
  defValue := "warn"
  descr := "the level of the lint `non_upper_case_constants`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.unfulfilled_lint_expectations : String := {
  defValue := "warn"
  descr := "the level of the lint `unfulfilled_lint_expectations`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.unused_variables : String := {
  defValue := "warn"
  descr := "the level of the lint `unused_variables`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.dead_code : String := {
  defValue := "warn"
  descr := "the level of the lint `dead_code`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.nonminimal_bool : String := {
  defValue := "warn"
  descr := "the level of the lint `nonminimal_bool`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.undecidable : String := {
  defValue := "deny"
  descr := "the level of the lint `undecidable`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.length_zero : String := {
  defValue := "warn"
  descr := "the level of the lint `length_zero`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.card_zero : String := {
  defValue := "warn"
  descr := "the level of the lint `card_zero`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.singleton_membership : String := {
  defValue := "warn"
  descr := "the level of the lint `singleton_membership`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.membership_chain : String := {
  defValue := "allow"
  descr := "the level of the lint `membership_chain`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.constant_output : String := {
  defValue := "warn"
  descr := "the level of the lint `constant_output`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.definable_output : String := {
  defValue := "allow"
  descr := "the level of the lint `definable_output`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.index_after_use : String := {
  defValue := "warn"
  descr := "the level of the lint `index_after_use`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.unless_not : String := {
  defValue := "warn"
  descr := "the level of the lint `unless_not`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.collapsible_when : String := {
  defValue := "warn"
  descr := "the level of the lint `collapsible_when`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.if_not_else : String := {
  defValue := "allow"
  descr := "the level of the lint `if_not_else`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.match_same_arms : String := {
  defValue := "allow"
  descr := "the level of the lint `match_same_arms`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.match_like_membership : String := {
  defValue := "warn"
  descr := "the level of the lint `match_like_membership`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.wildcard_single_variant : String := {
  defValue := "allow"
  descr := "the level of the lint `wildcard_single_variant`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.if_chain_match : String := {
  defValue := "allow"
  descr := "the level of the lint `if_chain_match`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.case_split_reqs : String := {
  defValue := "allow"
  descr := "the level of the lint `case_split_reqs`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.redundant_bindings : String := {
  defValue := "warn"
  descr := "the level of the lint `redundant_bindings`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.eq_op : String := {
  defValue := "warn"
  descr := "the level of the lint `eq_op`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.same_branches : String := {
  defValue := "warn"
  descr := "the level of the lint `same_branches`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.duplicate_elements : String := {
  defValue := "warn"
  descr := "the level of the lint `duplicate_elements`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.empty_argument : String := {
  defValue := "warn"
  descr := "the level of the lint `empty_argument`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.double_comparison : String := {
  defValue := "warn"
  descr := "the level of the lint `double_comparison`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.bool_equality : String := {
  defValue := "allow"
  descr := "the level of the lint `bool_equality`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.manual_method : String := {
  defValue := "warn"
  descr := "the level of the lint `manual_method`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.else_extends : String := {
  defValue := "warn"
  descr := "the level of the lint `else_extends`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.identity_op : String := {
  defValue := "warn"
  descr := "the level of the lint `identity_op`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.double_parens : String := {
  defValue := "warn"
  descr := "the level of the lint `double_parens`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.double_neg : String := {
  defValue := "warn"
  descr := "the level of the lint `double_neg`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.int_plus_one : String := {
  defValue := "warn"
  descr := "the level of the lint `int_plus_one`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.neg_multiply : String := {
  defValue := "warn"
  descr := "the level of the lint `neg_multiply`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.redundant_method_chain : String := {
  defValue := "warn"
  descr := "the level of the lint `redundant_method_chain`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.trivial_pattern : String := {
  defValue := "warn"
  descr := "the level of the lint `trivial_pattern`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.redundant_bool_type : String := {
  defValue := "warn"
  descr := "the level of the lint `redundant_bool_type`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.trivial_match : String := {
  defValue := "warn"
  descr := "the level of the lint `trivial_match`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.zero_sized_map_values : String := {
  defValue := "allow"
  descr := "the level of the lint `zero_sized_map_values`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.many_single_char_names : String := {
  defValue := "allow"
  descr := "the level of the lint `many_single_char_names`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.similar_names : String := {
  defValue := "allow"
  descr := "the level of the lint `similar_names`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.too_many_lines : String := {
  defValue := "allow"
  descr := "the level of the lint `too_many_lines`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.unused : String := {
  defValue := "warn"
  descr := "the level of each lint of the group `unused`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.nonstandard_style : String := {
  defValue := "warn"
  descr := "the level of each lint of the group `nonstandard_style`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.style : String := {
  defValue := "warn"
  descr := "the level of each lint of the group `style`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.complexity : String := {
  defValue := "warn"
  descr := "the level of each lint of the group `complexity`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.suspicious : String := {
  defValue := "warn"
  descr := "the level of each lint of the group `suspicious`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.pedantic : String := {
  defValue := "allow"
  descr := "the level of each lint of the group `pedantic`: allow, expect, warn, deny or forbid"
}

register_option fren.lint.decidability : String := {
  defValue := "deny"
  descr := "the level of each lint of the group `decidability`: allow, expect, warn, deny or forbid"
}

/-- The hidden option holding the expectation of a lint at `expect`. -/
def expectationOption (l : Core.Lint) : Name := l.option ++ `expectation

/-- The hidden option marking a lint's level as set by its group's
`set_option` in the file. -/
def viaGroupOption (l : Core.Lint) : Name := l.option ++ `via_group

def levelOption? (opts : Options) (n : Name) : Option Core.LintLevel :=
  match opts.find? n with
  | some (.ofString s) => Core.LintLevel.ofName? s
  | _ => none

/-- A lint's level here, from the options. In the file, a group's
`set_option` sets each of its lints' options, in order with theirs; outside
it, the lint's own option wins over its group's (`lint::outside_options`). -/
def lintLevel [Monad m] [MonadOptions m] (l : Core.Lint) : m Core.LevelInEffect := do
  let opts ← getOptions
  let own? := levelOption? opts l.option
  let group? := levelOption? opts l.group.option
  if own?.isNone && group?.isNone then return .ofDefault l
  let level := Core.outsideLevel l.default own? group?
  let expectation? := match opts.find? (expectationOption l) with
    | some (.ofNat n) => some n
    | _ => none
  let viaGroup := own?.isNone || opts.getBool (viaGroupOption l)
  return { level, isSet := true, group? := if viaGroup then some l.group else none, expectation? }

variable {m : Type → Type} [Monad m] [MonadEnv m] [MonadOptions m]

/-- Records that a path's first segment resolved through an import. -/
def recordUsed (u : Core.UsedName) : m Unit :=
  modifyLocal fun l => { l with used := l.used.push u }

/-- Records a `use` declared in this file, with the levels here. -/
def recordUse (u : Core.UseDef) (ref : Syntax) : m Unit := do
  let r : Core.UseRecord := {
    module := u.scope, target := u.target, glob := u.glob
    unusedLevel := ← lintLevel .unusedImports, globLevel := ← lintLevel .globImports }
  modifyLocal fun l => { l with useRecords := l.useRecords.push (r, ref) }

/-- Records a lint's message at `ref`, at the level here. -/
def recordLint (lint : Core.Lint) (ref : Syntax) (msg : Core.Msg) : m Unit := do
  let level ← lintLevel lint
  modifyLocal fun l => { l with lintReports := l.lintReports.push { lint, level, ref, msg } }

/-- Records the item that a resolved path uses (`dead_code`). -/
def recordUsedItem (r : Core.Resolved) : m Unit :=
  modifyLocal fun l => { l with usedItems := l.usedItems.push r.usedItem }

/-- Records a private enumeration or constant declared here, with the level
of `dead_code` here. -/
def recordItem (what : Core.Named) (path : Name) (ref : Syntax) : m Unit := do
  let r : Core.ItemRecord := { what, path, level := ← lintLevel .deadCode }
  modifyLocal fun l => { l with items := l.items.push (r, ref) }

/-- Records the naming lint for a declared name that is not in its case
(`lint::naming_case`), at the level here. -/
def lintName (what : Core.Named) (n : Name) (ref : Syntax) : m Unit := do
  if let some (lint, msg) := Core.namingMsg? what n then
    let level ← lintLevel lint
    modifyLocal fun l => { l with lintReports := l.lintReports.push { lint, level, ref, msg } }
  if what matches .variable | .instance | .binder then
    modifyLocal fun l => { l with declaredNames := l.declaredNames.push (n, ref) }

/-- Starts an item whose declared names `lintDeclared` checks. -/
def startDeclared : m Unit := modifyLocal fun l => { l with declaredNames := #[] }

/-- Records `many_single_char_names` and `similar_names` on the names that
the `what` named `n`, at `ref`, declares (`lint::many_single_char_names`,
`lint::similar_names`): each once, in source order. -/
def lintDeclared (what : Core.Named) (n : Name) (ref : Syntax) : m Unit := do
  let pos (r : Syntax) := (r.getPos?.map (·.byteIdx)).getD 0
  let ds := (← getLocal).declaredNames.foldl (init := #[]) fun acc d =>
    if acc.any fun e => e.1 == d.1 && pos e.2 == pos d.2 then acc else acc.push d
  let ds := ds.qsort fun a b => pos a.2 < pos b.2
  modifyLocal fun l => { l with declaredNames := #[] }
  let single := ds.filter (Core.singleChar ·.1)
  if Core.manySingleCharNames single.size then
    recordLint .manySingleCharNames ref (Core.manySingleCharNamesMsg what n (single.map (·.1)))
  for i in [0:ds.size] do
    if let some a := (ds.extract 0 i).find? (Core.namesSimilar ·.1 ds[i]!.1) then
      recordLint .similarNames ds[i]!.2 (Core.similarNamesMsg a.1 ds[i]!.1 what n)

/-- Reports the lints of the file, or Markdown spec, just elaborated, and
forgets them. -/
def reportLints : CommandElabM Unit := do
  let l ← getLocal
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := l.inMarkdown
  let (reports, fulfilled) := Core.finishReports
    (l.lintReports ++ Core.importReports l.useRecords l.used fixable ++ Core.deadCodeReports l.items l.usedItems)
  let (unfulfilled, _) := Core.finishReports (Core.expectationReports l.expectations fulfilled fixable)
  for (r, sev) in reports ++ unfulfilled do
    match sev with
    | .error => logErrorAt r.ref r.msg.text
    | .warning => logWarningAt r.ref r.msg.text
    | .info => logInfoAt r.ref r.msg.text
  modifyLocal fun l => { l with useRecords := #[], used := #[], expectations := #[], lintReports := #[],
                                items := #[], usedItems := #[] }

/-- `set_option fren.lint.NAME "LEVEL"`, for a lint (`lint::setting`) or a
group (`lint::group_setting`), which sets each of its lints. Other options,
and lints that do not exist, are left to Lean. -/
@[command_elab Lean.Parser.Command.set_option] def elabLintOption : CommandElab := fun stx => do
  let name := stx[1].getId.eraseMacroScopes
  let some target := (Core.Lint.all.map Core.LintTarget.lint ++ Core.Group.all.map Core.LintTarget.group).find?
    (·.option == name) | throwUnsupportedSyntax
  let some v := stx[3].isStrLit? | throwUnsupportedSyntax
  let some requested := Core.LintLevel.ofName? v | throwErrorAt stx[3] (Core.invalidLevelMsg v).text
  let levels ← target.members.mapM fun l => return (l, (← lintLevel l).level)
  let levelOf (l : Core.Lint) := ((levels.find? (·.1 == l)).map (·.2)).getD l.default
  if let some lint := target.rejectedBy? levelOf requested then
    throwErrorAt stx (Core.forbiddenMsg target lint requested).text
  let (opts, _) ← Elab.elabSetOption stx[1] stx[3]
  let expectation? ← if requested == .expect then do
      let e : Core.ExpectationRecord := { target, level := ← lintLevel .unfulfilledExpectations }
      let n := (← getLocal).expectations.size
      modifyLocal fun l => { l with expectations := l.expectations.push (e, stx) }
      pure (some n)
    else pure none
  let opts := target.members.foldl (init := opts) fun opts lint =>
    let opts := opts.insert lint.option (.ofString v)
    let opts := match expectation? with
      | some n => opts.insert (expectationOption lint) (.ofNat n)
      | none => opts.erase (expectationOption lint)
    if target matches .group _ then opts.insert (viaGroupOption lint) (.ofBool true) else opts.erase (viaGroupOption lint)
  modifyScope fun scope => { scope with opts }

/-- Reports the file's lints at its end. -/
def lintsAtEnd : ModuleLinter where
  run _ := do
    unless (← getLocal).inMarkdown do reportLints

initialize addModuleLinter lintsAtEnd

end Fren
