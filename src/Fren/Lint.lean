-- keep-sorted start
import Fren.Model
import FrenCore.Lint
-- keep-sorted end

/-!
# Lints in Lean

The Lean side of `FrenCore.Lint` (`Reqs/Lint`). A lint's level is the Lean
option `fren.lint.NAME`. `set_option` for these options is elaborated here,
before Lean's own elaborator: it rejects levels that do not exist and
changes to a forbidden lint, and gives each `"expect"` its expectation, as
the hidden option `fren.lint.NAME.expectation`. Since `set_option ... in`
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

register_option fren.lint.shadowed_constants : String := {
  defValue := "warn"
  descr := "the level of the lint `shadowed_constants`: allow, expect, warn, deny or forbid"
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

/-- The hidden option holding the expectation of a lint at `expect`. -/
def expectationOption (l : Core.Lint) : Name := l.option ++ `expectation

/-- A lint's level here, from the options. -/
def lintLevel [Monad m] [MonadOptions m] (l : Core.Lint) : m Core.LevelInEffect := do
  let opts ← getOptions
  let some (.ofString s) := opts.find? l.option | return .ofDefault l
  let some level := Core.LintLevel.ofName? s | return .ofDefault l
  let expectation? := match opts.find? (expectationOption l) with
    | some (.ofNat n) => some n
    | _ => none
  return { level, isSet := true, expectation? }

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

/-- `set_option fren.lint.NAME "LEVEL"` (`lint::setting`). Other options,
and lints that do not exist, are left to Lean. -/
@[command_elab Lean.Parser.Command.set_option] def elabLintOption : CommandElab := fun stx => do
  let name := stx[1].getId.eraseMacroScopes
  let some lint := Core.Lint.all.find? (·.option == name) | throwUnsupportedSyntax
  let some v := stx[3].isStrLit? | throwUnsupportedSyntax
  let some requested := Core.LintLevel.ofName? v | throwErrorAt stx[3] (Core.invalidLevelMsg v).text
  let (ok, _) := Core.setLevel (← lintLevel lint).level requested
  unless ok do throwErrorAt stx (Core.forbiddenMsg lint requested).text
  let (opts, _) ← Elab.elabSetOption stx[1] stx[3]
  let opts ← if requested == .expect then do
      let e : Core.ExpectationRecord := { lint, level := ← lintLevel .unfulfilledExpectations }
      let n := (← getLocal).expectations.size
      modifyLocal fun l => { l with expectations := l.expectations.push (e, stx) }
      pure (opts.insert (expectationOption lint) (.ofNat n))
    else pure (opts.erase (expectationOption lint))
  modifyScope fun scope => { scope with opts }

/-- Reports the file's lints at its end. -/
def lintsAtEnd : ModuleLinter where
  run _ := do
    unless (← getLocal).inMarkdown do reportLints

initialize addModuleLinter lintsAtEnd

end Fren
