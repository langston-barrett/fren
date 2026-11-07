-- keep-sorted start
import Fren.Elab.Declarations
-- keep-sorted end

/-! # Hosted elaboration: evidence -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Whether the evidence `value`, written at `ref`, is testing
(`Reqs/Check#checking-by-testing`). -/
def evidenceTested (ref : Syntax) (value : String) : CommandElabM Core.Evidence := do
  let some b := Core.evidenceOf? value | throwErrorAt ref (Core.invalidEvidenceMsg value).text
  return b

/-- Whether the item-level or file-level `fren.evidence` in effect sets
checks to testing. An invalid value, reported once where it is set
(`elabEvidenceOption`), sets nothing. -/
def evidenceInEffect : CommandElabM Core.Evidence :=
  return (Core.evidenceOf? (fren.evidence.get (← getOptions))).getD {}

/-- The size bound of enumeration in effect (`fren.enumeration.size`). -/
def enumSizeInEffect : CommandElabM Nat := do
  let n := fren.enumeration.size.get (← getOptions)
  return if n > Core.Enumeration.maxSize then Core.Enumeration.defaultSize else n

/-- `set_option`, as Lean elaborates it, but for `fren.evidence`, an invalid
value is reported once, at the value, rather than at each item it would
set, and does not stop them, as in the `fren` command. -/
@[command_elab Lean.Parser.Command.set_option] def elabEvidenceOption : CommandElab := recordingErrors fun stx => do
  let opt := stx[1].getId.eraseMacroScopes
  unless opt == `fren.evidence || opt == `fren.enumeration.size do throwUnsupportedSyntax
  if let some v := stx[3].isStrLit? then
    if (Core.evidenceTested? v).isNone then logErrorAt stx[3] (Core.invalidEvidenceMsg v).text
  if let some n := stx[3].isNatLit? then
    if n > Core.Enumeration.maxSize then logErrorAt stx[3] (Core.Enumeration.sizeTooLargeMsg n).text
  elabSetOption stx

namespace InternalSyntax
/-- An internal command, which `set_option fren.evidence "v" in` before a
function or a constant expands into (`expandItemEvidence`): it reports
`F0215` at the setting, with what the item is and the value. It is
scoped, so source that does not open this namespace cannot write it. -/
scoped syntax (name := itemEvidenceCmd) "fren_item_evidence% " str str : command
end InternalSyntax

open InternalSyntax in
@[command_elab InternalSyntax.itemEvidenceCmd] def elabItemEvidence : CommandElab := fun stx => do
  let (some what, some value) := (stx[1].isStrLit?, stx[2].isStrLit?) | throwUnsupportedSyntax
  logError (Core.itemEvidenceMsg what value).text

open Lang in
/-- What `F0215` calls the item `stx`, after `set_option ... in`, if it is
a function or a constant, through further settings with `in`, and what its
checks are of: a body, a constant's value, or a contract. -/
partial def evidenceTarget? (stx : Syntax) : Option (String × Core.CheckedItem) :=
  if stx.isOfKind ``Lean.Parser.Command.in then evidenceTarget? stx[2]
  else if stx.isOfKind ``fnCmd then some ("a function", if stx[8].isNone then .contract else .body)
  else if stx.isOfKind ``fnBlockCmd then
    some ("a function", if stx[12].getArgs.any (·.isOfKind ``defineMember) then .body else .contract)
  else if stx.isOfKind ``constCmd then some ("a constant", .body)
  else none

open InternalSyntax in
/-- `set_option fren.evidence "v" in` before a function or a constant,
whose checks are the solver's (`Fren.Core.dispatchOf`): `F0215`, as in the
`fren` command, and the item is elaborated as though the value were
`"solver"`. -/
@[macro Lean.Parser.Command.in] def expandItemEvidence : Macro := fun stx => do
  let opt := stx[0]
  unless opt.isOfKind ``Lean.Parser.Command.set_option && opt[1].getId.eraseMacroScopes == `fren.evidence do
    Macro.throwUnsupported
  let some value := opt[3].isStrLit? | Macro.throwUnsupported
  let some ev := Core.evidenceOf? value | Macro.throwUnsupported
  let some (what, item) := evidenceTarget? stx[2] | Macro.throwUnsupported
  if ev.settable item then Macro.throwUnsupported
  let report ← withRef opt `(fren_item_evidence% $(quote what) $(quote value))
  `(section $report:command $(⟨stx[2]⟩):command end)

open Lang in
/-- A member without its `set_option fren.evidence ... in`, and the
setting, if it has one: the innermost, if there are several. -/
partial def unwrapEvidence (m : Syntax) : CommandElabM (Syntax × Option (Core.Evidence × Syntax)) := do
  unless m.isOfKind ``Lang.evidenceMember do return (m, none)
  -- Its option is `fren.evidence` (`checkParsed`).
  let b ← evidenceTested m[2] (m[2].isStrLit?.getD "")
  let (inner, set?) ← unwrapEvidence m[4]
  return (inner, set?.getD (b, m))

open Lang in
/-- The members of a procedure without their evidence settings, and the checks
that those and the procedure's setting `all` set to testing. -/
def testedOf (all : Core.Evidence) (raw : Array Syntax) : CommandElabM (Array Syntax × Core.Tested × Core.Tested) := do
  let reserved := raw.filterMap fun m0 => Id.run do
    let mut m := m0
    while m.isOfKind ``Lang.evidenceMember do m := m[4]
    return (constraint? m).map fun (_, x, _) => x.getId
  let mut refinesIndex := 0
  let mut members := #[]
  let mut expects := #[]
  let mut insts := #[]
  let mut dets := #[]
  let mut constraints := #[]
  for m0 in raw do
    let (m, set?) ← unwrapEvidence m0
    members := members.push m
    let b? := set?.map (·.1)
    let misplaced (what : String) : CommandElabM Unit := do
      if let some (_, ref) := set? then throwErrorAt ref (Core.misplacedEvidenceMsg what).text
    if let some (kind, x, _) := constraint? m then
      match kind with
      | .expect | .cover => expects := expects.push (x.getId, b?)
      | .assume => misplaced "an assumption"; constraints := constraints.push x.getId
      | .ensure => misplaced "a guarantee"; constraints := constraints.push x.getId
    -- By the names they declare, without the `!` of shadowing.
    else if m.isOfKind ``Lang.refinesMember then
      refinesIndex := refinesIndex + 1
      while reserved.contains (Name.mkSimple s!"refines_{refinesIndex}") do refinesIndex := refinesIndex + 1
      expects := expects.push (Name.mkSimple s!"refines_{refinesIndex}", b?)
    else if m.isOfKind ``Lang.callMember then insts := insts.push ((declaredIdent m[1]).1.getId, b?)
    else if m.isOfKind ``Lang.outMember then
      -- `[pub] [det] out x [: T] [:= e]`
      let y := (declaredIdent m[3]).1.getId
      if !m[1].isNone then dets := dets.push (y, b?)
      else misplaced "a variable that is not `det`"
      if !m[5].isNone then constraints := constraints.push y
    else misplaced (if m.isOfKind ``Lang.inMember then "a parameter" else "a `use`")
  let by_ (f : Core.Evidence → Bool) :=
    let pick (xs : Array (Name × Option Core.Evidence)) := xs.map fun (n, e?) => (n, e?.map f)
    Core.Tested.ofSettings (f all) constraints (pick expects) (pick insts) (pick dets)
  return (members, by_ (·.tested), by_ (·.enumerated))


end Fren
