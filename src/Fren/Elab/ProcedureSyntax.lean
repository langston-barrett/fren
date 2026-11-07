-- keep-sorted start
import Fren.Elab.Blocks
import Fren.Elab.Evidence
-- keep-sorted end

/-! # Hosted elaboration: procedure syntax -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang

/-- The results of the procedure `stx`: `fren_result`s. -/
def procResults (stx : Syntax) : Array Syntax := if stx[6].isNone then #[] else stx[6][2].getSepArgs

/-- The static errors of the syntax of the procedure `stx` that the `fren`
command's parser reports, the first of them by `Core.firstBlockError?`
(`lang::block_errors`). Its parts, in source order: its signature; and each
member, an evidence setting before it as a part of its own, with its own
syntax, how it is written (`clauseSyntaxAt`: a clause without a label that
is not a Boolean block), and an `out` whose name is not one of its results
(`F0444`). -/
def procBlockErrors (stx : Syntax) : CommandElabM (Option (CommandElabM Unit)) := do
  let mut parts : List (List (Core.BlockCheck × CommandElabM Unit)) := []
  let header ← caughtError (for i in [0:8] do checkParsed stx[i])
  parts := parts ++ [(header.map (.syntax, ·)).toList]
  let results := (procResults stx).map fun r => (declaredIdent r[2]).1.getId
  for m0 in stx[8].getArgs do
    let mut m := m0
    while m.isOfKind ``Lang.evidenceMember do
      parts := parts ++ [settingErrors m none]
      m := m[4]
    let own ← caughtError (checkParsed m)
    let rejected? : Option (CommandElabM Unit) :=
      if m.isOfKind ``Lang.defineMember && !results.contains m[1].getId then
        some (throwErrorAt (mkNullNode #[m[0], m[1]]) (Core.procOutMsg (Core.nameText m[1].getId)).text)
      else none
    parts := parts ++ [(own.map (.syntax, ·)).toList ++ clauseSyntaxAt m own.isNone ++ (rejected?.map (.rejected, ·)).toList]
  let tail ← caughtError (for i in [9:stx.getNumArgs] do checkParsed stx[i])
  parts := parts ++ [(tail.map (.syntax, ·)).toList]
  return Core.firstBlockError? parts

/-- The procedure `stx`'s first static error, if any (`procBlockErrors`,
`reportItem`). -/
def checkProcMembers (stx : Syntax) : CommandElabM Unit := do reportItem (← procBlockErrors stx) stx

/-- The static errors of the syntax of the global expectation `stx`, the
first of them by `Core.firstBlockError?` (`lang::block_errors`). Its parts:
its signature, then each member, an evidence setting before it as a part
of its own, with its own syntax and how it is written (`clauseSyntaxAt`: a
clause without a label that is not a Boolean block). -/
def globalBlockErrors (stx : Syntax) : CommandElabM (Option (CommandElabM Unit)) := do
  let mut parts : List (List (Core.BlockCheck × CommandElabM Unit)) := []
  let header ← caughtError (for i in [0:7] do checkParsed stx[i] (global := true))
  parts := parts ++ [(header.map (.syntax, ·)).toList]
  for m0 in stx[7].getArgs do
    let mut m := m0
    while m.isOfKind ``Lang.evidenceMember do
      parts := parts ++ [settingErrors m none]
      m := m[4]
    let own ← caughtError (checkParsed m (global := true))
    parts := parts ++ [(own.map (.syntax, ·)).toList ++ clauseSyntaxAt m own.isNone]
  let tail ← caughtError (for i in [8:stx.getNumArgs] do checkParsed stx[i] (global := true))
  parts := parts ++ [(tail.map (.syntax, ·)).toList]
  return Core.firstBlockError? parts

/-- The global expectation `stx`'s first static error, if any
(`globalBlockErrors`, `reportItem`). -/
def checkGlobalBlockParsed (stx : Syntax) : CommandElabM Unit := do reportItem (← globalBlockErrors stx) stx

/-- The members of the procedure `stx` as a component's, as the `fren`
command reads them: its parameters as inputs, its results as public
outputs, each defined by the `out` member of its block that defines it, at
most one (`F0421`), and its block's `exists` and `let` members as private
outputs. Each keeps its evidence setting. -/
def procMembers (stx : Syntax) : CommandElabM (Array Syntax) := do
  let results := procResults stx
  let resultNames := results.map fun r => (declaredIdent r[2]).1.getId
  let mut defs : Array (Name × Syntax) := #[]
  let mut body := #[]
  for m0 in stx[8].getArgs do
    let (m, set?) ← unwrapEvidence m0
    let rewrap (inner : Syntax) : Syntax := match set? with
      | some (_, ev) => ev.setArg 4 inner
      | none => inner
    if let some split ← splitBooleanMember m then
      body := body ++ split.map rewrap
    else if m.isOfKind ``Lang.defineMember && resultNames.contains m[1].getId then
      if defs.any (·.1 == m[1].getId) then throwErrorAt m[1] (Core.resultDefinedTwiceMsg (Core.nameText m[1].getId)).text
      defs := defs.push (m[1].getId, mkNullNode #[m[2], m[3], m[4]])
    else if m.isOfKind ``Lang.existsMember then
      body := body.push (rewrap (mkNode ``Lang.outMember #[mkNullNode, m[0], mkAtom "out", m[2], m[3], mkNullNode]))
    else if m.isOfKind ``Lang.letMember then
      body := body.push (rewrap (mkNode ``Lang.outMember
        #[mkNullNode, m[0], mkAtom "out", m[2], m[3], mkNullNode #[m[4], m[5], m[6]]]))
    else body := body.push m0
  let params := stx[4].getSepArgs.map fun p => mkNode ``Lang.inMember #[mkAtom "in", p[1], p[2], mkNullNode]
  let outs := results.map fun r =>
    let defn := ((defs.find? (·.1 == (declaredIdent r[2]).1.getId)).map (·.2)).getD mkNullNode
    let out : Syntax := mkNode ``Lang.outMember #[mkNullNode #[mkAtom "pub"], r[1], mkAtom "out", r[2], r[3], defn]
    if r[0].isNone then out else
      let e := r[0][0]
      (mkNode ``Lang.evidenceMember #[e[0], e[1], e[2], e[3], out] : Syntax)
  return params ++ outs ++ body

/-- The results and members of the procedure `stx`, or of a global
expectation aligned as one, as `lang::block_member` reads them, each with
whether it is written with `det` and where it is reported. -/
def blockMembers (stx : Syntax) : CommandElabM (Array (Syntax × Core.BlockMember × Bool)) := do
  let results := (procResults stx).map fun r => (r[2], Core.BlockMember.result, !r[1].isNone)
  let others ← stx[8].getArgs.mapM fun m0 => do
    let (m, _) ← unwrapEvidence m0
    -- Each kind by name, the unlabelled Boolean blocks among them, so
    -- that a member kind added later is an error here rather than read as
    -- one the block accepts.
    let kind? : Option (Core.BlockMember × Bool) :=
      if m.isOfKind ``Lang.existsMember then some (.exists, !m[0].isNone)
      else if m.isOfKind ``Lang.letMember then some (.let, !m[0].isNone)
      else if m.isOfKind ``Lang.defineMember then some (.define, false)
      else if m.isOfKind ``Lang.assumeMember || m.isOfKind ``Lang.bareAssumeMember then some (.assume, false)
      -- Reported before, with a message of its own (`checkGlobalBlockParsed`),
      -- but named, so that it is no member of unknown kind.
      else if m.isOfKind ``Lang.requireMember || m.isOfKind ``Lang.bareRequireMember then some (.require, false)
      else if m.isOfKind ``Lang.ensureMember || m.isOfKind ``Lang.bareEnsureMember then some (.ensure, false)
      else if m.isOfKind ``Lang.expectMember || m.isOfKind ``Lang.bareExpectMember then some (.expect, false)
      else if m.isOfKind ``Lang.coverMember then some (.cover, false)
      else if m.isOfKind ``Lang.callMember then some (.call, false)
      else if m.isOfKind ``Lang.refinesMember then some (.refines, false)
      else if m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember then some (.use, false)
      else none
    let some (kind, det) := kind? | throwErrorAt m "internal error: a member of unknown kind `{m.getKind}`"
    return (m, kind, det)
  return results ++ others


end Fren
