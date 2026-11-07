-- keep-sorted start
import Fren.Elab.Declarations
-- keep-sorted end

/-! # Hosted elaboration: member lints -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- The conjuncts of `e`, a constraint: the operands of its `and`s, not
through parentheses but its own, as the `fren` command sees them
(`lint::manual_nat`). -/
partial def constraintConjuncts (e : Syntax) : Array Syntax :=
  let rec go (e : Syntax) : Array Syntax := if isBinOp e "and" then go e[0] ++ go e[2] else #[e]
  go (unparen e)

open Lang in
/-- Records `manual_nat` in the procedure `compPath` of `members`
(`lint::manual_nat`): for each variable it fires on, at its first bound,
reported at the end of the file (`reportLints`). -/
def lintManualNat (compPath : Name) (members : Array Syntax) : TermElabM Unit := do
  let vars := members.filterMap fun m =>
    if m.isOfKind ``Lang.inMember then some ((declaredIdent m[1]).1, (if m[2].isNone then none else some m[2][1]), true, false)
    else if m.isOfKind ``Lang.outMember then
      some ((declaredIdent m[3]).1, (if m[4].isNone then none else some m[4][1]), false, !m[5].isNone)
    else none
  let props := members.filterMap fun m => match m with
    | `(fren_member| assume $x:ident : $e) => some (true, x.raw, constraintConjuncts e)
    | `(fren_member| ensure $x:ident : $e) => some (false, x.raw, constraintConjuncts e)
    | `(fren_member| expect $x:ident : $e) => some (false, x.raw, #[])
    | `(fren_member| cover $x:ident : $e) => some (false, x.raw, #[])
    | _ => none
  let wf (e : Syntax) : String := Core.writtenForm (exactText (unparen e))
  let conjunct (assumption : Bool) (e : Syntax) : Core.NatConjunct :=
    let e := unparen e
    if e.getNumArgs == 3 && e[1].isAtom && Core.binaryOps.contains e[1].getAtomVal.trimAscii.toString then
      { assumption, op := .ofOp e[1].getAtomVal.trimAscii.toString, left := wf e[0], right := wf e[2] }
    else { assumption, op := .otherOp, left := "", right := "" }
  let isInt (ty? : Option Syntax) : Bool := ty?.any (exactText · == "Int")
  let bounds := Core.manualNatBounds
    (vars.map fun (x, ty?, isIn, defined) =>
      { name := Core.nameText x.getId, role := if isIn then .input else if defined then .definedOutput else .output
        int := isInt ty? })
    (props.map fun (assumption, _, cs) => cs.map (conjunct assumption))
  for (i, p, k) in bounds do
    let (x, _, isIn, _) := vars[i]!
    let (_, name, cs) := props[p]!
    let msg := Core.manualNatMsg (Core.nameText x.getId) isIn (Core.nameText name.getId) (exactText (unparen cs[k]!))
    let report := { lint := .manualNat, level := ← lintLevel .manualNat, ref := unparen cs[k]!
                    msg }
    modifyLocal fun l => { l with natReports := l.natReports.push (compPath, Core.nameText x.getId, report) }

open Lang in
/-- The name that a member declares, if any: a variable, a call or a
constraint, which share one namespace (`lang::distinct_names`). -/
def memberName? (m : Syntax) : Option Syntax :=
  if m.isOfKind ``Lang.inMember then some m[1]
  else if m.isOfKind ``Lang.outMember then some m[3]
  else if m.isOfKind ``Lang.defineMember then some m[1]
  else if m.isOfKind ``Lang.existsMember || m.isOfKind ``Lang.letMember then some m[2]
  else if m.isOfKind ``Lang.callMember then some m[1]
  else if let some (_, x, _) := constraint? m then some x
  else none

open Lang in
/-- The kind of a member without its evidence setting, for
`arbitrary_source_item_ordering`, by its syntax kind; `none` for what is
not one, which a procedure's members never are. -/
def memberKind? (m : Syntax) : Option Core.MemberKind :=
  [(``Lang.useMember, .use), (``Lang.useGroupMember, .use), (``Lang.existsMember, .exists), (``Lang.letMember, .let),
    (``Lang.defineMember, .define), (``Lang.assumeMember, .assumption), (``Lang.callMember, .call),
    (``Lang.ensureMember, .guarantee),
    (``Lang.expectMember, .expectation), (``Lang.coverMember, .cover)].lookup m.getKind

open Lang in
/-- The names that a defined output's definition, or a call's
bindings, mention: a binding `x` without `:= e` mentions `x`. -/
def memberMentions (m : Syntax) : Array Name :=
  if m.isOfKind ``Lang.defineMember then (pathMentions m[3]).map (·.getRoot)
  else if m.isOfKind ``Lang.letMember then (pathMentions m[5]).map (·.getRoot)
  else if m.isOfKind ``Lang.callMember then m[5].getSepArgs.foldl (init := #[]) fun acc a => acc ++ (pathMentions a).map (·.getRoot)
  else #[]

/-- Records `arbitrary_source_item_ordering` on the procedure `stx`, whose
members, with their evidence settings, are `raw`, and `members` without
them (`lint::arbitrary_source_item_ordering`); `global` if it is a global
expectation's. -/
def lintMemberOrder (stx open_ : Syntax) (raw members : Array Syntax) (global := false) : CommandElabM Unit := do
  let some kinds := members.mapM memberKind? | return
  let some i := Core.firstOutOfOrder? kinds | return
  let msg := Core.memberOrderMsg kinds[i]! kinds[i - 1]! global
  let some sub := stx.getSubstring? false false | return
  let off (p : Option String.Pos.Raw) := (String.Pos.Raw.extract sub.str sub.startPos (p.getD sub.startPos)).length
  let src := (String.Pos.Raw.extract sub.str sub.startPos sub.stopPos).toList.toArray
  let names := members.map fun m => (memberName? m).map fun x => (declaredIdent x).1.getId
  let mentions := members.map fun m => (memberMentions m).filterMap fun n => names.findIdx? (· == some n)
  let ranges := raw.map fun m => ({ start := off m.getPos?, stop := off m.getTailPos? } : Core.Range)
  let fix? := Core.memberOrderFix? src (off open_.getTailPos?) ranges kinds mentions
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown && fix?.isSome
  recordLint .arbitrarySourceItemOrdering raw[i]! (if fixable then msg.note Core.fixHelp else msg)


end Fren
