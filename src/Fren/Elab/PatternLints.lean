-- keep-sorted start
import Fren.Elab.Construction
-- keep-sorted end

/-! # Hosted elaboration: pattern lints -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

mutual
/-- The pattern `p`, resolved as `q`, as written (`Core.PatNode`). -/
partial def patNode (p : Syntax) (q : Core.Pat) : Core.PatNode Syntax :=
  match q with
  | .ctor _ qs => .mk q (exactText p) p (((patternArgs p).zip qs).map fun (a, q) => orNode a[0].getSepArgs q)
  | _ => .mk q (exactText p) p #[]

/-- The or-pattern of the alternatives `alts`, resolved as `q`, where its
alternatives are, or its only pattern. -/
partial def orNode (alts : Array Syntax) (q : Core.Pat) : Core.PatNode Syntax :=
  match q with
  | .or qs =>
    let at_ := mkNullNode #[alts[0]!, alts.back!]
    .mk q (exactText at_) at_ ((alts.zip qs).map fun (a, q) => patNode a q)
  | _ => patNode alts[0]! q
end

/-- The lints of each or-pattern within the pattern `n`, of a `match` arm
or of `is` (`Reqs/Lint/Complexity/Patterns`): `wildcard_in_or_patterns`,
`manual_range_patterns` and `unnested_or_patterns`. -/
def lintOrPatterns (n : Core.PatNode Syntax) : TermElabM Unit := do
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable then m.note Core.fixHelp else m
  for o in n.orPatterns do
    let alts := o.kids
    if Core.wildcardInOr (alts.any (·.pat matches .wild false)) then
      recordLint .wildcardInOrPatterns o.at_ (help Core.wildcardInOrMsg)
    else if let some fixed := Core.manualRangeFix? (alts.map fun a => (a.pat, a.text)) then
      recordLint .manualRangePatterns o.at_ (help (Core.manualRangeMsg fixed))
    else
      for (i, j, fixed) in Core.unnestedRuns alts do
        recordLint .unnestedOrPatterns (mkNullNode #[alts[i]!.at_, alts[j]!.at_]) (help (Core.unnestedOrMsg fixed))

/-- The name that the binder `x` declares, without its `!`. -/
def binderName (x : Syntax) : String := Core.nameText (Core.declaredName x.getId).1

/-- `collapsible_match` on the arm `i` of the `match` whose arms are `arms`
and patterns `pats` (`lint::collapsible_match`): the arm's pattern is one
variant whose payload's patterns are `_` or binders, and its body a
`match` on one of those binders. -/
def lintCollapsible (cx : ExprCtx) (arms : Array Syntax) (pats : Array Core.Pat) (i : Nat) : TermElabM Unit := do
  let arm := arms[i]!
  let (alts, isOr) := topAlts arm[0]
  let #[p] := alts | return
  if isOr || !p.isOfKind ``Lang.variantPattern || p[1].isNone then return
  let .ctor _ qs := pats[i]! | return
  let body := unparen arm[3]
  unless body.isOfKind ``Lang.matchExpr do return
  let s := unparen body[1]
  let s := if s.getNumArgs == 1 then s[0] else s
  unless s.isOfKind ``Lang.fren_path && (pathSegs s).size == 1 do return
  let x := Core.nameText (pathSegs s)[0]!.getId
  let args := (patternArgs p).map (·[0].getSepArgs)
  let binderOf : Array Syntax × Core.Pat → Option String
    | (#[b], .wild true) => some (binderName (pathSegs b[0])[0]!)
    | _ => none
  let binders := (args.zip qs).filterMap binderOf
  let some k := (args.zip qs).findIdx? (binderOf · == some x) | return
  let flat := qs.all (· matches .wild _)
  let innerArms := body[3].getSepArgs
  -- An arm with a guard may not be taken where its pattern matches.
  if (arms.any (!·[1].isNone)) || innerArms.any (!·[1].isNone) then return
  let some d := innerArms.back? | return
  let innerWildcard := match topAlts d[0] with
    | (#[w], false) => w.isOfKind ``Lang.wildPattern
    | _ => false
  -- The first later arm that matches a value of the variant: one with `_`
  -- or a binder among its alternatives, since an arm that names the variant
  -- after this one is unreachable.
  let wild? := ((List.range arms.size).filter (· > i)).find? fun j => pats[j]!.top.any (· matches .wild _)
  let sameWildcard := wild?.any fun j => pats[j]! matches .wild false &&
    Core.writtenSame (exactText arms[j]![3]) (exactText d[3])
  -- The inner `_` arm's body is taken where the outer one's is after the
  -- fix, outside the arm's pattern, so it must mention none of its binders.
  let mentioned := Core.mentionsName (exactText body[3]) x || binders.any (Core.mentionsName (exactText d[3]) ·)
  let innerBinders ← innerArms.flatMapM fun a => return (← topBinders cx a[0]).map binderName
  let clash := innerBinders.any binders.contains
  unless Core.collapsibleMatch true flat innerWildcard sameWildcard mentioned clash innerArms.size do return
  let commented := Core.hasComment (exactText arm)
  let innerTexts := innerArms.pop.map fun a => (" | ".intercalate ((topAlts a[0]).1.map exactText).toList, exactText a[3])
  let fixed := Core.collapsedArms (exactText p[0]) ((patternArgs p).map exactText) k innerTexts
  let msg := Core.collapsibleMatchMsg x (if commented then none else some fixed)
  recordLint .collapsibleMatch body (if !commented && (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)

/-- The match lints of the `match` `e` on a value of type `ty`, whose arms'
patterns are `pats`, where `slot` is (`Reqs/Lint/Style#matches-that-are-memberships`,
`Reqs/Lint/Pedantic/Matches`). The lints that move or remove arms, or
replace `_` with a variant, look only at a `match` whose patterns are all
flat (`Core.Pat.flat`), where no arm overlaps another without containing
it. -/
def lintMatch (cx : ExprCtx) (e : Syntax) (ty : Expr) (pats : Array Core.Pat)
    (slot : Option Core.Slot) : TermElabM Unit := do
  let arms := e[3].getSepArgs
  -- A table over a scrutinee is called a table (`Core.Msg.ofTable`).
  let tm (m : Core.Msg) : Core.Msg := if e.isOfKind ``Lang.tableMatchExpr then m.ofTable else m
  -- An arm with a guard may not be taken where its pattern matches, so
  -- the lints that move, merge or remove arms, or replace the `match`,
  -- look only at a `match` without guards, and the arms with guards name
  -- no variant for the lints of `_` (`Reqs/Lint/Pedantic/Matches#arms`).
  let guarded := arms.map (!·[1].isNone)
  let anyGuard := guarded.any id
  let mut infos : Array Core.ArmInfo := #[]
  for arm in arms, pat in pats do
    let (alts, _) := topAlts arm[0]
    let alts := if alts.size == 1 && arm[0][0].isNone && alts[0]!.isOfKind ``Lang.wildPattern then #[] else alts
    let texts := alts.map exactText
    infos := infos.push { alts := texts, binds := !(← topBinders cx arm[0]).isEmpty, noPayload := pat.noPayload
                          equatable := Core.equatable pat texts, disjoint := alts.isEmpty || Core.disjointPat pat texts
                          body := { text := exactText arm[3], prec := exprPrec arm[3] } }
  let flat := pats.all (·.flat)
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable then m.note Core.fixHelp else m
  -- `trivial_match` (`lint::trivial_match`).
  if let #[i] := infos then
    if Core.trivialMatch infos.size i.binds && !anyGuard then recordLint .trivialMatch e (tm (Core.trivialMatchMsg (i.body.inSlot slot (followedStx e))))
  -- `needless_match` (`lint::needless_match`): only a `match` whose arms
  -- are `_` and variants whose payloads' patterns are `_` or binders.
  let scr := exactText (unparen e[1])
  let enum? := (← getState).enumOf? ty
  let mut givenBack := true
  let mut wildcard := false
  let mut scrutineeBack := false
  for arm in arms, pat in pats do
    let body := unparen arm[3]
    let (alts, isOr) := topAlts arm[0]
    match pat, enum?, alts with
    | .wild false, _, _ =>
      wildcard := true
      scrutineeBack := Core.writtenSame (exactText body) scr
    | .ctor idx qs, some info, #[alt] =>
      unless !isOr && qs.all (· matches .wild _) do givenBack := false; continue
      let bs := (patternArgs alt).map (·[0].getSepArgs[0]!)
      let binders := bs.map fun b => if b.isOfKind ``Lang.wildPattern then "_" else (pathSegs b[0])[0]!.getId.toString
      -- The arm's binders shadow items in its body.
      let shadowing := cx.shadowing ++ (binders.filter (· != "_")).map Name.mkSimple
      let (p, args) := if body.isOfKind ``Lang.appExpr then (body[0], body[2].getSepArgs)
        else (if body.getNumArgs == 1 then body[0] else body, #[])
      -- A dotted name, as `K.len` or `w.x`, is a value, not a variant.
      let same ← if p.isOfKind ``Lang.fren_path && (pathSegs p).all (·.getId.isAtomic) then do
          let names := (pathSegs p).map (·.getId)
          pure (match (← getState).table.resolvePath cx.modName names shadowing with
            | .ok (.variant en i) => en.path == info.path && i == idx
            | _ => false)
        else pure false
      unless Core.givesBack same binders (args.map (exactText ∘ unparen)) do givenBack := false
    | _, _, _ => givenBack := false
  let trivial := Core.trivialMatch infos.size (infos[0]?.any (·.binds))
  let needless := Core.needlessMatch (givenBack && !anyGuard) wildcard scrutineeBack trivial
  if needless then
    let scrutinee : Core.BText := { text := scr, prec := exprPrec (unparen e[1]) }
    recordLint .needlessMatch e (help (tm (Core.needlessMatchMsg (scrutinee.inSlot slot (followedStx e)))))
  if flat && !anyGuard then
    for g in Core.sameArmGroups infos do
      let (i, msg) := Core.sameArmsMsg infos g slot (followedStx e)
      recordLint .matchSameArms arms[i]! (help (tm msg))
  let scrutinee : Core.BText := { text := exactText e[1], prec := exprPrec e[1] }
  let membership? := if anyGuard then none else Core.membershipParts? infos scrutinee slot
  if let some (pre, post, test) := membership? then
    recordLint .matchLikeMembership e (help (tm (Core.membershipMsg (pre ++ scrutinee.text ++ post) test)))
  -- `single_match_else` (`lint::single_match_else`).
  let bool := ty.isConstOf ``Bool || ty.isProp
  if let some fixed := (if anyGuard then none else
      Core.singleMatchElseFix? infos scrutinee slot (membership?.isSome || needless || trivial) (followedStx e) bool) then
    let msg := tm (Core.singleMatchElseMsg fixed (Core.hasComment (exactText e)))
    recordLint .singleMatchElse e (if msg.fixes.isEmpty then msg else help msg)
  -- `match_bool` (`lint::match_bool`).
  if bool && !anyGuard then
    if let some fixed := Core.matchBoolFix? pats infos scrutinee.text slot (membership?.isSome || trivial) (followedStx e) then
      let msg := tm (Core.matchBoolMsg fixed (Core.hasComment (exactText e)))
      recordLint .matchBool e (if msg.fixes.isEmpty then msg else help msg)
  let isTable := e.isOfKind ``Lang.tableMatchExpr
  -- `match_overlapping_arm` (`lint::match_overlapping_arm`). An arm with a
  -- guard is left out, as in Clippy; the arms of a table over a scrutinee
  -- are checked to be disjoint instead.
  let intervals := (pats.zip guarded).map fun (p, g) => p.top.map fun
    | .int lo hi => if g || isTable then none else some (lo, hi)
    | _ => none
  for ((j, b), (i, a)) in Core.overlappingArms intervals do
    recordLint .matchOverlappingArm (topAlts arms[j]![0]).1[b]! (Core.overlappingArmMsg (exactText (topAlts arms[i]![0]).1[a]!))
  unless isTable do
    for i in [0:arms.size] do lintCollapsible cx arms pats i
  for arm in arms, q in pats do lintOrPatterns (orNode (topAlts arm[0]).1 q)
  -- In a table over a scrutinee, `_` also takes what the guards of the
  -- other arms leave, which no pattern can name without overlapping them.
  unless flat && !(isTable && anyGuard) do return
  let some info := (← getState).enumOf? ty | return
  let some w := (Array.range infos.size).find? fun i => infos[i]!.wildcard && !guarded[i]! | return
  let names (p : Core.Pat) : Array Nat := match p with
    | .ctor k _ => #[k]
    | .or alts => alts.filterMap fun | .ctor k _ => some k | _ => none
    | _ => #[]
  let unguarded := (pats.zip guarded).filterMap fun (p, g) => if g then none else some p
  let covered := ((List.range info.variants.size).filter fun k => !unguarded.any (names · |>.contains k)).toArray
  let siblings ← (arms.flatMap fun arm => (topAlts arm[0]).1.filter (·.isOfKind ``Lang.variantPattern)).mapM fun p =>
    (pathSegs p[0]).mapM segName
  let table := (← getState).table
  -- The pattern that names each variant that `_` matches, if one resolves.
  let named := covered.map fun k => (table.variantPath? cx.modName cx.shadowing info.path info.variants[k]! siblings).map
    (Core.variantPattern · info.payloads[k]!.size)
  -- `wildcard_enum_match_arm` (`lint::wildcard_enum_match_arm`).
  let (_, fixable) := Core.wildcardEnumMatchArm true (named.filter (·.isNone)).size
  let pattern? := if fixable then some (" | ".intercalate (named.filterMap id).toList) else none
  let msg := tm (Core.wildcardEnumMsg (covered.map (info.path ++ info.variants[·]!)) pattern?)
  recordLint .wildcardEnumMatchArm arms[w]![0] (if fixable then help msg else msg)
  unless Core.wildcardSingle covered.size do return
  let msg := tm (Core.wildcardMsg (info.path ++ info.variants[covered[0]!]!) named[0]!)
  recordLint .wildcardSingleVariant arms[w]![0] (if named[0]!.isSome then help msg else msg)

/-- `match_could_be_table` on the `match` `e`, whose arms' patterns are
`pats`, on a value of `pty` (`lint::match_could_be_table`). -/
def lintCouldBeTable (e : Syntax) (sigs : Core.Sigs) (pty : Core.PatTy) (pats : Array Core.Pat) : TermElabM Unit := do
  unless e.isOfKind ``Lang.matchExpr do return
  let arms := e[3].getSepArgs
  let guarded := arms.map (!·[1].isNone)
  unless Core.matchCouldBeTable arms.size (guarded.any id) (Core.acceptedAsTable sigs pty pats guarded) do return
  let msg := Core.matchCouldBeTableMsg
  -- `fren fix` reads Markdown specs, but not Lean files.
  recordLint .matchCouldBeTable e (if (← getLocal).inMarkdown then msg.note Core.fixHelp else msg)

/-- The literal `true` or `false` that `e` is, without parentheses. -/
def boolLiteral? (e : Syntax) : Option Bool :=
  let e := unparen e
  -- `true` and `false` are also paths.
  let e := if e.isOfKind choiceKind then (e.getArgs.find? fun a => a.getNumArgs == 1 && a[0].isAtom).getD e[0] else e
  if e.getNumArgs == 1 && e[0].isAtom then
    match e[0].getAtomVal.trimAscii.toString with
    | "true" => some true
    | "false" => some false
    | _ => none
  else none

/-- The source text from the position of `a`, or its end if `aTail`, to
that of `b`, or its end if `bTail`. -/
def textBetween (a : Syntax) (aTail : Bool) (b : Syntax) (bTail : Bool) : String :=
  match a.getSubstring? false false, (if aTail then a.getTailPos? else a.getPos?), (if bTail then b.getTailPos? else b.getPos?) with
  | some sub, some i, some j => String.Pos.Raw.extract sub.str i j
  | _, _, _ => ""

/-- The value that the guard operand `v` is, as `redundant_guards` reads it,
with its text in a pattern and in an expression: a literal, or a variant
without a payload, which is written by its path (`Core.Table.variantPath?`). -/
def guardValue (cx : ExprCtx) (extra : Array Name) (sigs : Core.Sigs) (siblings : Array (Array Name)) (v : Syntax) :
    TermElabM (Core.GuardValue × String × String) := do
  let v := unparen v
  let other := (Core.GuardValue.other, "", "")
  if let some b := boolLiteral? v then return (.pattern (.bool b), toString b, toString b)
  let v := if v.isOfKind choiceKind then v[0] else v
  if v.getNumArgs == 1 && v[0].isOfKind numLitKind then
    let some n := v[0].isNatLit? | return other
    return (.pattern (.int (some n) (some n)), toString n, toString n)
  if v.getNumArgs == 2 && v[0].isAtom && v[0].getAtomVal == "-" && v[1].getNumArgs == 1 && v[1][0].isOfKind numLitKind then
    let some n := v[1][0].isNatLit? | return other
    return (.pattern (.int (some (-(n : Int))) (some (-(n : Int)))), s!"-{n}", s!"(-{n})")
  if v.getNumArgs == 1 && v[0].isOfKind strLitKind then
    let some t := v[0].isStrLit? | return other
    return (.pattern (.str t), exactText v, exactText v)
  let p := if v.getNumArgs == 1 then v[0] else v
  unless p.isOfKind ``Lang.fren_path && (pathSegs p).all (·.getId.isAtomic) do return other
  let names := (pathSegs p).map (·.getId)
  let table := (← getState).table
  let shadowing := cx.shadowing ++ extra
  let .ok (.variant en i) := table.resolvePath cx.modName names shadowing | return other
  unless ((sigs en.path)[i]?.map (·.2.size)) == some 0 do return other
  let some path := table.variantPath? cx.modName shadowing en.path en.variants[i]! siblings | return other
  let t := Core.variantPattern path 0
  return (.pattern (.ctor i #[]), t, t)

/-- `trivial_guard` and `redundant_guards` on the arms of the `match` `e`,
whose patterns are `pats`, on a value of `pty` (`lint::trivial_guard`,
`lint::redundant_guards`): each fix is given only where the static rules
accept the `match` after it (`Core.matchAccepted`). -/
def lintGuards (cx : ExprCtx) (e : Syntax) (sigs : Core.Sigs) (pty : Core.PatTy) (pats : Array Core.Pat) :
    TermElabM Unit := do
  let arms := e[3].getSepArgs
  let isTable := e.isOfKind ``Lang.tableMatchExpr
  let tm (m : Core.Msg) : Core.Msg := if isTable then m.ofTable else m
  -- `fren fix` reads Markdown specs, but not Lean files.
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable && !m.fixes.isEmpty then m.note Core.fixHelp else m
  let guarded := arms.map (!·[1].isNone)
  let siblings ← (arms.flatMap fun arm => (topAlts arm[0]).1.filter (·.isOfKind ``Lang.variantPattern)).mapM fun p =>
    (pathSegs p[0]).mapM segName
  for h : i in [0:arms.size] do
    let arm := arms[i]
    if arm[1].isNone then continue
    let g := arm[1][1]
    -- `trivial_guard` (`lint::trivial_guard`).
    if let some b := boolLiteral? g then
      let accepted := if b then Core.matchAccepted sigs pty pats (guarded.set! i false) isTable
        else Core.matchAccepted sigs pty (pats.eraseIdxIfInBounds i) (guarded.eraseIdxIfInBounds i) isTable
      -- What the fix removes: the guard, from the pattern's end; or the
      -- arm, up to the next one, or from the previous one's end.
      let removed := if b then textBetween arm[0] true arm[1] true
        else if h' : i + 1 < arms.size then textBetween arm false arms[i + 1] false
        else if i > 0 then textBetween arms[i - 1]! true arm true else exactText arm
      let (_, fix) := Core.trivialGuard (.literal b) accepted (Core.hasComment removed)
      recordLint .trivialGuard g (help (tm (Core.trivialGuardMsg b fix !accepted)))
      continue
    -- `redundant_guards` (`lint::redundant_guards`).
    let g' := unparen g
    unless isBinOp g' "=" do continue
    let binders := (← topBinders cx arm[0]).map binderName
    let sides := #[(g'[0], g'[2]), (g'[2], g'[0])]
    let some (x, v) := sides.findSome? fun (a, b) => (soleName? a).bind fun n =>
      if binders.contains (Core.nameText n) then some (Core.nameText n, b) else none | continue
    let (value, inPattern, inExpr) ← guardValue cx (binders.map Name.mkSimple) sigs siblings v
    let some p := Core.redundantGuard? pats[i]! (Core.guardBinderPath? pats[i]! (binders.idxOf? x)) value | continue
    unless Core.matchAccepted sigs pty (pats.set! i p) (guarded.set! i false) isTable do continue
    let some bx := (← topBinders cx arm[0]).find? (binderName · == x) | continue
    let pattern := textBetween arm[0] false bx false ++ inPattern ++ textBetween bx true arm[0] true
    let body := exactText arm[3]
    let (fixed?, why?) :=
      if !Core.mentionsName body x then
        if Core.hasComment (textBetween arm[0] false arm[1] true) then
          (none, some "note: the fix would drop the comments in the arm's pattern or guard, so it has none")
        else (some pattern, none)
      else match Core.replaceMentions? body x inExpr with
        | some b' => if Core.hasComment (textBetween arm[0] false arm[1] true) then
            (none, some "note: the fix would drop the comments in the arm's pattern or guard, so it has none")
          else (some s!"{pattern} => {b'}", none)
        | none => (none, some s!"note: the body mentions `{x}` where its value cannot be written in its place, so it has no fix")
    recordLint .redundantGuards g (help (tm (Core.redundantGuardsMsg x (exactText (unparen v)) fixed? why?)))

/-- `match_arm_if_else` on the `match` `e`, whose arms' patterns are
`pats`, on a value of `pty` (`lint::match_arm_if_else`). -/
def lintArmIfElse (cx : ExprCtx) (e : Syntax) (sigs : Core.Sigs) (pty : Core.PatTy) (pats : Array Core.Pat) :
    TermElabM Unit := do
  unless e.isOfKind ``Lang.matchExpr do return
  let arms := e[3].getSepArgs
  if arms.any (!·[1].isNone) then return
  let mut infos : Array (Core.IfArmInfo String) := #[]
  let mut binders : Array (Array String) := #[]
  for arm in arms, p in pats do
    let body := unparen arm[3]
    let armBody : Core.IfArmBody String := if isIte body then .ifElse (exactText body[5]) else .plain (exactText arm[3])
    -- A condition that binds names cannot be a guard (`F0334`).
    let condBinds ← if isIte body then chainBinds cx body[1] else pure false
    binders := binders.push ((← topBinders cx arm[0]).map binderName)
    infos := infos.push { wild := p matches .wild _, body := armBody, binds := condBinds }
  -- `d` names a binder of arm `j`'s pattern.
  let mentions (d : String) (j : Nat) : Bool := binders[j]!.any (Core.mentionsName d ·)
  let overlap (i j : Nat) : Bool := (pats[i]!.overlapWit? sigs pty pats[j]!).isSome
  let some (group, d, append) := Core.matchArmIfElse? Core.writtenSame mentions overlap infos.toList
    | return
  let guarded := (Array.range arms.size).map group.contains
  let (pats', guarded') := if append then (pats.push (.wild false), guarded.push false) else (pats, guarded)
  unless Core.matchAccepted sigs pty pats' guarded' false do return
  let commented := group.any fun i => Core.hasComment (textBetween arms[i]![0] true arms[i]! true)
  let msg := Core.matchArmIfElseMsg group.size d commented
  -- `fren fix` reads Markdown specs, but not Lean files.
  recordLint .matchArmIfElse arms[group[0]!]![3] (if (← getLocal).inMarkdown && !commented then msg.note Core.fixHelp else msg)


end Fren
