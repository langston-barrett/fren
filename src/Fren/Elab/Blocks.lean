-- keep-sorted start
import Fren.Elab.Functions
-- keep-sorted end

/-! # Hosted elaboration: blocks -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The names that the identifiers within `e` mention, as the `fren`
command reads them from its tokens: each one's first segment, without the
`!` of shadowing. -/
partial def identRoots (e : Syntax) : Array String :=
  if e.isIdent then
    let s := Core.nameText e.getId.getRoot
    #[if s.endsWith "!" then (s.dropEnd 1).toString else s]
  else e.getArgs.foldl (init := #[]) fun acc a =>
    (identRoots a).foldl (init := acc) fun acc n => if acc.contains n then acc else acc.push n

/-- `stx`, everything within it at the position of `ref`. -/
partial def withInfoOf (ref : Syntax) : Syntax → Syntax
  | .node _ k args => .node (SourceInfo.fromRef ref) k (args.map (withInfoOf ref))
  | .atom _ v => .atom (SourceInfo.fromRef ref) v
  | .ident _ raw v pre => .ident (SourceInfo.fromRef ref) raw v pre
  | s => s

/-- `text`, parsed as a `cat`, at the position of `ref`. -/
def parseAt (cat : Name) (text : String) (ref : Syntax) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) cat text with
  | .ok s => return withInfoOf ref s
  | .error e => throwErrorAt ref e

/-- The indices of the definitions of `defs`, `fren_def`s with their
names, that an expression `e` with its own `where` clause `w?` needs
(`Core.neededDefs`). -/
def neededOf (defs : Array (String × Syntax)) (e w? : Syntax) : Array Nat :=
  Core.neededDefs defs (fun d => identRoots d[3]) (identRoots e ++ identRoots w?)

/-- An expression `e` with its own `where` clause `w?`, as an expression
and a `where` clause: the definitions of `defs` that it needs, around it
with its own clause within. -/
def withNeeded (defs : Array (String × Syntax)) (e w? : Syntax) : Syntax × Syntax :=
  let needed := neededOf defs e w?
  if needed.isEmpty then (e, w?) else
  let args := needed.foldl (init := #[]) fun acc i => (if acc.isEmpty then acc else acc.push (mkAtom ",")).push defs[i]!.2
  (withWhere e w?, mkNullNode #[(mkNode ``Lang.fren_where #[mkAtom "where", mkNullNode args] : Syntax)])

/-- Whether `e` is a Boolean block, under any leading `when`, `unless` or
`let`, as a clause without a label must be (`lang::clause_errors`). -/
partial def booleanBlockRoot (e : Syntax) : Bool :=
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then booleanBlockRoot e[3]
  else (unparen e).isOfKind ``Lang.booleanBlockExpr

open Lang in
/-- The clause member `m` as `Core.clauseKeywordError?` and
`Core.clauseSyntaxError?` read it: its keyword,
and how it is written, with a label or without one, and whether its
expression, with its `where` clause, is a Boolean block. -/
def clauseOf? (m : Syntax) : Option (Core.ClauseWord × Core.ClauseForm) :=
  let bare? : Option Core.ClauseWord :=
    if m.isOfKind ``Lang.bareAssumeMember then some .assume
    else if m.isOfKind ``Lang.bareRequireMember then some .require
    else if m.isOfKind ``Lang.bareEnsureMember then some .ensure
    else if m.isOfKind ``Lang.bareExpectMember then some .expect
    else none
  let labelled? : Option Core.ClauseWord :=
    if m.isOfKind ``Lang.assumeMember then some .assume
    else if m.isOfKind ``Lang.requireMember then some .require
    else if m.isOfKind ``Lang.ensureMember then some .ensure
    else if m.isOfKind ``Lang.expectMember then some .expect
    else if m.isOfKind ``Lang.coverMember then some .cover
    else none
  match bare?, labelled? with
  | some w, _ => some (w, { labelled := false, blockRoot := booleanBlockRoot (withWhere m[1] m[2]) })
  | none, some w => some (w, { labelled := true, blockRoot := booleanBlockRoot (withWhere m[3] m[4]) })
  | none, none => none

open Lang in
/-- The member `m` of a function's block, if the block does not take it
(`F0442`, `F0443`): where it is reported, at its first token, or a
`use`'s or an evidence setting's whole, as the `fren` command reports it,
and the message. -/
def fnMemberError? (m : Syntax) : Option (Syntax × Core.Msg) :=
  let kind? : Option (Core.FnMember × Bool × String × Syntax) :=
    if m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember then some (.use, false, "use", m)
    else if m.isOfKind ``Lang.evidenceMember then some (.evidence, false, "set_option", mkNullNode #[m[0], m[3]])
    else if m.isOfKind ``Lang.callMember then some (.call, false, "call", m[0])
    else if m.isOfKind ``Lang.existsMember then some (.exists, !m[0].isNone, "exists", if m[0].isNone then m[1] else m[0])
    else if m.isOfKind ``Lang.letMember then some (.let, !m[0].isNone, "let", if m[0].isNone then m[1] else m[0])
    else match clauseOf? m with
      | some (.expect, _) => some (.claim, false, "expect", m[0])
      | some (.cover, _) => some (.claim, false, "cover", m[0])
      | _ => none
  kind?.bind fun (k, det, kw, ref) => (Core.fnMemberMsg? k det kw).map (ref, ·)

/-- The error that `x` throws first, if any, as an action that throws it
again. -/
def caughtError (x : CommandElabM Unit) : CommandElabM (Option (CommandElabM Unit)) := do
  try x; return none catch e => return some (throw e)

open Lang in
/-- The part of a block's errors (`Core.firstPartError?`) of an evidence
setting before a member, `set_option NAME "VALUE" in`: an option other
than `fren.evidence` (`checkParsed`), and, if `rejected?`, the error that
the block does not take it. -/
def settingErrors (w : Syntax) (rejected? : Option (CommandElabM Unit)) :
    List (Core.BlockCheck × CommandElabM Unit) :=
  (if w[1].getId == `fren.evidence then [] else
    [(.syntax, throwErrorAt w[1] (Core.memberOptionMsg w[1].getId.toString).text)])
  ++ (rejected?.map (.rejected, ·)).toList

/-- The error of how the clause member `m` is written, if it is `read`
with no error of its own syntax (`Core.clauseSyntaxError?`,
`lang::clause_errors`), of a member that the source writes, not one that
an item generates, reported at the keyword: a clause without a label that
is not a Boolean block. -/
def clauseSyntaxAt (m : Syntax) (read : Bool) : List (Core.BlockCheck × CommandElabM Unit) :=
  match clauseOf? m, m[0].getHeadInfo with
  | some (w, form), .original .. =>
    ((Core.clauseSyntaxError? w (if read then some form else none)).map fun msg => (.syntax, throwErrorAt m[0] msg.text)).toList
  | _, _ => []

/-- The member `m`, under any evidence settings before it. -/
partial def underEvidence (m : Syntax) : Syntax :=
  if m.isOfKind ``Lang.evidenceMember then underEvidence m[4] else m

/-- The command `c`, under any of Lean's `set_option ... in` before it. -/
partial def underSettings (c : Syntax) : Syntax :=
  if c.isOfKind ``Lean.Parser.Command.in then underSettings c[2] else c

open Lang in
/-- The clauses of the item `stx`, as `Core.ItemShape` (`lang::item_error`)
reads its structure, each that the source writes with its keyword, where
its error is reported: the members of a procedure's, a function's or a
global expectation's block, and every member of a trait, of every kind,
those that the trait does not take included, each under any `set_option
... in`. -/
partial def itemShape (stx : Syntax) : Core.ItemShape Syntax :=
  let stx := underSettings stx
  if stx.isOfKind ``Lang.procCmd then blockShape stx[8].getArgs false
  else if stx.isOfKind ``Lang.fnBlockCmd then blockShape stx[12].getArgs false
  else if stx.isOfKind ``Lang.globalBlockCmd then blockShape stx[7].getArgs true
  else if stx.isOfKind ``Lang.traitCmd then
    .members (stx[4].getArgs.toList.map fun m => if m.isOfKind ``Lang.lawMember then .done else itemShape m[0])
  else .done
where
  blockShape (members : Array Syntax) (global : Bool) : Core.ItemShape Syntax :=
    .ofList (members.toList.filterMap fun m0 =>
      let m := underEvidence m0
      match clauseOf? m, m[0].getHeadInfo with
      | some (w, _), .original .. => some (w, global, m[0])
      | _, _ => none)

/-- Reports the first static error of the item `stx`, whose first error of
its syntax, if any, is `parse?` (`Core.itemError?`, `lang::item_error`):
that one, else the first error of a clause's keyword in its shape
(`itemShape`), at the keyword. -/
def reportItem (parse? : Option (CommandElabM Unit)) (stx : Syntax) : CommandElabM Unit := do
  if let some r := Core.itemError? parse? (itemShape stx) (fun msg ref => throwErrorAt ref msg.text) then r

/-- The static errors of the syntax of the function's block `stx` that the
`fren` command's parser reports, the first of them by
`Core.firstBlockError?` (`lang::block_errors`). Its parts, in source order: its name
and parameters; its first result, with a modifier that it does not take,
`det` or an evidence setting (`F0442`), before its own syntax; a second
result (`F0445`); and each member, an evidence setting before it as a part
of its own (`F0442`), with its own syntax, how it is written
(`clauseSyntaxAt`: a clause without a label that is not a Boolean block),
and whether the block takes it (`F0442`, `F0443`, an `out` of another
name, `F0444`, or of the result again, `refines`). -/
def fnBlockErrors (stx : Syntax) : CommandElabM (Option (CommandElabM Unit)) := do
  let mut parts : List (List (Core.BlockCheck × CommandElabM Unit)) := []
  let header ← caughtError (for i in [0:9] do checkParsed stx[i])
  parts := parts ++ [(header.map (.syntax, ·)).toList]
  let results := stx[9].getSepArgs
  let r := results[0]!
  let mut first : List (Core.BlockCheck × CommandElabM Unit) := []
  unless r[0].isNone do
    first := first ++ [(.modifier, throwErrorAt r[0][0][0] (Core.fnMemberMsg? .evidence false "set_option").get!.text)]
  unless r[1].isNone do
    first := first ++ [(.modifier, throwErrorAt r[1] (Core.fnMemberMsg? .define true "det").get!.text)]
  if let some e ← caughtError (checkParsed r) then first := first ++ [(.syntax, e)]
  parts := parts ++ [first]
  if let some r2 := results[1]? then
    parts := parts ++ [[(.rejected, throwErrorAt (r2.getHead?.getD r2) Core.fnResultsMsg.text)]]
  let rest ← caughtError (for i in [10:12] do checkParsed stx[i])
  parts := parts ++ [(rest.map (.syntax, ·)).toList]
  let rn := Core.nameText (declaredIdent r[2]).1.getId
  let mut defined := false
  for m0 in stx[12].getArgs do
    let mut m := m0
    while m.isOfKind ``Lang.evidenceMember do
      let rejected? := (fnMemberError? m).map fun (ref, msg) => throwErrorAt ref msg.text
      parts := parts ++ [settingErrors m rejected?]
      m := m[4]
    let own ← caughtError (checkParsed m)
    let rejected? : Option (CommandElabM Unit) :=
      if m.isOfKind ``Lang.refinesMember then
        some (throwErrorAt m "`refines` is accepted only in global expectation blocks")
      else if m.isOfKind ``Lang.defineMember then
        let x := Core.nameText m[1].getId
        if x != rn then some (throwErrorAt (mkNullNode #[m[0], m[1]]) (Core.fnOutMsg x rn).text)
        else if defined then some (throwErrorAt m[1] (Core.resultDefinedTwiceMsg x).text)
        else none
      else (fnMemberError? (requireAsAssume m)).map fun (ref, msg) => throwErrorAt ref msg.text
    if m.isOfKind ``Lang.defineMember && Core.nameText m[1].getId == rn then defined := true
    parts := parts ++ [(own.map (.syntax, ·)).toList ++ clauseSyntaxAt m own.isNone ++ (rejected?.map (.rejected, ·)).toList]
  let tail ← caughtError (for i in [13:stx.getNumArgs] do checkParsed stx[i])
  parts := parts ++ [(tail.map (.syntax, ·)).toList]
  return Core.firstBlockError? parts

/-- The function's block `stx`'s first static error, if any
(`fnBlockErrors`, `reportItem`). -/
def checkFnBlockParsed (stx : Syntax) : CommandElabM Unit := do reportItem (← fnBlockErrors stx) stx

open Lang in
/-- One source clause's independent conjunction leaves, preserving lexical
and leading guard wrappers. Disjunction/negation/equivalence remain one
clause; generated paths are logical names, not user binder declarations. -/
partial def clauseLeaves (owner : Name) (source : Syntax) : CommandElabM (Array (Syntax × Syntax)) := do
  let e := unparen source
  if isBooleanGuard e then
    return (← clauseLeaves owner e[3]).map fun (name, body) => (name, e.setArg 3 body)
  if e.isOfKind ``Lang.letExpr then
    return (← clauseLeaves owner e[3]).map fun (name, body) => (name, e.setArg 3 body)
  if let some ("and", members) := booleanBlockView e then
    let labels := members.filterMap (·.1)
    if let some k := (Core.repeatsAt (labels.map (·.getId)))[0]? then
      throwErrorAt labels[k]! "a Boolean block repeats label `{labels[k]!.getId}`"
    let mut leaves := #[]
    for (label, body) in members, i in [0:members.size] do
      if let some label := label then
        discard (segName label)
        liftMsg label (Core.checkNoBang label.getId)
      let segment := label.map (·.getId.toString) |>.getD (toString (i + 1))
      let name := Name.mkSimple (if owner.isAnonymous then segment else owner.toString ++ "." ++ segment)
      let child ← clauseLeaves name body
      leaves := leaves ++ child.map fun (ref, value) =>
        (if ref.getId == name then (mkIdentFrom (label.getD body) name).raw else ref, value)
    return leaves
  let owner := if owner.isAnonymous then Name.mkSimple "1" else owner
  return #[(mkIdentFrom source owner, source)]

partial def conjunctionClause (e : Syntax) : Bool :=
  if isBooleanGuard e || e.isOfKind ``Lang.letExpr then conjunctionClause e[3]
  else (booleanBlockView e).any (·.1 == "and")

/-- Normalize the optional outer label and conjunction-clause sugar
before evidence settings and duplicate-member checks are collected. -/
def splitBooleanMember (member : Syntax) : CommandElabM (Option (Array Syntax)) := do
  let bare := member.isOfKind ``Lang.bareAssumeMember || member.isOfKind ``Lang.bareEnsureMember || member.isOfKind ``Lang.bareExpectMember
  let parsed := constraint? member
  if !bare && parsed.isNone then return none
  let (kind, owner, expression) := if bare then
      let kind := if member.isOfKind ``Lang.bareAssumeMember then PropKind.assume
                  else if member.isOfKind ``Lang.bareEnsureMember then .ensure else .expect
      (kind, Name.anonymous, withWhere member[1] member[2])
    else let (kind, name, expression) := parsed.get!; (kind, name.getId, expression)
  if bare && !booleanBlockRoot expression then
    throwErrorAt member[0] (Core.bareClauseMsg member[0].getAtomVal.trimAscii.toString).text
  if kind == .cover || (!bare && !conjunctionClause expression) then return some #[member]
  let leaves ← clauseLeaves owner expression
  return some (leaves.map fun (name, body) =>
    let syntaxKind := match kind with | .assume => ``Lang.assumeMember | .ensure => ``Lang.ensureMember
                                      | .expect => ``Lang.expectMember | .cover => ``Lang.coverMember
    mkNode syntaxKind #[member[0], name, mkAtom ":", body, mkNullNode])

/-- A function written with its result and a block
(`Reqs/Lang/Items#function-blocks`), as the `fren` command reads it: the
function whose body is its `out` member's expression and whose contract is
its `require`s and `ensure`s, each with the result, `r := f(x)`, and the
`let`s that it needs as a `where` clause (`F0442`–`F0445`, `F0165`). -/
def lowerFnBlock (stx : Syntax) : CommandElabM (Syntax × Array Syntax) := do
  checkLexemes stx
  checkFnBlockParsed stx
  let stx := requiresAsAssumes stx 12
  let results := stx[9].getSepArgs
  let r := results[0]!
  let rx := (declaredIdent r[2]).1
  let rn := Core.nameText rx.getId
  let mut lets : Array (String × Syntax) := #[]
  let mut out? : Option Syntax := none
  let mut clauses := #[]
  let mut uses := #[]
  for m in stx[12].getArgs do
    let mut inner := m
    while inner.isOfKind ``Lang.evidenceMember do inner := inner[4]
    if inner.isOfKind ``Lang.refinesMember then
      throwErrorAt inner "`refines` is accepted only in global expectation blocks"
    if m.isOfKind ``Lang.useMember || m.isOfKind ``Lang.useGroupMember then uses := uses.push m
    else if m.isOfKind ``Lang.letMember then
      let x := (declaredIdent m[2]).1
      lets := lets.push (Core.nameText x.getId, (mkNode ``Lang.fren_def #[m[2], m[3], m[4], withWhere m[5] m[6]] : Syntax))
    else if m.isOfKind ``Lang.defineMember then
      let x := Core.nameText m[1].getId
      unless x == rn do throwErrorAt (mkNullNode #[m[0], m[1]]) (Core.fnOutMsg x rn).text
      if out?.isSome then throwErrorAt m[1] (Core.resultDefinedTwiceMsg x).text
      out? := some (mkNullNode #[m[2], m[3], m[4]])
    else if (constraint? m).isSome then clauses := clauses.push m
    -- A clause without a label, a Boolean block, as its leaves, as a
    -- procedure's is (`splitBooleanMember`).
    else if (clauseOf? m).any (!·.2.labelled) then
      if let some split ← splitBooleanMember m then clauses := clauses ++ split
  -- Expand implicit parameters before forming the result's self-call in
  -- postconditions; that call must use the same fresh parameters.
  let (parameters, expandedOut) ← match out? with
    | some body => liftTermElabM do
      let fn := mkNode ``Lang.fnCmd #[stx[0], stx[1], stx[2], stx[3], stx[4], stx[5], stx[6], mkNullNode, body, mkNullNode]
      let expanded ← anonymousMatchFunction fn
      pure (expanded[5], some expanded[8])
    | none => pure (stx[5], out?)
  out? := expandedOut
  -- The result, the function applied to its parameters, at the result's
  -- name.
  let fname := Core.nameText (declaredIdent stx[2]).1.getId
  let pnames := parameters.getSepArgs.map fun p =>
    match typePath? p[0] with
    | some q => (declaredIdent (pathSegs q)[0]!).1.getId
    | none => Name.anonymous
  let args ← liftTermElabM <| pnames.mapM (pathExpr rx)
  let template ← parseAt `fren_expr s!"{fname}(false)" rx
  let value := template.setArg 2 (Syntax.mkSep args (mkAtom ","))
  -- With the result's type, if written, which a generic function's
  -- application may need.
  let rDef : Syntax := mkNode ``Lang.fren_def #[withInfoOf rx (mkIdent rx.getId), r[3], mkAtom ":=", value]
  let defs := #[(rn, rDef)] ++ lets
  -- The result is the function's value: neither its body nor its
  -- preconditions mention it (`F0165`).
  let check (e w? : Syntax) : CommandElabM Unit := do
    let needed := Core.neededDefs lets (fun d => identRoots d[3]) (identRoots e ++ identRoots w?)
    let all := identRoots e ++ identRoots w? ++ needed.flatMap fun i => identRoots lets[i]!.2[3]
    if all.contains rn then throwErrorAt (mkNullNode #[e, w?]) (Core.fnResultMentionMsg rn).text
  let mut clauses' := #[]
  -- And the `let`s that some expression needs, the others unused.
  let mut used : Array Nat := #[]
  for c in clauses do
    let isEnsure := c[0].getAtomVal.trimAscii.toString == "ensure"
    unless isEnsure do check c[3] c[4]
    used := used ++ (neededOf defs c[3] c[4]).filterMap fun i => if i == 0 then none else some (i - 1)
    let kw := mkAtomFrom c[0] (if isEnsure then "ensure " else "assume ")
    let (e, w) := withNeeded defs c[3] c[4]
    clauses' := clauses'.push (mkNode ``Lang.fren_clause #[kw, c[1], c[2], e, w])
  let body ← match out? with
    | some d => do
      check d[1] d[2]
      used := used ++ neededOf lets d[1] d[2]
      let (e, w) := withNeeded lets d[1] d[2]
      pure (mkNullNode #[d[0], e, w])
    | none => pure mkNullNode
  -- Its `let`s that nothing needs, as a procedure's (`unused_variables`).
  for (n, d) in lets, i in [0:lets.size] do
    unless used.contains i do
      recordLint .unusedVariables (declaredIdent d[0]).1 (Core.unusedVariableMsg (Name.mkSimple n) false true)
  -- A result `r?` without a type is a `Bool`, as is the function's
  -- value if its name ends in `?` too.
  let result ← if !r[3].isNone then pure r[3]
    else if rn.endsWith "?" && !fname.endsWith "?" then pure (mkNullNode #[mkAtom ":", ← parseAt `fren_type "Bool" rx])
    else pure mkNullNode
  let fn := mkNode ``Lang.fnCmd #[stx[0], stx[1], stx[2], stx[3], stx[4], parameters, stx[6], result, body, mkNullNode clauses']
  return (fn, uses)

@[command_elab Lang.fnBlockCmd] def elabFnBlock : CommandElab := recordingErrors fun stx => do
  let (fn, uses) ← lowerFnBlock stx
  elabFunctionCore fn stx uses



end Fren
