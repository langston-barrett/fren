-- keep-sorted start
import Fren.Elab.ProcedureSyntax
-- keep-sorted end

/-! # Hosted elaboration: induction -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang

/-- `stx`, with each identifier named `n` named `m` instead. -/
partial def renameIdent (n m : Name) : Syntax → Syntax
  | .node info k args => .node info k (args.map (renameIdent n m))
  | s@(.ident info raw v pre) => if v == n then .ident info raw m pre else s
  | s => s

/-- The text of each part of each identifier within `stx`. -/
partial def identNames : Syntax → Array String
  | .node _ _ args => args.foldl (fun acc a => acc ++ identNames a) #[]
  | .ident _ _ v _ => v.components.toArray.map Core.nameText
  | _ => #[]

open Lang in
/-- `stx`, with each expression or type that is the path of the one segment
`n` replaced by `repl`. -/
partial def substPath (n : Name) (repl : Syntax) : Syntax → Syntax
  | .node info k args =>
    if args.size == 1 && args[0]!.isOfKind ``Lang.fren_path && (pathSegs args[0]!).size == 1
        && (pathSegs args[0]!)[0]!.getId == n then repl
    else .node info k (args.map (substPath n repl))
  | s => s

open Lang in
/-- Elaborates the functions generated for induction on the parameters of
the global expectation at `path`, just elaborated, as a procedure `stx`,
whose members, as a component's, are `members`
(`Reqs/Lang/Recursion#induction`): one for each of its claims and each
candidate, in order (`Core.inductionCandidates`). Each is an item of the
module that nothing reports, whose body is not checked as a function's,
but only for the expectation, and which is kept apart from the defined
functions (`State.inductionFns`). -/
def elabInductions (stx : Syntax) (path : Name) (members : Array Syntax) : CommandElabM Unit := do
  let st ← getState
  let some c := st.globals.get? path | return
  let l ← getLocal
  let kinds := (← blockMembers stx).map (·.2.1)
  let params := stx[4].getSepArgs.filter (·[3].isNone)
  let names := params.map fun p => (declaredIdent p[1]).1.getId
  let vars := names.filterMap fun x => c.vars.find? (·.name == x)
  unless vars.size == params.size do return
  let tys := vars.map (·.ptype.ty)
  let candidates := Core.inductionCandidates st.shapeOf kinds.toList l.inductionAbstract
    (vars.map fun v => (v.name, v.ptype)) l.inductionArgs
  if candidates.isEmpty then return
  let assumptions := members.filterMap fun m => match constraint? m with
    | some (.assume, _, e) => some e
    | _ => none
  let position := (charRange (← getFileMap).source stx[2]).start
  let ref := stx[2]
  let savedModule := l.currentModule
  -- Placeholders for the parts that are spliced in after parsing, under a
  -- prefix that no name in the expectation or the generated patterns
  -- starts with: renaming must not rewrite a variant or an enum's name
  -- hidden by an alias in the expectation's signature.
  let patternNames := candidates.toArray.flatMap fun i => match tys[i]! with
    | .enum ep _ => ((st.enums.get? ep).map fun info => info.variants.flatMap fun v =>
        (Core.variantSegments savedModule ep v).toArray).getD #[]
    | _ => #[]
  let written := identNames stx ++ patternNames
  let mut fresh := "fren_induction_"
  while written.any (·.startsWith fresh) do fresh := fresh ++ "_"
  let stem := fresh
  let ph (s : String) : String := stem ++ s
  let mut inductions := #[]
  for m in members do
    let some (.expect, claim, e) := constraint? m | continue
    let mut fns := #[]
    for i in candidates do
      let .enum ep _ := tys[i]! | continue
      let some info := st.enums.get? ep | continue
      let n := params.size
      let fname := Core.inductionFnName (Core.nameText (declaredIdent stx[2]).1.getId) (Core.nameText claim.getId)
        (Core.nameText names[i]!) position
      let cases := Core.inductionCases st.shapeOf tys i
      let builder : Core.InductionSyntax String := {
        truth := "true"
        app := fun f xs => s!"{f}({", ".intercalate xs})"
        conjoin := fun a b => s!"({a}) and ({b})"
        guard := fun a b => s!"when {a}, {b}"
        matchOn := fun x arms =>
          let arms := arms.map fun arm =>
            let pattern := "::".intercalate arm.variant ++ (if arm.binders.isEmpty then ""
              else "(" ++ ", ".intercalate arm.binders.toList ++ ")")
            s!"{pattern} => {arm.value}"
          s!"match {x} \{ {", ".intercalate arms.toList} }" }
      let (bodyText, postText) := Core.buildInduction builder st.shapeOf savedModule ep info.variants
        (names.map Core.nameText) tys (ph "f?") i
        (assumptions.mapIdx fun k _ => ph s!"a{k}") (ph "c")
        (fun k b => ph s!"p{k}" ++ (if b then "?" else ""))
      let signature := params.mapIdx fun k p =>
        Core.nameText p[1].getId ++ (if p[2].isNone then "" else s!": {ph s!"t{k}"}")
      let text := s!"pub fn {ph "f?"}({", ".intercalate signature.toList}): Bool := {bodyText}"
      let some cmd ← try some <$> parseAt `command text ref catch _ => pure none | continue
      let some post ← try some <$> parseAt `fren_expr postText ref catch _ => pure none | continue
      -- Every placeholder of the parsed text is renamed before any of the
      -- expectation's own syntax is spliced in: the binders, and the
      -- function's name, which no source can write, so it is parsed as
      -- another; then the types, the assumptions, and the claim last.
      let mut cmd := cmd
      for ((payload, _), _) in cases.zip info.variants do
        for t in payload, k in [0:payload.size] do
          let b := t matches .bool
          cmd := renameIdent (Name.mkSimple (ph s!"p{k}" ++ (if b then "?" else ""))) (Name.mkSimple (Core.inductionBinder k b)) cmd
      cmd := renameIdent (Name.mkSimple (ph "f?")) (Name.mkSimple fname) cmd
      for p in params, k in [0:n] do
        unless p[2].isNone do cmd := substPath (Name.mkSimple (ph s!"t{k}")) p[2][1] cmd
      let mut post := renameIdent (Name.mkSimple (ph "f?")) (Name.mkSimple fname) post
      for a in assumptions, k in [0:assumptions.size] do
        post := substPath (Name.mkSimple (ph s!"a{k}")) a post
      post := substPath (Name.mkSimple (ph "c")) e post
      let clause := mkNode ``Lang.fren_clause #[mkAtom "ensure", mkIdentFrom ref `claim, mkAtom ":", post, mkNullNode]
      let function := mkNode ``Lang.fnCmd (cmd.getArgs.push (mkNullNode #[clause]))
      -- Nothing about it is reported, and its body is checked only for
      -- the expectation.
      let saved ← get
      let savedLocal ← getLocal
      let failed ← try elabFunctionCore function function; pure false catch _ => pure true
      let logged := (← get).messages.toList.drop saved.messages.toList.length
      let fpath := savedLocal.currentModule ++ Name.mkSimple fname
      let recursive := (((← getState).defined.get? fpath).bind (·.decreasing?)).isSome
      if failed || logged.any (·.severity == .error) || !recursive || !((← getState).bodies.contains fpath) then
        set saved
        continue
      modify fun s => { s with messages := saved.messages }
      modifyLocal fun l => { l with
        lintReports := savedLocal.lintReports, natReports := savedLocal.natReports, bodies := savedLocal.bodies
        currentItem := savedLocal.currentItem }
      record (.inductionFn fpath)
      fns := fns.push fpath
    inductions := inductions.push (claim.getId, fns)
  record (.globalInfo path { c with inductions })


end Fren
