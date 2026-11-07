-- keep-sorted start
import Fren.Elab.GlobalBlocks
import Fren.Elab.GlobalExpectations
-- keep-sorted end

/-! # Hosted elaboration: traits -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- What a member of a trait is, as written (`lang::trait_member`): its
kind, whether it is written `pub`, has type parameters, or has a `use` in
its block, and its name, under any `set_option ... in`. -/
partial def traitMemberOf (m : Syntax) : Core.TraitMember × Bool × Bool × Bool × Option Syntax × Syntax :=
  if m.isOfKind ``Lang.lawMember then (.law, false, false, false, some m[2], m[2]) else
  let c := m[0]
  let other (what : String) (ref : Syntax) := (Core.TraitMember.other what, false, false, false, none, ref)
  let uses (ms : Array Syntax) := ms.any fun x => x.isOfKind ``Lang.useMember || x.isOfKind ``Lang.useGroupMember
  if c.isOfKind ``Lean.Parser.Command.in then traitMemberOf (mkNode ``Lang.itemMember #[c[2]])
  else if c.isOfKind ``Lang.fnCmd then
    (if c[8].isNone then .method else .definedFunction, !c[0].isNone, !c[3].isNone, false, some c[2], c[2])
  else if c.isOfKind ``Lang.fnBlockCmd then
    let ms := c[12].getArgs
    (if ms.any (·.isOfKind ``Lang.defineMember) then .definedFunction else .method, !c[0].isNone, !c[3].isNone,
      uses ms, some c[2], c[2])
  else if c.isOfKind ``Lang.globalCmd then (.expectation, false, false, false, some c[1], c[1])
  else if c.isOfKind ``Lang.globalBlockCmd then (.expectation, false, false, uses c[7].getArgs, some c[1], c[1])
  else if c.isOfKind ``Lang.procCmd then (.other "procedures", !c[0].isNone, false, false, some c[2], c[2])
  else if c.isOfKind ``Lang.enumCmd || c.isOfKind ``Lang.structCmd || c.isOfKind ``Lang.newtypeCmd then
    other "enums or structs" c[3]
  else if c.isOfKind ``Lang.typeCmd || c.isOfKind ``Lang.subsetTypeCmd || c.isOfKind ``Lang.subsetShorthandCmd then
    other "types" c[2]
  else if c.isOfKind ``Lang.constCmd then other "constants" c[2]
  else if c.isOfKind ``Lang.modCmd then other "modules" c[2]
  else if c.isOfKind ``Lang.useCmd || c.isOfKind ``Lang.useGroupCmd then other "`use`s" c
  else if c.isOfKind ``Lang.traitCmd then other "traits" c[2]
  else if c.isOfKind `Fren.Lang.testedCmd || c.isOfKind `Fren.Lang.trustedCmd then other "claims" c[1]
  else other "commands" c

/-- `elabLaw`, once its settings are in effect. -/
def elabLawBody (path : Name) (m : Syntax) : CommandElabM (Name × Expr × Bool × Bool × Bool) := do
  let m := mkNullNode (m.getArgs.extract 1 m.getNumArgs)
  lintItem m
  let nameStx := m[1]
  let n ← itemSegName nameStx
  liftMsg nameStx (Core.checkNoBang (← segName nameStx))
  if n.toString.endsWith "?" then throwErrorAt nameStx (Core.propNameMsg n).text
  lintName .law n nameStx
  startDeclared
  modifyLocal fun l => { l with currentItem := path ++ n }
  let fields := m[3].getSepArgs
  -- Distinct names (`lang::distinct_names`), without the `!` of shadowing.
  let ids := fields.map (·[0])
  for x in ids do discard (segName x)
  let declared := ids.map fun x => (declaredIdent x).1.getId
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt ids[k]! (Core.dupParamMsg declared[k]!).text
  liftTermElabM do
    modifyLocal fun l => { l with outsideCore := false, guardedUsed := false, undecidableDenied := false, relationalUsed := false, countRefs := #[] }
    -- Each variable has its type written, but a `Bool`, which may be
    -- written `x?` alone, as a function's parameter may.
    let mut binders : Array Syntax := #[]
    for f in fields do
      let ty ← if f[1].isNone then do
          discard (varPType path f[0] none)
          liftCommandElabM (parseAt `fren_type "Bool" f[0])
        else pure f[1][1]
      -- At the variable, where a message about the binder is reported.
      binders := binders.push (mkNode ``Lang.fren_binder
        #[mkAtomFrom f "(", mkNullNode #[f[0]], mkAtomFrom f " : ", ty, mkAtomFrom f ")"])
    let body := withWhere m[6] m[7]
    let cx : ExprCtx := { modName := path, vars := #[], insts := #[], place := .prop }
    discard (takeIndexes #[])
    let t ← if binders.isEmpty then toTerm cx body else quantTerm toTerm cx body true binders body
    checkDeclared body t (mkConst ``Bool) fun _ => "note: a law is a `Bool`"
    let e ← elabProp t
    discard (takeIndexes #[])
    lintBools body (← hidesIn cx (declared.map (·, Core.BindingKind.boundName)))
    lintDeclared .law n nameStx
    discard checkCounts
    let l ← getLocal
    return (n, e, !l.outsideCore, l.undecidableDenied, l.guardedUsed)

/-- Elaborates a law of the trait at `path` (`Reqs/Lang/Traits#laws`): its
variables are a quantifier around its equation, and it mentions no
variables, as a global expectation in the short form does. Gives its
statement, a closed proposition over the placeholders, whether it is in the
decidable core, whether `undecidable` is an error in it, and whether it
sets `fmf-bound`. -/
def elabLaw (path : Name) (m : Syntax) : CommandElabM (Name × Expr × Bool × Bool × Bool) := do
  -- Its settings, `set_option ... in`, for it alone, as Lean's own are
  -- for an item.
  let opts := (← getScope).opts
  let settingOf (st : Syntax) : String × String :=
    let name := (st.getArgs.find? (·.isIdent)).map (·.getId) |>.getD .anonymous
    let value := st.getArgs.findSome? fun a => match a.isStrLit?, a.isNatLit? with
      | some v, _ => some s!"\"{v}\""
      | none, some n => some (toString n)
      | none, none => none
    (name.toString, value.getD "")
  -- The settings before it, which a law takes only if every one is a
  -- lint's (`Core.lawSettingsMsg?`), checked before any is in effect.
  if let some (k, msg) := Core.lawSettingsMsg? (m[0].getArgs.toList.map settingOf) then
    throwErrorAt m[0].getArgs[k]! msg.text
  try
    for st in m[0].getArgs do
      let name := (st.getArgs.find? (·.isIdent)).map (·.getId) |>.getD .anonymous
      let value := st.getArgs.findSome? fun a => match a.isStrLit?, a.isNatLit? with
        | some v, _ => some s!"\"{v}\""
        | none, some n => some (toString n)
        | none, none => none
      elabCommand (← parseAt `command s!"set_option {name} {value.getD ""}" st)
    elabLawBody path m
  finally modifyScope fun sc => { sc with opts }


/-- Runs `k` in the scope of the trait at `path`, declared in the module
`modName`, as its members are. -/
def inTraitScope (path modName : Name) (k : CommandElabM α) : CommandElabM α := do
  modifyLocal fun l => { l with currentModule := path, inTrait := true }
  try k finally modifyLocal fun l => { l with currentModule := modName, inTrait := false }

open Lang in
/-- `[pub] trait T { members }` (`Reqs/Lang/Traits`): its carrier `Self`,
an abstract type; its methods, uninterpreted functions, each seen by those
after it; its laws; and its expectations, global expectations whose checks
have the laws among their hypotheses (`CompInfo.laws`). Each member is in
the trait's scope, whose names shadow its module's, and reports its own
errors. -/
@[command_elab Lang.traitCmd] def elabTrait : CommandElab := recordingErrors fun stx => do
  -- Its name's and its members' lexemes, as each item's own are checked,
  -- but not those of Lean's `set_option ... in` before a member.
  let members := stx[4].getArgs
  -- A law's, without its settings, as a command's without Lean's.
  -- A method's, a procedure's or an expectation's block in the order of
  -- the `fren` command's parser (`lang::block_errors`), and the first error
  -- of a clause's keyword only once the whole trait is read, from its shape,
  -- as the `fren` command reads it as one item (`reportItem`,
  -- `lang::item_error`).
  for x in #[stx[2]] ++ members.map fun m =>
      if m.isOfKind ``Lang.lawMember then mkNullNode (m.getArgs.extract 1 m.getNumArgs) else underSettings m[0] do
    checkLexemes x
    let parse? ←
      if x.isOfKind ``Lang.fnBlockCmd then fnBlockErrors x
      else if x.isOfKind ``Lang.globalBlockCmd then globalBlockErrors x
      else if x.isOfKind ``Lang.procCmd then procBlockErrors x
      else caughtError (checkParsed x)
    if let some e := parse? then e
  reportItem none stx
  lintItem stx[2]
  lintTrailingCommas stx
  let modName := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "trait" nameStx
  checkFresh modName n nameStx
  lintName .trait n nameStx
  let path := modName ++ n
  let selfPath := path ++ Core.selfName
  for m in members do
    let (kind, isPubM, generic, uses, _, ref) := traitMemberOf m
    if let some msg := Core.traitMemberMsg? path kind isPubM generic uses then throwErrorAt ref msg.text
  -- Distinct names, with the carrier's (`lang::distinct_names`).
  let named := members.filterMap (traitMemberOf · |>.2.2.2.2.1)
  let declared := #[Core.selfName] ++ (← named.mapM fun x => return (declaredIdent x).1.getId)
  if let some k := (Core.repeatsAt declared)[0]? then
    throwErrorAt named[k - 1]! (Core.dupTraitMemberMsg declared[k]!).text
  -- The trait, and its carrier, which its members see first.
  record (.item { item := { kind := .traitItem, path, isPub, owner := modName }, ref := nameStx })
  liftTermElabM <| declarePlaceholder selfPath (mkSort (.succ .zero)) true
  record (.item { item := { kind := .typeItem, path := selfPath, isPub := true, owner := path }, ref := nameStx })
  record (.useDef { module := modName, scope := path, target := selfPath, glob := false })
  -- Each member in the trait's scope, without the lints that the trait
  -- reported of its tokens.
  let member (k : CommandElabM Unit) : CommandElabM Unit := inTraitScope path modName k
  -- The methods, each in scope after it, then the laws, then the
  -- expectations, each checked with the laws among its hypotheses
  -- (`Core.traitOrder`).
  let mut laws : Array (Name × Expr × Core.CheckFlags) := #[]
  for i in Core.traitOrder (members.map (traitMemberOf · |>.1)) do
    let m := members[i]!
    let (kind, _, _, _, f?, _) := traitMemberOf m
    match kind with
    | .method =>
      let some f := f? | continue
      let fp := path ++ (declaredIdent f).1.getId
      member (elabCommand m[0])
      if (← getState).table.items.contains fp then
        record (.useDef { module := modName, scope := path, target := fp, glob := false })
    | .law =>
      let out ← inTraitScope path modName do
        try some <$> elabLaw path m
        catch ex => logException ex; pure none
      if let some (n, e, inCore, denied, fmfBound) := out then
        laws := laws.push (n, e, { inCore, denied, fmfBound })
        record (.theoryLaw (path ++ n))
    | _ =>
      let some f := f? | continue
      let ep := path ++ (declaredIdent f).1.getId
      member (elabCommand m[0])
      let st ← getState
      if let some c := st.globals.get? ep then
        -- Its checks are the solver's (`F0215`).
        if let some msg := Core.traitEvidenceMsg? c.tested.any c.enumerated.any then logErrorAt f msg.text
        let uses ← liftTermElabM <| usesOf (c.uses.map (Lean.mkConst ·) ++ laws.map (·.2.1))
        let flags := Core.CheckFlags.withLaws { inCore := c.decidable, denied := c.undecidableDenied, fmfBound := c.guarded }
          (laws.map (·.2.2))
        record (.globalInfo ep { c with laws := laws.map fun (l, e, _) => (l, e), lawsOf := path, uses
                                        decidable := flags.inCore, undecidableDenied := flags.denied
                                        guarded := flags.fmfBound })


end Fren
