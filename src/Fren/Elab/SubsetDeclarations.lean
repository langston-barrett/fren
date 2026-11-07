-- keep-sorted start
import Fren.Elab.Procedures
-- keep-sorted end

/-! # Hosted elaboration: subset declarations -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang

open Lang in
/-- Declared subset aliases reuse ordinary predicate functions and the
shared procedure check protocol, with separate declaration-only checks. -/
@[command_elab Lang.subsetTypeCmd] def elabSubsetType : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  checkParsed stx
  let module := (← getLocal).currentModule
  let isPub := !stx[0].isNone
  let nameStx := stx[2]
  let n ← checkItemName "type alias" nameStx
  checkFresh module n nameStx
  let path := module ++ n
  let binder := stx[4]
  discard (segName binder)
  let base : TSyntax `fren_type := ⟨stx[6]⟩
  let (ty, baseType) ← liftTermElabM (elabPType module base)
  -- The pattern shorthand's value, which is not written, is tested
  -- against a pattern; an error about it is at the base type, where the
  -- declaration in full writes its binder, as the `fren` command reports
  -- it (`Reqs/Lang/SubsetTypes#the-pattern-shorthand`).
  let shorthand := Core.nameText binder.getId == Core.shorthandBinder
  if shorthand && patTyOf (← getState) ty == .other then
    throwErrorAt base (Core.isScrutineeMsg (← liftTermElabM (typeName ty)) true).text
  let some (op, members) := booleanBlockView stx[8]
    | throwErrorAt stx[8] "expected a labelled invariant"
  unless op == "and" && !members.isEmpty do throwErrorAt stx[8] "expected a nonempty labelled invariant list"
  let clauses ← members.mapM fun (label, expression) => do
    let some label := label | throwErrorAt expression "every subset invariant must have a label"
    discard (segName label)
    return (label, expression)
  let labels := clauses.map (·.1.getId)
  if let some k := (Core.repeatsAt labels)[0]? then
    throwErrorAt clauses[k]!.1 ({ code? := some "F0372", headline := s!"duplicate invariant `{Core.showPath (path ++ labels[k]!)}`", label? := some "already declared in this subset type" } : Core.Msg).text
  let position := (charRange (← getFileMap).source nameStx).start
  let mut invariants := baseType.invariants
  let mut pattern := baseType.pat?
  let mut previous : Array Syntax := #[]
  let makeProc (name : Syntax) (parameters results : Syntax) (members : Array Syntax) : Syntax :=
    mkNode ``Lang.procCmd #[mkNullNode #[mkAtom "pub"], mkAtom "proc", name, mkAtom "(", parameters,
      mkAtom ")", results, mkAtom "{", mkNullNode members, mkAtom "}"]
  let ghost (command : Syntax) : CommandElabM Unit := do
    let saved ← getLocal
    try
      modifyLocal fun l => { l with inSubset := true }
      elabProc command
    finally
      modifyLocal fun l => { l with inSubset := saved.inSubset, lintReports := saved.lintReports, natReports := saved.natReports }
  for (label, expression) in clauses do
    let predicateName := Name.mkSimple (Core.subsetPredicateName n.toString label.getId.toString position)
    let predicate := mkIdentFrom label predicateName
    let body : TSyntax `fren_expr := ⟨expression⟩
    let parameter : TSyntax `ident := ⟨binder⟩
    let command ← `(pub fn $predicate:ident($parameter:ident : $base) := $body)
    let before ← getLocal
    -- The pattern shorthand's invariant, as written: `is P`, without the
    -- scrutinee that it does not write, which is at the command's start.
    let written := if shorthand then mkNullNode #[expression[1], expression[2]] else expression
    let insideInvariant (ref : Syntax) := match ref.getPos?, ref.getTailPos?, written.getPos?, written.getTailPos? with
      | some start, some stop, some first, some last => first <= start && stop <= last
      | _, _, _, _ => false
    modifyLocal fun l => { l with inSubset := true }
    try
      elabFunctionCore command command
    catch ex =>
      let message ← ex.toMessageData.toString
      if (message.splitOn "cannot find").length > 1 then
        throwErrorAt written ({ code? := some "F0373", headline := "an invariant may mention only its binder, constants and functions", label? := some (Core.invariantScopeLabel (Core.nameText binder.getId)) } : Core.Msg).text
      throw ex
    finally
      -- Only the lints of the invariant's own source are reported, as for
      -- any expression, whether or not it has a static error: not those of
      -- the binder, which the pattern shorthand does not write.
      modifyLocal fun l => { l with
        inSubset := before.inSubset
        lintReports := before.lintReports ++ (l.lintReports.extract before.lintReports.size).filter (insideInvariant ·.ref)
        natReports := before.natReports ++ (l.natReports.extract before.natReports.size).filter (insideInvariant ·.2.2.ref) }
    -- Definedness is checked with earlier conjuncts, never unconditionally
    -- as an ordinary function body or using its own membership as a fact.
    modifyLocal fun l => { l with bodies := before.bodies }
    invariants := invariants.push { name := path ++ label.getId, predicate := module ++ predicateName }
    let value := unparen expression
    if pattern.isNone && clauses.size == 1 && value.isOfKind ``Lang.isExpr && soleName? value[0] == some binder.getId then
      let (matched, bound, _) ← liftTermElabM <| resolveTop { modName := module, vars := #[], insts := #[], place := .prop } ty (mkIdent `x) true value[2]
      if bound.isEmpty then pattern := some matched
    let validator := mkIdentFrom label (Name.mkSimple (Core.subsetCheckName n.toString s!"defined_{label.getId.toString.toLower}" position))
    let param ← `(fren_proc_param| $parameter:ident : $base)
    let assumptions ← previous.mapIdxM fun i e => do
      let earlier := mkIdentFrom label (Name.mkSimple s!"earlier_{i}")
      `(fren_member| assume $earlier:ident : $(⟨e⟩):fren_expr)
    let value := mkIdentFrom label `subset_predicate?
    let definition ← `(fren_member| let $value:ident := $body)
    ghost (makeProc validator (Syntax.mkSep #[param] (mkAtom ",")) mkNullNode (assumptions.map (·.raw) |>.push definition))
    if let some info := (← getState).comps.get? (module ++ validator.getId) then
      record (.compInfo { info with subsetInvariant? := some (path ++ label.getId) })
    previous := previous.push expression
  record (.item { item := { kind := .typeItem, path, isPub, owner := module }, ref := nameStx })
  record (.aliasInfo path ty { baseType with invariants, pat? := pattern, text := n.toString })
  let inhabit := mkIdentFrom nameStx (Name.mkSimple (Core.subsetCheckName n.toString "inhabited" position))
  let binderIdent : TSyntax `ident := ⟨binder⟩
  let result ← `(fren_result| $binderIdent:ident : $base)
  let resultSyntax := mkNullNode #[mkAtom ":", mkAtom "(", Syntax.mkSep #[result] (mkAtom ","), mkAtom ")"]
  let guarantees ← clauses.mapM fun (label, _) => do
    let predicate := mkIdentFrom label (Name.mkSimple (Core.subsetPredicateName n.toString label.getId.toString position))
    let app ← `(fren_expr| $predicate:ident($binderIdent:ident))
    let labelIdent : TSyntax `ident := ⟨label⟩
    `(fren_member| ensure $labelIdent:ident : $app)
  ghost (makeProc inhabit mkNullNode resultSyntax (guarantees.map (·.raw)))
  if let some info := (← getState).comps.get? (module ++ inhabit.getId) then
    record (.compInfo { info with subset? := some path })

open Lang in
/-- `type T = U is P`, elaborated as the declaration it stands for,
`type T = #value: U where pattern: #value is P`, whose binder is generated
(`Core.shorthandBinder`, `Reqs/Lang/SubsetTypes#the-pattern-shorthand`). -/
@[command_elab Lang.subsetShorthandCmd] def elabSubsetShorthand : CommandElab := fun stx => do
  let isTok := stx[5]
  -- The binder has no position. `elabSubsetType` reads the invariant as
  -- written as `is P`, and reports only its lints, as for a written binder.
  let binder := mkIdent (Name.mkSimple Core.shorthandBinder)
  let label := mkIdentFrom isTok `pattern
  let scrutinee ← `(fren_expr| $binder:ident)
  let test := mkNode ``Lang.isExpr #[scrutinee, isTok, stx[6]]
  let invariant := mkNode ``Lang.labelledExpr #[label, mkAtom ":", test]
  elabSubsetType (mkNode ``Lang.subsetTypeCmd
    #[stx[0], stx[1], stx[2], stx[3], binder, mkAtom ":", stx[4], mkAtom "where", invariant])



end Fren
