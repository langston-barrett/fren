-- keep-sorted start
import Fren.Elab.Guards
-- keep-sorted end

/-! # Hosted elaboration: paths -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- A path in an expression: a binder, a variable or a constant, with the
fields read from it, or a variant. `toTerm` translates its parts, and
`parent?` is the expression around it. -/
def pathTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (parent? : Option Syntax) (e : Syntax)
    (p : TSyntax ``fren_path) (expected? : Option Core.Ty := none) : TermElabM Term := do
  let segs := pathSegs p
  if h : segs.size = 1 then
    lintChain toTerm cx parent? e
    let id := segs[0]
    let n := id.getId
    -- A binder or variable, then any fields read from it.
    let base? ← if let some b := cx.binder? n.getRoot then do
        if let some sc := b.scrutinee then
          if b.isDef then
            -- A name stands for its definition: its indexes are guarded
            -- here, and what it mentions may be mentioned here, which
            -- translating it again checks, without its lints.
            if cx.noteIndexes then
              let goals ← b.obligations.mapM fun (r, g) => return (r, ← guardedGoal cx.guards g)
              let tables ← b.tableObligations.mapM fun (r, q, g) => return (r, q, ← guardedGoal cx.guards g)
              modifyLocal fun l => { l with indexes := l.indexes ++ goals, tables := l.tables ++ tables }
            let saved ← saveState
            discard (toTerm { cx.at b with noteIndexes := false, pending := #[], emptyOk := true, expected? := b.annot? } sc)
            saved.restore
          else discard (toTerm (cx.at b) sc)
        else if cx.noteIndexes && n.isAtomic then
          modifyLocal fun l => { l with boundMentions := l.boundMentions.push ((id.getPos?, id.getTailPos?), b.outer) }
        pure (some ((b.term, b.type), n.components.drop 1))
      else
        let ks := (List.range n.components.length).reverse.map (· + 1)
        match ks.findSome? fun k => (cx.vars.find? (·.name == (n.components.take k).foldl (· ++ ·) .anonymous)).map (·, k) with
        | some (v, k) =>
          let some t ← varRef? cx id v.name | throwError "internal error: no variable `{v.name}`"
          pure (some ((t, v.type), n.components.drop k))
        | none =>
          -- A constant, then the fields read from its value, or the
          -- methods without arguments applied to it.
          let root := n.getRoot
          if n.isAtomic || cx.insts.contains root then pure none else
          match (← getState).table.resolvePath cx.modName #[root] cx.shadowing with
          | .ok (.item { kind := .constItem, .. }) =>
            -- Resolved again, to record its use and any import it uses.
            let .item { kind := .constItem, path, .. } ← resolvePath cx.modName #[mkIdentFrom id root] cx.shadowing
              | pure none
            let some c := (← getState).consts.get? path | throwError "internal error: unknown constant `{path}`"
            unless cx.unmentioned do noteItemCore path
            let t ← `(($(← exprToSyntax c.value) : $(← exprToSyntax c.type)))
            pure (some ((t, c.type), n.components.drop 1))
          | _ => pure none
    if let some (base, fields) := base? then
      let parts := n.components
      let first := parts.length - fields.length
      return (← fields.zipIdx.foldlM (init := base) fun (t, ty) (f, j) =>
        readPathField cx id parts (first + j) t ty f).1
    if let some (_, own) := cx.pending.find? (·.1 == n.getRoot) then
      throwErrorAt id (Core.definedLaterMsg n.getRoot own).text
    unless n.isAtomic do throwErrorAt segs[0] (Core.dottedNameMsg n cx.insts (cx.vars.filter (·.role != .instHidden) |>.map (·.name))).text
    if let some c := Core.builtinFunction? n then throwError (Core.unappliedMsg (.mkSimple c.name)).text
    -- A function parameter, which is applied (`lang::function_argument`).
    if (cx.fnParam? n).isSome then throwError (Core.unappliedMsg n).text
  match ← resolveWritten cx.modName segs cx.shadowing cx.noteIndexes with
  | .variant en idx =>
    let some info := (← getState).enums.get? en.path | throwError "internal error: unknown enum `{en.path}`"
    let n := (info.payloads[idx]?.map (·.size)).getD 0
    if let some msg := Core.variantMentionMsg? (en.path ++ en.variants[idx]!) n false then throwError msg.text
    if cx.noteIndexes then
      let v := ((e.getPos?, e.getTailPos?), (en.path ++ en.variants[idx]!).toString)
      modifyLocal fun l => { l with variants := l.variants.push v }
      if info.ordered then
        let f := ((e.getPos?, e.getTailPos?), Core.NodeFact.ordinal en.path.toString idx info.variants.size)
        modifyLocal fun l => { l with facts := l.facts.push f }
    -- Of a generic enumeration, with its type arguments, which are inferred
    -- from what is expected (`Reqs/Lang/Generics#type-arguments`).
    if let some c ← construction? cx e then
      let (_, targs) ← constructionTerms (fun _ v => toTerm cx v) cx expected? e c #[]
        (Core.showPath (en.path ++ en.variants[idx]!)) fun _ _ => ""
      return ← ctorApp (info.ctor idx) (info.leanArgs (← targs.mapM leanTypeOf)) #[] e
    return mkCIdentFrom e (info.ctor idx)
  | .item { kind := .constItem, path, .. } =>
    let some c := (← getState).consts.get? path | throwError "internal error: unknown constant `{path}`"
    unless cx.unmentioned do noteItemCore path
    -- Its value's quantifiers are part of the queries
    -- (`Reqs/Lang/Quantifiers#guards`).
    if c.guarded then modifyLocal fun l => { l with guardedUsed := true }
    -- Its value, not its generated definition (see `Fren.Model`).
    `(($(← exprToSyntax c.value) : $(← exprToSyntax c.type)))
  | .item { kind := .fnItem, path, .. } => throwError (Core.unappliedMsg path).text
  | r => throwError (Core.notAValueMsg r).text

/-- `c(args)`, a cardinality operator applied, where `toTerm` translates
the arguments: the number of them that are `true`, compared with 1, as a
linear sum (`lang::cardinality`). -/
def cardinalityTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (c : Core.Cardinality)
    (args : Array Syntax) : TermElabM Term := do
  let mut ites : Array Term := #[]
  for a in args, k in [0:args.size] do
    -- A `Bool` gives `{}` no type, so `{}` is reported as one whose type
    -- cannot be known, as the `fren` command reports it.
    -- `{}` and `[]` are never `Bool`s, in parentheses or not.
    let lit := unparen a
    if (lit.isOfKind ``Lang.setExpr || lit.isOfKind ``Lang.seqExpr) && lit[1].getSepArgs.isEmpty then
      throwErrorAt lit (Core.cardinalityArgMsg c (k + 1) (if lit.isOfKind ``Lang.setExpr then "{}" else "[]")).text
    let t ← toTerm { cx with emptyOk := Core.ExprSite.countArgument.checked false false, natOk := false,
                             expected? := Core.ExprSite.countArgument.expected none none } a
    let ty ← typeOf t
    unless ty.isConstOf ``Bool || ty.isProp do throwErrorAt a (Core.cardinalityArgMsg c (k + 1) (← typeName ty)).text
    ites := ites.push (← `(if $t then (1 : Int) else 0))
  let mut sum := ites[0]!
  for i in ites.extract 1 ites.size do sum ← `($sum + $i)
  match c with
  | .exactlyOne => `($sum = 1)
  | .atMostOne => `($sum ≤ 1)


end Fren
