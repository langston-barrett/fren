-- keep-sorted start
import Fren.Elab.SubsetTypes
-- keep-sorted end

/-! # Hosted elaboration: records -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- How `e` is written, for whether it is written as a sequence
(`Core.WrittenShape`), as the `fren` command's `writtenShape` reads it. -/
partial def writtenShape (e : Syntax) : Core.WrittenShape :=
  if e.getNumArgs == 3 && e[0].isAtom && e[0].getAtomVal == "(" then .parenthesized (writtenShape e[1]) else
  let e := unparen e
  if e.isOfKind ``Lang.seqExpr then .seqLiteral
  else if isMatchLike e then .match ((matchSourceArms e).toList.map (writtenShape ·[3]))
  else if e.isOfKind ``Lang.letExpr then .let (writtenShape e[3])
  else if e.isOfKind ``Lang.tableExpr then .table (e[2].getSepArgs.toList.map (writtenShape ·[3]))
  else match e with
    | `(fren_expr| $a ++ $b) => .concat (writtenShape a) (writtenShape b)
    | `(fren_expr| if $_ then $a else $b) => .conditional (writtenShape a) (writtenShape b)
    | _ => .other

/-- Whether `e` is written as a sequence, so that the right of `in` is
checked against a sequence (`lang::written_sequence`). -/
def seqShaped (e : Syntax) : Bool := (writtenShape e).sequence

/-- Two parts of one type, `a` in `cxa` and `b` in `cxb`, as the `fren`
command's `pair`: one that does not synthesize its type is translated after
the other, if that one does, and expects the other's type, widened unless a
`Nat` is expected here (`lang::checked`). -/
def pairTerms (toTerm : ExprCtx → Syntax → TermElabM Term) (site : Core.ExprSite) (cxa cxb : ExprCtx) (a b : Syntax) :
    TermElabM (Term × Term) := do
  let sibling (cx' : ExprCtx) (t : Term) : TermElabM (Option Core.Ty) := do
    return site.expected cx'.expected? ((← frenTypeOf? t).map (·.widen))
  let (cxa, cxb) := ({ cxa with expected? := site.expected cxa.expected? none }, { cxb with expected? := site.expected cxb.expected? none })
  if !(← synthesizes cxa a) && (← synthesizes cxb b) then
    let y ← toTerm cxb b
    return (← toTerm { cxa with expected? := ← sibling cxa y } a, y)
  let x ← toTerm cxa a
  return (x, ← toTerm { cxb with expected? := ← sibling cxb x } b)

open Lang in
/-- Translates a record literal, where `go` translates its values, given
the type each is expected to have. -/
def recordTerm (go : Option Core.Ty → Syntax → TermElabM Term) (cx : ExprCtx) (expected? : Option Core.Ty) (e : Syntax) :
    TermElabM Term := withRef e do
  let r ← resolveWritten cx.modName (pathSegs e[0]) cx.shadowing cx.noteIndexes
  let .item { kind := .recordItem, path, .. } := r | throwErrorAt e[0] (Core.wrongKindMsg "a record" r).text
  if (← getState).newtypes.contains path then throwErrorAt e[0] (Core.constructionMsg path true).text
  let some info := (← getState).records.get? path | throwError "internal error: unknown record `{path}`"
  let given := e[2].getSepArgs
  match Core.checkFieldInits path (info.fields.map (·.1)) (given.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (some i, msg) => throwErrorAt given[i]![0] msg.text
  | .error (none, msg) => throwError msg.text
  if cx.noteIndexes then lintFieldOrder e path (info.fields.map (·.1)) given
  -- A generic record's type arguments are inferred, as the `fren` command
  -- infers them (`Reqs/Lang/Generics#type-arguments`).
  if let some c ← construction? cx e then
    let vals ← info.fields.mapM fun (f, _) => do
      let some b := given.find? (·[0].getId == f) | throwError "internal error: no field `{f}`"
      if cx.noteIndexes then lintRedundant b true
      if b[1].isNone then return (← `(fren_expr| $(⟨b[0]⟩):ident)).raw else pure b[1][1]
    let note (k : Nat) (t : Core.Ty) := s!"note: `{info.fields[k]!.1}` of `{Core.showPath path}` has type `{t.show}`"
    let (args, targs) ← constructionTerms go cx expected? e c vals (Core.showPath path) note
    -- Each field's obligation, of its type with the record's arguments.
    for v in vals, t in args, k in [0:vals.size] do
      noteObligation cx .field v (partPType info.shape 0 k targs) t
    if cx.noteIndexes then lintStructInit (go none) (.record path targs.toList) e given
    return ← ctorApp info.ctor (← targs.mapM leanTypeOf) args e[0]
  let args ← info.fields.zipIdx.mapM fun ((f, ty), k) => do
    let some b := given.find? (·[0].getId == f) | throwError "internal error: no field `{f}`"
    if cx.noteIndexes then lintRedundant b true
    let v := if b[1].isNone then b[0] else b[1][1]
    let x? ← coreTy? ty
    let t ← if b[1].isNone then go x? (← `(fren_expr| $(⟨b[0]⟩):ident)) else go x? b[1][1]
    checkDeclared v t ty fun tn => s!"note: `{f}` of `{Core.showPath path}` has type `{tn}`"
    noteObligation cx .field v (partPType info.shape 0 k) t
    return t
  if cx.noteIndexes then lintStructInit (go none) (.record path []) e given
  `($(mkCIdentFrom e[0] (recordCtor info.decl)) $args*)

open Lang in
/-- Translates a record update into the record literal whose other fields
are read from the updated value (`Reqs/Lang/Expressions#record-updates`),
where `toTerm` translates its parts. -/
def updateTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (e : Syntax) : TermElabM Term :=
    withRef e <| withFreshMacroScope do
  let rv ← toTerm { cx with emptyOk := Core.ExprSite.updatedRecord.checked false false } e[1]
  let ty ← typeOf rv
  let some info := (← getState).recordOf? ty
    | throwErrorAt e[1] (Core.updateBaseMsg (← typeName ty)).text
  let given := e[3].getSepArgs
  match Core.checkFieldUpdates info.path (info.fields.map (·.1)) (given.map (·[0].getId)) with
  | .ok () => pure ()
  | .error (i, msg) => throwErrorAt given[i]![0] msg.text
  -- A `Nat` is expected of a `Nat` field (`lang::literal_type`).
  let go (x? : Option Core.Ty) := toTerm { cx with emptyOk := Core.ExprSite.recordField.checked false false, expected? := Core.ExprSite.recordField.expected x? none,
                                                   natOk := x? == some .nat }
  -- `r` bound once, so that nested updates grow linearly.
  let bind := info.fields.size > given.size && !rv.raw.isIdent
  let r ← if bind then `(r) else pure rv
  -- With the record's arguments for its type parameters (`lang::instantiation`).
  let targs := ty.getAppArgs
  let cargs := match ← coreTy? ty with
    | some (.record _ as) => as.toArray
    | _ => #[]
  let args ← (info.fieldsAt targs).zipIdx.mapM fun ((f, ty), k) => do
    let some b := given.find? (·[0].getId == f) | `($(mkCIdentFrom e[1] (info.decl ++ f)) $r)
    let v := if b[1].isNone then b[0] else b[1][1]
    let x? ← coreTy? ty
    let t ← if b[1].isNone then go x? (← `(fren_expr| $(⟨b[0]⟩):ident)) else go x? b[1][1]
    checkDeclared v t ty fun tn => s!"note: `{f}` of `{Core.showPath info.path}` has type `{tn}`"
    noteObligation cx .field v (partPType info.shape 0 k cargs) t
    return t
  let lit ← ctorApp info.ctor targs args e
  if bind then `(let r := $rv; $lit) else pure lit


end Fren
