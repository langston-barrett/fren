-- keep-sorted start
import Fren.Elab.SubsetTypes
-- keep-sorted end

/-! # Hosted elaboration: definitions -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `t` within the `have`s of `binds`, each a local, its type and its
definition, the first outermost. -/
def haves (binds : Array (Ident × Term × Term)) (t : Term) : TermElabM Term :=
  binds.foldrM (fun (x, ty, d) acc => `(have $x : $ty := $d; $acc)) t

/-- The range of `stx` in the characters of `str`, the text it is written
in, as the `fren` command counts it. -/
def charRange (str : String) (stx : Syntax) : Core.Range := charRangeAt str (stx.getPos?, stx.getTailPos?)
where
  /-- The range from `p` to `q`, in characters. -/
  charRangeAt (str : String) : Option String.Pos.Raw × Option String.Pos.Raw → Core.Range
    | (p, q) =>
      let off (p : Option String.Pos.Raw) := (String.Pos.Raw.extract str 0 (p.getD 0)).length
      { start := off p, stop := off q }

/-- The text that `stx` is written in, as characters. -/
def sourceOf (stx : Syntax) : String :=
  match stx.getSubstring? false false with
  | some sub => sub.str
  | none => ""

/-- Records the lints of the `let` or `where` clause `e`, of the
definitions `defs`: its names that neither the body nor a later definition
mentions (`unused_variables`), `let_and_return` and `redundant_locals`
(`lint::let_and_return`, `lint::redundant_locals`), as the `fren` command
reports them. -/
def lintClause (e : Syntax) (defs : Array Syntax) (isWhere : Bool) : TermElabM Unit := do
  let body := e[3]
  let names := defs.map fun d => (declaredIdent d[0]).1.getId
  let used := (Core.clauseMentions names (defs.map (pathMentions ·[3])) (pathMentions body) true).2
  for d in defs, n in names, u in used do
    unless u do recordLint .unusedVariables (declaredIdent d[0]).1 (Core.unusedDefinitionMsg n)
  let fixable := (← getLocal).inMarkdown
  let help (m : Core.Msg) := if fixable && !m.fixes.isEmpty then m.note Core.fixHelp else m
  -- A path, as an expression, is a node around the path.
  let ownName (x : Syntax) (n : Name) : Bool :=
    let x := unparen x
    let x := if x.getNumArgs == 1 then x[0] else x
    x.isOfKind ``Lang.fren_path && (match pathSegs x with | #[y] => y.getId == n | _ => false)
  let bodyIsLast := defs.size > 0 && ownName body names.back!
  let redundant := (defs.zip names).map fun (d, n) =>
    Core.redundantLocal (declaredIdent d[0]).2 (!d[1].isNone) (ownName d[3] n)
  unless (defs.size > 0 && Core.letAndReturn bodyIsLast (!defs.back![1].isNone)) || redundant.contains true do return
  -- The clause's text, from `let`, or from its body to its last definition.
  let str := sourceOf body
  let cs := str.toList.toArray
  let clause : Core.Range := if isWhere then { start := (charRange str body).start, stop := (charRange str defs.back!).stop }
    else charRange str e
  let commented := Core.hasComment (Core.textOf cs clause)
  let ranges := defs.map fun d => ({ start := (charRange str d).start, stop := (charRange str d[3]).stop } : Core.Range)
  if defs.size > 0 && Core.letAndReturn bodyIsLast (!defs.back![1].isNone) then
    let earlier? := if defs.size < 2 then none
      else some (Core.textOf cs { start := ranges[0]!.start, stop := ranges[defs.size - 2]!.stop })
    let fixed := Core.letAndReturnFixed isWhere earlier? (Core.textOf cs (charRange str defs.back![3]))
    recordLint .letAndReturn (unparen body) (help (Core.letAndReturnMsg names.back! isWhere clause fixed commented))
  for d in defs, n in names, r in redundant do
    if r then recordLint .redundantLocals d[0] (Core.redundantLocalMsg n)

open Lang in
/-- Elaborates the definitions `defs` of a `let` (`inLet`) or `where`
clause, from the `k`th, each in the scope of the earlier ones, and runs
`body` in the context of the clause's body, with each name's local, type
and definition (`Reqs/Lang/Let`). Each name is a local while `body` runs,
so that the types of terms that mention it are known. -/
partial def withDefinitions (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (defs : Array Syntax)
    (inLet : Bool) (used : Array Bool) (body : ExprCtx → Array (Ident × Term × Term) → TermElabM α) (k : Nat := 0)
    (binds : Array (Ident × Term × Term) := #[]) : TermElabM α := do
  let some d := defs[k]? | body cx binds
  let locals := Core.bindingLocals (cx.vars.map (fun v => (v.name, v.role)) ++ cx.fnParams.map fun p => (p.1, .input)) cx.insts
    (cx.binders.map (·.what)) cx.selfFn.isSome
  let x ← declare d[0] cx.modName locals
  let n := x.getId
  -- This name and the later ones that hide nothing are not in scope yet.
  let pending := (defs.extract k defs.size).toList.zipIdx.filterMap fun (z, j) =>
    let (y, bang) := declaredIdent z[0]
    if bang then none else some (y.getId, j == 0)
  let pannot? ← if d[1].isNone then pure none else some <$> elabPType cx.modName d[1][1]
  let annot? := pannot?.map (·.1)
  -- Its indexes are guarded where the name is mentioned, and so is its
  -- written type's obligation (`Reqs/Lang/Let#definitions`).
  let before := (← getLocal).indexes
  let beforeTables := (← getLocal).tables
  modifyLocal fun l => { l with indexes := #[], tables := #[] }
  let site := if annot?.isSome then Core.ExprSite.typedDefinition else .untypedDefinition
  -- Its written type is expected of it, as the `fren` command has it.
  let dcx := { cx with guards := #[], pending := pending.toArray, emptyOk := site.checked false false
                       natOk := annot?.any (·.isConstOf ``Nat), unmentioned := cx.unmentioned || !used[k]!
                       expected? := site.expected (pannot?.map (·.2.ty)) none }
  let t ← toTerm dcx d[3]
  if let some (_, pt) := pannot? then noteObligation dcx .letDefinition d[3] pt t
  let obligations := (← getLocal).indexes
  let tableObligations := (← getLocal).tables
  modifyLocal fun l => { l with indexes := before, tables := beforeTables }
  let last := inLet && k + 1 == defs.size
  -- A condition is a `Prop`, and its name a `Bool`, as a variable is.
  let ty ← typeOf t
  let ty := if ty.isProp then Lean.mkConst ``Bool else ty
  -- A `Nat` widens to an `Int`, as anywhere an `Int` is expected.
  let widens := annot?.any (·.isConstOf ``Int) && ty.isConstOf ``Nat
  let ty ← match annot? with
    | some a =>
      unless widens || (← isDefEq a ty) do
        throwErrorAt d[3] (Core.definitionTypeMsg n (← typeName a) (← typeName ty) last).text
      pure a
    | none => pure ty
  let t ← if widens then widenTerm t else pure t
  liftMsg x ((Core.checkVarName n (some (ty.isConstOf ``Bool))).mapError (Core.membershipNote last))
  if cx.noteIndexes then lintName .binder n x
  -- Named apart from every local around it, so that putting a definition's
  -- indexes under the `have`s of its uses captures nothing.
  let lname := Name.mkSimple s!"{Core.nameText n}@{cx.binders.size}"
  let tyStx := typeSyntax (← instantiateMVars ty)
  let b : MatchBinder := { name := n, term := mkIdent lname, «type» := ty, scrutinee := d[3], outer := cx.binders.size,
                           isDef := true, obligations, tableObligations, annot? := pannot?.map (·.2.ty) }
  let value ← `(($t : $tyStx))
  withLocalDeclD lname ty fun _ =>
    withDefinitions toTerm { cx with binders := cx.binders.push b } defs inLet used body (k + 1)
      (binds.push (mkIdent lname, tyStx, value))

open Lang in
/-- `let ds in b`, or `b where ds`, which a `where` clause becomes
(`withWhere`): `b` within a `have` for each definition. -/
def letTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (emptyOk concatOk : Bool) (expected? : Option Core.Ty)
    (e : Syntax) :
    TermElabM Term := withRef e do
  let defs := e[1].getSepArgs
  let inLet := defs.all (·.isOfKind ``Lang.fren_let_def)
  withDefinitions toTerm cx defs inLet (usedDefinitions defs e[3]) fun bcx binds => do
    let mark := (← getLocal).indexes.size
    let tableMark := (← getLocal).tables.size
    -- A body that is a membership right after the `in` may have been meant
    -- as part of the last definition, which `in` ended.
    let b ← tryCatch (toTerm { bcx with emptyOk := Core.ExprSite.letBody.checked emptyOk false, concatOk,
                                         expected? := Core.ExprSite.letBody.expected expected? none } e[3]) fun ex => do
      let .error ref msg := ex | throw ex
      unless inLet && e[3].isOfKind ``Lang.memberExpr do throw ex
      let text ← msg.toString
      throw (.error ref m!"{text}{if (text.splitOn "\n\n").length > 1 then "\n" else "\n\n"}{Core.membershipNoteText}")
    -- Not of what a function's block lowers to, whose `where` is written
    -- nowhere (`Reqs/Lang/Items#function-blocks`).
    let lowered := e[2].getPos?.isNone
    if cx.noteIndexes && !lowered then lintClause e defs !inLet
    -- The indexes of the body, and of the names it mentions, are within the
    -- `have`s.
    let xs := (← getLocal).indexes
    let wrapped ← (xs.extract mark xs.size).mapM fun (r, g) => return (r, ← haves binds g)
    let ts := (← getLocal).tables
    let wrappedTables ← (ts.extract tableMark ts.size).mapM fun (r, q, g) => return (r, q, ← haves binds g)
    modifyLocal fun l => { l with indexes := xs.extract 0 mark ++ wrapped, tables := ts.extract 0 tableMark ++ wrappedTables }
    haves binds b


end Fren
