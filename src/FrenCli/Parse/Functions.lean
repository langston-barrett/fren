-- keep-sorted start
import FrenCli.Parse.Members
-- keep-sorted end

/-! Parsing function blocks and the local definitions their clauses need. -/

namespace FrenCli

namespace Parser

/-- The names that the tokens within `sp` mention: each identifier's
first segment, without the `!` of shadowing. -/
def mentionsIn (sp : Span) : P (Array String) := do
  let mut out := #[]
  for t in (← get).toks do
    if t.span.start >= sp.stop then break
    if t.span.start < sp.start then continue
    if let .ident s := t.tok then
      let n := unbanged ((s.splitOn ".").headD s)
      unless out.contains n do out := out.push n
  return out

/-- The indices of the local definitions of `defs` that `e` needs
(`Fren.Core.neededDefs`). -/
def neededIn (defs : Array (Ident × Option (Array Ident) × Expr)) (e : Expr) : P (Array Nat) := do
  let mut ms := #[]
  for (_, _, d) in defs do ms := ms.push (← mentionsIn d.span)
  return Fren.Core.neededDefs ((defs.zip ms).map fun ((x, _), m) => (unbanged x.name, m)) id (← mentionsIn e.span)

/-- `e`, with the local definitions of `defs` that it needs, in order, as a
`where` clause around it, its own `where` included: the result's and the
`let`s' of a function's block. Its definitions are written outside it,
which tells it apart from a clause as written, which the lints of `where`
clauses read (`isLowered`). -/
def withDefs (defs : Array (Ident × Option (Array Ident) × Expr)) (e : Expr) : P Expr := do
  let needed ← neededIn defs e
  if needed.isEmpty then return e
  return .«let» e.span (needed.map (defs[·]!)) e true

/-- A function written with a result and a block, after its parameters
(`Reqs/Lang/Items#function-blocks`): `: (r: T) { members }`. It is the
function whose body is its `out` member's expression and whose contract is
its `require`s and `ensure`s, each with the result, `r := f(x)`, and the
`let`s it needs as a `where` clause (`F0442`–`F0445`, `F0165`). -/
def fnBlock (isPub : Bool) (name : Ident) (typeParams : Array Ident)
    (params : Array (Array Ident × Option (Array Ident))) : P Item := do
  discard (expectKw ":")
  openList .parameters
  discard (expectKw "(")
  markStart
  let m ← peek
  if isWord m "set_option" then
    throw { span := m.span, msg := (Fren.Core.fnMemberMsg? .evidence false "set_option").get! }
  if isWord m "det" then
    throw { span := m.span, msg := (Fren.Core.fnMemberMsg? .define true "det").get! }
  let r ← ident
  let ty ← type?
  if (← listComma) && !isKw (← peek) ")" then
    let t ← peek
    throw { span := t.span, msg := Fren.Core.fnResultsMsg }
  closeList
  discard (expectKw ")")
  -- A result `r?` without a type is a `Bool`, as is the function's
  -- value if its name ends in `?` too.
  let result := if ty.isNone && (unbanged r.name).endsWith "?" && !name.name.endsWith "?" then
      some #[{ name := "Bool", span := r.span : Ident }]
    else ty
  openList .members
  discard (expectKw "{")
  let saved := ((← get).fnResult?, (← get).proc?)
  modify fun s => { s with fnResult? := some (unbanged r.name), proc? := none }
  let mut lets : Array (Ident × Option (Array Ident) × Expr) := #[]
  let mut body : Option Expr := none
  let mut clauses : Array (Bool × Ident × Expr) := #[]
  let mut uses : Array Member := #[]
  let mut prev? : Option Member := none
  repeat
    let t ← peek
    if isKw t "}" then break
    if t.tok == .eof then fail t "`}`"
    if prev?.any (!· matches .evidence ..) then memberEnd
    let mem ← member
    prev? := some mem
    let sp := t.span.to (← lastSpan)
    if mem matches .refines .. then
      err sp "F0417" "`refines` is accepted only in global expectation blocks" none #[]
    -- Each member that a function's block does not take (`F0442`,
    -- `F0443`), at its first token, or a `use`'s or an evidence
    -- setting's whole.
    let kind? : Option (Fren.Core.FnMember × Bool × String × Span) := match mem with
      | .use .. | .useGroup .. => some (.use, false, "use", sp)
      | .evidence .. => some (.evidence, false, "set_option", sp)
      | .inst .. => some (.call, false, "call", t.span)
      | .var _ _ det _ _ none => some (.exists, det, "exists", t.span)
      | .var _ _ det _ _ (some _) => some (.let, det, "let", t.span)
      | .prop .expect .. => some (.claim, false, "expect", t.span)
      | .prop .cover .. => some (.claim, false, "cover", t.span)
      | _ => none
    if let some (k, det, kw, at_) := kind? then
      if let some msg := Fren.Core.fnMemberMsg? k det kw then throw { span := at_, msg }
    match mem with
    | .use .. | .useGroup .. => uses := uses.push mem
    | .var _ _ _ x ty (some e) => lets := lets.push (x, ty, e)
    | .define x e =>
      if body.isSome then throw { span := x.span, msg := Fren.Core.resultDefinedTwiceMsg x.name }
      body := some e
    | .prop k x e => clauses := clauses.push (k == .ensure, x, e)
    | _ => pure ()
  closeList
  let close ← bump
  modify fun s => { s with fnResult? := saved.1, proc? := saved.2 }
  let (params, expandedBody) := lambdaMatchFunction params body
  body := expandedBody
  -- The function applied to its parameters, at the result's name.
  let args := params.map fun (p, _) => Expr.path r.span #[{ name := unbanged p[0]!.name, span := r.span }]
  let value := Expr.app r.span #[{ name with span := r.span }] args
  -- With the result's type, if written, which a generic function's
  -- application may need.
  let defs := #[(r, ty, value)] ++ lets
  -- The result is the function's value: neither its body nor its
  -- preconditions mention it (`F0165`), which the elaborator reports at
  -- the first that does.
  let rn := unbanged r.name
  let mentionsResult (e : Expr) : P Bool := do
    let mut all ← mentionsIn e.span
    for i in ← neededIn lets e do all := all ++ (← mentionsIn lets[i]!.2.2.span)
    return all.contains rn
  let mut mention? := none
  let mut clauses' := #[]
  -- And the `let`s that some expression needs, the others unused.
  let mut used : Array Nat := #[]
  for (isEnsure, x, e) in clauses do
    if !isEnsure && mention?.isNone && (← mentionsResult e) then mention? := some (e.span, rn)
    used := used ++ (← neededIn defs e).filterMap fun i => if i == 0 then none else some (i - 1)
    clauses' := clauses'.push (isEnsure, x, ← withDefs defs e)
  let body' ← match body with
    | some e => do
      if mention?.isNone && (← mentionsResult e) then mention? := some (e.span, rn)
      used := used ++ (← neededIn lets e)
      some <$> withDefs lets e
    | none => pure none
  let unusedLets := (lets.mapIdx fun i (x, _, _) => (i, x)).filterMap fun (i, x) => if used.contains i then none else some x
  return .function isPub name typeParams params result body' clauses' close.span
    { uses, unusedLets, resultMention? := mention? }

end Parser

end FrenCli
