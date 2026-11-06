-- keep-sorted start
import FrenCli.Parse.Expressions
import FrenCore.Evidence
import FrenCore.FnBlocks
import FrenCore.Global
-- keep-sorted end

/-! Parsing uses, type parameters and block members. -/

namespace FrenCli

namespace Parser

/-- The rest of a `use` whose keyword `t`, at token `first`, was just
read: the path, whether it ends in `::*`, and a group's paths. -/
def useRest (t : Token) (first : Nat) : P (Span × Array Ident × Bool × Option (Array (Array Ident))) := do
  let used : P Unit := modify fun s => { s with layout.uses := s.layout.uses.push (first, s.pos - 1) }
  let (segs, glob) ← path true
  if glob || !isKw (← peek) "::{" then used; return (t.span.to (← lastSpan), segs, glob, none)
  markList
  discard bump
  markStart
  let mut paths := #[(← path false).1]
  while (← eatKw ",").isSome do
    if isKw (← peek) "}" then break
    markStart
    paths := paths.push (← path false).1
  discard (expectKw "}")
  used
  return (t.span.to (← lastSpan), segs, false, some paths)


/-- The type parameters of an enumeration or record named `name`, `<A, B>`,
if any. -/
def typeParams (name : Ident) : P (Array Ident) := do
  let (b, adjacent) ← bracketAfter
  match Fren.Core.afterName b adjacent with
  | .ends => return #[]
  | .spaced => spacedAngle name.name s!"the type parameters of `{name.name}`"
  | .opens => pure ()
  markCall
  discard bump
  let mut ps := #[← ident]
  while (← eatKw ",").isSome do ps := ps.push (← ident)
  discard closeAngle
  return ps

/-- A declared name without the `!` of shadowing. -/
def unbanged (s : String) : String := if s.endsWith "!" then (s.dropEnd 1).toString else s

/-- The text of `src` from `a` to `b`. -/
def srcText (a b : Nat) : P String := return String.ofList (((← get).src).extract a b).toList

/-- A member of a procedure's block. -/
def member : P Member := do
  markStart
  let first := (← get).pos
  if isWord (← peek) "set_option" then
    let t ← bump
    let o ← peek
    let .ident name := o.tok | fail o "an option name"
    unless name == "fren.evidence" do throw { span := o.span, msg := Fren.Core.memberOptionMsg name }
    discard bump
    let v ← peek
    let .str value := v.tok | fail v "a string literal"
    discard bump
    discard (expectKw "in")
    return .evidence (t.span.to v.span) value v.span
  if isKw (← peek) "use" then
    let t ← bump
    return match ← useRest t first with
      | (span, segs, glob, none) => .use span segs glob
      | (span, segs, _, some paths) => .useGroup span segs paths
  let start := (← peek).span
  let pub? ← eatKw "pub"
  let t ← peek
  let det? := if isWord t "det" then some t else none
  let isDet := det?.isSome
  if isDet then discard bump
  let t ← peek
  -- `out r := e` defines the result `r`, of a function's block or of a
  -- procedure's (`F0444`).
  if isWord t "out" && pub?.isNone && !isDet then
    discard bump
    let x ← ident
    discard (expectKw ":=")
    let e ← rightSide top
    if let some rn := (← get).fnResult? then
      if x.name == rn then return .define x e
      throw { span := t.span.to x.span, msg := Fren.Core.fnOutMsg x.name rn }
    let results := ((← get).proc?.map (·.results)).getD #[]
    if results.contains x.name then return .define x e
    -- A global expectation's block has no results: its `out` members are
    -- reported as members that it does not accept (`F0417`).
    if (← get).proc?.any (·.global) then return .define x e
    throw { span := t.span.to x.span, msg := Fren.Core.procOutMsg x.name }
  if (isKw t "exists" || isKw t "let") && pub?.isNone then
    discard bump
    let x ← ident
    let ty ← type?
    let d? ← if isKw t "exists" then pure none else some <$> expectKw ":="
    match d? with
    | none => return .var false false isDet x ty none
    | some _ => return .var false false isDet x ty (some (← rightSide top))
  if let some m := det? <|> pub? then
    let mod := if isDet then "det" else "pub"
    let what := if isWord t "call" then "a call"
      else if isWord t "assume" || isWord t "require" || isWord t "ensure" || isKw t "expect" || isWord t "cover" then "a constraint"
      else if isWord t "out" then "`out`"
      else if isKw t "exists" then "`exists`" else if isKw t "let" then "`let`"
      else t.tok.describe
    let applies := if isDet then "results, `exists` and `let`" else "items"
    err m.span "F0113" s!"`{mod}` applies only to {applies}, not to {what}" (some s!"`{mod}` is not allowed here")
      #[if isDet then "note: `det` is written on a result, `det r: T`, or on `det exists x: T` or `det let x: T := e`"
        else "note: a procedure's public outputs are its results, and its other members are private"]
      #[{ msg := s!"remove `{mod}`", replacement := "", range? := some { start := m.span.start, stop := t.span.start } }]
  if isWord t "refines" then
    discard bump
    let call ← ident
    let (abstract, _) ← path false
    noSpaceBeforeParen abstract.back!.name "refinement arguments"
    markCall
    openList .arguments
    discard (expectKw "(")
    let mut args := #[]
    repeat
      if isKw (← peek) ")" then break
      markStart
      args := args.push (← withRecords expr)
      if !(← listComma) then break
    closeList
    discard (expectKw ")")
    if isWord (← peek) "by" then
      err (← peek).span "F0112" "Lean proofs are supported only in Lean files" none #[]
    return .refines call abstract args (start.to (← lastSpan))
  if isWord t "call" then
    discard bump
    let x ← ident
    discard (expectKw ":=")
    let (comp, _) ← path false
    noSpaceBeforeParen (" :: ".intercalate (comp.map (·.name)).toList) s!"the arguments of `{comp.back!.name}`"
    markCall
    openList .arguments
    discard (expectKw "(")
    let mut args := #[]
    repeat
      if isKw (← peek) ")" then break
      markStart
      let e ← withRecords expr
      args := args.push (({ name := "", span := e.span } : Ident), some e)
      if !(← listComma) then break
    closeList
    discard (expectKw ")")
    return .inst x comp args (start.to (← lastSpan))
  -- A clause about the inputs is written `assume` in a global
  -- expectation's block, and `require` in a procedure's or a function's
  -- (`lang::precondition_word`).
  let global := (← get).proc?.any (·.global)
  let word? : Option Fren.Core.ClauseWord := if isWord t "assume" then some .assume
    else if isWord t "require" then some .require
    else if isWord t "ensure" then some .ensure
    else if isKw t "expect" then some .expect
    else if isWord t "cover" then some .cover
    else none
  let kind? := word?.map fun
    | .require | .assume => PropKind.assume
    | .ensure => .ensure
    | .expect => .expect
    | .cover => .cover
  if isKw t "," then
    err t.span "F0104" "expected a member or `}`, found `,`" (some "unexpected `,`")
      #["note: the members of a procedure are not separated by commas"] #[{ msg := "remove it", replacement := "" }]
  let some kind := kind?
    | let pre := Fren.Core.preconditionKeyword global
      fail t s!"a member (`use`, `{pre}`, `exists`, `let`, `out`, `call`, `ensure`, `expect` or `cover`) or `}`"
        #["use", pre, "exists", "let", "out", "call", "det", "ensure", "expect", "cover"]
  discard bump
  let state ← get
  let clause : P Member := do
    if ((← peek).tok matches .ident _) && (state.toks[state.pos + 1]?).any (isKw · ":") then
      let x ← ident
      discard (expectKw ":")
      return .prop kind x (← top)
    return .prop kind { name := "", span := t.span } (← top)
  -- The clause is part of the item's structure, from which the error of
  -- its keyword is reported once the item is read whole
  -- (`Fren.Core.itemError?`, `lang::item_error`).
  if let some w := word? then
    modify fun s => { s with clauses := s.clauses.push (w, global, t.span) }
  -- The errors of its syntax, the first of them as both front ends report
  -- it (`Fren.Core.firstPartError?`, `lang::part_error`): its own, and,
  -- once it is read, that of how it is written (`Fren.Core.clauseSyntaxError?`,
  -- `lang::clause_errors`), at the keyword.
  let read ← try Except.ok <$> clause catch e => pure (.error e)
  let form? : Option Fren.Core.ClauseForm := match read with
    | .ok (.prop _ x e) => some { labelled := !x.name.isEmpty, blockRoot := e.blockRoot }
    | _ => none
  let own : List (Fren.Core.BlockCheck × ParseError) := match read with
    | .error e => [(.syntax, e)]
    | .ok _ => []
  let written : List (Fren.Core.BlockCheck × ParseError) :=
    ((word?.bind (Fren.Core.clauseSyntaxError? · form?)).map fun msg => (.syntax, { span := t.span, msg })).toList
  if let some e := Fren.Core.firstPartError? (own ++ written) then throw e
  match read with
  | .ok m => return m
  | .error e => throw e

end Parser

end FrenCli
