-- keep-sorted start
import FrenCli.Parse.Functions
import FrenCli.Parse.Procedures
-- keep-sorted end

/-! Parsing top-level items and their mutually recursive trait members. -/

namespace FrenCli

namespace Parser

mutual
/-- An item, or, `inTrait`, a member of a trait after a `set_option ... in`
(`traitMember`). -/
partial def item (inTrait := false) : P Item := do
  markStart
  -- This item's first token. An item is inside another only as the item
  -- that the other's `set_option ... in` ends with; `file` starts the list
  -- anew for each top-level item.
  modify fun s => { s with items := s.items.push s.pos }
  let first := (← get).pos
  let t ← peek
  if isKw t "#fren_check" then
    discard bump
    -- A Lean keyword after it starts the next command in Lean
    -- (`Fren.Lang.checkCmd`).
    if let .ident s := (← peek).tok then
      unless Fren.Core.leanKeywords.contains s do return .check (some (← path false).1)
    return .check none
  -- Reported by `fren trace`.
  if isKw t "#fren_trace" then
    discard bump
    return .check none
  if isWord t "set_option" then
    discard bump
    let o ← peek
    let .ident name := o.tok | fail o "an option name"
    unless name.startsWith "fren.lint." || name == "fren.evidence" || name == "fren.enumeration.size" do
      err o.span "F0112" "Lean code is not supported in .fren files" (some "not a lint option")
        #["note: the `fren` command accepts `set_option` only for lints, `fren.lint.NAME`, `fren.evidence` and \
            `fren.enumeration.size`",
          "help: move it to a Lean file that opens `Fren.Lang`, and check it with `lake build`"]
    discard bump
    let v ← peek
    -- The size bound of enumeration is a number (`Reqs/Check#checking-by-enumeration`).
    let value ← if name == "fren.enumeration.size" then
        match v.tok with
        | .num s _ => pure s
        | _ => fail v "a number"
      else match v.tok with
        | .str value => pure value
        | _ => fail v "a string literal"
    discard bump
    let span := t.span.to v.span
    if (← eatKw "in").isSome then
      let removal := { span with stop := (← peek).span.start }
      return .lintSetting span { name, span := o.span } value v.span removal
        (some (← if inTrait then traitMember else item))
    return .lintSetting span { name, span := o.span } value v.span span none
  if isKw t "tested" || isKw t "trusted" then
    discard bump
    let (comp, _) ← path false
    discard (expectKw ":")
    let mut texts := #[]
    let mut last := first
    repeat
      let s ← peek
      let .str v := s.tok | fail s "a string literal"
      last := (← get).pos
      discard bump
      texts := texts.push (v, s.span)
      if isKw t "trusted" || (← eatKw ",").isNone then break
      -- A trailing comma.
      unless (← peek).tok matches .str _ do break
    if isKw t "tested" then
      modify fun s => { s with layout.claims := s.layout.claims.push (first, last) }
    return .claim (isKw t "tested") comp texts
  if isKw t "use" then
    discard bump
    return match ← useRest t first with
      | (span, segs, glob, none) => .use span segs glob
      | (span, segs, _, some paths) => .useGroup span segs paths
  if isKw t "expect" then
    discard bump
    let name ← ident
    -- Written with parameters and a block (`Reqs/Lang/Global`).
    if isKw (← peek) "(" then
      let (header, ms, close, spans, openStop) ← procRest name (global := true)
      return .globalBlock name header ms close spans openStop
    discard (expectKw ":")
    let bs ← match ← eatKw "forall" with
      | some kw => binders kw
      | none => pure #[]
    return .global name bs (← top)
  let isPub := (← eatKw "pub").isSome
  -- `ordered`, which an enum or a struct takes, after `pub`
  -- (`lang::ordered_declaration`).
  let ordered? ← eatKw "ordered"
  let t ← peek
  if let some o := ordered? then
    unless isKw t "enum" || isKw t "struct" do
      let fix := { msg := "remove `ordered`", replacement := "", range? := some { start := o.span.start, stop := t.span.start } }
      if isKw t "pub" then
        err o.span "F0130" "`ordered` is written after `pub`" (some "before `pub`")
          #["note: an ordered enum or struct is declared `pub ordered enum E { ... }` or `pub ordered struct R { ... }`"]
      let what := match t.tok with
        | .kw "proc" => "procedures" | .kw "type" => "types"
        | .kw "fn" => "functions" | .kw "const" => "constants" | .kw "mod" => "modules"
        | tok => tok.describe
      err o.span "F0130" s!"`ordered` applies only to enums and structs, not to {what}" (some "`ordered` must be followed by `enum` or `struct`")
        #["note: an ordered enum orders its variants as they are declared, and an ordered struct its values by their fields"] #[fix]
  if isKw t "mod" then
    discard bump
    return .mod isPub (← path false).1
  if isKw t "enum" then
    discard bump
    let name ← ident
    let params ← typeParams name
    markList
    discard (expectKw "{")
    let variant : P (Ident × Option (Array (Array Ident))) := do
      markStart
      let v ← ident
      noSpaceBeforeParen v.name s!"the types of `{v.name}`'s payload"
      unless isKw (← peek) "(" do return (v, none)
      markCall
      discard bump
      let mut ts := #[← typeExpr]
      while (← eatKw ",").isSome do ts := ts.push (← typeExpr)
      discard (expectKw ")")
      return (v, some ts)
    let mut vs := #[← variant]
    while (← eatKw ",").isSome do
      if isKw (← peek) "}" then break
      vs := vs.push (← variant)
    discard (expectKw "}")
    return .enum isPub name vs ordered?.isSome params
  if isKw t "struct" then
    discard bump
    let name ← ident
    let params ← typeParams name
    if params.isEmpty then noSpaceBeforeParen name.name s!"the types of `{name.name}`"
    if params.isEmpty && isKw (← peek) "(" then
      -- A newtype: its types, in parentheses.
      markCall
      discard bump
      let mut ts := #[]
      unless isKw (← peek) ")" do
        ts := ts.push (← typeExpr)
        while (← eatKw ",").isSome do ts := ts.push (← typeExpr)
      discard (expectKw ")")
      return .newtype isPub name ts ordered?.isSome
    markList
    discard (expectKw "{")
    let field : P (Ident × Option (Array Ident)) := do
      markStart
      let f ← ident
      return (f, ← type?)
    let mut fs := #[← field]
    while (← eatKw ",").isSome do
      if isKw (← peek) "}" then break
      fs := fs.push (← field)
    discard (expectKw "}")
    return .record isPub name fs ordered?.isSome params
  if isKw t "type" then
    discard bump
    let name ← ident
    if (← eatKw ":=").isSome then return .typeAlias isPub name (← typeExpr)
    if (← eatKw "=").isSome then
      let s ← get
      unless s.toks[s.pos + 1]?.map (·.tok) == some (.kw ":") do
        -- `type T = U is P`, which means `type T = #value: U where pattern:
        -- #value is P`, whose binder is generated (`Fren.Core.shorthandBinder`,
        -- `Reqs/Lang/SubsetTypes#the-pattern-shorthand`).
        let baseStart := (← peek).span
        let base ← typeExpr
        let baseSpan ← spanFrom baseStart
        let isTok ← expectKw "is"
        let p ← pattern (arm := false)
        -- The binder, and the scrutinee that stands for the unwritten
        -- value, are at the base type: outside the invariant, as a written
        -- binder is, and where an error about the value is reported.
        let binder : Ident := { name := Fren.Core.shorthandBinder, span := baseSpan }
        let label : Ident := { name := "pattern", span := isTok.span }
        return .subsetType isPub name binder base #[(label, .is (← spanFrom isTok.span) (.path baseSpan #[binder]) p)]
      let binder ← ident
      discard (expectKw ":")
      let base ← typeExpr
      discard (expectKw "where")
      let invariantStart ← peek
      let labelled ← expr
      let .block _ "and" members := labelled | fail (← peek) "a labelled invariant"
      if members.isEmpty then fail invariantStart "a nonempty labelled invariant list"
      let invariants ← members.mapM fun (label, body) => do
        let some label := label | fail (← peek) "an invariant label"
        pure (label, body)
      return .subsetType isPub name binder base invariants
    return .abstractType isPub name
  if isKw t "fn" then
    discard bump
    let name ← ident
    -- Its type parameters, `<A, B>`, if any (`Reqs/Lang/GenericFunctions`).
    let mut typeParams := #[]
    let (b, adjacent) ← bracketAfter
    match Fren.Core.afterName b adjacent with
    | .spaced => spacedAngle name.name s!"the type parameters of `{name.name}`"
    | .opens =>
      markCall
      discard bump
      let mut ps := #[← typeExpr]
      while (← eatKw ",").isSome do ps := ps.push (← typeExpr)
      discard closeAngle
      for p in ps do
        if p.size != 1 || p[0]!.name.any fun c => !(c.isAlphanum || c == '_' || c == '?' || c == '!') then
          err p[0]!.span "F0152" "a type parameter is a name" (some "not a name")
            #["note: a generic function's type parameters are names, written in angle brackets before its parameters, as in `fn f<T>(x: T): T`"]
        typeParams := typeParams.push p[0]!
    | _ => pure ()
    noSpaceBeforeParen name.name s!"the parameters of `{name.name}`"
    markCall
    openList .functionParameters
    discard (expectKw "(")
    let param : P (Array Ident × Option (Array Ident)) := do
      let p ← typeExpr
      return (p, ← type?)
    let group : P (Array (Array Ident × Option (Array Ident))) := do
      let mut params := #[← param]
      while (← listComma) do params := params.push (← param)
      closeList
      discard (expectKw ")")
      return params
    let params ← group
    -- A named result and a block (`Reqs/Lang/Items#function-blocks`).
    let s ← get
    if (s.toks[s.pos]?).any (isKw · ":") && (s.toks[s.pos + 1]?).any (isKw · "(") then
      return ← fnBlock isPub name typeParams params
    let result ← if (← eatKw ":").isSome then some <$> typeExpr else pure none
    let body ← if (← eatKw ":=").isSome then some <$> rightSide top else pure none
    return .function isPub name typeParams params result body #[] (← lastSpan)
  if isKw t "const" then
    discard bump
    let name ← ident
    discard (expectKw ":")
    let ty ← typeExpr
    discard (expectKw ":=")
    return .const isPub name ty (← rightSide top)
  if isKw t "proc" then
    discard bump
    let name ← ident
    let (header, ms, close, spans, openStop) ← procRest name
    return .comp isPub name header ms close spans openStop
  if isKw t "trait" then
    discard bump
    let name ← ident
    openList .members
    discard (expectKw "{")
    let mut ms := #[]
    repeat
      let m ← peek
      if isKw m "}" then break
      if m.tok == .eof then fail m "`}`"
      unless ms.isEmpty do memberEnd
      ms := ms.push (← traitMember)
    closeList
    let close ← bump
    return .trait isPub name ms close.span
  match t.tok with
  | .ident w | .kw w =>
    if leanCommands.contains w then
      err t.span "F0112" "Lean code is not supported in .fren files" (some "Lean, not Fren")
        #["note: only Fren items (`mod`, `use`, `enum`, `struct`, `type`, `fn`, `const`, `proc`, `trait`, `expect`, `tested`, `trusted`) may appear",
          s!"help: move the `{w}` to a Lean file that opens `Fren.Lang`, and check it with `lake build`"]
  | _ => pure ()
  fail t "an item (`mod`, `use`, `enum`, `struct`, `type`, `fn`, `const`, `proc`, `trait`, `expect`, `tested` or `trusted`)"
    #["mod", "use", "pub", "enum", "struct", "type", "fn", "const", "proc", "trait", "expect", "tested", "trusted"]

/-- A member of a trait (`Reqs/Lang/Traits`): a law, `law n(x: T): e`,
whose `law` is a contextual keyword, or an item, which the elaborator
checks is a method or an expectation. -/
partial def traitMember : P Item := do
  let t ← peek
  unless isWord t "law" && ((← get).toks[(← get).pos + 1]?).any (·.tok matches .ident _) do return ← item (inTrait := true)
  markStart
  discard bump
  let name ← ident
  noSpaceBeforeParen name.name s!"the variables of `{name.name}`"
  markCall
  openList .functionParameters
  discard (expectKw "(")
  let mut params := #[]
  repeat
    if isKw (← peek) ")" then break
    let x ← ident
    params := params.push (x, ← type?)
    if !(← listComma) then break
  closeList
  discard (expectKw ")")
  discard (expectKw ":")
  return .law name params (← top)
end

end Parser

end FrenCli
