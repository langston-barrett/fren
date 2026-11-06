-- keep-sorted start
import FrenCli.Parse.Patterns
import FrenCli.Parse.Types
-- keep-sorted end

/-! Parsing expressions and their mutually recursive forms. -/

namespace FrenCli

namespace Parser

mutual
/-- An expression, whose span the layout records. -/
partial def expr : P Expr := do
  let e ← exprBody
  modify fun st => { st with layout.exprs := st.layout.exprs.push e.span }
  return e
partial def exprBody : P Expr := do
  let t ← peek
  let state ← get
  if (t.tok matches .ident _) && (state.toks[state.pos + 1]?).any (isKw · ":") then
    let mut members := #[]
    repeat
      let label ← ident
      discard (expectKw ":")
      let saved := (← get).stopNamedAnd
      modify fun st => { st with stopNamedAnd := true }
      let value ← expr
      modify fun st => { st with stopNamedAnd := saved }
      members := members.push (some label, value)
      if !(isKw (← peek) "and") then break
      discard bump
    return .block (← spanFrom t.span) "and" members
  if isKw t "let" then
    discard bump
    let defs ← definitions true
    discard (expectKw "in")
    let body ← expr
    return .«let» (← spanFrom t.span) defs body false
  if isKw t "forall" || isKw t "exists" then
    discard bump
    let bs ← binders t
    let body ← expr
    return .quant (← spanFrom t.span) (isKw t "forall") bs body
  if isWord t "when" || isWord t "unless" then
    discard bump
    let cond ← iff
    let comma ← peek
    unless isKw comma "," do
      if comma.tok matches .kw "==" | .kw "&&" | .kw "||" | .kw "|" | .kw "=>" | .kw "<-" then fail comma "`,`"
      let kw := if isWord t "when" then "when" else "unless"
      err comma.span "F0106" s!"expected `,` after the condition of `{kw}`, found {comma.tok.describe}"
        (some "expected `,`") #[s!"note: the condition of `{kw}` ends with a comma"]
        #[{ msg := "add a comma", replacement := ",", after := true, range? := some (range cond.span) }]
    discard bump
    let body ← expr
    return .when (← spanFrom t.span) (isWord t "unless") cond body
  iff

partial def iff : P Expr := do
  let start := (← peek).span
  let l ← or
  if (← eatKw "iff").isNone then return l
  let r ← or
  if let some t ← eatKw "iff" then
    err t.span "F0107" "`iff` is not associative" (some "second `iff`")
      #["help: add parentheses to say which `iff` applies first, e.g. `a iff (b iff c)`"]
  bin start "iff" l r
partial def or : P Expr := do
  let start := (← peek).span
  let mut l ← and
  while (← eatKw "or").isSome do l ← bin start "or" l (← and)
  return l
partial def and : P Expr := do
  let start := (← peek).span
  let mut l ← not
  repeat
    let state ← get
    if state.stopNamedAnd && isKw (← peek) "and" &&
        (state.toks[state.pos + 1]?).any (fun t => t.tok matches .ident _) &&
        (state.toks[state.pos + 2]?).any (isKw · ":") then break
    if (← eatKw "and").isNone then break
    l ← bin start "and" l (← not)
  return l
partial def not : P Expr := do
  let t ← peek
  if isWord t "not" then
    discard bump
    let e ← not
    return .not (← spanFrom t.span) e
  cmp
partial def cmpOp? : P (Option String) := do
  let t ← peek
  -- A membership's `in` is on the line of its left operand; at the start
  -- of a line, it starts an input. In a definition of a `let`, it ends
  -- the definitions.
  if isKw t "in" && !t.nlBefore && !(← get).noIn then return some "in"
  if isKw t "subset" then return some "subset"
  return ["=", "!=", "<", "<=", ">", ">="].find? (isKw t ·)
partial def cmp : P Expr := do
  let start := (← peek).span
  let l ← add
  if let some isTok ← eatKw "is" then
    let p ← pattern (arm := false)
    -- A pattern test takes no guard (`Reqs/Lang/Expressions#pattern-tests`).
    if let some g ← eatKw "if" then
      err g.span "F0140" "a pattern test has no guard" (some "a guard here")
        #["note: a guard belongs to a `match` arm", "help: write `e is P and C`"]
    let e := Expr.is (← spanFrom start) l p
    if (← cmpOp?).isSome || isKw (← peek) "is" then chainedIs isTok
    return e
  let some op ← cmpOp? | return l
  let t ← bump
  let r ← add
  if (← cmpOp?).isNone && !isKw (← peek) "is" then return ← bin start op l r
  -- A chained comparison (`lang::comparison_chain`), checked here, so that
  -- a chain that the grammar does not have does not parse. An `is` ends
  -- it, as an operator that does not chain.
  let mut operands := #[l, r]
  let mut ops := #[(op, t.span)]
  repeat
    if isKw (← peek) "is" then ops := ops.push ("is", (← peek).span); break
    let some op ← cmpOp? | break
    ops := ops.push (op, (← bump).span)
    operands := operands.push (← add)
  if let .error (k, msg) := Fren.Core.checkChain (ops.map (·.1)) then throw { span := ops[k]!.2, msg }
  return .chain (← spanFrom start) operands ops
/-- `is`, at `t`, chained with a comparison or another `is` after it: it
does not chain (`lang::comparison_chain`). -/
partial def chainedIs (t : Token) : P Unit :=
  throw { span := t.span, msg := Fren.Core.chainOtherMsg "is" }
partial def add : P Expr := do
  let start := (← peek).span
  let mut l ← mul
  repeat
    if isKw (← peek) "union" || isKw (← peek) "minus" then
      let op := match (← bump).tok with | .kw w => w | _ => ""
      l ← bin start op l (← mul)
    else if (← eatKw "++").isSome then l ← bin start "++" l (← mul)
    else if (← eatKw "+").isSome then l ← bin start "+" l (← mul)
    else if (← eatKw "-").isSome then l ← bin start "-" l (← mul)
    else break
  return l
partial def mul : P Expr := do
  let start := (← peek).span
  let mut l ← unary
  repeat
    if (← eatKw "*").isSome then l ← bin start "*" l (← unary)
    else if isKw (← peek) "inter" then discard bump; l ← bin start "inter" l (← unary)
    else if isKw (← peek) "join" then discard bump; l ← bin start "join" l (← unary)
    else if isKw (← peek) "div" then discard bump; l ← bin start "div" l (← unary)
    -- A remainder's `mod` is on the line of its left operand; at the start
    -- of a line, it starts a module.
    else if isKw (← peek) "mod" && !(← peek).nlBefore then discard bump; l ← bin start "mod" l (← unary)
    else break
  return l
partial def unary : P Expr := do
  let pos := (← get).pos
  if let some t ← eatKw "-" then
    modify fun s => { s with layout.unary := s.layout.unary.push pos }
    let e ← unary
    return .neg (← spanFrom t.span) e
  atom
/-- `(a, b)`, the arguments of a method call. -/
partial def callArgs : P (Array Expr) := do
  markCall
  openList .applicationArguments
  discard (expectKw "(")
  let mut args := #[← withRecords expr]
  while (← listComma) do args := args.push (← withRecords expr)
  closeList
  discard (expectKw ")")
  return args
/-- `[i]`, the index of an indexing. -/
partial def indexArg : P Expr := do
  -- Spaced like a call's `(`.
  markCall
  discard (expectKw "[")
  let i ← withRecords expr
  discard (expectKw "]")
  return i
/-- The fields of a record literal or update (`what`), up to its `}`: `x
:= e` or `x`, separated by commas. -/
partial def fieldInits (what : String) : P (Array (Ident × Option Expr)) := do
  let mut fs := #[]
  repeat
    if isKw (← peek) "}" then break
    markStart
    let f ← ident
    if let some eq ← eatKw "=" then
      err eq.span "F0104" s!"expected `:=` in {what}, found `=`" (some "expected `:=`")
        #["note: `=` is equality; a field is given as `x := e`"] #[{ msg := "use `:=`", replacement := ":=" }]
    -- Below `when`, which would swallow the following fields.
    let e ← if (← eatKw ":=").isSome then some <$> rightSide (withRecords iff) else pure none
    fs := fs.push (f, e)
    if !(← listComma) then break
  return fs
/-- The scrutinee and arms of `match e { ... }`, or of `table e { ... }`, a
table over a scrutinee (`table`), whose first token is `t`. -/
partial def matchArms (t : Token) (table : Bool) : P Expr := do
  discard bump
  let saved := (← get).noRecord
  modify fun s => { s with noRecord := true }
  -- An atom, as Lean reads it.
  let mut scrutinees := #[]
  unless isKw (← peek) "{" do
    scrutinees := scrutinees.push (← withIn atom)
    while (← eatKw ",").isSome do scrutinees := scrutinees.push (← withIn atom)
  modify fun s => { s with noRecord := saved }
  openList .arms
  discard (expectKw "{")
  let mut arms := #[]
  repeat
    if isKw (← peek) "}" && !(table && arms.isEmpty) then break
    markStart
    let mut ps := #[← pattern]
    while (← eatKw ",").isSome do ps := ps.push (← pattern)
    -- A guard, below `when`, which would swallow the arm's body.
    let guard? ← if (← eatKw "if").isSome then some <$> withRecords iff else pure none
    discard (expectKw "=>")
    -- Below `when`, which would swallow the following arms.
    arms := arms.push (ps, guard?, ← rightSide (withRecords iff))
    if !(← listComma) then break
  closeList
  discard (expectKw "}")
  let span ← spanFrom t.span
  if scrutinees.size == 1 && arms.all (·.1.size == 1) then
    fieldReads callArgs indexArg (.match span scrutinees[0]! (arms.map fun (ps, g, b) => (ps[0]!, g, b)) table)
  else fieldReads callArgs indexArg (.matches span scrutinees arms table)

partial def atom : P Expr := do
  let t ← peek
  let state ← get
  let oneBlock := (t.tok matches .ident "one") && isKw state.toks[state.pos + 1]! "{"
  if isKw t "and" || isKw t "or" || isKw t "iff" || oneBlock then
    let op := if isKw t "and" then "and" else if isKw t "or" then "or" else if oneBlock then "one" else "iff"
    discard bump
    openList .elements
    discard (expectKw "{")
    let mut members := #[]
    unless isKw (← peek) "}" do
      repeat
        markStart
        let st ← get
        let label ← if ((← peek).tok matches .ident _) && (st.toks[st.pos + 1]?).any (isKw · ":") then do
            let name ← ident
            discard (expectKw ":")
            pure (some name)
          else pure none
        if let some label := label then
          if members.any (fun (old, _) => old.any (·.name == label.name)) then
            err label.span "F0372" s!"duplicate Boolean member label `{label.name}`" (some "already used in this block")
        let value ← expr
        members := members.push (label, value)
        if !(← listComma) || isKw (← peek) "}" then break
    closeList
    discard (expectKw "}")
    return .block (← spanFrom t.span) op members
  match t.tok with
  | .num _ v => discard bump; return .num t.span v
  | .str v => discard bump; fieldReads callArgs indexArg (.str t.span v)
  | .ident "true" => discard bump; return .bool t.span true
  | .ident "false" => discard bump; return .bool t.span false
  | .ident kw@"when" | .ident kw@"unless" =>
    err t.span "F0109" s!"`{kw}` must be parenthesized here" (some "needs parentheses")
      #[s!"note: `{kw}` has the lowest precedence, and its body extends as far right as possible",
        s!"help: wrap it in parentheses: `({kw} c, e)`"]
  | .kw "let" =>
    err t.span "F0109" "`let` must be parenthesized here" (some "needs parentheses")
      #["note: `let` has the lowest precedence, and its body extends as far right as possible",
        "help: wrap it in parentheses: `(let x := e in b)`"]
  | .kw kw@"forall" | .kw kw@"exists" =>
    err t.span "F0109" s!"`{kw}` must be parenthesized here" (some "needs parentheses")
      #[s!"note: `{kw}` has the lowest precedence, and its body extends as far right as possible",
        s!"help: wrap it in parentheses: `({kw} (x: T), e)`"]
  | .ident s =>
    -- `w.x`, a variable of a call
    if s.contains '.' then
      let s' ← get
      unless (s'.toks[s'.pos + 1]?).any (isKw · "::") do
        discard bump
        noSpaceBeforeParen s s!"the arguments of `{(s.splitOn ".").getLast!}`"
        -- `x.m(a)`: a method call on `x`, which may itself be dotted.
        if (s'.toks[s'.pos + 1]?).any fun n => isKw n "(" && n.span.start == t.span.stop then
          let parts := s.splitOn "."
          let recvName := ".".intercalate parts.dropLast
          let recvSpan : Span := { start := t.span.start, stop := t.span.start + recvName.length }
          let m : Ident := { name := parts.getLast!, span := { start := recvSpan.stop + 1, stop := t.span.stop } }
          let as ← callArgs
          return ← fieldReads callArgs indexArg (.method (← spanFrom t.span) (.path recvSpan #[{ name := recvName, span := recvSpan }]) m as)
        return ← fieldReads callArgs indexArg (.path t.span #[{ name := s, span := t.span }])
    let (segs, _) ← path false
    let start := segs[0]!.span
    if isKw (← peek) "{" && !(← get).noRecord then
      openList .fields
      discard bump
      let fs ← fieldInits "a record literal"
      closeList
      discard (expectKw "}")
      return ← fieldReads callArgs indexArg (.record (← spanFrom start) segs fs)
    let name := "::".intercalate (segs.map (·.name)).toList
    noSpaceBeforeParen name s!"the arguments of `{name}`"
    unless isKw (← peek) "(" do return ← fieldReads callArgs indexArg (.path (start.to segs.back!.span) segs)
    markCall
    openList .applicationArguments
    discard bump
    -- A cardinality operator without arguments parses, so that the
    -- elaborator reports it (`lang::cardinality_args`).
    if segs.size == 1 && (Fren.Core.Cardinality.ofName? segs[0]!.name).isSome && isKw (← peek) ")" then
      closeList
      discard bump
      return ← fieldReads callArgs indexArg (.app (← spanFrom start) segs #[])
    let mut args := #[← withRecords expr]
    while (← listComma) do args := args.push (← withRecords expr)
    closeList
    discard (expectKw ")")
    fieldReads callArgs indexArg (.app (← spanFrom start) segs args)
  | .kw "table" =>
    -- `{` right after `table` starts the rows of a table by conditions,
    -- and anything else its scrutinee.
    let st ← get
    if !isKw (st.toks[st.pos + 1]?.getD (← peek)) "{" then matchArms t true else
    discard bump
    openList .arms
    discard (expectKw "{")
    let mut rows := #[]
    repeat
      if isKw (← peek) "}" && !rows.isEmpty then break
      markStart
      -- A row does not start with `|` (`F0166`), which would otherwise
      -- open a closure.
      if let some bar ← eatKw "|" then throw { span := bar.span, msg := Fren.Core.rowBarMsg }
      let start := (← peek).span
      -- `_`, which no condition can be, or a condition below `when`, which
      -- would swallow the row's value.
      let cond? ← if (← peek).tok == .ident "_" then discard bump; pure none else some <$> withRecords iff
      discard (expectKw "=>")
      rows := rows.push (start, cond?, ← rightSide (withRecords iff))
      if !(← listComma) then break
    closeList
    discard (expectKw "}")
    fieldReads callArgs indexArg (.table (← spanFrom t.span) rows)
  | .kw "match" => matchArms t false
  | .kw "{" =>
    -- A set literal, or a record update if `with` follows the first
    -- expression.
    openList .elements
    let brace := (← get).pos
    modify fun s => { s with layout.sets := s.layout.sets.push brace }
    discard bump
    let mut es := #[]
    repeat
      if isKw (← peek) "}" then break
      markStart
      es := es.push (← withRecords iff)
      if es.size == 1 && isKw (← peek) "with" then
        -- An update's braces are spaced as a record literal's.
        modify fun s => { s with layout.sets := s.layout.sets.filter (· != brace) }
        updateList
        discard bump
        -- At least one field.
        if isKw (← peek) "}" then fail (← peek) "a name"
        let fs ← fieldInits "a record update"
        closeList
        discard (expectKw "}")
        return ← fieldReads callArgs indexArg (.update (← spanFrom t.span) es[0]! fs)
      if !(← listComma) then break
    closeList
    discard (expectKw "}")
    fieldReads callArgs indexArg (.set (← spanFrom t.span) es)
  | .kw "[" =>
    -- A sequence literal.
    openList .elements
    discard bump
    let mut es := #[]
    repeat
      if isKw (← peek) "]" then break
      markStart
      es := es.push (← withRecords iff)
      if !(← listComma) then break
    closeList
    discard (expectKw "]")
    fieldReads callArgs indexArg (.seq (← spanFrom t.span) es)
  | .kw "if" =>
    discard bump
    -- The condition and `then` branch are delimited, so `in` is a
    -- membership there even in a definition of a `let`.
    let c ← withIn expr
    discard (expectKw "then")
    let a ← withIn expr
    discard (expectKw "else")
    let b ← expr
    let sp ← spanFrom t.span
    modify fun st => { st with layout.exprs := st.layout.exprs.push sp }
    return .ite sp c a b
  | .kw "(" =>
    discard bump
    let e ← withRecords expr
    -- `(a, b)`, a pair.
    if (← eatKw ",").isSome then
      let f ← withRecords expr
      discard (expectKw ")")
      return .pair (← spanFrom t.span) e f
    let close ← expectKw ")"
    -- A field read, method call or index of it starts at its `(`.
    fieldReads callArgs indexArg e (some (t.span.to close.span))
  -- A closure (`Reqs/Lang/HigherOrder#arguments`): where an operand is
  -- expected, `|` opens its parameters, as it is an operator nowhere.
  | .kw "|" =>
    modify fun s => { s with layout.closureOpens := s.layout.closureOpens.push s.pos }
    discard bump
    let mut params := #[]
    repeat
      let x ← peek
      -- `_`, as an identifier, is a parameter that declares no name.
      unless x.tok matches .ident _ do
        if params.isEmpty then closureNoParams x.span
        fail x "a closure's parameter"
      let x ← ident
      -- A type without a pattern, whose `|` would be read as a pattern's.
      let ty ← if (← eatKw ":").isSome then some <$> baseType else pure none
      params := params.push (x, ty)
      if (← eatKw ",").isNone then break
    let close ← peek
    unless isKw close "|" do fail close "`|`"
    modify fun s => { s with layout.closureCloses := s.layout.closureCloses.push s.pos }
    discard bump
    let body ← expr
    return .closure (← spanFrom t.span) params body
  | .kw "||" => closureNoParams t.span
  | _ => fail t "an expression"
/-- `x := e, y: T := f`, the definitions of a `let` (`inLet`), where `in`
outside brackets ends the last, or of a `where` clause. Each is below
`when`, which would swallow the following definitions. -/
partial def definitions (inLet : Bool) : P (Array (Ident × Option (Array Ident) × Expr)) := do
  let mut defs := #[]
  repeat
    let x ← ident
    let ty ← type?
    if let some eq ← eatKw "=" then
      err eq.span "F0104" "expected `:=` in a definition, found `=`" (some "expected `:=`")
        #["note: `=` is equality; a definition is written `x := e`"] #[{ msg := "use `:=`", replacement := ":=" }]
    discard (expectKw ":=")
    let saved := (← get).noIn
    modify fun s => { s with noIn := inLet }
    let e ← rightSide iff
    modify fun s => { s with noIn := saved }
    defs := defs.push (x, ty, e)
    if (← eatKw ",").isNone then break
  return defs
/-- An expression with an optional `where` clause: that of a constraint, a
defined output, a function's body, a constant or a global expectation. -/
partial def top : P Expr := do
  let start := (← peek).span
  let e ← expr
  if (← eatKw "where").isNone then return e
  let defs ← definitions false
  return .«let» (← spanFrom start) defs e true
end

end Parser

end FrenCli
