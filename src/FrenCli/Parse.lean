-- keep-sorted start
import FrenCli.Lex
import FrenCore.Names
-- keep-sorted end

/-!
# Parser for `.fren` files

The grammar and precedence of `Fren.Lang` (`Reqs/Lang.md`), lowest first:
`when`/`unless`, `iff`, `or`, `and`, `not`, comparisons, `+ -`, `*`, unary `-`;
`if` is an atom whose `else` branch extends as far right as possible.

A file may start with Lean header lines (`import ...`, `open Fren.Lang`),
which are skipped, so pure-spec Lean files can be checked too. Any other Lean
command is an error (`cli::accepts`).
-/

namespace FrenCli

structure Ident where
  name : String
  span : Span
  deriving Inhabited

/-- The pattern of a `match` arm. -/
inductive Pattern where
  /-- `_` -/
  | wild (span : Span)
  /-- `E::V` or `E::V(a, _)`; `_` is a binder named `_`. -/
  | variant (span : Span) (path : Array Ident) (binders : Option (Array Ident))
  /-- `A | B`, or `| A`: each alternative a `variant`. -/
  | or (span : Span) (alts : Array Pattern)
  deriving Inhabited

def Pattern.span : Pattern → Span
  | .wild s | .variant s .. | .or s _ => s

/-- The alternatives of a pattern, none for `_`. -/
def Pattern.alts : Pattern → Array Pattern
  | .wild _ => #[]
  | p@(.variant ..) => #[p]
  | .or _ alts => alts

inductive Expr where
  | when (span : Span) (negated : Bool) (cond body : Expr)
  | ite (span : Span) (cond thenE elseE : Expr)
  | bin (span : Span) (op : String) (lhs rhs : Expr)
  | not (span : Span) (e : Expr)
  | neg (span : Span) (e : Expr)
  | num (span : Span) (digits : String)
  | bool (span : Span) (b : Bool)
  | path (span : Span) (segs : Array Ident)
  /-- `f(a, b)`, a function application, or `E::V(a, b)`, a variant with a
  payload. -/
  | app (span : Span) (fn : Array Ident) (args : Array Expr)
  /-- `R { x := e, y }`, a record literal; a field without `:= e` is `none`. -/
  | record (span : Span) (ty : Array Ident) (fields : Array (Ident × Option Expr))
  /-- `e.x`, for `e` other than a name: a name's fields are part of its
  (dotted) identifier. -/
  | field (span : Span) (e : Expr) (field : Ident)
  | «match» (span : Span) (scrutinee : Expr) (arms : Array (Pattern × Expr))
  /-- A string literal, with its value. -/
  | str (span : Span) (value : String)
  /-- `{a, b}`, a set literal. -/
  | set (span : Span) (elems : Array Expr)
  /-- `(a, b)`, a pair: a member of a relation literal, or the left of `in`. -/
  | pair (span : Span) (fst snd : Expr)
  /-- `[a, b]`, a sequence literal. -/
  | seq (span : Span) (elems : Array Expr)
  /-- `q[i]`, indexing. -/
  | index (span : Span) (seq i : Expr)
  /-- `e.m(a, b)`, a method call with arguments; without them, `e.m` is a
  field read or a path, until its receiver's type is known. -/
  | method (span : Span) (recv : Expr) (name : Ident) (args : Array Expr)
  deriving Inhabited

def Expr.span : Expr → Span
  | .when s .. | .ite s .. | .bin s .. | .not s .. | .neg s .. | .num s .. | .bool s .. | .path s .. | .app s ..
  | .record s .. | .field s .. | .match s .. | .str s .. | .method s .. | .set s .. | .pair s .. | .seq s .. | .index s .. => s

inductive PropKind where
  | assume
  | req
  | expect
  deriving Inhabited, BEq

inductive Member where
  /-- A variable; an output may have a definition, `:= e`. -/
  | var (isIn isPub isDet : Bool) (name : Ident) (ty : Option (Array Ident)) (defn : Option Expr)
  | prop (kind : PropKind) (name : Ident) (e : Expr)
  /-- `inst name: comp { x := e, y }`; a binding without `:= e` is `none`. -/
  | inst (name : Ident) (comp : Array Ident) (bindings : Array (Ident × Option Expr))
  /-- `use a::b` or `use a::E::*`, with the span of the whole member. -/
  | use (span : Span) (path : Array Ident) (glob : Bool)
  /-- `use pre::{a, b::c}`: each path is appended to `pre`. -/
  | useGroup (span : Span) (pre : Array Ident) (paths : Array (Array Ident))
  deriving Inhabited

inductive Item where
  | mod (isPub : Bool) (path : Array Ident)
  /-- `use a::b` or `use a::E::*`, with the span of the whole item. -/
  | use (span : Span) (path : Array Ident) (glob : Bool)
  /-- `use pre::{a, b::c}`: each path is appended to `pre`. -/
  | useGroup (span : Span) (pre : Array Ident) (paths : Array (Array Ident))
  /-- `enum E { A, B(T, U) }`: each variant with its payload's types, if
  it has a payload. -/
  | enum (isPub : Bool) (name : Ident) (variants : Array (Ident × Option (Array (Array Ident))))
  /-- `struct R { x: T, y? }`: each field with its type, if written. -/
  | record (isPub : Bool) (name : Ident) (fields : Array (Ident × Option (Array Ident)))
  /-- `type T`, an abstract type. -/
  | abstractType (isPub : Bool) (name : Ident)
  /-- `fn f(T, U): R`, or `fn f(x: T, y?): R := e`: each parameter's path,
and its type after `:` if written. The result type is `none` if it is not
written, and the body if the function is uninterpreted. -/
  | function (isPub : Bool) (name : Ident) (params : Array (Array Ident × Option (Array Ident)))
      (result : Option (Array Ident)) (body : Option Expr)
  | const (isPub : Bool) (name : Ident) (ty : Array Ident) (value : Expr)
  | comp (isPub : Bool) (name : Ident) (members : Array Member)
  /-- `expect n: forall (a b: c) ..., e`: each binder's names and comp. -/
  | global (name : Ident) (binders : Array (Array Ident × Array Ident)) (body : Expr)
  /-- `tested c: "file", ...` or `trusted c: "why"`, with each string's span. -/
  | claim (tested : Bool) (comp : Array Ident) (texts : Array (String × Span))
  /-- `#fren_check [path]` or `#fren_trace`. -/
  | check (path : Option (Array Ident))
  /-- `set_option fren.lint.NAME "LEVEL" [in item]`, with the span of
  `set_option` to the level, the level's span, and what removing the
  setting removes: up to the item after `in`, if any. -/
  | lintSetting (span : Span) (option : Ident) (value : String) (valueSpan : Span) (removal : Span)
      (body : Option Item)
  deriving Inhabited

structure ParseError where
  span : Span
  msg : Fren.Core.Msg

/-- Lean commands that may not appear in a `.fren` file. -/
def leanCommands : List String :=
  ["impl", "interp", "def", "theorem", "lemma", "example", "abbrev", "instance", "structure", "inductive", "class",
   "namespace", "section", "end", "variable", "set_option", "attribute", "macro", "syntax",
   "notation", "#check", "#eval", "#print", "#guard_msgs"]

/-- What the formatter needs to know of a file's structure, as indices of
tokens. -/
structure Layout where
  /-- Tokens that start an item, a member or an element of a list. -/
  starts : Array Nat := #[]
  /-- `-` as a unary operator. -/
  unary : Array Nat := #[]
  /-- `{` and `::{` that open a list, whose elements are separated by commas. -/
  lists : Array Nat := #[]
  /-- `tested` claims: the `tested` and the last string. -/
  claims : Array (Nat × Nat) := #[]
  /-- `use` items: their first and last tokens. -/
  uses : Array (Nat × Nat) := #[]
  /-- The `(` after a function's name, opening its parameters or arguments. -/
  calls : Array Nat := #[]
  /-- The `{` of a set literal, spaced like `(`. -/
  sets : Array Nat := #[]

structure PState where
  toks : Array Token
  pos : Nat := 0
  layout : Layout := {}
  /-- In a `match`'s scrutinee, where `R {` starts the arms rather than a
  record literal. -/
  noRecord : Bool := false

abbrev P := StateT PState (Except ParseError)

namespace Parser

def peek : P Token := do let s ← get; return s.toks[s.pos]!
def bump : P Token := do
  let t ← peek
  if t.tok != .eof then modify fun s => { s with pos := s.pos + 1 }
  return t
/-- The span of the last token consumed. -/
def lastSpan : P Span := do let s ← get; return s.toks[s.pos - 1]!.span
def range (s : Span) : Fren.Core.Range := { start := s.start, stop := s.stop }

/-- Records that the next token starts an item, a member or an element. -/
def markStart : P Unit := modify fun s => { s with layout.starts := s.layout.starts.push s.pos }
/-- Records that the next token opens a list. -/
def markList : P Unit := modify fun s => { s with layout.lists := s.layout.lists.push s.pos }
/-- Records that the next token is the `(` of a call. -/
def markCall : P Unit := modify fun s => { s with layout.calls := s.layout.calls.push s.pos }

def err (span : Span) (code headline : String) (label? : Option String := none)
    (notes : Array String := #[]) (fixes : Array Fren.Core.Fix := #[]) : P α :=
  throw { span, msg := { code? := some code, headline, label?, notes, fixes } }

/-- `t` where `expected` was. Operators of other languages say what to
write instead. -/
def fail (t : Token) (expected : String) (keywords : Array String := #[]) : P α := do
  match t.tok with
  | .kw op@"==" | .kw op@"&&" | .kw op@"||" | .kw op@"|" | .kw op@"=>" => throw { span := t.span, msg := Fren.Core.foreignOpMsg op }
  | _ => pure ()
  -- At the end of the file, point just after the last token, as rustc does.
  let s ← get
  let span := if t.tok == .eof && s.pos > 0 then
      let prev := s.toks[s.pos - 1]!.span
      { start := prev.stop, stop := prev.stop }
    else t.span
  let fixes := match t.tok with
    | .ident w => (Fren.Core.similarStr w keywords).toArray.map fun k => { msg := s!"a keyword with a similar name exists: `{k}`", replacement := k }
    | _ => #[]
  err span "F0104" s!"expected {expected}, found {t.tok.describe}" (some s!"expected {expected}") (fixes := fixes)

def isKw (t : Token) (s : String) : Bool := t.tok == .kw s
def isWord (t : Token) (s : String) : Bool := t.tok == .ident s

def eatKw (s : String) : P (Option Token) := do
  let t ← peek
  if isKw t s then return some (← bump) else return none

def expectKw (s : String) : P Token := do
  match ← eatKw s with
  | some t => return t
  | none => fail (← peek) s!"`{s}`"

def ident (afterPath := false) : P Ident := do
  let t ← peek
  match t.tok with
  | .ident s =>
    discard bump
    if s.contains '.' then
      let n := (s.splitOn ".").foldl Lean.Name.mkStr .anonymous
      throw { span := t.span, msg := Fren.Core.dottedNameMsg n #[] (inExpr := false) (afterPath := afterPath) }
    return { name := s, span := t.span }
  | _ => fail t "a name"

/-- `a::b::c`; with `allowGlob`, a trailing `::*` is returned as `true`. -/
def path (allowGlob : Bool) : P (Array Ident × Bool) := do
  let mut segs := #[← ident]
  repeat
    if (← eatKw "::").isSome then segs := segs.push (← ident (afterPath := true))
    else if allowGlob then
      if (← eatKw "::*").isSome then return (segs, true)
      break
    else break
  return (segs, false)

/-- The span from `start` to the last token consumed, which includes any
parentheses around the last operand. -/
def spanFrom (start : Span) : P Span := return start.to (← lastSpan)

/-- `l op r`, where `start` is the span of its first token, which may be a
`(` around `l`. -/
def bin (start : Span) (op : String) (l r : Expr) : P Expr := return .bin (← spanFrom start) op l r

/-- Runs `x` where a record literal may appear: within brackets, even in a
`match`'s scrutinee. -/
def withRecords (x : P α) : P α := do
  let saved := (← get).noRecord
  modify fun s => { s with noRecord := false }
  let r ← x
  modify fun s => { s with noRecord := saved }
  return r

/-- `.x` reading a field of `e`, an atom that ends in `)` or `}`; the `.`
touches both. After `.`, `x.y` is one (dotted) identifier. If `(` follows
the last of them, without a space, it is a method call, whose arguments
`args` parses. -/
def fieldReads (args : P (Array Expr)) (index : P Expr) (e : Expr) : P Expr := do
  let mut e := e
  repeat
    let s ← get
    -- `q[i]`: indexing, with no space before `[`.
    if let (some b, some prev) := (s.toks[s.pos]?, s.toks[s.pos - 1]?) then
      if isKw b "[" && prev.span.stop == b.span.start then
        let i ← index
        e := .index (e.span.to (← lastSpan)) e i
        continue
    let some dot := s.toks[s.pos]? | break
    let some next := s.toks[s.pos + 1]? | break
    let some prev := s.toks[s.pos - 1]? | break
    unless isKw dot "." && prev.span.stop == dot.span.start && dot.span.stop == next.span.start do break
    let .ident name := next.tok | break
    discard bump
    discard bump
    let mut start := next.span.start
    let parts := name.splitOn "."
    for f in parts.dropLast do
      let span : Span := { start, stop := start + f.length }
      e := .field (e.span.to span) e { name := f, span }
      start := span.stop + 1
    let last : Ident := { name := parts.getLast!, span := { start, stop := next.span.stop } }
    let s ← get
    if (s.toks[s.pos]?).any fun t => isKw t "(" && t.span.start == next.span.stop then
      let as ← args
      e := .method (e.span.to (← lastSpan)) e last as
    else
      e := .field (e.span.to last.span) e last
  return e

/-- An alternative of a pattern: `E::V` or `E::V(a, _)`. -/
def alternative : P Pattern := do
  let (segs, _) ← path false
  let start := segs[0]!.span
  unless isKw (← peek) "(" do return .variant (start.to segs.back!.span) segs none
  markCall
  discard bump
  let mut bs := #[← ident]
  while (← eatKw ",").isSome do bs := bs.push (← ident)
  discard (expectKw ")")
  return .variant (← spanFrom start) segs (some bs)

/-- A `match` arm's pattern. -/
def pattern : P Pattern := do
  let t ← peek
  if t.tok == .ident "_" then discard bump; return .wild t.span
  -- Each `|` starts its alternative, so that they line up one per line.
  markStart
  let lead ← eatKw "|"
  let first ← alternative
  let mut alts := #[first]
  while isKw (← peek) "|" do
    markStart
    discard bump
    alts := alts.push (← alternative)
  if alts.size == 1 && lead.isNone then return first
  return .or (← spanFrom ((lead.map (·.span)).getD first.span)) alts

mutual
partial def expr : P Expr := do
  let t ← peek
  if isWord t "when" || isWord t "unless" then
    discard bump
    let cond ← iff
    let comma ← peek
    unless isKw comma "," do
      if comma.tok matches .kw "==" | .kw "&&" | .kw "||" | .kw "|" | .kw "=>" then fail comma "`,`"
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
  while (← eatKw "and").isSome do l ← bin start "and" l (← not)
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
  -- of a line, it starts an input.
  if isKw t "in" && !t.nlBefore then return some "in"
  if isKw t "subset" then return some "subset"
  return ["=", "!=", "<", "<=", ">", ">="].find? (isKw t ·)
partial def cmp : P Expr := do
  let start := (← peek).span
  let l ← add
  let some op ← cmpOp? | return l
  discard bump
  let r ← add
  if (← cmpOp?).isSome then
    err (← peek).span "F0108" "comparisons cannot be chained" (some "second comparison")
      #["note: `a < b < c` would compare the `Bool` `a < b` with `c`",
        "help: split it with `and`, e.g. `a < b and b < c`"]
  bin start op l r
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
  discard (expectKw "(")
  let mut args := #[← withRecords expr]
  while (← eatKw ",").isSome do args := args.push (← withRecords expr)
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
partial def atom : P Expr := do
  let t ← peek
  match t.tok with
  | .num d => discard bump; return .num t.span d
  | .str v => discard bump; fieldReads callArgs indexArg (.str t.span v)
  | .ident "true" => discard bump; return .bool t.span true
  | .ident "false" => discard bump; return .bool t.span false
  | .ident kw@"when" | .ident kw@"unless" =>
    err t.span "F0109" s!"`{kw}` must be parenthesized here" (some "needs parentheses")
      #[s!"note: `{kw}` has the lowest precedence, and its body extends as far right as possible",
        s!"help: wrap it in parentheses: `({kw} c, e)`"]
  | .ident s =>
    -- `w.x`, a variable of an instance
    if s.contains '.' then
      let s' ← get
      unless (s'.toks[s'.pos + 1]?).any (isKw · "::") do
        discard bump
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
      markList
      discard bump
      let mut fs := #[]
      repeat
        if isKw (← peek) "}" then break
        markStart
        let f ← ident
        if let some eq ← eatKw "=" then
          err eq.span "F0104" "expected `:=` in a record literal, found `=`" (some "expected `:=`")
            #["note: `=` is equality; a field is given as `x := e`"] #[{ msg := "use `:=`", replacement := ":=" }]
        -- Below `when`, which would swallow the following fields.
        let e ← if (← eatKw ":=").isSome then some <$> withRecords iff else pure none
        fs := fs.push (f, e)
        if (← eatKw ",").isNone then break
      discard (expectKw "}")
      return ← fieldReads callArgs indexArg (.record (← spanFrom start) segs fs)
    unless isKw (← peek) "(" do return ← fieldReads callArgs indexArg (.path (start.to segs.back!.span) segs)
    markCall
    discard bump
    let mut args := #[← withRecords expr]
    while (← eatKw ",").isSome do args := args.push (← withRecords expr)
    discard (expectKw ")")
    fieldReads callArgs indexArg (.app (← spanFrom start) segs args)
  | .kw "match" =>
    discard bump
    let saved := (← get).noRecord
    modify fun s => { s with noRecord := true }
    let scrutinee ← expr
    modify fun s => { s with noRecord := saved }
    markList
    discard (expectKw "{")
    let mut arms := #[]
    repeat
      if isKw (← peek) "}" then break
      markStart
      let p ← pattern
      discard (expectKw "=>")
      -- Below `when`, which would swallow the following arms.
      arms := arms.push (p, ← withRecords iff)
      if (← eatKw ",").isNone then break
    discard (expectKw "}")
    fieldReads callArgs indexArg (.match (← spanFrom t.span) scrutinee arms)
  | .kw "{" =>
    -- A set literal.
    markList
    modify fun s => { s with layout.sets := s.layout.sets.push s.pos }
    discard bump
    let mut es := #[]
    repeat
      if isKw (← peek) "}" then break
      markStart
      es := es.push (← withRecords iff)
      if (← eatKw ",").isNone then break
    discard (expectKw "}")
    fieldReads callArgs indexArg (.set (← spanFrom t.span) es)
  | .kw "[" =>
    -- A sequence literal.
    markList
    discard bump
    let mut es := #[]
    repeat
      if isKw (← peek) "]" then break
      markStart
      es := es.push (← withRecords iff)
      if (← eatKw ",").isNone then break
    discard (expectKw "]")
    fieldReads callArgs indexArg (.seq (← spanFrom t.span) es)
  | .kw "if" =>
    discard bump
    let c ← expr
    discard (expectKw "then")
    let a ← expr
    discard (expectKw "else")
    let b ← expr
    return .ite (← spanFrom t.span) c a b
  | .kw "(" =>
    discard bump
    let e ← withRecords expr
    -- `(a, b)`, a pair.
    if (← eatKw ",").isSome then
      let f ← withRecords expr
      discard (expectKw ")")
      return .pair (← spanFrom t.span) e f
    discard (expectKw ")")
    fieldReads callArgs indexArg e
  | _ => fail t "an expression"
end

/-- The segment that starts `Set(T)` in a type, which no identifier can
be: a type is a path, `Set(` followed by its element type, or `Rel(`
followed by its two element types, separated by `relSep`. -/
def setSeg : String := "Set("

def relSeg : String := "Rel("

def relSep : String := ","

/-- The two element types of the segments of `Rel(A, B)` after `Rel(`: each
`Rel(` within `A` is matched by a separator of its own. -/
def splitRel (segs : Array Ident) : Array Ident × Array Ident := Id.run do
  let mut depth := 0
  for s in segs, i in [0:segs.size] do
    if s.name == relSeg then depth := depth + 1
    else if s.name == relSep then
      if depth == 0 then return (segs.extract 0 i, segs.extract (i + 1))
      depth := depth - 1
  return (segs, #[])

def seqSeg : String := "Seq("

/-- A type: a path, `Set(T)`, `Seq(T)` or `Rel(A, B)`. -/
partial def typeExpr : P (Array Ident) := do
  let t ← peek
  let s ← get
  if t.tok == .ident "Set" && (s.toks[s.pos + 1]?).any (isKw · "(") then
    discard bump
    markCall
    discard bump
    let inner ← typeExpr
    discard (expectKw ")")
    return #[{ name := setSeg, span := t.span }] ++ inner
  if t.tok == .ident "Seq" && (s.toks[s.pos + 1]?).any (isKw · "(") then
    discard bump
    markCall
    discard bump
    let inner ← typeExpr
    discard (expectKw ")")
    return #[{ name := seqSeg, span := t.span }] ++ inner
  if t.tok == .ident "Rel" && (s.toks[s.pos + 1]?).any (isKw · "(") then
    discard bump
    markCall
    discard bump
    let a ← typeExpr
    let c ← expectKw ","
    let b ← typeExpr
    discard (expectKw ")")
    return #[{ name := relSeg, span := t.span }] ++ a ++ #[{ name := relSep, span := c.span }] ++ b
  return (← path false).1

def type? : P (Option (Array Ident)) := do
  if (← eatKw ":").isNone then return none
  return some (← typeExpr)

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

def member : P Member := do
  markStart
  let first := (← get).pos
  if isKw (← peek) "use" then
    let t ← bump
    return match ← useRest t first with
      | (span, segs, glob, none) => .use span segs glob
      | (span, segs, _, some paths) => .useGroup span segs paths
  let pub? ← eatKw "pub"
  let isPub := pub?.isSome
  let t ← peek
  if isKw t "in" then
    discard bump
    if let some p := pub? then
      err p.span "F0110" "inputs cannot be declared `pub`" (some "not allowed on `in`")
        #["note: inputs are always public"]
        #[{ msg := "remove `pub`", replacement := "", range? := some { start := p.span.start, stop := t.span.start } }]
    let x ← ident
    let ty ← type?
    if let some d ← eatKw ":=" then
      throw { span := d.span, msg := Fren.Core.inputDefinitionMsg }
    return .var true true false x ty none
  let det? := if isWord t "det" then some t else none
  let isDet := det?.isSome
  if isDet then discard bump
  let t ← peek
  if isWord t "out" then
    discard bump
    let x ← ident
    let ty ← type?
    let defn ← if (← eatKw ":=").isSome then some <$> expr else pure none
    return .var false isPub isDet x ty defn
  if let some m := det? <|> pub? then
    let mod := if isDet then "det" else "pub"
    let what := if isKw t "in" then "an input"
      else if isWord t "inst" then "an instance"
      else if isWord t "assume" || isWord t "req" || isKw t "expect" then "a constraint"
      else t.tok.describe
    err m.span "F0113" s!"`{mod}` applies only to outputs, not to {what}" (some s!"`{mod}` must be followed by `out`")
      #[if isKw t "in" then s!"note: inputs are always {if isDet then "determined" else "public"}"
        else s!"note: `{mod}` is written `{mod} out x: T`"]
      #[{ msg := s!"remove `{mod}`", replacement := "", range? := some { start := m.span.start, stop := t.span.start } }]
  if isWord t "inst" then
    discard bump
    let x ← ident
    discard (expectKw ":")
    let (comp, _) ← path false
    markList
    discard (expectKw "{")
    let mut bs := #[]
    repeat
      if isKw (← peek) "}" then break
      markStart
      let b ← ident
      if let some eq ← eatKw "=" then
        err eq.span "F0104" "expected `:=` in a binding, found `=`" (some "expected `:=`")
          #["note: `=` is equality; a binding is written `x := e`"] #[{ msg := "use `:=`", replacement := ":=" }]
      -- Below `when`, which would swallow the following bindings.
      let e ← if (← eatKw ":=").isSome then some <$> iff else pure none
      bs := bs.push (b, e)
      if (← eatKw ",").isNone then break
    discard (expectKw "}")
    return .inst x comp bs
  let kind? := if isWord t "assume" then some PropKind.assume
    else if isWord t "req" then some .req
    else if isKw t "expect" then some .expect
    else none
  if isKw t "," then
    err t.span "F0104" "expected a member or `}`, found `,`" (some "unexpected `,`")
      #["note: the members of a component are not separated by commas"] #[{ msg := "remove it", replacement := "" }]
  let some kind := kind?
    | fail t "a member (`in`, `out`, `inst`, `assume`, `req`, `expect` or `use`) or `}`"
        #["in", "out", "pub", "det", "inst", "assume", "req", "expect", "use"]
  discard bump
  let x ← ident
  discard (expectKw ":")
  return .prop kind x (← expr)

partial def item : P Item := do
  markStart
  let first := (← get).pos
  let t ← peek
  if isKw t "#fren_check" then
    discard bump
    if (← peek).tok matches .ident _ then return .check (some (← path false).1)
    return .check none
  -- Reported by `fren trace`.
  if isKw t "#fren_trace" then
    discard bump
    return .check none
  if isWord t "set_option" then
    discard bump
    let o ← peek
    let .ident name := o.tok | fail o "an option name"
    unless name.startsWith "fren.lint." do
      err o.span "F0112" "Lean code is not supported in .fren files" (some "not a lint option")
        #["note: the `fren` command accepts `set_option` only for lints, `fren.lint.NAME`",
          "help: move it to a Lean file that opens `Fren.Lang`, and check it with `lake build`"]
    discard bump
    let v ← peek
    let .str value := v.tok | fail v "a string literal"
    discard bump
    let span := t.span.to v.span
    if (← eatKw "in").isSome then
      let removal := { span with stop := (← peek).span.start }
      return .lintSetting span { name, span := o.span } value v.span removal (some (← item))
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
    discard (expectKw ":")
    let mut binders := #[]
    if (← eatKw "forall").isSome then
      repeat
        discard (expectKw "(")
        let mut names := #[← ident]
        while (← peek).tok matches .ident _ do names := names.push (← ident)
        discard (expectKw ":")
        let (comp, _) ← path false
        discard (expectKw ")")
        binders := binders.push (names, comp)
        if (← eatKw ",").isSome then break
        unless isKw (← peek) "(" do fail (← peek) "`(` or `,`"
    return .global name binders (← expr)
  let isPub := (← eatKw "pub").isSome
  let t ← peek
  if isKw t "mod" then
    discard bump
    return .mod isPub (← path false).1
  if isKw t "enum" then
    discard bump
    let name ← ident
    markList
    discard (expectKw "{")
    let variant : P (Ident × Option (Array (Array Ident))) := do
      markStart
      let v ← ident
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
    return .enum isPub name vs
  if isKw t "struct" then
    discard bump
    let name ← ident
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
    return .record isPub name fs
  if isKw t "type" then
    discard bump
    return .abstractType isPub (← ident)
  if isKw t "fn" then
    discard bump
    let name ← ident
    markCall
    discard (expectKw "(")
    let param : P (Array Ident × Option (Array Ident)) := do
      let p ← typeExpr
      return (p, ← type?)
    let mut params := #[← param]
    while (← eatKw ",").isSome do params := params.push (← param)
    discard (expectKw ")")
    let result ← if (← eatKw ":").isSome then some <$> typeExpr else pure none
    let body ← if (← eatKw ":=").isSome then some <$> expr else pure none
    return .function isPub name params result body
  if isKw t "const" then
    discard bump
    let name ← ident
    discard (expectKw ":")
    let ty ← typeExpr
    discard (expectKw ":=")
    return .const isPub name ty (← expr)
  if isKw t "comp" then
    discard bump
    let name ← ident
    discard (expectKw "{")
    let mut ms := #[]
    repeat
      let t ← peek
      if isKw t "}" then break
      if t.tok == .eof then fail t "`}`"
      ms := ms.push (← member)
    discard bump
    return .comp isPub name ms
  match t.tok with
  | .ident w | .kw w =>
    if leanCommands.contains w then
      err t.span "F0112" "Lean code is not supported in .fren files" (some "Lean, not Fren")
        #["note: only Fren items (`mod`, `use`, `enum`, `struct`, `type`, `fn`, `const`, `comp`, `expect`, `tested`, `trusted`) may appear",
          s!"help: move the `{w}` to a Lean file that opens `Fren.Lang`, and check it with `lake build`"]
  | _ => pure ()
  fail t "an item (`mod`, `use`, `enum`, `struct`, `type`, `fn`, `const`, `comp`, `expect`, `tested` or `trusted`)"
    #["mod", "use", "pub", "enum", "struct", "type", "fn", "const", "comp", "expect", "tested", "trusted"]

/-- Skips `import X` and `open X` lines at the start of the file. -/
def header : P Unit := do
  repeat
    let t ← peek
    if isWord t "import" || isWord t "open" then
      markStart
      discard bump
      let n ← peek
      unless n.tok matches .ident _ do fail n "a module name"
      discard bump
    else break

/-- Parses a file, stopping at the first error. -/
def file : P (Array Item) := do
  header
  let mut items := #[]
  repeat
    if (← peek).tok == .eof then break
    items := items.push (← item)
  return items

end Parser

def parse (toks : Array Token) : Except ParseError (Array Item) :=
  (Parser.file).run' { toks }

/-- The layout of a file that parses. -/
def parseLayout (toks : Array Token) : Except ParseError Layout :=
  (·.2.layout) <$> (Parser.file).run { toks }

end FrenCli
