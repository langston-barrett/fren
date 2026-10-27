-- keep-sorted start
import FrenCli.Lex
import FrenCore.Evidence
import FrenCore.Generics
import FrenCore.Names
import FrenCore.PatternTypes
-- keep-sorted end

/-!
# Parser for `.fren` files

The grammar and precedence of `Fren.Lang` (`Reqs/Lang.md`), lowest first:
`when`/`unless` and the quantifiers `forall`/`exists`, `iff`, `or`, `and`,
`not`, comparisons and `is`, `+ -`, `*`, unary `-`; `if` is an atom whose
`else` branch extends as far right as possible.

A file may start with Lean header lines (`import ...`, `open Fren.Lang`),
which are skipped, so pure-spec Lean files can be checked too. Any other Lean
command is an error (`cli::accepts`).
-/

namespace FrenCli

structure Ident where
  name : String
  span : Span
  deriving Inhabited

/-- A bound of a range pattern: an integer, possibly negated, or a path to
a constant. -/
inductive Bound where
  | num (span : Span) (value : Int)
  | path (span : Span) (segs : Array Ident)
  deriving Inhabited

def Bound.span : Bound → Span
  | .num s _ | .path s _ => s

/-- A pattern (`Reqs/Lang/Patterns`). -/
inductive Pattern where
  /-- `_` -/
  | wild (span : Span)
  /-- `x`, `E::V` or `E::V(p, q)`: a path of one segment, not applied, is a
  binder, `true`, `false`, or a variant, once resolved
  (`lang::pattern_name`). -/
  | variant (span : Span) (path : Array Ident) (args : Option (Array Pattern))
  /-- An integer literal, possibly negated. -/
  | num (span : Span) (value : Int)
  | str (span : Span) (value : String)
  /-- `a..=b`, `a..b`, `a..` or `..=b`. -/
  | range (span : Span) (lo hi : Option Bound) (inclusive : Bool)
  /-- `A | B`, or `| A`. -/
  | or (span : Span) (alts : Array Pattern)
  deriving Inhabited

def Pattern.span : Pattern → Span
  | .wild s | .variant s .. | .num s _ | .str s _ | .range s .. | .or s _ => s

/-- The alternatives of a pattern's own or-pattern, or the pattern itself. -/
def Pattern.alts : Pattern → Array Pattern
  | .or _ alts => alts
  | p => #[p]

/-- The alternatives of the or-patterns of a pattern, in preorder
(`Fren.Core.Pat.alternatives`). -/
partial def Pattern.alternatives : Pattern → Array Pattern
  | .or _ alts => alts.flatMap fun a => #[a] ++ a.alternatives
  | .variant _ _ (some args) => args.flatMap Pattern.alternatives
  | _ => #[]

/-- The identifiers of one segment, not applied, of a pattern, in
preorder: its binders, once those that name variants, `true` and `false`
are told apart. -/
partial def Pattern.names : Pattern → Array Ident
  | .variant _ #[x] none => #[x]
  | .variant _ _ (some args) => args.flatMap Pattern.names
  | .or _ alts => alts.flatMap Pattern.names
  | _ => #[]

/-- A binder of a quantifier or of a global expectation's leading
`forall`, `(x y: T)`: its names, its type, and its span, with its
parentheses. -/
structure Binder where
  names : Array Ident
  ty : Array Ident
  span : Span
  deriving Inhabited

/-! ### Patterns within types

A type is a flat array of segments (`typeExpr`), so a pattern type's
pattern is a segment of its own, whose name holds the pattern written out
by `Pattern.encode`, and which `Pattern.decode` reads back. -/

/-- The atoms of an encoded pattern, each prefixed by its length, so that
any string literal's characters fit. -/
private def atom (s : String) : String := s!"{s.length}:{s}"

private def spanAtoms (sp : Span) : String := atom (toString sp.start) ++ atom (toString sp.stop)

private def segAtoms (segs : Array Ident) : String :=
  atom (toString segs.size) ++ String.join (segs.toList.map fun i => atom i.name ++ spanAtoms i.span)

/-- `p`, written as atoms (`Pattern.decode`). -/
partial def Pattern.encode : Pattern → String
  | .wild sp => atom "w" ++ spanAtoms sp
  | .num sp v => atom "n" ++ spanAtoms sp ++ atom (toString v)
  | .str sp v => atom "s" ++ spanAtoms sp ++ atom v
  | .range sp lo hi inclusive =>
    let bound : Option Bound → String
      | none => atom "-"
      | some (.num bs v) => atom "bn" ++ spanAtoms bs ++ atom (toString v)
      | some (.path bs segs) => atom "bp" ++ spanAtoms bs ++ segAtoms segs
    atom "r" ++ spanAtoms sp ++ atom (if inclusive then "1" else "0") ++ bound lo ++ bound hi
  | .variant sp segs args =>
    atom "v" ++ spanAtoms sp ++ segAtoms segs ++ match args with
      | none => atom "0"
      | some as => atom "1" ++ atom (toString as.size) ++ String.join (as.toList.map Pattern.encode)
  | .or sp alts => atom "o" ++ spanAtoms sp ++ atom (toString alts.size) ++ String.join (alts.toList.map Pattern.encode)

/-- The atoms of `s`, as `atom` writes them. -/
private partial def atomsOf (s : List Char) (acc : Array String := #[]) : Array String :=
  if s.isEmpty then acc else
  let digits := s.takeWhile (·.isDigit)
  let n := (String.ofList digits).toNat!
  let rest := s.drop (digits.length + 1)
  atomsOf (rest.drop n) (acc.push (String.ofList (rest.take n)))

private abbrev D := StateT Nat (Except String)

private def next (as : Array String) : D String := do
  let i ← get
  let some a := as[i]? | throw "a truncated pattern"
  set (i + 1)
  return a

private def nextNat (as : Array String) : D Nat := return (← next as).toNat!

private def nextInt (as : Array String) : D Int := do
  let a ← next as
  return if a.startsWith "-" then -((a.drop 1).toString.toNat! : Int) else (a.toNat! : Int)

private def nextSpan (as : Array String) : D Span := return { start := ← nextNat as, stop := ← nextNat as }

private def nextSegs (as : Array String) : D (Array Ident) := do
  let n ← nextNat as
  (Array.range n).mapM fun _ => do return { name := ← next as, span := ← nextSpan as }

private partial def decodeAt (as : Array String) : D Pattern := do
  match ← next as with
  | "w" => return .wild (← nextSpan as)
  | "n" => return .num (← nextSpan as) (← nextInt as)
  | "s" => return .str (← nextSpan as) (← next as)
  | "r" =>
    let sp ← nextSpan as
    let inclusive := (← next as) == "1"
    let bound : D (Option Bound) := do
      match ← next as with
      | "bn" => return some (.num (← nextSpan as) (← nextInt as))
      | "bp" => return some (.path (← nextSpan as) (← nextSegs as))
      | _ => return none
    let lo ← bound
    let hi ← bound
    return .range sp lo hi inclusive
  | "v" =>
    let sp ← nextSpan as
    let segs ← nextSegs as
    if (← next as) == "0" then return .variant sp segs none
    let n ← nextNat as
    return .variant sp segs (some (← (Array.range n).mapM fun _ => decodeAt as))
  | "o" =>
    let sp ← nextSpan as
    let n ← nextNat as
    return .or sp (← (Array.range n).mapM fun _ => decodeAt as)
  | t => throw s!"an unknown pattern `{t}`"

/-- The pattern that `Pattern.encode` wrote as `s`. -/
def Pattern.decode (s : String) : Except String Pattern := (decodeAt (atomsOf s.toList)).run' 0

/-- The prefix of the name of a pattern type's pattern's segment, which no
identifier can start with: it follows the segments of the base type, or,
for a base type that is a set, relation or sequence, precedes them
(`patOuterSeg`), so that it is never read as an element type's. -/
def patSeg : String := Fren.Core.patSeg

def patOuterSeg : String := Fren.Core.patOuterSeg

/-- The segment of the pattern `p`, after the base type, or before it if
`outer`. -/
def Pattern.seg (p : Pattern) (outer : Bool) : Ident :=
  { name := (if outer then patOuterSeg else patSeg) ++ p.encode, span := p.span }

/-- The type `segs`, split into its base type and its pattern, if it is a
pattern type (`patSeg`). -/
def splitPatternType (segs : Array Ident) : Array Ident × Option Ident :=
  match segs[0]?, segs.back? with
  | some f, some b =>
    if f.name.startsWith patOuterSeg then (segs.extract 1, some f)
    -- A set's, relation's or sequence's last segment is its element type's.
    else if f.name == "Set(" || f.name == "Seq(" || f.name == "Rel(" then (segs, none)
    else if b.name.startsWith patSeg && segs.size > 1 then (segs.pop, some b) else (segs, none)
  | _, _ => (segs, none)

/-- Whether the segment `s` is a pattern type's pattern's. -/
def Ident.isPatternSeg (s : Ident) : Bool := s.name.startsWith patSeg || s.name.startsWith patOuterSeg

/-- The pattern of the segment `seg` that `Pattern.seg` made. -/
def Ident.pattern? (seg : Ident) : Option Pattern :=
  let text := if seg.name.startsWith patOuterSeg then seg.name.drop patOuterSeg.length
    else if seg.name.startsWith patSeg then seg.name.drop patSeg.length else ""
  if text.isEmpty then none else (Pattern.decode text.toString).toOption

inductive Expr where
  | when (span : Span) (negated : Bool) (cond body : Expr)
  | ite (span : Span) (cond thenE elseE : Expr)
  | bin (span : Span) (op : String) (lhs rhs : Expr)
  | not (span : Span) (e : Expr)
  | neg (span : Span) (e : Expr)
  | num (span : Span) (value : Nat)
  | bool (span : Span) (b : Bool)
  | path (span : Span) (segs : Array Ident)
  /-- `f(a, b)`, a function application, or `E::V(a, b)`, a variant with a
  payload. -/
  | app (span : Span) (fn : Array Ident) (args : Array Expr)
  /-- `R { x := e, y }`, a record literal; a field without `:= e` is `none`. -/
  | record (span : Span) (ty : Array Ident) (fields : Array (Ident × Option Expr))
  /-- `{ r with x := e, y }`, a record update; a field without `:= e` is
  `none`. -/
  | update (span : Span) (base : Expr) (fields : Array (Ident × Option Expr))
  /-- `e.x`, for `e` other than a name: a name's fields are part of its
  (dotted) identifier. `x.0` reads the field `0` of a newtype, for any
  `e`: a field named by digits is never part of an identifier. -/
  | field (span : Span) (e : Expr) (field : Ident)
  /-- `match e { P => b, Q if C => c }`: each arm's pattern, its guard, if
  it has one, and its body; or `table e { ... }`, a table over a
  scrutinee (`table`), which means the `match` whose arms are disjoint
  (`Reqs/Lang/Expressions#tables-over-a-scrutinee`). -/
  | «match» (span : Span) (scrutinee : Expr) (arms : Array (Pattern × Option Expr × Expr)) (table : Bool)
  /-- `e is P`, a pattern test. -/
  | is (span : Span) (scrutinee : Expr) (pattern : Pattern)
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
  /-- `a < b <= c`, a chained comparison: at least two operators, each
  with its span, between its operands, one more than its operators, which
  chain (`lang::comparison_chain`), as the parser checks. -/
  | chain (span : Span) (operands : Array Expr) (ops : Array (String × Span))
  /-- `let x := e, y: T := f in body`, or `body where x := e` (`isWhere`),
  which means the same (`Reqs/Lang/Let`): each definition's name, its
  type if written, and its expression. -/
  | «let» (span : Span) (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) (isWhere : Bool)
  /-- `forall (x y: T) (z: U), e`, or `exists` if not `all`, with its
  binders and its body (`Reqs/Lang/Quantifiers`). -/
  | quant (span : Span) (all : Bool) (binders : Array Binder) (body : Expr)
  /-- `table { C => e, ... }`, a condition table: each row's start, its
  condition, `none` for `_`, and its value. -/
  | table (span : Span) (rows : Array (Span × Option Expr × Expr))
  deriving Inhabited

def Expr.span : Expr → Span
  | .when s .. | .ite s .. | .bin s .. | .not s .. | .neg s .. | .num s .. | .bool s .. | .path s .. | .app s ..
  | .record s .. | .update s .. | .field s .. | .match s .. | .is s .. | .str s .. | .method s .. | .set s .. | .pair s ..
  | .seq s .. | .index s .. | .chain s .. | .«let» s .. | .quant s .. | .table s .. => s

/-- The conditions and values of a table's rows, in order. -/
def tableParts (rows : Array (Span × Option Expr × Expr)) : Array Expr :=
  rows.flatMap fun (_, c?, v) => c?.toArray.push v

/-- The guards and bodies of a `match`'s arms, in order. -/
def armParts (arms : Array (Pattern × Option Expr × Expr)) : Array Expr :=
  arms.flatMap fun (_, g?, b) => g?.toArray.push b

inductive PropKind where
  | assume
  | ensure
  | expect
  | cover
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
  /-- `set_option fren.evidence "VALUE" in`, which sets the evidence of the
  next member's checks (`Reqs/Check#checking-by-testing`), with the span of
  `set_option` to the value, and the value's span. -/
  | evidence (span : Span) (value : String) (valueSpan : Span)
  deriving Inhabited

inductive Item where
  | mod (isPub : Bool) (path : Array Ident)
  /-- `use a::b` or `use a::E::*`, with the span of the whole item. -/
  | use (span : Span) (path : Array Ident) (glob : Bool)
  /-- `use pre::{a, b::c}`: each path is appended to `pre`. -/
  | useGroup (span : Span) (pre : Array Ident) (paths : Array (Array Ident))
  /-- `enum E { A, B(T, U) }`: each variant with its payload's types, if
  it has a payload; `ordered enum E { A, B }` if `isOrdered`; with type
  parameters, `enum E<T> { ... }`. -/
  | enum (isPub : Bool) (name : Ident) (variants : Array (Ident × Option (Array (Array Ident)))) (isOrdered : Bool)
      (params : Array Ident)
  /-- `struct R { x: T, y? }`: each field with its type, if written;
  `ordered struct R { ... }` if `isOrdered`; with type parameters,
  `struct R<A, B> { ... }`. -/
  | record (isPub : Bool) (name : Ident) (fields : Array (Ident × Option (Array Ident))) (isOrdered : Bool)
      (params : Array Ident)
  /-- `struct N(T)`: a newtype, with the types in its parentheses, which
  must be one (`lang::newtype`); `ordered struct N(T)` if `isOrdered`. -/
  | newtype (isPub : Bool) (name : Ident) (fields : Array (Array Ident)) (isOrdered : Bool := false)
  /-- `type T`, an abstract type. -/
  | abstractType (isPub : Bool) (name : Ident)
  /-- `type T := U`, a type alias. -/
  | typeAlias (isPub : Bool) (name : Ident) (ty : Array Ident)
  /-- `fn f(T, U): R`, or `fn f(x: T, y?): R := e`, or with type parameters
`fn f<A, B>(x: A): B := e`: each parameter's path,
and its type after `:` if written. The result type is `none` if it is not
written, and the body if the function is uninterpreted. Then the clauses
of its contract: whether each is a postcondition, its name and its
expression. `last` is the span of its last token, such as a `)` around the
body, which `body` leaves out. -/
  | function (isPub : Bool) (name : Ident) (typeParams : Array Ident) (params : Array (Array Ident × Option (Array Ident)))
      (result : Option (Array Ident)) (body : Option Expr) (clauses : Array (Bool × Ident × Expr)) (last : Span)
  | const (isPub : Bool) (name : Ident) (ty : Array Ident) (value : Expr)
  /-- `comp c { members }`, with the span of its closing `}`, the span of each
  member, and where its `{` ends. -/
  | comp (isPub : Bool) (name : Ident) (members : Array Member) (close : Span) (spans : Array Span) (openStop : Nat)
  /-- `expect n: forall (a b: c) ..., e`: each binder names a component or
  a type. -/
  | global (name : Ident) (binders : Array Binder) (body : Expr)
  /-- `refine r: c refines a { bindings }` (`Reqs/Lang/Refinement`). -/
  | refine (name : Ident) (concrete abstract : Array Ident) (bindings : Array (Ident × Option Expr))
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
  /-- The `(` after a function's name, opening its parameters or arguments,
  and the `<` and `>` of type arguments and type parameters. -/
  calls : Array Nat := #[]
  /-- The `{` of a set literal, spaced like `(`. -/
  sets : Array Nat := #[]
  /-- The `..=` and `..` of ranges with a lower bound. -/
  rangeLower : Array Nat := #[]
  /-- The `..=` and `..` of ranges with an upper bound. -/
  rangeUpper : Array Nat := #[]

structure PState where
  toks : Array Token
  pos : Nat := 0
  layout : Layout := {}
  /-- In a `match`'s scrutinee, where `R {` starts the arms rather than a
  record literal. -/
  noRecord : Bool := false
  /-- Where each item starts, in the source. -/
  itemStarts : Array Nat := #[]
  /-- In a definition of a `let`, outside brackets, where `in` ends the
  definitions rather than starting a membership (`Reqs/Lang/Let#parentheses`). -/
  noIn : Bool := false
  /-- Within a type written with its type arguments in parentheses
  (`F0155`): the indices of the tokens of those parentheses, and of those
  of the types within it, which the suggestion writes as `<` and `>`. -/
  parens : Option (Array Nat) := none

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
  | .kw "<-" => throw { span := t.span, msg := Fren.Core.leftArrowMsg }
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
  let notes := if t.tok == .kw "where" then
      #["note: a `where` clause follows the whole expression of a constraint, a cover goal, a definition, a function's body or a constant's value, not a part of one"]
    else #[]
  err span "F0104" s!"expected {expected}, found {t.tok.describe}" (some s!"expected {expected}") notes fixes

def isKw (t : Token) (s : String) : Bool := match t.tok with | .kw k => k == s | _ => false
def isWord (t : Token) (s : String) : Bool := match t.tok with | .ident w => w == s | _ => false

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

/-- Runs `x` within brackets: a record literal may appear, even in a
`match`'s scrutinee, and `in` is a membership, even in a definition of a
`let`. -/
def withRecords (x : P α) : P α := do
  let s0 ← get
  modify fun s => { s with noRecord := false, noIn := false }
  let r ← x
  modify fun s => { s with noRecord := s0.noRecord, noIn := s0.noIn }
  return r

/-- Runs `x` where `in` is a membership, even in a definition of a `let`:
in a delimited part of an `if` or a `match`. -/
def withIn (x : P α) : P α := do
  let saved := (← get).noIn
  modify fun s => { s with noIn := false }
  let r ← x
  modify fun s => { s with noIn := saved }
  return r

/-- If the next token is a `(` after a space, reports it (`F0144`): the
`(` that opens what a name takes follows it directly, as in Lean
(`Reqs/Lang/Lexical#punctuators`). `name` is the name before it, and
`what` what the `(` would open. -/
def noSpaceBeforeParen (name what : String) : P Unit := do
  let s ← get
  let some t := s.toks[s.pos]? | return
  unless isKw t "(" do return
  let some prev := s.toks[s.pos - 1]? | return
  if s.pos == 0 || prev.span.stop == t.span.start then return
  err t.span "F0144" s!"a space before the `(` of {what}" (some "after a space")
    #["note: the `(` that opens what a name takes follows the name directly, as in Lean",
      s!"help: remove the space: `{name}(`"]

/-- The bracket after the last token, and whether it follows it directly
(`Fren.Core.afterName`). -/
def bracketAfter : P (Fren.Core.Bracket × Bool) := do
  let s ← get
  let some t := s.toks[s.pos]? | return (.other, false)
  let b := match t.tok with | .kw p => Fren.Core.Bracket.of p | _ => .other
  let adjacent := s.pos > 0 && (s.toks[s.pos - 1]?).any (·.span.stop == t.span.start)
  return (b, adjacent)

/-- Reports a `<` after a space where it would open what the name `name`
takes, `what` (`F0144`), as `noSpaceBeforeParen` does a `(`. -/
def spacedAngle (name what : String) : P α := do
  err (← peek).span "F0144" s!"a space before the `<` of {what}" (some "after a space")
    #["note: the `<` that opens a type's arguments or a declaration's type parameters follows the name directly",
      s!"help: remove the space: `{name}<`"]

/-- The text of the token `t`, as written. -/
def lexeme (t : Token) : String :=
  match t.tok with
  | .ident s | .num s _ | .kw s => s
  | .str s => s!"\"{s}\""
  | .eof => ""

/-- The `>` that closes type arguments or type parameters, recorded for
the formatter as a call's `)` is. -/
def closeAngle : P Token := do
  markCall
  expectKw ">"

/-- `.x` reading a field of `e`, an atom that ends in `)` or `}`; the `.`
touches both. After `.`, `x.y` is one (dotted) identifier. If `(` follows
the last of them, without a space, it is a method call, whose arguments
`args` parses. -/
def fieldReads (args : P (Array Expr)) (index : P Expr) (e : Expr) (start? : Option Span := none) : P Expr := do
  let mut e := e
  -- Where the expression starts: before the parentheses of `(e).f`.
  let mut first := start?.getD e.span
  repeat
    let s ← get
    -- `q[i]`: indexing, with no space before `[`.
    if let (some b, some prev) := (s.toks[s.pos]?, s.toks[s.pos - 1]?) then
      if isKw b "[" && prev.span.stop == b.span.start then
        let i ← index
        e := .index (first.to (← lastSpan)) e i
        first := e.span
        continue
    let some dot := s.toks[s.pos]? | break
    let some next := s.toks[s.pos + 1]? | break
    let some prev := s.toks[s.pos - 1]? | break
    unless isKw dot "." && prev.span.stop == dot.span.start && dot.span.stop == next.span.start do break
    -- `x.0`, a field named by decimal digits: of a newtype, which the
    -- elaborator checks. It is read as Lean reads a field index, so a
    -- number of another base, or with `_`, does not parse.
    if let .num digits _ := next.tok then
      unless digits.all Char.isDigit do fail next "a field"
      discard bump
      discard bump
      e := .field (first.to next.span) e { name := digits, span := next.span }
      first := e.span
      continue
    let .ident name := next.tok | break
    discard bump
    discard bump
    let mut start := next.span.start
    let parts := name.splitOn "."
    for f in parts.dropLast do
      let span : Span := { start, stop := start + f.length }
      e := .field (first.to span) e { name := f, span }
      first := e.span
      start := span.stop + 1
    let last : Ident := { name := parts.getLast!, span := { start, stop := next.span.stop } }
    noSpaceBeforeParen last.name s!"the arguments of `{last.name}`"
    let s ← get
    if (s.toks[s.pos]?).any fun t => isKw t "(" && t.span.start == next.span.stop then
      let as ← args
      e := .method (first.to (← lastSpan)) e last as
      first := e.span
    else
      e := .field (first.to last.span) e last
      first := e.span
  return e

/-- Records that the next token is a unary `-`. -/
def markUnary : P Unit := modify fun s => { s with layout.unary := s.layout.unary.push s.pos }

/-- Whether the next token touches the last one consumed. -/
def touching : P Bool := do
  let s ← get
  return match s.toks[s.pos]?, s.toks[s.pos - 1]? with
    | some t, some prev => prev.span.stop == t.span.start
    | _, _ => false

/-- Whether `t` can start a bound of a range. -/
def boundStart (t : Token) : Bool := t.tok matches .num .. | .ident _ | .kw "-"

/-- The bound of a range: `["-"] INT`, or a path. -/
def bound : P Bound := do
  let t ← peek
  match t.tok with
  | .kw "-" =>
    markUnary
    discard bump
    let n ← peek
    let .num _ v := n.tok | fail n "an integer"
    discard bump
    return .num (t.span.to n.span) (-(v : Int))
  | .num _ v => discard bump; return .num t.span v
  | .ident _ =>
    let (segs, _) ← path false
    return .path (segs[0]!.span.to segs.back!.span) segs
  | _ => fail t "a bound of a range"

/-- Spaces around the `..=` or `..` of a range (`F0128`). -/
def rangeSpaceErr (op : Token) : P α :=
  err op.span "F0128" s!"spaces around `{if isKw op "..=" then "..=" else ".."}` in a range pattern"
    (some "spaced") #["note: a range is written without spaces around its `..=` or `..`, as in `0..=9`"]

/-- The rest of a range after its lower bound `lo?`, at its `..=` or
`..`: its upper bound, if any. `..=` needs one, and `..` with no lower
bound is not a range (`F0129`). -/
def rangeRest (start : Span) (lo? : Option Bound) : P Pattern := do
  let at_ := (← get).pos
  if lo?.isSome then modify fun s => { s with layout.rangeLower := s.layout.rangeLower.push at_ }
  let op ← bump
  let inclusive := isKw op "..="
  let next ← peek
  -- An upper bound touches the operator, as Lean's parser reads it: what
  -- follows a space is not part of the range. After `..=`, a spaced bound
  -- is reported as such.
  let upper := boundStart next && (← touching)
  if inclusive && !upper && boundStart next && !next.nlBefore then rangeSpaceErr op
  if upper then modify fun s => { s with layout.rangeUpper := s.layout.rangeUpper.push at_ }
  let hi? ← if upper then some <$> bound else pure none
  if inclusive && hi?.isNone then
    err op.span "F0129" "an inclusive range needs an upper bound" (some "no upper bound")
      #["note: the ranges are `a..=b`, `a..b`, `a..` and `..=b`"]
  if !inclusive && lo?.isNone then
    err op.span "F0129" "a range with `..` needs a lower bound" (some "no lower bound")
      #["note: the ranges are `a..=b`, `a..b`, `a..` and `..=b`", "help: for the integers below `b`, write `..=` and the integer before `b`"]
  return .range (← spanFrom start) lo? hi? inclusive

/-- After the lower bound `lo` of a pattern, a range if `..=` or `..`
follows, touching it. -/
def maybeRange (lo : Bound) (otherwise : Pattern) : P Pattern := do
  let t ← peek
  unless isKw t "..=" || isKw t ".." do return otherwise
  unless ← touching do rangeSpaceErr t
  rangeRest lo.span (some lo)

mutual
/-- An alternative of an or-pattern, or a pattern of a payload: `_`, a
binder or variant, a literal, or a range. -/
partial def primaryPattern : P Pattern := do
  let t ← peek
  match t.tok with
  | .ident "_" => discard bump; return .wild t.span
  | .str v => discard bump; return .str t.span v
  | .num .. | .kw "-" =>
    let b ← bound
    let .num sp v := b | fail t "a pattern"
    maybeRange b (.num sp v)
  | .kw "..=" => rangeRest t.span none
  | .kw ".." => rangeRest t.span none
  | .ident _ =>
    let (segs, _) ← path false
    let start := segs[0]!.span
    let pathSpan := start.to segs.back!.span
    let name := "::".intercalate (segs.map (·.name)).toList
    noSpaceBeforeParen name s!"the binders of `{name}`"
    let next ← peek
    if isKw next "(" && (← touching) then
      markCall
      discard bump
      let mut args := #[← orPattern]
      while (← eatKw ",").isSome do args := args.push (← orPattern)
      discard (expectKw ")")
      return .variant (← spanFrom start) segs (some args)
    maybeRange (.path pathSpan segs) (.variant pathSpan segs none)
  | _ => fail t "a pattern"

/-- `A | B`, an or-pattern, or one pattern. -/
partial def orPattern : P Pattern := do
  let first ← primaryPattern
  let mut alts := #[first]
  while isKw (← peek) "|" do
    discard bump
    alts := alts.push (← primaryPattern)
  if alts.size == 1 then return first
  return .or (← spanFrom first.span) alts
end

/-- A pattern, of a `match` arm or of `is`. In an arm (`arm`), each `|`
starts its alternative, so that they line up one per line; after `is`, a
line that starts with `|` continues the expression. -/
def pattern (arm := true) : P Pattern := do
  if arm then markStart
  let lead ← eatKw "|"
  let first ← primaryPattern
  let mut alts := #[first]
  while isKw (← peek) "|" do
    if arm then markStart
    discard bump
    alts := alts.push (← primaryPattern)
  if alts.size == 1 && lead.isNone then return first
  return .or (← spanFrom ((lead.map (·.span)).getD first.span)) alts

/-- The segment that starts `Set<T>` in a type, which no identifier can
be: a type's segments are a path, `setSeg` followed by its element
type's, or `relSeg` followed by its two element types', separated by
`relSep`. -/
def setSeg : String := Fren.Core.setSeg

def relSeg : String := Fren.Core.relSeg

def relSep : String := Fren.Core.relSep

/-- The two element types of the segments of `Rel<A, B>` after `relSeg`:
each `relSeg` within `A` is matched by a separator of its own. -/
def splitRel (segs : Array Ident) : Array Ident × Array Ident := Id.run do
  let mut depth := 0
  for s in segs, i in [0:segs.size] do
    if s.name == relSeg then depth := depth + 1
    else if s.name == relSep then
      if depth == 0 then return (segs.extract 0 i, segs.extract (i + 1))
      depth := depth - 1
  return (segs, #[])

def seqSeg : String := Fren.Core.seqSeg

/-- The segments around and between the type arguments of an instance of a
generic type, `G<A, B>`, written as `G`'s path, `argsOpen`, `A`, `argsSep`,
`B` and `argsClose`, none of which an identifier can be. `argsSep` is not
`relSep`, so that `splitRel` never splits at it. -/
def argsOpen : String := Fren.Core.argsOpen

def argsSep : String := Fren.Core.argsSep

def argsClose : String := Fren.Core.argsClose

/-- The type arguments within the segments between `argsOpen` and
`argsClose`, split at each `argsSep` that is not within another instance's
arguments. -/
def splitArgs (segs : Array Ident) : Array (Array Ident) := Id.run do
  let mut out := #[]
  let mut cur := #[]
  let mut depth := 0
  for s in segs do
    if s.name == argsOpen then depth := depth + 1
    else if s.name == argsClose then depth := depth - 1
    else if s.name == argsSep && depth == 0 then
      out := out.push cur
      cur := #[]
      continue
    cur := cur.push s
  return if cur.isEmpty && out.isEmpty then #[] else out.push cur

mutual
/-- A type: a path, `Set<T>`, `Seq<T>`, `Rel<A, B>`, or an instance of a
generic type, `G<A, B>`, optionally followed by `is` and a pattern, for a
pattern type. -/
partial def typeExpr : P (Array Ident) := do
  let base ← baseType
  unless isKw (← peek) "is" do return base
  discard bump
  let p ← pattern (arm := false)
  if let some t ← eatKw "is" then throw { span := t.span, msg := Fren.Core.nestedPatternMsg }
  let outer := base[0]?.any fun s => s.name == setSeg || s.name == seqSeg || s.name == relSeg
  return if outer then #[p.seg true] ++ base else base.push (p.seg false)

/-- A type without a pattern of its own: a path, `Set<T>`, `Seq<T>`,
`Rel<A, B>` or an instance of a generic type, `G<A, B>`, whose element
types and type arguments may be pattern types. -/
partial def baseType : P (Array Ident) := do
  let t ← peek
  let start := (← get).pos
  let p := (← path false).1
  let pathName := "::".intercalate (p.map (·.name)).toList
  let (b, adjacent) ← bracketAfter
  match Fren.Core.afterName b adjacent with
  | .ends => return p
  | .spaced =>
    let what := match pathName with
      | "Set" | "Seq" => s!"`{pathName}`'s element type"
      | "Rel" => "`Rel`'s element types"
      | _ => s!"the type arguments of `{pathName}`"
    spacedAngle pathName what
  | .parenthesized => return ← parenArgs start p
  | .opens => pure ()
  markCall
  let o ← bump
  let builtin := p.size == 1 && (pathName == "Set" || pathName == "Seq" || pathName == "Rel")
  if builtin then
    if pathName == "Rel" then
      let a ← typeExpr
      let c ← expectKw ","
      let b ← typeExpr
      discard closeAngle
      return #[{ name := relSeg, span := t.span }] ++ a ++ #[{ name := relSep, span := c.span }] ++ b
    let inner ← typeExpr
    discard closeAngle
    return #[{ name := if pathName == "Set" then setSeg else seqSeg, span := t.span }] ++ inner
  let mut out := p ++ #[{ name := argsOpen, span := o.span }] ++ (← typeExpr)
  while isKw (← peek) "," do
    let c ← bump
    out := out ++ #[{ name := argsSep, span := c.span }] ++ (← typeExpr)
  let close ← closeAngle
  return out.push { name := argsClose, span := close.span }

/-- A type written with its type arguments in parentheses, `G(A, B)`, as
types were before they were written in angle brackets: read as if it were
`G<A, B>`, so that the error (`F0155`) suggests the whole type, with the
parentheses of each type within it that is written so too. `start` is the
index of its first token, and `p` its path. -/
partial def parenArgs (start : Nat) (p : Array Ident) : P (Array Ident) := do
  let outer := (← get).parens.isNone
  if outer then modify fun s => { s with parens := some #[] }
  let openAt := (← get).pos
  discard bump
  discard typeExpr
  while (← eatKw ",").isSome do discard typeExpr
  let close ← expectKw ")"
  let closeAt := (← get).pos - 1
  modify fun s => { s with parens := s.parens.map (·.push openAt |>.push closeAt) }
  unless outer do return p
  let s ← get
  let parens := s.parens.getD #[]
  let lexemes := (s.toks.extract start (closeAt + 1)).mapIdx fun i t =>
    if parens.contains (start + i) then (if isKw t "(" then "<" else ">") else lexeme t
  throw { span := s.toks[start]!.span.to close.span, msg := Fren.Core.parenTypeArgsMsg (Fren.Core.lexemesText lexemes) }

end

def type? : P (Option (Array Ident)) := do
  if (← eatKw ":").isNone then return none
  return some (← typeExpr)

/-- The binders of a quantifier, or of a global expectation's leading
`forall`, after the keyword `kw`, up to and including the `,` that ends
them. -/
def binders (kw : Token) : P (Array Binder) := do
  let name := if isKw kw "exists" then "exists" else "forall"
  unless isKw (← peek) "(" do
    let t ← peek
    if t.tok matches .ident _ then
      err t.span "F0131" s!"the binders of `{name}` must be in parentheses" (some "expected `(`")
        #[s!"note: a binder is written `(x: T)`, or `(x y: T)` for several names of one type",
          s!"help: write `{name} (x: T), e`"]
    fail t "`(`"
  let mut out := #[]
  repeat
    let openParen ← expectKw "("
    let mut names := #[← ident]
    while (← peek).tok matches .ident _ do names := names.push (← ident)
    discard (expectKw ":")
    let ty ← typeExpr
    discard (expectKw ")")
    out := out.push { names, ty, span := ← spanFrom openParen.span }
    if (← eatKw ",").isSome then break
    let t ← peek
    unless isKw t "(" do
      if t.tok matches .kw "==" | .kw "&&" | .kw "||" | .kw "|" | .kw "=>" then fail t "`,`"
      err t.span "F0132" s!"expected `,` after the binders of `{name}`, found {t.tok.describe}" (some "expected `,`")
        #[s!"note: the binders of `{name}` end with a comma, before its body"]
        #[{ msg := "add a comma", replacement := ",", after := true, range? := some (range (← lastSpan)) }]
  return out

mutual
partial def expr : P Expr := do
  let t ← peek
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
    let e ← if (← eatKw ":=").isSome then some <$> withRecords iff else pure none
    fs := fs.push (f, e)
    if (← eatKw ",").isNone then break
  return fs
/-- The scrutinee and arms of `match e { ... }`, or of `table e { ... }`, a
table over a scrutinee (`table`), whose first token is `t`. -/
partial def matchArms (t : Token) (table : Bool) : P Expr := do
  discard bump
  let saved := (← get).noRecord
  modify fun s => { s with noRecord := true }
  -- An atom, as Lean reads it.
  let scrutinee ← withIn atom
  modify fun s => { s with noRecord := saved }
  markList
  discard (expectKw "{")
  let mut arms := #[]
  repeat
    if isKw (← peek) "}" && !(table && arms.isEmpty) then break
    markStart
    let p ← pattern
    -- A guard, below `when`, which would swallow the arm's body.
    let guard? ← if (← eatKw "if").isSome then some <$> withRecords iff else pure none
    discard (expectKw "=>")
    -- Below `when`, which would swallow the following arms.
    arms := arms.push (p, guard?, ← withRecords iff)
    if (← eatKw ",").isNone then break
  discard (expectKw "}")
  fieldReads callArgs indexArg (.match (← spanFrom t.span) scrutinee arms table)

partial def atom : P Expr := do
  let t ← peek
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
    -- `w.x`, a variable of an instance
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
      markList
      discard bump
      let fs ← fieldInits "a record literal"
      discard (expectKw "}")
      return ← fieldReads callArgs indexArg (.record (← spanFrom start) segs fs)
    let name := "::".intercalate (segs.map (·.name)).toList
    noSpaceBeforeParen name s!"the arguments of `{name}`"
    unless isKw (← peek) "(" do return ← fieldReads callArgs indexArg (.path (start.to segs.back!.span) segs)
    markCall
    discard bump
    -- A cardinality operator without arguments parses, so that the
    -- elaborator reports it (`lang::cardinality_args`).
    if segs.size == 1 && (Fren.Core.Cardinality.ofName? segs[0]!.name).isSome && isKw (← peek) ")" then
      discard bump
      return ← fieldReads callArgs indexArg (.app (← spanFrom start) segs #[])
    let mut args := #[← withRecords expr]
    while (← eatKw ",").isSome do args := args.push (← withRecords expr)
    discard (expectKw ")")
    fieldReads callArgs indexArg (.app (← spanFrom start) segs args)
  | .kw "table" =>
    -- `{` right after `table` starts the rows of a table by conditions,
    -- and anything else its scrutinee.
    let st ← get
    if !isKw (st.toks[st.pos + 1]?.getD (← peek)) "{" then matchArms t true else
    discard bump
    markList
    discard (expectKw "{")
    let mut rows := #[]
    repeat
      if isKw (← peek) "}" && !rows.isEmpty then break
      markStart
      discard (eatKw "|")
      let start := (← peek).span
      -- `_`, which no condition can be, or a condition below `when`, which
      -- would swallow the row's value.
      let cond? ← if (← peek).tok == .ident "_" then discard bump; pure none else some <$> withRecords iff
      discard (expectKw "=>")
      rows := rows.push (start, cond?, ← withRecords iff)
      if (← eatKw ",").isNone then break
    discard (expectKw "}")
    fieldReads callArgs indexArg (.table (← spanFrom t.span) rows)
  | .kw "match" => matchArms t false
  | .kw "{" =>
    -- A set literal, or a record update if `with` follows the first
    -- expression.
    markList
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
        discard bump
        -- At least one field.
        if isKw (← peek) "}" then fail (← peek) "a name"
        let fs ← fieldInits "a record update"
        discard (expectKw "}")
        return ← fieldReads callArgs indexArg (.update (← spanFrom t.span) es[0]! fs)
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
    -- The condition and `then` branch are delimited, so `in` is a
    -- membership there even in a definition of a `let`.
    let c ← withIn expr
    discard (expectKw "then")
    let a ← withIn expr
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
    let close ← expectKw ")"
    -- A field read, method call or index of it starts at its `(`.
    fieldReads callArgs indexArg e (some (t.span.to close.span))
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
    let e ← iff
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


/-- Whether the next tokens are an enumeration's or a record's type
parameters written in parentheses, as they were before they were written
in angle brackets: `(`, up to the matching `)`, followed by `{`, which a
newtype's types are not. -/
def generic : P Bool := do
  let s ← get
  unless (s.toks[s.pos]?).any (isKw · "(") do return false
  let mut depth := 0
  let mut i := s.pos
  while h : i < s.toks.size do
    let t := s.toks[i]
    if isKw t "(" then depth := depth + 1
    else if isKw t ")" then
      depth := depth - 1
      if depth == 0 then return (s.toks[i + 1]?).any (isKw · "{")
    i := i + 1
  return false

/-- Reports the type parameters of the declaration of `name`, written in
parentheses from the next token, `(A, B)`, as they were before they were
written in angle brackets (`F0156`). -/
def parenParams (name : Ident) (params : Array Ident) (close : Span) : P α := do
  let lexemes := #[name.name, "<"] ++ ((params.map (·.name)).toList.intersperse ",").toArray |>.push ">"
  throw { span := name.span.to close, msg := Fren.Core.parenTypeParamsMsg (Fren.Core.lexemesText lexemes) }

/-- The type parameters of an enumeration or record named `name`, `<A, B>`,
if any. -/
def typeParams (name : Ident) : P (Array Ident) := do
  let (b, adjacent) ← bracketAfter
  match Fren.Core.afterName b adjacent with
  | .ends => return #[]
  | .spaced => spacedAngle name.name s!"the type parameters of `{name.name}`"
  | .parenthesized =>
    -- A newtype's types, unless a `{` follows them.
    unless ← generic do return #[]
    discard bump
    let mut ps := #[← ident]
    while (← eatKw ",").isSome do ps := ps.push (← ident)
    parenParams name ps (← expectKw ")").span
  | .opens => pure ()
  markCall
  discard bump
  let mut ps := #[← ident]
  while (← eatKw ",").isSome do ps := ps.push (← ident)
  discard closeAngle
  return ps

/-- `{ x := e, y, ... }`: the bindings of an instance or a refinement. -/
def bindings : P (Array (Ident × Option Expr)) := do
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
  return bs

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
    let defn ← if (← eatKw ":=").isSome then some <$> top else pure none
    return .var false isPub isDet x ty defn
  if let some m := det? <|> pub? then
    let mod := if isDet then "det" else "pub"
    let what := if isKw t "in" then "an input"
      else if isWord t "inst" then "an instance"
      else if isWord t "assume" || isWord t "ensure" || isKw t "expect" || isWord t "cover" then "a constraint"
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
    return .inst x comp (← bindings)
  let kind? := if isWord t "assume" then some PropKind.assume
    else if isWord t "ensure" then some .ensure
    else if isKw t "expect" then some .expect
    else if isWord t "cover" then some .cover
    else none
  if isKw t "," then
    err t.span "F0104" "expected a member or `}`, found `,`" (some "unexpected `,`")
      #["note: the members of a component are not separated by commas"] #[{ msg := "remove it", replacement := "" }]
  if isWord t "req" then
    err t.span "F0142" "`req` is now written `ensure`" (some "not a keyword")
      #["note: a guarantee is written `ensure name: e`, as an assumption is `assume name: e`"]
      #[{ msg := "write `ensure`", replacement := "ensure" }]
  let some kind := kind?
    | fail t "a member (`in`, `out`, `inst`, `assume`, `ensure`, `expect`, `cover` or `use`) or `}`"
        #["in", "out", "pub", "det", "inst", "assume", "ensure", "expect", "cover", "use"]
  discard bump
  let x ← ident
  discard (expectKw ":")
  return .prop kind x (← top)

partial def item : P Item := do
  markStart
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
      return .lintSetting span { name, span := o.span } value v.span removal (some (← item))
    return .lintSetting span { name, span := o.span } value v.span span none
  if isKw t "refine" then
    discard bump
    let name ← ident
    discard (expectKw ":")
    let (concrete, _) ← path false
    let r ← peek
    unless isWord r "refines" do fail r "`refines`"
    discard bump
    let (abstract, _) ← path false
    let bs ← if isKw (← peek) "{" then bindings else pure #[]
    let b ← peek
    if isWord b "by" then
      err b.span "F0112" "Lean code is not supported in .fren files" (some "a proof needs Lean")
        #["note: a refinement is proved with `by` only in Lean; the `fren` command checks it with the solver, or by testing",
          "help: move it to a Lean file that opens `Fren.Lang`, and check it with `lake build`"]
    return .refine name concrete abstract bs
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
        | .kw "comp" => "components" | .kw "type" => "types"
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
    discard (expectKw "(")
    let param : P (Array Ident × Option (Array Ident)) := do
      let p ← typeExpr
      return (p, ← type?)
    let group : P (Array (Array Ident × Option (Array Ident))) := do
      let mut params := #[← param]
      while (← eatKw ",").isSome do params := params.push (← param)
      discard (expectKw ")")
      return params
    let params ← group
    -- A second `(` right after the first group, each of whose parameters
    -- is a name: that group is type parameters, written in parentheses as
    -- they were before they were written in angle brackets.
    let s ← get
    if typeParams.isEmpty && (s.toks[s.pos]?).any (isKw · "(") && (s.toks[s.pos - 1]?).any (·.span.stop == s.toks[s.pos]!.span.start)
        && params.all fun (p, ty?) => p.size == 1 && ty?.isNone then
      parenParams name (params.map (·.1[0]!)) (← lastSpan)
    let result ← if (← eatKw ":").isSome then some <$> typeExpr else pure none
    let body ← if (← eatKw ":=").isSome then some <$> top else pure none
    -- Its contract (`Reqs/Lang/Items#contracts`), each clause continuing it.
    let mut clauses := #[]
    repeat
      let c ← peek
      unless isWord c "assume" || isWord c "ensure" do break
      discard bump
      let x ← ident
      discard (expectKw ":")
      clauses := clauses.push (isWord c "ensure", x, ← top)
    let t ← peek
    if !clauses.isEmpty && isKw t ":=" then
      err t.span "F0143" "a function's body is written after its contract" (some "after the contract")
        #["note: the clauses of a contract follow the signature and the body, as in `fn f(x: Int): Int := x + 1` and then `assume pos: x > 0`",
          "help: move the body, with its `:=`, before the first `assume` or `ensure`"]
    return .function isPub name typeParams params result body clauses (← lastSpan)
  if isKw t "const" then
    discard bump
    let name ← ident
    discard (expectKw ":")
    let ty ← typeExpr
    discard (expectKw ":=")
    return .const isPub name ty (← top)
  if isKw t "comp" then
    discard bump
    let name ← ident
    let openStop := (← expectKw "{").span.stop
    let mut ms := #[]
    let mut spans := #[]
    repeat
      let t ← peek
      if isKw t "}" then break
      if t.tok == .eof then fail t "`}`"
      ms := ms.push (← member)
      spans := spans.push { t.span with stop := (← lastSpan).stop }
    let close ← bump
    return .comp isPub name ms close.span spans openStop
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
    let start := (← peek).span.start
    modify fun s => { s with itemStarts := s.itemStarts.push start }
    items := items.push (← item)
  return items

end Parser

def parse (toks : Array Token) : Except ParseError (Array Item) :=
  (Parser.file).run' { toks }

/-- The items of a file, with where each starts in the source. -/
def parseItems (toks : Array Token) : Except ParseError (Array Item × Array Nat) :=
  (fun (items, s) => (items, s.itemStarts)) <$> (Parser.file).run { toks }

/-- The layout of a file that parses. -/
def parseLayout (toks : Array Token) : Except ParseError Layout :=
  (·.2.layout) <$> (Parser.file).run { toks }

end FrenCli
