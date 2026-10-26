-- keep-sorted start
import FrenCli.Parse
import FrenCore.Names
-- keep-sorted end

/-!
# Mutants

The small changes that `fren mutate` makes to a spec (`Reqs/Mutate`). Each
mutant replaces one span of a file's text, as elaborated, with new text. The
operators work on the parsed items, so every mutant parses: precedence is
kept by parenthesizing where an operator binds more loosely than the one it
replaces, and a hoisted operand keeps its own parentheses.

Only what a spec asserts is changed: the expressions of `assume`s, `ensure`s,
defined outputs, instance bindings, constants and defined functions. The
expectations, local and global, are what kills mutants, and are left alone.

Generating mutants is pure; `FrenCli.mutate` runs them.
-/

namespace FrenCli.Mutate

open Lean (Name)

/-- What made a mutant (`Reqs/Mutate#mutants`). -/
inductive Origin where
  | swapComparison
  | swapAndOr
  | swapArithmetic
  | dropConjunct
  | negateTrigger
  | swapQuantifier
  | shiftInteger
  | flipBool
  | removeElement
  | swapRepetition
  | narrowClass
  | dropAlternative
  | swapCardinality
  | dropArgument
  | swapRows
  | dropRow
  | shiftVariant
  | swapBranches
  | dropNegation
  | dropTrigger
  | dropUpdate
  | swapArms
  | swapMinMax
  | swapAffix
  deriving BEq, Inhabited, Repr

def Origin.all : Array Origin :=
  #[.swapComparison, .swapAndOr, .swapArithmetic, .dropConjunct, .negateTrigger, .swapQuantifier, .shiftInteger, .flipBool,
    .removeElement, .swapRepetition, .narrowClass, .dropAlternative, .swapCardinality, .dropArgument, .swapRows, .dropRow,
    .shiftVariant, .swapBranches, .dropNegation, .dropTrigger, .dropUpdate, .swapArms, .swapMinMax, .swapAffix]

def Origin.name : Origin → String
  | .swapComparison => "swap-comparison"
  | .swapAndOr => "swap-and-or"
  | .swapArithmetic => "swap-arithmetic"
  | .dropConjunct => "drop-conjunct"
  | .negateTrigger => "negate-trigger"
  | .swapQuantifier => "swap-quantifier"
  | .shiftInteger => "shift-integer"
  | .flipBool => "flip-bool"
  | .removeElement => "remove-element"
  | .swapRepetition => "swap-repetition"
  | .narrowClass => "narrow-class"
  | .dropAlternative => "drop-alternative"
  | .swapCardinality => "swap-cardinality"
  | .dropArgument => "drop-argument"
  | .swapRows => "swap-rows"
  | .dropRow => "drop-row"
  | .shiftVariant => "shift-variant"
  | .swapBranches => "swap-branches"
  | .dropNegation => "drop-negation"
  | .dropTrigger => "drop-trigger"
  | .dropUpdate => "drop-update"
  | .swapArms => "swap-arms"
  | .swapMinMax => "swap-min-max"
  | .swapAffix => "swap-affix"

structure Mutant where
  origin : Origin
  file : Nat
  /-- The item that it changes: a constraint or defined output, as
  `module::comp::name`, an instance, a constant or a function. -/
  item : Name
  /-- The component whose item it changes, if any. -/
  comp? : Option Name
  /-- The text replaced, in the file as elaborated. -/
  span : Span
  before : String
  after : String
  /-- `ORIGIN-ITEM-HASH` (`Reqs/Mutate#identifiers`). -/
  id : String := ""
  deriving Inhabited

/-- `chars` with `m` applied. -/
def Mutant.apply (m : Mutant) (chars : Array Char) : Array Char :=
  chars.extract 0 m.span.start ++ m.after.toList.toArray ++ chars.extract m.span.stop chars.size

/-! ## Text and tokens -/

/-- The enumerations of a spec, by name: each variant in order, with
whether it has a payload. Two enumerations of one name are left out, since
a name alone does not tell them apart. -/
abbrev Enums := Std.HashMap String (Array (String × Bool))

/-- What generation needs of one file. -/
structure Src where
  file : Nat
  path : String
  chars : Array Char
  /-- Its tokens, in order. -/
  toks : Array Token
  /-- Each `+` where a `Nat` is expected, which a `-` would make an `Int`. -/
  natSums : Array Span := #[]
  /-- The spec's enumerations, in any of its files. -/
  enums : Enums := {}
  /-- The variants that the file's `use`s bring into scope by their own
  names, each with the name of its enumeration. -/
  bare : Std.HashMap String String := {}
  /-- The names that the file declares with a `!`, shadowing
  (`Reqs/Lang/Components#shadowing`): a variant of such a name, written by
  its name alone, may mean the binder instead. -/
  shadowed : Std.HashSet String := {}

def Src.text (s : Src) (sp : Span) : String := String.ofList (s.chars.extract sp.start sp.stop).toList

/-- The index of the first token that starts at or after `pos`. -/
def Src.tokAt (s : Src) (pos : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := s.toks.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if s.toks[mid]!.span.start < pos then lo := mid + 1 else hi := mid
  return lo

/-- The first token in `sp` that is the keyword or identifier `w`. -/
def Src.wordIn (s : Src) (sp : Span) (w : String) : Option Token := Id.run do
  let mut i := s.tokAt sp.start
  while i < s.toks.size && s.toks[i]!.span.stop ≤ sp.stop do
    let t := s.toks[i]!
    if t.tok == .kw w || t.tok == .ident w then return some t
    i := i + 1
  return none

/-- `child` with the parentheses around it that lie within `parent`: an
expression's span leaves out its own parentheses, which its parent's
includes. -/
def Src.outer (s : Src) (parent child : Span) : Span := Id.run do
  let mut sp := child
  repeat
    let i := s.tokAt sp.start
    let j := s.tokAt sp.stop
    let some prev := s.toks[i - 1]? | break
    let some next := s.toks[j]? | break
    if i > 0 && prev.tok == .kw "(" && next.tok == .kw ")" && parent.start ≤ prev.span.start && next.span.stop ≤ parent.stop then
      sp := { start := prev.span.start, stop := next.span.stop }
    else break
  return sp

/-- `s` with each run of whitespace made one space, for identifiers. -/
def normalize (s : String) : String :=
  let words := s.toList.splitBy (fun a b => a.isWhitespace == b.isWhitespace) |>.filter (·.any (!·.isWhitespace))
  " ".intercalate (words.map String.ofList)

/-- `s` as an identifier hashes it, so that formatting cannot change it:
without whitespace, and without the commas that end a list. -/
def idText (s : String) : String :=
  let cs := s.toList.filter (!·.isWhitespace)
  let rec go : List Char → List Char
    | ',' :: c :: rest => if c == '}' || c == ']' || c == ')' then go (c :: rest) else ',' :: go (c :: rest)
    | c :: rest => c :: go rest
    | [] => []
  String.ofList (go cs)

/-- `path` as an identifier hashes it: without `.` segments and repeated
`/`, so that `./spec.fren` and `spec.fren` agree. -/
def idPath (path : String) : String :=
  let segs := (path.splitOn "/").filter fun g => g != "." && !g.isEmpty
  (if path.startsWith "/" then "/" else "") ++ "/".intercalate segs

/-! ## Operators -/

def comparisonSwap? : String → Option String
  | "<" => some "<="
  | "<=" => some "<"
  | ">" => some ">="
  | ">=" => some ">"
  | "=" => some "!="
  | "!=" => some "="
  | _ => none

def arithmeticSwap? : String → Option String
  | "+" => some "-"
  | "-" => some "+"
  | "div" => some "mod"
  | "mod" => some "div"
  | _ => none

/-- The operands of `e`. -/
def exprChildren : Expr → Array Expr
  | .when _ _ c b | .bin _ _ c b | .pair _ c b | .index _ c b => #[c, b]
  | .ite _ c a b => #[c, a, b]
  | .not _ e | .neg _ e | .field _ e _ => #[e]
  | .app _ _ as | .set _ as | .seq _ as => as
  | .record _ _ fs => fs.filterMap (·.2)
  | .match _ sc arms _ => #[sc] ++ armParts arms
  | .is _ sc _ => #[sc]
  | .table _ rows => tableParts rows
  | .method _ r _ as => #[r] ++ as
  | _ => #[]

/-- Every expression of `items`, and their subexpressions. -/
partial def allExprs (items : Array Item) : Array Expr :=
  let rec sub (e : Expr) : Array Expr := #[e] ++ (exprChildren e).flatMap sub
  let rec ofItem : Item → Array Expr
    | .const _ _ _ v | .global _ _ v | .function _ _ _ _ (some v) _ _ => #[v]
    | .comp _ _ members .. => members.flatMap fun
      | .prop _ _ e | .var _ _ _ _ _ (some e) => #[e]
      | .inst _ _ bs => bs.filterMap (·.2)
      | _ => #[]
    | .refine _ _ _ bs => bs.filterMap (·.2)
    | .lintSetting _ _ _ _ _ (some body) => ofItem body
    | _ => #[]
  (items.flatMap ofItem).flatMap sub

/-- The last segments of the paths that bound the range patterns of `p`. -/
partial def rangeBounds : Pattern → Array String
  | .range _ lo hi _ => (#[lo, hi].filterMap id).filterMap fun
    | .path _ segs => some segs.back!.name
    | .num .. => none
  | .variant _ _ (some args) => args.flatMap rangeBounds
  | .or _ alts => alts.flatMap rangeBounds
  | _ => #[]

/-- The last segment of the name of each constant that a divisor of `items`
names, or a bound of a range pattern, and of each constant that the value of
such a constant names, which changing could make a divisor `0`, a range
empty, or a `match` not exhaustive or an arm unreachable
(`Reqs/Mutate#mutants`). -/
partial def divisorConstants (items : Array Item) : Std.HashSet String := Id.run do
  let rec named : Expr → Option String
    | .neg _ e => named e
    | .path _ segs => some ((segs.back!.name.splitOn ".").head!)
    | _ => none
  let mut out : Std.HashSet String := {}
  for e in allExprs items do
    if let .bin _ op _ k := e then
      if op == "div" || op == "mod" then
        if let some n := named k then out := out.insert n
    if let .match _ _ arms _ := e then
      out := out.insertMany (arms.flatMap (rangeBounds ·.1))
    if let .is _ _ p := e then
      out := out.insertMany (rangeBounds p)
  -- Through the values of constants, until nothing is new.
  let values := items.filterMap fun | .const _ n _ v => some (n.name, v) | _ => none
  let mut changed := true
  while changed do
    changed := false
    for (n, v) in values do
      unless out.contains n do continue
      for e in allExprs #[.const false { name := n, span := default } #[] v] do
        if let .path _ segs := e then
          let m := (segs.back!.name.splitOn ".").head!
          unless out.contains m do out := out.insert m; changed := true
  return out

/-- The items of the class that starts after the `[` at `i` of pattern `p`,
as offsets in `p`, and the offset of its `]`. -/
def classItems (p : Array Char) (i : Nat) : Array (Nat × Nat) × Nat := Id.run do
  let mut j := if p[i]? == some '^' then i + 1 else i
  let mut items := #[]
  while j < p.size && p[j]! != ']' do
    let start := j
    j := if p[j]! == '\\' then j + 2 else j + 1
    -- A range, `a-z`, unless the `-` is last.
    if p[j]? == some '-' && p[j + 1]?.any (· != ']') then
      j := if p[j + 1]! == '\\' then j + 3 else j + 2
    items := items.push (start, j)
  return (items, j)

/-- The edits of pattern `p` (`Reqs/Lang/Expressions#patterns`), as spans
of `p` and their replacements: `*` and `+` swapped, and each item of a
class of at least two removed, unless that leaves a `^` first. -/
def patternEdits (p : Array Char) : Array (Origin × Span × String) := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < p.size do
    let c := p[i]!
    if c == '\\' then i := i + 2
    else if c == '[' then
      let (items, close) := classItems p (i + 1)
      if items.size ≥ 2 then
        let negated := p[i + 1]? == some '^'
        for (a, b) in items, k in [0:items.size] do
          -- A `^` that would come first would negate the class.
          if k == 0 && !negated && items[1]?.any (p[·.1]? == some '^') then continue
          out := out.push (.narrowClass, { start := a, stop := b }, "")
      i := close + 1
    else
      if c == '*' then out := out.push (.swapRepetition, { start := i, stop := i + 1 }, "+")
      if c == '+' then out := out.push (.swapRepetition, { start := i, stop := i + 1 }, "*")
      i := i + 1
  return out

/-- Where the body of the string literal at `sp` starts, if its text is
its value: a raw literal, or one without escapes. -/
def Src.literalBody? (s : Src) (sp : Span) : Option Span := do
  let text := s.chars.extract sp.start sp.stop
  if text[0]? == some 'r' then
    let hashes := ((text.toList.drop 1).takeWhile (· == '#')).length
    return { start := sp.start + hashes + 2, stop := sp.stop - hashes - 1 }
  guard !text.contains '\\'
  return { start := sp.start + 1, stop := sp.stop - 1 }

/-- The enumerations of `items` (`Enums`). -/
partial def enumsOf (items : Array Item) : Enums := Id.run do
  let rec decls : Item → Array (String × Array (String × Bool))
    | .enum _ n vs _ => #[(n.name, vs.map fun (v, p?) => (v.name, p?.isSome))]
    | .lintSetting _ _ _ _ _ (some body) => decls body
    | _ => #[]
  let mut out : Enums := {}
  let mut clash : Std.HashSet String := {}
  for (n, vs) in items.flatMap decls do
    if let some old := out[n]? then
      if old.map (·.1) != vs.map (·.1) then clash := clash.insert n
    else out := out.insert n vs
  return clash.fold (init := out) fun acc n => acc.erase n

/-- The variants of `enums` that the `use`s `paths`, each a path and
whether it ends in `*`, bring into scope by their own names, `use E::V`,
`use E::{V, W}` and `use E::*` for any prefix of `E`, each with the name of
its enumeration, added to those of `outer`, which they shadow. A name that
`paths` bring from two enumerations is left out. -/
def importedVariants (enums : Enums) (paths : Array (Array Ident × Bool)) (outer : Std.HashMap String String := {}) :
    Std.HashMap String String := Id.run do
  let mut found : Array (String × String) := #[]
  for (path, glob) in paths do
    let names := path.map (·.name)
    if glob then
      if let some e := names.back? then
        if let some vs := enums[e]? then found := found ++ vs.map (·.1, e)
    else if h : 2 ≤ names.size then
      let e := names[names.size - 2]
      if (enums[e]?).any (·.any (·.1 == names.back!)) then found := found.push (names.back!, e)
  let mut out : Std.HashMap String String := {}
  let mut clash : Std.HashSet String := {}
  for (v, e) in found do
    match out[v]? with
    | some e' => if e' != e then clash := clash.insert v
    | none => out := out.insert v e
  let own := clash.fold (init := out) fun acc v => acc.erase v
  return own.fold (init := clash.fold (init := outer) fun acc v => acc.erase v) fun acc v e => acc.insert v e

/-- The names that tokens `toks` declare with a `!`, without it. -/
def shadowedNames (toks : Array Token) : Std.HashSet String :=
  toks.foldl (init := {}) fun acc t => match t.tok with
    | .ident w => if w.endsWith "!" then acc.insert (w.dropEnd 1).toString else acc
    | _ => acc

/-- Whether pattern `p` binds a name: a path of one segment that is not
`true`, `false` or a variant in scope (`lang::pattern_name`). -/
partial def Src.binds (s : Src) : Pattern → Bool
  | .variant _ #[x] none => x.name != "true" && x.name != "false" && !s.bare.contains x.name
  | .variant _ _ (some args) => args.any s.binds
  | .or _ alts => alts.any s.binds
  | _ => false

/-- The payload-free variants next to the variant that the path `segs`
names, in the order declared, written as `segs` would write them: `E::W`
after `E::V`, and `W` after `V` only if `use`s bring both into scope from
the same enumeration, and no binder shadows `V`. -/
def Src.neighbours (s : Src) (segs : Array Ident) : Array String := Id.run do
  let some v := segs.back? | return #[]
  let enum? := if segs.size ≥ 2 then some segs[segs.size - 2]!.name
    else if s.shadowed.contains v.name then none
    else s.bare[v.name]?
  let some e := enum? | return #[]
  let some vs := s.enums[e]? | return #[]
  let some i := vs.findIdx? (·.1 == v.name) | return #[]
  if vs[i]!.2 then return #[]
  let near := (if i > 0 then #[vs[i - 1]!] else #[]) ++ (vs[i + 1]?.toArray)
  return near.filterMap fun (w, payload) =>
    if payload || (segs.size == 1 && s.bare[w]? != some e) then none else some w

/-- The spans of the items of a list separated by commas, as removed:
each with the `,` after it, and the last with the `,` before it. -/
def removals (spans : Array Span) : Array Span :=
  (Array.range spans.size).map fun k =>
    if h : k + 1 < spans.size then { start := spans[k]!.start, stop := spans[k + 1].start }
    else { start := spans[k - 1]!.stop, stop := spans[k]!.stop }

/-- The text of `a` and `b`, two spans in order, each written where the
other was. -/
def Src.swapped (s : Src) (a b : Span) : String :=
  s.text b ++ s.text { start := a.stop, stop := b.start } ++ s.text a

/-- A candidate change, before it is given its item and identifier. -/
structure Edit where
  origin : Origin
  span : Span
  after : String
  /-- The expression changed, for the identifier. -/
  context : Span

/-- The edits of expression `e`. `inAndLeft` says that `e` is the left
operand of an `and`, unparenthesized, where an `or` needs parentheses; an
`or` whose left operand is an unparenthesized `or` parenthesizes it. -/
partial def edits (s : Src) (e : Expr) (inAndLeft : Bool := false) (divisor : Bool := false) : Array Edit :=
  let here : Array Edit := match e with
    | .bin sp op l r =>
      let opTok? := s.wordIn { start := l.span.stop, stop := r.span.start } op
      let swap (origin : Origin) (new : String) : Array Edit := match opTok? with
        | some t => #[{ origin, span := t.span, after := new, context := sp }]
        | none => #[]
      if let some new := comparisonSwap? op then swap .swapComparison new
      -- A `-` is an `Int`, so a `+` where a `Nat` is expected stays.
      else if let some new := arithmeticSwap? op then if s.natSums.contains sp then #[] else swap .swapArithmetic new
      else if op == "or" then
        -- `a or b or c` is `(a or b) or c`: its left operand needs
        -- parentheses under `and`.
        match l, opTok? with
        | .bin _ "or" .., some t =>
          if s.outer sp l.span == l.span then
            let text := s!"({s.text l.span}){s.text { start := l.span.stop, stop := t.span.start }}and{s.text { start := t.span.stop, stop := sp.stop }}"
            #[{ origin := .swapAndOr, span := sp, after := text, context := sp }]
          else swap .swapAndOr "and"
        | _, _ => swap .swapAndOr "and"
      else if op == "and" then
        let toOr : Array Edit := match opTok? with
          | some t =>
            if inAndLeft then
              let text := s.text { start := sp.start, stop := t.span.start } ++ "or" ++ s.text { start := t.span.stop, stop := sp.stop }
              #[{ origin := .swapAndOr, span := sp, after := s!"({text})", context := sp }]
            else #[{ origin := .swapAndOr, span := t.span, after := "or", context := sp }]
          | none => #[]
        toOr ++ #[l, r].map fun k => { origin := .dropConjunct, span := sp, after := s.text (s.outer sp k.span), context := sp }
      else #[]
    | .chain sp es ops =>
      let outs := es.map (s.outer sp ·.span)
      let swaps := (ops.zip (outs.zip (outs.extract 1))).filterMap fun ((op, opSpan), l, r) =>
        (comparisonSwap? op).map fun new =>
          { origin := .swapComparison, span := opSpan, after := new, context := { start := l.start, stop := r.stop } }
      -- Without its first comparison, and without its last.
      swaps ++ #[{ start := outs[1]!.start, stop := sp.stop }, { start := sp.start, stop := outs[outs.size - 2]!.stop }].map fun k =>
        { origin := .dropConjunct, span := sp, after := s.text k, context := sp }
    | .when sp negated _ body =>
      let kw := if negated then "unless" else "when"
      #[{ origin := .negateTrigger, span := { start := sp.start, stop := sp.start + kw.length }, after := if negated then "when" else "unless",
          context := sp },
        { origin := .dropTrigger, span := sp, after := s.text (s.outer sp body.span), context := sp }]
    -- `forall` and `exists` are both six letters long.
    | .quant sp all _ _ =>
      #[{ origin := .swapQuantifier, span := { start := sp.start, stop := sp.start + 6 }, after := if all then "exists" else "forall",
          context := sp }]
    -- In decimal, whatever the literal's radix.
    -- A divisor is never made `0`.
    | .num sp n => (#[n + 1] ++ (if n > 0 && !(divisor && n == 1) then #[n - 1] else #[])).map fun k =>
        { origin := .shiftInteger, span := sp, after := toString k, context := sp }
    | .bool sp b => #[{ origin := .flipBool, span := sp, after := if b then "false" else "true", context := sp }]
    | .path sp segs => (s.neighbours segs).map fun w =>
        { origin := .shiftVariant, span := segs.back!.span, after := w, context := sp }
    | .ite sp _ a b =>
      let (a, b) := (s.outer sp a.span, s.outer sp b.span)
      if s.text a == s.text b then #[] else
      #[{ origin := .swapBranches, span := { start := a.start, stop := b.stop }, after := s.swapped a b, context := sp }]
    | .not sp k | .neg sp k => #[{ origin := .dropNegation, span := sp, after := s.text (s.outer sp k.span), context := sp }]
    | .update sp _ fs =>
      if fs.size < 2 then #[] else
      let spans := fs.map fun (x, e?) => match e? with
        | some v => { start := x.span.start, stop := (s.outer sp v.span).stop }
        | none => x.span
      (removals spans).map fun span => { origin := .dropUpdate, span, after := "", context := sp }
    | .match sp _ arms _ =>
      let vals := arms.map fun (_, _, b) => s.outer sp b.span
      (Array.range (arms.size - 1)).filterMap fun k =>
        let (a, b) := (vals[k]!, vals[k + 1]!)
        if s.binds arms[k]!.1 || s.binds arms[k + 1]!.1 || s.text a == s.text b then none else
        some { origin := .swapArms, span := { start := a.start, stop := b.stop }, after := s.swapped a b, context := sp }
    -- A well-formed spec applies no variable, so this is the built-in
    -- function.
    | .app sp #[f] args =>
      match Fren.Core.Cardinality.ofName? f.name with
      | none => #[]
      | some c =>
        let swap : Edit := { origin := .swapCardinality, span := f.span, after := c.swap.name, context := sp }
        if args.size < 2 then #[swap] else
        -- With its `,`, as an element of a set literal.
        let outs := args.map fun k => s.outer sp k.span
        #[swap] ++ (Array.range args.size).map fun k =>
          let span := if h : k + 1 < outs.size then { start := outs[k]!.start, stop := outs[k + 1].start }
            else { start := outs[k - 1]!.stop, stop := outs[k]!.stop }
          { origin := .dropArgument, span, after := "", context := sp }
    | .set sp es | .seq sp es =>
      if es.size < 2 then #[] else
      let outs := es.map fun k => s.outer sp k.span
      (Array.range es.size).map fun k =>
        let span := if h : k + 1 < outs.size then { start := outs[k]!.start, stop := outs[k + 1].start }
          else { start := outs[k - 1]!.stop, stop := outs[k]!.stop }
        { origin := .removeElement, span, after := "", context := sp }
    -- With its `|`: before the next alternative, or after the one before.
    | .is sp _ (.or _ alts) =>
      if alts.size < 2 then #[] else
      (Array.range alts.size).map fun k =>
        let span := if h : k + 1 < alts.size then { start := alts[k]!.span.start, stop := alts[k + 1].span.start }
          else { start := alts[k - 1]!.span.stop, stop := alts[k]!.span.stop }
        { origin := .dropAlternative, span, after := "", context := sp }
    -- The values of two rows in a row swapped, and each row dropped, with
    -- its `|`, if a row is left: before the next row, or after the one
    -- before.
    | .table sp rows =>
      let vals := rows.map fun (_, _, v) => s.outer sp v.span
      let swaps := (Array.range (rows.size - 1)).filterMap fun k =>
        let (a, b) := (vals[k]!, vals[k + 1]!)
        if s.text a == s.text b then none else
        some { origin := .swapRows, span := { start := a.start, stop := b.stop }
               after := s.text b ++ s.text { start := a.stop, stop := b.start } ++ s.text a, context := sp }
      let starts := rows.map fun (st, _, _) =>
        let i := s.tokAt st.start
        match s.toks[i - 1]? with
        | some t => if i > 0 && t.tok == .kw "|" then t.span.start else st.start
        | none => st.start
      let drops := if rows.size < 2 then #[] else (Array.range rows.size).map fun k =>
        let span := if h : k + 1 < starts.size then { start := starts[k]!, stop := starts[k + 1] }
          else { start := vals[k - 1]!.stop, stop := vals[k]!.stop }
        { origin := .dropRow, span, after := "", context := sp }
      swaps ++ drops
    | .method sp _ name args =>
      let swap (origin : Origin) (new : String) : Array Edit := #[{ origin, span := name.span, after := new, context := sp }]
      match name.name, args with
      | "min", #[_] => swap .swapMinMax "max"
      | "max", #[_] => swap .swapMinMax "min"
      | "starts_with?", #[_] => swap .swapAffix "ends_with?"
      | "ends_with?", #[_] => swap .swapAffix "starts_with?"
      | "matches?", #[.str lit _] =>
        match s.literalBody? lit with
        | some body =>
          (patternEdits (s.chars.extract body.start body.stop)).map fun (origin, p, after) =>
            { origin, span := { start := body.start + p.start, stop := body.start + p.stop }, after, context := sp }
        | none => #[]
      | _, _ => #[]
    | _ => #[]
  here ++ (children e).flatMap id
where
  children : Expr → Array (Array Edit)
    | .when _ _ c b => #[edits s c, edits s b]
    | .ite _ c a b => #[edits s c, edits s a, edits s b]
    | .bin sp op l r =>
      -- `l` is unparenthesized when its span starts the `and`'s.
      #[edits s l (op == "and" && s.outer sp l.span == l.span), edits s r (divisor := op == "div" || op == "mod")]
    | .neg _ e => #[edits s e (divisor := divisor)]
    | .not _ e | .field _ e _ => #[edits s e]
    | .app _ _ as | .set _ as | .seq _ as | .chain _ as _ => as.map (edits s ·)
    | .record _ _ fs => fs.filterMap fun (_, e?) => e?.map (edits s ·)
    | .update _ r fs => #[edits s r] ++ fs.filterMap fun (_, e?) => e?.map (edits s ·)
    | .match _ sc arms _ => #[edits s sc] ++ (armParts arms).map (edits s ·)
    | .table _ rows => (tableParts rows).map (edits s ·)
    | .is _ sc _ => #[edits s sc]
    -- The body once, not each instance.
    | .quant _ _ _ b => #[edits s b]
    | .pair _ a b | .index _ a b => #[edits s a, edits s b]
    | .method _ r _ as => #[edits s r] ++ as.map (edits s ·)
    | .«let» _ defs body _ => defs.map (edits s ·.2.2) |>.push (edits s body)
    | _ => #[]

/-! ## Sites -/

/-- The expressions of `items` that mutants change, each with its item and
component. -/
partial def sites (items : Array Item) : Array (Name × Option Name × Expr) := Id.run do
  let mut module : Name := .anonymous
  let mut out := #[]
  for item in items do
    match item with
    | .mod _ segs => module := segs.foldl (fun n i => Name.mkStr n i.name) .anonymous
    | _ => out := out ++ (ofItem module item)
  return out
where
  declared (x : Ident) : String := Fren.Core.nameText (Fren.Core.declaredName (.mkSimple x.name)).1
  ofItem (module : Name) : Item → Array (Name × Option Name × Expr)
    | .const _ n _ v => #[(.str module n.name, none, v)]
    | .function _ n _ _ (some body) _ _ => #[(.str module n.name, none, body)]
    | .comp _ n members .. =>
      let c := Name.str module n.name
      members.flatMap fun
        -- Expectations and cover goals are what rejects mutants, so they are not mutated.
        | .prop kind p e => if kind == .expect || kind == .cover then #[] else #[(.str c p.name, some c, e)]
        -- By the names they declare, without the `!` of shadowing.
        | .var _ _ _ x _ (some d) => #[(.str c (declared x), some c, d)]
        | .inst i _ bs => bs.filterMap fun (_, e?) => e?.map (.str c (declared i), some c, ·)
        | _ => #[]
    | .lintSetting _ _ _ _ _ (some body) => ofItem module body
    | _ => #[]

/-- `n` as an identifier's `ITEM`: each run of characters other than ASCII
letters, digits, `_` and `:` becomes one `_`, trimmed. -/
def itemSlug (n : Name) : String :=
  let keep (c : Char) := c.isAlphanum || c == '_' || c == ':'
  let s := "::".intercalate (n.components.map (·.toString))
  let s := s.toList.foldl (init := "") fun acc c =>
    if keep c then acc.push c else if acc.endsWith "_" then acc else acc.push '_'
  let trim (p : List Char) := ((p.dropWhile (· == '_')).reverse.dropWhile (· == '_')).reverse
  "::".intercalate ((s.splitOn "::").map fun p => String.ofList (trim p.toList))

/-- The 64-bit FNV-1a hash of the UTF-8 bytes of `s`: fixed, unlike
`hash`, which may change with Lean. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (init := 0xcbf29ce484222325) fun h b => (h ^^^ b.toUInt64) * 0x100000001b3

/-- Twelve hexadecimal digits of `h`. -/
def hex12 (h : UInt64) : String :=
  let digits := String.ofList (Nat.toDigits 16 (h.toNat % 2 ^ 48))
  String.ofList (List.replicate (12 - digits.length) '0') ++ digits

/-- The mutants of one file, in order of position. The constants named
`divisors`, and those that `divisorConstants` finds in the file, are left
alone. -/
def ofFile (s : Src) (items : Array Item) (divisors : Std.HashSet String := {}) : Array Mutant := Id.run do
  let mut out := #[]
  -- How many identical mutants each item has had so far.
  let mut seen : Std.HashMap String Nat := {}
  let divisors := divisors.insertMany (divisorConstants items)
  -- The file's own enumerations, if its spec's are not given.
  let enums := (enumsOf items).fold (init := s.enums) fun acc n vs => if acc.contains n then acc else acc.insert n vs
  let s := { s with enums, shadowed := shadowedNames s.toks }
  -- The `use`s of the file, which bring names into scope after them, and
  -- those of each component, which bring them into its scope
  -- (`Reqs/Lang/Modules`).
  let fileUses := items.flatMap fun
    | .use sp path glob => #[(sp, path, glob)]
    | .useGroup sp pre paths => paths.map (sp, pre ++ ·, false)
    | _ => #[]
  let compUses : Std.HashMap Name (Array (Array Ident × Bool)) := Id.run do
    let mut module : Name := .anonymous
    let mut out := {}
    let rec comp? : Item → Option (Ident × Array Member)
      | .comp _ n members .. => some (n, members)
      | .lintSetting _ _ _ _ _ (some body) => comp? body
      | _ => none
    for item in items do
      if let .mod _ segs := item then module := segs.foldl (fun n i => Name.mkStr n i.name) .anonymous
      if let some (n, members) := comp? item then
        out := out.insert (.str module n.name) (members.flatMap fun
          | .use _ path glob => #[(path, glob)]
          | .useGroup _ pre paths => paths.map (pre ++ ·, false)
          | _ => #[])
    return out
  let rec constName? : Item → Option String
    | .const _ n _ _ => some n.name
    | .lintSetting _ _ _ _ _ (some body) => constName? body
    | _ => none
  let consts := items.filterMap constName?
  for (item, comp?, e) in sites items do
    if comp?.isNone && consts.contains item.getString! && divisors.contains item.getString! then continue
    let outer := importedVariants enums ((fileUses.filter (·.1.stop ≤ e.span.start)).map (·.2))
    let s := { s with bare := importedVariants enums ((comp?.bind (compUses[·]?)).getD #[]) outer }
    for ed in edits s e do
      let before := s.text ed.span
      let key := "\x00".intercalate [ed.origin.name, idPath s.path, item.toString, idText (s.text ed.context), idText before, idText ed.after]
      let k := seen.getD key 0
      seen := seen.insert key (k + 1)
      let id := s!"{ed.origin.name}-{itemSlug item}-{hex12 (fnv1a s!"{key}\x00{k}")}"
      out := out.push { origin := ed.origin, file := s.file, item, comp?, span := ed.span, before, after := ed.after, id }
  -- In order of position, and otherwise as made.
  let order := (out.mapIdx fun k m => (k, m)).qsort fun (i, a) (j, b) => a.span.start < b.span.start || (a.span.start == b.span.start && i < j)
  return order.map (·.2)

end FrenCli.Mutate
