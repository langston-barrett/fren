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

Only what a spec asserts is changed: the expressions of `assume`s, `req`s,
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
  | shiftInteger
  | flipBool
  | removeElement
  | swapRepetition
  | narrowClass
  deriving BEq, Inhabited, Repr

def Origin.all : Array Origin :=
  #[.swapComparison, .swapAndOr, .swapArithmetic, .dropConjunct, .negateTrigger, .shiftInteger, .flipBool, .removeElement,
    .swapRepetition, .narrowClass]

def Origin.name : Origin → String
  | .swapComparison => "swap-comparison"
  | .swapAndOr => "swap-and-or"
  | .swapArithmetic => "swap-arithmetic"
  | .dropConjunct => "drop-conjunct"
  | .negateTrigger => "negate-trigger"
  | .shiftInteger => "shift-integer"
  | .flipBool => "flip-bool"
  | .removeElement => "remove-element"
  | .swapRepetition => "swap-repetition"
  | .narrowClass => "narrow-class"

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

/-- What generation needs of one file. -/
structure Src where
  file : Nat
  path : String
  chars : Array Char
  /-- Its tokens, in order. -/
  toks : Array Token

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
  | _ => none

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
partial def edits (s : Src) (e : Expr) (inAndLeft : Bool := false) : Array Edit :=
  let here : Array Edit := match e with
    | .bin sp op l r =>
      let opTok? := s.wordIn { start := l.span.stop, stop := r.span.start } op
      let swap (origin : Origin) (new : String) : Array Edit := match opTok? with
        | some t => #[{ origin, span := t.span, after := new, context := sp }]
        | none => #[]
      if let some new := comparisonSwap? op then swap .swapComparison new
      else if let some new := arithmeticSwap? op then swap .swapArithmetic new
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
    | .when sp negated _ _ =>
      let kw := if negated then "unless" else "when"
      #[{ origin := .negateTrigger, span := { start := sp.start, stop := sp.start + kw.length }, after := if negated then "when" else "unless",
          context := sp }]
    -- In decimal, whatever the literal's radix.
    | .num sp n => (#[n + 1] ++ (if n > 0 then #[n - 1] else #[])).map fun k =>
        { origin := .shiftInteger, span := sp, after := toString k, context := sp }
    | .bool sp b => #[{ origin := .flipBool, span := sp, after := if b then "false" else "true", context := sp }]
    | .set sp es | .seq sp es =>
      if es.size < 2 then #[] else
      let outs := es.map fun k => s.outer sp k.span
      (Array.range es.size).map fun k =>
        let span := if h : k + 1 < outs.size then { start := outs[k]!.start, stop := outs[k + 1].start }
          else { start := outs[k - 1]!.stop, stop := outs[k]!.stop }
        { origin := .removeElement, span, after := "", context := sp }
    | .method sp _ name #[.str lit _] =>
      if name.name != "matches?" then #[] else
      match s.literalBody? lit with
      | some body =>
        (patternEdits (s.chars.extract body.start body.stop)).map fun (origin, p, after) =>
          { origin, span := { start := body.start + p.start, stop := body.start + p.stop }, after, context := sp }
      | none => #[]
    | _ => #[]
  here ++ (children e).flatMap id
where
  children : Expr → Array (Array Edit)
    | .when _ _ c b => #[edits s c, edits s b]
    | .ite _ c a b => #[edits s c, edits s a, edits s b]
    | .bin sp op l r =>
      -- `l` is unparenthesized when its span starts the `and`'s.
      #[edits s l (op == "and" && s.outer sp l.span == l.span), edits s r]
    | .not _ e | .neg _ e | .field _ e _ => #[edits s e]
    | .app _ _ as | .set _ as | .seq _ as => as.map (edits s ·)
    | .record _ _ fs => fs.filterMap fun (_, e?) => e?.map (edits s ·)
    | .match _ sc arms => #[edits s sc] ++ arms.map fun (_, b) => edits s b
    | .pair _ a b | .index _ a b => #[edits s a, edits s b]
    | .method _ r _ as => #[edits s r] ++ as.map (edits s ·)
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
    | .function _ n _ _ (some body) => #[(.str module n.name, none, body)]
    | .comp _ n members =>
      let c := Name.str module n.name
      members.flatMap fun
        | .prop kind p e => if kind == .expect then #[] else #[(.str c p.name, some c, e)]
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

/-- The mutants of one file, in order of position. -/
def ofFile (s : Src) (items : Array Item) : Array Mutant := Id.run do
  let mut out := #[]
  -- How many identical mutants each item has had so far.
  let mut seen : Std.HashMap String Nat := {}
  for (item, comp?, e) in sites items do
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
