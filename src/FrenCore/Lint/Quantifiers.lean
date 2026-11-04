-- keep-sorted start
import FrenCore.Lint.Cardinality
import FrenCore.Lint.Naming
-- keep-sorted end

/-!
# Local definition and quantifier lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Local definitions and quantifiers -/

/-- Whether `let_and_return` fires on a `let` or `where` clause, from
whether its body is the name of its last definition, alone, and whether
that definition's type is written (`lint::let_and_return`). -/
def letAndReturn (bodyIsLast annotated : Bool) : Bool := bodyIsLast && !annotated

/-- The fix of `let_and_return`: the clause without its last definition,
whose expression `e` is its body, where `earlier?` is the text of the
definitions before it, from the first to the end of the one before it. -/
def letAndReturnFixed (isWhere : Bool) (earlier? : Option String) (e : String) : String :=
  match earlier? with
  | none => e
  | some ds => if isWhere then s!"{e} where {ds}" else s!"let {ds} in {e}"

/-- `let_and_return`'s message, at the body `n`, whose fix replaces the
clause at `range` with `fixed`, or none but a note if a comment in the
clause would be lost (`commented`). -/
def letAndReturnMsg (n : Name) (isWhere : Bool) (range : Range) (fixed : String) (commented : Bool) : Msg :=
  let help := s!"write the definition of `{n}` in place of `{n}`"
  { code? := some Lint.letAndReturn.code
    headline := s!"this {if isWhere then "`where` clause" else "`let`"} only gives back its last definition"
    label? := some s!"the body is `{n}`"
    notes := if commented then #[s!"help: {help}", "note: `fren fix` leaves this, since a comment in it would be lost"]
      else #[]
    fixes := if commented then #[] else #[{ msg := help, replacement := fixed, range? := some range }] }

/-- Whether `redundant_locals` fires on a definition, from whether its
name is written with `!`, whether its type is written, and whether its
expression is that name alone (`lint::redundant_locals`). -/
def redundantLocal (bang annotated ownName : Bool) : Bool := bang && !annotated && ownName

/-- `redundant_locals`' message on `x! := x`. It suggests removing the
definition, but `fren fix` does not apply that: the definition may be an
unfinished edit, such as of `x! := x + 1`, which removing it would hide. -/
def redundantLocalMsg (n : Name) : Msg :=
  { code? := some Lint.redundantLocals.code, headline := s!"redundant definition of `{n}`"
    label? := some s!"defines `{n}` as the `{n}` it hides"
    notes := #[s!"note: `{n}` means the same with the definition and without it",
      s!"help: write the expression meant for `{n}`, or remove the definition"] }

/-- Whether `trivial_quantifier` fires on a quantifier, from the number of
its bound names whose types have one value (`lint::trivial_quantifier`). -/
def trivialQuantifier (nOne : Nat) : Bool := nOne ≥ 1

/-- Whether `trivial_quantifier`'s fix is given, from the number of bound
names whose types have one value, the number of bound names, whether each
of those types is an enumeration with one variant without a payload, and
whether the quantifier is a global expectation's leading `forall`, and
whether its body declares one of its bound names again
(`lint::trivial_quantifier`). -/
def trivialQuantifierFixed (nOne nNames : Nat) (variants global redeclared : Bool) : Bool :=
  nOne ≥ 1 && nOne == nNames && variants && !global && !redeclared

/-- The body of a quantifier at `body`, with each of the mentions of its
bound names at `mentions`, which are within it, replaced by its value
`value`: the fix of `trivial_quantifier`. -/
def substituted (src : Array Char) (body : Range) (mentions : Array (Range × String)) : String := Id.run do
  let ms := mentions.qsort fun a b => a.1.start < b.1.start
  let mut out := ""
  let mut i := body.start
  for (r, v) in ms do
    if r.start < i || r.stop > body.stop then continue
    out := out ++ textOf src { start := i, stop := r.start } ++ v
    i := r.stop
  return out ++ textOf src { start := i, stop := body.stop }

/-- `trivial_quantifier`'s message on a `forall` (`all`) or an `exists`
whose bound name `n` has a type `ty` of one value, `value` if it is a
variant: fixed to `fixed?` if every bound name's type has one, which is a
variant, and no comment would be lost, in place of the quantifier at
`range`. -/
def trivialQuantifierMsg (all : Bool) (n : Name) (ty : String) (value? : Option String) (range : Range)
    (fixed? : Option String) : Msg :=
  let kw := if all then "forall" else "exists"
  let help := match value? with
    | some v => s!"write the body with `{v}` in place of `{n}`"
    | none => s!"write the body at the one value of `{ty}`"
  { code? := some Lint.trivialQuantifier.code, headline := s!"this `{kw}` ranges over one value"
    label? := some s!"`{ty}` has one value"
    notes := #[s!"note: {if all then "a" else "an"} `{kw}` over a type of one value is its body at that value"]
      ++ (if fixed?.isSome then #[] else #[s!"help: {help}"])
    fixes := match fixed? with
      | some f => #[{ msg := help, replacement := f, range? := some range }]
      | none => #[] }

/-- The lexemes of `src[r]` as `manual_forall` compares them, each with
its range: a name or a path, `a::b` or `a.b`, possibly with a final `!`,
is one, and so is a number or a string literal, raw ones too; comments
and whitespace are none, and every other character is one. -/
def pathLexemes (src : Array Char) (r : Range) : Array (Range × String) := Id.run do
  let stop := min r.stop src.size
  let mut out := #[]
  let mut i := r.start
  while i < stop do
    let c := src[i]!
    let start := i
    if c.isWhitespace then
      i := i + 1
    else if c == '-' && src[i + 1]? == some '-' then
      while i < stop && src[i]! != '\n' do i := i + 1
    else if c == '/' && src[i + 1]? == some '-' then
      let mut depth := 1
      i := i + 2
      while i < stop && depth > 0 do
        if src[i]! == '/' && src[i + 1]? == some '-' then depth := depth + 1; i := i + 2
        else if src[i]! == '-' && src[i + 1]? == some '/' then depth := depth - 1; i := i + 2
        else i := i + 1
    else
      -- A raw literal is `r`, some `#`, then `"`, and ends with `"` and as many `#`.
      let mut hashes := 0
      while c == 'r' && src[i + 1 + hashes]? == some '#' do hashes := hashes + 1
      let raw := c == 'r' && src[i + 1 + hashes]? == some '"'
      if raw || c == '"' then
        i := if raw then i + hashes + 2 else i + 1
        let closes (k : Nat) := src[k]! == '"' && (List.range (if raw then hashes else 0)).all (src[k + 1 + ·]? == some '#')
        while i < stop && !closes i do
          i := i + (if !raw && src[i]! == '\\' then 2 else 1)
        i := min stop (i + 1 + (if raw then hashes else 0))
      else if isWordChar c then
        while i < stop && isWordChar src[i]! do i := i + 1
        repeat
          if src[i]? == some ':' && src[i + 1]? == some ':' && (src[i + 2]?.any isWordChar) then i := i + 2
          else if src[i]? == some '.' && (src[i + 1]?.any isWordChar) then i := i + 1
          else break
          while i < stop && isWordChar src[i]! do i := i + 1
        if src[i]? == some '!' && src[i + 1]? != some '=' then i := i + 1
      else
        i := i + 1
      out := out.push ({ start, stop := i }, textOf src { start, stop := i })
  return out

/-- The first segment of a name or a path, without a `!`. -/
def pathRoot (s : String) : String :=
  (((s.splitOn "::").head!.splitOn ".").head!.dropEndWhile (· == '!')).toString

/-- Whether an expression written `s` has an index or a table, whose
guards a rewrite that reorders or regroups its parts might change. -/
def hasGuarded (s : String) : Bool :=
  let cs := s.toList.toArray
  (pathLexemes cs { start := 0, stop := cs.size }).any fun (_, t) => t == "[" || t == "table"

/-- What `manual_forall` needs to know of the constraint that an
expression is in, from its front end. -/
structure ForallCx where
  /-- The number of variants of the enumeration of a path, as `variant?`
  gives its variants, if none of them has a payload. -/
  variants? : String → Option Nat := fun _ => none
  /-- The names that the constraint declares: those of its `let`s and
  `where` clause, its bound names and its patterns' binders. -/
  declared : Array String := #[]
  /-- Whether a name declared there would hide something in scope. -/
  hides : String → Bool := fun _ => false
  /-- The constraint has no index and no table (`hasGuarded`), so that
  the guards are the same however its parts are ordered. -/
  unguarded : Bool := false
  deriving Inhabited

/-- Whether `manual_forall` fires on operands of a run of `and` or `or`,
from whether they are one expression at a variant written in the same
places in each, whether each variant of its enumeration is one operand's,
once, and the number of operands (`lint::manual_forall`). -/
def manualForall (instances covers : Bool) (n : Nat) : Bool := instances && covers && n ≥ 3

/-- The bound name that `manual_forall`'s fix writes for the enumeration
written `ty`, if it can: its last segment in snake case, which is not a
reserved word, written with `!` if it hides something; none if the
constraint declares it, or the operands mention it. -/
def forallName? (cx : ForallCx) (ty : String) (mentioned : Array String) : Option String := do
  let n := toCase .snake ((ty.splitOn "::").getLast!)
  guard (identifierAccepted n && !reservedWords.contains n && !expressionWords.contains n)
  guard (!cx.declared.contains n && !mentioned.contains n)
  return if cx.hides n then n ++ "!" else n

/-- `manual_forall`'s message on the operands of a run of `and` (`all`)
or `or`, which are one expression at each variant of `ty`, fixed to
`fixed?`, if a bound name can be written and no comment would be lost. -/
def manualForallMsg (all : Bool) (ty : String) (fixed? : Option String) : Msg :=
  let kw := if all then "forall" else "exists"
  { code? := some Lint.manualForall.code
    headline := s!"these {if all then "conjuncts" else "disjuncts"} are one expression at each variant of `{ty}`"
    label? := some "one for each variant"
    notes := #[s!"note: `{kw}` says this once, and says it of a variant added later too"]
      ++ (if fixed?.isSome then #[] else #[s!"help: write it with `{kw}`"])
    fixes := match fixed? with
      | some f => #[{ msg := s!"write it with `{kw}`", replacement := f }]
      | none => #[] }

/-- Where a run of operands is (`lint::RunPlace`): where any expression may
be written; a body of `when`, `let` or a quantifier; a `when`'s condition,
or a part of an atom, which take an operand alike (`delimitedSlot`); an
operand of an operator; or a receiver. -/
inductive RunPlace where
  | free
  | body
  | condition
  | operand
  | receiver
  deriving Inhabited, DecidableEq, Repr

/-- The place of an operand in `slot`. -/
def RunPlace.ofSlot : Option Slot → RunPlace
  | none => .free
  | some s =>
    if s.outer == 0 then (if s.right then .body else .condition)
    else if s.outer == BKind.atom.prec then .receiver else .operand

/-- Whether `manual_forall`'s quantifier is put in parentheses, from where
the run is, whether something follows it, whether the fix replaces the
whole run, and whether the run is already in parentheses of its own
(`lint::quantifier_parentheses`). A quantifier is open-ended, so this is
`BText.inSlot` for it. -/
def quantifierParenthesized (p : RunPlace) (followed whole enclosed : Bool) : Bool :=
  !enclosed && (!whole || followed || p matches .condition | .operand | .receiver)

/-- The paths in `n` that `variant?` says are variants without a payload,
each with its range and variant. -/
partial def variantPaths (variant? : α → Option String) (n : BNode α) : Array (Range × String) :=
  ((variant? n.ref).map (n.range, ·)).toArray ++ n.kids.flatMap (variantPaths variant?)

/-- The enumeration of a variant as `variant?` gives it: all but its last
component. -/
def variantEnum (v : String) : String := ".".intercalate (v.splitOn ".").dropLast

/-- Whether the operands `ops`, each as its lexemes and the variants in
it, are one expression at a variant: they have the same lexemes but at
some places, and at each of those, each operand has a path to one variant
of one enumeration, its own; if so, those places, each operand's variant,
and the type that the first operand's path names. -/
def instancesOf? (ops : Array (Array (Range × String) × Array (Range × String))) :
    Option (Array Nat × Array String × String) := do
  let (first, _) ← ops[0]?
  guard (ops.all (·.1.size == first.size))
  let places := (List.range first.size).toArray.filter fun p => ops.any (·.1[p]!.2 != first[p]!.2)
  guard (!places.isEmpty)
  let vs ← ops.mapM fun (lex, paths) => do
    let ws ← places.mapM fun p => (paths.find? (·.1 == lex[p]!.1)).map (·.2)
    let v ← ws[0]?
    guard (ws.all (· == v))
    pure v
  let e := variantEnum vs[0]!
  guard (vs.all (variantEnum · == e))
  let path := first[places[0]!]!.2
  guard ((path.splitOn "::").length ≥ 2)
  return (places, vs, "::".intercalate (path.splitOn "::").dropLast)

/-- `manual_forall` on `n`, an `and` or an `or` in `slot` within
`parent`, if it is the top of a run (`lint::manual_forall`): one report
for each run of adjacent operands, not in parentheses, that are one
expression at each variant of an enumeration, in a constraint that `cx`
says has no index and no table. -/
def manualForallAt [Inhabited α] (src : Array Char) (variant? : α → Option String) (cx : ForallCx) (n : BNode α)
    (slot : Option Slot) (parent : Range) : Array (OpReport α) := Id.run do
  let .bin op := n.kind | return #[]
  unless cx.unguarded && (op == "and" || op == "or") do return #[]
  if slot.any (fun s => s.outer == (BKind.bin op).prec && !s.right) && !enclosed src parent n.range then return #[]
  let cs := runOperands op src n
  let parts := cs.map fun k => (pathLexemes src k.range, variantPaths variant? k)
  let bare := cs.map fun k => !enclosed src n.range k.range
  let mut out := #[]
  let mut i := 0
  while i + 3 ≤ cs.size do
    let found? := (List.range (cs.size + 1 - i - 3)).findSome? fun d => do
      let j := i + 3 + d
      guard ((bare.extract i j).all id)
      let (places, vs, ty) ← instancesOf? (parts.extract i j)
      -- `x = E::A or x = E::B or ...` over every variant is always `true`,
      -- and is not a quantifier's instances but a test of `x`.
      let k := cs[i]!
      guard (!(k.kind matches .bin "=" | .bin "!=") ||
        !k.kids.any fun c => places.any (parts[i]!.1[·]!.1 == c.range))
      let covers := (cx.variants? (variantEnum vs[0]!)).any (· == j - i) && (vs.toList.eraseDups.length == j - i)
      guard (manualForall true covers (j - i))
      pure (j, places, ty)
    let some (j, places, ty) := found? | i := i + 1; continue
    let whole := i == 0 && j == cs.size
    let range : Range := { start := cs[i]!.range.start, stop := cs[j - 1]!.range.stop }
    let mentioned := ((parts.extract i j).flatMap (·.1)).map (pathRoot ·.2)
    let fixed? := do
      guard (!hasComment (textOf src range))
      let x ← forallName? cx ty mentioned
      let (lex, _) := parts[i]!
      let body := substituted src cs[i]!.range (places.map fun p => (lex[p]!.1, x.dropEndWhile (· == '!') |>.toString))
      let t : BText := { text := s!"{if op == "and" then "forall" else "exists"} ({x}: {ty}), {body}", prec := BKind.quant.prec }
      let paren := quantifierParenthesized (RunPlace.ofSlot slot) (followedAt src n.range) whole
        (whole && inOwnParens src n parent)
      pure (if paren then s!"({t.text})" else t.text)
    out := out.push { lint := .manualForall, ref := cs[i]!.ref, last? := some cs[j - 1]!.ref
                      msg := manualForallMsg (op == "and") ty fixed? }
    i := j
  return out
end Fren.Core
