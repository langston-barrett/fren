-- keep-sorted start
import FrenCli.Parse.Basic
import FrenCore.Closures
-- keep-sorted end

/-! Parsing type paths, type arguments and quantifier binders. -/

namespace FrenCli

namespace Parser

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

/-- A closure without parameters, `||` or `| |`, at `span`. -/
def closureNoParams (span : Span) : P α :=
  err span "F0161" "a closure has at least one parameter" (some "no parameters")
    #["note: a closure is written `|x| e`, with the parameters of the function that it is given for"]

/-- The segments of a function type, `fn(A, B) -> R`: `fnSeg`, the
parameters' types separated by `fnSep`, `fnArrow` and the result's type. -/
def fnSeg : String := Fren.Core.fnSeg

def fnSep : String := Fren.Core.fnSep

def fnArrow : String := Fren.Core.fnArrow

mutual
/-- A type: a path, `Set<T>`, `Seq<T>`, `Rel<A, B>`, or an instance of a
generic type, `G<A, B>`. -/
partial def typeExpr : P (Array Ident) := baseType

/-- A declared type path or a collection/generic instance of declared
types. Subset constraints appear only in named declarations. -/
partial def baseType : P (Array Ident) := do
  let t ← peek
  -- A function type (`Reqs/Lang/HigherOrder#function-types`).
  if isKw t "fn" then
    discard bump
    markCall
    discard (expectKw "(")
    let mut out := #[{ name := fnSeg, span := t.span : Ident }] ++ (← typeExpr)
    while isKw (← peek) "," do
      let c ← bump
      out := out ++ #[{ name := fnSep, span := c.span : Ident }] ++ (← typeExpr)
    let close ← expectKw ")"
    let arrow ← peek
    unless isKw arrow "->" do
      err arrow.span "F0162" s!"expected `->` after a function type's parameters, found {arrow.tok.describe}"
        (some "expected `->`") #["note: a function type is written `fn(T) -> U`, with its result's type after `->`"]
    discard bump
    return out ++ #[{ name := fnArrow, span := close.span.to arrow.span : Ident }] ++ (← typeExpr)
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

end Parser

end FrenCli
