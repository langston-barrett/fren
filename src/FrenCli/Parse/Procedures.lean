-- keep-sorted start
import FrenCli.Parse.Members
-- keep-sorted end

/-! Pattern-test binders and parsing procedure and global expectation blocks. -/

namespace FrenCli

namespace Parser

/-- The names that the pattern `p` may bind: each path of one segment
without arguments, which is a binder unless it names a variant. -/
partial def patternNames : Pattern → Array String
  | .variant _ #[x] none => #[x.name]
  | .variant _ _ (some args) => args.flatMap patternNames
  | .or _ alts => alts.flatMap patternNames
  | _ => #[]

/-- The names that the pattern tests within `e` may bind: those of each
`x is P`'s pattern, which are in scope in a `when`'s body, the later
operands of an `and` and an `if`'s `then` branch
(`Reqs/Lang/Expressions#pattern-tests`). -/
partial def isNames : Expr → Array String
  | .is _ a p => isNames a ++ patternNames p
  | .bin _ _ a b => isNames a ++ isNames b
  | .not _ a => isNames a
  | .chain _ es _ => es.flatMap isNames
  | _ => #[]

/-- The rest of a procedure, or of a global expectation written with a
block (`global`), after its name: its parameters, as inputs, and its results, as
public outputs, each after any evidence setting (`header`); its block's
members, the span of its closing `}`, the span of each member, and where
its `{` ends. -/
def procRest (name : Ident) (global := false) : P (Array Member × Array Member × Span × Array Span × Nat) := do
  noSpaceBeforeParen name.name s!"the parameters of `{name.name}`"
  markCall
  openList .parameters
  discard (expectKw "(")
  let mut header := #[]
  repeat
    if isKw (← peek) ")" then break
    markStart
    -- A parameter takes no modifier (`F0110`).
    let m ← peek
    if (isKw m "pub" || isWord m "det") && ((← get).toks[(← get).pos + 1]?).any (·.tok matches .ident _) then
      let mod := if isKw m "pub" then "pub" else "det"
      let next := (← get).toks[(← get).pos + 1]!
      throw { span := m.span, msg := Fren.Core.paramModifierMsg mod (some { start := m.span.start, stop := next.span.start }) }
    let x ← ident
    let ty ← type?
    if let some d ← eatKw ":=" then
      throw { span := d.span, msg := Fren.Core.inputDefinitionMsg global }
    header := header.push (.var true true false x ty none)
    if !(← listComma) then break
  closeList
  discard (expectKw ")")
  let mut results := #[]
  if (← eatKw ":").isSome then
    openList .parameters
    discard (expectKw "(")
    repeat
      markStart
      if isWord (← peek) "set_option" then
        let ev ← member
        header := header.push ev
      let det? ← if isWord (← peek) "det" then some <$> bump else pure none
      let x ← ident
      header := header.push (.var false true det?.isSome x (← type?) none)
      results := results.push (unbanged x.name)
      if !(← listComma) then break
      if isKw (← peek) ")" then break
    closeList
    discard (expectKw ")")
  openList .members
  let ob ← expectKw "{"
  let saved := (← get).proc?
  modify fun s => { s with proc? := some { results, global } }
  let mut ms := #[]
  let mut spans := #[]
  repeat
    let t ← peek
    if isKw t "}" then break
    if t.tok == .eof then fail t "`}`"
    if ms.back?.any (!· matches .evidence ..) then memberEnd
    ms := ms.push (← member)
    spans := spans.push { t.span with stop := (← lastSpan).stop }
  closeList
  let close ← bump
  modify fun s => { s with proc? := saved }
  return (header, ms, close.span, spans, ob.span.stop)

end Parser

end FrenCli
