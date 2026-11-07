-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Native-cardinality fallback alone: a 257-value enum, 16 by 17 pairs,
abstract element types and Int payloads. Only empty-set and singleton laws
are asked, avoiding the known native finite-sort counterexample bug above
the cap. -/
def genSetCardFallback : R String := do
  let kind ← below 4
  let decls := "mod card_fallback\n\nset_option fren.lint.assertions_on_constants \"allow\"\n\n" ++
    "type A\n\nenum G<T> { Item(T) }\n\n" ++
    "struct Four { a?, b?, c?, d? }\n\n" ++
    "struct Eight { a?, b?, c?, d?, e?, f?, g?, h? }\n\n" ++
    "enum Seventeen { Extra, Bits(Four) }\n\nenum Beyond { Extra, Bits(Eight) }\n\n"
  let (ty, singleton) := match kind with
    | 0 => ("Set<Beyond>", "{Beyond::Extra}")
    | 1 => ("Rel<Four, Seventeen>", "{(Four { a? := false, b? := false, c? := false, d? := false }, Seventeen::Extra)}")
    | 2 => ("Set<A>", "{a}")
    | _ => ("Set<G<Int>>", "{G::Item(0)}")
  let arg := if kind == 2 then ", a: A" else ""
  let single := "    expect singleton: " ++ singleton ++ ".card = 1\n\n"
  return decls ++ s!"proc fallback(s: {ty}{arg}) \{\n" ++
    "    expect empty: (s minus s).card = 0\n\n" ++ single ++
    "    expect union_empty: when s = {}, (s union {}).card = 0\n}\n"

end FrenTest.FuzzFrontends.Wide
