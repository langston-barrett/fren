-- keep-sorted start
import FrenTest.FuzzFrontends.Expressions
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

mutual
/-- A term of a trait's carrier, over the carriers `ss` and the integers
`xs`, of depth at most `d` (`traitGroup`). -/
partial def traitSelf (sc : WScope) (ss xs : Array String) (d : Nat) : R String := do
  if d == 0 || (← chance 50) then pick ss
  else return s!"step({← traitSelf sc ss xs (d - 1)}, {← traitInt sc ss xs (d - 1)})"

/-- An integer term of a trait: a variable, a literal, an observation, a
sum, or an expression of the spec's constants and functions alone, which
multiplies no two variables, an error (`traitGroup`). -/
partial def traitInt (sc : WScope) (ss xs : Array String) (d : Nat) : R String := do
  match ← below (if d == 0 then 3 else 6) with
  | 0 => if xs.isEmpty then return toString (← below 4) else pick xs
  | 1 => return toString (← below 4)
  | 2 => return s!"obs({← traitSelf sc ss xs 0})"
  | 3 => return s!"obs({← traitSelf sc ss xs (d - 1)})"
  | 4 => return s!"{← traitInt sc ss xs (d - 1)} + {← traitInt sc ss xs (d - 1)}"
  | _ => gen { sc with vars := #[] } .int 1
end

/-- A `Bool` term of a trait, which applies `ok?` if `flag` (`traitGroup`). -/
def traitBool (sc : WScope) (flag : Bool) (ss xs : Array String) (d : Nat) : R String := do
  match ← below (if flag then 4 else 3) with
  | 0 => return s!"{← traitInt sc ss xs d} = {← traitInt sc ss xs d}"
  | 1 => return s!"{← traitInt sc ss xs d} <= {← traitInt sc ss xs d}"
  | 2 => return s!"{← traitSelf sc ss xs d} = {← traitSelf sc ss xs d}"
  | _ => return s!"ok?({← traitSelf sc ss xs d})"

/-- A trait (`Reqs/Lang/Traits`): methods in both of an uninterpreted
function's forms, one with a contract, laws over them, and expectations
in both of a global expectation's forms, whose terms apply the methods to
each other and to the spec's constants and functions. Its laws are
outside the decidable core, so `undecidable` is allowed on it, and
nothing in it is an error. -/
def traitGroup (sc : WScope) : R String := do
  let contract ← chance 50
  let flag ← chance 50
  let mut out := "set_option fren.lint.undecidable \"allow\" in\npub trait Tr {\n"
  out := out ++ (if contract then "    fn obs(s: Self): (r: Int) {\n        ensure low: r >= 0\n    }\n"
    else "    fn obs(Self): Int\n")
  out := out ++ "    fn step(Self, Int): Self\n"
  if flag then out := out ++ "    fn ok?(Self)\n"
  for k in [0:← below 3] do
    let law ← if ← chance 50 then
        pure s!"obs(step(s, x)) = {← traitInt sc #["s"] #["x"] 1}"
      else traitBool sc flag #["s"] #["x"] 1
    out := out ++ s!"\n    law l{k}(s: Self, x: Int): {law}\n"
  for k in [0:(← below 2) + 1] do
    -- Now and then under a lint setting, as a member may be.
    if ← chance 20 then out := out ++ "\n    set_option fren.lint.eq_op \"allow\" in"
    if ← chance 50 then
      let assume ← if ← chance 40 then pure s!"        assume a: {← traitBool sc flag #["s", "t"] #["x"] 0}\n" else pure ""
      let claim ← traitBool sc flag #["s", "t"] #["x"] 1
      out := out ++ s!"\n    expect e{k}(s: Self, t: Self, x: Int) \{\n{assume}        expect c: {claim}\n    }\n"
    else
      out := out ++ s!"\n    expect e{k}: forall (s: Self) (x: Int), {← traitBool sc flag #["s"] #["x"] 1}\n"
  -- The other forms, drawn after the members above, so that a trait drawn
  -- before them is as it was: a method that shadows a procedure's name,
  -- which only the trait's own law mentions; a contract over an earlier
  -- method; a law with no variables, one with a `Bool` variable written
  -- `x?`, and one after a lint setting; and a trait that is not `pub`.
  if ← chance 40 then
    out := out ++ "\n    fn c0(Self): Int\n    law shadowed(s: Self): c0(s) >= 0\n"
  if ← chance 40 then
    out := out ++ "\n    fn grown(s: Self): (r: Int) { ensure above: r >= obs(s) }\n"
  if ← chance 30 then
    out := out ++ s!"\n    law closed(): {← gen { sc with vars := #[] } .int 1} <= {← gen { sc with vars := #[] } .int 1}\n"
  if ← chance 30 then
    out := out ++ s!"\n    law flagged(s: Self, b?): when b?, {← traitBool sc flag #["s"] #[] 0}\n"
  if ← chance 30 then
    out := out ++ s!"\n    set_option fren.lint.eq_op \"allow\" in\n    law set(s: Self, x: Int): {← traitBool sc flag #["s"] #["x"] 0}\n"
  out := if ← chance 30 then out.replace "pub trait Tr" "trait Tr" else out
  return out ++ "}\n"

end FrenTest.FuzzFrontends.Wide
