-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# The facts of a query's applications (`check::query_facts`)

`Fren.Core.appFactsWith`, which both front ends' query builders call,
keeps the facts of an application of the item's own function, `own?`, out
of its queries (`appBrings`): in an uninterpreted function's own contract,
each application of it is its value, so its facts would assume the clause
that a question about a table leaves out (#559). Over formulas that are
names, each its own one application: `f` and `g` have contracts, `x`
does not.
-/

namespace FrenTest.AppFacts

open Lean (Name)

def appsOf (f : String) : Array String := if f == "x" then #[] else #[f]

def factsOf (a : String) : Id (Array (Name × String)) := pure #[(`post, s!"post({a})")]

def fnOf (a : String) : Option Name := if a == "f" then some `f else if a == "g" then some `g else none

def run (own? : Option Name) : Array (Name × String) × Array Name :=
  Id.run (Fren.Core.appFactsWith appsOf factsOf fnOf #[(`h, "f")] "g" own?)

-- In `f`'s own item, only `g`'s facts, and only `g` among the functions.
#guard run (some `f) == (#[(`post, "post(g)")], #[`g])
-- Elsewhere, both.
#guard run none == (#[(`post, "post(f)"), (`post, "post(g)")], #[`f, `g])
-- In `g`'s, only `f`'s.
#guard run (some `g) == (#[(`post, "post(f)")], #[`f])

end FrenTest.AppFacts
