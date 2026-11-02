-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# The facts of a query's applications (`check::query_facts`)

`Fren.Core.appFactsWith`, which both front ends' query builders call,
keeps the facts of an application of the item's own function, `own?`, out
of its queries (`appBrings`): in an uninterpreted function's own contract,
each application of it is its value, so its facts would assume the clause
that a question about a table leaves out (#559). And it gives them the
facts of the applications that their facts mention, transitively
(`closeApps`, #619). Over formulas that are names, each its own one
application: `f` and `g` have contracts, `x` does not.
-/

namespace FrenTest.AppFacts

open Lean (Name)

def appsOf (f : String) : Array String := if f == "x" then #[] else #[f]

def factsOf (a : String) : Id (Array (Name × String)) := pure #[(`post, s!"post({a})")]

def fnOf (a : String) : Option Name := if a == "f" then some `f else if a == "g" then some `g else none

def run (own? : Option Name) : Array (Name × String) × Array Name :=
  (Id.run (Fren.Core.appFactsWith appsOf factsOf fnOf (fun _ => pure #[]) 1 #[(`h, "f")] "g" own?)).getD (#[], #[])

-- In `f`'s own item, only `g`'s facts, and only `g` among the functions.
#guard run (some `f) == (#[(`post, "post(g)")], #[`g])
-- Elsewhere, both.
#guard run none == (#[(`post, "post(f)"), (`post, "post(g)")], #[`f, `g])
-- In `g`'s, only `f`'s.
#guard run (some `g) == (#[(`post, "post(f)")], #[`f])

/-! The facts of the applications that facts mention are the query's too
(`check::fact_applications`, `closeApps`): `post(g)` mentions `f`, and
`post(f)` mentions `g` again, which the query has. -/

def factAppsOf (f : String) : Id (Array String) :=
  pure (if f == "post(g)" then #["f"] else if f == "post(f)" then #["g"] else #[])

def runChain (own? : Option Name) (rounds : Nat := 3) : Option (Array (Name × String) × Array Name) :=
  Id.run (Fren.Core.appFactsWith appsOf factsOf fnOf factAppsOf rounds #[] "g" own?)

-- `g`'s, then `f`'s, which only `g`'s fact mentions.
#guard runChain none == some (#[(`post, "post(g)"), (`post, "post(f)")], #[`g, `f])
-- In `f`'s own item, `f` brings nothing, though `g`'s fact mentions it.
#guard runChain (some `f) == some (#[(`post, "post(g)")], #[`g])
-- Rounds that run out first give none, never fewer facts.
#guard runChain none 1 == none

end FrenTest.AppFacts
