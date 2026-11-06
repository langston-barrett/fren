-- keep-sorted start
import FrenCore.Check.Contracts
-- keep-sorted end

/-!
fren-covers: check::fact_applications

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

/-! Query isolation (#766). For `closeApps` in `Id`, changing a pure
`inside` outside a closed set containing the initial work leaves its
returned closure unchanged, even when its rounds run out. The guards below
exercise `appFactsWith` separately, at reached and unreached applications. -/

/-- Deduplication only removes elements, even for the comparison on Lean
expressions, which has no `LawfulBEq` instance. -/
private theorem mem_of_mem_eraseDups {F : Type} [BEq F] (l : List F) {a : F}
    (h : a ∈ l.eraseDups) : a ∈ l := by
  have loop : ∀ (xs acc : List F) a, a ∈ List.eraseDupsBy.loop (· == ·) xs acc → a ∈ xs ∨ a ∈ acc := by
    intro xs
    induction xs with
    | nil => intro acc a h; exact .inr (by simpa [List.eraseDupsBy.loop] using h)
    | cons x xs ih =>
      intro acc a h
      simp only [List.eraseDupsBy.loop] at h
      split at h
      · exact (ih acc a h).imp (List.mem_cons_of_mem x) id
      · rcases ih (x :: acc) a h with h | h
        · exact .inl (List.mem_cons_of_mem x h)
        · rcases List.mem_cons.mp h with h | h
          · exact .inl (List.mem_cons.mpr (.inl h))
          · exact .inr h
  exact (loop l [] a h).resolve_right (by simp)

/-- For `closeApps` with a pure `inside`, changing it outside a closed set
containing the initial work leaves the returned application/payload pairs
and their order unchanged, including the exhaustion result. -/
theorem closeApps_congr {F α : Type} [BEq F] (brings : F → Bool)
    (inside₁ inside₂ : F → Id (α × List F)) (P : F → Prop)
    (agree : ∀ a, P a → inside₁ a = inside₂ a)
    (closed : ∀ a, P a → ∀ b ∈ (inside₁ a).run.2, P b) :
    ∀ (n : Nat) (seen work : List F) (acc : List (F × α)),
      (∀ a ∈ work, P a) →
      (Fren.Core.closeApps brings inside₁ n seen work acc).run =
        (Fren.Core.closeApps brings inside₂ n seen work acc).run := by
  intro n
  induction n with
  | zero => intro seen work acc _; cases work <;> rfl
  | succ n ih =>
    intro seen work acc hw
    cases work with
    | nil => rfl
    | cons w ws =>
      have he : (w :: ws).map (fun a => (inside₁ a).run) = (w :: ws).map (fun a => (inside₂ a).run) :=
        List.map_congr_left fun a ha => congrArg Id.run (agree a (hw a ha))
      simp only [Fren.Core.closeApps, Id.run_bind, List.idRun_mapM]
      rw [← he]
      apply ih
      intro b hb
      have hb := (List.mem_filter.mp (mem_of_mem_eraseDups _ hb)).1
      simp only [List.mem_flatMap, List.mem_map] at hb
      obtain ⟨_, ⟨a, ha, rfl⟩, hb⟩ := hb
      exact closed a (hw a ha) b hb

/-- Exercise the query entry point with a fact callback that varies at
`unused`: queries rooted at `g` leave that value unreached, while a query
rooted at `unused` observes it. -/
def isolated (other : String) (goal : String := "g") : Option (Array (Name × String) × Array Name) :=
  Id.run (Fren.Core.appFactsWith appsOf
    (fun a => if a == "unused" then pure #[(`post, other)] else factsOf a)
    fnOf factAppsOf 3 #[] goal)

#guard isolated "true" == runChain none
#guard isolated "false" == runChain none
-- The control queries must observe the changed callback when they reach it.
#guard isolated "true" "unused" == some (#[(`post, "true")], #[])
#guard isolated "false" "unused" == some (#[(`post, "false")], #[])
#guard isolated "true" "unused" != isolated "false" "unused"
-- Neither a function nor a fact at all when this query mentions none.
#guard Id.run (Fren.Core.appFactsWith appsOf factsOf fnOf factAppsOf 3 #[] "x") == some (#[], #[])

end FrenTest.AppFacts
