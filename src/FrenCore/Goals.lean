/-!
# A goal's leading binders (`Reqs/Cli#goal-introduction`)

Before a query is given to the solver, both front ends introduce its
goal's leading binders: each bound name of a leading universal quantifier
becomes a fresh constant, each premise of a leading implication a
hypothesis, and a leading `let` is substituted into the rest. The solver is
then asked to refute the hypotheses with the negation of what is left. Each
step keeps the query's meaning: `hyps ⊨ ∀ x, P x` iff `hyps ⊨ P c` for a
constant `c` that occurs nowhere else, and `hyps ⊨ (p → q)` iff
`hyps, p ⊨ q`.

It changes what cvc5 decides, though. With the constants, the negated
goal is ground, and its terms are ones that cvc5 can instantiate the
quantified hypotheses with; under the quantifier, cvc5 can fail to, and
answer `unknown` where the query is `unsat` (#543).

`introduceGoal` is the decision, which `cli::goal_introduction` and
`cli::head_introduction` state;
each front end only reads the head of its own goals (`GoalHead`): the
Lean-hosted front end of its `Expr`s, which lean-smt is then told not to
introduce again, and `fren check` of its SMT-LIB terms.
-/

namespace Fren.Core

/-- The head of a goal, as a front end reads it: a universal quantifier
over one bound name, `binder`, an implication with the premise `premise`,
or a `let`, each in front of the rest of the goal, `rest`, in which the
bound name is the binder, or which has the `let`'s definitions
substituted; or anything else. -/
inductive GoalHead (B F : Type) where
  | universal (binder : B) (rest : F)
  | premise (premise rest : F)
  | definition (rest : F)
  | other
  deriving Inhabited

/-- What became of a head of a goal that was introduced. -/
inductive Introduced (B F : Type) where
  /-- A bound name, now a fresh constant. -/
  | constant (binder : B)
  /-- A premise, now a hypothesis. -/
  | hypothesis (premise : F)
  /-- A `let`, substituted into the rest. -/
  | substituted
  deriving Inhabited

/-- A goal with its leading heads introduced: what became of each, from
the outermost, and the goal that is left. -/
structure IntroducedGoal (B F : Type) where
  steps : List (Introduced B F) := []
  goal : F

/-- The bound names that became constants, from the outermost. -/
def IntroducedGoal.constants (g : IntroducedGoal B F) : Array B :=
  g.steps.toArray.filterMap fun | .constant b => some b | _ => none

/-- The premises that became hypotheses, from the outermost. -/
def IntroducedGoal.premises (g : IntroducedGoal B F) : Array F :=
  g.steps.toArray.filterMap fun | .hypothesis p => some p | _ => none

/-- What `h` becomes when it is introduced, with the rest of the goal;
none if it is not (`cli::head_introduction`). -/
def GoalHead.introduced? : GoalHead B F → Option (Introduced B F × F)
  | .universal b rest => some (.constant b, rest)
  | .premise p rest => some (.hypothesis p, rest)
  | .definition rest => some (.substituted, rest)
  | .other => none

/-- At most how many heads of a goal are introduced. A goal with more,
which no spec writes, keeps the rest as it is, which keeps its meaning
too. -/
def goalIntroductionLimit : Nat := 1024

/-- `goal` with its leading heads introduced, as `read` reads each, in at
most `fuel` steps: every universal quantifier, premise and `let` in front,
up to the first head that is none of them (`cli::goal_introduction`). -/
def introduceGoal [Monad m] (read : F → m (GoalHead B F)) (goal : F) :
    (fuel : Nat := goalIntroductionLimit) → m (IntroducedGoal B F)
  | 0 => pure { goal }
  | fuel + 1 => do
    match (← read goal).introduced? with
    | some (i, rest) =>
      let r ← introduceGoal read rest fuel
      pure { r with steps := i :: r.steps }
    | none => pure { goal }

/-- The `k`th symbol that a bound name `base` of a goal may be renamed
to: `base#goal{k}`, which no Fren name and no symbol that `smtName` makes
is. -/
def goalCandidate (base : String) (k : Nat) : String := base ++ "#goal" ++ toString k

/-- The first of `start`, `start + 1`, ... that `free` holds of, looking
at `fuel` of them, and `start + fuel` if none. -/
def firstFree (free : Nat → Bool) (start : Nat) : (fuel : Nat) → Nat
  | 0 => start
  | fuel + 1 => if free start then start else firstFree free (start + 1) fuel

/-- The symbol of the constant that a bound name `base` of a goal becomes
(`cli::goal_constant_name`): `base` itself if the query does not have it,
by `taken`, and otherwise the first `goalCandidate base k` that it does
not have. `fuel` bounds how many candidates are tried: more than the
query has symbols is enough, since the candidates are distinct. -/
def goalConstantName (taken : String → Bool) (base : String) (fuel : Nat) : String :=
  if !taken base then base else goalCandidate base (firstFree (fun k => !taken (goalCandidate base k)) 0 fuel)

end Fren.Core
