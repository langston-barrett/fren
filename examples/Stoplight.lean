-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# A pedestrian crossing in Lean

A controller built from one `step` function, which an `impl` proves meets
the spec's `stoplight::step`. The spec checks one step at a time, and
fixed-length chains of them; the theorems here say what it can't, about
every sequence of events: every state that the controller reaches from
`START` is valid, and the phases that it shows form a run of the abstract
machine `stoplight::cycle`. Both follow from lemmas that serve any step
function: one for an invariant, and one for a simulation.
-/

open Fren.Lang

-- The spec, in its module `stoplight`.
#fren_md "stoplight.fren"

#fren_check

namespace Stoplight

open stoplight

/-- One step of the controller. -/
def step (s : State) : Event → State
  | .Press => { s with waiting? := decide (s.people = .DontWalk) }
  | .Tick =>
    if s.timer > 1 then { s with timer := s.timer - 1 }
    else match s.cars with
      | .Green => if s.waiting? then { s with cars := .Yellow, timer := YELLOW } else s
      | .Yellow => { cars := .Red, people := .Walk, waiting? := false, timer := WALK }
      | .Red => { s with cars := .Green, people := .DontWalk, timer := MIN_GREEN }

-- `step` is the spec's procedure, resolved from the spec's module, `stoplight`.
impl step_meets: step for (s : State) (e : Event) {
  now := s, event := e, next := Stoplight.step s e
} by
  intro s e h
  obtain ⟨cars, people, waiting, timer⟩ := s
  cases e <;> cases cars <;> cases people <;> cases waiting <;>
    by_cases ht : 1 < timer <;> simp only [Stoplight.step, ht, if_true, if_false] <;>
    simp_all [fren_spec] <;> omega

/-! ## Lemmas for any step function -/

section Generic

variable {σ α ε : Type} (step : σ → ε → σ)

/-- An invariant that every step keeps holds after any sequence of events. -/
theorem foldl_invariant (inv : σ → Prop) (keeps : ∀ s e, inv s → inv (step s e)) :
    ∀ (es : List ε) (s : σ), inv s → inv (es.foldl step s)
  | [], _, h => h
  | e :: es, s, h => foldl_invariant inv keeps es (step s e) (keeps s e h)

/-- `Run r a es b`: the abstract machine `r` goes from `a` to `b` by the events `es`. -/
inductive Run (r : α → ε → α → Prop) : α → List ε → α → Prop
  | nil (a : α) : Run r a [] a
  | cons {a b c : α} {e : ε} {es : List ε} : r a e b → Run r b es c → Run r a (e :: es) c

/-- Where each step from a state with the invariant `inv` is a step of `r`
on the states' images under `abs`, every sequence of events is a run of `r`. -/
theorem foldl_simulates (inv : σ → Prop) (keeps : ∀ s e, inv s → inv (step s e))
    (abs : σ → α) (r : α → ε → α → Prop) (sim : ∀ s e, inv s → r (abs s) e (abs (step s e))) :
    ∀ (es : List ε) (s : σ), inv s → Run r (abs s) es (abs (es.foldl step s))
  | [], s, _ => .nil (abs s)
  | e :: es, s, h => .cons (sim s e h) (foldl_simulates inv keeps abs r sim es (step s e) (keeps s e h))

end Generic

/-! ## The controller -/

/-- The spec's invariant, the subset type `Lights`, as `stoplight::step`
assumes it of its state; the event and the rest do not matter. -/
def Valid (s : State) : Prop := stoplight.step.assumes s .Tick s false

/-- A step keeps the invariant: the guarantees of `stoplight::step` start
with the invariant of its result. -/
theorem step_valid (s : State) (e : Event) (h : Valid s) : Valid (step s e) := by
  obtain ⟨_, _, ⟨hinv, _⟩⟩ := step_meets s e h
  exact hinv

theorem start_valid : Valid START := by simp [Valid, fren_spec]

/-- Every state reachable from `START` is valid. -/
theorem reachable_valid (es : List Event) : Valid (es.foldl step START) :=
  foldl_invariant step Valid step_valid es START start_valid

/-- Each step is a step of the abstract machine on the phases. -/
theorem step_cycles (s : State) (e : Event) (h : Valid s) :
    stoplight.cycle.ensures (phase s) e (phase (step s e)) := by
  obtain ⟨cars, people, waiting, timer⟩ := s
  cases e <;> cases cars <;> cases people <;> cases waiting <;>
    by_cases ht : 1 < timer <;> simp only [Stoplight.step, ht, if_true, if_false] <;>
    simp_all [fren_spec, phase]

/-- The phases of every sequence of events from `START` are a run of the
abstract machine. -/
theorem reachable_cycles (es : List Event) :
    Run stoplight.cycle.ensures (phase START) es (phase (es.foldl step START)) :=
  foldl_simulates step Valid step_valid phase _ step_cycles es START start_valid

end Stoplight
