-- keep-sorted start
import FrenCore.Check.Contracts
import FrenCore.Definitions
-- keep-sorted end

/-!
# Terms used for matching

Definition references are distinct from the symbols of applications. A
resolved `let`, `where`, `out :=` or constant can therefore be expanded
without unfolding a function with the same spelling. Definitions are in
reverse dependency order; each value sees only the tail before it.
-/

namespace Fren.Core.Matching

/-- Resolved syntax. An atom includes its type and resolved identity; `app`
keeps its head opaque. `nil` and `cons` represent any number of arguments.
Only `ref` stands for a definition. -/
inductive Term where
  | atom (symbol : String)
  | ref (name : String)
  | app (symbol : String) (args : Term)
  | nil
  | cons (head tail : Term)
  deriving Inhabited, DecidableEq, Repr

/-- Traverse the small reference model; application symbols stay opaque. -/
def Term.expandDefinitions (lookup : String → Term → Term) : Term → Term
  | .ref n => lookup n (.ref n)
  | .app f args => .app f (args.expandDefinitions lookup)
  | .cons a b => .cons (a.expandDefinitions lookup) (b.expandDefinitions lookup)
  | t => t

instance : DefinitionSyntax String Term := ⟨Term.expandDefinitions⟩

/-- Expand references using already normalized definitions. -/
def normalize {K T : Type} [BEq K] [DefinitionSyntax K T] (defs : List (K × T)) : T → T :=
  DefinitionSyntax.expand (definitionValue defs.toArray)

/-- Normalize each definition in its own scope, before it can be shadowed. -/
def definitions {K T : Type} [BEq K] [DefinitionSyntax K T] : List (K × T) → List (K × T)
  | [] => []
  | (n, v) :: rest =>
    let ds := definitions rest
    (n, normalize ds v) :: ds

/-- Syntactic equality after expanding definitions; no evaluation or
function unfolding participates. -/
def same {K T : Type} [BEq K] [BEq T] [DefinitionSyntax K T]
    (defs : List (K × T)) (a b : T) : Bool :=
  let ds := definitions defs
  normalize ds a == normalize ds b

/-- The vertices of a finite candidate graph, including isolated query
applications. Repetitions do not increase the bound. -/
def vertices {T : Type} [BEq T] (written : List T) (inside : List (T × T)) : List T :=
  (written ++ inside.map Prod.fst ++ inside.map Prod.snd).eraseDups

/-- Applications mentioned by the facts of `a`, in the candidate graph. -/
def successors {T : Type} [BEq T] (inside : List (T × T)) (a : T) : Id (Unit × List T) :=
  pure ((), (inside.filter (·.1 == a)).map Prod.snd)

/-- Run today's shared closure traversal at a bound computed from the
finite graph, returning the rounds passed to `closeApps` with its result.
The binding proves that this cannot run out of rounds. -/
def closure {T : Type} [BEq T] [LawfulBEq T] (written : List T) (inside : List (T × T))
    (brings : T → Bool) : Nat × Option (List (T × Unit)) :=
  let rounds := (vertices written inside).length + 1
  let roots := (written.filter brings).eraseDups
  (rounds, (closeApps brings (successors inside) rounds roots roots []).run)

end Fren.Core.Matching
