namespace Fren.Core

/-- Look up a resolved definition, keeping the original term otherwise.
The first binding wins, including when it shadows another definition.
Shared by matching normalization and the obligations substitution. -/
def definitionValue {K T : Type} [BEq K] (defs : Array (K × T)) (name : K) (original : T) : T :=
  ((defs.find? (·.1 == name)).map (·.2)).getD original

/-- The reference-bearing nodes and recursive traversal of a resolved syntax.
The callback makes definition lookup common to all matching term models. -/
class DefinitionSyntax (K : outParam Type) (T : Type) where
  expand : (K → T → T) → T → T

end Fren.Core
