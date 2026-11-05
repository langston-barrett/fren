namespace Fren.Core

/-- Look up a resolved definition, keeping the original term otherwise.
The first binding wins, including when it shadows another definition.
Shared by matching normalization and the obligations substitution. -/
def definitionValue {T : Type} (defs : Array (String × T)) (name : String) (original : T) : T :=
  ((defs.find? (·.1 == name)).map (·.2)).getD original

end Fren.Core
