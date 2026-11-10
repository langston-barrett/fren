module

public import FrenWalking
public import FrenTextTests

public section
namespace FrenHirToThirTests
open FrenHirToThir

/-- Test adapter only: production checkWalkingSource makes every decision. -/
@[fren_text_tests "test/FrenWalking"]
def walkingRunner : Fren.TextTests.Runner := .of
  (fun raw => if raw.isEmpty then .ok () else .error "empty context required")
  fun (_ : Unit) source => pure <| .ok <|
    match checkWalkingSource ⟨61⟩ source with
    | .ok t => s!"static accepted; functions={t.signatures.size}; bodies={t.bodies.size}"
    | .error (.typing d) => "typing: " ++ d.headline
    | .error (.validation (.coverage _ owner missing repeated)) =>
      s!"coverage {owner.render}; missing={missing.size}; repeated={repeated.size}"
    | .error (.validation (.cycle _ path)) =>
      "cycle " ++ " -> ".intercalate (path.toList.map (·.render))
    | .error (.validation (.termination _ group reason)) =>
      "termination " ++ ", ".intercalate (group.toList.map (·.render)) ++ ": " ++
        match reason with
        | .noParameters function => s!"{function.render} has no parameter"
        | .unguarded => "some call is not guarded under every choice of decreasing parameters"
    | .error (.validation (.invalidMetadata _)) => "invalid typed metadata"

end FrenHirToThirTests
