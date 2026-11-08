module

public import FrenHirToThirTests.Support

public section
namespace FrenHirToThirTests
open FrenAst FrenModule FrenHirToThir FrenExpr

/-- Expectations are written independently of the production operator tables.
Every matrix cell also runs the entire admitted traversal with real enum IDs. -/
def runOperators : IO Unit := do
  let families : Array (String × String × FrenExpr.Ty) :=
    #[("Bool", "true", .bool), ("Int", "1", .int),
      ("Light", "Light::Red", .enum (key "Light")),
      ("Signal", "Signal::Red", .enum (key "Signal"))]
  let prelude := "mod m\nenum Light { Red, Green }\nenum Signal { Red, Green }\n"
  let ops : List (String × BinaryOp × Nat) :=
    [("+", .add, 0), ("-", .sub, 0), ("*", .mul, 0), ("div", .div, 0), ("mod", .mod, 0),
     ("<", .lt, 1), ("<=", .le, 1), (">", .gt, 1), (">=", .ge, 1),
     ("and", .and, 2), ("or", .or, 2), ("iff", .iff, 2), ("=", .eq, 3), ("!=", .ne, 3)]
  let mut accepted := 0
  let mut failed := 0
  for (text, op, category) in ops do
    for i in [:families.size] do
      for j in [:families.size] do
        let some left := families[i]? | throw (IO.userError "matrix left")
        let some right := families[j]? | throw (IO.userError "matrix right")
        let good := if category < 2 then i == 1 && j == 1
          else if category == 2 then i == 0 && j == 0 else i == j
        let expected : FrenExpr.Ty := if category == 0 then .int else .bool
        require (binary op left.2.2 right.2.2 == if good then some expected else none)
          s!"primitive matrix {text} {i} {j}"
        let result := if category == 0 then "Int" else "Bool"
        let source := prelude ++ s!"fn f(x: {left.1}, y: {right.1}): {result} := x {text} y"
        if good then
          let t ← typed source
          require ((t.bodies[0]?).map (·.type) == some expected && localsRetained t)
            s!"traversal matrix result {text} {i} {j}"
          accepted := accepted + 1
        else
          let d ← rejected source
          require (d.code == some "F0304") s!"matrix mismatch code {text} {i} {j}"
          failed := failed + 1
  for (text, op, index) in [("-", UnaryOp.neg, 1), ("not ", .not, 0)] do
    for i in [:families.size] do
      let some f := families[i]? | throw (IO.userError "unary matrix")
      let good := i == index
      require (unary op f.2.2 == if good then some f.2.2 else none) "unary primitive matrix"
      let out := if index == 0 then "Bool" else "Int"
      let source := prelude ++ s!"fn f(x: {f.1}): {out} := {text}x"
      if good then
        let t ← typed source
        require ((t.bodies[0]?).map (·.type) == some f.2.2) "unary traversal result"
        accepted := accepted + 1
      else
        discard <| rejected source
        failed := failed + 1
  require (accepted == 22 && failed == 210) s!"matrix census {accepted}/{failed}"
  -- Builtin/nominal equality and display-collision controls use real ItemIds.
  let flat := FrenBase.ItemId.root.named "m.Light"
  let nested := key "Light"
  require (flat.render == nested.render && flat != nested) "identity display collision"
  require (!(ValueType.enum flat).compatible (.enum nested)) "render-string identity mutant"
  require (!(ValueType.bool : FrenExpr.Ty).compatible (.enum (FrenBase.ItemId.root.named "Bool")))
    "builtin/enum conflation mutant"
  IO.println s!"typing operators: {accepted} successes, {failed} rejections; all 2 unary/14 binary × builtin/distinct-enum cells"

end FrenHirToThirTests
