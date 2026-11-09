module

public import FrenEvalTests.Support

public section
namespace FrenEvalTests
open FrenEval

private def walkingExample : IO Unit := do
  let p ← load s1
  require (p.typed.resolved.document.emit == s1) "S1 source changed"
  require (hasValue (result p "next" #[light "Amber"]) (light "Red")) "S1 next(Amber)"
  require (hasValue (result p "wait" #[light "Red", .int 70]) (.int 100)) "S1 wait(Red,70)"
  require (hasValue (result p "wrong" #[light "Amber"] (some "never_red")) (.bool false))
    "S1 never_red must be false at Amber"
  for ctor in ["Red", "Amber", "Green"] do
    require (hasValue (result p "cycles" #[light ctor] (some "back")) (.bool true)) "S1 cycle"
    require (hasValue (result p "waits" #[light ctor, .int 70] (some "at_most")) (.bool true))
      "S1 bound concrete instance"
  let .ok assumption := evaluate p ⟨key "waits", some "bounded"⟩ #[light "Red", .int 101]
    | throw (IO.userError "S1 assumption missing")
  require (assumption.body.member.map (·.kind) == some .assume &&
    hasValue assumption.outcome (.bool false)) "assumption was discarded/coerced to verdict"
  let .ok failing := evaluate p ⟨key "wrong", some "never_red"⟩ #[light "Amber"]
    | throw (IO.userError "S1 expectation missing")
  require (failing.body.member.map (·.kind) == some .expect &&
    failing.body.owner == key "wrong" &&
    failing.body.member.map (·.label.text) == some "never_red" &&
    (failing.body.expression.tokens.head?).map (·.span.file) == some ⟨101⟩)
    "expectation source identity"
  for args in [#[], #[light "Red"], #[light "Red", .bool true],
      #[.enum (key "Light") ((key "Light").named "Invented"), .int 70],
      #[.enum (key "Signal") ((key "Signal").named "Red"), .int 70],
      #[light "Red", .int 70, .int 1]] do
    require (isInvalid (result p "wait" args)) "invalid external arguments accepted"
  require (isInvalid (result p "missing")) "missing body"
  require (isExhausted (result p "next" #[light "Amber"] none 0)) "zero depth became false/undefined"
  -- Re-admit the deliberately changed source: a real typed operator mutant.
  let mutant ← load (s1.replace "base + 30" "base - 30")
  require (hasValue (result mutant "wait" #[light "Red", .int 70]) (.int 40) &&
    !hasValue (result mutant "wait" #[light "Red", .int 70]) (.int 100)) "addition mutant survived"
  let equalityMutant ← load (s1.replace "next(l) != Light::Red" "next(l) = Light::Red")
  require (hasValue (result equalityMutant "wrong" #[light "Amber"] (some "never_red")) (.bool true))
    "inequality mutant survived"

private def demandCases : IO Unit := do
  let p ← load "mod skeleton\nenum Light { Red, Amber, Green }\n\
    fn q(x: Int, y: Int): Int := x div y\n\
    fn r(x: Int, y: Int): Int := x % y\n\
    fn lazy(b?: Bool): Int := if b? then 7 else 9 div 0\n\
    fn arm(l: Light): Int := match l { Light::Red => 5, Light::Amber => 1 div 0, Light::Green => 6 }\n\
    fn conjunction(b?: Bool): Bool := b? and (1 div 0 = 0)\n\
    fn disjunction(b?: Bool): Bool := b? or (1 % 0 = 0)\n\
    fn first(x: Int, y: Int): Int := x\n\
    fn argument(dummy: Int): Int := first(3, 1 div 0)\n\
    fn order(dummy: Int): Int := first(1 div 0, 2 % 0)\n\
    fn binaryOrder(dummy: Int): Int := (1 div 0) + (2 % 0)\n\
    fn unusedLet(dummy: Int): Int := let x := 1 div 0 in 3\n\
    expect partial() { assume a: 1 div 0 = 0 expect e: 1 % 0 = 0 }"
  for (a, b, q, r) in [(-7, 3, -3, 2), (7, -3, -2, 1), (-7, -3, 3, 2), (7, 3, 2, 1)] do
    require (hasValue (result p "q" #[.int a, .int b]) (.int q) &&
      hasValue (result p "r" #[.int a, .int b]) (.int r)) "Euclidean signed division"
  for name in ["q", "r"] do
    require (isUndefined (result p name #[.int (-7), .int 0])) "zero divisor defaulted"
  require (hasValue (result p "lazy" #[.bool true]) (.int 7) &&
    isUndefined (result p "lazy" #[.bool false])) "if demanded/unselected"
  require (hasValue (result p "arm" #[light "Red"]) (.int 5) &&
    isUndefined (result p "arm" #[light "Amber"])) "match demanded/unselected"
  require (hasValue (result p "conjunction" #[.bool false]) (.bool false) &&
    hasValue (result p "disjunction" #[.bool true]) (.bool true)) "skipped Boolean right operand"
  require (isUndefined (result p "conjunction" #[.bool true]) &&
    isUndefined (result p "disjunction" #[.bool false])) "demanded Boolean right operand"
  require (hasValue (result p "unusedLet") (.int 3)) "unused undefined let"
  require (isUndefined (result p "argument")) "ordinary argument must stay strict"
  require (isInvalid (result p "unusedLet" #[.bool true]) &&
    isInvalid (result p "conjunction" #[.int 0])) "lazy demand bypassed argument validation"
  for member in ["a", "e"] do
    require (isUndefined (result p "partial" #[] (some member))) "partial check became verdict"
  let .error (.undefined span .div) := result p "q" #[.int 1, .int 0]
    | throw (IO.userError "undefined lost operator identity")
  require (span.file == ⟨101⟩ && span.start < span.stop) "undefined lost source span"
  for name in ["order", "binaryOrder"] do
    let .error (.undefined _ .div) := result p name
      | throw (IO.userError "written operand/argument order changed")

-- Independent expected outcomes from evaluation.let.lazy, evaluation.and/or,
-- and semantics.derived.iff; none is a comparison of two evaluator calls.
private def nestedDemandCases : IO Unit := do
  let p ← load "mod skeleton\n\
    fn guarded(d: Int): Int := let x := 1 div d in if d != 0 then x else 0\n\
    fn used(dummy: Int): Int := let x := 1 div 0 in x\n\
    fn nested(dummy: Int): Int := let x := 1 div 0 in let y := x + 1 in 4\n\
    fn nestedUsed(dummy: Int): Int := let x := 1 div 0 in let y := x + 1 in y\n\
    fn shadowUnused(dummy: Int): Int := let x := 1 div 0 in let x := 8 in x\n\
    fn shadowUsed(x: Int): Int := let y := x + 1 in let x := 100 in y\n\
    fn shadowFailure(dummy: Int): Int := let x := 1 div 0 in let y := x in let x := 8 in y\n\
    fn repeated(x: Int): Int := let y := x + 1 in y + y\n\
    fn letAnd(b?: Bool): Bool := let x := 1 div 0 = 0 in b? and x\n\
    fn letOr(b?: Bool): Bool := let x := 1 % 0 = 0 in b? or x\n\
    fn eq(b?: Bool): Bool := b? = (1 div 0 = 0)\n\
    fn ne(b?: Bool): Bool := b? != (1 div 0 = 0)\n\
    fn strictIff(b?: Bool): Bool := b? iff (1 div 0 = 0)\n\
    fn leftAnd(dummy: Int): Bool := (1 div 0 = 0) and false\n\
    fn leftOr(dummy: Int): Bool := (1 div 0 = 0) or true\n\
    fn inner(d: Int): Int := let x := 1 div d in if d != 0 then x else 0\n\
    fn caller(d: Int): Int := let x := 99 in inner(d)\n\
    expect checks(b?: Bool) {\n\
      assume lazy_and: b? and (1 div 0 = 0)\n\
      expect lazy_or: b? or (1 % 0 = 0)\n\
      assume lazy_let: let x := 1 div 0 in true\n\
      expect guarded_let: let x := 1 div 0 in if b? then x = 0 else true\n\
    }"
  for (name, args, expected) in [
      ("guarded", #[.int 0], .int 0), ("guarded", #[.int 1], .int 1),
      ("nested", #[.int 0], .int 4), ("shadowUnused", #[.int 0], .int 8),
      ("shadowUsed", #[.int 10], .int 11), ("repeated", #[.int 10], .int 22),
      ("caller", #[.int 0], .int 0), ("caller", #[.int 1], .int 1),
      ("letAnd", #[.bool false], .bool false), ("letOr", #[.bool true], .bool true)] do
    require (hasValue (result p name args none 100) expected) s!"lazy binding {name}"
  for name in ["used", "nestedUsed", "shadowFailure", "leftAnd", "leftOr"] do
    require (isUndefined (result p name #[.int 0] none 100)) s!"demanded binding/left {name}"
  for b in [false, true] do
    for name in ["eq", "ne", "strictIff"] do
      require (isUndefined (result p name #[.bool b] none 100)) s!"strict Boolean {name}"
  require (isUndefined (result p "letAnd" #[.bool true] none 100) &&
    isUndefined (result p "letOr" #[.bool false] none 100)) "demanded let Boolean"
  for (member, b, expected) in [("lazy_and", false, false), ("lazy_or", true, true),
      ("lazy_let", false, true), ("guarded_let", false, true)] do
    let .ok e := evaluate p ⟨key "checks", some member⟩ #[.bool b] 100
      | throw (IO.userError s!"missing check {member}")
    require (hasValue e.outcome (.bool expected) &&
      e.body.member.map (·.kind) == some (if member == "lazy_and" || member == "lazy_let"
        then .assume else .expect) &&
      e.body.member.map (·.label.text) == some member &&
      (e.body.expression.tokens.head?).map (·.span.file) == some ⟨101⟩)
      s!"check demand/role/provenance {member}"
  for (member, b) in [("lazy_and", true), ("lazy_or", false), ("guarded_let", true)] do
    require (isUndefined (result p "checks" #[.bool b] (some member) 100)) s!"demanded check {member}"
  -- The complete definition failure survives storage and shadowing unchanged.
  for name in ["used", "nestedUsed", "shadowFailure"] do
    let some body := p.typed.bodies.find? (·.owner == key name)
      | throw (IO.userError "missing let body")
    let some token := body.expression.tokens.find? (·.text == "div")
      | throw (IO.userError "missing definition operator")
    let .error failure := result p name #[.int 0] none 100
      | throw (IO.userError s!"missing stored failure {name}")
    require (failure == .undefined token.span .div) s!"stored failure lost complete source identity {name}"

private def depthCases : IO Unit := do
  let p ← load "mod skeleton\n\
    fn unused(dummy: Int): Int := let x := (((1 div 0))) in 7\n\
    fn used(dummy: Int): Int := let x := (((1 div 0))) in x\n\
    fn conjunction(dummy: Int): Bool := false and (((1 div 0 = 0)))\n\
    fn disjunction(dummy: Int): Bool := true or (((1 div 0 = 0)))\n\
    fn demanded(dummy: Int): Bool := true and (((1 div 0 = 0)))"
  for (name, expected) in [("unused", .int 7), ("conjunction", .bool false), ("disjunction", .bool true)] do
    require (hasValue (result p name #[.int 0] none 2) expected) s!"skipped exhausted outcome {name}"
    require (isExhausted (result p name #[.int 0] none 1)) s!"body/left depth {name}"
  for name in ["used", "demanded"] do
    require (isExhausted (result p name #[.int 0] none 2)) s!"demanded depth {name}"
    require (isUndefined (result p name #[.int 0] none 100)) s!"demanded semantic failure {name}"

private def bindingCases : IO Unit := do
  let p ← load "mod skeleton\n\
    fn difference(first: Int, second: Int): Int := first - second\n\
    fn shadow(x: Int): Int := let x := x + 1 in let x := x + 2 in x\n\
    fn siblings(x: Int): Int := (let x := 2 in x) + x\n\
    fn caller(x: Int): Int := let first := 100 in difference(x, 3)\n\
    fn chain(x: Int): Int := difference(difference(x, 2), difference(8, 3))"
  for (name, expected) in [("shadow", 13), ("siblings", 12), ("caller", 7), ("chain", 3)] do
    require (hasValue (result p name #[.int 10]) (.int expected)) s!"binding/call {name}"
  let nominal ← load "mod skeleton\nenum Light { Red }\nenum Signal { Red }\n\
    fn id(l: Light): Light := l\nfn eq(l: Light): Bool := l = Light::Red"
  require (isInvalid (result nominal "id" #[.enum (key "Light") ((key "Signal").named "Red")]))
    "constructor from another declared enum accepted"
  require (isInvalid (result nominal "id" #[.enum (key "Signal") ((key "Signal").named "Red")]))
    "wrong nominal type accepted"
  require (hasValue (result nominal "eq" #[light "Red"]) (.bool true)) "nominal equality"

private def operatorCases : IO Unit := do
  -- Independent concrete expectations exercise the actual typed consumer,
  -- rather than only comparing two copies of an operator table.
  let cases : List (String × Value) :=
    [("70 + 30", .int 100), ("70 - 30", .int 40), ("7 * (-3)", .int (-21)),
     ("-7", .int (-7)), ("not true", .bool false), ("not false", .bool true),
     ("2 < 3", .bool true), ("3 < 2", .bool false), ("2 <= 2", .bool true),
     ("3 <= 2", .bool false), ("3 > 2", .bool true), ("2 > 3", .bool false),
     ("2 >= 2", .bool true), ("2 >= 3", .bool false), ("2 = 2", .bool true),
     ("2 = 3", .bool false), ("2 != 3", .bool true), ("2 != 2", .bool false),
     ("true = false", .bool false), ("true != false", .bool true)]
  for (expression, expected) in cases do
    let p ← load s!"mod skeleton\nfn probe(dummy: Int): {expected.type.display} := {expression}"
    require (hasValue (result p "probe") expected) s!"operator {expression}"
  for (a, b, conj, disj, equiv) in [(false, false, false, false, true),
      (false, true, false, true, false), (true, false, false, true, false),
      (true, true, true, true, true)] do
    for (op, expected) in [("and", conj), ("or", disj), ("iff", equiv)] do
      let p ← load s!"mod skeleton\nfn probe(dummy: Int): Bool := {a} {op} {b}"
      require (hasValue (result p "probe") (.bool expected)) s!"Boolean truth table {a} {op} {b}"

private def rejectedCases : IO Unit := do
  for source in [
    "mod skeleton\nfn f(x: Int): Int := false",
    "mod skeleton\nfn f(x: Int): Int := f(x)",
    "mod skeleton\nenum E { A, B }\nfn f(e: E): Int := match e { E::A => 0 }",
    "mod skeleton\nfn f(x: Int): Int := if true then 1 else false",
    "mod skeleton\nfn f(x: Int): Int := x\nfn g(dummy: Int): Int := f",
    "mod skeleton\nfn f(dummy: Int): Int := missing",
    "mod skeleton\nfn f(dummy: Int): Int := _"] do
    require (!(fromSource ⟨101⟩ source).isOk) s!"unadmitted source accepted: {source}"
  let p ← load s1
  require (!(fromResolved {p.input with references := #[]}).isOk) "edited producer accepted"
  require (!(FrenHirToThir.check p.input).toOption.any (fun t => t.bodies.isEmpty))
    "arbitrary empty typed body table treated as produced"

def runCases : IO Unit := do
  walkingExample
  demandCases
  nestedDemandCases
  depthCases
  bindingCases
  operatorCases
  rejectedCases
  IO.println "walking evaluator: S1, lazy let/and/or, strict controls, depth, Euclidean arithmetic, bindings, nominal input and producer controls passed"

end FrenEvalTests
