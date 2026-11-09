module

public import FrenThirToMirTests.Support

public section
namespace FrenThirToMirTests
open FrenMir FrenModule FrenEval

private def s1Cases : IO Unit := do
  let c ← load s1
  let t := c.theory
  require (t.source == c.admitted.typed && t.source.resolved.document.emit == s1) "full typed/source retention"
  require (requestsMatch t s1Expected) "S1 six unresolved requests"
  require (declarationIds t == #["Light", "next", "wait", "cycles", "waits", "wrong"].map key) "S1 declaration order"
  let some next := function t "next" | throw (IO.userError "next missing")
  let some wait := function t "wait" | throw (IO.userError "wait missing")
  require (next.signature.result == .enum (key "Light") &&
    next.signature.parameters.map (·.type) == #[.enum (key "Light")] &&
    wait.signature.parameters.map (·.type) == #[.enum (key "Light"), .int] &&
    wait.signature.result == .int && slots wait.definition.context == ["base", "l"]) "signature types/slots"
  require (match next.definition.expression, wait.definition.expression with
    | .matchE .., .matchE .. => true | _, _ => false) "match must stay match"
  for ctor in ["Red", "Amber", "Green"] do
    require (value (outcome c "cycles" #[light ctor] (some "back")) (.bool true)) "cycles concrete"
  require (value (outcome c "wait" #[light "Red", .int 70]) (.int 100)) "wait positional arguments"
  require (value (outcome c "waits" #[light "Red", .int 101] (some "bounded")) (.bool false) &&
    value (outcome c "waits" #[light "Red", .int 101] (some "at_most")) (.bool false)) "bounded matters"
  require (value (outcome c "wrong" #[light "Amber"] (some "never_red")) (.bool false)) "never_red false control"
  -- Call references and constructor owners use canonical identities, not names.
  require (t.source.resolved.references.any (fun r => r.target == .item (key "next")) &&
    t.source.resolved.references.any (fun r => r.target == .item ((key "Light").named "Red"))) "canonical references"

private def blockCases : IO Unit := do
  let c ← load (blocksSource 7)
  let t := c.theory
  require (blocksAudit t) "ordered multi-owner/empty blocks"
  let enums := t.declarations.filterMap fun d => match d with
    | .enumeration e => some e | _ => none
  require (enums.map (·.id) == #[key "Light", key "Other"] &&
    enums.map (fun e => e.constructors.map Prod.fst) ==
      #[#[((key "Light").named "Red"), ((key "Light").named "Green")],
        #[((key "Other").named "Red"), ((key "Other").named "Green")]]) "nominal spelling ownership/order"
  require (value (outcome c "unused" #[.int 3]) (.int 6)) "unused definition and shadowed let slots"
  require (value (outcome c "multi" #[.int 11, .bool true] (some "first")) (.bool true) &&
    value (outcome c "multi" #[.int 11, .bool true] (some "later")) (.bool false)) "later assumption concrete"
  require (value (outcome c "only" #[] (some "impossible")) (.bool false)) "contradictory assumptions stay requested"
  require (value (outcome c "vacuous" #[] (some "no")) (.bool false) &&
    value (outcome c "vacuous" #[] (some "contradiction")) (.bool false)) "vacuous validity still needs separate satisfiability"
  let edits : Array (Theory → Theory) := #[
    fun q => {q with requests := q.requests.modify 1 (fun r => {r with assumptions := r.assumptions.extract 0 1})},
    fun q => {q with requests := q.requests.modify 1 (fun r => {r with owner := key "other"})},
    fun q => {q with requests := q.requests.modify 1 (fun r => {r with context := r.context.reverse})},
    fun q => {q with requests := q.requests.modify 1 (fun r => {r with parameters := r.parameters.reverse})},
    fun q => {q with requests := q.requests.modify 1 (fun r => {r with assumptions := r.assumptions ++
      (match r.question with | .validity g => #[g] | _ => #[])})},
    fun q => {q with requests := q.requests.extract 0 8},
    fun q => {q with declarations := q.declarations.extract 1 q.declarations.size},
    fun q => {q with declarations := q.declarations.reverse},
    fun q => {q with requests := q.requests.modify 1 (fun r => {r with demand := #[]})}]
  for edit in edits do require (!blocksAudit (edit t)) "raw expected audit accepted an omission/context/role/order mutant"
  for changed in [(blocksSource 7).replace "assume later: x <= 10" "",
      (blocksSource 7).replace "expect first:" "assume first:",
      (blocksSource 7).replace "expect other(x: Int) { assume own: x > 20 expect goal: x > 10 }" ""] do
    let mutant ← load changed
    require (!blocksAudit mutant.theory) "independent audit accepted source role/member/owner mutant"

/-- Every demanded failure below points to this first div's exact source
occurrence, including a let-slot read far from its definition. -/
def demandSource : String := "mod skeleton\n\
  fn partial(x: Int): Int := let y := 1 div 0 in y\n\
  fn unused(x: Int): Int := let y := 1 div 0 in x\n\
  fn guard(d: Int): Int := let y := 1 div d in if d != 0 then y else 0\n\
  fn lazyAnd(b?: Bool): Bool := b? and (1 div 0 = 0)\n\
  fn lazyOr(b?: Bool): Bool := b? or (1 mod 0 = 0)\n\
  fn strictIff(b?: Bool): Bool := b? iff (1 div 0 = 0)\n\
  fn strictEq(b?: Bool): Bool := b? = (1 div 0 = 0)\n\
  fn first(x: Int, y: Int): Int := x\n\
  fn call(x: Int): Int := first(x, partial(x))\n\
  expect demand(b?: Bool) { expect goal: let x := 1 div 0 in b? assume later: b? or (1 div 0 = 0) }\n"

private def localAudit (t : Theory) : Bool :=
  t.source.resolved.references.any fun r =>
    r.written.anchor.text == "y" && r.role == .expression && r.target == .local 0 &&
    r.context.map (·.text) == ["y", "x"]

private def demandCases : IO Unit := do
  let c ← load demandSource
  require (localAudit c.theory) "let source slot 0 missing"
  let preceding :=  "mod skeleton\nfn partial(x: Int): Int := let y := 1 "
  let some expected := FrenSource.Span.checked ⟨101⟩ preceding.utf8ByteSize
      (preceding.utf8ByteSize + 3) demandSource.utf8ByteSize
    | throw (IO.userError "bad raw expected span")
  for (name, args) in [("partial", #[Value.int 4]), ("call", #[.int 4])] do
    require (match outcome c name args with
      | .error (.undefined span op) => span == expected && op == .div | _ => false) "exact original failure span/operator"
  let demands := #[("unused", #[Value.int 4], Value.int 4), ("guard", #[.int 0], .int 0),
    ("guard", #[.int 1], .int 1), ("lazyAnd", #[.bool false], .bool false),
    ("lazyOr", #[.bool true], .bool true)]
  for (name, args, expected) in demands do require (value (outcome c name args) expected) "demand result"
  for (name, args) in [("lazyAnd", #[Value.bool true]), ("lazyOr", #[.bool false]),
      ("strictIff", #[.bool false]), ("strictEq", #[.bool false])] do
    require (match outcome c name args with | .error (.undefined ..) => true | _ => false) "strict demanded outcome"
  require (match outcome c "partial" #[.bool true] with | .error (.invalid ..) => true | _ => false) "invalid kept distinct"
  require (match outcome c "partial" #[.int 0] none 0 with | .error (.exhausted ..) => true | _ => false) "exhaustion kept distinct"
  let expectedRequests : Array ExpectedRequest := #[
    ⟨"demand", none, #["later"], #["b?"], ["b?"]⟩,
    ⟨"demand", some "goal", #["later"], #["b?"], ["b?"]⟩]
  require (requestsMatch c.theory expectedRequests) "demand roots/late assumption requests"
  require (value (outcome c "demand" #[.bool false] (some "goal")) (.bool false) &&
    value (outcome c "demand" #[.bool true] (some "later")) (.bool true) &&
    (match outcome c "demand" #[.bool false] (some "later") with
      | .error (.undefined ..) => true | _ => false)) "undefined assumption cannot filter as false"
  let edited : Theory := {c.theory with source := {c.theory.source with resolved :=
    {c.theory.source.resolved with references := c.theory.source.resolved.references.map fun r =>
      if r.written.anchor.text == "y" && r.role == .expression then {r with target := .local 1} else r}}}
  require (!localAudit edited) "raw slot expectation accepted local-index substitution"
  let guarded ← load (demandSource.replace "if d != 0" "if d = 0")
  require (!value (outcome guarded "guard" #[.int 0]) (.int 0)) "guard alteration escaped expected outcome"

private def rejectionCases : IO Unit := do
  let bad := #["mod skeleton\nfn f(x: Int): Int := (", "mod skeleton\nfn f(x: Int): Int := false",
    "mod skeleton\nfn f(x: Int): Int := absent", "mod skeleton\nfn f(x: Int): Int := f(x)",
    "mod skeleton\nenum E { A, B }\nfn f(e: E): Int := match e { E::A => 0 }"]
  for source in bad do
    let .error original := FrenThirDesugar.fromSource ⟨101⟩ source
      | throw (IO.userError "invalid fixture admitted")
    let .error actual := FrenThirToMir.fromSource ⟨101⟩ source
      | throw (IO.userError "MIR admitted invalid source")
    require (reprStr actual == reprStr original) "admission diagnostic changed"
  let c ← load s1
  require (!(FrenThirDesugar.fromResolved {c.admitted.input with references := #[]}).isOk) "edited resolution admitted"

def runCases : IO Unit := do
  s1Cases
  blockCases
  demandCases
  rejectionCases
  IO.println "MIR cases: S1 6 requests, ordered blocks 11, demand 2; 9 output and 3 source mutants rejected; 5 invalid sources and edited resolution rejected; exact source failure probes passed"

end FrenThirToMirTests
