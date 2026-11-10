module

public import FrenFlatToLirTests.Verification

public section
namespace FrenFlatToLirTests
open FrenLir FrenEval

private def walking : IO Unit := do
  let c ← load walkingSource
  let p := c.program
  require (p.mir.source.resolved.document.emit == walkingSource) "walking lossless source"
  require (p.declarations.map (fun d => match d with
    | .enumeration e => e.id | .function s _ => s.id | .block b _ => b.owner) ==
      #[key "Light", key "wait", key "waits"]) "walking declaration order"
  require (p.requests.size == 2 && p.requests.map (fun r => labels r.assumptions) ==
    #[#["bounded"], #["bounded"]] && p.requests.map (fun r => labels r.demand) ==
    #[#["bounded"], #["bounded", "limit"]]) "walking independent request roots"
  require (p.requests.all (fun r => r.source.context.map (·.1.text) == ["base", "l"] &&
    r.source.parameters.map (·.written.name.text) == #["l", "base"])) "walking slot order"
  for (ctor, base, expected) in [("Red", 100, 130), ("Green", 100, 100), ("Red", 101, 131)] do
    require (agrees c "wait" #[light ctor, .int base] (some (.int expected))) "walking lowered definition"
  require (agrees c "waits" #[light "Red", .int 100] (some (.bool true)) (some "limit") &&
    agrees c "waits" #[light "Red", .int 101] (some (.bool false)) (some "limit") &&
    agrees c "waits" #[light "Red", .int 101] (some (.bool false)) (some "bounded")) "walking function symbols and bound"
  let some b := body? p "wait" | throw (IO.userError "missing wait")
  require (b.source.context.map (·.1.text) == ["base", "l"]) "definition parameter context"
  let changed ← load (walkingSource.replace "base + 30" "base + 31")
  require (!agrees changed "wait" #[light "Red", .int 100] (some (.int 130))) "definition mutant escaped"

private def controls : IO Unit := do
  let c ← load demandSource
  require (demandAudit c) "demand/context/native expected controls"
  require (match sourceOutcome c "unused" #[.int 0], sourceOutcome c "lazyAnd" #[.bool false] with
    | .ok (.int 0), .ok (.bool false) => true | _, _ => false)
    "raw lazy value strategy remains distinct from source verification"
  let some unused := body? c.program "unused" | throw (IO.userError "missing unused definition")
  require (!(nonzeroLeaves unused).isEmpty && c.program.requests.all (fun r => r.source.owner != key "unused"))
    "unused definition retains its own obligation outside request reachability"

  verificationMutants c
  require (structuralAudit c) "static primitive obligations and exact guard scopes"
  let enums := c.program.declarations.filterMap fun d => match d with
    | .enumeration e => some (e.id, e.constructors.map Prod.fst) | _ => none
  require (enums == #[(key "Light", #[((key "Light").named "Red"), ((key "Light").named "Green")]),
    (key "Other", #[((key "Other").named "Red"), ((key "Other").named "Green")])]) "nominal ownership/order"
  let unresolved ← load "mod lir_walk\nfn unknownDomain(x: Int): Int := x\nfn uses(x: Int): Int := unknownDomain(x)"
  let some unresolvedBody := body? unresolved.program "uses" | throw (IO.userError "missing unresolved symbol body")
  require (observe 400 symbols [(.int 1, true)] unresolvedBody.term.defined == none)
    "uninterpreted definition predicate must stay unresolved in the finite debug probe"
  require (match sourceOutcome c "unused" #[.int 0] none 0 with | .error (.exhausted ..) => true | _ => false)
    "operational exhaustion lost"
  require (match sourceOutcome c "guarded" #[.bool false] with | .error (.invalid ..) => true | _ => false)
    "invalid arguments lost"
  -- Concrete AST-origin context for a reused let slot, not only a slot count.
  let some shadow := body? c.program "shadow" | throw (IO.userError "missing shadow")
  require (shadow.source.occurrences.any (fun o => o.context.map (·.1.text) == ["x", "x", "x"]))
    "nested shadow lexical identities"
  let some selected := body? c.program "selected" | throw (IO.userError "missing selected")
  require (Term.infer 10000 c.program.mir.source selected.source.context selected.term.defined == some .bool)
    "actual selected-arm domain scope"
  let edits : Array (FrenLir.Program → FrenLir.Program) := #[
    fun p => {p with requests := p.requests.reverse},
    fun p => {p with requests := p.requests.modify 1 (fun r => {r with assumptions := #[]})},
    fun p => {p with requests := p.requests.modify 1 (fun r => {r with demand := #[]})},
    fun p => {p with requests := p.requests.modify 1 (fun r => {r with source := {r.source with owner := key "other"}})},
    fun p => {p with declarations := p.declarations.reverse}]
  for edit in edits do require (!(edit c.program).wellFormed) "scope/retention certificate accepted mutant"
  for source in [demandSource.replace "if d != 0 then n div d" "if d = 0 then n div d",
      demandSource.replace "assume later:" "expect later:",
      demandSource.replace "Light::Green => 0" "Light::Green => 1 div 0"] do
    let changed ← load source
    require (!demandAudit changed) "actual source mutant escaped independent declarative audit"
  let t := c.program.mir.source
  let ctx := shadow.source.context
  require (Term.infer 100 t ctx (.local .int 999 .value) == none &&
    Term.infer 100 t ctx (.constructor (key "Other") ((key "Light").named "Red")) == none)
    "dangling slot/nominal owner controls"
  -- A constructor has a sort only when its owner is an enumeration item, as
  -- `Value.valid` requires of the enum value (`lir.terms.constructors`).
  let red := Term.constructor (key "Light") ((key "Light").named "Red")
  let ownerless := {t with resolved := {t.resolved with scope := {t.resolved.scope with
    items := t.resolved.scope.items.filter (fun i => i.kind != .enumeration)}}}
  require (Term.infer 100 t ctx red == some (.enum (key "Light")) &&
    Value.valid t (.enum (key "Light") ((key "Light").named "Red")) &&
    Term.infer 100 ownerless ctx red == none &&
    !Value.valid ownerless (.enum (key "Light") ((key "Light").named "Red")))
    "constructor without an enumeration owner must have no sort"
  let some sig := t.signatures[0]? | throw (IO.userError "missing fixture signature")
  let fakeSig := {sig with id := key "absent"}
  require (Term.infer 100 t [] (.app fakeSig .domain [.int 0]) == none) "unknown symbol control"
  -- Source identity and original division token survive each domain root.
  let some b := body? c.program "guarded" | throw (IO.userError "missing guarded")
  require (match b.term.defined with
    | .at _ (.binary .and (.at origin _) _) =>
      match origin.expression with
      | .binary _ token .div _ => token.span.file == ⟨301⟩ && token.text == "div" &&
        origin.owner == key "guarded" && origin.context.map (·.1.text) == ["d"]
      | _ => false
    | _ => false) "let domain retains the original partial occurrence and incoming context"
  require (match b.term.defined with
    | .at o _ => o.owner == key "guarded" && o.expression == b.source.expression &&
      o.context == b.source.context && o.expression.tokens.all (·.span.file == ⟨301⟩)
    | _ => false) "source/domain origin"

private def checkContexts : IO Unit := do
  let source := "mod lir_walk\nfn ignore(x: Int): Int := 0\n" ++
    "expect contexts(b?: Bool, x: Int) { " ++
    "expect repeated: let x := x + 1 in let x := x + 2 in x + x = 14 " ++
    "expect lazy: let x := 1 div 0 in if b? then x = x else true " ++
    "assume call: if b? then ignore(1 div 0) = 0 else true " ++
    "assume unused: let x := 1 div 0 in true }"
  let c ← load source
  require (c.program.requests.map (fun r => (labels r.assumptions, labels r.demand)) ==
    #[(#["call", "unused"], #["call", "unused"]),
      (#["call", "unused"], #["call", "unused", "repeated"]),
      (#["call", "unused"], #["call", "unused", "lazy"])]) "context check independent roots/late assumptions"
  require (c.program.requests.all (fun r => r.source.context.map (·.1.text) == ["x", "b?"]))
    "context check parameter order"
  require (agrees c "contexts" #[.bool false, .int 4] (some (.bool true)) (some "repeated") &&
    agrees c "contexts" #[.bool false, .int 5] (some (.bool false)) (some "repeated") &&
    domainIs c "contexts" #[.bool false, .int 4] false (some "lazy") &&
    agrees c "contexts" #[.bool true, .int 4] none (some "lazy") &&
    agrees c "contexts" #[.bool false, .int 4] (some (.bool true)) (some "call") &&
    agrees c "contexts" #[.bool true, .int 4] none (some "call") &&
    domainIs c "contexts" #[.bool true, .int 4] false (some "unused"))
    "context checks: nested shadow/repeated reads/guarded partial lets/strict calls/unused outcome"

private def rejections : IO Unit := do
  for source in ["mod lir_walk\nfn f(x: Int): Int := (", "mod lir_walk\nfn f(x: Int): Int := false",
      "mod lir_walk\nfn f(x: Int): Int := absent", "mod lir_walk\nfn f(x: Int): Int := f(x)",
      "mod lir_walk\nenum E { A, B }\nfn f(e: E): Int := match e { E::A => 0 }"] do
    let .error original := FrenWalking.fromSource ⟨301⟩ source
      | throw (IO.userError "invalid fixture admitted")
    let .error actual := FrenFlatToLir.fromSource ⟨301⟩ source
      | throw (IO.userError "invalid source lowered")
    require (reprStr actual == reprStr original) "original admission failure changed"

def runCases : IO Unit := do
  let started ← IO.monoMsNow
  walking
  controls
  checkContexts
  rejections
  IO.println s!"LIR native execution: {(← IO.monoMsNow) - started} ms"
  IO.println "LIR native: walking definition/symbols, declarative domains/value premises, both-branch static scope audits, 8 + 3 owned requests, nominal/context/provenance controls; 5 rejected sources; 4 source + 6 verification + 1 lexical-slot + 5 retention mutants killed. Probe is test-only with finite symbols; no solver or general simulation."

end FrenFlatToLirTests
