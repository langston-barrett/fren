module

public import FrenAstToHirTests.Support
import Plausible

public section
namespace FrenAstToHirTests
open FrenAst FrenModule FrenAstToHir Plausible
open scoped Plausible.Decorations

private def generated (n : Nat) (reverse : Bool) : String :=
  let f := s!"fn f(x: Int, y: Int): Int := let x := x + y in if true then x + {n % 100} else y\n"
  let e := "enum Light { Red, Green }\n"
  let g := "fn g(l: Light): Light := Light::Red\n"
  "mod walking\n" ++ (if reverse then g ++ e ++ f else f ++ e ++ g)

private def isError (code : String) (doc : Document) : Bool :=
  match resolve doc with | .error d => d.code == some code | _ => false

/-- Each generated case requires both accepted and rejected outcomes. No
implication discards an unknown/ill-typed/partial input. Expected local slots
are written directly; no second implementation computes them. -/
def generatedAudit (n file : Nat) (reverse : Bool) : Bool := Id.run do
  let source := generated n reverse
  let .ok doc := FrenParse.parseFile ⟨file⟩ source | return false
  let .ok result := resolve doc | return false
  let actual := (expressionRefs result).filter (fun r => match r.target with | .local _ => true | _ => false)
  if actual.map (·.target) != #[.local 1, .local 0, .local 0, .local 1] then return false
  if !audit doc result then return false
  let .ok illtyped := FrenParse.parseFile ⟨file⟩
    "mod walking\nenum Light { Red }\nfn f(l: Light): Int := l + 1" | return false
  let .ok illResult := resolve illtyped | return false
  if targets illResult != #[.local 0] || !audit illtyped illResult then return false
  let .ok unknown := FrenParse.parseFile ⟨file⟩
    "mod walking\nfn f(x: Int): Int := let x := missing in x" | return false
  if !isError "F0201" unknown then return false
  let .ok duplicate := FrenParse.parseFile ⟨file⟩
    "mod walking\nfn f(x: Int, x: Int): Int := x" | return false
  if !isError "F0213" duplicate then return false
  let .error _ := FrenParse.parseFile ⟨file⟩ (source ++ "fn truncated(") | return false
  let .error malformed := resolve {doc with root := .declarations #[]} | return false
  return malformed.code.isNone

private def nearestAudit (names : List String) (query : String) : Bool :=
  match nearest names query with
  | none => !names.contains query
  | some i =>
    FrenBase.Binding.lookup names i == some query &&
      !(names.take i).contains query && i < names.length

private def check (label : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let report ← Testable.checkIO p' {numInst := 150, maxSize := 35, randomSeed := some 20261108}
  IO.println s!"{label}: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError s!"resolver Plausible failure: {label}")

/-- Native direct Plausible jobs; sampled evidence, never an `impl` proof. -/
def runProperties : IO Unit := do
  check "actual parser/resolver: 150 required valid + ill-typed + unknown + duplicate + partial + edited AST groups" <|
    ∀ (n file : Nat) (reverse : Bool), generatedAudit n file reverse = true
  check "actual nearest search: first binding entry and absence" <|
    ∀ (names : List String) (query : String),
    nearestAudit names query = true

  -- This census uses actual outcomes, independently of Plausible's displayed
  -- sample count. It audits partial source prefixes instead of discarding them.
  let mut parseAccepted := 0
  let mut parseRejected := 0
  let mut walkingShape := 0
  let mut collectionAccepted := 0
  let mut duplicateRejected := 0
  let mut lookupMisses := 0
  let mut referenceHits := 0
  let mut resolvedCount := 0
  let mut resolutionRejected := 0
  let mut localHits := 0
  let mut scopedHits := 0
  let source := "mod walking\nfn f(x: Int): Int := let y := x in y + absent"
  let prefixes := (List.range (source.length + 1)).map fun n => String.ofList (source.toList.take n)
  let completeAndPartial := (List.range 40).flatMap fun n =>
    [generated n (n % 2 == 0),
     "mod walking\nenum Light { Red }\nfn f(l: Light): Int := l + 1",
     "mod walking\nfn f(x: Int): Int := missing",
     "mod walking\nfn f(x: Int, x: Int): Int := x",
     generated n false ++ "fn truncated("]
  for text in prefixes ++ completeAndPartial do
    match FrenParse.parseFile ⟨77⟩ text with
    | .error _ => parseRejected := parseRejected + 1
    | .ok doc =>
      parseAccepted := parseAccepted + 1
      let some span := FrenSource.Span.checked ⟨77⟩ 0 0 text.utf8ByteSize
        | throw (IO.userError "census span")
      let .declarations decls := doc.root | throw (IO.userError "census root")
      if let some (Decl.moduleDecl _ _ path) := decls[0]? then
        if path.tail.isEmpty && !(decls.extract 1 decls.size).any (fun d =>
            match d with | .moduleDecl .. => true | _ => false) then
          walkingShape := walkingShape + 1
      match collect decls span with
      | .ok _ => collectionAccepted := collectionAccepted + 1
      | .error d => if d.code == some "F0213" then duplicateRejected := duplicateRejected + 1
      match resolve doc with
      | .error d =>
        resolutionRejected := resolutionRejected + 1
        if d.code == some "F0201" then lookupMisses := lookupMisses + 1
      | .ok result =>
        resolvedCount := resolvedCount + 1
        require (audit doc result) "prefix output audit"
        referenceHits := referenceHits + result.references.size
        for ref in result.references do
          if let .local i := ref.target then
            localHits := localHits + 1
            if i < ref.context.length then scopedHits := scopedHits + 1
  require (parseAccepted > 0 && parseRejected > 0 && collectionAccepted > 0 &&
    walkingShape > 0 && duplicateRejected > 0 && lookupMisses > 0 && referenceHits > 0 &&
    resolvedCount > 0 && resolutionRejected > 0 && localHits > 0 && localHits == scopedHits)
    "prefix census became vacuous"
  IO.println s!"actual source census (prefixes and generated valid/ill-typed/unknown/duplicate/truncated): parsed={parseAccepted}, parse-rejected={parseRejected}, walking-shape={walkingShape}, collected={collectionAccepted}, duplicates={duplicateRejected}, resolved={resolvedCount}, resolution-rejected={resolutionRejected}, reference-hits={referenceHits}, lookup-misses={lookupMisses}, local-hits={localHits}, scoped={scopedHits}; discarded=0"
  -- Mutant expectations are tested against actual output: accepting any one
  -- would mask the contract regressions this suite is meant to detect.
  let result ← resolved "mod m\nfn f(x: Int, y: Int): Int := let x := x + y in x + y"
  require (targets result != #[.local 0, .local 1, .local 0, .local 1]) "older-first/incorrect-slot mutant survived"
  require (targets result != #[.local 0, .local 1, .local 0, .local 2]) "let-value binder leak mutant survived"
  let .ok sibling := FrenParse.parseFile ⟨77⟩
    "mod m\nfn f(x: Int): Int := (let z := x in z) + z" | throw (IO.userError "sibling parse")
  require (isError "F0201" sibling) "sibling leak mutant survived"

end FrenAstToHirTests
