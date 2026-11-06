-- keep-sorted start
import FrenCli.Run
-- keep-sorted end

-- A corrupt evaluator counterpart must report the pairing error without
-- losing the solver's other results for the same procedure.
-- The native enumeration job runs this with the solver bindings linked.
namespace FrenTest.SolverPairing

open FrenCli Lean

/-- A vacuity query needs only the guard, but observing a closed record
member still needs its datatype and no unused predicate arguments. -/
private def observationDeclarations : IO (Array String) := do
  let src := "mod observation_declarations\n\
    pub struct R { value: Int }\n\
    pub fn choice?(value: R, other?) := or { first: value != R { value := 1 }, second: other? }\n\
    pub proc observed(active?, other?) {\n\
        expect output: let saved := R { value := 1 } in when active?, choice?(saved, other?)\n\
    }\n"
  let files := #[("observations.fren", src.toList.toArray)]
  let st := elabText (initialState #[]) 0 files[0]!.2
  unless st.diags.all (·.severity != .error) do
    return #["the observation-declarations regression failed to elaborate"]
  let .ok sp := specOf files st.callTargs
    | return #["the observation-declarations regression has no evaluator spec"]
  let some c := st.comps.find? (·.path == `observation_declarations.observed)
    | return #["the observation-declarations regression has no procedure"]
  let cache ← QueryCache.new
  let (results, refuted, error?) ← solveComp st.forSolving (.ok sp) (symbolsOf (.ok sp))
    c false #[.expect, .vacuity] {} cache
  if error?.isSome || !refuted.isEmpty then
    return #["the observation-declarations regression failed to check"]
  let vacuity := results.filter (·.kind == .vacuity)
  if vacuity.isEmpty || vacuity.any (fun result =>
      let first := result.memberValues.filter fun value => (value.name.toString (escape := false)).endsWith ".first"
      first.size != 1 || first.any (fun value => value.evaluated? != some true || value.value? != some false)) then
    return #["a vacuity query lost the closed record member's value"]
  return #[]

def check : IO (Array String) := do
  let src := "type Nonnegative = n: Int where lower: n >= 0\n\
    proc accept(n: Nonnegative) {}\n\
    proc caller(n: Int) {\n\
        call c := accept(n)\n\
        expect independent: true\n\
    }\n"
  let files := #[("pairing.fren", src.toList.toArray)]
  let st := elabText (initialState #[]) 0 files[0]!.2
  unless st.diags.all (·.severity != .error) do
    return #["the pairing regression failed to elaborate"]
  let .ok sp := specOf files st.callTargs
    | return #["the pairing regression has no evaluator spec"]
  let some c := st.comps.find? (·.path == `caller)
    | return #["the pairing regression has no caller"]
  let damaged : Eval.Spec := { sp with comps := sp.comps.map fun d =>
    if d.path == `accept then
      { d with inputObligations := d.inputObligations.map fun p => { p with typed? := some "wrong" } }
    else d }
  let some ec := damaged.comp? `caller | return #["the evaluator has no caller"]
  if (pairCore damaged ec (toCore c) #[]).isOk then
    return #["the regression did not exercise a pairing mismatch"]
  let cache ← QueryCache.new
  let (results, refuted, error?) ← solveComp st.forSolving (.ok damaged) (symbolsOf (.ok damaged))
    c false #[.expect] {} cache
  unless error?.any (·.headline.startsWith "internal error:") do
    return #["a pairing mismatch was not reported"]
  unless refuted.isEmpty && results.any (fun r =>
      r.kind == .expect && r.prop? == some `independent && r.verdict == .pass) do
    return #["a pairing mismatch lost the independent solver result"]
  return ← observationDeclarations

end FrenTest.SolverPairing
