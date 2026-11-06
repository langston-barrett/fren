-- keep-sorted start
import FrenCli.Smt
-- keep-sorted end

/-! The standalone extractor unfolds defined functions before the shared
`check::output_query_core` decision, including arguments a definition
ignores. A backend that gives up makes that classification observable
without relying on a particular solver's completeness. -/
-- fren-covers: check::output_query_core

open FrenCli Fren.Core

#eval show IO Unit from do
  let prelude := Prelude.ofDecls #[
    { text := "(declare-fun |::f| (Int) Int)", syms := #["::f"] },
    { text := "(define-fun |::ignore| ((|a| Int)) Int 0)", syms := #["::ignore"] },
    { text := "(define-fun |::id| ((|a| Int)) Int |a|)", syms := #["::id"] },
    { text := "(define-fun |::first| ((|a| Int) (|b| Int)) Int |a|)", syms := #["::first"] },
    { text := "(define-fun |::wrap| ((|a| Int)) Int (|::f| (|::ignore| |a|)))", syms := #["::wrap"] }] #[]
  let c : CComp := { path := `p, file := 0, span := default, props := #[], vars := #[
    { name := `x, role := .input, isPub := true, ty := .int, span := default },
    { name := `y, role := .output, isPub := true, ty := .int, span := default }] }
  let comp : Comp String :=
    { path := `p
      vars := #[{ name := `x, role := .input, isPub := true }, { name := `y, role := .output, isPub := true }]
      assumes := #[]
      reqs := #[]
      expects := #[]
      triggers := #[] }
  for (term, inCore) in [
      ("|y|", false), ("|x|", true), ("(|::ignore| |y|)", true),
      ("(|::id| |y|)", false), ("(|::first| |x| |y|)", true),
      ("(|::wrap| |y|)", true), ("(|::ignore| (|::f| |y|))", true),
      ("(let ((|a| |y|)) |a|)", false), ("(let ((|a| |y|)) 0)", true)] do
    let formula := s!"(>= (|::f| {term}) 0)"
    for asFact in [false, true] do
      let c := if asFact then { c with vars := c.vars.map fun v =>
          if v.role == .output then { v with fact? := some formula } else v }
        else c
      let bk := { backend prelude #[] c {} (kind := .realizable) with
        query := fun _ _ model => pure (if model then .unknown "INCOMPLETE" else .sat #[]) }
      let comp := if asFact then comp else { comp with reqs := #[(`claim, formula)] }
      let r ← checkRealizableUniversal bk comp
      let ms := messages false r
      unless r.outputQueryInCore == inCore && ms.size == 1 &&
          ms[0]!.severity == (if inCore then .error else .warning) do
        throw <| IO.userError s!"wrong output query classification for {term}, type fact {asFact}: {r.outputQueryInCore}"
