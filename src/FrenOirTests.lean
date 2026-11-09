module

public import FrenOir

public section
namespace FrenOirTests
open FrenOir FrenLir

private def q (kind : Kind) : FrenOir.Question :=
  ⟨0, kind, .root, #[], [], none, none, none, [], #[], [], .bool false, #[], .ready⟩

def run : IO Unit := do
  unless (q .assumptionsSatisfiable).search == .bool true do
    throw (IO.userError "empty conjunction is true")
  for kind in [.validity, .functionDefinedness, .goalDefinedness, .assumptionDefinedness] do
    unless (q kind).search == .binary .and (.bool true) (.unary .not (.bool false)) do
      throw (IO.userError "refutation polarity")
    unless (q kind).interpret .sat == .candidateCounterexample &&
        (q kind).interpret .unsat == .noCounterexample do
      throw (IO.userError "refutation answer polarity")
  unless (q .assumptionsSatisfiable).interpret .sat == .candidateWitness &&
      (q .assumptionsSatisfiable).interpret .unsat == .unsatisfiableAssumptionSearch do
    throw (IO.userError "Sat answer polarity")
  for kind in [.validity, .assumptionsSatisfiable] do
    let query := q kind
    unless query.interpret (.unknown "timeout") == .unknown "timeout" &&
        query.interpret (.unsupported "feature") == .unsupported "feature" &&
        query.interpret (.resourceExhausted "memory") == .resourceExhausted "memory" do
      throw (IO.userError "nonanswers must preserve their reasons")
  IO.println "OIR primitives: empty conjunction, four refutations, Sat/validity polarity and six preserved nonanswers"

#print axioms FrenOir.scoped_binding
#print axioms FrenOir.scoped_guard
#print axioms FrenOir.search_counterexample

end FrenOirTests
