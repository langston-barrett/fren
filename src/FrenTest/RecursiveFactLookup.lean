-- keep-sorted start
import Fren.View
-- keep-sorted end

open Fren.Lang

mod recursive_fact_lookup

pub enum Tree { Leaf, Node(Tree, Tree) }

-- Induction adds recursive functions that a later query need not mention.
-- Their number must not multiply the cost of visiting each subterm (#750).
run_cmd do
  for i in [:64] do
    let name := s!"noise_{i}"
    let text := s!"pub fn {name}(t: Tree): Int := match t \{ Tree::Leaf => 0, Tree::Node(a, b) => {name}(a) + {name}(b) + 1, }"
    Lean.Elab.Command.elabCommand (← Fren.parseAt `command text (← Lean.getRef))

open Lean Meta

-- The old array lookup took about 400 heartbeats here; the index takes
-- fewer than 10. If Lean changes these costs, keep that gap around the
-- budget when adjusting the number of functions or subterms.
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let goal := (List.range 256).foldl (fun e _ => mkAnd (mkConst ``True) e) (mkConst ``True)
    withCurrHeartbeats do
      let facts ← Fren.recursiveQueryFacts #[] goal
      Lean.Core.checkMaxHeartbeatsCore "recursive fact lookup" `maxHeartbeats (50 * 1000)
      unless facts.isEmpty do throwError "a query without recursive symbols gained recursive facts"
