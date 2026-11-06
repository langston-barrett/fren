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

-- The same application may be discovered in another function's body at a
-- deeper depth. Its contract should not be expanded a second time there.
pub fn size(t: Tree): Int := match t {
    Tree::Leaf => 0,
    Tree::Node(a, b) => 1 + size(a) + size(b),
}

pub fn with_size(t: Tree): Int := size(t) + match t {
    Tree::Leaf => 0,
    Tree::Node(a, b) => with_size(a) + with_size(b),
}

pub fn bridge0(t: Tree): (r: Int) {
    out r := match t {
        Tree::Leaf => 0,
        Tree::Node(a, b) => 1 + bridge0(a) + bridge0(b),
    }
    ensure agrees: r = size(t)
}

pub fn bridge1(t: Tree): (r: Int) {
    out r := match t {
        Tree::Leaf => 0,
        Tree::Node(a, b) => 1 + bridge1(a) + bridge1(b),
    }
    ensure agrees: r = bridge0(t)
}

pub fn bridge2(t: Tree): (r: Int) {
    out r := match t {
        Tree::Leaf => 0,
        Tree::Node(a, b) => 1 + bridge2(a) + bridge2(b),
    }
    ensure agrees: r = bridge1(t)
}

-- Count actual visits through the existing contract-evidence hook. The
-- bridge's contract chain reaches size(t) after with_size's body does:
-- a later shallower discovery must still be processed.
-- fren-covers: lang::recursive_depth
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let st ← Fren.getState
    let solver (p : Name) : MetaM Name := do
      let some d := st.defined.get? p | throwError "missing definition {p}"
      let some n := d.solver? | throwError "missing solver symbol {p}"
      return n
    let size ← solver `recursive_fact_lookup.size
    let other ← solver `recursive_fact_lookup.with_size
    let bridge ← solver `recursive_fact_lookup.bridge2
    let treeTy := (← getConstInfo size).type.bindingDomain!
    withLocalDeclD `t treeTy fun t => do
      let sizeApp := mkApp (mkConst size) t
      for (left, expected) in #[(size, 1), (bridge, 2)] do
        let visits ← IO.mkRef 0
        let goal ← mkEq (mkApp2 (mkConst ``Int.add)
          (mkApp (mkConst left) t) (mkApp (mkConst other) t)) (mkIntLit 0)
        let _ ← Fren.recursiveQueryFacts #[] goal
          (allowPosts := fun _ app gs => do
            if app == sizeApp && gs.isEmpty then visits.modify (· + 1)
            return true)
          (unfoldings := 3)
        unless (← visits.get) == expected do
          throwError "size(t) visited {(← visits.get)} times, expected {expected}"
