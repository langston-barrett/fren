-- keep-sorted start
import Fren.Elab.Blocks
import Fren.View
import FrenCli.Smt
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

-- The CLI must also memoize equal/deeper visits. These diamonds have only
-- 16 distinct applications but exponentially many paths without the memo.
-- All applications initially occur at depth zero in the second query;
-- the bodies' later discoveries are deeper and must not expand again.
-- Each traversal has a heartbeat budget, as the lookup test above does;
-- keep the gap between memoized and repeated traversal when adjusting it.
-- fren-covers: lang::recursive_depth
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let levels := 16
    let names := (List.range levels).toArray.map fun i => s!"f{i}"
    let recs := names.map fun n => (n, #["x"], FrenCli.SeqElems.parse "0")
    let prelude : FrenCli.Prelude :=
      { (default : FrenCli.Prelude) with recs := Thunk.pure recs, recReach := Thunk.pure names }
    let types := (names.zipIdx).foldl (init := {}) fun acc (n, i) =>
      if i + 1 < levels then
        acc.insert n s!"(= {FrenCli.factHole} (+ (f{i+1} x) (f{i+1} x)))"
      else acc
    withCurrHeartbeats do
      let facts := FrenCli.recursiveQueryFacts prelude {} types #[] "(= (f0 x) 0)" {} 0
      unless facts.size == levels - 1 do throwError "equal visits changed the CLI contract facts"
      Lean.Core.checkMaxHeartbeatsCore "CLI equal visits" `maxHeartbeats (100 * 1000)
    let recs := names.mapIdx fun i n =>
      (n, #["x"], FrenCli.SeqElems.parse
        (if i + 1 < levels then s!"(+ (f{i+1} x) (f{i+1} x))" else "0"))
    let prelude := { prelude with recs := Thunk.pure recs }
    let goal := "(+ " ++ " ".intercalate (names.toList.map fun n => s!"({n} x)") ++ ")"
    withCurrHeartbeats do
      let facts := FrenCli.recursiveQueryFacts prelude {} {} #[] goal {} levels
      unless facts.size == levels do throwError "deeper visits changed the CLI equations"
      Lean.Core.checkMaxHeartbeatsCore "CLI deeper visits" `maxHeartbeats (100 * 1000)

-- The contract chain reaches size(x) at depth zero after other's body
-- reaches it at depth one. Only the later visit may unfold its equation.
run_cmd do
  let recs := #[
    ("size", #["x"], FrenCli.SeqElems.parse "42"),
    ("other", #["x"], FrenCli.SeqElems.parse "(size x)"),
    ("b0", #["x"], FrenCli.SeqElems.parse "0"),
    ("b1", #["x"], FrenCli.SeqElems.parse "0"),
    ("b2", #["x"], FrenCli.SeqElems.parse "0")]
  let prelude : FrenCli.Prelude :=
    { (default : FrenCli.Prelude) with recs := Thunk.pure recs, recReach := Thunk.pure #["size"] }
  let types := ({} : Std.HashMap String String)
    |>.insert "b2" s!"(= {FrenCli.factHole} (b1 x))"
    |>.insert "b1" s!"(= {FrenCli.factHole} (b0 x))"
    |>.insert "b0" s!"(= {FrenCli.factHole} (size x))"
  let facts := FrenCli.recursiveQueryFacts prelude {} types #[]
    "(= (+ (b2 x) (other x)) 0)" {} 1
  unless facts.contains (`equation, "(= (size x) 42)") do
    throwError "a later shallower CLI visit lost size's equation"
