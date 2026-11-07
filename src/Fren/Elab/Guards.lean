-- keep-sorted start
import Fren.Elab.Sets
-- keep-sorted end

/-! # Hosted elaboration: guards -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `when c, d`, `unless c, d`, `c and d` or `c or d`, where `d` is the
`operand`, guarded by `c` or by `not c` (`lang::guard`). -/
def guardedTerm (toTerm : ExprCtx → Syntax → TermElabM Term) (cx : ExprCtx) (c d : Syntax) (operand : Core.GuardedOperand)
    (op : Join := .implies) (test : Core.TestContext × Option (Nat × Nat) := (.standalone, none)) : TermElabM Term := do
  let e ← getRef
  let j := match op with | .or => "or" | .and => "and" | .implies => ""
  -- `membership_chain`, at the top of a chain of `or` or of `and` (`lint::membership_chain`).
  if !j.isEmpty && cx.chain != j && cx.noteIndexes then
    let ds := chainOperands j e
    let cmp := if op matches .and then "!=" else "="
    let eqs := ds.filterMap fun d => let d := unparen d; if isBinOp d cmp then some (d[0], d[2]) else none
    let lefts := eqs.map (srcText ·.1)
    let laterIndexes := (eqs.extract 1).any fun (_, v) => !(indexedIn v).isEmpty
    let patterns ← eqs.allM fun (_, v) => return Core.patternValue (srcText (unparen v)) (← variantOf? cx v).isSome
    if Core.membershipChainFires ds.size (eqs.size == ds.size && lefts.all (· == lefts[0]!)) laterIndexes patterns then
      recordLint .membershipChain e (Core.membershipChainMsg lefts[0]! (eqs.map (srcText ·.2)) (op matches .and))
  -- `index_after_use` (`lint::index_after_use`).
  if op matches .and && cx.noteIndexes && !(← chainBinds cx c) then
    if (indexedIn c).any (fun q => boundsSeq d q && !boundsSeq c q) then recordLint .indexAfterUse e (Core.indexAfterUseMsg (srcText c) (srcText d))
  let cx := { cx with chain := j }
  -- Each operand's type is checked as the `fren` command checks it
  -- (`lang::operator_type`).
  let kw := if operand matches .unlessBody then "unless" else "when"
  -- For `manual_at_most_one`: whether the operands give a definedness
  -- obligation.
  let mark := (← getLocal).indexes.size + (← getLocal).tables.size
  -- Of `and`, the position of each operand in its chain, and the names
  -- that the left one's pattern tests bind, which the right one sees; at
  -- the top of the chain, those of the whole, which only the body of the
  -- `when` or `if` whose condition it is sees. Of `when`, the names that
  -- its condition's pattern tests bind, which its body sees
  -- (`lang::test_scope`).
  let (context, at?) := test
  let (k, n) := at?.getD (0, (chainOperands "and" e).size)
  let left := (chainOperands "and" c).size
  let (ccx, dcx) : ExprCtx × ExprCtx := match op with
    | .and => ({ cx with testContext := context, testAt? := some (k, n) }, { cx with testContext := context, testAt? := some (k + left, n) })
    | .or => ({ cx with testContext := .orOperand }, { cx with testContext := .orOperand })
    | .implies => ({ cx with testContext := if operand matches .unlessBody then .unlessCondition else .whenCondition }, cx)
  let boundMark := (← getLocal).bound.size
  let x ← toTerm ccx c
  checkTermType c x .bool (if j.isEmpty then some s!"note: the condition of `{kw}` is a `Bool`" else Core.opNote j .bool)
  let x ← propositionTerm x
  let g ← operand.guard (pure x) `(¬$x)
  let new ← boundSince boundMark
  let seen := match op with
    | .and => new
    | .or => #[]
    | .implies => if Core.binderVisible ccx.testContext 0 1 .body then new else #[]
  if op matches .implies then modifyLocal fun l => { l with bound := l.bound.extract 0 boundMark }
  let y ← toTerm { dcx with guards := cx.guards.push g, binders := cx.binders ++ seen } d
  if op matches .and && at?.isNone && !Core.binderVisible context 0 n .body then
    modifyLocal fun l => { l with bound := l.bound.extract 0 boundMark }
  if op matches .and && cx.noteIndexes && (← getLocal).indexes.size + (← getLocal).tables.size > mark then
    modifyLocal fun l => { l with facts := l.facts.push ((e.getPos?, e.getTailPos?), .obligations) }
  if j.isEmpty then checkTermType e y .bool (some s!"note: the body of `{kw}` is a `Bool`")
  else checkTermType d y .bool (Core.opNote j .bool)
  let y ← propositionTerm y
  match op with
  | .implies => `($g → $y)
  | .and => `($x ∧ $y)
  | .or => `($x ∨ $y)

/-- `goal` where `guards` hold. -/
def guardedGoal (guards : Array Term) (goal : Term) : TermElabM Term :=
  guards.foldrM (fun g acc => `($g → $acc)) goal

/-- Records the index `q[i]` at `ref`, as the terms `q` and `i`, for the
definedness check (`check::definedness`): its guard implies its bounds. -/
def noteIndex (cx : ExprCtx) (ref : Syntax) (q i : Term) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let bounds ← `(0 ≤ $i ∧ $i < Fren.Seq.len $q)
  let goal ← guardedGoal cx.guards bounds
  modifyLocal fun l => { l with indexes := l.indexes.push (ref, goal) }

/-- Records the questions about the rows of the table `e`, whose rows other
than `_` have the conditions `conds`, written at `refs`, whose indexes are
in range where `defined` says, for its
completeness and disjointness checks (`check::completeness`,
`check::disjointness`): completeness is reported at `table`, and the
disjointness of two rows at the later one's condition. -/
def noteTable (cx : ExprCtx) (e : Syntax) (refs : Array Syntax) (conds : Array Term) (defined : Array (Option Term))
    (wild : Bool) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let orF (cs : Array Term) : Term := cs.pop.foldr (fun c acc => Unhygienic.run `($c ∨ $acc)) cs.back!
  let andF (a b : Term) : Term := Unhygienic.run `($a ∧ $b)
  let notF (c : Term) : Term := Unhygienic.run `(¬$c)
  for (g, f) in Core.tableGoals orF andF notF (Unhygienic.run `(True)) conds defined wild do
    let ref := match g with
      | .disjointness _ _ j | .reachability _ j => refs[j]!
      | _ => e[0]
    let goal ← guardedGoal cx.guards f
    modifyLocal fun l => { l with tables := l.tables.push (ref, g, goal) }

/-- The arguments for the placeholders `uses` of a definition of the generic
function at `path`, or of its contract, with the type parameters `tps`, at
its instance with the type arguments `targs`: a type parameter's type
argument, its `Inhabited` instance's, and any other placeholder itself
(`Reqs/Generated#generic-functions`). -/
def usesTerms (uses : Array Name) (path : Name) (tps : Array Name) (targs : Array Core.Ty) : TermElabM (Array Term) := do
  -- `_` lets Lean fill the dictionary by instance synthesis, rather than
  -- putting `inferInstance` around it, which `simp` would see.
  let args ← targs.flatMapM fun t => do
    return #[typeSyntax (← leanTypeOf t), ← `(_)]
  let images := typeInstanceImages path tps args uses
  return uses.map fun u => (images[u]?).getD ⟨(mkCIdent u).raw⟩

/-- Records an application of the generic function at `path` at the type
arguments `targs`, in the current item (`Core.GenericUse`). -/
def recordGenericUse (path : Name) (targs : Array Core.Ty) : TermElabM Unit := do
  let l ← getLocal
  record (.genericUse (← getMainModule)
    { file := 0, item := l.currentItem, caller? := l.fnTypeParams.map (·.1), callee := path, targs })

/-- Records the questions about the application at `ref` of the function at
`path` to the arguments `args`, if the function has preconditions, for
the precondition check (`check::precondition`): its guard implies each
precondition at the arguments, in order; of a generic function, at the
instance with the type arguments that `inst?` gives its type parameters. -/
def notePreconditions (cx : ExprCtx) (ref : Syntax) (path : Name) (args : Array Term)
    (inst? : Option (Array Name × Array Core.Ty) := none) : TermElabM Unit := do
  unless cx.noteIndexes do return
  let some k := (← getState).contracts.get? path | return
  let pres ← k.pres.mapM fun pre => do
    let some (tps, targs) := inst? | return (pre.name, ← `(@$(mkCIdent pre.decl) $(pre.uses.map fun u => ⟨(mkCIdent u).raw⟩)* $args*))
    return (pre.name, ← `(@$(mkCIdent pre.decl) $(← usesTerms pre.uses path tps targs)* $args*))
  let guarded (g : Term) : Term := cx.guards.foldr (fun c acc => Unhygienic.run `($c → $acc)) g
  for (q, goal) in Core.preconditionQuestions guarded path pres do
    modifyLocal fun l => { l with tables := l.tables.push (ref, q, goal) }


end Fren
