-- keep-sorted start
import Fren.Model
import FrenCore.SolverSorts
-- keep-sorted end

namespace Fren

/-- Types occurring in expressions or their signatures. Open binders are
visited with locals, so function results and quantified types are included
as well as the procedure's free variables. -/
partial def solverSortRoots (hooks : ElabHooks) (seen : IO.Ref (Std.HashSet Lean.Expr))
    (e : Lean.Expr) : Lean.Meta.MetaM (Array Core.Ty) := do
  if (← seen.get).contains e then return #[]
  seen.modify (·.insert e)
  let ty ← Lean.Meta.inferType e
  let mut out := #[]
  for t in #[e, ty] do
    -- A partially applied datatype still has a function type; its
    -- missing arguments are declaration parameters, not query types.
    if (← Lean.Meta.inferType t).isSort then
      if let some t ← hooks.coreTy t then out := out.push t
  if ty.isForall then out := out ++ (← solverSortRoots hooks seen ty)
  match e with
  | .app f a => return out ++ (← solverSortRoots hooks seen f) ++ (← solverSortRoots hooks seen a)
  | .lam n t b bi | .forallE n t b bi =>
    out := out ++ (← solverSortRoots hooks seen t)
    return out ++ (← Lean.Meta.withLocalDecl n bi t fun x => solverSortRoots hooks seen (b.instantiate1 x))
  | .letE n t v b _ =>
    out := out ++ (← solverSortRoots hooks seen t) ++ (← solverSortRoots hooks seen v)
    return out ++ (← Lean.Meta.withLetDecl n t v fun x => solverSortRoots hooks seen (b.instantiate1 x))
  | .mdata _ b | .proj _ _ b => return out ++ (← solverSortRoots hooks seen b)
  | _ => return out

/-- Unconstrained set/relation locals make lean-smt explicitly create the
concrete tuple sorts hidden inside datatype payloads and fields. Empty
collections inhabit these types, so the declarations constrain no behaviour. -/
def withSolverCollectionSorts [Inhabited α] (hooks? : Option ElabHooks) (es : Array Lean.Expr)
    (k : Array Lean.Expr → Lean.Meta.MetaM α) : Lean.Meta.MetaM α := do
  let some hooks := hooks? | return ← k #[]
  let st ← getState
  unless st.enums.toArray.any (fun (_, d) => d.shape.hasImplicitTuple d.params.size)
      || st.records.toArray.any (fun (_, d) => d.shape.hasImplicitTuple d.params.size) do
    return ← k #[]
  let seen ← IO.mkRef ({} : Std.HashSet Lean.Expr)
  let roots := (← es.mapM (solverSortRoots hooks seen)).flatten
  let types := (roots.flatMap (·.collectionSorts st.shapeOf)).foldl
    (fun acc t => if acc.contains t then acc else acc.push t) #[]
  let types ← types.mapM hooks.leanType
  Lean.Meta.withLocalDeclsD (types.mapIdx fun i t => (Lean.Name.mkSimple s!"#fren.tuple.{i}", fun _ => pure t)) k

end Fren
