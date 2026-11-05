-- keep-sorted start
import FrenCli.Elab.Model
import FrenCli.SeqElems
import FrenCore.SolverSorts
-- keep-sorted end

namespace FrenCli.SolverSorts

open Fren.Core SeqElems

/-- There is an implicitly instantiated tuple in a declaration. -/
def needed (ds : Array DataDecl) : Bool :=
  ds.any fun d => d.ctors.any (fun (_, fs) => fs.any (·.2.hasImplicitTuple d.params.size))

/-- Read a sort occurring in a query, undoing the prelude's parameter
order. Datatype templates are skipped by `instances`, so a quoted
uninterpreted sort here is a query's declared abstract type. -/
partial def readSort? (ds : Array DataDecl) (e : SExpr) : Option Ty := do
  match e with
  | .atom "Bool" => return .bool
  | .atom "Int" => return .int
  | .atom "String" => return .string
  | .atom s =>
    if let some d := ds.find? (fun d => d.params.isEmpty && dataSortSym d.path == s) then
      return d.ty []
    let s := unquoted s
    let some s := s.dropPrefix? "::" | none
    return .abstract ((s.toString.splitOn "::").foldl Lean.Name.mkStr .anonymous)
  | .list #[.atom "Seq", a] => return .seq (← readSort? ds a)
  | .list #[.atom "Set", .list #[.atom "Tuple", a]] => return .set (← readSort? ds a)
  | .list #[.atom "Set", .list #[.atom "Tuple", a, b]] => return .rel (← readSort? ds a) (← readSort? ds b)
  | .list es =>
    let some (SExpr.atom name) := es[0]? | none
    let some d := ds.find? (fun d => dataSortSym d.path == name && es.size == d.params.size + 1) | none
    let args ← (es.extract 1 es.size).mapM (readSort? ds)
    let args := match d.lean? with
      | none => args
      | some l => (Array.range d.params.size).map fun k => args[(l.argOrder.findIdx? (· == k)).getD k]!
    return d.ty args.toList

/-- Datatype instances mentioned by the query, including function
signatures, quantified types and qualified constructors. A declaration's
`par` parameters are not instances. -/
partial def instances (ds : Array DataDecl) (e : SExpr) : Array Ty :=
  match e with
  | .list es =>
    if es[0]? == some (.atom "declare-datatypes") || es[0]? == some (.atom "declare-datatype") then #[]
    else ((readSort? ds e).filter (·.dataPath?.isSome)).toArray ++ es.flatMap (instances ds)
  | _ => ((readSort? ds e).filter (·.dataPath?.isSome)).toArray

/-- Explicit tuple sorts for instantiated collection payloads and fields,
selected by the same traversal as in the hosted front end. These aliases
introduce no value or assertion. -/
def tupleSorts (ds : Array DataDecl) (script : String) : Array String := Id.run do
  let shape (p : Lean.Name) : Option DataShape := (ds.find? (·.path == p)).map fun d =>
    { isRecord := d.isRecord, parts := d.ctors.map fun (_, fs) => fs.map (PTy.plain ·.2) }
  let roots := (parseAt script.toList.toArray 0).1.flatMap (instances ds)
  let types := roots.flatMap (·.collectionSorts shape)
  let sorts := types.filterMap fun
    | .set a => some s!"(Tuple {a.sort})"
    | .rel a b => some s!"(Tuple {a.sort} {b.sort})"
    | _ => none
  return sorts.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]

end FrenCli.SolverSorts
