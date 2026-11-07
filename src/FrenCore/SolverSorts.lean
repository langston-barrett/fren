import FrenCore.SubsetTypes

/-!
# Collection sorts inside datatype instances

cvc5 needs the tuple sorts of instantiated set and relation payloads and
fields to be created explicitly, including fields the query never selects.
Its implicit substitution into a parametric datatype does not initialize
those tuple sorts. Both front ends collect them by this traversal
(`Reqs/Lang/Generics#meaning`).
-/

namespace Fren.Core

/-- A tuple in this payload's or field's sort contains a datatype parameter.
Other collection sorts are already explicit in the declaration. -/
partial def Ty.hasImplicitTuple (params : Nat) (t : Ty) : Bool :=
  let own := match t with
    | .set _ | .rel .. => (List.range params).any t.mentions
    | _ => false
  own || t.parts.any (·.hasImplicitTuple params)

/-- Whether any payload or field needs tuple initialization at an instance. -/
def DataShape.hasImplicitTuple (d : DataShape) (params : Nat) : Bool :=
  d.parts.any (·.any (·.ty.hasImplicitTuple params))

/-- Collection sorts that implicit substitution into a datatype changes.
Explicit collection sorts are already initialized when the query is read.
A recursive declaration is visited once; its type arguments are still
visited at every occurrence. Children precede their enclosing collection.
`args` substitutes the parameters of the payload or field being visited. -/
partial def Ty.collectionSorts (shapes : Lean.Name → Option DataShape) (t : Ty)
    (seen : List Lean.Name := []) (args : Array Ty := #[]) : Array Ty := Id.run do
  if let .param k _ := t then
    return (args[k]?.map fun a => a.collectionSorts shapes seen).getD #[]
  let actual := (genericTypeMorphism args).type t
  let mut out := t.parts.toArray.flatMap (·.collectionSorts shapes seen args)
  if let some p := actual.dataPath? then
    unless seen.contains p do
      if let some d := shapes p then
        out := out ++ d.parts.flatten.flatMap
          (·.ty.collectionSorts shapes (p :: seen) actual.parts.toArray)
  match t with
  | .set _ | .rel .. =>
    if (List.range args.size).any t.mentions then out := out.push actual
  | _ => pure ()
  return out.foldl (fun acc ty => if acc.contains ty then acc else acc.push ty) #[]

end Fren.Core
