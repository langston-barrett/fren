-- keep-sorted start
import Fren.Elab
import FrenCore.TheoryDump
-- keep-sorted end

/-! # The Lean front end's structural theory view (`Reqs/Cli#theories`) -/

namespace Fren

open Lean (Name)

/-- Extract declaration facts without inspecting formulas or unfolding Lean
terms. Genuine Lean interpretations and implementations are named references. -/
def theoryDiagram (s : State) : Core.TheoryDiagram := Id.run do
  let mut items := #[]
  for (_, item) in s.table.items.toArray do
    let p := item.path
    let mut d : Core.TheoryDumpItem := { item, alias? := (s.aliases.get? p).map (·.2) }
    if let some a := s.abstracts.get? p then
      unless a.isType do
        d := { d with
          parameters := a.typeParams,
          types := if a.typeParams.isEmpty then (a.ptys.1.map (·.ty)).push a.ptys.2.ty else a.declared.push a.result }
    if let some f := s.defined.get? p then
      d := { d with
        parameters := f.typeParams, higherOrder := f.hoParams, defined := true,
        types := if f.typeParams.isEmpty then (f.ptys.1.map (·.ty)).push f.ptys.2.ty else f.declared.push f.result }
    if let some c := s.consts.get? p then d := { d with types := (coreTyOf s c.type).toArray }
    if let some (_, ty) := s.aliases.get? p then d := { d with types := #[ty.ty] }
    if let some e := s.enums.get? p then
      let args := e.params.toList.zipIdx.map fun (n, k) => Core.Ty.param k n
      let ctors := e.variants.zipIdx.map fun (n, k) =>
        (n, (e.shape.parts[k]?.getD #[]).zipIdx.map fun (ty, i) => (Name.mkSimple (toString i), ty.ty))
      d := { d with
        parameters := e.params, carrier? := some (.enum p args), constructors := ctors }
    if let some r := s.records.get? p then
      let args := r.params.toList.zipIdx.map fun (n, k) => Core.Ty.param k n
      let fields := r.fields.zipIdx.map fun ((n, _), k) => (n, (r.shape.parts[0]?.getD #[])[k]!.ty)
      d := { d with
        parameters := r.params, carrier? := some (.record p args), constructors := #[(`mk, fields)] }
    if let some n := s.newtypes.get? p then
      if let some under := coreTyOf s n.under then
        d := { d with
          carrier? := some (.newtype p under), constructors := #[(`mk, #[(Name.mkSimple "0", under)])] }
    if let some c := s.contracts.get? p then
      d := { d with
        defined := c.defined,
        clauses := (c.pres.map fun c => (c.name, "require")) ++ (c.posts.map fun c => (c.name, "ensure")) }
    let comp := if item.kind == .expectItem then s.globals.get? p else s.comps.get? p
    if let some c := comp then
      d := { d with
        variables := c.vars.map fun v => { name := v.name, type := v.ptype.ty, role := v.role, isPub := v.isPub },
        clauses := (c.props.filterMap fun prop =>
          if prop.kind == .cover then none else
            let name := if item.kind == .expectItem && !c.global then .anonymous else prop.evidenceOwner?.getD prop.name
            let keyword := match prop.kind with
              | .assume => "require" | .ensure => "ensure" | .expect => "expect" | .cover => "cover"
            some (name, keyword)) ++
          c.defs.map (fun (n, _) => (n, "define")),
        calls := c.insts.map fun i => (i.name, i.comp), subset? := c.subset?, subsetInvariant? := c.subsetInvariant? }
    items := items.push d
  let bindings : Array Core.TheoryDumpBinding := (s.interps.toArray.map fun (p, ref) => { kind := "interpretation", source := p, reference := ref.toString }) ++
    s.impls.toArray.flatMap (fun (p, refs) => refs.map fun ref => { kind := "implementation", source := p, reference := ref.toString })
  return Core.theoryDiagram {
    items, uses := s.table.uses.toArray.flatMap (·.2),
    genericUses := s.genericUses.map (·.2), laws := s.theoryLaws, bindings }

end Fren
