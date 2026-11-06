-- keep-sorted start
import FrenCli.Elab.Model
import FrenCore.TheoryDump
-- keep-sorted end

/-! # The native front end's structural theory view (`Reqs/Cli#theories`) -/

namespace FrenCli

open Lean (Name)

/-- Extract declaration facts without reading any SMT terms. -/
def theoryDiagram (s : State) : Fren.Core.TheoryDiagram := Id.run do
  let mut items := #[]
  for (_, item) in s.table.items.toArray do
    let p := item.path
    let mut d : Fren.Core.TheoryDumpItem := { item, alias? := s.aliases.get? p }
    if let some (args, result) := s.funPTys.get? p then
      d := { d with
        types := (args.map (·.ty)).push result.ty }
    if let some g := s.genericFns.get? p then
      d := { d with
        parameters := g.params, types := g.declared.push g.result, defined := g.defined }
    else if let some h := s.hofs.get? p then
      d := { d with
        parameters := h.typeParams, types := #[h.result], higherOrder := h.params.map (·.2.2), defined := true }
    else
      d := { d with
        defined := s.defs.any (·.1 == p) }
    if let some (_, ty) := s.consts.get? p then d := { d with types := #[ty] }
    if let some ty := s.aliases.get? p then d := { d with types := #[ty.ty] }
    if let some data := s.datatypes.find? (·.path == p) then
      let args := data.params.toList.zipIdx.map fun (n, k) => Fren.Core.Ty.param k n
      d := { d with
        parameters := data.params, constructors := data.ctors,
        carrier? := some (if data.isRecord then .record p args else .enum p args) }
    if let some under := s.newtypes.get? p then
      d := { d with
        carrier? := some (.newtype p under), constructors := #[(`mk, #[(Name.mkSimple "0", under)])] }
    if let some c := s.contracts.get? p then
      d := { d with
        defined := c.defined,
        clauses := (c.pres.map fun (n, _) => (n, "require")) ++ (c.posts.map fun (n, _) => (n, "ensure")) }
    let comp := if item.kind == .expectItem then
        s.globals.find? fun c => (if c.short then c.path ++ (c.props[0]?.map (·.name)).getD .anonymous else c.path) == p
      else s.comps.find? (·.path == p)
    if let some c := comp then
      d := { d with
        variables := c.vars.map fun v => { name := v.name, type := v.ty, role := v.role, isPub := v.isPub },
        clauses := (c.props.filterMap fun prop =>
          if prop.kind == .cover then none else
            let name := if c.short then .anonymous else prop.sourceName?.getD prop.name
            let keyword := match prop.kind with
              | .assume => "require" | .ensure => "ensure" | .expect => "expect" | .cover => "cover"
            some (name, keyword)) ++
          c.defs.map (fun (n, _) => (n, "define")),
        calls := c.insts.map fun i => (i.name, i.comp), subset? := c.subset?, subsetInvariant? := c.subsetInvariant? }
    items := items.push d
  return Fren.Core.theoryDiagram {
    items, uses := s.table.uses.toArray.flatMap (·.2),
    genericUses := s.genericUses, laws := s.theoryLaws }

end FrenCli
