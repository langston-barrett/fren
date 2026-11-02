-- keep-sorted start
import FrenCore.Generics
-- keep-sorted end

/-! A test of `Core.instanceSites`, which groups the applications by the
generic function they are in (`Core.usesByCaller`) and by the item they
are in (`Core.usesByItem`), once, rather than scanning every application
at each instance and each item. That each grouping gives what its scan
gave, in order, is proved (`usesByCaller_getD`, `usesByCaller_map`,
`usesByItem_getD`); `instancesThrough` is `partial`, so this checks the
whole, over random applications, against the scans as they were. -/

namespace Fren.Test.InstanceSites

open Fren.Core
open Lean (Name)

/-- `Core.instancesThrough` as it was before the grouping: each instance
scans every application for those within its function. -/
partial def throughByScan (uses : Array GenericUse) (tps : Name → Array Name) (start : Array (Name × Array Ty)) :
    Array (Name × Array Ty) :=
  go start #[]
where
  go (todo all : Array (Name × Array Ty)) : Array (Name × Array Ty) :=
    if h : 0 < todo.size then
      let (g, targs) := todo[0]
      let todo := todo.extract 1
      if all.contains (g, targs) then go todo all else
      let all := all.push (g, targs)
      let ps := tps g
      let own := ps.mapIdx fun k p => Ty.abstract (typeParamPath g k p)
      if targs == own then go todo all else
      let more := uses.filterMap fun u =>
        if u.caller? == some g then some (u.callee, u.targs.map fun t => (t.asParams g ps).subst targs) else none
      go (todo ++ more) all
    else all

/-- `Core.instanceSites` as it was before the grouping. -/
def sitesByScan (uses : Array GenericUse) (tps : Name → Array Name) (fileOf : Name → Option Nat)
    (checked : Name → Bool) (done : Name → Array Ty → Bool) : Array (InstanceSite × Name × Array Ty) := Id.run do
  let items := uses.foldl (init := #[]) fun acc u =>
    if !checked u.item || acc.contains (u.file, u.item) then acc else acc.push (u.file, u.item)
  let mut out : Array (InstanceSite × Name × Array Ty) := #[]
  let mut seen : Array (Name × Array Ty) := #[]
  for (file, item) in items do
    let direct := uses.filterMap fun u => if u.file == file && u.item == item then some (u.callee, u.targs) else none
    for (f, targs) in throughByScan uses tps direct do
      let some ff := fileOf f | continue
      let own := (tps f).mapIdx fun k p => Ty.abstract (typeParamPath f k p)
      if targs == own || seen.contains (f, targs) then continue
      seen := seen.push (f, targs)
      if let some site := siteOf ff (checked f) (done f targs) (some (file, item)) then out := out.push (site, f, targs)
  return out

/-- The generic functions, each with one type parameter `T`. -/
def fns : Array Name := #[`f0, `f1, `f2, `f3]

def tps (g : Name) : Array Name := if fns.contains g then #[`T] else #[]

/-- A pseudo-random number below `n`, and the next state. -/
def next (s : Nat) (n : Nat) : Nat × Nat :=
  let s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  ((s / 65536) % n, s)

/-- `n` random applications: in one of two files and four items, within a
generic function or not, of a generic function, at `Int`, `Bool`, a set,
or the caller's own type parameter. -/
def randomUses (seed n : Nat) : Array GenericUse := Id.run do
  let mut s := seed
  let mut out := #[]
  for _ in [0:n] do
    let (file, s1) := next s 2
    let (item, s2) := next s1 4
    let (c, s3) := next s2 5
    let (callee, s4) := next s3 4
    let (t, s5) := next s4 4
    s := s5
    let caller? := fns[c]?
    let targ := match t, caller? with
      | 0, _ => Ty.int
      | 1, _ => .bool
      | 2, _ => .set .int
      | _, some g => .abstract (typeParamPath g 0 `T)
      | _, none => .int
    out := out.push { file, item := Name.mkSimple s!"i{item}", caller?, callee := fns[callee]!, targs := #[targ] }
  return out

def fileOf (g : Name) : Option Nat := if g == `f0 || g == `f2 then some 0 else if fns.contains g then some 1 else none

/-- Whether both give the same sites for the applications of `seed`. -/
def agrees (seed : Nat) : Bool :=
  let uses := randomUses seed (seed % 40)
  let checked (n : Name) := n != `i3 && n != `f3
  let done (f : Name) (targs : Array Ty) := f == `f1 && targs == #[.bool]
  instanceSites uses tps fileOf checked done == sitesByScan uses tps fileOf checked done
    && instanceSites uses tps fileOf == sitesByScan uses tps fileOf (fun _ => true) (fun _ _ => false)

#guard (List.range 500).all agrees

-- Not vacuous: in some runs, the instances that items apply lead,
-- through generic functions' own applications, to others.
#guard (List.range 500).any fun seed =>
  let uses := randomUses seed (seed % 40)
  let direct := uses.filterMap fun u => if u.caller?.isNone then some (u.callee, u.targs) else none
  (instancesThrough (usesByCaller uses) tps direct).any (!direct.contains ·)

end Fren.Test.InstanceSites
