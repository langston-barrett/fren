-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Pattern tests that match every value of their scrutinee's type, or
bind a name that what follows reads: `_`, alternatives that cover an
enumeration, a variant of an enumeration of one variant, a binder, and
payload binders of one-variant enumerations, nested or not, each where
the binding is visible, so that none is an error (`F0334`). Both front
ends decide `irrefutable_is` and `is_equality` on them with
`Core.irrefutableIsAt` (`lint::irrefutable_is`). -/
def patternTests : R String := do
  let decls := "pub enum Zt { A, B(Int), C(Bool) }\npub enum Zo { Only }\npub enum Zw { W(Int) }\n" ++
    "pub enum Zn { N(Zw) }\npub enum Zq { Q(Int, Bool) }\n"
  let forms : Array (String × String) := #[
    ("Bool", "t is _"),
    ("Bool", "t is Zt::A | Zt::B(_) | Zt::C(_)"),
    ("Bool", "t is Zt::C(true) | Zt::C(false) | Zt::A | Zt::B(_)"),
    ("Bool", "o is Zo::Only"),
    ("Bool", "not (o is _)"),
    ("Bool", "w is Zw::W(_)"),
    ("Int", "if n is zm then zm else 0"),
    ("Bool", "(when t is Zt::B(zy), zy > 0)"),
    ("Bool", "t is Zt::B(zy) and zy > 0"),
    ("Int", "if w is Zw::W(zx) then zx else 0"),
    ("Int", "if v is Zn::N(Zw::W(zz)) then zz else 0"),
    ("Bool", "q is Zq::Q(zk, zb?) and (zb? or zk > 0)"),
    ("Int", "if q is Zq::Q(_, zb?) then (if zb? then 1 else 0) else 2")
  ]
  let mut results := #[]
  let mut body := ""
  for (ty, e) in forms, k in [0:forms.size] do
    unless ← chance 60 do continue
    let name := if ty == "Bool" then s!"zr{k}?" else s!"zr{k}"
    results := results.push (if ty == "Bool" then name else s!"{name}: {ty}")
    body := body ++ (if ty == "Bool" then s!"    ensure zk{k}: {name} iff {e}\n" else s!"    ensure zk{k}: {name} = {e}\n")
  if results.isEmpty then return ""
  return decls ++ s!"pub proc zpt(t: Zt, o: Zo, w: Zw, v: Zn, q: Zq, n: Int): ({", ".intercalate results.toList}) \{\n{body}}\n"

end FrenTest.FuzzFrontends.Wide
