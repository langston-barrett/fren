-- keep-sorted start
import FrenCli.Parse
import FrenCore.Quantifier
-- keep-sorted end

/-!
# The guards of quantifiers (`Reqs/Lang/Quantifiers#guards`)

A quantifier's guard, read from the `fren` command's syntax: its
conjuncts, each a comparison or membership with its operands, and the
domain of each bound name of a type that is not listed, by
`Fren.Core.boundDomain`. Both the elaborator, which sets `fmf-bound` for a
quantifier with a domain, and the evaluator, which enumerates it, read it
here.
-/

namespace FrenCli

/-- The expressions directly within `e`, all of them. -/
def Expr.children : Expr → Array Expr
  | .block _ _ members => members.map (·.2)
  | .when _ _ c d | .bin _ _ c d | .pair _ c d | .index _ c d => #[c, d]
  | .ite _ c a b => #[c, a, b]
  | .not _ a | .neg _ a | .field _ a _ | .is _ a _ => #[a]
  | .app _ _ args | .set _ args | .seq _ args | .chain _ args _ => args
  | .method _ r _ args => #[r] ++ args
  | .record _ _ fs => fs.filterMap (·.2)
  | .update _ r fs => #[r] ++ fs.filterMap (·.2)
  | .match _ s arms _ => arms.foldl (init := #[s]) fun acc (_, g?, b) => acc ++ g?.toArray ++ #[b]
  | .matches _ ss arms _ => arms.foldl (init := ss) fun acc (_, g, b) => acc ++ g.toArray ++ #[b]
  | .«let» _ defs body _ => defs.map (·.2.2) ++ #[body]
  | .quant _ _ _ body | .closure _ _ body => #[body]
  | .table _ rows => tableParts rows
  | .num .. | .bool .. | .path .. | .str .. => #[]

/-- The name that the identifier `s` reads: before its first `.`. -/
def rootOf (s : String) : String := (s.splitOn ".")[0]!

/-- Whether `e` names `n` anywhere within it: as a path of one segment, the
root of a dotted name, or a field of a record literal or update written
without `:=`. A name is compared as written, whatever shadows it. -/
partial def Expr.names (n : String) (e : Expr) : Bool :=
  match e with
  | .path _ #[s] => rootOf s.name == n
  | .record _ _ fs | .update _ _ fs => fs.any (fun (f, e?) => e?.isNone && f.name == n) || e.children.any (·.names n)
  | _ => e.children.any (·.names n)

/-- What `Fren.Core.splitConjuncts` sees of a node of a guard. The parser
drops parentheses, so a node is as written. -/
instance : Inhabited (Fren.Core.GuardNode Expr) := ⟨.other⟩

partial def guardNode : Expr → Fren.Core.GuardNode Expr
  | .block sp op members => guardNode (Expr.lowerBlock sp op members)
  | .bin _ "and" a b => .conj a b
  | .bin _ op a b => .compare #[a, b] #[op]
  | .chain _ es ops => .compare es (ops.map (·.1))
  | _ => .other

/-- The condition and body of `e`, if it is a `when`. -/
def whenOf? : Expr → Option (Expr × Expr)
  | .when _ false c d => some (c, d)
  | _ => none

/-- The conjuncts of the guard of a quantifier, a `forall` if `all`, whose
body is `body` (`Fren.Core.guardConjunctsBy`). -/
def guardConjuncts (all : Bool) (body : Expr) : Array (Fren.Core.GuardConjunct Expr) :=
  Fren.Core.guardConjunctsBy guardNode whenOf? all body

/-- The bound name, among `names`, that the operand `e` is, written alone,
and the fields read from it, outermost last: `m`, `m.0` as one path, or
`(m).0` as a field of one. -/
partial def readFrom (names : Array String) : Expr → Option (Nat × List String)
  | .path _ #[s] => match s.name.splitOn "." with
    | root :: fs => (names.idxOf? root).map (·, fs)
    | [] => none
  | .field _ e f => (readFrom names e).map fun (j, fs) => (j, fs ++ [f.name])
  | _ => none

/-- The domain of the bound name at position `k` of `names`, the bound
names of a quantifier, a `forall` if `all`, with the body `body`, where
`nat` says that it is a `Nat`; and the expressions that its domain reads,
by conjunct, each with whether its bound is strict (`Fren.Core.boundDomain`).
`newtypeAt j d` says whether the bound name at `j`, with `d` fields `0`
read from it, is a newtype, so that its field `0` is the name itself
(`Fren.Core.nameAlone`); the elaborators, which set `fmf-bound` from the
guard's shape alone, read no field as the name. -/
def domainOf (all : Bool) (names : Array String) (body : Expr) (k : Nat) (nat : Bool)
    (newtypeAt : Nat → Nat → Bool := fun _ _ => false) :
    Fren.Core.GuardDomain × Array (Option (Expr × Bool)) :=
  let alone (e : Expr) : Option Nat := match readFrom names e with
    | some (j, fs) => Fren.Core.nameAlone (some j) (fs.zipIdx.map fun (f, d) => f == "0" && newtypeAt j d)
    | none => none
  let mentions (e : Expr) : List Nat := (List.range names.size).filter fun j => e.names names[j]!
  Fren.Core.boundDomain alone mentions (guardConjuncts all body) k nat

end FrenCli
