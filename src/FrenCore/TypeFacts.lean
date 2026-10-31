-- keep-sorted start
import FrenCore.SubsetTypes
-- keep-sorted end

/-!
# Facts of types over their constituents

Whether a type is recursive, finite, unbounded and listed, from the types
it is built from (`lang::type_facts`), which both front ends compute here.
A type is a `Node`: its type without patterns, whether its pattern bounds
it to finitely many integers, and the declared types of its parts. That is
all of a declared type (`PTy`) that these facts depend on.

The types a type is built from are found by a closure with a visited list,
and fuel for the steps it takes. When the fuel runs out, or a declaration
is missing, the facts are unknown (`none`), and each caller treats them as
the answer that accepts the least: unbounded, not finite, not listed and
recursive (`TypeFacts.unknown`).
-/

namespace Fren.Core

open Lean (Name)

mutual
/-- A declared type, as far as the facts of `lang::type_facts` depend on it
(`lang::DeclaredTy`). -/
inductive Node where
  | mk (ty : Ty) (bounded : Bool) (elems : Nodes)

/-- The declared types of a type's parts, in order. -/
inductive Nodes where
  | nil
  | cons (head : Node) (tail : Nodes)
end

deriving instance DecidableEq for Node, Nodes

instance : Inhabited Node := ⟨.mk .bool false .nil⟩

/-- The type of a node, without patterns. -/
def Node.ty : Node → Ty
  | .mk t _ _ => t

/-- Whether a node's pattern bounds it to finitely many integers
(`lang::pattern_finite`). -/
def Node.bounded : Node → Bool
  | .mk _ b _ => b

def Nodes.toList : Nodes → List Node
  | .nil => []
  | .cons n ns => n :: ns.toList

def Nodes.ofList : List Node → Nodes
  | [] => .nil
  | n :: ns => .cons n (Nodes.ofList ns)

/-- Whether the pattern `p?` of a type `t` bounds it to finitely many
integers: an `Int` or `Nat` with a pattern of finitely many integers
(`lang::pattern_finite`). -/
def boundedPattern (t : Ty) (p? : Option Pat) : Bool :=
  match t with
  | .int => (p?.bind (·.intCount?)).isSome
  | .nat => (p?.bind (·.intCount? (some 0))).isSome
  | _ => false

/-- The node of a declared type. -/
partial def PTy.node (t : PTy) : Node :=
  .mk t.ty (boundedPattern t.ty t.pat?) (Nodes.ofList (t.parts.toList.map PTy.node))

/-- The node of a type without patterns. -/
def Ty.node (t : Ty) : Node := (PTy.plain t).node

mutual
/-- A declared type with the facts of a node: a bounded node has a pattern
of one integer, which bounds it as its own did. -/
def Node.pty : Node → PTy
  | .mk t b es => { ty := t, pat? := if b then some (.int (some 0) (some 0)) else none, elems := (Nodes.pty es).toArray }

def Nodes.pty : Nodes → List PTy
  | .nil => []
  | .cons n ns => n.pty :: Nodes.pty ns
end

/-- What a type's former gives it by itself (`lang::former`): whether it is
finite when its constituents are, and whether its values can be
arbitrarily large whatever its constituents. A subset type's former is
its base type's, and it is also finite when its pattern-test invariant
bounds it. -/
structure Former where
  finite : Bool
  growing : Bool
  deriving Inhabited, DecidableEq, Repr

/-- The former of a node (`lang::former`, `lang::own_finite?`). -/
def Node.former (n : Node) : Former :=
  match n.ty with
  | .bool | .enum .. | .record .. | .newtype .. => { finite := true, growing := false }
  | .int | .nat => { finite := n.bounded, growing := false }
  | .abstract _ | .param .. => { finite := false, growing := false }
  | .string | .seq _ => { finite := false, growing := true }
  | .set _ | .rel .. => { finite := true, growing := true }

/-- The constituents of a node, one layer: its element types, the types of
an enumeration's payloads or of a record's fields, with its arguments for
its type parameters, or a newtype's underlying type, from the declarations
`shapes`. `none` if a declaration is missing. -/
def Node.next (shapes : Name → Option DataShape) (n : Node) : Option (List Node) :=
  match n with
  | .mk (.set _) _ _ | .mk (.seq _) _ _ | .mk (.rel ..) _ _ => some (n.pty.parts.toList.map PTy.node)
  | .mk (.enum p _) _ _ | .mk (.record p _) _ _ => do
    let d ← shapes p
    some ((d.inst n.pty.parts).parts.toList.flatMap fun ps => ps.toList.map PTy.node)
  | .mk (.newtype p u) _ _ => some [((shapes p).bind (·.parts[0]? >>= (·[0]?)) |>.getD (PTy.plain u)).node]
  | _ => some []

/-- The closure of `next` from the nodes `todo`, with those of `seen`
already visited, in at most `fuel` steps: every node that `next` reaches in
zero or more steps. `none` if the fuel runs out or `next` fails. -/
def reach (next : Node → Option (List Node)) : Nat → List Node → List Node → Option (List Node)
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, t :: todo, seen =>
    if t ∈ seen then reach next fuel todo seen
    else do
      let ns ← next t
      reach next fuel (ns ++ todo) (t :: seen)

/-- The steps that `reach` may take: more than any type a spec writes is
built from. -/
def reachFuel : Nat := 10000

/-- The facts of a type (`lang::type_facts`, `lang::quantified_type`). -/
structure TypeFacts where
  recursive : Bool
  finite : Bool
  unbounded : Bool
  deriving Inhabited, DecidableEq, Repr

/-- Whether a quantifier over the type is expanded: finite and not
unbounded (`lang::quantified_type`). -/
def TypeFacts.listed (f : TypeFacts) : Bool := f.finite && !f.unbounded

/-- The facts that accept the least, for a type whose facts are unknown. -/
def TypeFacts.unknown : TypeFacts := { recursive := true, finite := false, unbounded := true }

/-- Whether the closure of `n`'s constituents reaches `n`, from the
declarations `shapes`, if it is known (`lang::type_facts`'s `recursive?`). -/
def recursive? (shapes : Name → Option DataShape) (n : Node) : Option Bool := do
  let ns ← Node.next shapes n
  let r ← reach (Node.next shapes) reachFuel ns []
  some (r.contains n)

/-- The facts of `n` from the declarations `shapes`, if they are known
(`lang::type_facts`): from the types it is built from, each one's former,
and whether each is recursive. -/
def typeFacts? (shapes : Name → Option DataShape) (n : Node) : Option TypeFacts := do
  let built ← reach (Node.next shapes) reachFuel [n] []
  let rec_ (u : Node) : Bool := (recursive? shapes u).getD true
  if built.all fun u => (recursive? shapes u).isSome then
    some {
      recursive := rec_ n
      finite := built.all fun u => u.former.finite && !rec_ u
      unbounded := built.any fun u => u.former.growing || rec_ u
    }
  else none

/-- The facts of `n`, or the ones that accept the least if they are
unknown. -/
def typeFacts (shapes : Name → Option DataShape) (n : Node) : TypeFacts :=
  (typeFacts? shapes n).getD .unknown

/-- Whether an enumeration's variant is recursive: one of its payloads' types
is the enumeration, or a type built from it (`lang::well_founded`). A
variant whose facts are unknown is recursive. -/
def recursiveVariant (shapes : Name → Option DataShape) (enum : Node) (payloads : List Node) : Bool :=
  payloads.any fun u => u == enum || (reach (Node.next shapes) reachFuel [u] []).all (·.contains enum)

end Fren.Core
