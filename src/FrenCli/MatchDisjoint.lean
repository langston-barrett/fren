-- keep-sorted start
import FrenCore.Patterns
-- keep-sorted end

/-!
# Disjoint constructor arms in standalone SMT paths

Resolved patterns are interpreted at one scrutinee's type. A constructor
index is an identity only within that datatype. This deliberately recognizes
only constructors whose fields are binders or wildcards; it does not try to
prove disjointness of literals, nested patterns or alternatives.
-/

namespace FrenCli

open Fren.Core (Pat PatTy)

/-- The constructor tested by `p`, when all its fields test nothing.
This inspects the resolved pattern, including every immediate field. -/
def plainMatchConstructor? : Pat → Option Nat
  | .ctor index fields =>
    if fields.all (fun p => match p with | .wild _ => true | _ => false) then some index else none
  | _ => none

/-- Whether a standalone SMT arm path can omit all earlier exclusions.
The caller supplies resolved patterns and the actual optional guards.
Every arm involved must be an unguarded, plain constructor of the same
scrutinee datatype, with the current constructor distinct from each earlier
one. Unknown types and synthetic multi-scrutinee vectors retain exclusions.
This decision changes no pattern resolution or source labels. -/
def omitMatchExclusions {α : Type} (ty : PatTy) (current : Pat)
    (guard : Option α) (earlier : Array (Pat × Option α)) : Bool :=
  match ty, guard, plainMatchConstructor? current with
  | .enum path _, none, some index =>
    path != Fren.Core.matchVectorPath && earlier.all fun (pattern, guard) =>
      guard.isNone && (plainMatchConstructor? pattern).any (· != index)
  | _, _, _ => false

end FrenCli
