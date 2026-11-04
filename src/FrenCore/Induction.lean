-- keep-sorted start
import FrenCore.Check
import FrenCore.Generics
import FrenCore.Global
import FrenCore.SubsetTypes
-- keep-sorted end

/-!
# Induction on a global expectation's parameter (`Reqs/Lang/Recursion#induction`)

A global expectation that its check does not prove may be proved by
induction on a parameter of a recursive enumeration. Both front ends
generate the same function from it, a structural recursion on the
parameter whose postcondition is the expectation's claim, and check that
contract by Hoare's rule, as any other: `inductionCandidate` decides which
parameters are tried, `inductionHypotheses` the function's recursive
applications in each case, and `inductionVerdict` what the check reports.
-/

namespace Fren.Core

/-- The members that a global expectation's block may have for induction on
its parameters (`lang::induction_candidate`): assumptions, claims and
scenarios, but no call, `let`, `use` or `refines`. -/
def inductionMember (m : BlockMember) : Bool := m == .assume || m == .expect || m == .cover

/-- Whether a payload of one of the variants, whose payloads' types are
`parts`, has the type `t` (`lang::directly_recursive`). -/
def payloadOfType {T : Type} [BEq T] (parts : List (List T)) (t : T) : Bool := parts.any (·.contains t)

/-- Whether the parameter `x` of type `t` is an induction candidate
(`lang::induction_candidate`), from the block's members and applications,
the restrictions of all its parameters, and the variants' payload types.
The payloads are instantiated at `t`'s type arguments (`enumParts`). -/
def inductionCandidate {T N : Type} [BEq T] [BEq N] (members : List BlockMember) (abstract : Bool)
    (restrictions : List Bool) (t : T) (payloads : List (List T)) (x : N) (arguments : List N) : Bool :=
  members.all inductionMember && !abstract && !restrictions.contains true &&
    payloadOfType payloads t && arguments.contains x

/-- Whether a written name is a local variable available for induction,
without a binder shadowing it (`lang::induction_argument`). -/
def inductionArgument {N : Type} [BEq N] (variables : List N) (bound : N → Bool) (x : N) : Bool :=
  variables.contains x && !bound x

/-- The local variable at a structural recursion's decreasing argument,
if it is written as a variable's name and is not shadowed by a binder.
Front ends extract paths from their syntax; this function decides which
of them to collect for `inductionCandidates`. -/
def inductionArgument? (decreasing : Option Nat) (arguments : Array (Option Lean.Name))
    (variables : Array Lean.Name) (bound : Lean.Name → Bool) : Option Lean.Name := do
  let i ← decreasing
  let x ← (← arguments[i]?)
  if inductionArgument variables.toList bound x then some x else none

/-- The positions of `payloads` whose type is `t`, after the `n` parameters,
as the case's variables number them. -/
def payloadsOf {T : Type} [BEq T] (n : Nat) (payloads : List T) (t : T) : List Nat :=
  (payloads.zipIdx.filter (·.1 == t)).map (n + ·.2)

/-- The recursive applications of a case of induction on the parameter at
`i` (`lang::induction_hypotheses`): each by its arguments, as positions
among the case's variables, which are the parameters, whose types are
`params`, then the payloads of the case's variant, whose types are
`payloads`: one for each child, a payload of the parameter's type, in
order, with the child at `i` and each other parameter itself elsewhere. -/
def inductionHypotheses {T : Type} [BEq T] (params : List T) (i : Nat) (payloads : List T) : List (List Nat) :=
  match params[i]? with
  | none => []
  | some x => (payloadsOf params.length payloads x).map fun c => (List.range params.length).set i c

/-- The variants of the enumeration `t`, by `shapes`, each with its payload's
types at `t`'s type arguments; none where `t` is not an enumeration. -/
def enumParts (shapes : Lean.Name → Option DataShape) (t : Ty) : Option (Array (Array Ty)) := do
  let .enum p args := t | none
  let d ← shapes p
  if d.isRecord || d.isNewtype then none
  return d.parts.map (·.map (·.ty.subst args.toArray))

/-- Whether `t` is an enumeration with a payload of type `t` itself, by
`shapes`: induction on a value of it has children
(`lang::induction_candidate`). Its variants' payloads' types, at `t`'s type
arguments (`enumParts`), are compared with `t` by `payloadOfType`. -/
def directlyRecursive (shapes : Lean.Name → Option DataShape) (t : Ty) : Bool :=
  match enumParts shapes t with
  | some parts => payloadOfType (parts.toList.map fun ps => ps.toList.map (·.flat)) t.flat
  | none => false

/-- The candidates, in parameter order (`lang::induction_candidate`).
Both front ends supply declared parameter types and the local variables
collected by `inductionArgument?`; all candidacy decisions are made here. -/
def inductionCandidates (shapes : Lean.Name → Option DataShape) (members : List BlockMember) (abstract : Bool)
    (params : Array (Lean.Name × PTy)) (arguments : Array Lean.Name) : List Nat :=
  let restrictions := params.toList.map (·.2.restricted)
  (List.range params.size).filter fun i =>
    let (x, t) := params[i]!
    let payloads := ((enumParts shapes t.ty).getD #[]).toList.map fun ps => ps.toList.map (·.flat)
    inductionCandidate members abstract restrictions t.ty.flat payloads x arguments.toList

/-- The cases of induction on the parameter at `i`, of the parameters'
types `params`, by `shapes`: for each variant of its enumeration, in
order, its payload's types and its recursive applications
(`inductionHypotheses`). -/
def inductionCases (shapes : Lean.Name → Option DataShape) (params : Array Ty) (i : Nat) :
    Array (Array Ty × List (List Nat)) :=
  let flat := params.toList.map (·.flat)
  match params[i]?.bind (enumParts shapes) with
  | some parts => parts.map fun ps => (ps, inductionHypotheses flat i (ps.toList.map (·.flat)))
  | none => #[]

/-- Why the `fren` command makes a check inconclusive where evaluation
refutes the solver's model of it, an internal error that it reports beside
the check (`eval::confirmed_verdict`). -/
def refutedModelReason : String := "the solver's model was refuted"

/-- Whether the detail `d` of an inconclusive check says that the solver's
model contradicts Fren's semantics, an internal error that the check
reports (`model::report`): its check's translation is in doubt, so no
induction overrides it (`lang::induction_verdict`). -/
def Detail.modelRefuted : Detail → Bool
  | .refuted .. => true
  | .unknown w => w == refutedModelReason
  | _ => false

/-- What a global expectation's check reports, where its own check gives
`direct`, the solver's model of it contradicts Fren's semantics if
`refuted` (`Detail.modelRefuted`), and the inductions tried give
`attempts`, in order (`lang::induction_verdict`): a pass where its check is
inconclusive, not because of such a model, and an induction passes, and its
own check's verdict otherwise. -/
def inductionVerdict (direct : Verdict) (refuted : Bool) (attempts : List Verdict) : Verdict :=
  if direct == .inconclusive && !refuted && attempts.contains .pass then .pass else direct

/-- The name of the function generated for induction on the parameter `x`
of the claim `claim` of the global expectation `n`, whose name starts at
`position` in its file: a name of a Boolean, which no other item has. Its
parts are joined by `#`, which no written name has, and the `.` of a claim
within a Boolean block is written `#` too, as a name of one segment has no
`.`: only the claim's part can have a `#`, so the parts, and so the claim
and the parameter, are read back from the name, and two functions of one
expectation never share it. It starts with `#`,
a generated name (`generatedName`), which no source can write: nothing but
the function itself can apply it, and so rest on its contract, which is
checked only for the expectation, and no message offers it as a similar
name (`similar`). -/
def inductionFnName (n claim x : String) (position : Nat) : String :=
  s!"#induction#{n}#{String.map (fun c => if c == '.' then '#' else c) claim}#{x}#{position}?"

/-- The segments of the path that names the variant `v` of the enumeration
`e` within the module `module`: from `self` where `e` is the module's,
and otherwise from the root, which a pattern's path cannot be written from
(`Reqs/Lang/Modules#resolution`), so the generated function does not
elaborate and its candidate is not tried (`Reqs/Lang/Recursion#induction`). -/
def variantSegments (module e v : Lean.Name) : List String :=
  if e.getPrefix == module then ["self", e.getString!, v.toString] else e.components.map (·.toString) ++ [v.toString]

/-- The binder of the payload at `k` of a case, `#k`, or `#k?` where it is a
`Bool`: a generated name, which shadows nothing (`shorthandBinder`). -/
def inductionBinder (k : Nat) (bool : Bool) : String :=
  s!"#{k}" ++ (if bool then "?" else "")

/-- An arm of the generated induction function, before a front end turns
its variant path and binders into a pattern in its own syntax. -/
structure InductionArm (E : Type) where
  variant : List String
  binders : Array String
  value : E

/-- The syntax operations needed by the shared induction builder. These
only represent syntax: which applications, arms and hypotheses to build
is decided by `buildInduction`. -/
structure InductionSyntax (E : Type) where
  truth : E
  app : String → List String → E
  conjoin : E → E → E
  guard : E → E → E
  matchOn : String → Array (InductionArm E) → E

/-- The generated function's body and postcondition
(`Reqs/Lang/Recursion#induction`), in either front end's syntax. Every
arm binds all payloads and conjoins precisely `inductionHypotheses`'s
applications, with `true` at a leaf. The postcondition conjoins the
function's own application with the claim under all assumptions.
`binder` allows the hosted front end to parse temporary names before
renaming them to the unwriteable generated binders. -/
def buildInduction {E : Type} (builder : InductionSyntax E) (shapes : Lean.Name → Option DataShape)
    (module enum : Lean.Name) (variants : Array Lean.Name) (params : Array String) (types : Array Ty)
    (fn : String) (i : Nat) (assumptions : Array E) (claim : E)
    (binder : Nat → Bool → String := inductionBinder) : E × E := Id.run do
  let conjoin (es : Array E) := match es[0]? with
    | none => builder.truth
    | some e => es.extract 1 es.size |>.foldl builder.conjoin e
  let cases := inductionCases shapes types i
  let arms := (cases.zip variants).map fun ((payload, hyps), v) =>
    let binders := payload.mapIdx fun k t => binder k (t matches .bool)
    let arg (k : Nat) := if k < params.size then params[k]! else binders[k - params.size]!
    { variant := variantSegments module enum v, binders,
      value := conjoin (hyps.toArray.map fun h => builder.app fn (h.map arg)) : InductionArm E }
  let held := if assumptions.isEmpty then claim else builder.guard (conjoin assumptions) claim
  return (builder.matchOn params[i]! arms, builder.conjoin (builder.app fn params.toList) held)

end Fren.Core
