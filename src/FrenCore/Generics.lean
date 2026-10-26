-- keep-sorted start
import FrenCore.Checking
import FrenCore.Quantifier
import FrenCore.Typing
-- keep-sorted end

/-!
# Generic types (`Reqs/Lang/Generics`)

The rules for enumerations and records with type parameters that both
front ends share: substituting an instance's type arguments for its
parameters, where a parameter may be written, how many arguments a type
takes, and how a construction's arguments are inferred. Each front end
elaborates a construction's values with `inferConstruction`, so that both
infer the same arguments, check the same values against the same types,
and report the same first error.
-/

namespace Fren.Core

open Lean (Name)

mutual
/-- `t`, with `args[k]` for each type parameter `k`
(`lang::instantiation`). A parameter with no argument stays as it is, and
a newtype, which has no type parameters, is left alone. -/
def Ty.subst (args : Array Ty) : Ty → Ty
  | .param k n => args[k]?.getD (.param k n)
  | .set t => .set (t.subst args)
  | .rel a b => .rel (a.subst args) (b.subst args)
  | .seq t => .seq (t.subst args)
  | .enum p as => .enum p (Ty.substAll args as)
  | .record p as => .record p (Ty.substAll args as)
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .abstract p => .abstract p
  | .newtype p u => .newtype p u

/-- Each of `ts`, with `args` for the type parameters (`Ty.subst`). -/
def Ty.substAll (args : Array Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => t.subst args :: Ty.substAll args ts
end

mutual
/-- Whether `t` mentions the type parameter `k`. -/
def Ty.mentions (k : Nat) : Ty → Bool
  | .param j _ => j == k
  | .set t | .seq t => t.mentions k
  | .rel a b => a.mentions k || b.mentions k
  | .enum _ as | .record _ as => Ty.mentionsAny k as
  | .bool | .int | .nat | .string | .abstract _ | .newtype .. => false

/-- Whether one of `ts` mentions the type parameter `k`. -/
def Ty.mentionsAny (k : Nat) : List Ty → Bool
  | [] => false
  | t :: ts => t.mentions k || Ty.mentionsAny k ts
end

/-- The types that `t` is built from directly: an instance's type
arguments, a set's or sequence's element type, or a relation's two; none
for any other type (`lang::parts`). -/
def Ty.parts : Ty → List Ty
  | .enum _ as | .record _ as => as
  | .set t | .seq t => [t]
  | .rel a b => [a, b]
  | _ => []

/-- `t`, with the parts `ps` in place of its own (`Ty.parts`), if it has as
many (`lang::with_parts`). -/
def Ty.withParts (t : Ty) (ps : List Ty) : Ty :=
  match t, ps with
  | .enum p _, ps => .enum p ps
  | .record p _, ps => .record p ps
  | .set _, [e] => .set e
  | .seq _, [e] => .seq e
  | .rel _ _, [a, b] => .rel a b
  | t, _ => t

/-- Whether `d` and `f` have one kind, one generic type and as many parts,
so that matching one against the other matches their parts. -/
def Ty.sameShape (d f : Ty) : Bool :=
  d.parts.length == f.parts.length && match d, f with
  | .enum p _, .enum q _ | .record p _, .record q _ => p == q
  | .set _, .set _ | .seq _, .seq _ | .rel .., .rel .. => true
  | _, _ => false

/-- Whether `t` mentions a type parameter that `b` gives no argument. -/
def Ty.unknownIn (b : Array (Option Ty)) (t : Ty) : Bool :=
  (List.range b.size).any fun k => t.mentions k && b[k]?.join.isNone

mutual
/-- The argument that matching the type `found` against the declared type
`decl` gives the type parameter `k`, if it gives one
(`lang::parameter_matching`): the found type itself where `decl` is the
parameter, and otherwise, if the two have the same shape, what matching
the first of `decl`'s parts that mentions `k` against the part of `found`
in its place gives. -/
def matchParam (k : Nat) : Ty → Ty → Option Ty
  | .param j _, f => if j == k then some f else none
  | .set d, .set f | .seq d, .seq f => matchParam k d f
  | .rel d e, .rel f g => if d.mentions k then matchParam k d f else matchParam k e g
  | .enum p ds, .enum q fs | .record p ds, .record q fs =>
    if p == q && ds.length == fs.length then matchFirst k ds fs else none
  | _, _ => none

/-- `matchParam` on the first of `ds` that mentions `k`, and the one of
`fs` in its place. -/
def matchFirst (k : Nat) : List Ty → List Ty → Option Ty
  | d :: ds, f :: fs => if d.mentions k then matchParam k d f else matchFirst k ds fs
  | _, _ => none
end

/-- The first of the values whose declared types are `declared`, and which
synthesize their types where `synth` says so, that mentions the type
parameter `k`: `-1` if none does (`lang::first_giver`). -/
def firstGiver (declared : Array Ty) (synth : Array Bool) (k : Nat) : Int :=
  match (List.range declared.size).find? fun j => synth[j]?.getD false && declared[j]!.mentions k with
  | some j => j
  | none => -1

/-- The argument of the type parameter `k` of a construction whose values
have the declared types `declared`, and the types `found`, for those that
synthesize them, if it can be inferred (`lang::type_argument_inference`):
the expected instance's, if there is one, and otherwise, what matching the
first value that synthesizes its type and whose declared type mentions
`k` gives it, widened. -/
def inferArg (declared : Array Ty) (found : Array (Option Ty)) (expected? : Option (Array Ty)) (k : Nat) :
    Option Ty :=
  match expected? with
  | some as => as[k]?
  | none =>
    let j := firstGiver declared (found.map Option.isSome) k
    if j < 0 then none else do
      let f ← found[j.toNat]?.join
      return (← matchParam k declared[j.toNat]! f).widen

/-- The type arguments of a construction of a generic type with `n` type
parameters (`inferArg`), if they can all be inferred. -/
def inferArgs (n : Nat) (declared : Array Ty) (found : Array (Option Ty)) (expected? : Option (Array Ty)) :
    Option (Array Ty) :=
  (Array.range n).mapM (inferArg declared found expected?)

/-- The shape of a construction of a generic type with the type parameters
`params`, whose values have the declared types `declared` and the shapes
`shapes` (`TypeShape.construction`). -/
def constructionShape (params : Array Name) (declared : Array Ty) (shapes : Array TypeShape) : TypeShape :=
  .construction <| (List.range params.size).map fun k =>
    ((declared.zip shapes).filter (·.1.mentions k)).toList.map (·.2)

/-- Elaborates the values of a construction of a generic type with the
type parameters `params`, whose values have the declared types `declared`,
and returns its type arguments (`Reqs/Lang/Generics#type-arguments`).
`synth` says which values synthesize their types, `expected?` gives the
arguments of the instance expected of the construction, if one is, and
`unknown` reports that the arguments cannot be inferred. `elabValue k x?`
elaborates value `k`, checked against `x?` if it is given, and returns its
type, if it has one; `check k x found` checks that value `k`, of type
`found`, may stand where `x` is declared.

Values are elaborated in order, except that one whose declared type
mentions a parameter that has no argument yet, and that does not
synthesize its type, waits until every value that does has been: so each
value is elaborated once, and both front ends elaborate them in the same
order. -/
def inferConstruction [Monad m] (params : Array Name) (declared : Array Ty) (synth : Array Bool)
    (expected? : Option (Array Ty)) (unknown : m Unit) (elabValue : Nat → Option Ty → m (Option Ty))
    (check : Nat → Ty → Ty → m Unit) : m (Array Ty) := do
  let mut b : Array (Option Ty) := match expected? with
    | some as => as.map some
    | none => params.map fun _ => none
  if expected?.isNone && !(constructionShape params declared (synth.map fun s => if s then .other else .emptyLiteral)).synthesizes then
    unknown
  let current (b : Array (Option Ty)) : Array Ty := b.mapIdx fun i a => a.getD (.param i params[i]!)
  -- The parameters that a value has given an argument, or tried to.
  let mut tried := params.map fun _ => expected?.isSome
  let mut waiting := #[]
  for d in declared, k in [0:declared.size] do
    if !d.unknownIn b then
      let x := d.subst (current b)
      if let some f ← elabValue k (some x) then check k x f
    else if synth[k]?.getD false then
      if let some f ← elabValue k none then
        for i in [0:params.size] do
          if d.mentions i && !tried[i]! then
            b := b.set! i ((matchParam i d f).map (·.widen))
            tried := tried.set! i true
        check k (d.subst (current b)) f
    else waiting := waiting.push k
  for k in waiting do
    let x := declared[k]!.subst (current b)
    if let some f ← elabValue k (some x) then check k x f
  if b.any (·.isNone) then unknown
  return current b

/-! ## Values of instances -/

/-- What counting the values of an enumeration's or record's instances
needs of its declaration. -/
structure DataSig where
  isRecord : Bool
  /-- Unbounded whatever its arguments: recursive, or with a part of an
  unbounded type. -/
  unbounded : Bool
  /-- Each constructor's payload or field types, which mention its type
  parameters. -/
  ctors : Array (Array Ty)
  deriving Inhabited

/-- The number of values of `t`, if a quantifier ranges over it
(`lang::quantified_type`, `lang::instance_values`), where `sigs` gives the
declarations of enumerations and records, and `env` the numbers of values
of the type arguments, for the type parameters that `t` mentions. An
instance has as many values as its constructors have combinations of their
payloads' or fields' values, with its arguments' for its parameters
(`Reqs/Lang/Generics#recursive-unbounded-and-finite-instances`). `fuel`
bounds the depth of the types and declarations looked into: both front ends
give `valueFuel`. -/
def countIn (sigs : Name → Option DataSig) : (fuel : Nat) → List (Option Nat) → Ty → Option Nat
  | 0, _, _ => none
  | n + 1, env, t => match t with
    | .bool => some 2
    | .param k _ => env[k]?.join
    | .enum p as | .record p as => do
      let d ← sigs p
      if d.unbounded then none
      let cs := as.map (countIn sigs n env)
      let counts := d.ctors.map (·.map (countIn sigs n cs))
      unless quantifiedTypeAccepted (if d.isRecord then .record else .enum) false (counts.all (·.all Option.isSome)) do none
      return counts.foldl (fun acc c => acc + c.foldl (fun m x => m * x.getD 0) 1) 0
    | _ => none

/-- How deep `countIn` looks: deeper than any type a spec writes. -/
def valueFuel : Nat := 1000

/-- The number of values of `t`, if a quantifier ranges over it (`countIn`). -/
def Ty.valueCount (sigs : Name → Option DataSig) (t : Ty) : Option Nat := countIn sigs valueFuel [] t

/-- Whether a type with `params` type parameters may be written with `args`
type arguments (`lang::type_arguments`). -/
def typeArgumentsAccepted (params args : Nat) : Bool := args == params

/-- What the path of a type written with type arguments names
(`lang::written_type_arguments`): a built-in type, a type parameter, an
enumeration or record, which may be generic, or another item. -/
inductive TypeNamed where
  | builtin
  | parameter
  | data
  | other
  deriving Inhabited, DecidableEq, Repr

/-- Whether a type whose path names `named`, an enumeration or record with
`params` type parameters if it is one, may be written with `args` type
arguments (`lang::written_type_arguments`): only an enumeration or record
has type parameters. -/
def writtenArgumentsAccepted (named : TypeNamed) (params args : Nat) : Bool :=
  typeArgumentsAccepted (if named == .data then params else 0) args

/-! ## Messages -/

/-- The type `ty`, with the type parameters `params`, written with `n`
type arguments: not as many (`lang::type_arguments`). -/
def typeArgsMsg (ty : String) (params : Array Name) (n : Nat) : Msg :=
  let k := params.size
  let args (n : Nat) := if n == 1 then "1 type argument" else s!"{n} type arguments"
  let given := if n == 0 then "none was given" else if n == 1 then "1 was given" else s!"{n} were given"
  let headline := if k == 0 then s!"`{ty}` takes no type arguments, but {given}"
    else s!"`{ty}` takes {args k}, but {given}"
  { code? := some "F0385", headline
    label? := some (if n == 0 then "no type arguments" else args n)
    notes := if k == 0 then #[s!"note: `{ty}` is not generic"] else
      #[s!"note: `{ty}` is generic, with the type {if k == 1 then "parameter" else "parameters"} {", ".intercalate (params.toList.map fun p => s!"`{p}`")}",
        s!"help: write it with {if k == 1 then "its argument" else "one argument for each"}, as in `{ty}({", ".intercalate (List.replicate k "Int")})`"] }

/-- A construction, written `what`, of the generic type `ty`, whose type
arguments cannot be inferred (`Reqs/Lang/Generics#type-arguments`). -/
def cannotInferMsg (what ty : String) : Msg :=
  { code? := some "F0386", headline := s!"cannot infer the type arguments of `{what}`"
    label? := some s!"which instance of `{ty}`?"
    notes := #[s!"note: `{ty}` is generic, and neither what is expected here nor the values given say what its type arguments are",
      s!"help: write it where an instance of `{ty}` is expected, as where it is compared with a variable of one, or give it a type with `let`"] }

/-- Where a type parameter may not be written (`lang::type_parameter_place`). -/
inductive ParamPlace where
  | whole
  | argument
  | ownParameter
  | ownOther
  | element
  deriving Inhabited, DecidableEq, Repr

/-- Whether a type parameter is accepted at `place` (`lang::type_parameter_place`). -/
def typeParamPlaceAccepted : ParamPlace → Bool
  | .whole | .argument | .ownParameter => true
  | .ownOther | .element => false

/-- Where a recursive payload of a generic enumeration writes the
enumeration's own type (`lang::recursive_payload`): `declared` if with its
own type parameters, in order, and `nested` if within an argument of an
instance. -/
def recursivePlace (declared nested : Bool) : ParamPlace :=
  if !nested && declared then .ownParameter else .ownOther

/-- The type parameter `p`, written at `place`, where it may not be. For a
recursive payload, `own` is how the declared type should be written, and
`generic` whether the enumeration has type parameters. -/
def typeParamPlaceMsg (p : Name) (place : ParamPlace) (own : String) (generic : Bool := true) : Msg :=
  if place == .element then
    { code? := some "F0387", headline := s!"type parameter `{p}` cannot be an element type, for now"
      label? := some "an element type"
      notes := #["note: a type parameter is a payload's or field's type, or an argument of a generic type, as in `Option(T)`"] }
  else
    { code? := some "F0387", headline := s!"a recursive payload must be `{own}`"
      label? := some s!"not `{own}`"
      notes := #[if generic then s!"note: a generic enumeration's payload of its own type gives it its own type parameters, in order"
        else s!"note: a recursive payload is the enumeration itself, not within an argument of an instance, as in `{own}`"] }

/-- Whether a record with `nParams` type parameters may be declared
`ordered` if `isOrdered` (`lang::ordered_generic`): an ordered
record's fields must be of ordered types, which a type parameter's is not
known to be until an instance gives it, so a generic record is not
ordered, for now. -/
def orderedGenericAccepted (isOrdered : Bool) (nParams : Nat) : Bool := !isOrdered || nParams == 0

/-- The ordered record `n`, which has type parameters
(`orderedGenericAccepted`). -/
def orderedGenericMsg (n : Name) : Msg :=
  { code? := some "F0390", headline := s!"the ordered struct `{n}` cannot have type parameters, for now"
    label? := some "ordered, with type parameters"
    notes := #["note: an ordered struct orders its values by their fields, whose types must be ordered, and a type parameter's type is not known until an instance gives it",
      s!"help: declare `{n}` without `ordered`, or without type parameters"] }

/-- A type parameter declared again. -/
def dupTypeParamMsg (p : Name) : Msg :=
  { code? := some "F0213", headline := s!"type parameter `{p}` is defined multiple times", label? := some "defined again here" }

/-- How a recursive payload of the generic enumeration `ty` with the type
parameters `params` is written: `List(T)`. -/
def ownWritten (ty : Name) (params : Array Name) : String :=
  showPath ty ++ (if params.isEmpty then "" else "(" ++ ", ".intercalate (params.toList.map toString) ++ ")")

/-! ## Types as segments

A type, as both front ends see it for the checks of a declaration's own
type: the segments of its paths, with markers that no identifier can be
for the rest. `Set(T)` is `setSeg` and `T`'s segments, `Seq(T)` likewise,
`Rel(A, B)` is `relSeg`, `A`'s, `relSep` and `B`'s, and an instance
`G(A, B)` is `G`'s path, `argsOpen`, `A`'s, `argsSep`, `B`'s and
`argsClose`. -/

def setSeg : String := "Set("

def relSeg : String := "Rel("

def relSep : String := ","

def seqSeg : String := "Seq("

def argsOpen : String := "<("

def argsSep : String := "<,"

def argsClose : String := ")>"

/-- The prefix of the segment of a pattern type's pattern, which follows
its base type's segments, or, for a base type that is a set, relation or
sequence, precedes them, with `patOuterSeg` as its prefix. -/
def patSeg : String := "is "

def patOuterSeg : String := "is( "

/-- `segs` without the segments of pattern types' patterns. -/
def withoutPatterns (segs : Array String) : Array String :=
  segs.filter fun s => !s.startsWith patSeg && !s.startsWith patOuterSeg

/-- Whether the type `segs` is the item `name`, and whether it has it as a
set's element type (`lang::field_type`, `lang::own_type`), whatever the
patterns within it. -/
def ownIn (segs : Array String) (name : String) : Bool × Bool :=
  let segs := withoutPatterns segs
  let core := segs.filter fun s => s != setSeg && s != relSeg && s != relSep && s != seqSeg
  let isName := core.size == 1 && core[0]! == name
  (isName && core.size == segs.size, core.size < segs.size && core.any (· == name))

/-- Whether the type `segs` is the item `name` being declared, with type
arguments or not; whether those are its own type parameters, whose names
are `params`, in order; and whether `name` is within the arguments of an
instance that `segs` is, rather than within a set's element type
(`lang::own_type`). -/
def ownArgs (segs : Array String) (name : String) (params : Array String) : Bool × Bool × Bool :=
  let segs := withoutPatterns segs
  let whole := segs[0]! == name && (segs.size == 1 || segs[1]! == argsOpen)
  let asDeclared := argsOpen :: params.toList.intersperse argsSep ++ [argsClose]
  let declared := if params.isEmpty then segs.size == 1 else (segs.extract 1 segs.size).toList == asDeclared
  let elems := segs[0]! == setSeg || segs[0]! == seqSeg || segs[0]! == relSeg
  let nested := !elems && (if whole then segs.extract 1 segs.size else segs).any (· == name)
  (whole, declared, nested)

/-- A type parameter `p` with the name of what `r` describes: a built-in
type or an item in scope. -/
def typeParamNameMsg (p : Name) (what : String) : Msg :=
  { code? := some "F0388", headline := s!"type parameter `{p}` has the name of {what}"
    label? := some "already a name"
    notes := #["note: within its declaration, a type parameter's name must mean only the parameter",
      s!"help: rename it, as in `T`"] }

end Fren.Core
