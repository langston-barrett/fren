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

/-- `inferConstruction`'s and `inferCall`'s elaboration of the values: in
order, but for those that wait, and each value once. `argOf found i` is the
argument of the type parameter `i`, if it has one, from the types `found`
of the values that synthesize them and have been elaborated (`inferArg`,
`inferCallArg`): before any value is, what is expected gives it; once the
first value that gives it one is, that value's. -/
def inferFrom [Monad m] (params : Array Name) (declared : Array Ty) (synth : Array Bool)
    (argOf : Array (Option Ty) → Nat → Option Ty) (unknown : m Unit) (elabValue : Nat → Option Ty → m (Option Ty))
    (check : Nat → Ty → Ty → m Unit) : m (Array Ty) := do
  -- The types of the values that synthesize them, as they are elaborated.
  let mut found : Array (Option Ty) := declared.map fun _ => none
  let init := params.mapIdx fun i _ => argOf found i
  let mut b : Array (Option Ty) := init
  let current (b : Array (Option Ty)) : Array Ty := b.mapIdx fun i a => a.getD (.param i params[i]!)
  -- The parameters that a value has given an argument, or tried to.
  let mut tried := params.mapIdx fun i _ => (init[i]?.join).isSome
  let mut waiting := #[]
  for d in declared, k in [0:declared.size] do
    if !d.unknownIn b then
      let x := d.subst (current b)
      if let some f ← elabValue k (some x) then check k x f
    else if synth[k]?.getD false then
      if let some f ← elabValue k none then
        found := found.set! k (some f)
        for i in [0:params.size] do
          if d.mentions i && !tried[i]! then
            -- This value is the first that gives `i` an argument.
            b := b.set! i (argOf found i)
            tried := tried.set! i true
        check k (d.subst (current b)) f
    else waiting := waiting.push k
  for k in waiting do
    let x := declared[k]!.subst (current b)
    if let some f ← elabValue k (some x) then check k x f
  if b.any (·.isNone) then unknown
  return current b

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
  let init : Array (Option Ty) := match expected? with
    | some as => as.map some
    | none => params.map fun _ => none
  if expected?.isNone && !(constructionShape params declared (synth.map fun s => if s then .other else .emptyLiteral)).synthesizes then
    unknown
  inferFrom params declared synth (fun found i => if expected?.isSome then (init[i]?).join else inferArg declared found none i)
    unknown elabValue check

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
    -- A newtype has its underlying type's values (`Reqs/Lang/Items#newtypes`).
    | .newtype _ u => countIn sigs n env u
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
        s!"help: write it with {if k == 1 then "its argument" else "one argument for each"}, as in `{ty}<{", ".intercalate (List.replicate k "Int")}>`"] }

/-! ## Angle brackets (`Reqs/Lang/Generics#angle-brackets`) -/

/-- The bracket after a type's name, or after the name of a generic
declaration, as the parser reads it (`lang::Bracket`). -/
inductive Bracket where
  | angle
  | paren
  | other
  deriving BEq, DecidableEq, Repr

/-- What the bracket after a type's name, or after a declaration's name,
does (`lang::AfterName`). -/
inductive AfterName where
  /-- Opens its type arguments or type parameters. -/
  | opens
  /-- Is a `(` that would have opened them before they were written in
  angle brackets (`F0155`, `F0156`). -/
  | parenthesized
  /-- Is a `<` after a space (`F0144`). -/
  | spaced
  /-- Is not the type's: the type, or the name, ends before it. -/
  | ends
  deriving BEq, DecidableEq, Repr

/-- The bracket that the punctuator `p` is. -/
def Bracket.of (p : String) : Bracket :=
  if p == "<" then .angle else if p == "(" then .paren else .other

/-- What the bracket `b` after a type's name does, if it follows the name
directly (`adjacent`) or after a space, a line break or a comment
(`lang::type_bracket`). -/
def afterName (b : Bracket) (adjacent : Bool) : AfterName :=
  match b with
  | .angle => if adjacent then .opens else .spaced
  | .paren => if adjacent then .parenthesized else .ends
  | .other => .ends

/-- A character of a type or a declaration written with parentheses, as
both front ends write it in the suggestion that replaces it
(`lang::angle_char`): a parenthesis that opened or closed type arguments or
type parameters (`swapped`) is an angle bracket, and any other character,
comments' and string literals' included, is copied. -/
def angleChar (ch : String) (swapped : Bool) : String :=
  if swapped && ch == "(" then "<" else if swapped && ch == ")" then ">" else ch

/-- The text of a type or a declaration, from its source's characters, each
with whether it is one of the parentheses to write as an angle bracket. -/
def angleText (chars : Array (Char × Bool)) : String :=
  chars.foldl (fun out (c, b) => out ++ angleChar (String.singleton c) b) ""

/-- A type written with its type arguments in parentheses, as `Option(Int)`
was before they were written in angle brackets: `written` is the type
with each of its type arguments' parentheses made `<` and `>`. -/
def parenTypeArgsMsg (written : String) : Msg :=
  { code? := some "F0155", headline := "type arguments are written in angle brackets"
    label? := some "type arguments in parentheses"
    notes := #["note: a type's arguments follow its name in `<` and `>`, as in `Set<Int>` and `Option<Int>`"]
    fixes := #[{ msg := s!"write `{written}`", replacement := written }] }

/-- A generic type's or function's type parameters, written in parentheses
as `enum Option(T)` and `fn f(T)(x: T)` were: `written` is its name with
them in angle brackets. -/
def parenTypeParamsMsg (written : String) : Msg :=
  { code? := some "F0156", headline := "type parameters are written in angle brackets"
    label? := some "type parameters in parentheses"
    notes := #["note: a generic type's or function's type parameters follow its name in `<` and `>`, as in `enum Option<T>` and `fn f<T>(x: T): T`"]
    fixes := #[{ msg := s!"write `{written}`", replacement := written }] }

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
      notes := #["note: a type parameter is a payload's or field's type, or an argument of a generic type, as in `Option<T>`"] }
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
parameters `params` is written: `List<T>`. -/
def ownWritten (ty : Name) (params : Array Name) : String :=
  showPath ty ++ (if params.isEmpty then "" else "<" ++ ", ".intercalate (params.toList.map toString) ++ ">")

/-! ## Types as segments

A type, as both front ends see it for the checks of a declaration's own
type: the segments of its paths, with markers that no identifier can be
for the rest. `Set<T>` is `setSeg` and `T`'s segments, `Seq<T>` likewise,
`Rel<A, B>` is `relSeg`, `A`'s, `relSep` and `B`'s, and an instance
`G<A, B>` is `G`'s path, `argsOpen`, `A`'s, `argsSep`, `B`'s and
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

/-! ## Generic functions (`Reqs/Lang/GenericFunctions`) -/

mutual
/-- `t`, with the type parameter at `typeParamPath fn k n` for each abstract
type that is one of the type parameters `params` of the generic function at
`fn`: a type as the function's signature declares it, from the type that
its body sees (`Ty.asAbstract`). -/
def Ty.asParams (fn : Name) (params : Array Name) : Ty → Ty
  | .abstract p =>
    match (List.range params.size).find? fun k => typeParamPath fn k params[k]! == p with
    | some k => .param k params[k]!
    | none => .abstract p
  | .set t => .set (t.asParams fn params)
  | .rel a b => .rel (a.asParams fn params) (b.asParams fn params)
  | .seq t => .seq (t.asParams fn params)
  | .enum p as => .enum p (Ty.asParamsAll fn params as)
  | .record p as => .record p (Ty.asParamsAll fn params as)
  | .newtype p u => .newtype p u
  | t => t

/-- Each of `ts`, as `Ty.asParams` gives it. -/
def Ty.asParamsAll (fn : Name) (params : Array Name) : List Ty → List Ty
  | [] => []
  | t :: ts => t.asParams fn params :: Ty.asParamsAll fn params ts
end

/-- `t`, as the body of the generic function at `fn`, with the type
parameters `params`, sees it: each type parameter an abstract type of its
own (`Reqs/Lang/GenericFunctions#type-parameters`). -/
def Ty.asAbstract (fn : Name) (params : Array Name) (t : Ty) : Ty :=
  t.subst (params.mapIdx fun k n => .abstract (typeParamPath fn k n))

/-- Whether a function may have `params` type parameters
(`lang::generic_function`): if it has any, each is mentioned by its
signature, whether the function is defined or not. -/
def genericFunctionAccepted (params : Nat) (unmentioned : Bool) : Bool :=
  params == 0 || !unmentioned

/-- Whether the type parameter `k` is mentioned by one of the parameters'
declared types `declared` or by the result's, `result`. -/
def inSignature (declared : Array Ty) (result : Ty) (k : Nat) : Bool :=
  result.mentions k || declared.any (·.mentions k)

/-- The first of `n` type parameters that the signature does not mention
(`inSignature`), if one is not. -/
def firstUnmentioned? (declared : Array Ty) (result : Ty) (n : Nat) : Option Nat :=
  (List.range n).find? fun k => !inSignature declared result k

/-- The arguments that matching the type `expected?`, if one is expected of
an application, against the declared result type `result` gives each of
`n` type parameters, widened (`lang::call_type_argument`). -/
def expectedArgs (result : Ty) (expected? : Option Ty) (n : Nat) : Array (Option Ty) :=
  (Array.range n).map fun k => expected?.bind fun x => (matchParam k result x).map (·.widen)

/-- The argument of the type parameter `k` of an application of a generic
function whose parameters have the declared types `declared`, and whose
arguments the types `found`, for those that synthesize them, with the
declared result type `result`, if it can be inferred
(`lang::call_type_argument`): what matching the expected type, if there is
one, against the result gives it, and otherwise what the first argument
that gives it one gives it (`inferArg`). -/
def inferCallArg (declared : Array Ty) (found : Array (Option Ty)) (result : Ty) (expected? : Option Ty) (k : Nat) :
    Option Ty :=
  match (expectedArgs result expected? (k + 1))[k]?.join with
  | some a => some a
  | none => inferArg declared found none k

/-- Elaborates the arguments of an application of a generic function with
the type parameters `params`, whose parameters have the declared types
`declared` and whose result the declared type `result`, and returns its type
arguments (`Reqs/Lang/GenericFunctions#applications`), as
`inferConstruction` does a construction's, in the same order
(`lang::call_order`): what matching the type expected of the application,
`expected?`, against the result gives a type parameter stands for an
expected instance's argument. `unknown` reports that the arguments cannot
be inferred, before any argument is elaborated if some type parameter has
neither an argument from what is expected nor an argument that synthesizes
its type and whose declared type mentions it. -/
def inferCall [Monad m] (params : Array Name) (declared : Array Ty) (result : Ty) (synth : Array Bool)
    (expected? : Option Ty) (unknown : m Unit) (elabValue : Nat → Option Ty → m (Option Ty))
    (check : Nat → Ty → Ty → m Unit) : m (Array Ty) := do
  let init := expectedArgs result expected? params.size
  if (List.range params.size).any fun k => (init[k]?.join).isNone && firstGiver declared synth k < 0 then unknown
  inferFrom params declared synth (inferCallArg declared · result expected?) unknown elabValue check

/-- The shape of an application of a generic function with `n` type
parameters, whose parameters have the declared types `declared`, its result
the declared type `result`, and its arguments the shapes `shapes`: a
construction whose parts are the type parameters that the result mentions
(`Reqs/Lang/GenericFunctions#applications`). -/
def callShape (n : Nat) (declared : Array Ty) (result : Ty) (shapes : Array TypeShape) : TypeShape :=
  .construction <| ((List.range n).filter result.mentions).map fun k =>
    ((declared.zip shapes).filter (·.1.mentions k)).toList.map (·.2)

/-- The type of an application of a generic function whose declared result
type is `result`, with the type arguments `args` (`lang::call_instance`). -/
def callType (result : Ty) (args : Array Ty) : Ty := result.subst args

/-- The parameters' and result's types of the instance of a generic
function whose parameters and result have the declared types `declared`
and `result`, at the type arguments `args` (`lang::uninterpreted_instance`):
each declared type instantiated with them. Of a generic function without a
body, it is the signature of the unknown function that the solver sees for
that instance. -/
def instanceSig (declared : Array Ty) (result : Ty) (args : Array Ty) : Array Ty × Ty :=
  (declared.map (·.subst args), result.subst args)

/-- A type as it is written, but with each generic function's type
parameter by its whole path, so that two functions' are told apart: the key
of an instance of a generic function. -/
partial def Ty.instKey : Ty → String
  | .set t => s!"Set<{t.instKey}>"
  | .rel a b => s!"Rel<{a.instKey}, {b.instKey}>"
  | .seq t => s!"Seq<{t.instKey}>"
  | .enum p [] | .record p [] => showPath p
  | .enum p as | .record p as => s!"{showPath p}<{", ".intercalate (as.map Ty.instKey)}>"
  | .abstract p => showPath p
  | t => t.show

/-- The type arguments `args` of an instance of a generic function, as its
name has them after the function's (`Ty.instKey`), as in `<Int>`
(`Reqs/Lang/GenericFunctions#meaning`). -/
def instanceText (args : Array Ty) : String := s!"<{", ".intercalate (args.toList.map Ty.instKey)}>"

/-- The name of the instance of the function at `path` with the type
arguments `args`, as messages show it, as `pick<Int>`. -/
def instanceName (path : Name) (args : Array Ty) : Name :=
  match path with
  | .str p s => .str p (s ++ instanceText args)
  | p => .str p (instanceText args)

/-- Whether `t` mentions a generic function's type parameter, an abstract
type of its own (`typeParamPath`): an instance at it is checked with
finite-model finding, as the function's own check at its type parameters'
sorts is. -/
partial def Ty.hasTypeParam : Ty → Bool
  | .abstract p => (typeParamName? p).isSome
  | .set t | .seq t => t.hasTypeParam
  | .rel a b => a.hasTypeParam || b.hasTypeParam
  | .enum _ as | .record _ as => as.any Ty.hasTypeParam
  | _ => false

/-- An application of the generic function `callee` at the type arguments
`targs`, written in the item `item` (a component, global expectation,
refinement or function, by its path) of the file `file`, and within the
generic function `caller?`, if it is in one, whose type parameters `targs`
may mention (`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`).
Both front ends record each, in the order in which they elaborate them. -/
structure GenericUse where
  file : Nat
  item : Name
  caller? : Option Name
  callee : Name
  targs : Array Ty
  deriving Inhabited, BEq

/-- The instances that applying the instances `start` applies, them
included: each, and, for an instance of a generic function, its
applications within the function at that instance, and so on, each once,
in the order found, where `tps` gives each generic function's type
parameters. A function's applications at its own type parameters are its
own, and lead nowhere else. -/
partial def instancesThrough (uses : Array GenericUse) (tps : Name → Array Name) (start : Array (Name × Array Ty)) :
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

/-- Where the contract of an instance of a generic function without a body
is checked, where its check at the type parameters' sorts does not pass
(`lang::instance_site`): with the function's own, or with an item's. -/
inductive InstanceSite where
  | function
  | item (file : Nat) (item : Name)
  deriving Inhabited, BEq

/-- Where an instance of a generic function without a body declared in the
file `functionFile` is checked in a run of checks (`lang::instance_site`):
nowhere if an earlier run checked it (`done`) or no item that this run
checks uses it; with the function's own check if this run checks it
(`functionChecked`) and the first item, in order, that this run checks and
whose checks use the instance, `first?`, is in the function's file; and
with that item's otherwise. The `fren` command checks every item in one
run, so its site is the first item that uses it, or the function's. -/
def siteOf (functionFile : Nat) (functionChecked done : Bool) : Option (Nat × Name) → Option InstanceSite
  | none => none
  | some (file, item) =>
    if done then none
    else some (if functionChecked && file == functionFile then .function else .item file item)

/-- Each instance that the items that a run checks use, of a generic
function that `fileOf` gives the file of, but its own, with where the run
checks its contract (`siteOf`): an item's checks use the instances that its
applications apply, through the generic functions' (`instancesThrough`).
The items are taken in the order of their first applications; `checked`
says which this run checks, by path, a function's by its own, and `done`
which instances an earlier run checked. -/
def instanceSites (uses : Array GenericUse) (tps : Name → Array Name) (fileOf : Name → Option Nat)
    (checked : Name → Bool := fun _ => true) (done : Name → Array Ty → Bool := fun _ _ => false) :
    Array (InstanceSite × Name × Array Ty) := Id.run do
  let items := uses.foldl (init := #[]) fun acc u =>
    if !checked u.item || acc.contains (u.file, u.item) then acc else acc.push (u.file, u.item)
  let mut out : Array (InstanceSite × Name × Array Ty) := #[]
  let mut seen : Array (Name × Array Ty) := #[]
  for (file, item) in items do
    let direct := uses.filterMap fun u => if u.file == file && u.item == item then some (u.callee, u.targs) else none
    for (f, targs) in instancesThrough uses tps direct do
      let some ff := fileOf f | continue
      let own := (tps f).mapIdx fun k p => Ty.abstract (typeParamPath f k p)
      if targs == own || seen.contains (f, targs) then continue
      seen := seen.push (f, targs)
      if let some site := siteOf ff (checked f) (done f targs) (some (file, item)) then out := out.push (site, f, targs)
  return out

/-- Whether each application of an instance of a generic function without
a body, whose declared result type is `result`, brings that it is at least
0 (`lang::uninterpreted_instance`): exactly when `result` is `Nat`, since a
type argument is never a `Nat` (`expectedArgs`, `inferArg`). -/
def instanceNat (result : Ty) : Bool := result == .nat

/-- The type parameter `p` of the generic function `f`, which its signature
does not mention (`lang::generic_function`). -/
def unmentionedTypeParamMsg (f p : Name) : Msg :=
  { code? := some "F0400", headline := s!"type parameter `{p}` of `{f}` cannot be inferred"
    label? := some "not in the signature"
    notes := #[s!"note: a type parameter's argument is inferred at each application from the parameters' and the result's types, and none of them mentions `{p}`",
      s!"help: mention `{p}` in a parameter's type or the result's, or remove it"] }

/-- An application of the generic function `f`, whose type arguments
cannot be inferred (`Reqs/Lang/GenericFunctions#applications`). -/
def cannotInferCallMsg (f : String) : Msg :=
  { code? := some "F0400", headline := s!"cannot infer the type arguments of `{f}`"
    label? := some s!"which instance of `{f}`?"
    notes := #[s!"note: `{f}` is generic, and neither what is expected here nor its arguments say what its type arguments are",
      "help: write it where its result's type is expected, as where it is compared with a variable, or give it a type with `let`"] }

end Fren.Core
