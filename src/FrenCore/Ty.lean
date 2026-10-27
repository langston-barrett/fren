-- keep-sorted start
import FrenCore.Names
-- keep-sorted end

/-!
# Types

The types of Fren's values, as the `fren` command elaborates them, and the
rule for applications over them (`lang::application`). The Lean-hosted
front end has Lean's types instead, which its elaborator compares.
-/

namespace Fren.Core

open Lean (Name)

/-- A type of values (`lang::Ty`). -/
inductive Ty where
  | bool
  | int
  /-- `Nat`, which widens to `Int` (`lang::widening`). -/
  | nat
  | string
  /-- `Set<T>`. -/
  | set (elem : Ty)
  /-- `Rel<A, B>`. -/
  | rel (a b : Ty)
  /-- `Seq<T>`. -/
  | seq (elem : Ty)
  /-- An enumeration, with its type arguments if it is generic
  (`Reqs/Lang/Generics`). -/
  | enum (path : Name) (args : List Ty)
  /-- A record, with its type arguments if it is generic. -/
  | record (path : Name) (args : List Ty)
  /-- An abstract type. -/
  | abstract (path : Name)
  /-- A newtype, with its underlying type, which is how the solver sees it
  (`Reqs/Lang/Items#newtypes`). -/
  | newtype (path : Name) (under : Ty)
  /-- A type parameter, within the declaration of a generic type, by its
  position among the declaration's and its name: what a payload's or
  field's type is before the arguments of an instance stand for its
  parameters (`Ty.subst`). -/
  | param (index : Nat) (name : Name)
  deriving Inhabited

/-! Lean derives no `DecidableEq` for `Ty`, whose type arguments are a
`List Ty`: it derives one for `Ty.Flat`, which holds them in a type of its
own, and `Ty` decides equality through it. -/

mutual
/-- `Ty`, with its type arguments in `Ty.FlatList` rather than a `List`. -/
inductive Ty.Flat where
  | bool | int | nat | string
  | set (elem : Ty.Flat)
  | rel (a b : Ty.Flat)
  | seq (elem : Ty.Flat)
  | enum (path : Name) (args : Ty.FlatList)
  | record (path : Name) (args : Ty.FlatList)
  | abstract (path : Name)
  | newtype (path : Name) (under : Ty.Flat)
  | param (index : Nat) (name : Name)

inductive Ty.FlatList where
  | nil
  | cons (head : Ty.Flat) (tail : Ty.FlatList)
end

deriving instance DecidableEq for Ty.Flat, Ty.FlatList

mutual
def Ty.flat : Ty → Ty.Flat
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .set t => .set t.flat
  | .rel a b => .rel a.flat b.flat
  | .seq t => .seq t.flat
  | .enum p as => .enum p (Ty.flatList as)
  | .record p as => .record p (Ty.flatList as)
  | .abstract p => .abstract p
  | .newtype p u => .newtype p u.flat
  | .param k n => .param k n

def Ty.flatList : List Ty → Ty.FlatList
  | [] => .nil
  | t :: ts => .cons t.flat (Ty.flatList ts)
end

mutual
def Ty.Flat.unflat : Ty.Flat → Ty
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .set t => .set t.unflat
  | .rel a b => .rel a.unflat b.unflat
  | .seq t => .seq t.unflat
  | .enum p as => .enum p as.unflat
  | .record p as => .record p as.unflat
  | .abstract p => .abstract p
  | .newtype p u => .newtype p u.unflat
  | .param k n => .param k n

def Ty.FlatList.unflat : Ty.FlatList → List Ty
  | .nil => []
  | .cons t ts => t.unflat :: ts.unflat
end

mutual
theorem Ty.unflat_flat : (t : Ty) → t.flat.unflat = t
  | .bool | .int | .nat | .string | .abstract _ | .param .. => rfl
  | .set t | .seq t => by simp [Ty.flat, Ty.Flat.unflat, Ty.unflat_flat t]
  | .rel a b => by simp [Ty.flat, Ty.Flat.unflat, Ty.unflat_flat a, Ty.unflat_flat b]
  | .enum _ as | .record _ as => by simp [Ty.flat, Ty.Flat.unflat, Ty.unflat_flatList as]
  | .newtype _ u => by simp [Ty.flat, Ty.Flat.unflat, Ty.unflat_flat u]

theorem Ty.unflat_flatList : (ts : List Ty) → (Ty.flatList ts).unflat = ts
  | [] => rfl
  | t :: ts => by simp [Ty.flatList, Ty.FlatList.unflat, Ty.unflat_flat t, Ty.unflat_flatList ts]
end

instance : DecidableEq Ty := fun a b =>
  if h : a.flat = b.flat then isTrue (by rw [← Ty.unflat_flat a, h, Ty.unflat_flat])
  else isFalse fun e => h (e ▸ rfl)

/-- The path of the abstract type that the type parameter `n`, the `k`th of
the generic function at `fn`, is within the function
(`Reqs/Lang/GenericFunctions#type-parameters`): `fn::k::n`, whose numeric
segment no path that a spec writes has. -/
def typeParamPath (fn : Name) (k : Nat) (n : Name) : Name := Name.mkStr (Name.mkNum fn k) n.toString

/-- The name of the type parameter whose abstract type is at `p`
(`typeParamPath`), if `p` is one's. -/
def typeParamName? : Name → Option String
  | .str (.num _ _) n => some n
  | _ => none

/-- The abstract type that `t` is, or that is an element type within it. -/
def Ty.abstractWithin? : Ty → Option Name
  -- A generic function's type parameter, which is an abstract type only
  -- within the function (`typeParamPath`), may be anywhere a type is.
  | .abstract p => if (typeParamName? p).isSome then none else some p
  | .set t => t.abstractWithin?
  | .rel a b => a.abstractWithin? <|> b.abstractWithin?
  | .seq t => t.abstractWithin?
  | _ => none

mutual
/-- A type as it is written, with its type arguments, if any
(`Reqs/Lang/Generics#printing`). -/
def Ty.show : Ty → String
  | .bool => "Bool"
  | .int => "Int"
  | .nat => "Nat"
  | .string => "String"
  | .set t => s!"Set<{t.show}>"
  | .rel a b => s!"Rel<{a.show}, {b.show}>"
  | .seq t => s!"Seq<{t.show}>"
  | .enum p args | .record p args =>
    showPath p ++ (if args.isEmpty then "" else "<" ++ ", ".intercalate (Ty.showAll args) ++ ">")
  | .abstract p => (typeParamName? p).getD (showPath p)
  | .newtype p _ => showPath p
  | .param _ n => n.toString

/-- Each of `ts`, as written. -/
def Ty.showAll : List Ty → List String
  | [] => []
  | t :: ts => t.show :: Ty.showAll ts
end

/-- `t` as written, but with each of the prelude's types as
`prelude::Option`, for a message about two types that print alike, one of
them a user's `Option!` (`Ty.showApart`). -/
partial def Ty.showQualified : Ty → String
  | .set t => s!"Set<{t.showQualified}>"
  | .rel a b => s!"Rel<{a.showQualified}, {b.showQualified}>"
  | .seq t => s!"Seq<{t.showQualified}>"
  | .enum p args | .record p args =>
    (if inPrelude p then "prelude::" else "") ++ showPath p
      ++ (if args.isEmpty then "" else "<" ++ ", ".intercalate (args.map (·.showQualified)) ++ ">")
  | t => t.show

/-- `a` and `b` as written, or, if they are different types that print
alike, as a user's `Option!` and the prelude's `Option` do, with the
prelude's types qualified, so that a message tells them apart. -/
def Ty.showApart (a b : Ty) : String × String :=
  if a.show == b.show && !(a == b) then (a.showQualified, b.showQualified) else (a.show, b.show)

/-- Whether an expression of type `found` is accepted where `expected` is:
the same type, or a `Nat` widened to an `Int` (`lang::widening`). -/
def Ty.widens (found expected : Ty) : Bool := found == expected || (found == .nat && expected == .int)

/-- The type of a conditional or a `match` whose branches have the types
`a` and `b`, one of which widens to the other: a `Nat` with an `Int` is
widened (`lang::operator_type`). -/
def Ty.join (a b : Ty) : Ty := if a == .nat && b == .int then .int else a

/-- `t`, widened to `Int` if it is a `Nat`: the type of a member of a set
or sequence, which is never a `Nat` (`lang::nat_place`). -/
def Ty.widen : Ty → Ty
  | .nat => .int
  | t => t

/-- The type of an integer literal, from whether a `Nat` is expected where
it is (`lang::literal_type`). -/
def literalTy (natExpected : Bool) : Ty := if natExpected then .nat else .int

/-- Whether an application is accepted, from its parameters' types and its
arguments' (`lang::application`): the arguments' types after widening, as
`lang::application` takes them, so they must equal the parameters'. -/
def applicationAccepted (params args : Array Ty) : Bool := args == params

/-- The operations on integers whose result may be a `Nat`
(`lang::nat_result`). -/
inductive NatOp where
  | div
  | mod
  | min
  | max
  | abs
  deriving Inhabited, DecidableEq, Repr

/-- Whether `op` gives a `Nat`, from whether its dividend or receiver is a
`Nat`, whether the argument of `min` or `max` is, and whether the divisor of
`div` or `mod` is positive (`lang::nat_result`). -/
def natResult : NatOp → (aNat bNat positive : Bool) → Bool
  | .div, a, _, p | .mod, a, _, p => a && p
  | .min, a, b, _ | .max, a, b, _ => a && b
  | .abs, _, _, _ => false

/-- Where the type `Nat` is written (`lang::nat_place`). -/
inductive TypePlace where
  | variable
  | parameter
  | result
  | constant
  /-- The written type of a definition of a `let` or `where`, which stands
  for its definition, so the `Nat` is never inside another value. -/
  | definition
  | field
  | payload
  /-- A payload of a recursive enumeration. -/
  | recursivePayload
  | element
  /-- A type argument of an instance of a generic type
  (`Reqs/Lang/Generics#type-parameters`). -/
  | argument
  deriving Inhabited, DecidableEq, Repr

/-- Whether `Nat` may be written at `place` (`lang::nat_place`). -/
def natPlaceAccepted : TypePlace → Bool
  | .recursivePayload | .element | .argument => false
  | _ => true

/-- The note of a type mismatch where a `Nat` is expected and an `Int`
found. -/
def narrowingNote : String :=
  "note: an `Int` is never narrowed to a `Nat`, and `a - b` and `-a` are `Int`s, even of `Nat`s"

/-- An `Int` where a `Nat` is expected, which `why` explains. -/
def narrowingMsg (why : String) : Msg :=
  { code? := some "F0304", headline := "type mismatch: expected `Nat`, found `Int`"
    label? := some "expected `Nat`, found `Int`", notes := #[why, narrowingNote] }

/-- `Nat` written at `place`, where it may not be (`lang::nat_place`). -/
def natPlaceMsg (place : TypePlace) : Msg :=
  let what := match place with
    | .recursivePayload => "the type of a payload of a recursive enumeration"
    | .argument => "a type argument"
    | _ => "the element type of a set, relation or sequence"
  { code? := some "F0338", headline := s!"`Nat` cannot be {what}", label? := some "a `Nat`"
    notes := #[if place == .argument then "note: a type argument is never `Nat`, so that an instance's type arguments are those that a construction's values give, widened"
        else "note: for now, a `Nat` is never inside a collection, nor a payload of a recursive enumeration, where its constraint would hold of every element",
      "help: use `Int`, and say where it is used that it is at least 0"] }

/-- What a `Nat` variable brings (`lang::nat_variable`). -/
inductive Brought where
  | nothing
  | assumption
  | guarantee
  deriving Inhabited, DecidableEq, Repr

/-- What a `Nat` variable brings, from whether it is an output of the
procedure itself and whether it is defined (`lang::nat_variable`). -/
def natBrought (ownOutput defined : Bool) : Brought :=
  if defined then .nothing else if ownOutput then .guarantee else .assumption

/-! ## Newtypes -/

/-- Whether a newtype is accepted (`lang::newtype`), from how many types its
parentheses hold and whether its one field's type is accepted as a record's
field is (`lang::field_type`). -/
def newtypeAccepted (nFields : Nat) (fieldAccepted : Bool) : Bool := nFields == 1 && fieldAccepted

/-- Whether a newtype is unbounded, from whether its underlying type is
(`lang::newtype`). -/
def newtypeUnbounded (underUnbounded : Bool) : Bool := underUnbounded

/-! ## Ordered types -/

/-- Whether the values of `t` are ordered, so that `<`, `<=`, `>`, `>=`,
`min` and `max` apply to them (`lang::ordered_type`): an `Int`, a `Nat` or
a `String`, and an enumeration, record or newtype declared `ordered`, which
`orderedDecl` says of its path. A pattern type is its base type here, and
a type alias the type it names, so each is ordered exactly when that is. -/
def Ty.ordered (orderedDecl : Name → Bool) : Ty → Bool
  | .int | .nat | .string => true
  | .enum p _ | .record p _ | .newtype p _ => orderedDecl p
  | _ => false

/-- The kind of declaration that `t` is, if it can be declared `ordered`. -/
def Ty.orderedDecl? : Ty → Option OrderedDecl
  | .enum .. => some .enumeration
  | .record .. => some .record
  | .newtype .. => some .newtype
  | _ => none

/-- The field `f`, of the type `ty`, which is not ordered, of the ordered
record or newtype `n` (`lang::ordered_declaration`). -/
def unorderedFieldMsg (decl : OrderedDecl) (n f : Name) (ty : Ty) : Msg :=
  let (headline, label) := if decl == .newtype then
      (s!"the ordered newtype `{n}` has the underlying type `{ty.show}`, which is not ordered", s!"`{ty.show}` is not ordered")
    else (s!"the field `{f}` of the ordered struct `{n}` has the type `{ty.show}`, which is not ordered", s!"`{ty.show}` is not ordered")
  let help := if ty.orderedDecl?.isSome then s!"help: declare `{ty.show}` `ordered`, or declare `{n}` without `ordered`"
    else s!"help: give it an ordered type, or declare `{n}` without `ordered`"
  { code? := some "F0371", headline, label? := some label
    notes := #["note: an ordered struct orders its values by their fields, in the order declared, so each field's type must be ordered",
      "note: only `Int`s, `Nat`s, `String`s and the types declared `ordered` are ordered", help] }

/-- How two values of an ordered type are compared
(`Reqs/Lang/Items#ordered-declarations`, `lang::order_plan`): numbers and
strings by their own orders, an enumeration's variants by their positions,
a newtype's values as their fields are, and a record's lexicographically,
by its fields in the order declared, each by its own type's order
(`lang::lexicographic`). Both front ends build one with `orderPlan?` and
render it in their own terms. -/
inductive OrderPlan where
  | number
  | string
  /-- An ordered enumeration, with its type arguments if it is generic. -/
  | enum (path : Name) (args : List Ty)
  /-- A record's fields, by name, in the order declared, each with how it
  is compared. -/
  | record (path : Name) (fields : List (Name × OrderPlan))
  | newtype (path : Name) (under : OrderPlan)
  deriving Inhabited

/-- How values of `t` are compared, `none` if it is not ordered or `depth`
runs out: `orderedDecl` says which declarations are ordered, and
`fieldsOf` gives a record's fields, by name, with their types, in order.
Each record or newtype within `t` takes one of `depth`; records are never
recursive, and their fields' types are declared before them, so a `depth`
greater than the number of declarations never runs out. -/
def orderPlanAt (orderedDecl : Name → Bool) (fieldsOf : Name → List (Name × Ty)) : Nat → Ty → Option OrderPlan
  | 0, _ => none
  | _ + 1, .int | _ + 1, .nat => some .number
  | _ + 1, .string => some .string
  | _ + 1, .enum p as => if orderedDecl p then some (.enum p as) else none
  | n + 1, .record p _ =>
    if orderedDecl p then
      (.record p) <$> (fieldsOf p).mapM fun (f, t) => (f, ·) <$> orderPlanAt orderedDecl fieldsOf n t
    else none
  | n + 1, .newtype p u => if orderedDecl p then .newtype p <$> orderPlanAt orderedDecl fieldsOf n u else none
  | _ + 1, _ => none

/-- How values of `t` are compared, `none` if it is not ordered
(`orderPlanAt`), where there are `nDecls` declarations. -/
def orderPlan? (orderedDecl : Name → Bool) (fieldsOf : Name → List (Name × Ty)) (nDecls : Nat) (t : Ty) :
    Option OrderPlan :=
  orderPlanAt orderedDecl fieldsOf (nDecls + 2) t

/-- Whether comparing by `o` compares strings, which the decidable core
allows only with a constant (`Reqs/Lang/Decidability#orderings`). -/
partial def OrderPlan.strings : OrderPlan → Bool
  | .string => true
  | .record _ fs => fs.any (·.2.strings)
  | .newtype _ u => u.strings
  | _ => false

/-- How two values compare whose fields, in the order declared, compare as
`cs`: as the first field that is not equal, and equal if every one is
(`lang::lexicographic`). -/
def lexCompare : List Ordering → Ordering
  | [] => .eq
  | c :: cs => if c == .eq then lexCompare cs else c

/-- The type that `t` is erased to: its underlying type, through every
newtype, as the solver sees it (`Reqs/Lang/Expressions#newtypes`). -/
def Ty.erased : Ty → Ty
  | .newtype _ u => u.erased
  | t => t

/-- The newtypes that `t` is, from the outermost in: `t` itself, if it is a
newtype, then its underlying type, if that is one, and so on. -/
def Ty.newtypePaths : Ty → Array Name
  | .newtype p u => #[p] ++ u.newtypePaths
  | _ => #[]

/-- The operators, as `lang::newtype_operator` groups them. -/
inductive NewtypeOp where
  /-- `=` and `!=`. -/
  | equality
  /-- `<`, `<=`, `>` and `>=`. -/
  | order
  /-- `+`. -/
  | add
  /-- `-` between two operands. -/
  | sub
  /-- Any other operator, such as `*`, `div`, `mod`, `++` or a prefix `-`. -/
  | other
  deriving Inhabited, DecidableEq, Repr

/-- The group of the operator `op`, which is prefix if `pre`. -/
def NewtypeOp.ofOp (op : String) (pre := false) : NewtypeOp :=
  match op, pre with
  | "=", _ | "!=", _ => .equality
  | "<", _ | "<=", _ | ">", _ | ">=", _ => .order
  | "+", false => .add
  | "-", false => .sub
  | _, _ => .other

/-- Whether a newtype whose underlying type is `under` has the operator `op`
(`lang::newtype_operator`), where `ordered` says whether the newtype is
ordered (`Ty.ordered`): the orderings if it is, and `+` and `-` exactly
when `N(a.0 + b.0)` and `N(a.0 - b.0)` are accepted, which they are of an
`Int`, of a `Nat` only for `+`, since `a.0 - b.0` is an `Int`, never
narrowed to a `Nat`, and of a newtype that has them itself. -/
def newtypeOpAccepted (op : NewtypeOp) (under : Ty) (ordered : Bool) : Bool :=
  match op, under with
  | .equality, _ => true
  | .order, _ => ordered
  | .add, .int | .add, .nat | .sub, .int => true
  | .add, .newtype _ v | .sub, .newtype _ v => newtypeOpAccepted op v false
  | _, _ => false

/-- The newtype among `a` and `b`, with its underlying type: the first. -/
def newtypeOf? (a b : Ty) : Option (Name × Ty) :=
  match a, b with
  | .newtype p u, _ | _, .newtype p u => some (p, u)
  | _, _ => none

/-- Whether `f` is a field named by digits, as the field `0` of a newtype
is. -/
def positionalField (f : Name) : Bool :=
  match f with
  | .str .anonymous d => !d.isEmpty && d.all Char.isDigit
  | _ => false

/-- A newtype that declares `n` fields, not exactly one
(`lang::newtype`). -/
def newtypeFieldsMsg (name : Name) (n : Nat) : Msg :=
  { code? := some "F0361"
    headline := s!"newtype `{showPath name}` has {n} {if n == 1 then "field" else "fields"}, but a newtype has exactly one"
    label? := some (if n == 0 then "no field" else s!"{n} fields")
    notes := #["note: `struct N(T)` declares a newtype, a distinct type with the values of `T`"]
      ++ if n == 0 then #[s!"help: give it its underlying type, as in `struct {name.getString!}(Int)`"]
        else #["help: for several fields, declare a record with named fields, as in `struct P { x: Int, y: Int }`"] }

/-- The operator `op`, which `ty`, a newtype whose underlying type is
`under`, does not have (`lang::newtype_operator`), where `ordered` says
whether it is ordered. -/
def newtypeOpMsg (op : String) (ty : Name) (under : Ty) (ordered : Bool) : Msg :=
  let accepts (o : NewtypeOp) := newtypeOpAccepted o under ordered
  let has := match accepts .order, accepts .add, accepts .sub with
    | true, true, true => "`=`, `!=`, `<`, `<=`, `>`, `>=`, and `+` and `-` of two of them"
    | true, true, false => "`=`, `!=`, `<`, `<=`, `>`, `>=`, and `+` of two of them"
    | true, _, _ => "`=`, `!=`, `<`, `<=`, `>` and `>=`"
    | false, true, true => "`=`, `!=`, and `+` and `-` of two of them"
    | false, true, false => "`=`, `!=`, and `+` of two of them"
    | false, _, _ => "`=` and `!=`"
  -- `-` of a newtype of `Nat` would be `N(a.0 - b.0)`, an `Int` where a
  -- `Nat` is expected.
  let why := if op == "-" && accepts .add then #[narrowingNote] else #[]
  { code? := some "F0362", headline := s!"newtype `{showPath ty}` has no operator `{op}`"
    label? := some s!"`{op}` of `{showPath ty}`"
    notes := #[s!"note: a newtype of `{under.show}` has {has}"] ++ why
      ++ #[s!"help: read its `{under.show}` with `.0`, as in `x.0`"] }

/-- An operator `op` whose operands are of the types `a` and `b`, which
differ, one of which is the newtype `nt` of `under`. -/
def newtypeMixMsg (op : String) (a b : Ty) (nt : Name) (under : Ty) : Msg :=
  let headline := match op with
    | "+" => s!"cannot add `{b.show}` to `{a.show}`"
    | "-" => s!"cannot subtract `{b.show}` from `{a.show}`"
    | _ => s!"cannot compare `{a.show}` with `{b.show}`"
  let other := if a == .newtype nt under then b else a
  { code? := some "F0363", headline, label? := some s!"`{a.show}` and `{b.show}`"
    notes := #[s!"note: `{showPath nt}` is a newtype, a type distinct from every other, even from `{under.show}`"]
      ++ if other == under || (other == .nat && under == .int) then
          #[s!"help: build a `{showPath nt}` with `{nt.getString!}(e)`, or read its `{under.show}` with `.0`"]
        else #[] }

/-- `R(e)` for a record `R` with named fields, or `N { ... }` for a
newtype `N`: each is built the other way. -/
def constructionMsg (ty : Name) (newtype : Bool) : Msg :=
  let n := ty.getString!
  if newtype then
    { code? := some "F0364", headline := s!"`{showPath ty}` is a newtype, not a record with named fields"
      label? := some "a newtype"
      notes := #[s!"note: a newtype has one unnamed field, its value: build it as `{n}(e)`, and read it as `x.0`"] }
  else
    { code? := some "F0364", headline := s!"`{showPath ty}` is a record with named fields, not a newtype"
      label? := some "a record with named fields"
      notes := #[s!"note: a record with named fields is built as `{n} \{ x := e, ... }`"] }

/-- A member of a set literal (or, if `seq`, an element of a sequence
literal) of the type `other`, whose first is of the type `first`, which
makes the literal one of the type `literal`. -/
def membersMsg (seq : Bool) (first other literal : String) : Msg :=
  let (what, member) := if seq then ("elements of a sequence", "element") else ("members of a set", "member")
  { code? := some "F0326", headline := s!"the {what} have different types: `{first}` and `{other}`"
    label? := some s!"a `{other}`"
    notes := #[s!"note: the first {member} is a `{first}`, so the literal is a `{literal}`"] }

end Fren.Core
