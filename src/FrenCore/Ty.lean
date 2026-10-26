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
  /-- `Set(T)`. -/
  | set (elem : Ty)
  /-- `Rel(A, B)`. -/
  | rel (a b : Ty)
  /-- `Seq(T)`. -/
  | seq (elem : Ty)
  | enum (path : Name)
  | record (path : Name)
  /-- An abstract type. -/
  | abstract (path : Name)
  /-- A newtype, with its underlying type, which is how the solver sees it
  (`Reqs/Lang/Items#newtypes`). -/
  | newtype (path : Name) (under : Ty)
  deriving Inhabited, DecidableEq

/-- The abstract type that `t` is, or that is an element type within it. -/
def Ty.abstractWithin? : Ty → Option Name
  | .abstract p => some p
  | .set t => t.abstractWithin?
  | .rel a b => a.abstractWithin? <|> b.abstractWithin?
  | .seq t => t.abstractWithin?
  | _ => none

def Ty.show : Ty → String
  | .bool => "Bool"
  | .int => "Int"
  | .nat => "Nat"
  | .string => "String"
  | .set t => s!"Set({t.show})"
  | .rel a b => s!"Rel({a.show}, {b.show})"
  | .seq t => s!"Seq({t.show})"
  | .enum p | .record p | .abstract p | .newtype p _ => showPath p

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
  deriving Inhabited, DecidableEq, Repr

/-- Whether `Nat` may be written at `place` (`lang::nat_place`). -/
def natPlaceAccepted : TypePlace → Bool
  | .recursivePayload | .element => false
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
    | _ => "the element type of a set, relation or sequence"
  { code? := some "F0338", headline := s!"`Nat` cannot be {what}", label? := some "a `Nat`"
    notes := #["note: for now, a `Nat` is never inside a collection, nor a payload of a recursive enumeration, where its constraint would hold of every element",
      "help: use `Int`, and say where it is used that it is at least 0"] }

/-- What a `Nat` variable brings (`lang::nat_variable`). -/
inductive Brought where
  | nothing
  | assumption
  | guarantee
  deriving Inhabited, DecidableEq, Repr

/-- What a `Nat` variable brings, from whether it is an output of the
component itself and whether it is defined (`lang::nat_variable`). -/
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
  | .enum p | .record p | .newtype p _ => orderedDecl p
  | _ => false

/-- The kind of declaration that `t` is, if it can be declared `ordered`. -/
def Ty.orderedDecl? : Ty → Option OrderedDecl
  | .enum _ => some .enumeration
  | .record _ => some .record
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
(`Reqs/Lang/Items#ordered-declarations`): numbers and strings by their own
orders, an enumeration's variants by their positions, a newtype's values
as their fields are, and a record's lexicographically, by its fields in
the order declared, each by its own type's order. Both front ends build one
with `orderPlan?` and render it in their own terms. -/
inductive OrderPlan where
  | number
  | string
  | enum (path : Name)
  /-- A record's fields, by name, each with how it is compared. -/
  | record (path : Name) (fields : Array (Name × OrderPlan))
  | newtype (path : Name) (under : OrderPlan)
  deriving Inhabited

/-- How values of `t` are compared, `none` if it is not ordered:
`orderedDecl` says which declarations are ordered, and `fieldsOf` gives a
record's fields, by name, with their types. An ordered record's fields are
ordered (`lang::ordered_declaration`), and records are never recursive, so
this ends. -/
partial def orderPlan? (orderedDecl : Name → Bool) (fieldsOf : Name → Array (Name × Ty)) : Ty → Option OrderPlan
  | .int | .nat => some .number
  | .string => some .string
  | .enum p => if orderedDecl p then some (.enum p) else none
  | .record p => do
    unless orderedDecl p do none
    return .record p (← (fieldsOf p).mapM fun (f, t) => return (f, ← orderPlan? orderedDecl fieldsOf t))
  | .newtype p u => do
    unless orderedDecl p do none
    return .newtype p (← orderPlan? orderedDecl fieldsOf u)
  | _ => none

/-- Whether comparing by `o` compares strings, which the decidable core
allows only with a constant (`Reqs/Lang/Decidability#strings`). -/
partial def OrderPlan.strings : OrderPlan → Bool
  | .string => true
  | .record _ fs => fs.any (·.2.strings)
  | .newtype _ u => u.strings
  | _ => false

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
