-- keep-sorted start
import FrenCli.Parse.ExprSyntax
import FrenCore.Check.Types
-- keep-sorted end

/-! Item and member syntax, with their clause lowering helpers. -/

namespace FrenCli

inductive PropKind where
  | assume
  | ensure
  | expect
  | cover
  deriving Inhabited, BEq

inductive Member where
  /-- A variable; an output may have a definition, `:= e`. -/
  | var (isIn isPub isDet : Bool) (name : Ident) (ty : Option (Array Ident)) (defn : Option Expr)
  | prop (kind : PropKind) (name : Ident) (e : Expr)
  /-- `out r := e`, the definition of the result `r`. -/
  | define (name : Ident) (e : Expr)
  /-- `call name := comp(a, b)`, whose bindings are its arguments, each
  named after its position until the callee's parameters are known. `span`
  is the whole member's. -/
  | refines (call : Ident) (abstract : Array Ident) (args : Array Expr) (span : Span)
  | inst (name : Ident) (comp : Array Ident) (bindings : Array (Ident × Option Expr)) (span : Span)
  /-- `use a::b` or `use a::E::*`, with the span of the whole member. -/
  | use (span : Span) (path : Array Ident) (glob : Bool)
  /-- `use pre::{a, b::c}`: each path is appended to `pre`. -/
  | useGroup (span : Span) (pre : Array Ident) (paths : Array (Array Ident))
  /-- `set_option fren.evidence "VALUE" in`, which sets the evidence of the
  next member's checks (`Reqs/Check#checking-by-testing`), with the span of
  `set_option` to the value, and the value's span. -/
  | evidence (span : Span) (value : String) (valueSpan : Span)
  deriving Inhabited

/-- The logical members of a top-level disjunction/equivalence, with
all surrounding guard/let wrappers retained on each member. -/
partial def branchMembers (e : Expr) : Option (Fren.Core.BranchKind × Option Expr × Array (Option Ident × Span × Expr)) :=
  match e with
  | .block _ "or" members => some (.disjunction, none, members.map fun (label, value) => (label, value.span, value))
  | .block _ "iff" members => some (.equivalence, none, members.map fun (label, value) => (label, value.span, value))
  | .block _ "one" members => some (.exactlyOne, none, members.map fun (label, value) => (label, value.span, value))
  | .bin _ "iff" a b => some (.equivalence, none, #[(none, a.span, a), (none, b.span, b)])
  | .when sp negative condition body => (branchMembers body).map fun (kind, guard, members) =>
    let inactive := .not sp (guard.getD (.bool sp true))
    (kind, some (.not sp (.when sp negative condition inactive)),
      members.map fun (label, source, member) => (label, source, .when sp negative condition member))
  | .«let» sp defs body isWhere => (branchMembers body).map fun (kind, guard, members) =>
    (kind, guard.map (.«let» sp defs · isWhere), members.map fun (label, source, member) => (label, source, .«let» sp defs member isWhere))
  | _ => none

structure BlockObservation where
  op : String
  wanted : Bool := true
  members : Array (Option Ident × Span × Expr × Expr)

/-- Value and evaluation guard are kept separate: observing a diagnostic
must not evaluate a singleton equivalence or a short-circuited tail. -/
partial def observedMembers (e : Expr) : Option BlockObservation :=
  match e with
  | .block sp op members => Id.run do
    let values := members.map (·.2)
    let combine (xs : Array Expr) := Expr.lowerBlock sp "and" (xs.map (none, ·))
    let result := members.zipIdx.map fun ((label, value), i) =>
      let preceding := values.extract 0 i
      let guard := if op == "and" then combine preceding
        else if op == "or" then combine (preceding.map fun value => .not value.span value)
        else if op == "one" then
          combine (preceding.zipIdx.flatMap fun (left, j) =>
            (preceding.extract (j + 1)).map fun right => .not sp (.bin sp "and" left right))
        else if values.size <= 1 then Expr.bool sp false
        else if i == 0 then Expr.bool sp true
        else combine ((values.extract 1 i).map fun previous => .bin sp "iff" values[0]! previous)
      (label, value.span, value, guard)
    return some { op, members := result }
  | .not _ body => (observedMembers body).map fun group => { group with wanted := !group.wanted }
  | .when sp negative condition body => (observedMembers body).map fun group =>
    let active := if negative then Expr.not condition.span condition else condition
    { group with members := group.members.map fun (label, source, value, guard) =>
      (label, source, .when sp negative condition value, .bin sp "and" active guard) }
  | .«let» sp defs body isWhere => (observedMembers body).map fun group =>
    { group with members := group.members.map fun (label, source, value, guard) =>
      (label, source, .«let» sp defs value isWhere, .«let» sp defs guard isWhere) }
  | _ => none

/-- Function contracts have the same independent conjunction clauses as
procedure assumptions and guarantees. -/
def splitContractClauses (clauses : Array (Bool × Ident × Expr)) : Array (Bool × Ident × Expr) :=
  clauses.flatMap fun (post, owner, expression) =>
    (expression.clauseLeaves owner).map fun (label, value) => (post, label, value)

/-- Split a conjunction's own checks, copying a member-level method
setting to every generated clause. No synthetic enclosing check remains. -/
def splitConjunctionMembers (members : Array Member) : Array Member := Id.run do
  let mut out := #[]
  let mut pending : Option Member := none
  for member in members do
    match member with
    | .evidence .. =>
      if let some prior := pending then out := out.push prior
      pending := some member
    | .prop kind name expression =>
      for (label, leaf) in expression.clauseLeaves name do
        if let some setting := pending then out := out.push setting
        out := out.push (.prop kind label leaf)
      pending := none
    | _ =>
      if let some setting := pending then out := out.push setting
      pending := none
      out := out.push member
  if let some setting := pending then out := out.push setting
  return out

/-- What a function's block gives its function beyond its lowering
(`Reqs/Lang/Items#function-blocks`): its `use`s; its `let`s that nothing
needs, which `unused_variables` reports; and the first precondition or
body that mentions the result, an error (`F0165`), with the result's name. -/
structure FnBlockInfo where
  uses : Array Member := #[]
  unusedLets : Array Ident := #[]
  resultMention? : Option (Span × String) := none
  deriving Inhabited

inductive Item where
  | mod (isPub : Bool) (path : Array Ident)
  /-- `use a::b` or `use a::E::*`, with the span of the whole item. -/
  | use (span : Span) (path : Array Ident) (glob : Bool)
  /-- `use pre::{a, b::c}`: each path is appended to `pre`. -/
  | useGroup (span : Span) (pre : Array Ident) (paths : Array (Array Ident))
  /-- `enum E { A, B(T, U) }`: each variant with its payload's types, if
  it has a payload; `ordered enum E { A, B }` if `isOrdered`; with type
  parameters, `enum E<T> { ... }`. -/
  | enum (isPub : Bool) (name : Ident) (variants : Array (Ident × Option (Array (Array Ident)))) (isOrdered : Bool)
      (params : Array Ident)
  /-- `struct R { x: T, y? }`: each field with its type, if written;
  `ordered struct R { ... }` if `isOrdered`; with type parameters,
  `struct R<A, B> { ... }`. -/
  | record (isPub : Bool) (name : Ident) (fields : Array (Ident × Option (Array Ident))) (isOrdered : Bool)
      (params : Array Ident)
  /-- `struct N(T)`: a newtype, with the types in its parentheses, which
  must be one (`lang::newtype`); `ordered struct N(T)` if `isOrdered`. -/
  | newtype (isPub : Bool) (name : Ident) (fields : Array (Array Ident)) (isOrdered : Bool := false)
  /-- `type T`, an abstract type. -/
  | abstractType (isPub : Bool) (name : Ident)
  /-- `type T := U`, a type alias. -/
  | typeAlias (isPub : Bool) (name : Ident) (ty : Array Ident)
  | subsetType (isPub : Bool) (name binder : Ident) (base : Array Ident) (invariants : Array (Ident × Expr))
  /-- `fn f(T, U): R`, or `fn f(x: T, y?): R := e`, or with type parameters
`fn f<A, B>(x: A): B := e`: each parameter's path,
and its type after `:` if written. The result type is `none` if it is not
written, and the body if the function is uninterpreted. Then the clauses
of its contract: whether each is a postcondition, its name and its
expression. `last` is the span of its last token, such as a `)` around the
body, which `body` leaves out. `block` is what its block gives it beyond
its lowering (`Reqs/Lang/Items#function-blocks`). -/
  | function (isPub : Bool) (name : Ident) (typeParams : Array Ident) (params : Array (Array Ident × Option (Array Ident)))
      (result : Option (Array Ident)) (body : Option Expr) (clauses : Array (Bool × Ident × Expr)) (last : Span)
      (block : FnBlockInfo := {})
  | const (isPub : Bool) (name : Ident) (ty : Array Ident) (value : Expr)
  /-- `proc p(x: T): (y: U) { members }`: its parameters, as inputs, and
  its results, as public outputs, each after any evidence setting
  (`header`); its block's members, with the span of its closing `}`, the
  span of each member, and where its `{` ends. -/
  | comp (isPub : Bool) (name : Ident) (header : Array Member) (members : Array Member) (close : Span) (spans : Array Span)
      (openStop : Nat)
  /-- `expect n: e`, or `expect n: forall (a b: T) ..., e`, whose binders
  are a quantifier around `e`. -/
  | global (name : Ident) (binders : Array Binder) (body : Expr)
  /-- `expect n(x: T) { members }`, a global expectation written with a
  block (`Reqs/Lang/Global`): as a procedure's, its parameters, and any
  results, which are an error (`F0417`), as `header`, then its block. -/
  | globalBlock (name : Ident) (header : Array Member) (members : Array Member) (close : Span) (spans : Array Span)
      (openStop : Nat)
  /-- `tested c: "file", ...` or `trusted c: "why"`, with each string's span. -/
  | claim (tested : Bool) (comp : Array Ident) (texts : Array (String × Span))
  /-- `#fren_check [path]` or `#fren_trace`. -/
  | check (path : Option (Array Ident))
  /-- `set_option fren.lint.NAME "LEVEL" [in item]`, with the span of
  `set_option` to the level, the level's span, and what removing the
  setting removes: up to the item after `in`, if any. -/
  | lintSetting (span : Span) (option : Ident) (value : String) (valueSpan : Span) (removal : Span)
      (body : Option Item)
  /-- `trait T { members }` (`Reqs/Lang/Traits`): its members, each an item
  as written, which the elaborator checks is a method, a law or an
  expectation (`lang::trait_member`), and the span of its closing `}`. -/
  | «trait» (isPub : Bool) (name : Ident) (members : Array Item) (close : Span)
  /-- `law n(x: T, y?): e`, a member of a trait: its variables, each with its
  type after `:` if written, and its equation. -/
  | law (name : Ident) (params : Array (Ident × Option (Array Ident))) (body : Expr)
  /-- An item, read whole with no error of its syntax, whose first error
  is a clause's keyword's (`lang::item_error`): the error, which the
  elaborator reports, and nothing else of the item. -/
  | broken (span : Span) (msg : Fren.Core.Msg)
  deriving Inhabited

/-- `it`, broken by the error `msg` at `span`: the item under any
`set_option ... in`, whose setting stays, as the Lean front end reads the
setting and then fails the item under it. -/
def Item.breakWith (it : Item) (span : Span) (msg : Fren.Core.Msg) : Item :=
  match it with
  | .lintSetting stx opt value valueSpan removal (some body) =>
    .lintSetting stx opt value valueSpan removal (some (body.breakWith span msg))
  | _ => .broken span msg

end FrenCli
