-- keep-sorted start
import FrenCli.Parse.PatternSyntax
import FrenCore.SubsetTypes
-- keep-sorted end

/-! Expression syntax and its lowering helpers. -/

namespace FrenCli

inductive Expr where
  /-- A prefix Boolean block, retaining member names for lowering and reports. -/
  | block (span : Span) (op : String) (members : Array (Option Ident × Expr))
  | when (span : Span) (negated : Bool) (cond body : Expr)
  | ite (span : Span) (cond thenE elseE : Expr)
  | bin (span : Span) (op : String) (lhs rhs : Expr)
  | not (span : Span) (e : Expr)
  | neg (span : Span) (e : Expr)
  | num (span : Span) (value : Nat)
  | bool (span : Span) (b : Bool)
  | path (span : Span) (segs : Array Ident)
  /-- `f(a, b)`, a function application, or `E::V(a, b)`, a variant with a
  payload. -/
  | app (span : Span) (fn : Array Ident) (args : Array Expr)
  /-- `R { x := e, y }`, a record literal; a field without `:= e` is `none`. -/
  | record (span : Span) (ty : Array Ident) (fields : Array (Ident × Option Expr))
  /-- `{ r with x := e, y }`, a record update; a field without `:= e` is
  `none`. -/
  | update (span : Span) (base : Expr) (fields : Array (Ident × Option Expr))
  /-- `e.x`, for `e` other than a name: a name's fields are part of its
  (dotted) identifier. `x.0` reads the field `0` of a newtype, for any
  `e`: a field named by digits is never part of an identifier. -/
  | field (span : Span) (e : Expr) (field : Ident)
  /-- `match e { P => b, Q if C => c }`: each arm's pattern, its guard, if
  it has one, and its body; or `table e { ... }`, a table over a
  scrutinee (`table`), which means the `match` whose arms are disjoint
  (`Reqs/Lang/Expressions#tables-over-a-scrutinee`). -/
  | «match» (span : Span) (scrutinee : Expr) (arms : Array (Pattern × Option Expr × Expr)) (table : Bool)
  /-- Multiple scrutinees, or an implicit-argument match when empty. -/
  | matches (span : Span) (scrutinees : Array Expr) (arms : Array (Array Pattern × Option Expr × Expr)) (table : Bool)
  /-- `e is P`, a pattern test. -/
  | is (span : Span) (scrutinee : Expr) (pattern : Pattern)
  /-- A string literal, with its value. -/
  | str (span : Span) (value : String)
  /-- `{a, b}`, a set literal. -/
  | set (span : Span) (elems : Array Expr)
  /-- `(a, b)`, a pair: a member of a relation literal, or the left of `in`. -/
  | pair (span : Span) (fst snd : Expr)
  /-- `[a, b]`, a sequence literal. -/
  | seq (span : Span) (elems : Array Expr)
  /-- `q[i]`, indexing. -/
  | index (span : Span) (seq i : Expr)
  /-- `e.m(a, b)`, a method call with arguments; without them, `e.m` is a
  field read or a path, until its receiver's type is known. -/
  | method (span : Span) (recv : Expr) (name : Ident) (args : Array Expr)
  /-- `a < b <= c`, a chained comparison: at least two operators, each
  with its span, between its operands, one more than its operators, which
  chain (`lang::comparison_chain`), as the parser checks. -/
  | chain (span : Span) (operands : Array Expr) (ops : Array (String × Span))
  /-- `let x := e, y: T := f in body`, or `body where x := e` (`isWhere`),
  which means the same (`Reqs/Lang/Let`): each definition's name, its
  type if written, and its expression. -/
  | «let» (span : Span) (defs : Array (Ident × Option (Array Ident) × Expr)) (body : Expr) (isWhere : Bool)
  /-- `forall (x y: T) (z: U), e`, or `exists` if not `all`, with its
  binders and its body (`Reqs/Lang/Quantifiers`). -/
  | quant (span : Span) (all : Bool) (binders : Array Binder) (body : Expr)
  /-- `table { C => e, ... }`, a condition table: each row's start, its
  condition, `none` for `_`, and its value. -/
  | table (span : Span) (rows : Array (Span × Option Expr × Expr))
  /-- `|x, y: T| e`, a closure (`Reqs/Lang/HigherOrder#arguments`): each
  parameter's name and its type if written, and its body. -/
  | closure (span : Span) (params : Array (Ident × Option (Array Ident))) (body : Expr)
  deriving Inhabited

def Expr.span : Expr → Span
  | .block s .. | .when s .. | .ite s .. | .bin s .. | .not s .. | .neg s .. | .num s .. | .bool s .. | .path s .. | .app s ..
  | .record s .. | .update s .. | .field s .. | .match s .. | .matches s .. | .is s .. | .str s .. | .method s .. | .set s .. | .pair s ..
  | .seq s .. | .index s .. | .chain s .. | .«let» s .. | .quant s .. | .table s .. | .closure s .. => s

/-- Instantiate an implicit-argument match with its surrounding arguments. -/
def Expr.explicitMatch (span : Span) (values : Array Expr)
    (arms : Array (Array Pattern × Option Expr × Expr)) (table := false) : Expr :=
  if values.size == 1 && arms.all (·.1.size == 1) then
    .match span values[0]! (arms.map fun (ps, g, b) => (ps[0]!, g, b)) table
  else .matches span values arms table

/-- Expand the match before its optional `where` definitions are lowered. -/
partial def Expr.implicitMatchBody (names : Array Ident) : Expr → Option Expr
  | .matches span #[] arms false => some (.explicitMatch span (names.map fun n => .path n.span #[n]) arms)
  | .«let» span defs body true => (body.implicitMatchBody names).map fun b => .«let» span defs b true
  | _ => none

/-- Unnamed defined parameters are fresh internal arguments of a lambda match. -/
def lambdaMatchFunction (params : Array (Array Ident × Option (Array Ident))) (body : Option Expr) :
    Array (Array Ident × Option (Array Ident)) × Option Expr := Id.run do
  unless params.all (fun p => p.2.isNone && !(p.1.size == 1 && p.1[0]!.name.endsWith "?")) do return (params, body)
  let some e := body | return (params, body)
  let names := params.mapIdx fun j p => ({ name := s!"#match{j}", span := p.1[0]!.span } : Ident)
  let some expanded := e.implicitMatchBody names | return (params, body)
  return (params.zip names |>.map fun ((ty, _), n) => (#[n], some ty), some expanded)

/-- Erase a single Boolean block's annotations while preserving evaluation
order and short-circuiting. Equivalence compares all members to the first;
empty and singleton equivalence evaluate no member. -/
def Expr.lowerBlock (span : Span) (op : String) (members : Array (Option Ident × Expr)) : Expr := Id.run do
  let values := members.map (·.2)
  let combine (op : String) (identity : Bool) (xs : Array Expr) : Expr :=
    if xs.isEmpty then .bool span identity else xs.toList.tail.foldl (fun acc e => .bin span op acc e) xs[0]!
  if op == "and" then return combine "and" true values
  if op == "or" then return combine "or" false values
  if op == "one" then
    let rec exactly (rest : List Expr) (held : Bool) : Expr :=
      match rest with
      | [] => .bool span held
      | value :: tail =>
        if held then .bin span "and" (.not value.span value) (exactly tail true)
        else .ite span value (exactly tail true) (exactly tail false)
    return exactly values.toList false
  if values.size <= 1 then return .bool span true
  let rest := values.extract 1
  return .ite span values[0]! (combine "and" true rest)
    (combine "and" true (rest.map fun e => .not e.span e))

/-- Deterministic private implementation names for a subset declaration.
All front ends use the same names; diagnostics use the invariant's logical
`Type::label` name instead. -/
def subsetPredicateIdent (typeName label : Ident) : Ident :=
  { name := Fren.Core.subsetPredicateName typeName.name label.name typeName.span.start, span := label.span }

def subsetCheckIdent (typeName : Ident) (part : String) : Ident :=
  { name := Fren.Core.subsetCheckName typeName.name part typeName.span.start, span := typeName.span }

/-- Whether a clause can omit its outer label: a leading guard may
wrap an explicit Boolean block. -/
partial def Expr.blockRoot : Expr → Bool
  | .block .. => true
  | .when _ _ _ body | .«let» _ _ body _ => body.blockRoot
  | _ => false

/-- The positive clause positions that distribute into independent leaves. -/
partial def Expr.conjunctionRoot : Expr → Bool
  | .block _ "and" _ => true
  | .when _ _ _ body | .«let» _ _ body _ => body.conjunctionRoot
  | _ => false

/-- Independent conjunction leaves, retaining guards and lexical lets. -/
partial def Expr.clauseLeaves (owner : Ident) : Expr → Array (Ident × Expr)
  | .block _ "and" members => members.zipIdx.flatMap fun ((label, value), i) =>
    let segment := label.map (·.name) |>.getD (toString (i + 1))
    let child : Ident := {
      name := if owner.name.isEmpty then segment else owner.name ++ "." ++ segment
      span := label.map (·.span) |>.getD value.span
    }
    value.clauseLeaves child
  | .when sp negative condition body => (body.clauseLeaves owner).map fun (label, value) =>
    (label, .when sp negative condition value)
  | .«let» sp defs body isWhere => (body.clauseLeaves owner).map fun (label, value) =>
    (label, .«let» sp defs value isWhere)
  | e => #[(if owner.name.isEmpty then { owner with name := "1" } else owner, e)]

/-- The conditions and values of a table's rows, in order. -/
def tableParts (rows : Array (Span × Option Expr × Expr)) : Array Expr :=
  rows.flatMap fun (_, c?, v) => c?.toArray.push v

/-- The guards and bodies of a `match`'s arms, in order. -/
def armParts (arms : Array (Pattern × Option Expr × Expr)) : Array Expr :=
  arms.flatMap fun (_, g?, b) => g?.toArray.push b

end FrenCli
