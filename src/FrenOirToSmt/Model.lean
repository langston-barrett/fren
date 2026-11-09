module

public import FrenOirToSmt.Translate
public import FrenSexp.Text
public import FrenEval.Value

public section
namespace FrenOirToSmt
open Fren

/-- Only decimal magnitudes in the canonical SMT numeral grammar are accepted. -/
def magnitude (s : String) : Option Nat :=
  if s == "0" || (!s.isEmpty && s.toList.head? != some '0' && s.all Char.isDigit)
  then s.toNat? else none

/-- No coercions, defaults, unknown constructors or solver expressions. -/
@[expose] def modelValue (p : FrenOir.Program) (ty : FrenExpr.Ty) (x : Sexp) : Except String FrenEval.Value := do
  match ty, x with
  | .bool, .atom a =>
    if a.val == "true" then return .bool true
    if a.val == "false" then return .bool false
    throw "expected Boolean model value"
  | .int, .atom a =>
    let some n := magnitude a.val | throw "expected integer magnitude"
    return .int (Int.ofNat n)
  | .int, .list #[.atom op, .atom a] =>
    unless op.val == "-" do throw "expected negative integer"
    let some n := magnitude a.val | throw "expected negative magnitude"
    if n == 0 then throw "noncanonical negative zero"
    return .int (-Int.ofNat n)
  | .enum owner, .atom a =>
    let i ← (enumIndex p owner).mapError reprStr
    let some e := p.enumerations[i]? | throw "missing model enum"
    let some j := (List.range e.constructors.size).find? (fun j =>
      a.val == (Symbol.constructor i j).render) | throw "foreign model constructor"
    let some (ctor, _) := e.constructors[j]? | throw "missing model constructor"
    return .enum owner ctor
  | _, _ => throw "unsupported model value or wrong sort"

/-- Complete get-value response with a literal sentinel even for zero parameters.
Entries are unique and exhaustive; the returned array is always source order. -/
def decodeModel (p : FrenOir.Program) (q : FrenOir.Question) (text : String)
    (cap : Nat := 65536) : Except String (Array FrenEval.Value) := do
  if text.utf8ByteSize > cap || cap > 1048576 then throw "model output limit"
  -- The shared parser permits comments; the model protocol deliberately does not.
  if text.contains ';' || text.contains '"' then throw "diagnostic or quoted model output"
  -- Bound nesting before entering the shared recursive S-expression parser.
  let mut depth := 0
  for c in text.toList do
    if c == '(' then
      depth := depth + 1
      if depth > 8 then throw "model nesting limit"
    if c == ')' then
      if depth == 0 then throw "unbalanced model output"
      depth := depth - 1
  if depth != 0 then throw "partial model output"
  let x ← (Sexp.parse ("(" ++ text ++ ")")).mapError toString
  let .list #[.atom status, .list entries] := x | throw "invalid model response envelope"
  unless status.val == "sat" do throw "model response is not SAT"
  unless entries.size == q.parameters.size + 1 do throw "missing or extra model symbols"
  let mut values : Array (Option FrenEval.Value) := Array.replicate q.parameters.size none
  let mut sentinel := false
  for entry in entries do
    let .list #[.atom symbol, value] := entry | throw "invalid model binding"
    if symbol.val == "true" then
      if sentinel || value != Sexp.symbol "true" then throw "invalid model sentinel"
      sentinel := true
    else
      let some i := (List.range q.parameters.size).find? (fun i => symbol.val == (Symbol.parameter i).render)
        | throw "foreign model symbol"
      if values[i]!.isSome then throw "duplicate model symbol"
      let some param := q.parameters[i]? | throw "missing model parameter"
      values := values.set! i (some (← modelValue p param.source.type value))
  unless sentinel do throw "missing model sentinel"
  values.mapM fun v => match v with
    | some x => .ok x
    | none => .error "missing model parameter"

/-- Reissue exactly the original search, with only model production and the
finite ordered value request added. The first SAT receipt remains separate. -/
def modelScript (q : Query) : Except Failure String := do
  let text ← q.script
  let names := (List.range q.question.parameters.size).map (fun i => (Symbol.parameter i).render)
  return "(set-option :produce-models true)\n" ++ text ++
    "(get-value (true" ++ (if names.isEmpty then "" else " " ++ String.intercalate " " names) ++ "))\n"

theorem wrong_bool (p : FrenOir.Program) :
    modelValue p .bool (.list #[]) = .error "unsupported model value or wrong sort" := rfl


end FrenOirToSmt
