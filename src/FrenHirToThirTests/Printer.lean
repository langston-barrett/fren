module

public import FrenHirToThirTests.Support
public import FrenGen

/-! Test-only printer from an HIR module to Fren source, for checking the
separated pass against the existing checker on the same program. Locals are
named by depth exactly as the generator names them, so every name is unique
along its scope chain and resolution selects the generated index. -/

public section
namespace FrenHirToThirTests.Printer
open FrenExpr FrenModule.Core

def lastName (id : FrenBase.ItemId) : String :=
  match id.components.getLast? with
  | some (.named n) => n
  | _ => "unnamed"

def itemText (m : Hir) (id : FrenBase.ItemId) : String :=
  match m.ctorOwner id with
  | some owner => lastName owner ++ "::" ++ lastName id
  | none => lastName id

def tyText : Ty → String
  | .bool => "Bool"
  | .int => "Int"
  | .enum id => lastName id

def unaryText : FrenAst.UnaryOp → String
  | .neg => "-" | .not => "not"

def binaryText : FrenAst.BinaryOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "div" | .mod => "mod"
  | .eq => "=" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "and" | .or => "or" | .iff => "iff"

def paramName (i : Nat) (q : Param) : String := s!"p{i}{if q.suffix then "?" else ""}"

/-- Print a body; the context holds the names of the enclosing binders. -/
def expr (m : Hir) : Expr .hir → List String → String :=
  Expr.fold fun _ _ n ctx =>
    let local_ (i : Nat) := ctx[i]?.getD s!"dangling{i}"
    match n with
    | .bool v => toString v
    | .int v => toString v
    | .var i => local_ i
    | .item _ id => itemText m id
    | .ctor g _ | .call g _ _ => absurd g (by decide)
    | .apply _ callee args =>
      let head := match callee with | .item id => itemText m id | .local i => local_ i
      head ++ "(" ++ ", ".intercalate (args.map (· ctx)).toList ++ ")"
    | .unary op e => unaryText op ++ " " ++ e ctx
    | .binary op l r => l ctx ++ " " ++ binaryText op ++ " " ++ r ctx
    | .ite c y e => s!"if {c ctx} then {y ctx} else {e ctx}"
    | .letE b v body =>
      let name := s!"x{ctx.length}{if b.suffix then "?" else ""}"
      s!"let {name} := {v ctx} in {body (name :: ctx)}"
    | .matchE s arms =>
      s!"match {s ctx} \{ " ++ ", ".intercalate (arms.map fun (pat, e) =>
        itemText m pat.ctor ++ " => " ++ e ctx).toList ++ " }"
    | .paren _ e => "(" ++ e ctx ++ ")"

def params (ps : Array Param) : String × List String :=
  let texts := ps.toList.zipIdx.map fun (q, i) =>
    let name := paramName i q
    if q.annotated then s!"{name}: {tyText q.type}" else name
  let names := ps.toList.zipIdx.map fun (q, i) => paramName i q
  (", ".intercalate texts, names.reverse)

/-- The whole module, one declaration per line (members on their own lines). -/
def module (m : Hir) : String := Id.run do
  let mut out := s!"mod {lastName m.id}\n"
  for item in m.items do
    match item with
    | .enum e _ =>
      out := out ++ s!"enum {lastName e.id} \{ " ++ ", ".intercalate (e.ctors.map lastName).toList ++ " }\n"
    | .function f _ =>
      let (ps, ctx) := params f.params
      out := out ++ s!"fn {lastName f.id}({ps}): {tyText f.result} := {expr m f.body ctx}\n"
    | .check c _ =>
      let (ps, ctx) := params c.params
      out := out ++ s!"expect {lastName c.id}({ps}) \{\n"
      for mem in c.members do
        let kw := if mem.kind == .assume then "assume" else "expect"
        out := out ++ s!"  {kw} {mem.label}: {expr m mem.body ctx}\n"
      out := out ++ "}\n"
  return out

end FrenHirToThirTests.Printer
