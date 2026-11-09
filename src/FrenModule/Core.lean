module

public import FrenExpr.Core
public import FrenAst

/-! `Module E`: one module as written, shared by HIR and THIR (and later DTHIR),
over the expression core. Items keep declaration order. Each item owns its
origin table; every `OriginId` in the item (its own, its parameters', its
nodes', binders' and patterns') indexes that table. -/

public section
namespace FrenModule.Core

open FrenExpr

/-- A parameter: its declared type, whether its name has the `?` suffix and
whether the type was written (an unwritten type means implicit `Bool`). -/
structure Param where
  origin : OriginId
  type : Ty
  suffix : Bool
  annotated : Bool
  deriving Repr, BEq, DecidableEq

structure Enum where
  id : FrenBase.ItemId
  origin : OriginId
  ctors : Array FrenBase.ItemId
  deriving Repr, BEq, DecidableEq

structure Function (E : Type) where
  id : FrenBase.ItemId
  origin : OriginId
  params : Array Param
  result : Ty
  body : E

structure Member (E : Type) where
  kind : FrenAst.MemberKind
  label : String
  origin : OriginId
  body : E

/-- An expectation (a check): parameters and assume/expect members. -/
structure Check (E : Type) where
  id : FrenBase.ItemId
  origin : OriginId
  params : Array Param
  members : Array (Member E)

inductive Item (E : Type) where
  | enum (value : Enum) (origins : Array Origin)
  | function (value : Function E) (origins : Array Origin)
  | check (value : Check E) (origins : Array Origin)

structure Module (E : Type) where
  id : FrenBase.ItemId
  items : Array (Item E)

namespace Item

variable {E : Type}

@[expose] def origins : Item E → Array Origin
  | .enum _ o | .function _ o | .check _ o => o

@[expose] def id : Item E → FrenBase.ItemId
  | .enum v _ => v.id
  | .function v _ => v.id
  | .check v _ => v.id

end Item

namespace Module

variable {E : Type}

@[expose] def enums (m : Module E) : Array Enum :=
  m.items.filterMap fun | .enum v _ => some v | _ => none

@[expose] def functions (m : Module E) : Array (Function E) :=
  m.items.filterMap fun | .function v _ => some v | _ => none

@[expose] def checks (m : Module E) : Array (Check E) :=
  m.items.filterMap fun | .check v _ => some v | _ => none

/-- The enum that declares a constructor, in declaration order. -/
@[expose] def ctorOwner (m : Module E) (ctor : FrenBase.ItemId) : Option FrenBase.ItemId :=
  (m.enums.find? (·.ctors.contains ctor)).map (·.id)

/-- Every body of the module in declaration order: function bodies, then each
check's members in order, interleaved as the items are. -/
@[expose] def bodies (m : Module E) : Array E :=
  m.items.flatMap fun
    | .enum _ _ => #[]
    | .function f _ => #[f.body]
    | .check c _ => c.members.map (·.body)

end Module

/-- HIR and THIR modules over the expression core. -/
abbrev Hir := Module (Expr .hir)
abbrev Thir := Module (Expr .thir)

open Fren (Sexp) in
/-- The module's S-expression form; origins are omitted unless requested. -/
@[expose] def Module.toSexp {p : Phase} (m : Module (Expr p)) (origins : Bool := false) : Sexp :=
  let nat (k : Nat) := Sexp.symbol (toString k)
  let at_ (k : Nat) := if origins then #[Sexp.list #[Sexp.symbol "@", nat k]] else #[]
  let param (q : Param) := Sexp.list (#[FrenExpr.Sexp.ty q.type,
    Sexp.symbol (if q.suffix then "suffix" else "plain"),
    Sexp.symbol (if q.annotated then "written" else "implicit")] ++ at_ q.origin)
  let table (os : Array Origin) : Array Sexp :=
    if origins then #[Sexp.list (os.map fun o => Sexp.list #[Sexp.string (o.name.getD ""),
      Sexp.symbol (if o.span.isSome then "span" else "nospan")])] else #[]
  .list (#[Sexp.symbol "module", FrenExpr.Sexp.item m.id] ++ m.items.map fun
    | .enum e os => .list (#[Sexp.symbol "enum", FrenExpr.Sexp.item e.id] ++ at_ e.origin ++
        e.ctors.map FrenExpr.Sexp.item ++ table os)
    | .function f os => .list (#[Sexp.symbol "fn", FrenExpr.Sexp.item f.id] ++ at_ f.origin ++
        #[.list (f.params.map param), FrenExpr.Sexp.ty f.result, f.body.toSexp origins] ++ table os)
    | .check c os => .list (#[Sexp.symbol "check", FrenExpr.Sexp.item c.id] ++ at_ c.origin ++
        #[.list (c.params.map param)] ++ c.members.map (fun mem => .list (#[
          Sexp.symbol (if mem.kind == .assume then "assume" else "expect"), Sexp.string mem.label] ++
          at_ mem.origin ++ #[mem.body.toSexp origins])) ++ table os))

/-- Structural equality ignoring origins. -/
@[expose] def Module.same {p : Phase} (a b : Module (Expr p)) : Bool := a.toSexp == b.toSexp

/-- Every local index in every body points at an enclosing binder or parameter. -/
@[expose] def Module.scoped {p : Phase} (m : Module (Expr p)) : Bool :=
  m.items.all fun
    | .enum _ _ => true
    | .function f _ => f.body.scopedIn f.params.size
    | .check c _ => c.members.all (·.body.scopedIn c.params.size)

/-- Erase every body's type decisions and annotations: THIR back to HIR. -/
@[expose] def Module.eraseTypes (m : Thir) : Hir :=
  ⟨m.id, m.items.map fun
    | .enum e os => .enum e os
    | .function f os => .function {f with body := f.body.eraseTypes} os
    | .check c os => .check {c with members := c.members.map fun mem =>
        {mem with body := mem.body.eraseTypes}} os⟩

end FrenModule.Core
