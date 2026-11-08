module

public import scratch.expr.Prototype
public import FrenSexp

public section
namespace ExprPrototype
open Fren

/-- Handwritten one-layer codec, using the existing base classes. Proof gates
are omitted on output and reconstructed by the phase check on input. -/
instance [ToSexp R] : ToSexp (Layer p R) where
  toSexp
    | .lit n => .list #[Sexp.symbol "lit", toSexp n]
    | .var i => .list #[Sexp.symbol "var", toSexp i]
    | .letE v b => .list #[Sexp.symbol "let", toSexp v, toSexp b]
    | .all b => .list #[Sexp.symbol "all", toSexp b]
    | .array xs => .list #[Sexp.symbol "array", toSexp xs]
    | .sugar _ b => .list #[Sexp.symbol "sugar", toSexp b]

instance [FromSexp R] : FromSexp (Layer p R) where
  fromSexp
    | .list #[.atom tag, x] => match tag.val with
      | "lit" => Layer.lit <$> Sexp.atChild 1 (fromSexp x)
      | "var" => Layer.var <$> Sexp.atChild 1 (fromSexp x)
      | "all" => Layer.all <$> Sexp.atChild 1 (fromSexp x)
      | "array" => Layer.array <$> Sexp.atChild 1 (fromSexp x)
      | "sugar" =>
        if h : HasSugar p then Layer.sugar h <$> Sexp.atChild 1 (fromSexp x)
        else Sexp.atChild 0 (Sexp.expected "a constructor allowed in this phase")
      | _ => Sexp.atChild 0 (Sexp.expected "a one-child prototype constructor")
    | .list #[.atom tag, v, b] =>
      if tag.val == "let" then return .letE (← Sexp.atChild 1 (fromSexp v)) (← Sexp.atChild 2 (fromSexp b))
      else Sexp.atChild 0 (Sexp.expected "let")
    | _ => Sexp.expected "a prototype layer with the exact constructor arity"

/-- Full-tree encoding via the fold. Full-tree decoding is left to #979;
the one-layer roundtrips isolate the gate and field contracts it must handle. -/
def encodeExpr (e : Expr p) : Sexp := fold toSexp e

end ExprPrototype
