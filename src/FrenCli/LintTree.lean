-- keep-sorted start
import FrenCli.Parse
import FrenCore.Lint
-- keep-sorted end

/-!
# Expressions as the lints read them

The `fren` command's expressions (`Expr`) as the trees that the lints of
`FrenCore.Lint` read (`Fren.Core.BNode`). The hosted front end builds the
same trees from Lean's syntax.
-/

namespace FrenCli

def toRange (sp : Span) : Fren.Core.Range := { start := sp.start, stop := sp.stop }

/-- The span of `e` as written: a field read, method call or index of a
receiver in parentheses starts at the `(`, which its span leaves out. -/
partial def Expr.writtenSpan (src : Array Char) (e : Expr) : Span :=
  match e with
  | .field _ r _ | .method _ r _ _ | .index _ r _ =>
    let r := Fren.Core.withParens src (toRange (r.writtenSpan src))
    { e.span with start := r.start }
  | _ => e.span

/-- `e` as the lints that rewrite it (`Fren.Core.ExLint`) and the operator
lints see it, with its ranges counted from `base`. Given `src`, a field
read or method call is at its span as written. -/
partial def Expr.boolNode (e : Expr) (src : Array Char := #[]) (base : Nat := 0) : Fren.Core.BNode Span :=
  match e with
  | .block sp _ members => .mk .atom (toRange sp) sp (members.map (fun m => m.2.boolNode src base))
  | .when s n c d => .mk (.when n) (toRange s) s #[c.boolNode src base, d.boolNode src base]
  | .ite s c a b => .mk .ite (toRange s) s #[c.boolNode src base, a.boolNode src base, b.boolNode src base]
  | .bin s op a b => .mk (.bin op) (toRange s) s #[a.boolNode src base, b.boolNode src base]
  | .not s a => .mk .not (toRange s) s #[a.boolNode src base]
  | .neg s a => .mk .neg (toRange s) s #[a.boolNode src base]
  | .bool s b => .mk (.lit b) (toRange s) s #[]
  | .method s r m args =>
    let s := if src.isEmpty then s else e.writtenSpan src
    .mk (.method m.name) (toRange s) s (#[r.boolNode src base] ++ args.map (·.boolNode src base))
  | .app s _ args | .set s args | .seq s args => .mk .atom (toRange s) s (args.map (·.boolNode src base))
  | .record s _ fields => .mk .atom (toRange s) s (fields.filterMap (·.2.map (·.boolNode src base)))
  | .update s r fields => .mk .atom (toRange s) s (#[r.boolNode src base] ++ fields.filterMap (·.2.map (·.boolNode src base)))
  | .field s a _ =>
    let s := if src.isEmpty then s else e.writtenSpan src
    .mk .atom (toRange s) s #[a.boolNode src base]
  | .is s scrutinee _ => .mk .patternTest (toRange s) s #[scrutinee.boolNode src base]
  | .match s scrutinee arms _ => .mk .atom (toRange s) s (#[scrutinee.boolNode src base] ++ (armParts arms).map (·.boolNode src base))
  | .table s rows => .mk .atom (toRange s) s ((tableParts rows).map (·.boolNode src base))
  | .pair s a b | .index s a b => .mk .atom (toRange s) s #[a.boolNode src base, b.boolNode src base]
  | .chain s es ops => .mk (.chain (ops.map (·.1))) (toRange s) s (es.map (·.boolNode src base))
  | .«let» s _ body _ => .mk .«let» (toRange s) s #[body.boolNode src base]
  | .matches s ss arms _ => .mk .atom (toRange s) s ((ss ++ arms.flatMap (fun (_, g, b) => g.toArray.push b)).map (·.boolNode src base))
  | .quant s _ _ b | .closure s _ b => .mk .quant (toRange s) s #[b.boolNode src base]
  | .num s _ | .path s _ | .str s .. => .mk .atom (toRange s) s #[]
-- `base` is at most the start of `e`'s span as written, and every span in
-- `e` is within it, so the subtractions do not truncate.
where toRange (sp : Span) : Fren.Core.Range := { start := sp.start - base, stop := sp.stop - base }

end FrenCli
