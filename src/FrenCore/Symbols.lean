-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# The symbols that both front ends make (`Reqs/Cli#solver-queries`)

A query names a variable by its own name, with `smtName`'s `#` after it if
a theory has that symbol. Every other symbol that the front ends make for
what has a name, a quantifier's bound name, a variable's second copy and a
closure's parameter, is the name, a `#`, and what tells the families apart,
which no Fren name has: a name is an identifier, and no identifier contains
`#` (`lang::identifier`). So none of them is a variable's symbol, nor
another's of a different name, family or position (`cli::query_symbols`).
Fren identifiers may contain `'`, so `'` cannot be the separator: `x'0`
was a variable's name as well as a bound name's symbol.
-/

namespace Fren.Core

/-- The symbol of a quantifier's bound name `x`, of a type that is not
listed, at position `k` among the bound names in scope: `x#k`
(`cli::query_symbols`). Both front ends name it so. -/
def boundSymbol (x : String) (k : Nat) : String := x ++ "#" ++ toString k

/-- The symbol of the parameter `x` of the closure numbered `n` in its
spec, as `fren check` writes it: `x#closure{n}` (`cli::query_symbols`). -/
def closureSymbol (x : String) (n : Nat) : String := x ++ "#closure" ++ toString n

/-- The symbol of the second copy of the variable `x`, for `determinism`:
`x#'`, as `primed` names it (`cli::query_symbols`). -/
def copySymbol (x : String) : String := x ++ "#'"

/-- What a symbol of a query is the symbol of, as `cli::query_symbols` has it. -/
inductive QuerySymbol where
  /-- A variable, by its name. -/
  | name (x : String)
  /-- A variable's second copy. -/
  | copy (x : String)
  /-- A quantifier's bound name, at its position among those in scope. -/
  | bound (x : String) (k : Nat)
  /-- A closure's parameter, of the closure with that number. -/
  | closure (x : String) (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The symbol itself, as the solver is given it. -/
def QuerySymbol.text : QuerySymbol → String
  | .name x => smtName x
  | .copy x => copySymbol x
  | .bound x k => boundSymbol x k
  | .closure x n => closureSymbol x n

/-- The name that a symbol of `s` is made from. -/
def QuerySymbol.base : QuerySymbol → String
  | .name x | .copy x | .bound x _ | .closure x _ => x

end Fren.Core
