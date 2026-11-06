-- keep-sorted start
import FrenCli.SeqElems
-- keep-sorted end

/-!
# SMT identifiers in executable sentence input (#758)

SMT-LIB 2.7, sections 3.1 and 3.11, distinguishes symbols from literal and
reserved tokens. Quoting a symbol preserves its identity; quoting a numeral
or a reserved word instead makes it a symbol. Keep the existing `SExpr` syntax
and hashing unchanged, and use this equality when reading bridge input.
See https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-04-09.pdf.
-/

namespace FrenCli.SmtSymbols

open SeqElems (SExpr)

private def reserved : List String := [
  "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING",
  "_", "!", "as", "lambda", "let", "exists", "forall", "match", "par",
  "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-datatype",
  "declare-datatypes", "declare-fun", "declare-sort", "declare-sort-parameter",
  "define-const", "define-fun", "define-fun-rec", "define-funs-rec", "define-sort",
  "echo", "exit", "get-assertions", "get-assignment", "get-info", "get-model",
  "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core", "get-value",
  "pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option"]

/-- The identifier denoted by an atom, excluding literals, keywords and
reserved syntax. The bridge receives already parsed, elaborated SMT terms. -/
def symbol? (s : String) : Option String :=
  if s.length ≥ 2 && s.startsWith "|" && s.endsWith "|" then
    let body := ((s.drop 1).dropEnd 1).toString
    if body.toList.all (fun c => c != '|' && c != '\\') then some body else none
  else if s.isEmpty || reserved.contains s then none
  else if s.toList.head!.isDigit then none
  else if s.toList.all (fun c => c.isAlpha && c.toNat < 128 || c.isDigit ||
      "~!@$%^&*_-+=<>.?/".contains c) then some s
  else none

/-- Identifier equality, not token equality: neither `1` nor `let` is a
symbol, whereas `|1|` and `|let|` are symbols. -/
def sameSymbol (a b : String) : Bool :=
  match symbol? a, symbol? b with
  | some x, some y => x == y
  | _, _ => false

/-- Structural SMT equality modulo identifier quoting. Literal and reserved
tokens compare exactly and cannot equal a quoted identifier. -/
partial def sameTerm : SExpr → SExpr → Bool
  | .atom a, .atom b =>
    match symbol? a, symbol? b with
    | some x, some y => x == y
    | none, none => a == b
    | _, _ => false
  | .list xs, .list ys =>
    xs.size == ys.size && (xs.zip ys).all fun (a, b) => sameTerm a b
  | _, _ => false

/-- All identifier names, including bound ones: a conservative set to avoid
when generating a fresh binder. Literal contents are not identifiers. -/
partial def symbols : SExpr → List String
  | .atom a => (symbol? a).toList
  | .list xs => xs.toList.flatMap symbols

end FrenCli.SmtSymbols
