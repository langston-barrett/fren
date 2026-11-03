-- keep-sorted start
import FrenCli.Smt
-- keep-sorted end

/-!
`FrenCli.quotedSymbols` and `FrenCli.substQuoted` read the bytes of a
script, and `FrenCli.quotedPieces`, the reference, reads its characters.
`quotedSymbols` finds the same symbols, in the same order, as
`quotedPieces`, and `substQuoted` gives the text of its pieces, each name
replaced.
-/

open FrenCli

/-- The symbols that `quotedPieces` finds. -/
def piecesSymbols (smt : String) : Array String :=
  (quotedPieces smt).filterMap fun | .inr name => some name | .inl _ => none

/-- Scripts with string literals, `""` within them, `|` within them, symbols
that are not ASCII, and a symbol and a literal that are never closed. -/
def quotedCases : Array String := #[
  "",
  "(assert (= |x| 1))",
  "(assert (= |x| \"|y|\"))",
  "(assert (= |a.b?| \"say \"\"|hi|\"\" \" |c'|))",
  "(assert (= |héllo| \"ö|\" |日本::Ω|))",
  "(assert (str.in_re |s| (str.to_re \"\"\"\")))",
  "\"\"|x|\"\"",
  "(= |x| |",
  "(= |x| \"unclosed |y|",
  "||",
  "|𝔸|\"\"\"|\"|z|"]

#guard quotedCases.all fun s => quotedSymbols s == piecesSymbols s
#guard quotedSymbols "(assert (= |x| \"|y|\")) ; |z|" == #["x", "z"]

/-- What `substQuoted f` gives, read from `quotedPieces`. -/
def piecesSubst (f : String → String) (smt : String) : String :=
  String.join ((quotedPieces smt).toList.map fun | .inl text => text | .inr name => f name)

/-- A replacement that shows where each name was and what it was, and
that is not ASCII. -/
def marked (name : String) : String := s!"⟨{name}⟩"

/-- Every string of up to 6 of `a`, `|`, `"` and `é`: each way that
symbols, literals and their `""` can follow each other, closed or not. -/
def smallScripts : Array String :=
  (List.range 7).toArray.flatMap fun n =>
    (List.range (4 ^ n)).toArray.map fun k =>
      String.ofList ((List.range n).map fun d => #['a', '|', '"', 'é'][(k / 4 ^ d) % 4]!)

#guard quotedCases.all fun s => substQuoted marked s == piecesSubst marked s
#guard smallScripts.all fun s => substQuoted marked s == piecesSubst marked s
#guard smallScripts.all fun s => quotedSymbols s == piecesSymbols s
#guard substQuoted marked "(assert (= |x| \"|y|\")) ; |z|" == "(assert (= ⟨x⟩ \"|y|\")) ; ⟨z⟩"
