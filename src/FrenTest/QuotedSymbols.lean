-- keep-sorted start
import FrenCli.Smt
-- keep-sorted end

/-!
`FrenCli.quotedSymbols` reads the bytes of a script, but finds the same
symbols, in the same order, as `FrenCli.quotedPieces`, which reads its
characters.
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
