-- keep-sorted start
import FrenCli.Smt
import FrenCore.Text.Correctness
-- keep-sorted end

/-! A test of `Core.occursIn`, the search for text in a query's formulas
that `SeqElems.hasMarker`, `Core.hasQuantifier`, `needsExpansion` and
`Core.projectsRelation` now make. The first three asked whether `t`
occurs in `s` as `(s.splitOn t).length > 1`, and the last as
`s.contains t`. `Core.occursIn_iff` proves that the byte search finds
exactly the character infixes of a nonempty needle, and
`Core.occursIn_eq_contains` connects it to `String.contains`. These tests
also check the native byte comparison against the old searches, over
random texts made of pieces of the searched-for texts, so that they hold
partial matches, overlaps and repeats, and of characters of two, three
and four bytes. -/

namespace Fren.Test.TextSearch

open FrenCli

/-- Whether `t` occurs in `s`, as the first three searches asked it. -/
def splitHas (s t : String) : Bool := (s.splitOn t).length > 1

/-- `SeqElems.hasMarker` as it was. -/
def hasMarkerBySplit (s : String) : Bool := SeqElems.markerHeads.any (splitHas s ·)

/-- `Core.hasQuantifier` as it was. -/
def hasQuantifierBySplit (f : String) : Bool := ["(forall (", "(exists ("].any (splitHas f ·)

/-- `needsExpansion` as it was. -/
def needsExpansionBySplit (marked : Std.HashMap String (Array String × SeqElems.SExpr)) (fs : Array String) : Bool :=
  fs.any fun f => hasMarkerBySplit f || marked.keys.any (splitHas f ·)

/-- The names of `define-fun`s with marked quantifiers, the empty name
among them, which `splitOn` does not split at. -/
def names : Array String := #["", "f", "ff", "fa", "|a é|", "é", "ü€", "€😀"]

/-- The texts that the random texts are made of: each searched-for text,
each of its proper prefixes, and some other characters, of one to four
bytes, some of whose bytes are those of others. -/
def pieces : Array String :=
  let whole := SeqElems.markerHeads.toArray ++ #["(forall (", "(exists (", "rel.project"] ++ names
  let prefixes := whole.flatMap fun w => (Array.range w.length).map fun k => (w.take k).toString
  whole ++ prefixes ++ #["(", " ", "#", "a", "s", ")", "fren.", "forall", "e", "©", "€", "è", "😁", "\u0000"]

def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- A random text of up to 8 pieces, and the state after. -/
def randomText (s : Nat) : String × Nat := Id.run do
  let mut s := next s
  let n := (s / 65536) % 9
  let mut out := ""
  for _ in [0:n] do
    s := next s
    out := out ++ pieces[(s / 65536) % pieces.size]!
  return (out, s)

/-- `seed`'s formulas and `define-fun`s with marked quantifiers. -/
def randomQuery (seed : Nat) : Array String × Std.HashMap String (Array String × SeqElems.SExpr) := Id.run do
  let mut s := next (seed + 1)
  let mut fs := #[]
  for _ in [0:(s / 65536) % 3 + 1] do
    let (f, s') := randomText s
    fs := fs.push f
    s := s'
  let mut marked : Std.HashMap String (Array String × SeqElems.SExpr) := {}
  for n in names do
    s := next s
    if (s / 65536) % 3 == 0 then marked := marked.insert n (#[], .atom n)
  return (fs, marked)

/-- Whether the searches give what they gave before on `seed`'s query,
and `occursIn` what `splitOn` gives for each name and piece. -/
def agrees (seed : Nat) : Bool :=
  let (fs, marked) := randomQuery seed
  fs.all (fun f => SeqElems.hasMarker f == hasMarkerBySplit f && Fren.Core.hasQuantifier f == hasQuantifierBySplit f
      && Fren.Core.projectsRelation f == f.contains "rel.project"
      && (names ++ pieces).all fun t => Fren.Core.occursIn t f == splitHas f t)
    && needsExpansion marked fs == needsExpansionBySplit marked fs

#guard (List.range 5000).all agrees

-- Not vacuous: each search finds its text in some queries and not in
-- others, and some texts hold a proper prefix of a quantifier's head
-- without the head.
#guard [true, false].all fun b => (List.range 5000).any fun seed =>
  let (fs, marked) := randomQuery seed
  needsExpansion marked fs == b && !fs.any SeqElems.hasMarker
#guard [true, false].all fun b => (List.range 5000).any fun seed => (randomQuery seed).1.any (SeqElems.hasMarker · == b)
#guard [true, false].all fun b => (List.range 5000).any fun seed =>
  (randomQuery seed).1.any fun f => Fren.Core.hasQuantifier f == b && Fren.Core.projectsRelation f == b
#guard (List.range 5000).any fun seed => (randomQuery seed).1.any fun f =>
  splitHas f "(forall" && !Fren.Core.hasQuantifier f
-- The empty name, which `splitOn` never splits at, is among those of some
-- queries that would otherwise need no expansion.
#guard (List.range 5000).any fun seed =>
  let (fs, marked) := randomQuery seed
  marked.contains "" && !needsExpansion marked fs

/-- Every text of at most `n` characters of `alphabet`, each once if
`alphabet` has no duplicates: a text of `k + 1` characters only as its
first `k` with its last pushed on. -/
def allTexts (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (allTexts alphabet n).flatMap fun t => alphabet.map (t.push ·)

-- Exhaustively on small inputs: every text of at most 3 characters
-- against every text of at most 5, over characters of one to four bytes,
-- `é` and `è` sharing their lead byte. That covers the empty text, a text
-- longer than the other, a match at the very end, overlaps and
-- neighbouring multi-byte characters.
#guard let alphabet := ['a', 'b', 'é', 'è', '€', '😀']
  let haystacks := allTexts alphabet 5
  (allTexts alphabet 3).all fun t => haystacks.all fun s => Fren.Core.occursIn t s == splitHas s t

end Fren.Test.TextSearch
