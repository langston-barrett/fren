-- keep-sorted start
import FrenCore.NfcData
-- keep-sorted end

/-!
# NFC

Unicode Normalization Form C, as Unicode Standard Annex #15 defines it,
for `unicode_not_nfc` (`Reqs/Lint/Pedantic/Text#unicode-normalization`): a string is
decomposed canonically, its combining marks put in canonical order, and
then composed canonically. The tables are `NfcData`'s, of one version of
Unicode; a string with a code point that the version does not assign is
not normalized, since a later version may give that code point a
combining class or a decomposition.
-/

namespace Fren.Core.Nfc

/-- The hexadecimal number `s`. -/
def hex (s : String) : Nat :=
  s.foldl (init := 0) fun n c =>
    16 * n + if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- The entries of a table of `NfcData`, each as its fields. -/
def entries (table : String) : Array (Array Nat) :=
  ((table.splitOn " ").filter (· ≠ "")).toArray.map fun e => ((e.splitOn ",").map hex).toArray

/-- The tables, read once. -/
structure Tables where
  /-- `first, last, class`, in order. -/
  classes : Array (Array Nat)
  /-- `first, last`, in order. -/
  assigned : Array (Array Nat)
  /-- Characters with a decomposition, in order, and their decompositions. -/
  decomposed : Array Nat
  decompositions : Array (Array Nat)
  /-- `first * 0x110000 + second`, in order, for each pair that composes,
  and what it composes to. -/
  pairs : Array (Nat × Nat)

def Tables.read : Tables :=
  let ds := entries NfcData.decompositions
  let excluded := entries NfcData.exclusions |>.map (·[0]!)
  let pairs := ds.filterMap fun d =>
    if d.size == 3 && !excluded.contains d[0]! then some (d[1]! * 0x110000 + d[2]!, d[0]!) else none
  { classes := entries NfcData.combiningClasses
    assigned := entries NfcData.assigned
    decomposed := ds.map (·[0]!)
    decompositions := ds.map (·.extract 1)
    pairs := pairs.qsort (·.1 < ·.1) }

def tables : Tables := Tables.read

/-- The index of the last element of the sorted `xs` whose key is at most
`k`, if any. -/
def lastAtMost [Inhabited α] (xs : Array α) (key : α → Nat) (k : Nat) : Option Nat := Id.run do
  if xs.isEmpty || key xs[0]! > k then return none
  -- `key xs[lo] ≤ k`, and every key from `hi` on is greater.
  let mut lo := 0
  let mut hi := xs.size
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if key xs[mid]! ≤ k then lo := mid else hi := mid
  return some lo

/-- The entry of the ranges `rs` that contains `c`. -/
def inRanges (rs : Array (Array Nat)) (c : Nat) : Option (Array Nat) := do
  let r := rs[← lastAtMost rs (·[0]!) c]!
  if c ≤ r[1]! then some r else none

/-- The canonical combining class of `c`. -/
def combiningClass (c : Nat) : Nat := ((inRanges tables.classes c).map (·[2]!)).getD 0

/-- Whether this version of Unicode assigns `c`. -/
def assigned (c : Nat) : Bool := (inRanges tables.assigned c).isSome

-- Hangul syllables are decomposed and composed by arithmetic.
def sBase : Nat := 0xAC00
def lBase : Nat := 0x1100
def vBase : Nat := 0x1161
def tBase : Nat := 0x11A7
def lCount : Nat := 19
def vCount : Nat := 21
def tCount : Nat := 28
def nCount : Nat := vCount * tCount
def sCount : Nat := lCount * nCount

/-- The canonical decomposition of `c`, one level. -/
def decomposition? (c : Nat) : Option (Array Nat) :=
  if sBase ≤ c && c < sBase + sCount then
    let s := c - sBase
    let t := s % tCount
    if t == 0 then some #[lBase + s / nCount, vBase + (s % nCount) / tCount]
    else some #[sBase + (s - t), tBase + t]
  else do
    let i ← lastAtMost tables.decomposed id c
    if tables.decomposed[i]! == c then tables.decompositions[i]! else none

/-- `c` decomposed canonically, fully, after `acc`. A decomposition is
at most four deep. -/
def decompose (c : Nat) (acc : Array Nat) : Nat → Array Nat
  | 0 => acc.push c
  | fuel + 1 => match decomposition? c with
    | some ds => ds.foldl (fun acc d => decompose d acc fuel) acc
    | none => acc.push c

/-- What `a` and then `b` compose to, if they compose. -/
def composite? (a b : Nat) : Option Nat :=
  if lBase ≤ a && a < lBase + lCount && vBase ≤ b && b < vBase + vCount then
    some (sBase + ((a - lBase) * vCount + (b - vBase)) * tCount)
  else if sBase ≤ a && a < sBase + sCount && (a - sBase) % tCount == 0 && tBase < b && b < tBase + tCount then
    some (a + (b - tBase))
  else do
    let k := a * 0x110000 + b
    let i ← lastAtMost tables.pairs (·.1) k
    if tables.pairs[i]!.1 == k then some tables.pairs[i]!.2 else none

/-- `cs` with each run of combining marks in canonical order: sorted by
combining class, stably. -/
def reorder (cs : Array Nat) : Array Nat := Id.run do
  let mut out := cs
  for i in [1:out.size] do
    let mut j := i
    let k := combiningClass out[j]!
    while j > 0 && k != 0 && combiningClass out[j - 1]! > k do
      out := out.swapIfInBounds j (j - 1)
      j := j - 1
  return out

/-- `cs`, in canonical order, composed canonically: each character is
composed with the last starter before it, if nothing between them blocks
it, a character of the same class or a starter. -/
def compose (cs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  -- The index in `out` of the last starter, and the class of the last
  -- character after it.
  let mut starter? : Option Nat := none
  let mut last := 0
  for c in cs do
    let k := combiningClass c
    if let some s := starter? then
      -- Not blocked: right after the starter, or after a character of a
      -- lower class, which is not a starter.
      if out.size == s + 1 || (last != 0 && last < k) then
        if let some p := composite? out[s]! c then
          out := out.set! s p
          continue
    if k == 0 then
      starter? := some out.size
      last := 0
    else last := k
    out := out.push c
  return out

/-- The code points of `s` in NFC. -/
def nfcCodes (s : String) : Array Nat :=
  compose (reorder (s.foldl (fun acc c => decompose c.toNat acc 4) #[]))

/-- `s` in NFC, if this version of Unicode assigns each of its code points;
`none` if not. A string below `U+0300` is in NFC. -/
def nfc? (s : String) : Option String :=
  if s.toList.all (·.toNat < 0x300) then some s
  else if s.toList.all (assigned ·.toNat) then
    some (String.ofList ((nfcCodes s).toList.map Char.ofNat))
  else none

end Fren.Core.Nfc
