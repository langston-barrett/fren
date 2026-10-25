-- keep-sorted start
import FrenCore.Nfc
-- keep-sorted end

/-!
`Fren.Core.Nfc.nfc?` on code points, each against what Python's
`unicodedata.normalize("NFC", ...)` gives at Unicode 15.0: composition,
reordering, blocking, decomposition, exclusions and Hangul.
-/

open Fren.Core

/-- The code points of `cs` in NFC, if Unicode 15.0 assigns each. -/
def nfcOf (cs : List Nat) : Option (List Nat) :=
  (Nfc.nfc? (String.ofList (cs.map Char.ofNat))).map (·.toList.map Char.toNat)

-- composes
#guard nfcOf [0x65, 0x301] == some [0xe9]
-- already composed
#guard nfcOf [0xe9] == some [0xe9]
-- reorders, then composes past a lower class
#guard nfcOf [0x61, 0x301, 0x316] == some [0xe1, 0x316]
-- blocked by the same class
#guard nfcOf [0x61, 0x301, 0x301] == some [0xe1, 0x301]
-- decomposes, reorders and recomposes
#guard nfcOf [0x1e0b, 0x323] == some [0x1e0d, 0x307]
-- composes twice
#guard nfcOf [0x41, 0x308, 0x304] == some [0x1de]
-- singleton
#guard nfcOf [0x212b] == some [0xc5]
-- singleton to ASCII
#guard nfcOf [0x212a] == some [0x4b]
-- excluded composite
#guard nfcOf [0x958] == some [0x915, 0x93c]
-- excluded pair stays apart
#guard nfcOf [0x915, 0x93c] == some [0x915, 0x93c]
-- non-starter decomposition
#guard nfcOf [0x344] == some [0x308, 0x301]
-- no composite
#guard nfcOf [0x71, 0x301] == some [0x71, 0x301]
-- Hangul LV
#guard nfcOf [0x1100, 0x1161] == some [0xac00]
-- Hangul LVT
#guard nfcOf [0x1100, 0x1161, 0x11a8] == some [0xac01]
-- Hangul LV and T
#guard nfcOf [0xac00, 0x11a8] == some [0xac01]
-- Hangul LVT already
#guard nfcOf [0xac01] == some [0xac01]
-- starts with a mark
#guard nfcOf [0x301, 0x65] == some [0x301, 0x65]

-- A code point that Unicode 15.0 does not assign.
#guard nfcOf [0x65, 0x301, 0x378] == none
-- Below U+0300, nothing to do.
#guard nfcOf [0x63, 0x61, 0x66, 0xe9] == some [0x63, 0x61, 0x66, 0xe9]
