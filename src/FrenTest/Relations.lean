-- keep-sorted start
import Fren.FinSet
-- keep-sorted end

/-!
# Relations

The relational operations of `Fren.FinSet` on small relations, computed.
-/

open Fren.FinSet

#guard closure (ofList [(1, 2), (2, 3)]) = ofList [(1, 2), (2, 3), (1, 3)]
#guard closure (ofList [(1, 2), (2, 1)]) = ofList [(1, 2), (2, 1), (1, 1), (2, 2)]
#guard closure (ofList ([] : List (Nat × Nat))) = ∅
#guard card (ofList [1, 1, 2]) = 2
#guard image (ofList [(1, 2)]) (ofList [1, 3]) = ofList [2]
#guard image (ofList [(1, 2), (3, 4)]) (ofList [5]) = ∅
#guard join (ofList [(1, 2), (1, 3)]) (ofList [(2, 4), (3, 5), (6, 7)]) = ofList [(1, 4), (1, 5)]
#guard inverse (ofList [(1, 2), (3, 4)]) = ofList [(2, 1), (4, 3)]
#guard domain (ofList [(1, 2), (1, 3), (4, 5)]) = ofList [1, 4]
#guard range (ofList [(1, 2), (1, 3), (4, 2)]) = ofList [2, 3]

-- The membership lemmas, in the pair forms the elaborator relies on.
example {r : Fren.FinSet (Nat × Int)} {q : Fren.FinSet (Int × Bool)} {a : Nat} {c : Bool} :
    (a, c) ∈ join r q ↔ ∃ b, (a, b) ∈ r ∧ (b, c) ∈ q := by simp
example {r : Fren.FinSet (Nat × Int)} {a : Nat} {b : Int} : (b, a) ∈ inverse r ↔ (a, b) ∈ r := by
  simp
