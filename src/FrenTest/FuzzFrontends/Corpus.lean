-- keep-sorted start
import FrenTest.FuzzFrontends.Known
-- keep-sorted end

open Lean

namespace FrenTest.FuzzFrontends

/-- The ranges of seeds of the corpus that `lake test` checks: the seeds
`[SEED, SEED + COUNT)` of each mode, split into jobs by `corpusJobs`.
Sized so that the whole corpus takes about 2 minutes of one CI machine. -/
def corpus : List (Mode × Nat × Nat) :=
  ([({}, 0, 30), ({}, 30, 30), ({ guards := true }, 0, 20), ({ guards := true }, 20, 20), ({ sites := true }, 0, 20),
    ({ confirm := true }, 0, 20), ({ scrutinees := true }, 0, 20), ({ scrutinees := true }, 840434, 1),
    ({ inductions := true }, 0, 20),
    ({ inductionForms := true }, 0, 20), ({ factScopes := true }, 0, 20),
    ({ inductionCandidates := true }, 0, 20), ({ decidable := true }, 0, 5),
    ({ decidable := true }, 8182108, 1), ({ decidable := true }, 8182118, 1),
    ({ decidable := true }, 8187312, 1),
    ({ enumerationObligations := true }, 0, 20), ({ enumerationObligations := true }, 438, 1),
    ({ enumerationObligations := true }, 555, 1), ({ enumerationRelations := true }, 0, 20),
    ({ unfoldings := true }, 0, 10), ({ datatypeElements := true }, 0, 20),
    ({ recursionPositions := true }, 0, 20), ({ recursionPositions := true }, 934000, 1),
    ({ recursionPositions := true }, 934051, 1), ({ setCardFallback := true }, 0, 8),
    ({ setCardFallback := true }, 1324204, 1)] : List (Mode × Nat × Nat)) ++
    -- Every seed of #820, including the four refuted models, plus a
    -- vacuous check that must not count as a shared static error.
    ([3, 19, 162, 228, 292, 310, 358, 495, 566, 807, 815, 866, 963, 1067, 1164, 1166, 1195,
      1376, 1480, 1499, 1691, 1934, 1942, 2003, 2012, 2085, 2117, 2161, 2173, 2274, 2310,
      2370, 2548, 2631, 2790, 2993].map fun s => ({ setCard := true }, s, 1))

/-- The specs that `knownDifferences` lists outside `corpus`, checked in
the batches that `corpusJobs` lists as `frontendFuzz listed START COUNT`. -/
def listedOutside : List (Mode × Nat) :=
  let inCorpus (m : Mode) (s : Nat) := corpus.any fun (m', a, n) => m' == m && a ≤ s && s < a + n
  (knownDifferences.filterMap fun k => if inCorpus k.mode k.seed then none else some (k.mode, k.seed)).eraseDups

/-- At most this many specs per corpus job, so that no large batch holds
up a shard after its other jobs finish. Each job imports `Fren` once. -/
def corpusBatch : Nat := 5

/-- The arguments of the corpus's jobs of `fren_test`, with every range
and the seeds listed outside them split into batches of `corpusBatch`. -/
def corpusJobs : List (List String) :=
  let batches (n : Nat) := (List.range ((n + corpusBatch - 1) / corpusBatch)).map fun i =>
    (i * corpusBatch, min corpusBatch (n - i * corpusBatch))
  corpus.flatMap (fun (m, a, n) => (batches n).map fun (offset, count) =>
    ["frontendFuzz", toString (a + offset), toString count] ++ m.args.toList)
    ++ (batches listedOutside.length).map fun (offset, count) =>
      ["frontendFuzz", "listed", toString offset, toString count]

/-- The specs of a job of the corpus, from its arguments after
`frontendFuzz`. -/
def corpusSpecs? : List String → Option (List (Mode × Nat))
  | ["listed"] => some listedOutside
  | ["listed", start, count] => do
    let a ← start.toNat?
    let n ← count.toNat?
    return (listedOutside.drop a).take n
  | seed :: count :: args => do
    let a ← seed.toNat?
    let n ← count.toNat?
    let m ← Mode.ofArgs? args
    return (List.range n).map fun i => (m, a + i)
  | _ => none

#guard corpusSpecs? ["listed"] == some listedOutside
#guard corpusSpecs? ["listed", "5", "2"] == some ((listedOutside.drop 5).take 2)
#guard corpusSpecs? ["listed", "x", "2"] == none
#guard corpusSpecs? ["5", "2", "--guards"] == some [({ guards := true }, 5), ({ guards := true }, 6)]
#guard corpusSpecs? ["5", "2", "--other"] == none
#guard corpusSpecs? ["5"] == none
-- The seeds of `knownDifferences` outside the corpus's ranges, the
-- `--avoid-known` ones among them, and every job's specs are the corpus's
-- or those.
#guard listedOutside == ({}, 153) :: ([41, 1156065, 1160095, 3000319, 3102696, 3103202, 3100624, 1159002, 3102505,
  3101311, 3104511, 1157147, 1158050, 3000892, 3102156, 1157298, 1160124, 1160173, 1267162, 1267186].map
    fun s => ({ avoidKnown := true }, s))
#guard corpusJobs.all fun j => (corpusSpecs? (j.drop 1)).isSome
-- The jobs keep every original mode and seed, in order, exactly once,
-- including the final partial batch of seeds outside the ranges.
#guard (corpusJobs.flatMap fun j => (corpusSpecs? (j.drop 1)).getD []) ==
  corpus.flatMap (fun (m, a, n) => (List.range n).map fun i => (m, a + i)) ++ listedOutside
#guard corpusJobs.all fun j =>
  let specs := (corpusSpecs? (j.drop 1)).getD []
  !specs.isEmpty && specs.length ≤ corpusBatch

end FrenTest.FuzzFrontends
