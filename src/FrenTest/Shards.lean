-- keep-sorted start
import FrenTest.Jobs
-- keep-sorted end

/-!
The selection of `lake test`'s jobs (`Reqs/dev/Testing`): the shards of
`--shard K/N` run each job once, shard 0 runs `ownSpec` alone, and
`--skip-own-mutants` leaves out the slices of the mutants of Fren's own
requirements and nothing else. `Impls.Testing` proves this for any jobs;
these pin down the arguments too.
-/

open FrenTest.Jobs

/-- Jobs as `jobs` in `src/FrenTestMain.lean` lists them: `ownSpec`, the
slices of the mutants of Fren's own requirements, then the others, with a
mutation job of another group, which is not left out. -/
def sample : Array (List String) :=
  #[["ownSpec"]] ++ (List.range 8).toArray.map (["mutation", "0", toString ·, "8"])
    ++ #[["ui", "a.fren"], ["ui", "b.fren"], ["snapshots"], ["mutation", "1", "0", "1"], ["decisions", "x.fren"]]

/-- The jobs of each shard of `n`, with the arguments `args` too. -/
def shards (args : List String) (n : Nat) : List (Array (List String)) :=
  (List.range n).map fun k => (selectJobs (args ++ ["--shard", s!"{k}/{n}"]) sample).toOption.getD #[]

/-- The jobs of the shards together, sorted. -/
def together (args : List String) (n : Nat) : List (List String) :=
  ((shards args n).foldl (· ++ ·) #[]).toList.mergeSort (toString · ≤ toString ·)

def sorted (jobs : Array (List String)) : List (List String) := jobs.toList.mergeSort (toString · ≤ toString ·)

def isError : Except String α → Bool
  | .error _ => true
  | .ok _ => false

-- Without arguments, every job; `--skip-own-mutants` leaves out the eight
-- slices alone.
#guard (selectJobs [] sample).toOption == some sample
#guard (selectJobs ["--skip-own-mutants"] sample).toOption == some (sample.filter (!ownMutantsJob ·))
#guard ((selectJobs ["--skip-own-mutants"] sample).toOption.map (·.size)) == some (sample.size - 8)
#guard ownMutantsJob ["mutation", "0", "3", "8"] && !ownMutantsJob ["mutation", "1", "0", "1"] && !ownMutantsJob ["ownSpec"]

-- The shards together run each job once, with or without
-- `--skip-own-mutants`, for any number of shards.
#guard (List.range 6).all fun n => together [] (n + 1) == sorted sample
#guard (List.range 6).all fun n =>
  together ["--skip-own-mutants"] (n + 1) == sorted (sample.filter (!ownMutantsJob ·))

-- Shard 0 runs `ownSpec` alone, and the others are dealt in turn.
#guard (shards ["--skip-own-mutants"] 4).head? == some #[["ownSpec"]]
#guard shards ["--skip-own-mutants"] 3 ==
  [#[["ownSpec"]], #[["ui", "a.fren"], ["snapshots"], ["decisions", "x.fren"]], #[["ui", "b.fren"], ["mutation", "1", "0", "1"]]]
-- `--skip-own-mutants` may come after `--shard`.
#guard (selectJobs ["--shard", "1/3", "--skip-own-mutants"] sample).toOption == some (shards ["--skip-own-mutants"] 3)[1]!
-- With one shard, it runs everything.
#guard (selectJobs ["--shard", "0/1"] sample).toOption == some sample

-- A shard out of range, or not a pair of whole numbers, is an error.
#guard (parseShard "2/4").toOption == some (2, 4)
#guard isError (parseShard "4/4")
#guard isError (parseShard "0/0")
#guard isError (parseShard "1")
#guard isError (parseShard "1/2/3")
#guard isError (parseShard "-1/2")
#guard isError (parseShard "a/2")
#guard isError (selectJobs ["--shard"] sample)
#guard isError (selectJobs ["--shard", "3/3"] sample)
