/-!
# Selecting the jobs of `lake test`

Which jobs `lake test -- [--skip-own-mutants] [--shard K/N]` runs
(`Reqs/dev/Testing`): the shard of each job, which `Impls.Testing` proves
meets `testing::shard`, and the selection, which runs the jobs placed in
the shard asked for.
-/

namespace FrenTest.Jobs

/-- Whether `job` checks a slice of the mutants of Fren's own requirements,
the slowest jobs, which `--skip-own-mutants` leaves out. -/
def ownMutantsJob : List String → Bool
  | ["mutation", "0", _, _] => true
  | _ => false

/-- Whether `--skip-own-mutants`, if `skip`, leaves out `job`. -/
def skipped (skip : Bool) (job : List String) : Bool := skip && ownMutantsJob job

/-- The shard `K/N` of `--shard K/N`, for `K < N`. -/
def parseShard (s : String) : Except String (Nat × Nat) :=
  match s.splitOn "/" with
  | [k, n] => match k.toNat?, n.toNat? with
    | some k, some n => if k < n then .ok (k, n) else .error s!"--shard {s}: K must be less than N"
    | _, _ => .error s!"--shard {s}: expected K/N, two whole numbers"
  | _ => .error s!"--shard {s}: expected K/N, two whole numbers"

/-- The shard of the `i`th job of the selection, of `n` shards: the first
job, `ownSpec`, alone in shard 0, as on one machine it takes about as long
as all the others but `ownMutantsJob`'s, and the others dealt in turn to
shards 1 to `n - 1`, so that the slowest, which come first, spread over
them. -/
def shardOf (n i : Nat) : Nat :=
  if n ≤ 1 then 0 else if i == 0 then 0 else 1 + (i - 1) % (n - 1)

/-- The shard of `n` that runs the job at position `i` of `jobs`, or `none`
if `--skip-own-mutants` (`skip`) leaves it out: that of its position among
the jobs kept (`shardOf`). -/
def placement (skip : Bool) (n : Nat) (jobs : List (List String)) (i : Nat) : Option Nat :=
  if skipped skip jobs[i]! then none else some (shardOf n ((jobs.take i).countP (!skipped skip ·)))

/-- The jobs that `args` select, in order: those that `placement` puts in
the shard `K` of `--shard K/N`, or, without it, in the one shard of one, so
that the shards together run each job once, but those that
`--skip-own-mutants` leaves out. -/
def selectJobs (args : List String) (all : Array (List String)) : Except String (Array (List String)) := do
  let skip := args.contains "--skip-own-mutants"
  let (k, n) ← match args.dropWhile (· != "--shard") with
    | _ :: s :: _ => parseShard s
    | [_] => .error "--shard needs an argument, K/N"
    | [] => pure (0, 1)
  return (all.zipIdx.filter fun (_, i) => placement skip n all.toList i == some k).map (·.1)

end FrenTest.Jobs
