-- fren-covers: eval::outputs_seen
-- keep-sorted start
import FrenCli.Quick
-- keep-sorted end

/-! Tests of `outputsSeen` (`eval::outputs_seen`), and of the search's use
of it, `Spec.noOutputsExist`, through `fren check`'s results in
`test/cli/results/f0601_random_exhausted`. -/

open FrenCli.Eval

-- Every output finite, every assignment ruled out: seen.
#guard outputsSeen #[some 2, some 2] 4 #[.Ruled, .Ruled, .Ruled, .Ruled]
-- No outputs without definitions: one assignment, of the defined ones.
#guard outputsSeen #[] 1 #[.Ruled]
-- An output with infinitely many values.
#guard !outputsSeen #[some 2, none] 0 #[]
-- An assignment that meets the constraints, or that needs a value it lacks.
#guard !outputsSeen #[some 2] 2 #[.Ruled, .Satisfied]
#guard !outputsSeen #[some 2] 2 #[.Undefined, .Ruled]
-- Too many assignments to try.
#guard !outputsSeen #[some 4097] 4097 #[]
-- Assignments missing.
#guard !outputsSeen #[some 2] 2 #[.Ruled]
