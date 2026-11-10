-- keep-sorted start
import Fren.Impl
import Heavy.ProcStat
import Reqs.Testing
-- keep-sorted end
open Fren.Lang

/-! The Std-only reading of a process sample, bound to
`testing::heavy_process_sample`. Parsing the stat file remains a tested
claim in `Impls.Trace`. -/

namespace Fren.Impls.HeavyProcStat

open Heavy.ProcStat

def reading : Sample → testing.ProcessSample
  | .vanished => .Vanished
  | .rejected => .Rejected
  | .process => .Process

impl process_sample: testing::heavy_process_sample
    for (state : String) (pid parent group session user system start pages : Int) {
  state := state,
  pid := pid,
  parent := parent,
  group := group,
  session := session,
  user := user,
  system := system,
  start := start,
  pages := pages,
  sample := reading (sample state pid parent group session user system start pages),
} by
  intro state pid parent group session user system start pages _
  simp only [fren_spec, sample]
  split <;> (try split) <;> simp_all [reading] <;> omega

end Fren.Impls.HeavyProcStat
