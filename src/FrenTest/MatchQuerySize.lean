-- keep-sorted start
import FrenTest.Resolved
-- keep-sorted end

/-! # A bound on standalone nested-match queries (#976) -/

namespace FrenTest.MatchQuerySize

/-- Source-labelled assumptions for index checks, as the production dump
writes them. The positive case is separate from conservative controls. -/
def premises (text : String) (positive : Bool) : Array String := Id.run do
  let mut header := ""
  let mut lines := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "; " then header := line
    if line.endsWith " ; premise" && header.startsWith "; distinct:" == positive then
      lines := lines.push s!"{header}\n{line}"
  return lines

/-- Exercise the production CLI and solver, rather than a model of the
encoder. The driver uses its existing fresh-process CLI entry point;
standalone probes may supply the freshly built `fren` executable instead.
This bound is below the original encoding's 154,505-byte dump. -/
def check (run : Array String → IO IO.Process.Output := Resolved.run) : IO (Array String) := do
  let args := #["check", "--jobs", "1", "--timeout", "2", "--color=never",
    "test/ui/checks/match_query_size.fren"]
  let plain ← run args
  let dumped ← run (args.push "--dump=smt")
  let mut failures := #[]
  unless plain.exitCode == 0 && dumped.exitCode == 0 do
    failures := failures.push s!"match query size: check failed:\n{plain.stderr}{dumped.stderr}"
  unless plain.stderr == dumped.stderr do
    failures := failures.push "match query size: dumping changed diagnostics"
  let queries := (dumped.stdout.splitOn "(check-sat)").length - 1
  unless queries == 17 do
    failures := failures.push s!"match query size: expected 17 production queries, got {queries}"
  let bytes := dumped.stdout.toUTF8.size
  unless bytes > 1000 && bytes < 150000 do
    failures := failures.push s!"match query size: expected a nonempty dump below 150000 bytes, got {bytes}"
  let indexed := (dumped.stdout.splitOn "(reset)").filter (·.contains " ; premise".toSlice)
  let largest := indexed.foldl (fun n query => max n query.toUTF8.size) 0
  unless indexed.length == 10 && largest < 8000 do
    failures := failures.push s!"match query size: expected 10 indexed queries below 8000 bytes, got {indexed.length} with largest {largest}"
  let args := #["check", "--jobs", "1", "--timeout", "2", "--color=never",
    "test/ui/checks/match_query_size_controls.fren"]
  let plain ← run args
  let dumped ← run (args.push "--dump=smt")
  unless plain.exitCode == 0 && dumped.exitCode == 0 && plain.stderr == dumped.stderr do
    failures := failures.push s!"match query controls: verdicts or diagnostics changed:\n{plain.stderr}{dumped.stderr}"
  let positive := premises dumped.stdout true
  unless positive.size == 4 && positive.all (!·.contains "(not ".toSlice) do
    failures := failures.push "match query controls: distinct constructor paths retain exclusions or are missing"
  let negative := premises dumped.stdout false
  let expected ← IO.FS.readFile "test/ui/checks/match_query_size_controls.expected"
  unless negative.size == 38 && String.intercalate "\n" negative.toList ++ "\n" == expected do
    failures := failures.push "match query controls: conservative paths differ from the original production encoding"
  return failures

end FrenTest.MatchQuerySize
