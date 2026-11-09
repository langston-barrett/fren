module

public import FrenCli2

public section
namespace FrenCli2Tests

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Library tests and real standalone command controls share the existing
bounded SMT job, so the ordinary parent/default path executes them too. -/
def run : IO Unit := do
  for v in [FrenOirToSmt.Verdict.refuted, .inconsistent, .inconclusive, .noChecks, .inputFailure] do
    require (FrenCli2.exitCode v != 0) "nonverified exit zero"
  require (FrenCli2.exitCode .verified == 0) "verified exit"
  let bad ← FrenCli2.checkText "mod test\nexpect c() { expect bad: absent }"
  require (bad.report.verdict == .inputFailure && bad.diagnostic.isSome) "lost source diagnostic"
  let invalid ← FrenCli2.checkText "mod empty" {evaluationDepth := 10001}
  require (invalid.report.verdict == .inputFailure) "unbounded library configuration"
  let good ← FrenCli2.checkText "mod test\nexpect c() { expect good: true }"
  require (good.report.verdict == .verified && good.report.checks.any (·.status == .witness))
    "actual library source check"
  let root ← FrenOirToSmt.sourceRoot
  let out ← IO.Process.output {cmd := "python3", args := #[(root / "test/FrenCli2/controls.py").toString,
    (root / ".lake/build/bin/fren2_check").toString]}
  unless out.exitCode == 0 do throw (IO.userError (out.stdout ++ out.stderr))
  IO.print out.stdout

end FrenCli2Tests
