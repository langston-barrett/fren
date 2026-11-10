module

public import FrenThirToMirTests.Support
import Plausible

public section
namespace FrenThirToMirTests
open FrenMir FrenModule Plausible
open scoped Plausible.Decorations

/-- Direct generated source -> actual admission -> actual producer. Each sample
must include its valid, invalid and partial classes; there are no discarded
premises and expected counts are independent constants. -/
private def sample (file n : Nat) : Bool := Id.run do
  let source := blocksSource (n % 41)
  let .ok c := compile file source | return false
  if !blocksAudit c.theory || c.theory.source != c.admitted.typed ||
      c.theory.source.resolved.document.emit != source then return false
  -- Distinct nominal ownership even with equal constructor spellings.
  let enums := c.theory.declarations.filterMap fun d => match d with
    | .enumeration e => some e | _ => none
  if enums.map (·.id) != #[key "Light", key "Other"] then return false
  if enums.map (fun e => e.constructors.map Prod.fst) !=
      #[#[((key "Light").named "Red"), ((key "Light").named "Green")],
        #[((key "Other").named "Red"), ((key "Other").named "Green")]] then return false
  if !value (outcome c "unused" #[.int (n : Int)]) (.int ((n : Int) + 3)) then return false
  if !(c.theory.source.resolved.document.tape.all (·.span.file == ⟨file⟩)) then return false
  let .ok again := compile file source | return false
  if again.theory != c.theory then return false
  let .ok changedFile := compile (file + 1) source | return false
  if changedFile.theory.source == c.theory.source then return false
  for text in #[source.replace "assume later: x <= 10" "",
      source.replace "expect first:" "assume first:",
      source.replace "expect empty() {}" ""] do
    let .ok mutant := compile file text | return false
    if blocksAudit mutant.theory then return false
  for text in #[source ++ "\nfn loop(x: Int): Int := loop(x)",
      source ++ "\nfn bad(x: Int): Int := false",
      source ++ "\nfn bad(x: Int): Int := missing",
      source ++ "\nfn bad(x: Int): Int := ("] do
    if (FrenThirToMir.fromSource ⟨file⟩ text).isOk then return false
  if (FrenWalking.fromResolved {c.admitted.input with references := #[]}).isOk then return false
  -- Generated actual partial input remains admitted and carries structured
  -- demand; undefined is not an admission failure or a Boolean false.
  let partialSource := "mod skeleton\nexpect partial(x: Int) { expect goal: x div 0 = 0 assume later: x <= 10 }"
  let .ok p := compile file partialSource | return false
  if !requestsMatch p.theory #[⟨"partial", none, #["later"], #["x"], ["x"]⟩,
      ⟨"partial", some "goal", #["later"], #["x"], ["x"]⟩] then return false
  match outcome p "partial" #[.int (n : Int)] (some "goal") with
  | .error (.undefined span .div) =>
    if span.file != ⟨file⟩ then return false
  | _ => return false
  return true

private def checkProperty (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 35, randomSeed := some 20261119}
  IO.println s!"actual MIR Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "MIR actual source property failed")

def runProperties : IO Unit := do
  checkProperty <| ∀ (file n : Nat), sample file n = true
  for n in [:24] do
    unless sample (200 + n) n do throw (IO.userError s!"MIR census sample {n} failed")
  IO.println "MIR census: 24 base admitted + 24 partial admitted; 96 rejected sources, 24 edited-resolution rejections, 72 admitted source mutants failing independent checks, 24 undefined outcomes; 264 base + 48 partial requests; discarded=0. Plausible: 100 samples, same mandatory classes per sample."

#print axioms FrenThirToMir.retains
#print axioms FrenThirToMir.requests_from_blocks
#print axioms FrenThirToMir.request_from_block
#print axioms FrenThirToMir.admission
#print axioms FrenThirToMir.deterministic
#print axioms FrenThirToMir.rejected
#print axioms FrenMir.assumptions_exact
#print axioms FrenMir.request_context
#print axioms FrenMir.validity_member

end FrenThirToMirTests
