-- keep-sorted start
import FrenTest.ImplPath
import Heavy.Forecast
import Heavy.Ownership
-- keep-sorted end

/-! Regressions use real compiled declarations and real `impl` theorems.
None is an audit entry point in the production environment. -/

namespace Fren.Core.ImplPathFixture

@[inline] def bound (b : Bool) : Bool := !b

def direct (b : Bool) : Bool := bound b

def derived (b : Bool) : Bool := !(direct b)

def discard (_ : Bool) : Bool := true

def bypass (b : Bool) : Bool := discard (bound b)

def unused (b : Bool) : Bool := let _ := bound b; b

def branch (b : Bool) : Nat := if bound b then 0 else 1

def closure (bs : Array Bool) : Array Bool := bs.map fun b => bound b

def unusedClosure (b : Bool) : Bool := let _ := fun x => bound x; b

def proofOnly (b : Bool) : Bool :=
  have _ : bound false = true := rfl
  b

structure Box where
  value : Bool

def boxed (b : Bool) : Box := ⟨bound b⟩

inductive Tag where
  | yes | no

def tagged (b : Bool) : Tag := if bound b then .yes else .no

def slow (b : Bool) : Bool := bound b

def fast (b : Bool) : Bool := bound b

@[csimp] theorem slow_eq_fast : @slow = @fast := rfl

def replaced (b : Bool) : Bool := fast b

structure ProofBox where
  value : Bool
  witness : bound false = true

structure Phantom (p : Bool → Prop) where
  value : Bool

def predicateFrom (b : Bool) : Bool → Prop := fun x => b = x

end Fren.Core.ImplPathFixture

namespace Fren.Impls.ImplPathFixture

universe u

def discard (_ : Bool) : Bool := true

def project (b : Fren.Core.ImplPathFixture.Box) : Bool := b.value

def unwrapSubtype {p : Bool → Prop} (x : Subtype p) : Bool := x.val

def identityValue {α : Type u} (x : α) : α := x

-- A real call to the standalone kernel is still outside the audited Fren
-- runtimes. Naming its adapter in Fren.Impls must not turn it into production.
def standaloneRegistry (b : Bool) : Bool :=
  (Heavy.Ownership.registry (!b) 0 1 false false).acquired

def readTag : Fren.Core.ImplPathFixture.Tag → Bool
  | .yes => true
  | .no => false

end Fren.Impls.ImplPathFixture

open Fren.Lang

mod impl_path_fixture

proc rule(b?): (det accepted?) {
  out accepted? := not b?
}

namespace FrenTest.ImplPathTests

impl actual: rule for (b : Bool) {
  b? := b,
  accepted? := Fren.Core.ImplPathFixture.bound b,
} by
  intro b _
  cases b <;> decide

-- Only the mapped result is a binding; functions in an input and in a
-- theorem's proof must not count. Another impl of the same Req is
-- inventoried separately.
impl input_only: rule for (b : Bool) {
  b? := Fren.Core.ImplPathFixture.bound b,
  accepted? := b,
} by
  intro b _
  cases b <;> decide

impl adapter_discarded: rule {
  b? := false,
  accepted? := Fren.Impls.ImplPathFixture.discard (Fren.Core.ImplPathFixture.bound true),
}

impl standalone_kernel: rule for (b : Bool) {
  b? := b,
  accepted? := Fren.Impls.ImplPathFixture.standaloneRegistry b,
} by
  intro b _
  cases b <;> decide

impl binder_domain: rule for
    (_h : Fren.Generated.impl_path_fixture.rule.assumes true (Fren.Core.ImplPathFixture.derived false)) {
  b? := true,
  accepted? := Fren.Core.ImplPathFixture.bound true,
} by
  intro _h _
  decide

impl projected: rule for (b : Bool) {
  b? := b,
  accepted? := Fren.Impls.ImplPathFixture.project (Fren.Core.ImplPathFixture.boxed b),
} by
  intro b _
  cases b <;> decide

impl matched: rule for (b : Bool) {
  b? := b,
  accepted? := Fren.Impls.ImplPathFixture.readTag (Fren.Core.ImplPathFixture.tagged b),
} by
  intro b _
  cases b <;> decide

-- Erased predicates, type formers and proof fields must not supply a
-- producer for a literal runtime output, even through an unfolded adapter.
impl erased_subtype: rule {
  b? := false,
  accepted? := (⟨true, rfl⟩ : { b : Bool // Fren.Core.ImplPathFixture.bound false = b }).val,
}

impl erased_adapter: rule {
  b? := false,
  accepted? := Fren.Impls.ImplPathFixture.unwrapSubtype
    (⟨true, rfl⟩ : { b : Bool // Fren.Core.ImplPathFixture.bound false = b }),
}

impl erased_proof: rule {
  b? := false,
  accepted? := ({ value := true, witness := Eq.refl (Fren.Core.ImplPathFixture.bound false) } :
    Fren.Core.ImplPathFixture.ProofBox).value,
}

impl erased_type_former: rule {
  b? := false,
  accepted? := (⟨true⟩ : Fren.Core.ImplPathFixture.Phantom
    (Fren.Core.ImplPathFixture.predicateFrom (Fren.Core.ImplPathFixture.bound false))).value,
}

impl erased_polymorphic_adapter: rule {
  b? := false,
  accepted? := (Fren.Impls.ImplPathFixture.identityValue
    (⟨true, rfl⟩ : { b : Bool // Fren.Core.ImplPathFixture.bound false = b })).val,
}

impl dependent_runtime: rule for (b : Bool) {
  b? := b,
  accepted? := (⟨Fren.Core.ImplPathFixture.bound b, rfl⟩ :
    { value : Bool // Fren.Core.ImplPathFixture.bound b = value }).val,
} by
  intro b _
  cases b <;> decide

impl polymorphic_runtime: rule for (b : Bool) {
  b? := b,
  accepted? := Fren.Impls.ImplPathFixture.identityValue (Fren.Core.ImplPathFixture.bound b),
} by
  intro b _
  cases b <;> decide

impl lambda_runtime: rule for (b : Bool) {
  b? := b,
  accepted? := [b].all fun x => Fren.Core.ImplPathFixture.bound x,
} by
  intro b _
  cases b <;> decide

open Lean FrenTest.ImplPath

run_elab do
  let env ← getEnv
  let ds ← sourceDeclarations ((declarations env).filter fun d =>
    (`Fren.Core.ImplPathFixture).isPrefixOf d.name)
  let g := graph env ds
  let target := `Fren.Core.ImplPathFixture.bound
  -- Audit all five impls' deciding functions across both Heavy modules.
  -- Conformance proofs and differential fixtures do not create a path from
  -- Fren's reporting roots. Keep the standalone scope distinct from adapters
  -- and the connected, discarded and erased runtime cases below.
  for n in #[`Heavy.Forecast.predict, `Heavy.Ownership.registry,
      `Heavy.Ownership.reportOwner, `Heavy.Ownership.lease,
      `Heavy.Ownership.elapsedTimestamp, `Heavy.Ownership.remainingDeadline,
      `Heavy.Ownership.freshReport] do
    unless env.contains n do
      throwError "implPaths: missing standalone kernel declaration: {n}"
    if production n then
      throwError "implPaths: standalone kernel counted as Fren production: {n}"
  for n in #[`Fren.Core.ImplPathFixture.direct, `Fren.Core.ImplPathFixture.derived,
      `Fren.Core.ImplPathFixture.branch, `Fren.Core.ImplPathFixture.closure] do
    unless (paths g #[n]).contains target do
      throwError "implPaths: failed to follow value dependency from {n}"
  for n in #[`Fren.Core.ImplPathFixture.bypass, `Fren.Core.ImplPathFixture.unused,
      `Fren.Core.ImplPathFixture.unusedClosure, `Fren.Core.ImplPathFixture.proofOnly] do
    if (paths g #[n]).contains target then
      throwError "implPaths: accepted discarded or proof-only dependency from {n}"
  unless (paths g #[`Fren.Core.ImplPathFixture.replaced]).contains `Fren.Core.ImplPathFixture.slow do
    throwError "implPaths: ignored a proved compiler replacement"
  let bs ← bindings env
  let some actual := bs.find? (·.impl == `FrenTest.ImplPathTests.actual)
    | throwError "implPaths: did not extract the actual impl"
  unless actual.output == `accepted? && actual.functions == #[target] do
    throwError "implPaths: did not recover the mapped output function"
  let some inputOnly := bs.find? (·.impl == `FrenTest.ImplPathTests.input_only)
    | throwError "implPaths: did not extract the input-only impl"
  unless inputOnly.functions.isEmpty do
    throwError "implPaths: treated an input function as a result binding"
  let some discarded := bs.find? (·.impl == `FrenTest.ImplPathTests.adapter_discarded)
    | throwError "implPaths: did not extract the discarded adapter impl"
  unless discarded.functions.isEmpty do
    throwError "implPaths: treated a discarded adapter argument as a result binding"
  let some standalone := bs.find? (·.impl == `FrenTest.ImplPathTests.standalone_kernel)
    | throwError "implPaths: did not extract the standalone-kernel impl"
  unless standalone.output == `accepted? && standalone.functions.isEmpty do
    throwError "implPaths: treated a standalone kernel as a Fren production binding"
  let some binderDomain := bs.find? (·.impl == `FrenTest.ImplPathTests.binder_domain)
    | throwError "implPaths: did not extract the proof-binder impl"
  unless binderDomain.functions == #[target] do
    throwError "implPaths: confused a proof binder with the actual mappings"
  for (bindingName, functionName) in #[(`FrenTest.ImplPathTests.projected, `Fren.Core.ImplPathFixture.boxed),
      (`FrenTest.ImplPathTests.matched, `Fren.Core.ImplPathFixture.tagged)] do
    let some b := bs.find? (·.impl == bindingName)
      | throwError "implPaths: missing mapping {bindingName}"
    unless b.functions == #[functionName] do
      throwError "implPaths: treated representation machinery as the producer in {bindingName}"
  for bindingName in #[`FrenTest.ImplPathTests.erased_subtype, `FrenTest.ImplPathTests.erased_adapter,
      `FrenTest.ImplPathTests.erased_proof, `FrenTest.ImplPathTests.erased_type_former,
      `FrenTest.ImplPathTests.erased_polymorphic_adapter] do
    let some b := bs.find? (·.impl == bindingName)
      | throwError "implPaths: missing erased-argument mapping {bindingName}"
    unless b.functions.isEmpty do
      throwError "implPaths: counted an erased argument in {bindingName}: {b.functions}"
  for bindingName in #[`FrenTest.ImplPathTests.dependent_runtime,
      `FrenTest.ImplPathTests.polymorphic_runtime, `FrenTest.ImplPathTests.lambda_runtime] do
    let some b := bs.find? (·.impl == bindingName)
      | throwError "implPaths: missing runtime mapping {bindingName}"
    unless b.functions == #[target] do
      throwError "implPaths: erased a runtime producer in {bindingName}"

end FrenTest.ImplPathTests
