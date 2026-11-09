import Heavy.Budget
import Heavy.Forecast
import Heavy.Process

/-! Statistical compiler advice, separate from complete-input provenance and
legacy whole-job forecasts. No admission policy or future memory bound. -/
namespace Heavy.CompilerForecast

structure Context where
  source : String
  cwd : String
  sourceFingerprint : String
  compiler : String
  compilerFingerprint : String
  version : String
  githash : String
  args : List String
  setup : Option String
  setupFingerprint : Option String
  deriving DecidableEq, Repr

/-- Length framing and hexadecimal bytes preserve order and missing versus empty. -/
def identityField (s : String) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := s!"{s.utf8ByteSize}:"
  for b in s.toUTF8 do
    out := out.push digits[b.toNat / 16]!
    out := out.push digits[b.toNat % 16]!
  return out

def identityOption : Option String → String
  | none => "0"
  | some s => "1" ++ identityField s

/-- Bounded partial identity, not a cryptographic digest or input closure. -/
def cohortIdentity (c : Context) (boot : String) : Option String :=
  if boot == "" then none else
  let value := String.join (([c.source, c.cwd, c.sourceFingerprint, c.compiler,
    c.compilerFingerprint, c.version, c.githash].map identityField) ++
    [s!"{c.args.length}:"] ++ c.args.map identityField ++
    [identityOption c.setup, identityOption c.setupFingerprint, identityField boot])
  if value.utf8ByteSize > 65536 then none else some value

/-- Required fields are decoded strictly, never defaulted to successful zeroes. -/
structure Record where
  context : Context
  sourceAfter : String
  boot : Option String
  schema : Nat
  family : String
  kind : String
  launchError : Nat
  execError : Nat
  waitError : Nat
  clockError : Nat
  status : Nat
  pid : Nat
  gateError : Option Nat
  childPresent : Option Bool
  wrapperCode : Option Nat
  start : Nat
  finish : Nat
  rss : Nat
  measuredRss : Nat
  deriving Repr

/-- Exact raw paths and argv, not a filename/module hint or job-kind key.
Absent setup is supported; a named setup requires a nonempty fingerprint.
This deliberately does not assert closure over imports or environment. -/
def validContext (c : Context) : Bool :=
  [c.source, c.cwd, c.sourceFingerprint, c.compiler, c.compilerFingerprint,
    c.version, c.githash].all (· != "") &&
  c.cwd.startsWith "/" && c.compiler.startsWith "/" &&
  (match c.setup, c.setupFingerprint with
   | none, none => true
   | some s, some f => s != "" && f != ""
   | _, _ => false) &&
  (match Heavy.Process.parseMetadata c.args with
   | some m => m.kind == "file" && m.source == some c.source && m.setup == c.setup &&
       !c.args.contains "--run"
   | none => false)

/-- Adviser eligibility is weaker than provenance completeness, but stricter
than measured-usage availability: only successful stable-source compiles.
Monotonic times are comparable only in the caller's nonempty boot domain. -/
def sample (r : Record) (c : Context) (boot : String) (cutoff now : Nat) : Bool :=
  decide (r.context = c) && r.sourceAfter == c.sourceFingerprint &&
  boot != "" && r.boot == some boot && r.family == "lean" && r.kind == "file" &&
  (if r.schema == 2 then true else r.schema == 3 && r.gateError == some 0 &&
    r.childPresent == some true && r.wrapperCode == some 0) &&
  r.launchError == 0 && r.execError == 0 && r.waitError == 0 && r.clockError == 0 &&
  r.status == 0 && r.pid > 0 && r.start ≤ r.finish &&
  cutoff ≤ r.finish && r.finish ≤ now && r.rss > 0 && r.measuredRss == r.rss

def eligible (r : Record) (c : Context) (boot : String) (cutoff now : Nat) : Bool :=
  validContext c && sample r c boot cutoff now

/-- At most n retained samples; newest completion wins, then larger peak.
The accumulator is bounded even when the supplied history is longer. -/
def recent (rs : List Record) (c : Context) (boot : String) (cutoff now n : Nat) : Heavy.Forecast.Peaks :=
  rs.foldl (fun ps r => if eligible r c boot cutoff now then
    Heavy.Forecast.insert r.finish r.rss n ps else ps) []

/-- Zero limits, empty/insufficient evidence and invalid windows are UNKNOWN.
A positive minimum is explicit caller policy, not statistical calibration. -/
def advice (rs : List Record) (c : Context) (boot : String) (cutoff now n minimum : Nat) :
    Option Int × Nat :=
  let ps := recent rs c boot cutoff now n
  (if minimum = 0 ∨ n < minimum ∨ now < cutoff ∨ ps.length < minimum then none
   else Heavy.Forecast.maximum ps, ps.length)

/-- Shared with the explicit exporter: positive additive padding, bounded by
manifest demand capacity. This is not a guarantee about a future peak. -/
def padded (peak : Option Int) (padding : Nat) : Option Int := do
  let p ← peak
  if p > 0 && padding > 0 && p + padding ≤ 2^50 then some (p + padding) else none

/-- Optional advice that cannot fit alone in the configured session is
unavailable. Preserve the operator fallback, without weakening the real gate
or treating the fallback as an upper bound on measured/future usage. -/
def forSession (peak : Option Int) (padding : Nat) (allowance parent : Int) : Option Int := do
  let demand ← padded peak padding
  if Heavy.Budget.decision allowance parent 0 demand 1 1 == 1 then some demand else none

/-- The retained count is bounded for arbitrary raw histories, not fixtures. -/
theorem take_bound (ps : Heavy.Forecast.Peaks) (n : Nat) :
    (Heavy.Forecast.take n ps).length ≤ n := by
  induction ps generalizing n with
  | nil => simp [Heavy.Forecast.take]
  | cons p ps ih =>
    by_cases hn : n = 0
    · simp [Heavy.Forecast.take, hn]
    · simp only [Heavy.Forecast.take, hn, if_false, List.length_cons]
      have := ih (n - 1)
      omega

theorem insert_bound (ps : Heavy.Forecast.Peaks) (t p : Int) (n : Nat) :
    (Heavy.Forecast.insert t p n ps).length ≤ n := by
  induction ps generalizing n with
  | nil => by_cases hn : n = 0 <;> simp [Heavy.Forecast.insert, hn] <;> omega
  | cons x ps ih =>
    obtain ⟨u, q⟩ := x
    by_cases hn : n = 0
    · simp [Heavy.Forecast.insert, hn]
    · simp only [Heavy.Forecast.insert, hn, if_false]
      split
      · have := take_bound ((u, q) :: ps) (n - 1)
        simp only [List.length_cons]; omega
      · have := ih (n - 1)
        simp only [List.length_cons]; omega

theorem recent_bound (rs : List Record) (c : Context) (boot : String) (cutoff now n : Nat) :
    (recent rs c boot cutoff now n).length ≤ n := by
  have aux (rows : List Record) (ps : Heavy.Forecast.Peaks) (h : ps.length ≤ n) :
      (rows.foldl (fun ps r => if eligible r c boot cutoff now then
        Heavy.Forecast.insert r.finish r.rss n ps else ps) ps).length ≤ n := by
    induction rows generalizing ps with
    | nil => exact h
    | cons r rows ih =>
      simp only [List.foldl_cons]
      apply ih
      split
      · exact insert_bound _ _ _ _
      · exact h
  exact aux rs [] (by simp)

/-- Every returned maximum is an actual selected peak and covers all selected
peaks. This says nothing about a future run or concurrent physical memory. -/
theorem maximum_exact (ps : Heavy.Forecast.Peaks) (m : Int)
    (h : Heavy.Forecast.maximum ps = some m) :
    (∃ t, (t, m) ∈ ps) ∧ ∀ t p, (t, p) ∈ ps → p ≤ m := by
  induction ps generalizing m with
  | nil => simp [Heavy.Forecast.maximum] at h
  | cons x ps ih =>
    obtain ⟨t, p⟩ := x
    cases hm : Heavy.Forecast.maximum ps with
    | none =>
      have empty : ps = [] := by
        cases ps with
        | nil => rfl
        | cons y ys =>
          obtain ⟨v, w⟩ := y
          simp only [Heavy.Forecast.maximum] at hm
          cases hy : Heavy.Forecast.maximum ys <;> simp_all
      subst empty
      have hp : p = m := by simpa [Heavy.Forecast.maximum] using h
      subst m
      exact ⟨⟨t, by simp⟩, by
        intro u r hr
        have he : u = t ∧ r = p := by simpa using hr
        omega⟩
    | some q =>
      have hmax : max p q = m := by simpa [Heavy.Forecast.maximum, hm] using h
      obtain ⟨⟨u, hu⟩, covers⟩ := ih q hm
      constructor
      · by_cases hp : p ≤ q
        · have hmq : m = q := by omega
          rw [hmq]
          exact ⟨u, List.mem_cons_of_mem _ hu⟩
        · have hmp : m = p := by omega
          rw [hmp]
          exact ⟨t, by simp⟩
      · intro u r hr
        rcases List.mem_cons.mp hr with he | hr
        · cases he; omega
        · have := covers u r hr; omega

/-- Equality at both time endpoints is admitted, including completion = now. -/
theorem sample_endpoints (r : Record) (c : Context) (boot : String) :
    sample r c boot r.finish r.finish = sample r c boot 0 r.finish := by
  simp [sample]

/-- Strict unknown is a property of the actual advice boundary. -/
theorem insufficient_unknown (rs : List Record) (c : Context) (boot : String)
    (cutoff now n minimum : Nat)
    (h : (recent rs c boot cutoff now n).length < minimum) :
    (advice rs c boot cutoff now n minimum).1 = none := by
  simp [advice, h]

end Heavy.CompilerForecast
