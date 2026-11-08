module

public import Std

public section
namespace ExprPrototype

inductive Phase where
  | high | low
  deriving DecidableEq, Repr

/-- The toy sugared form exists only before lowering. -/
@[expose] def HasSugar (p : Phase) : Prop := p = .high
instance (p : Phase) : Decidable (HasSugar p) := inferInstanceAs (Decidable (p = .high))

/-- Child positions bind zero or one new variable; let values are outside the binder. -/
inductive Layer (p : Phase) (R : Type) where
  | lit (value : Nat)
  | var (index : Nat)
  | letE (value body : R)
  | all (body : R)
  | array (children : Array R)
  | sugar (gate : HasSugar p) (body : R)
  deriving BEq, Repr

inductive Expr (p : Phase) where
  | roll (layer : Layer p (Expr p))
  deriving BEq, Repr

namespace Layer
/-- Visit immediate children left to right, passing the number of new binders.
This is a one-layer traversal, not a recursive whole-term walk. -/
def mapChildrenM [Monad m] (f : Nat → R → m S) : Layer p R → m (Layer p S)
  | .lit n => pure (.lit n)
  | .var i => pure (.var i)
  | .letE v b => return .letE (← f 0 v) (← f 1 b)
  | .all b => return .all (← f 1 b)
  | .array xs => return .array (← xs.mapM (f 0))
  | .sugar h b => return .sugar h (← f 0 b)

def mapChildren (f : Nat → R → S) (layer : Layer p R) : Layer p S :=
  Id.run (mapChildrenM (fun d x => pure (f d x)) layer)
end Layer

/-- A total catamorphism; direct constructor recursion exposes the decrease
that recursion hidden behind a generic traversal does not expose. -/
def fold (alg : Layer p A → A) : Expr p → A
  | .roll (.lit n) => alg (.lit n)
  | .roll (.var i) => alg (.var i)
  | .roll (.letE v b) => alg (.letE (fold alg v) (fold alg b))
  | .roll (.all b) => alg (.all (fold alg b))
  | .roll (.array xs) => alg (.array (xs.map (fold alg)))
  | .roll (.sugar h b) => alg (.sugar h (fold alg b))
termination_by e => sizeOf e

/-- Zero is the newly bound variable; all older variables move one place. -/
def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

def renameAlg : Layer p ((Nat → Nat) → Expr p) → (Nat → Nat) → Expr p
  | .lit n, _ => .roll (.lit n)
  | .var i, ρ => .roll (.var (ρ i))
  | .letE v b, ρ => .roll (.letE (v ρ) (b (upRen ρ)))
  | .all b, ρ => .roll (.all (b (upRen ρ)))
  | .array xs, ρ => .roll (.array (xs.map (· ρ)))
  | .sugar h b, ρ => .roll (.sugar h (b ρ))

/-- Simultaneous renaming; under each binder it lifts the variable map. -/
def rename (ρ : Nat → Nat) (e : Expr p) : Expr p := fold renameAlg e ρ

/-- Increase free indices at or above cutoff, respecting nested binders. -/
def shift (amount cutoff : Nat) (e : Expr p) : Expr p :=
  rename (fun i => if i < cutoff then i else i + amount) e

/-- Lift an environment under a binder, shifting its images to avoid capture. -/
def upSub (σ : Nat → Expr p) : Nat → Expr p
  | 0 => .roll (.var 0)
  | i + 1 => rename Nat.succ (σ i)

def substAlg : Layer p ((Nat → Expr p) → Expr p) → (Nat → Expr p) → Expr p
  | .lit n, _ => .roll (.lit n)
  | .var i, σ => σ i
  | .letE v b, σ => .roll (.letE (v σ) (b (upSub σ)))
  | .all b, σ => .roll (.all (b (upSub σ)))
  | .array xs, σ => .roll (.array (xs.map (· σ)))
  | .sugar h b, σ => .roll (.sugar h (b σ))

/-- Total simultaneous substitution on raw indices, including ill-scoped inputs. -/
def subst (σ : Nat → Expr p) (e : Expr p) : Expr p := fold substAlg e σ

/-- Remove the outermost context entry, replacing its uses with value. -/
def substTop (value body : Expr p) : Expr p :=
  subst (fun | 0 => value | i + 1 => .roll (.var i)) body

/-- Extrinsic scope: no bound on depth, array length or index is sampled here. -/
inductive Scoped : Nat → Expr p → Prop where
  | lit : Scoped n (.roll (.lit value))
  | var : i < n → Scoped n (.roll (.var i))
  | letE : Scoped n value → Scoped (n + 1) body → Scoped n (.roll (.letE value body))
  | all : Scoped (n + 1) body → Scoped n (.roll (.all body))
  | array : (∀ e ∈ children, Scoped n e) → Scoped n (.roll (.array children))
  | sugar : Scoped n body → Scoped n (.roll (.sugar gate body))

theorem rename_scoped (he : Scoped n e) (hρ : ∀ i, i < n → ρ i < m) :
    Scoped m (rename ρ e) := by
  induction he generalizing m ρ with
  | lit => simpa only [rename, fold, renameAlg, subst, substAlg] using (Scoped.lit (n := m))
  | var h => simpa only [rename, fold, renameAlg] using Scoped.var (hρ _ h)
  | letE hv hb ihv ihb =>
    simp only [rename, fold, renameAlg]
    apply Scoped.letE (ihv hρ)
    apply ihb
    intro i hi
    cases i with
    | zero => simp [upRen]
    | succ i => simp only [upRen]; exact Nat.succ_lt_succ (hρ i (by omega))
  | all hb ih =>
    simp only [rename, fold, renameAlg]
    apply Scoped.all
    apply ih
    intro i hi
    cases i with
    | zero => simp [upRen]
    | succ i => simp only [upRen]; exact Nat.succ_lt_succ (hρ i (by omega))
  | array hs ih =>
    simp only [rename, fold, renameAlg]
    apply Scoped.array
    intro x hx
    simp only [Array.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    exact ih z hz hρ
  | sugar hb ih => simpa only [rename, fold, renameAlg] using Scoped.sugar (gate := _) (ih hρ)

theorem subst_scoped (he : Scoped n e) (hσ : ∀ i, i < n → Scoped m (σ i)) :
    Scoped m (subst σ e) := by
  induction he generalizing m σ with
  | lit => simpa only [rename, fold, renameAlg, subst, substAlg] using (Scoped.lit (n := m))
  | var h => simpa only [subst, fold, substAlg] using hσ _ h
  | letE hv hb ihv ihb =>
    simp only [subst, fold, substAlg]
    apply Scoped.letE (ihv hσ)
    apply ihb
    intro i hi
    cases i with
    | zero => exact .var (Nat.zero_lt_succ _)
    | succ i => exact rename_scoped (hσ i (by omega)) (by intro j hj; omega)
  | all hb ih =>
    simp only [subst, fold, substAlg]
    apply Scoped.all
    apply ih
    intro i hi
    cases i with
    | zero => exact .var (Nat.zero_lt_succ _)
    | succ i => exact rename_scoped (hσ i (by omega)) (by intro j hj; omega)
  | array hs ih =>
    simp only [subst, fold, substAlg]
    apply Scoped.array
    intro x hx
    simp only [Array.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    exact ih z hz hσ
  | sugar hb ih => simpa only [subst, fold, substAlg] using Scoped.sugar (gate := _) (ih hσ)

theorem scoped_mono (he : Scoped n e) (hnm : n ≤ m) : Scoped m e := by
  induction he generalizing m with
  | lit => exact .lit
  | var h => exact .var (Nat.lt_of_lt_of_le h hnm)
  | letE hv hb ihv ihb => exact .letE (ihv hnm) (ihb (by omega))
  | all hb ih => exact .all (ih (by omega))
  | array hs ih => exact .array (fun x hx => ih x hx hnm)
  | sugar hb ih => exact .sugar (ih hnm)

/-- Inserting a closed term at index zero preserves the remaining context. -/
theorem substTop_closed_scoped (hv : Scoped 0 value) (hb : Scoped (n + 1) body) :
    Scoped n (substTop value body) := by
  apply subst_scoped hb
  intro i hi
  cases i with
  | zero => exact scoped_mono hv (Nat.zero_le n)
  | succ i => exact .var (by omega)

/-- The executable scope predicate uses the same context increments as Scoped. -/
def scopeAlg : Layer p (Nat → Bool) → Nat → Bool
  | .lit _, _ => true
  | .var i, n => i < n
  | .letE v b, n => v n && b (n + 1)
  | .all b, n => b (n + 1)
  | .array xs, n => xs.all (· n)
  | .sugar _ b, n => b n

def scopeCheck (n : Nat) (e : Expr p) : Bool := fold scopeAlg e n

theorem scopeCheck_iff (n : Nat) (e : Expr p) : scopeCheck n e = true ↔ Scoped n e := by
  cases e with
  | roll layer =>
    cases layer with
    | lit v =>
      constructor
      · intro _; exact .lit
      · intro _; simp [scopeCheck, fold, scopeAlg]
    | var i =>
      simp only [scopeCheck, fold, scopeAlg, decide_eq_true_eq]
      constructor
      · exact Scoped.var
      · intro h; cases h; assumption
    | letE v b =>
      simp only [scopeCheck, fold, scopeAlg, Bool.and_eq_true]
      rw [← scopeCheck, ← scopeCheck, scopeCheck_iff, scopeCheck_iff]
      constructor
      · rintro ⟨hv, hb⟩; exact .letE hv hb
      · intro h; cases h; exact ⟨by assumption, by assumption⟩
    | all b =>
      simp only [scopeCheck, fold, scopeAlg]
      rw [← scopeCheck, scopeCheck_iff]
      constructor
      · exact Scoped.all
      · intro h; cases h; assumption
    | array xs =>
      simp only [scopeCheck, fold, scopeAlg, Array.all_eq_true_iff_forall_mem, Array.mem_map]
      constructor
      · intro h
        apply Scoped.array
        intro x hx
        exact (scopeCheck_iff n x).mp (h _ ⟨x, hx, rfl⟩)
      · intro h f hf
        obtain ⟨x, hx, rfl⟩ := hf
        cases h with
        | array hs => exact (scopeCheck_iff n x).mpr (hs x hx)
    | sugar gate b =>
      simp only [scopeCheck, fold, scopeAlg]
      rw [← scopeCheck, scopeCheck_iff]
      constructor
      · exact Scoped.sugar
      · intro h; cases h; assumption
termination_by sizeOf e

end ExprPrototype
