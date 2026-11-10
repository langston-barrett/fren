import Fren.Impl
import Spec.Compiler.Lir

/-! The production sort checker `FrenLir.Term.infer` and the declarative
judgment `Sorted` of `lir.terms.sorts` (rule `lir.terms.checker`). -/

open Fren.Lang

namespace Spec.Compiler.Lir
open FrenModule FrenAst FrenLir

/-- A successful `mapM` in `Option` is pointwise success, in order. -/
theorem mapM_eq_some_map {α β γ : Type} (f : α → Option β) (g : γ → β) (as : List α) (ps : List γ) :
    as.mapM f = some (ps.map g) ↔
      as.length = ps.length ∧ ∀ (i : Nat) a p, as[i]? = some a → ps[i]? = some p → f a = some (g p) := by
  induction as generalizing ps with
  | nil => cases ps <;> simp
  | cons a as ih =>
    cases ps with
    | nil => cases fa : f a <;> cases rest : as.mapM f <;> simp [List.mapM_cons, fa, rest]
    | cons p ps =>
      simp only [List.mapM_cons, List.map_cons, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · intro h
        cases fa : f a with
        | none => simp [fa] at h
        | some b =>
          cases rest : as.mapM f with
          | none => simp [fa, rest] at h
          | some bs =>
            simp only [fa, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, List.cons.injEq] at h
            obtain ⟨length, each⟩ := (ih ps).mp (h.2 ▸ rest)
            refine ⟨length, fun i x y hx hy => ?_⟩
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
              rw [← hx, ← hy, fa, h.1]
            | succ i => exact each i x y (by simpa using hx) (by simpa using hy)
      · rintro ⟨length, each⟩
        have head := each 0 a p rfl rfl
        have tail := (ih ps).mpr ⟨length, fun i x y hx hy => each (i + 1) x y (by simpa using hx) (by simpa using hy)⟩
        simp [head, tail]

/-- Pointwise eventual facts over paired lists have one common bound. -/
theorem common_bound {α β : Type} (holds : Nat → α → β → Prop) (as : List α) (bs : List β)
    (each : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → ∃ n, ∀ m, n ≤ m → holds m a b) :
    ∃ n, ∀ m, n ≤ m → ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → holds m a b := by
  induction as generalizing bs with
  | nil => exact ⟨0, fun _ _ i a b ha => by simp at ha⟩
  | cons a as ih =>
    cases bs with
    | nil => exact ⟨0, fun _ _ i a b _ hb => by simp at hb⟩
    | cons b bs =>
      obtain ⟨first, head⟩ := each 0 a b rfl rfl
      obtain ⟨rest, tail⟩ := ih bs fun i x y hx hy => each (i + 1) x y (by simpa using hx) (by simpa using hy)
      refine ⟨max first rest, fun m bound i x y hx hy => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
        exact hx ▸ hy ▸ head m (Nat.le_trans (Nat.le_max_left ..) bound)
      | succ i =>
        exact tail m (Nat.le_trans (Nat.le_max_right ..) bound) i x y (by simpa using hx) (by simpa using hy)

/-- Soundness: every sort that the checker returns, at any depth bound, is derivable. -/
--@ reference: lir.terms.checker
theorem infer_sorted (n : Nat) (s : Typed) (ctx : TypeContext) (term : Term) (ty : FrenExpr.Ty)
    (h : Term.infer n s ctx term = some ty) : Sorted s ctx term ty := by
  induction n generalizing ctx term ty with
  | zero => simp [Term.infer] at h
  | succ n ih =>
    rw [Term.infer.eq_def] at h
    cases term with
    | bool b => cases h; exact .bool
    | int v => cases h; exact .int
    | constructor owner id =>
      simp only at h
      split at h
      · rename_i valid
        cases h
        exact .constructor (by simpa [FrenEval.Value.valid] using valid)
      · contradiction
    | «local» sort i component =>
      simp only at h
      split at h
      · contradiction
      · rename_i slot
        cases h
        exact .local (by simpa using slot)
    | unary op a =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ta, ha, hop⟩ := h
      exact .unary (ih _ _ _ ha) hop
    | binary op a b =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ta, ha, tb, hb, hop⟩ := h
      exact .binary (ih _ _ _ ha) (ih _ _ _ hb) hop
    | ite c a b =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨tc, hc, h⟩ := h
      split at h
      · contradiction
      · rename_i condition
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨ta, ha, tb, hb, h⟩ := h
        split at h
        · rename_i same
          have hc' : tc = .bool := by simpa using condition
          have hb' : tb = ta := by simpa using same
          cases h
          exact .ite (hc' ▸ ih _ _ _ hc) (ih _ _ _ ha) (hb' ▸ ih _ _ _ hb)
        · contradiction
    | app sig component args =>
      simp only at h
      split at h
      · contradiction
      · rename_i present
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨sorts, hargs, h⟩ := h
        split at h
        · contradiction
        · rename_i same
          cases h
          have same : sorts = sig.parameters.toList.map (·.type) := by simpa using same
          obtain ⟨length, each⟩ := (mapM_eq_some_map _ _ _ _).mp (same ▸ hargs)
          refine .app (by simpa using present) (by simpa using length) fun i a param ha hp => ?_
          exact ih _ _ _ (each i a param ha (by simpa using hp))
    | letE binder sort value domain body =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨tv, hv, td, hd, h⟩ := h
      split at h
      · contradiction
      · rename_i sorts
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at sorts
        exact .letE (sorts.1 ▸ ih _ _ _ hv) (sorts.2 ▸ ih _ _ _ hd) (ih _ _ _ h)
    | «at» origin value =>
      simp only at h
      split at h
      · contradiction
      · rename_i context
        exact .at (by simpa using context) (ih _ _ _ h)

/-- Completeness up to depth: a derivable sort is returned at every large enough bound. -/
--@ reference: lir.terms.checker
theorem sorted_infer (s : Typed) (ctx : TypeContext) (term : Term) (ty : FrenExpr.Ty)
    (h : Sorted s ctx term ty) : ∃ n, ∀ m, n ≤ m → Term.infer m s ctx term = some ty := by
  induction h with
  | bool => exact ⟨1, fun m bound => by obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩; rfl⟩
  | int => exact ⟨1, fun m bound => by obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩; rfl⟩
  | constructor valid =>
    refine ⟨1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Term.infer.eq_def]
    simp only
    rw [if_pos (by simpa [FrenEval.Value.valid] using valid)]
  | «local» slot =>
    refine ⟨1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Term.infer.eq_def]
    simp [slot]
  | unary _ hop ih =>
    obtain ⟨n, ih⟩ := ih
    refine ⟨n + 1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Term.infer.eq_def]
    simp [ih m (by omega), hop]
  | binary _ _ hop iha ihb =>
    obtain ⟨na, iha⟩ := iha
    obtain ⟨nb, ihb⟩ := ihb
    refine ⟨max na nb + 1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Term.infer.eq_def]
    simp [iha m (by omega), ihb m (by omega), hop]
  | ite _ _ _ ihc iha ihb =>
    obtain ⟨nc, ihc⟩ := ihc
    obtain ⟨na, iha⟩ := iha
    obtain ⟨nb, ihb⟩ := ihb
    refine ⟨max nc (max na nb) + 1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Term.infer.eq_def]
    simp [ihc m (by omega), iha m (by omega), ihb m (by omega)]
  | @app sig args ctx component present length _ ih =>
    obtain ⟨n, ih⟩ := common_bound (fun m a (param : TypedParameter) => Term.infer m s ctx a = some param.type)
      args sig.parameters.toList (fun i a param ha hp => ih i a param ha (by simpa using hp))
    refine ⟨n + 1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hargs := (mapM_eq_some_map (Term.infer m s ctx) (·.type) args sig.parameters.toList).mpr
      ⟨by simpa using length, ih m (by omega)⟩
    rw [Term.infer.eq_def]
    simp [hargs, show sig ∈ s.signatures by simpa using present]
  | letE _ _ _ ihv ihd ihb =>
    obtain ⟨nv, ihv⟩ := ihv
    obtain ⟨nd, ihd⟩ := ihd
    obtain ⟨nb, ihb⟩ := ihb
    refine ⟨max nv (max nd nb) + 1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Term.infer.eq_def]
    simp [ihv m (by omega), ihd m (by omega), ihb m (by omega)]
  | «at» context _ ih =>
    obtain ⟨n, ih⟩ := ih
    refine ⟨n + 1, fun m bound => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Term.infer.eq_def]
    simp [ih m (by omega), context]

/-- The checker decides the judgment up to its depth bound. -/
--@ reference: lir.terms.checker
theorem sorted_iff_infer (s : Typed) (ctx : TypeContext) (term : Term) (ty : FrenExpr.Ty) :
    Sorted s ctx term ty ↔ ∃ n, Term.infer n s ctx term = some ty :=
  ⟨fun h => (sorted_infer s ctx term ty h).imp fun n all => all n (Nat.le_refl n),
    fun ⟨n, h⟩ => infer_sorted n s ctx term ty h⟩

/-- A term has at most one sort in a context. -/
--@ reference: lir.terms.checker
theorem sorted_unique (s : Typed) (ctx : TypeContext) (term : Term) (a b : FrenExpr.Ty)
    (ha : Sorted s ctx term a) (hb : Sorted s ctx term b) : a = b := by
  obtain ⟨na, ha⟩ := sorted_infer s ctx term a ha
  obtain ⟨nb, hb⟩ := sorted_infer s ctx term b hb
  have ha := ha (max na nb) (Nat.le_max_left ..)
  rw [hb (max na nb) (Nat.le_max_right ..)] at ha
  exact (Option.some.inj ha).symm

/-- A body that passes the production certificate has both sorting derivations of `BodyFor`. -/
theorem wellSorted_sorted (s : Typed) (b : Body) (h : b.wellSorted s = true) :
    Sorted s b.source.context b.term.value b.source.type ∧
      Sorted s b.source.context b.term.defined .bool := by
  simp only [Body.wellSorted, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨infer_sorted _ _ _ _ _ h.1.2, infer_sorted _ _ _ _ _ h.2⟩

/-- The production certificate covers every root body. -/
theorem wellFormed_root (out : Program) (h : out.wellFormed = true) (b : Body) (root : Root out b) :
    b.wellSorted out.mir.source = true := by
  simp only [Program.wellFormed, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨⟨-, declarations⟩, -⟩, requests⟩ := h
  rcases root with ⟨sig, member⟩ | ⟨source, members, member, inside⟩ | ⟨r, member, inside⟩
  · exact declarations _ (Array.mem_toList_iff.mp member)
  · have block := declarations _ (Array.mem_toList_iff.mp member)
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at block
    exact block.2 b (Array.mem_toList_iff.mp inside)
  · have request := requests r (Array.mem_toList_iff.mp member)
    simp only [Array.mem_append] at request
    rcases inside with assumption | demand | question
    · exact request.1.2 b (.inl (Array.mem_toList_iff.mp assumption))
    · exact request.1.2 b (.inr (Array.mem_toList_iff.mp demand))
    · have goal := request.2
      rw [question] at goal
      exact goal

/-- Every root body of a successful production is sorted at its retained source
sort, and its definedness summary at `Bool`. -/
--@ reference: lir.terms.checker
theorem produced_sorted (p : Input) (out : Program) (h : Produces p out) (b : Body) (root : Root out b) :
    Sorted out.mir.source b.source.context b.term.value b.source.type ∧
      Sorted out.mir.source b.source.context b.term.defined .bool :=
  wellSorted_sorted _ b (wellFormed_root out (FrenFlatToLir.wellFormed p out h) b root)

/-- The checker sorts a constructor term exactly when its enum value is valid. -/
theorem infer_constructor (n : Nat) (s : Typed) (ctx : TypeContext) (owner c : FrenBase.ItemId) :
    (Term.infer (n + 1) s ctx (.constructor owner c) == some (.enum owner)) =
      FrenEval.Value.valid s (.enum owner c) := by
  rw [Term.infer.eq_def]
  simp only [FrenEval.Value.valid]
  split
  · rename_i h; rw [h]; exact beq_self_eq_true _
  · rename_i h; rw [Bool.not_eq_true] at h; rw [h]; rfl

--@ reference: lir.terms.constructors
impl constructor_sort: spec::lir::constructor_sort
    for (s : Typed) (ctx : TypeContext) (owner c : FrenBase.ItemId) (n : Nat) {
  valid? := FrenEval.Value.valid s (.enum owner c),
  sorted? := Term.infer (n + 1) s ctx (.constructor owner c) == some (.enum owner)
} by
  intro s ctx owner c n _
  simp [fren_spec, infer_constructor]

#print axioms infer_sorted
#print axioms sorted_infer
#print axioms sorted_unique
#print axioms produced_sorted

end Spec.Compiler.Lir
