-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.PatternTypes
import FrenCore.Quantifier
-- keep-sorted end

/-!
# Quantifiers over a sequence's elements (`Reqs/Lang/ElementQuantifiers`)

`forall (x: T), when x in q, P(x)` and `exists (x: T), x in q and P(x)`,
with `q` a sequence, are in the decidable core when `x` is used in `P`
only as a value: they are then in the *array property fragment* of
Bradley, Manna and Sipma ("What's decidable about arrays?", VMCAI 2006),
and both front ends instantiate them, at each query, over the fragment's
index set, so that the query stays quantifier-free.

This holds what both front ends share: which quantifiers are recognized
(`elementVerdict`), the index set (`indexSet`), the instances' tuples
(`elementTuples`), the limit on their number, the messages, and the
projection (`project`) by which a model of the instantiated query is made
a model of the quantified one, which is the fragment's completeness.
-/

namespace Fren.Core

/-! ## Recognition (`lang::element_quantifier`) -/

/-- How the body of a quantifier mentions its bound name `x`, at one place
(`lang::ElementUse`). -/
inductive ElementUse where
  /-- As a value: an operand, an argument, a scrutinee, a field read from it. -/
  | value
  /-- In the position of an index, or of an `update`, of a sequence that is
  not a constant. -/
  | index
  /-- In an argument of a function with a parameter whose type has a
  sequence within it. -/
  | seqArgument
  /-- In the members of the guard of a quantifier within the body. -/
  | receiver
  /-- In an argument of an application of an uninterpreted function that
  brings facts: a `Nat` or a pattern type as its result, or a contract. -/
  | factArgument
  /-- In an argument of a defined function whose body has a quantifier over
  a type that is not listed, directly or through another: once the body is
  unfolded, that quantifier is within this one. -/
  | quantifiedArgument
  deriving Inhabited, DecidableEq, Repr

/-- What a bound name's domain is (`lang::ElementMembers`). -/
inductive ElementMembers where
  /-- The members of a sequence, by a conjunct `x in q`. -/
  | seq
  /-- The members of a set or a relation. -/
  | set
  /-- None: a range, or no domain. -/
  | none
  deriving Inhabited, DecidableEq, Repr

/-- What both front ends see of a bound name of a type that is not listed
(`lang::ElementBinder`). -/
structure ElementBinder where
  members : ElementMembers
  /-- The members' expression mentions an earlier bound name of the same
  quantifier, or one of an enclosing quantifier of a type that is not
  listed. -/
  receiverBound : Bool
  /-- How the body mentions it. -/
  uses : List ElementUse
  deriving Inhabited, BEq, Repr

/-- Where a quantifier is, among the quantifiers over elements around it
(`lang::ElementNesting`). -/
inductive ElementNesting where
  /-- Within none. -/
  | top
  /-- The body of one of the same kind: a `forall`'s under its `when`s, or
  the last conjunct of an `exists`'s. -/
  | direct
  /-- Anywhere else within one. -/
  | other
  deriving Inhabited, DecidableEq, Repr

/-- Whether a quantifier over elements is in the decidable core, or why
not (`lang::ElementVerdict`). -/
inductive ElementVerdict where
  | inCore
  /-- Some bound name has no members as its domain: #259's unbounded
  quantifier. -/
  | notMembers
  | setMembers
  | receiverBound
  /-- Its sequence or its body mentions an output that is not defined,
  which the realizability check quantifies over. -/
  | mentionsOutput
  /-- Its body mentions a bound name of a quantifier around it, other than
  of those of the same kind that it is directly the body of. -/
  | mentionsBound
  | used (u : ElementUse)
  | nested
  deriving Inhabited, DecidableEq, Repr

/-- The expressions of each conjunct of a guard `e`, split as
`splitConjuncts` splits it, so that the `k`th is the `k`th conjunct's: a
comparison's two operands, or the whole of any other conjunct. -/
partial def splitParts (view : α → GuardNode α) (e : α) : Array (Array α) :=
  match view e with
  | .conj a b => splitParts view a ++ splitParts view b
  | .compare xs ops => ops.zipIdx.map fun (_, i) => #[xs[i]?, xs[i + 1]?].filterMap id
  | .other => #[#[e]]

/-- The expressions of the conjuncts of a quantifier's guard
(`guardConjunctsBy`), each as `splitParts` gives them: a bound name's
membership is its first mention when no earlier conjunct names it. -/
partial def guardPartsBy (view : α → GuardNode α) (when? : α → Option (α × α)) (all : Bool) (body : α) :
    Array (Array α) :=
  if all then
    match when? body with
    | some (c, d) => splitParts view c ++ guardPartsBy view when? all d
    | none => #[]
  else splitParts view body

/-- Whether a value of type `t` has a sequence within it, by the shapes of
the declarations that `shapeOf` gives: it is one, or a set, relation,
newtype, record or enumeration with one within, to a depth of `fuel`,
beyond which it is taken to have one. A function with a parameter of such a
type may use another argument as an index of it (`ElementUse.seqArgument`). -/
def hasSeqWithin (shapeOf : Lean.Name → Option DataShape) : Nat → Ty → Bool
  | 0, _ => true
  | _, .seq _ => true
  | n + 1, .set t => hasSeqWithin shapeOf n t
  | n + 1, .rel a b => hasSeqWithin shapeOf n a || hasSeqWithin shapeOf n b
  | n + 1, .newtype _ u => hasSeqWithin shapeOf n u
  | n + 1, .enum p args | n + 1, .record p args =>
    args.any (hasSeqWithin shapeOf n) || (shapeOf p).any fun d => d.parts.any (·.any (hasSeqWithin shapeOf n ·.ty))
  | _, _ => false

/-- Whether the verdict is `inCore`. -/
def ElementVerdict.isInCore : ElementVerdict → Bool
  | .inCore => true
  | _ => false

/-- The uses that keep a quantifier out of the core, in the order in which
they are reported. -/
def ElementUse.outside : List ElementUse := [.index, .seqArgument, .receiver, .factArgument, .quantifiedArgument]

/-- The verdict of one bound name (`lang::binder_verdict`). -/
def ElementBinder.verdict (b : ElementBinder) : ElementVerdict :=
  match b.members with
  | .none => .notMembers
  | .set => .setMembers
  | .seq =>
    if b.receiverBound then .receiverBound
    else match ElementUse.outside.find? (fun u => decide (u ∈ b.uses)) with
      | some u => .used u
      | none => .inCore

/-- Whether a quantifier with the bound names `bs` of types that are not
listed, in order, at `nesting`, is in the decidable core, or the first
reason that it is not: its first bound name's that is not; else that it
mentions an output (`output`); else its nesting; else that it mentions a
bound name of a quantifier around it other than of those that it is
directly the body of (`bound`) (`lang::element_quantifier`). Both front ends decide by it. -/
def elementVerdict (nesting : ElementNesting) (output bound : Bool) (bs : List ElementBinder) : ElementVerdict :=
  match bs.find? (!·.verdict.isInCore) with
  | some b => b.verdict
  | none =>
    if output then .mentionsOutput
    else match nesting with
      | .other => .nested
      | _ => if bound then .mentionsBound else .inCore

/-- Why a quantifier over elements is outside the core (`F0714`), unless it
is #259's unbounded quantifier, whose message is `undecidableMsg`. -/
def elementUndecidableMsg : ElementVerdict → Option Msg
  | .inCore | .notMembers => none
  | v =>
    let (why, help) : String × String := match v with
      | .setMembers => ("a quantifier over a set's members is given to the solver, which decides sets with `card` only without quantifiers",
          "help: quantify over a sequence's elements, or over a listed type, or opt out")
      | .receiverBound => ("its members' sequence mentions a bound name, so the solver would quantify over sequences' elements within each other",
          "help: quantify over a sequence that mentions no bound name")
      | .mentionsOutput => ("it mentions an output, which the realizability check quantifies over, so the quantifiers would alternate",
          "help: mention the inputs that the output depends on instead, or define the output")
      | .mentionsBound => ("its body mentions a bound name of a quantifier around it, so its witness would depend on that name",
          "help: bind both names in one quantifier over elements, or make it directly the body of the other")
      | .used .quantifiedArgument => ("its bound name is an argument of a function with a quantifier within it, which would be nested in this one",
          "help: state the function's quantifier here, as directly the body of this one, or opt out")
      | .used .index => ("its bound name is used as an index, which is outside the array property fragment",
          "help: use the element only as a value, or quantify over the positions and opt out")
      | .used .seqArgument => ("its bound name is an argument of a function of a sequence, which may use it as an index",
          "help: use the element only as a value")
      | .used .receiver => ("its bound name is the sequence of a quantifier within it, which nests quantifiers over elements",
          "help: quantify over the elements of a sequence that is not the bound name")
      | .used .factArgument => ("its bound name is an argument of a function whose applications bring facts, which the solver would state for every element",
          "help: use a function without a `Nat` or pattern-type result or a contract, or opt out")
      | _ => ("a quantifier over elements within another, other than as the body of one of the same kind, alternates quantifiers",
          "help: write the inner quantifier as the body of the outer, or bind both names in one quantifier")
    some { code? := some "F0714", headline := s!"this is outside the decidable core: {why}"
           label? := some "outside the decidable core", notes := #[help] }

/-! ## The index set (`lang::index_set`) -/

/-- Where the terms of a query's index set come from (`lang::IndexSources`):
the position `0`, the last position of each quantifier's sequence, each
index read in the query, each position of an `update` with its
neighbours, and each witness: a fresh name for each bound name of each
quantifier, and for each equation between sequences of which one is a
quantifier's. -/
structure IndexSources (τ : Type) where
  zero : τ
  lasts : List τ
  reads : List τ
  /-- Each update's position less one, itself and plus one. -/
  updates : List (τ × τ × τ)
  witnesses : List τ
  deriving Inhabited

/-- The terms, in order, before those equal to an earlier one are removed. -/
def IndexSources.candidates (s : IndexSources τ) : List τ :=
  s.zero :: s.lasts ++ s.reads ++ s.updates.flatMap (fun u => [u.1, u.2.1, u.2.2]) ++ s.witnesses

/-- `acc` followed by the terms of `ts` that are neither in `acc` nor equal
to an earlier one. -/
def firstOccurrences [BEq τ] (acc : List τ) : List τ → List τ
  | [] => acc
  | t :: ts => firstOccurrences (if acc.contains t then acc else acc ++ [t]) ts

/-- The index set: the candidates, each once, in the order of their first
occurrence (`lang::index_set`). -/
def indexSet [BEq τ] (s : IndexSources τ) : List τ := firstOccurrences [] s.candidates

theorem mem_firstOccurrences [BEq τ] [LawfulBEq τ] (acc ts : List τ) (t : τ) :
    t ∈ firstOccurrences acc ts ↔ t ∈ acc ∨ t ∈ ts := by
  induction ts generalizing acc with
  | nil => simp [firstOccurrences]
  | cons u us ih =>
    simp only [firstOccurrences, ih, List.mem_cons]
    split
    · rename_i h
      have : u ∈ acc := by simpa using h
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl this
        · exact .inr h
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | rfl) | h)
        · exact .inl h
        · exact .inr (.inl rfl)
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inl h)
        · exact .inl (.inr rfl)
        · exact .inr h

theorem nodup_firstOccurrences [BEq τ] [LawfulBEq τ] (acc ts : List τ) (h : acc.Nodup) :
    (firstOccurrences acc ts).Nodup := by
  induction ts generalizing acc with
  | nil => simpa [firstOccurrences]
  | cons u us ih =>
    simp only [firstOccurrences]
    split
    · exact ih _ h
    · rename_i hu
      apply ih
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro e
      subst e
      simp_all

theorem firstOccurrences_prefix [BEq τ] (acc ts : List τ) : ∃ r, firstOccurrences acc ts = acc ++ r := by
  induction ts generalizing acc with
  | nil => exact ⟨[], by simp [firstOccurrences]⟩
  | cons u us ih =>
    simp only [firstOccurrences]
    split
    · exact ih acc
    · obtain ⟨r, hr⟩ := ih (acc ++ [u])
      exact ⟨[u] ++ r, by simp [hr]⟩

/-- The index set has every candidate, and nothing else. -/
theorem mem_indexSet [BEq τ] [LawfulBEq τ] (s : IndexSources τ) (t : τ) : t ∈ indexSet s ↔ t ∈ s.candidates := by
  simp [indexSet, mem_firstOccurrences]

/-- The index set has no term twice. -/
theorem nodup_indexSet [BEq τ] [LawfulBEq τ] (s : IndexSources τ) : (indexSet s).Nodup :=
  nodup_firstOccurrences [] _ List.nodup_nil

/-- The index set starts with `0`. -/
theorem indexSet_head [BEq τ] (s : IndexSources τ) : ∃ r, indexSet s = s.zero :: r := by
  obtain ⟨r, hr⟩ := firstOccurrences_prefix [s.zero] (s.lasts ++ s.reads ++ s.updates.flatMap (fun u => [u.1, u.2.1, u.2.2]) ++ s.witnesses)
  refine ⟨r, ?_⟩
  simp only [indexSet, IndexSources.candidates, firstOccurrences, List.contains_nil, Bool.false_eq_true, ite_false,
    List.nil_append, List.cons_append, List.append_assoc] at hr ⊢
  simpa using hr

/-- The instances' tuples of a quantifier of `n` bound names over the index
set `ts`: every combination, the last name varying fastest, as a
quantifier over listed types orders its instances. -/
def elementTuples (ts : List τ) : Nat → List (List τ)
  | 0 => [[]]
  | n + 1 => (elementTuples ts n).flatMap fun pre => ts.map (pre ++ [·])

/-! ## The quantifiers that a query expands (`lang::site_expanded`) -/

/-- A binder around a marked quantifier in a query, outermost first
(`lang::Frame`): a marked quantifier that is expanded, whether it is a
`forall`, and whether what is within it is on its *spine*, where it has the
quantifier's polarity: the consequent of an implication or a conjunct; or
any other binder: the solver's quantifier, the realizability check's `∃`
over outputs, a marked quantifier that is not expanded. -/
inductive Frame where
  | element (all spine : Bool)
  | other
  deriving Inhabited, DecidableEq, Repr

/-- Whether the frames from position `j` to the innermost are a chain of
expanded quantifiers of the kind `all`, each with what is within it on its
spine (`lang::in_chain?`). -/
def inChain (frames : List Frame) (all : Bool) (j : Nat) : Bool :=
  (frames.drop j).all (· == .element all true)

/-- Whether a marked quantifier, a `forall` if `all`, within `frames`, is
expanded (`lang::site_expanded`): its sequences mention no name bound
around it (`receiversClosed`), and every frame whose names its body
mentions, by position, is in the chain of quantifiers of its kind that it is
directly within. Its witnesses are then fresh names of the whole query: no
name that its value could depend on is bound around it, but those of that
chain, whose instances share them soundly. Otherwise the solver is given
the quantifier as written. Both front ends decide by it. -/
def siteExpanded (frames : List Frame) (all receiversClosed : Bool) (mentioned : List Nat) : Bool :=
  receiversClosed && mentioned.all fun j => j < frames.length && inChain frames all j

/-- The per-quantifier law of the expansion: a quantifier over the
positions of `q` holds exactly when its instances hold at the terms `ix`
and at every value of a witness `w`. So, since a witness is a fresh name of
the query, the instances at `w :: ix` hold in some interpretation of `w`
exactly where they do in all, and exactly where the quantifier does, when
`w` is taken to be a position where it fails, if there is one. -/
theorem all_iff_instances (q : List α) (p : α → Prop) (ix : List Int) :
    (∀ x ∈ q, p x) ↔ ∀ w : Int, ∀ t ∈ w :: ix, (h : 0 ≤ t ∧ t < q.length) → p (q[t.toNat]'(by omega)) := by
  constructor
  · intro h w t _ ht
    exact h _ (List.getElem_mem _)
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := h i i (List.mem_cons_self) ⟨by omega, by omega⟩
    simpa using this

/-! ## The size of the expansion (`lang::element_size`) -/

/-- The most instances that a query's quantifiers over elements may have
(`lang::MAX_ELEMENT_INSTANCES`). -/
def maxElementInstances : Nat := 256

/-- Whether a query whose quantifiers over elements have `n` instances in
all is asked (`lang::element_size`). -/
def elementSizeAccepted (n : Nat) : Bool := n ≤ maxElementInstances

/-- The instances of quantifiers of `arities` bound names each, over an
index set of `terms` terms. -/
def elementInstances (terms : Nat) (arities : List Nat) : Nat := (arities.map (terms ^ ·)).sum

/-- The reason of an inconclusive check whose query's expansion reached `n`
instances, more than `maxElementInstances` (`F0647`), as both backends
answer it: the expansion stops there, so `n` is not shown. -/
def elementLimitReason (_n : Nat) : String :=
  s!"its quantifiers over sequences' elements would have more than {maxElementInstances} instances"

/-- The reason of an inconclusive check whose model, with its sequences'
lengths pinned, the quantifiers over their elements refute (`F0648`). -/
def elementUnconfirmedReason : String :=
  "the solver's model does not satisfy the quantifiers over sequences' elements, and none does with the same lengths"

/-- The message of an inconclusive check whose reason is one of those
above, if it is: its code and notes. -/
def elementReasonNotes? (reason : String) : Option (String × Array String) :=
  if reason == elementLimitReason 0 then
    some ("F0647", #[s!"note: a quantifier over a sequence's elements is instantiated at each term of the query's index set, at most {maxElementInstances} instances in all",
      "help: bind fewer names in one quantifier, or read fewer positions of its sequence where the check uses it"])
  else if reason == elementUnconfirmedReason then
    some ("F0648", #["note: the instances at the index set do not hold of every element of the solver's model, and no model has every element satisfy them at the same lengths",
      "help: state the property by the elements, within the decidable core, or check it by testing"])
  else none

/-! ## Completeness: the projection (`lang::element_projection`)

A model of the instantiated query is made a model of the quantified one by
replacing each element of each sequence by the element at the last value
of the index set at or before its position. Reads at the index set, and
lengths, do not change, so neither does the rest of the query; an update
at a position whose successor is in the index set commutes with it; and
every element is then one at which an instance holds. -/

/-- The last value of `ix` at or before `j`, or `0` if there is none. -/
def projAt (ix : List Int) (j : Int) : Int := ix.foldl (fun m t => if t ≤ j ∧ m < t then t else m) 0

/-- `q` projected onto `ix`: each element replaced by the element at
`projAt ix` of its position. -/
def project (ix : List Int) (q : List α) : List α :=
  q.zipIdx.map fun (x, j) => q.getD (projAt ix j).toNat x

theorem projAt_fold (ix : List Int) (j m : Int) :
    (0 ≤ m → m ≤ j → 0 ≤ ix.foldl (fun m t => if t ≤ j ∧ m < t then t else m) m ∧
      ix.foldl (fun m t => if t ≤ j ∧ m < t then t else m) m ≤ j) ∧
    (m ≤ ix.foldl (fun m t => if t ≤ j ∧ m < t then t else m) m) ∧
    (∀ t ∈ ix, t ≤ j → t ≤ ix.foldl (fun m t => if t ≤ j ∧ m < t then t else m) m) ∧
    (ix.foldl (fun m t => if t ≤ j ∧ m < t then t else m) m = m ∨
      ix.foldl (fun m t => if t ≤ j ∧ m < t then t else m) m ∈ ix) := by
  induction ix generalizing m with
  | nil => exact ⟨fun a b => ⟨a, b⟩, Int.le_refl _, by simp, .inl rfl⟩
  | cons t ts ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    by_cases h : t ≤ j ∧ m < t
    · simp only [h, and_self, ite_true]
      obtain ⟨h1, h2, h3, h4⟩ := ih t
      refine ⟨fun hm _ => h1 (by omega) h.1, by omega, ⟨fun _ => h2, h3⟩, ?_⟩
      rcases h4 with h4 | h4
      · exact .inr (.inl h4)
      · exact .inr (.inr h4)
    · simp only [h, ite_false]
      obtain ⟨h1, h2, h3, h4⟩ := ih m
      refine ⟨h1, h2, ⟨fun ht => ?_, h3⟩, ?_⟩
      · have : ¬ m < t := fun hmt => h ⟨ht, hmt⟩
        omega
      · rcases h4 with h4 | h4
        · exact .inl h4
        · exact .inr (.inr h4)

/-- `projAt ix j` is a position at or before `j`, at least `0`, of `ix` or
`0` itself, and no value of `ix` at or before `j` is after it. -/
theorem projAt_spec (ix : List Int) (j : Int) (hj : 0 ≤ j) :
    0 ≤ projAt ix j ∧ projAt ix j ≤ j ∧ (∀ t ∈ ix, t ≤ j → t ≤ projAt ix j) ∧
      (projAt ix j = 0 ∨ projAt ix j ∈ ix) := by
  obtain ⟨h1, _, h3, h4⟩ := projAt_fold ix j 0
  exact ⟨(h1 (by omega) hj).1, (h1 (by omega) hj).2, h3, h4⟩

theorem projAt_self (ix : List Int) (t : Int) (ht : t ∈ ix) (h0 : 0 ≤ t) : projAt ix t = t := by
  obtain ⟨_, h2, h3, _⟩ := projAt_spec ix t h0
  have := h3 t ht (Int.le_refl t)
  omega

@[simp] theorem project_length (ix : List Int) (q : List α) : (project ix q).length = q.length := by
  simp [project]

theorem project_getElem (ix : List Int) (q : List α) (j : Nat) (h : j < (project ix q).length) :
    (project ix q)[j] = q[(projAt ix j).toNat]'(by
      have := (projAt_spec ix j (by omega)).2.1; simp at h; omega) := by
  have := (projAt_spec ix j (by omega)).2.1
  simp only [project_length] at h
  simp only [project, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- Reads at the index set do not change. -/
theorem project_read (ix : List Int) (q : List α) (t : Nat) (ht : (t : Int) ∈ ix) (h : t < q.length) :
    (project ix q)[t]'(by simpa using h) = q[t] := by
  rw [project_getElem]
  simp [projAt_self ix t ht (by omega)]

/-- Every element of the projection is an element of `q` at a value of the
index set, if `0` is one. -/
theorem project_mem (ix : List Int) (q : List α) (h0 : (0 : Int) ∈ ix) (x : α) (hx : x ∈ project ix q) :
    ∃ t : Nat, (t : Int) ∈ ix ∧ ∃ h : t < q.length, q[t] = x := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  rw [project_getElem]
  obtain ⟨p0, p1, _, p3⟩ := projAt_spec ix j (by omega)
  simp only [project_length] at hj
  refine ⟨(projAt ix j).toNat, ?_, by omega, rfl⟩
  rcases p3 with p3 | p3
  · rw [p3]; simpa using h0
  · rwa [Int.toNat_of_nonneg p0]

/-- If the body holds at each element at the index set, it holds at every
element of the projection. -/
theorem project_all (ix : List Int) (q : List α) (p : α → Prop) (h0 : (0 : Int) ∈ ix)
    (hI : ∀ t : Nat, (t : Int) ∈ ix → (h : t < q.length) → p q[t]) : ∀ x ∈ project ix q, p x := by
  intro x hx
  obtain ⟨t, ht, hlt, rfl⟩ := project_mem ix q h0 x hx
  exact hI t ht hlt

/-- An update at a position whose successor, and itself, are in the index
set commutes with the projection. -/
theorem project_set (ix : List Int) (q : List α) (i : Nat) (v : α) (hi : (i : Int) ∈ ix)
    (hs : (i : Int) + 1 ∈ ix) : project ix (q.set i v) = (project ix q).set i v := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_set, project_length] at h1
  obtain ⟨p0, p1, p2, _⟩ := projAt_spec ix j (by omega)
  rw [project_getElem, List.getElem_set, List.getElem_set]
  by_cases hj : i = j
  · subst hj
    simp [projAt_self ix i hi (by omega)]
  · have : i ≠ (projAt ix j).toNat := by
      intro he
      have hlt : (i : Int) + 1 ≤ j := by omega
      have := p2 _ hs hlt
      omega
    rw [if_neg this, if_neg hj, project_getElem]

/-- A difference at a value of the index set survives the projection. -/
theorem project_ne (ix : List Int) (q r : List α) (d : Nat) (hd : (d : Int) ∈ ix) (hq : d < q.length)
    (hr : d < r.length) (hne : q[d] ≠ r[d]) : project ix q ≠ project ix r := by
  intro he
  have := project_read ix q d hd hq
  have h' := project_read ix r d hd hr
  apply hne
  rw [← this, ← h']
  simp only [he]

end Fren.Core
