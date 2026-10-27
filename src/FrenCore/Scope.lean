/-!
# Scope (`Reqs/Lang/Scope`)

The bindings in scope where a name is written, and the one it resolves to:
the innermost of that name, or none if several distinct ones are, as
variants that glob imports open may be. Both front ends resolve names that
a declaration may hide (`Table.hidden?`), the first segment of a path
(`Table.resolvePath`) and the members of a module or enumeration
(`Table.walk`) with `lookup`.

A binding is generic in its name and target, so that the front ends'
`Name`s and the spec's `String`s are both read by the same function.
-/

namespace Fren.Core

/-- What a binding declares (`lang::BindingKind`). -/
inductive BindingKind where
  | input
  | output
  | parameter
  | inst
  | expectBinder
  | patternBinder
  | boundName
  | definition
  | builtin
  | constant
  | function
  | variant
  | opened
  | module
  | enumeration
  | item
  deriving Inhabited, DecidableEq, Repr

/-- Whether it names a value, which a declaration may hide (`lang::names_value?`). -/
def BindingKind.namesValue : BindingKind → Bool
  | .module | .enumeration | .item => false
  | _ => true

/-- Whether it names a variant (`lang::names_variant?`). -/
def BindingKind.namesVariant : BindingKind → Bool
  | .variant | .opened => true
  | _ => false

/-- What a local binding is, in a message: `the input`, and so on. -/
def BindingKind.describe : BindingKind → String
  | .input => "the input"
  | .output => "the output"
  | .parameter => "the parameter"
  | .inst => "the instance"
  | .expectBinder => "the global expectation's binder"
  | .patternBinder => "the binder"
  | .boundName => "the bound name"
  | .definition => "the definition"
  | .builtin => "the built-in function"
  | .constant => "the constant"
  | .function => "the function"
  | .variant | .opened => "the variant"
  | .module => "the module"
  | .enumeration => "the enum"
  | .item => "the item"

/-- One declaration in scope (`lang::Binding`): its name, its kind, what
it declares, and how many scopes out it is, from 0. -/
structure Binding (ν τ : Type) where
  name : ν
  kind : BindingKind
  target : τ
  depth : Nat
  deriving Inhabited, DecidableEq, Repr

/-- What a name resolves to (`lang::Lookup`), with its binding. -/
inductive Lookup (ν τ : Type) where
  | found (b : Binding ν τ)
  | ambiguous
  | unbound
  deriving Inhabited, Repr

section
variable {ν τ : Type} [DecidableEq ν] [DecidableEq τ]

/-- The least depth of the bindings `bs`, all of one name. -/
def leastDepth : List (Binding ν τ) → Nat
  | [] => 0
  | b :: bs => bs.foldl (fun m c => min m c.depth) b.depth

/-- The bindings of `n` in `bs` at the least depth of those of `n`, in
order: its innermost, each as often as `bs` has it. -/
def innermost (bs : List (Binding ν τ)) (n : ν) : List (Binding ν τ) :=
  let hits := bs.filter (·.name == n)
  hits.filter (·.depth == leastDepth hits)

/-- What `n` resolves to in the scope `bs` (`lang::resolve`): the
innermost binding of `n`, if every innermost one is the same. -/
def lookup (bs : List (Binding ν τ)) (n : ν) : Lookup ν τ :=
  match innermost bs n with
  | [] => .unbound
  | b :: rest => if rest.all (· == b) then .found b else .ambiguous

/-- Whether `n` resolves to a binding in `bs` (`modules::member`'s `found?`). -/
def resolves (bs : List (Binding ν τ)) (n : ν) : Bool := lookup bs n matches .found _

/-- What a declaration of `n` would hide in the scope `bs`, if anything
(`lang::shadowing`): what `n` resolves to, if it names a value. -/
def hiddenBy (bs : List (Binding ν τ)) (n : ν) : Option (Binding ν τ) :=
  match lookup bs n with
  | .found b => if b.kind.namesValue then some b else none
  | _ => none

/-- Whether `n` names a variant among the items and imports `bs`
(`lang::pattern_name`'s `variant?`). -/
def namesVariant (bs : List (Binding ν τ)) (n : ν) : Bool :=
  match lookup bs n with
  | .found b => b.kind.namesVariant
  | _ => false

end

/-! ## What a name resolves to, by the members of its scope -/

variable {ν τ : Type}

section


theorem foldl_min_le (bs : List (Binding ν τ)) (a : Nat) :
    bs.foldl (fun m c => min m c.depth) a ≤ a ∧ ∀ c ∈ bs, bs.foldl (fun m c => min m c.depth) a ≤ c.depth := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨h1, h2⟩ := ih (min a b.depth)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, by omega, h2⟩

theorem foldl_min_mem (bs : List (Binding ν τ)) (a : Nat) :
    bs.foldl (fun m c => min m c.depth) a = a ∨ ∃ c ∈ bs, bs.foldl (fun m c => min m c.depth) a = c.depth := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (min a b.depth) with h | ⟨c, hc, h⟩
    · rw [h]; by_cases hab : a ≤ b.depth
      · left; omega
      · right; exact ⟨b, Or.inl rfl, by omega⟩
    · right; exact ⟨c, Or.inr hc, h⟩

theorem leastDepth_spec (hs : List (Binding ν τ)) (h : hs ≠ []) :
    (∃ c ∈ hs, leastDepth hs = c.depth) ∧ ∀ c ∈ hs, leastDepth hs ≤ c.depth := by
  match hs, h with
  | b :: bs, _ =>
    obtain ⟨h1, h2⟩ := foldl_min_le bs b.depth
    refine ⟨?_, ?_⟩
    · rcases foldl_min_mem bs b.depth with e | ⟨c, hc, e⟩
      · exact ⟨b, List.mem_cons_self, e⟩
      · exact ⟨c, List.mem_cons_of_mem _ hc, e⟩
    · simp only [List.mem_cons, forall_eq_or_imp, leastDepth]; exact ⟨h1, h2⟩

end

section
variable [DecidableEq ν] [DecidableEq τ]

/-- `b` is a binding of `n` in `bs` at the least depth of those of `n`. -/
def Innermost (bs : List (Binding ν τ)) (b : Binding ν τ) (n : ν) : Prop :=
  b ∈ bs ∧ b.name = n ∧ ∀ c ∈ bs, c.name = n → b.depth ≤ c.depth

omit [DecidableEq τ] in
theorem mem_innermost (bs : List (Binding ν τ)) (n : ν) (b : Binding ν τ) :
    b ∈ innermost bs n ↔ Innermost bs b n := by
  by_cases hne : bs.filter (·.name == n) = []
  · simp only [innermost, hne, List.filter_nil, List.not_mem_nil, false_iff]
    rintro ⟨hb, hn, _⟩
    have : b ∈ bs.filter (·.name == n) := by simp [hb, hn]
    rw [hne] at this; simp at this
  · simp only [innermost, List.mem_filter, beq_iff_eq, Innermost]
    obtain ⟨⟨c, hc, e⟩, hle⟩ := leastDepth_spec _ hne
    have hc' := List.mem_filter.1 hc
    have hcn : c.name = n := by simpa using hc'.2
    have hle' : ∀ d ∈ bs, d.name = n → leastDepth (bs.filter (·.name == n)) ≤ d.depth :=
      fun d hd hdn => hle d (List.mem_filter.2 ⟨hd, by simp [hdn]⟩)
    constructor
    · rintro ⟨⟨hb, hn⟩, hd⟩
      refine ⟨hb, hn, fun d hd' hdn => ?_⟩
      have := hle' d hd' hdn; omega
    · rintro ⟨hb, hn, hmin⟩
      refine ⟨⟨hb, hn⟩, ?_⟩
      have h1 := hle' b hb hn
      have h2 := hmin c hc'.1 hcn
      omega

theorem lookup_found (bs : List (Binding ν τ)) (n : ν) (b : Binding ν τ) (hb : Innermost bs b n)
    (hu : ∀ c, Innermost bs c n → c = b) : lookup bs n = .found b := by
  have hall : ∀ c ∈ innermost bs n, c = b := fun c hc => hu c ((mem_innermost _ _ _).1 hc)
  have hmem : b ∈ innermost bs n := (mem_innermost _ _ _).2 hb
  unfold lookup
  match h : innermost bs n, hall, hmem with
  | [], _, hm => simp at hm
  | x :: rest, ha, _ =>
    have hx := ha x (by simp); subst hx
    have : rest.all (· == x) = true := by
      simp only [List.all_eq_true, beq_iff_eq]; exact fun c hc => ha c (by simp [hc])
    simp [this]

theorem lookup_ambiguous (bs : List (Binding ν τ)) (n : ν) (b c : Binding ν τ) (hb : Innermost bs b n)
    (hc : Innermost bs c n) (hne : b ≠ c) : lookup bs n = .ambiguous := by
  have mb := (mem_innermost _ _ _).2 hb
  have mc := (mem_innermost _ _ _).2 hc
  unfold lookup
  match h : innermost bs n, mb, mc with
  | [], m, _ => simp at m
  | x :: rest, m1, m2 =>
    have : rest.all (· == x) = false := by
      rw [Bool.eq_false_iff]; intro ha
      simp only [List.all_eq_true, beq_iff_eq] at ha
      have e : ∀ d ∈ x :: rest, d = x := by
        intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | hd; rfl; exact ha d hd
      exact hne ((e b m1).trans (e c m2).symm)
    simp [this]

theorem lookup_unbound (bs : List (Binding ν τ)) (n : ν) (h : ∀ b ∈ bs, b.name ≠ n) : lookup bs n = .unbound := by
  have : innermost bs n = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro b hb; obtain ⟨hm, hn, _⟩ := (mem_innermost _ _ _).1 hb; exact h b hm hn
  unfold lookup; rw [this]


omit [DecidableEq τ] in
theorem exists_innermost (bs : List (Binding ν τ)) (n : ν) (h : ∃ b ∈ bs, b.name = n) :
    ∃ b, Innermost bs b n := by
  obtain ⟨b, hb, hn⟩ := h
  have hne : bs.filter (·.name == n) ≠ [] := List.ne_nil_of_mem (List.mem_filter.2 ⟨hb, by simp [hn]⟩)
  obtain ⟨⟨c, hc, e⟩, hle⟩ := leastDepth_spec _ hne
  have hc' := List.mem_filter.1 hc
  have hcn : c.name = n := by simpa using hc'.2
  refine ⟨c, hc'.1, hcn, fun d hd hdn => ?_⟩
  have := hle d (List.mem_filter.2 ⟨hd, by simp [hdn]⟩); omega

/-- What a name resolves to depends only on the members of the scope. -/
theorem lookup_congr (l₁ l₂ : List (Binding ν τ)) (n : ν) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    lookup l₁ n = lookup l₂ n := by
  have hi : ∀ b, Innermost l₁ b n ↔ Innermost l₂ b n := by
    intro b; simp only [Innermost, h]
  by_cases hu : ∃ b, Innermost l₁ b n ∧ ∀ c, Innermost l₁ c n → c = b
  · obtain ⟨b, hb, hc⟩ := hu
    rw [lookup_found _ _ b hb hc, lookup_found _ _ b ((hi b).1 hb) (fun c h' => hc c ((hi c).2 h'))]
  · by_cases ha : ∃ b c, Innermost l₁ b n ∧ Innermost l₁ c n ∧ b ≠ c
    · obtain ⟨b, c, hb, hc, hne⟩ := ha
      rw [lookup_ambiguous _ _ b c hb hc hne, lookup_ambiguous _ _ b c ((hi b).1 hb) ((hi c).1 hc) hne]
    · have hnone : ∀ b ∈ l₁, b.name ≠ n := by
        intro b hb hn
        obtain ⟨c, hc⟩ := exists_innermost l₁ n ⟨b, hb, hn⟩
        exact hu ⟨c, hc, fun d hd => Classical.byContradiction fun hne => ha ⟨d, c, hd, hc, hne⟩⟩
      rw [lookup_unbound _ _ hnone, lookup_unbound _ _ (fun b hb => hnone b ((h b).2 hb))]

end

end Fren.Core
