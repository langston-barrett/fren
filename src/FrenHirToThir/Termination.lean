module

public section
namespace FrenHirToThir.Termination

/-! The deciding functions of the termination check of the static semantics
(`src/Spec/Language/StaticSemantics.md`, Termination). Each mirrors the
chapter's Fren definition of the same name over lists, oldest entry first,
and `Spec.Compiler.Thir` proves the two equal. Levels are de Bruijn levels. -/

inductive Size where
  | same | smaller | unknown
  deriving Repr, DecidableEq

/-- The written calls of a body: each call with its callee and, for each
argument, its level where it is a local; `bind` holds the calls of a let's
body and the level of the let's value where the value is a local. -/
inductive Calls (α : Type) where
  | leaf
  | both (left right : Calls α)
  | call (callee : α) (arguments : List (Option Nat))
  | bind (value : Option Nat) (body : Calls α)
  deriving Repr

/-- What the check reads of a function. `unchecked` is the termination mark. -/
structure Function (α τ : Type) where
  item : α
  parameters : List τ
  unchecked : Bool
  body : Calls α

@[expose] def localSize (sizes : List Size) : Option Nat → Size
  | some level => sizes[level]?.getD .unknown
  | none => .unknown

@[expose] def parameterSizes {τ : Type} (parameters : List τ) (decreasing : Nat) : List Size :=
  (List.range parameters.length).map fun level => if level = decreasing then .same else .unknown

@[expose] def argumentGuarded (sizes : List Size) (arguments : List (Option Nat))
    (parameter : Nat) : Bool :=
  match arguments[parameter]? with
  | some argument => localSize sizes argument == .smaller
  | none => false

variable {α τ : Type} [BEq α]

/-- The parameter that a choice gives a function: the newest entry for it. -/
@[expose] def chosen (choice : List (α × Nat)) (item : α) : Option Nat :=
  (choice.reverse.find? (·.1 == item)).map (·.2)

@[expose] def callsGuarded (choice : List (α × Nat)) : List Size → Calls α → Bool
  | _, .leaf => true
  | sizes, .both left right => callsGuarded choice sizes left && callsGuarded choice sizes right
  | sizes, .call callee arguments =>
    match chosen choice callee with
    | some parameter => argumentGuarded sizes arguments parameter
    | none => true
  | sizes, .bind value body => callsGuarded choice (sizes ++ [localSize sizes value]) body

@[expose] def bodyGuarded (choice : List (α × Nat)) (function : Function α τ) : Bool :=
  match chosen choice function.item with
  | some parameter =>
    callsGuarded choice (parameterSizes function.parameters parameter) function.body
  | none => false

@[expose] def choiceGuarded (choice : List (α × Nat)) (group : List (Function α τ)) : Bool :=
  group.all (bodyGuarded choice)

omit [BEq α] in
/-- Every choice of one parameter for each function of the group. -/
@[expose] def choices (group : List (Function α τ)) : List (List (α × Nat)) :=
  group.foldl (fun found function =>
    (List.range function.parameters.length).flatMap fun level =>
      found.map (· ++ [(function.item, level)])) [[]]

/-- The chapter's `structural?`: an exhaustive search of the choices. -/
@[expose] def structural (group : List (Function α τ)) : Bool :=
  (choices group).any (choiceGuarded · group)

omit [BEq α] in
@[expose] def optedOut (covered : List (Function α τ)) : Bool := covered.any (·.unchecked)

omit [BEq α] in
/-- The judgment of a function that is in no recursive group. -/
@[expose] def passesAlone (function : Function α τ) : Bool := !function.unchecked

/-- The judgment of the functions of one recursive group. -/
@[expose] def groupPasses (group : List (Function α τ)) : Bool :=
  !optedOut group && structural group

/-- A function passes hereditarily when it and every function it reaches pass. -/
@[expose] def hereditary (passes : α → Bool) (reached : α → List α) (item : α) : Bool :=
  passes item && (reached item).all passes

/-- A condition mentions only functions that pass hereditarily. -/
@[expose] def conditionTerminating (passes : α → Bool) (reached : α → List α)
    (mentioned : List α) : Bool :=
  mentioned.all (hereditary passes reached)

/-! ## The search in the present Core

No size context of the present Core holds `smaller`: a parameter has `same`
or `unknown`, and a let gives its local the size of its value. So a call that
a choice lists is never guarded, every choice gives one verdict, and the
exhaustive search of `structural` has the closed form `structuralNow`, which
validation runs. `structural_eq_now` is the proof; it stops holding, and
validation must search, once a form gives a local the size `smaller`. -/

/-- Some written call has one of the items as its callee. -/
@[expose] def mentions (items : List α) : Calls α → Bool
  | .leaf => false
  | .both left right => mentions items left || mentions items right
  | .call callee _ => items.any (· == callee)
  | .bind _ body => mentions items body

/-- `structural` without the search: every function of the group has a
parameter, and no body of the group calls a function of the group. -/
@[expose] def structuralNow (group : List (Function α τ)) : Bool :=
  !group.any (·.parameters.isEmpty) &&
    group.all fun function =>
      (group.map (·.item)).any (· == function.item) &&
        !mentions (group.map (·.item)) function.body

/-- Some written call has a callee that the choice lists. -/
def listed (choice : List (α × Nat)) : Calls α → Bool
  | .leaf => false
  | .both left right => listed choice left || listed choice right
  | .call callee _ => (chosen choice callee).isSome
  | .bind _ body => listed choice body

theorem localSize_ne_smaller (sizes : List Size) (h : ∀ size ∈ sizes, size ≠ .smaller)
    (value : Option Nat) : localSize sizes value ≠ .smaller := by
  cases value with
  | none => simp [localSize]
  | some level =>
    cases hl : sizes[level]? with
    | none => simp [localSize, hl]
    | some size =>
      have := h size (List.mem_of_getElem? hl)
      simpa [localSize, hl] using this

theorem callsGuarded_eq_not_listed (choice : List (α × Nat)) (calls : Calls α)
    (sizes : List Size) (h : ∀ size ∈ sizes, size ≠ .smaller) :
    callsGuarded choice sizes calls = !listed choice calls := by
  induction calls generalizing sizes with
  | leaf => simp [callsGuarded, listed]
  | both left right ihl ihr => simp [callsGuarded, listed, ihl sizes h, ihr sizes h]
  | call callee arguments =>
    cases hc : chosen choice callee with
    | none => simp [callsGuarded, listed, hc]
    | some parameter =>
      cases ha : arguments[parameter]? with
      | none => simp [callsGuarded, listed, hc, argumentGuarded, ha]
      | some argument =>
        have := localSize_ne_smaller sizes h argument
        simp [callsGuarded, listed, hc, argumentGuarded, ha, this]
  | bind value body ih =>
    have hs : ∀ size ∈ sizes ++ [localSize sizes value], size ≠ .smaller := by
      intro size hm
      rcases List.mem_append.1 hm with hm | hm
      · exact h size hm
      · have : size = localSize sizes value := by simpa using hm
        exact this ▸ localSize_ne_smaller sizes h value
    simp [callsGuarded, listed, ih _ hs]

theorem parameterSizes_ne_smaller (parameters : List τ) (decreasing : Nat) :
    ∀ size ∈ parameterSizes parameters decreasing, size ≠ .smaller := by
  intro size hm
  obtain ⟨level, _, rfl⟩ := List.mem_map.1 hm
  split <;> simp

omit [BEq α] in
/-- Induction on a list from its newest entry. -/
theorem snoc_induction {β : Type} {motive : List β → Prop} (nil : motive [])
    (snoc : ∀ earlier last, motive earlier → motive (earlier ++ [last])) :
    ∀ entries, motive entries := by
  have reversed : ∀ entries : List β, motive entries.reverse := by
    intro entries
    induction entries with
    | nil => exact nil
    | cons first rest ih => rw [List.reverse_cons]; exact snoc _ _ ih
  intro entries
  rw [← List.reverse_reverse entries]
  exact reversed _

omit [BEq α] in
theorem choices_append (group : List (Function α τ)) (function : Function α τ) :
    choices (group ++ [function]) =
      (List.range function.parameters.length).flatMap fun level =>
        (choices group).map (· ++ [(function.item, level)]) := by
  simp [choices, List.foldl_append]

theorem chosen_append (choice : List (α × Nat)) (entry : α × Nat) (item : α) :
    chosen (choice ++ [entry]) item =
      if entry.1 == item then some entry.2 else chosen choice item := by
  by_cases h : entry.1 == item <;> simp [chosen, h]

theorem chosen_isSome (group : List (Function α τ)) (item : α) :
    ∀ choice ∈ choices group,
      (chosen choice item).isSome = (group.map (·.item)).any (· == item) := by
  induction group using snoc_induction with
  | nil => simp [choices, chosen]
  | snoc earlier function ih =>
    intro choice hm
    rw [choices_append] at hm
    obtain ⟨level, _, hm⟩ := List.mem_flatMap.1 hm
    obtain ⟨shorter, hs, rfl⟩ := List.mem_map.1 hm
    have := ih shorter hs
    by_cases h : function.item == item <;> simp [chosen_append, h, this]

omit [BEq α] in
theorem choices_eq_nil (group : List (Function α τ)) :
    choices group = [] ↔ ∃ function ∈ group, function.parameters = [] := by
  induction group using snoc_induction with
  | nil => simp [choices]
  | snoc earlier function ih =>
    rw [choices_append]
    constructor
    · intro h
      by_cases hp : function.parameters = []
      · exact ⟨function, by simp, hp⟩
      · have hz : 0 ∈ List.range function.parameters.length :=
          List.mem_range.2 (List.length_pos_iff.2 hp)
        have := List.flatMap_eq_nil_iff.1 h 0 hz
        obtain ⟨found, hf, he⟩ := ih.1 (List.map_eq_nil_iff.1 this)
        exact ⟨found, by simp [hf], he⟩
    · rintro ⟨found, hf, he⟩
      rcases List.mem_append.1 hf with hf | hf
      · have := ih.2 ⟨found, hf, he⟩
        simp [this]
      · have : found = function := by simpa using hf
        subst this
        simp [he]

theorem listed_eq_mentions (group : List (Function α τ)) (choice : List (α × Nat))
    (h : choice ∈ choices group) (calls : Calls α) :
    listed choice calls = mentions (group.map (·.item)) calls := by
  induction calls with
  | leaf => rfl
  | both left right ihl ihr => simp [listed, mentions, ihl, ihr]
  | call callee arguments => simpa [listed, mentions] using chosen_isSome group callee choice h
  | bind value body ih => simpa [listed, mentions] using ih

theorem bodyGuarded_eq (group : List (Function α τ)) (choice : List (α × Nat))
    (h : choice ∈ choices group) (function : Function α τ) :
    bodyGuarded choice function =
      ((group.map (·.item)).any (· == function.item) &&
        !mentions (group.map (·.item)) function.body) := by
  have hs := chosen_isSome group function.item choice h
  cases hc : chosen choice function.item with
  | none =>
    rw [hc] at hs
    simp [bodyGuarded, hc, ← hs]
  | some parameter =>
    rw [hc] at hs
    rw [bodyGuarded, hc, ← hs, ← listed_eq_mentions group choice h]
    simpa using callsGuarded_eq_not_listed choice function.body _
      (parameterSizes_ne_smaller function.parameters parameter)

/-- The exhaustive search and its closed form in the present Core agree. -/
theorem structural_eq_now (group : List (Function α τ)) :
    structural group = structuralNow group := by
  by_cases he : ∃ function ∈ group, function.parameters = []
  · have hn := (choices_eq_nil group).2 he
    have : group.any (·.parameters.isEmpty) = true := by
      obtain ⟨function, hf, hp⟩ := he
      exact List.any_eq_true.2 ⟨function, hf, by simp [hp]⟩
    simp [structural, structuralNow, hn, this]
  · have hn : choices group ≠ [] := fun h => he ((choices_eq_nil group).1 h)
    have hp : group.any (·.parameters.isEmpty) = false := by
      apply Bool.eq_false_iff.2
      intro ha
      obtain ⟨function, hf, hp⟩ := List.any_eq_true.1 ha
      exact he ⟨function, hf, by simpa using hp⟩
    have hall : ∀ choice ∈ choices group, choiceGuarded choice group =
        group.all fun function =>
          (group.map (·.item)).any (· == function.item) &&
            !mentions (group.map (·.item)) function.body := by
      intro choice hc
      unfold choiceGuarded
      exact congrArg group.all (funext fun function => bodyGuarded_eq group choice hc function)
    obtain ⟨first, rest, hl⟩ := List.exists_cons_of_ne_nil hn
    unfold structural structuralNow
    rw [hp]
    cases hk : (group.all fun function =>
        (group.map (·.item)).any (· == function.item) &&
          !mentions (group.map (·.item)) function.body) with
    | true =>
      have := hall first (by simp [hl])
      rw [hk] at this
      simpa using List.any_eq_true.2 ⟨first, by simp [hl], this⟩
    | false =>
      have : (choices group).any (choiceGuarded · group) = false := by
        apply Bool.eq_false_iff.2
        intro ha
        obtain ⟨choice, hc, hg⟩ := List.any_eq_true.1 ha
        rw [hall choice hc, hk] at hg
        cases hg
      simpa using this

/-- The judgment of one recursive group as validation computes it. -/
@[expose] def groupPassesNow (group : List (Function α τ)) : Bool :=
  !optedOut group && structuralNow group

theorem groupPasses_eq_now (group : List (Function α τ)) :
    groupPasses group = groupPassesNow group := by
  rw [groupPasses, groupPassesNow, structural_eq_now]

end FrenHirToThir.Termination
