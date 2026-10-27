-- keep-sorted start
import FrenCore.Names
import FrenCore.Patterns
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Scope (`Reqs/Lang/Scope`)

`lang::resolve` is interpreted with `Fren.Core.lookup`, and `lang::scope`,
`lang::shadowing` and `lang::pattern_name` are proved of the functions
that both front ends call, `lookup`, `hiddenBy` and `namesVariant`, for
every scope. Both front ends build the scope they pass with
`Table.bindingsOf` and `Table.itemBindings`, which read the table of items
and imports and the local declarations; that they list the right
bindings is tested (`test/ui/lang/shadowing_static.fren`,
`test/ui/lang/scoping.fren`), not proved. -/

namespace Fren.Impls

open Fren.Core (BindingKind Binding Lookup lookup Innermost)

def toBindingKind : BindingKind → lang.BindingKind
  | .input => .Input
  | .output => .Output
  | .parameter => .Parameter
  | .inst => .Instance
  | .expectBinder => .ExpectBinder
  | .patternBinder => .PatternBinder
  | .boundName => .BoundName
  | .definition => .Definition
  | .builtin => .Builtin
  | .constant => .Constant
  | .function => .Function
  | .variant => .Variant
  | .opened => .Opened
  | .module => .Module
  | .enumeration => .Enumeration
  | .item => .Item

def ofBindingKind : lang.BindingKind → BindingKind
  | .Input => .input
  | .Output => .output
  | .Parameter => .parameter
  | .Instance => .inst
  | .ExpectBinder => .expectBinder
  | .PatternBinder => .patternBinder
  | .BoundName => .boundName
  | .Definition => .definition
  | .Builtin => .builtin
  | .Constant => .constant
  | .Function => .function
  | .Variant => .variant
  | .Opened => .opened
  | .Module => .module
  | .Enumeration => .enumeration
  | .Item => .item

@[simp] theorem toBindingKind_ofBindingKind (k : lang.BindingKind) : toBindingKind (ofBindingKind k) = k := by
  cases k <;> rfl

@[simp] theorem ofBindingKind_toBindingKind (k : BindingKind) : ofBindingKind (toBindingKind k) = k := by
  cases k <;> rfl

/-- A binding, as the spec writes it. -/
def toBinding (b : Binding String String) : lang.Binding := ⟨b.name, toBindingKind b.kind, b.target, b.depth⟩

/-- A binding of the spec's, as `Fren.Core` writes it. -/
def ofBinding (b : lang.Binding) : Binding String String := ⟨b.name, ofBindingKind b.kind, b.target, b.depth⟩

@[simp] theorem ofBinding_name (b : lang.Binding) : (ofBinding b).name = b.name := rfl
@[simp] theorem ofBinding_depth (b : lang.Binding) : (ofBinding b).depth = b.depth := rfl
@[simp] theorem ofBinding_target (b : lang.Binding) : (ofBinding b).target = b.target := rfl

@[simp] theorem toBinding_ofBinding (b : lang.Binding) : toBinding (ofBinding b) = b := by
  cases b; simp [toBinding, ofBinding]

@[simp] theorem ofBinding_toBinding (b : Binding String String) : ofBinding (toBinding b) = b := by
  cases b; simp [toBinding, ofBinding]

theorem ofBinding_inj {b c : lang.Binding} : ofBinding b = ofBinding c ↔ b = c :=
  ⟨fun h => by simpa using congrArg toBinding h, fun h => h ▸ rfl⟩

theorem mem_map_ofBinding (l : List lang.Binding) (c : Binding String String) :
    c ∈ l.map ofBinding ↔ toBinding c ∈ l := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩; simpa using hb
  · intro h; exact ⟨_, h, by simp⟩

/-- What a name resolves to, as the spec writes it. -/
def toLookup : Lookup String String → lang.Lookup
  | .found b => .Found (toBindingKind b.kind)
  | .ambiguous => .Ambiguous
  | .unbound => .Unbound

/-- `lookup` over a list of the spec's bindings. -/
def resolveList (l : List lang.Binding) (n : String) : lang.Lookup := toLookup (lookup (l.map ofBinding) n)

theorem resolveList_congr (n : String) (l₁ l₂ : List lang.Binding) (h : Fren.FinSet.Equiv l₁ l₂) :
    resolveList l₁ n = resolveList l₂ n := by
  unfold resolveList
  rw [Fren.Core.lookup_congr (l₁.map ofBinding) (l₂.map ofBinding) n fun x => by
    simp only [mem_map_ofBinding]; exact h _]

/-- `lang::innermost?` is `Innermost`, over the same members. -/
theorem innermost_iff (l : List lang.Binding) (b : lang.Binding) (n : String) :
    lang.innermost? (Fren.FinSet.ofList l) b n = true ↔ Innermost (l.map ofBinding) (ofBinding b) n := by
  simp only [lang.innermost?, decide_eq_true_eq, Fren.FinSet.mem_ofList, Innermost, mem_map_ofBinding,
    toBinding_ofBinding]
  constructor
  · rintro ⟨⟨hb, hn⟩, h⟩
    exact ⟨hb, hn, fun c hc hcn => h (toBinding c) (Nat.zero_le _) ⟨hc, hcn⟩⟩
  · rintro ⟨hb, hn, h⟩
    exact ⟨⟨hb, hn⟩, fun c _ ⟨hc, hcn⟩ => h (ofBinding c) (by simpa using hc) hcn⟩

theorem resolves_to_iff {s : Fren.FinSet lang.Binding} {b : lang.Binding} {n : String} :
    lang.resolves_to? s b n = true ↔
      lang.innermost? s b n = true ∧ ∀ c : lang.Binding, 0 ≤ c.depth → lang.innermost? s c n = true → c = b := by
  unfold lang.resolves_to?; exact @decide_eq_true_iff _ (Classical.propDecidable _)

-- What a name resolves to is `lookup`'s, which depends only on the
-- members of the scope.
interp lang::resolve := fun s n => Quotient.lift (fun l => resolveList l n) (resolveList_congr n) s by
  intro s n
  induction s using Fren.FinSet.ind with | h l => ?_
  show lang.resolve.found _ _ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro b _ hb
    obtain ⟨hi, hu⟩ := resolves_to_iff.1 hb
    show resolveList l n = _
    unfold resolveList
    rw [Fren.Core.lookup_found _ _ (ofBinding b) ((innermost_iff l b n).1 hi) (fun c hc => ?_)]
    · simp [toLookup, ofBinding]
    · have := hu (toBinding c) (Nat.zero_le _) ((innermost_iff l _ n).2 (by simpa using hc))
      subst this; simp
  · rintro ⟨b, c, _, _, ⟨hb, hc⟩, hne⟩
    show resolveList l n = _
    unfold resolveList
    rw [Fren.Core.lookup_ambiguous _ _ (ofBinding b) (ofBinding c) ((innermost_iff l b n).1 hb)
      ((innermost_iff l c n).1 hc) (fun h => hne (ofBinding_inj.1 h))]
    rfl
  · intro hnd
    show resolveList l n = _
    unfold resolveList
    rw [Fren.Core.lookup_unbound _ _ fun c hc hcn => hnd (by
      simp only [lang.declared?, decide_eq_true_eq, Fren.FinSet.mem_ofList]
      exact ⟨toBinding c, Nat.zero_le _, (mem_map_ofBinding l c).1 hc, hcn⟩)]
    rfl

@[simp] theorem resolve_ofList (l : List (Binding String String)) (n : String) :
    lang.resolve (Fren.FinSet.ofList (l.map toBinding)) n = toLookup (lookup l n) := by
  show resolveList _ n = _
  simp [resolveList, List.map_map, Function.comp_def]

theorem namesValue_eq (k : BindingKind) : lang.names_value? (toBindingKind k) = k.namesValue := by
  cases k <;> decide

theorem namesVariant_eq (k : BindingKind) : lang.names_variant? (toBindingKind k) = k.namesVariant := by
  cases k <;> decide

theorem value_eq (l : List (Binding String String)) (n : String) :
    (match toLookup (lookup l n) with
      | .Found k => lang.names_value? k
      | _ => false) = (Fren.Core.hiddenBy l n).isSome := by
  unfold Fren.Core.hiddenBy
  cases lookup l n with
  | found b => simp only [toLookup, Option.isSome]; rw [namesValue_eq]; cases b.kind.namesValue <;> rfl
  | _ => rfl

-- For every scope and name: what it resolves to, by `lookup`, and whether
-- a declaration of it would hide something, by `hiddenBy`.
impl scope: lang::scope for (l : List (Binding String String)) (n : String) {
  bindings := Fren.FinSet.ofList (l.map toBinding),
  name := n,
  result := toLookup (lookup l n),
  value? := (Fren.Core.hiddenBy l n).isSome,
} by
  intro l n _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [lang.scope.def.result, resolve_ofList]
  · simp only [lang.scope.def.value?, resolve_ofList]
    rw [← value_eq]
    cases lookup l n <;> simp [toLookup, lang.Lookup.Found.x0]
  · trivial

-- For every declaration: the scope where it is declared, its name, and
-- whether it has `!`, through `hiddenBy` and the check that both front
-- ends call. A function is absent from the scope of its own body.
impl shadowing: lang::shadowing for (l : List (Binding String String)) (n : String) (b : Bool) {
  bindings := Fren.FinSet.ofList (l.map toBinding),
  name := n,
  bang? := b,
  hides? := (Fren.Core.hiddenBy l n).isSome,
  accepted? := (Fren.Core.checkShadowing (.mkSimple n) ((Fren.Core.hiddenBy l n).map (·.target)) b).isOk,
} by
  intro l n b _
  obtain ⟨hd, he⟩ := scope l n (fun _ _ => Nat.zero_le _)
  refine ⟨_, _, _, _, rfl, ?_, ⟨⟨rfl, rfl⟩, hd, fun _ _ => Nat.zero_le _, he⟩⟩
  simp only [lang.shadowing.ensures, lang.shadowing.ensure.rule]
  cases Fren.Core.hiddenBy l n <;> cases b <;>
    simp [Fren.Core.checkShadowing, Fren.Core.shadowingAccepted, Except.isOk, Except.toBool] <;> rfl

/-- What an identifier in a pattern is, as the spec writes it. -/
def toPatternName : Fren.Core.PatternName → lang.PatternName
  | .boolLiteral => .BoolLiteral
  | .variant => .Variant
  | .binder => .Binder

-- For every identifier of one segment, not applied, in a pattern, and the
-- items and imports in scope: both front ends and the evaluator read it
-- with `patternName` and `namesVariant`.
impl pattern_name: lang::pattern_name for (l : List (Binding String String)) (n : String) (b : Bool) {
  items := Fren.FinSet.ofList (l.map toBinding),
  name := n,
  bang? := b,
  bool_word? := n == "true" || n == "false",
  variant? := Fren.Core.namesVariant l n,
  reading := toPatternName (Fren.Core.patternName (n == "true" || n == "false") b (Fren.Core.namesVariant l n)),
} by
  intro l n b _
  obtain ⟨hd, he⟩ := scope l n (fun _ _ => Nat.zero_le _)
  refine ⟨_, _, _, _, ⟨?_, ?_⟩, ?_, ⟨⟨rfl, rfl⟩, hd, fun _ _ => Nat.zero_le _, he⟩⟩
  · simp only [lang.pattern_name.def.bool_word?]
    rw [Bool.eq_iff_iff]
    simp only [Fren.Str.lit, Fren.FinSet.mem_insert, Fren.FinSet.mem_singleton, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
  · simp only [lang.pattern_name.def.variant?]
    unfold Fren.Core.namesVariant
    cases lookup l n <;> simp [toLookup, lang.Lookup.Found.x0, namesVariant_eq]
  · simp only [lang.pattern_name.ensures, lang.pattern_name.ensure.rule]
    generalize (n == "true" || n == "false") = w
    generalize Fren.Core.namesVariant l n = v
    cases w <;> cases b <;> cases v <;> rfl

end Fren.Impls
