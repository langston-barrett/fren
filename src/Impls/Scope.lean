-- keep-sorted start
import FrenCore.Names
import FrenCore.Patterns
import Impls.Check
import Impls.Lang
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Scope (`Reqs/Lang/Scope`)

`lang::resolve` is interpreted with `Fren.Core.lookup`, and `lang::scope`,
`lang::shadowing` and `lang::pattern_name` are proved of the functions
that both front ends call, `lookup`, `hiddenBy` and `namesVariant`, for
every context. `lang::context_scope` is proved of `Context.bindings`, which
lists a context's scope: both front ends build theirs with it
(`Table.bindingsOf`, `Table.itemBindings`). What is tested, not proved, is
only that `Table.contextOf` reads the context from the table of items and
imports and the local declarations (`test/ui/lang/shadowing_static.fren`,
`test/ui/lang/scoping.fren`). -/

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

theorem toBindingKind_inj {a b : BindingKind} : toBindingKind a = toBindingKind b ↔ a = b := by
  constructor
  · intro h; cases a <;> cases b <;> first | rfl | (simp [toBindingKind] at h)
  · intro h; rw [h]

/-! ## Contexts -/

def toDeclared (d : Fren.Core.Declared String) : lang.Declared := ⟨d.name, toBindingKind d.kind, d.target⟩
def toLocal (l : Fren.Core.Local String) : lang.Local := ⟨toDeclared l.declaration, l.visible⟩
def toImport (i : Fren.Core.Import String) : lang.Import := ⟨toDeclared i.declaration, i.glob⟩
def toContext (cx : Fren.Core.Context String) : lang.Context :=
  ⟨Fren.Seq.ofList (cx.locals.map toLocal), Fren.Seq.ofList cx.builtins, cx.component,
    Fren.Seq.ofList (cx.componentImports.map toImport), Fren.Seq.ofList (cx.items.map toDeclared), cx.declared,
    Fren.Seq.ofList (cx.moduleImports.map toImport), Fren.Seq.ofList (cx.prelude.map toDeclared)⟩

theorem exists_nth {β α : Type} [Inhabited α] (l : List β) (f : β → α) (Q : Int → α → Prop) :
    (∃ i : Int, (0 ≤ i ∧ i < (Fren.Seq.ofList (l.map f)).len) ∧ Q i ((Fren.Seq.ofList (l.map f)).nth i)) ↔
      ∃ i : Fin l.length, Q i (f l[i]) := by
  constructor
  · rintro ⟨i, ⟨h0, h1⟩, hq⟩
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map] at h1
    refine ⟨⟨i.toNat, by omega⟩, ?_⟩
    rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)] at hq
    have e : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg h0
    simpa [e] using hq
  · rintro ⟨i, hq⟩
    refine ⟨i, ⟨by omega, by simp⟩, ?_⟩
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp)]
    simpa using hq

theorem binding_of_iff (d : Fren.Core.Declared String) (k : Int) (b : Binding String String) :
    lang.binding_of? (toDeclared d) k (toBinding b) = true ↔
      b.name = d.name ∧ b.kind = d.kind ∧ b.target = d.target ∧ (b.depth : Int) = k := by
  simp [lang.binding_of?, toDeclared, toBinding, toBindingKind_inj, and_assoc]

theorem eq_at (d : Fren.Core.Declared String) (m : Nat) (b : Binding String String) :
    b = d.at m ↔ b.name = d.name ∧ b.kind = d.kind ∧ b.target = d.target ∧ b.depth = m := by
  rcases b with ⟨_, _, _, _⟩; simp [Fren.Core.Declared.at]

theorem at_eq (d : Fren.Core.Declared String) (m : Nat) (b : Binding String String) :
    d.at m = b ↔ b.name = d.name ∧ b.kind = d.kind ∧ b.target = d.target ∧ b.depth = m := by
  rw [eq_comm, eq_at]

theorem imported_def (q : Fren.Seq lang.Import) (k : Int) (b : lang.Binding) :
    lang.imported? q k b = true ↔ ∃ i : Int, (0 ≤ i ∧ i < q.len) ∧
      lang.binding_of? (q.nth i).declaration (if (q.nth i).glob? = true then k + 1 else k) b = true := by
  unfold lang.imported?; exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem mem_map_fin {β α : Type} (l : List β) (g : β → α) (b : α) :
    b ∈ l.map g ↔ ∃ i : Fin l.length, g l[i] = b := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.getElem_mem _, rfl⟩

theorem imported_iff (ims : List (Fren.Core.Import String)) (k : Nat) (b : Binding String String) :
    lang.imported? (Fren.Seq.ofList (ims.map toImport)) k (toBinding b) = true ↔ b ∈ Fren.Core.importBindings ims k := by
  rw [imported_def, exists_nth ims toImport (fun _ x => lang.binding_of? x.declaration (if x.glob? = true then (k : Int) + 1 else k) (toBinding b) = true),
    Fren.Core.importBindings, mem_map_fin]
  refine exists_congr fun i => ?_
  rw [show (toImport ims[i]).declaration = toDeclared ims[i].declaration from rfl,
    show (toImport ims[i]).glob? = ims[i].glob from rfl, binding_of_iff]
  rw [show ∀ x : Binding String String, (x = b) ↔ (b = x) from fun _ => eq_comm, eq_at]
  cases ims[i].glob <;> simp <;> omega

theorem in_scope_def (cx : lang.Context) (b : lang.Binding) :
    lang.in_scope? cx b = true ↔
      (((((∃ i : Int, (0 ≤ i ∧ i < cx.locals.len) ∧ ((cx.locals.nth i).visible? = true ∧
            lang.binding_of? (cx.locals.nth i).declaration (cx.locals.len - 1 - i) b = true)) ∨
          ∃ i : Int, (0 ≤ i ∧ i < cx.builtins.len) ∧ (b.kind = lang.BindingKind.Builtin ∧
            b.name = cx.builtins.nth i ∧ b.target = cx.builtins.nth i ∧ (b.depth : Int) = cx.locals.len)) ∨
        cx.component? = true ∧ lang.imported? cx.component_imports (cx.locals.len + 1) b = true) ∨
      ∃ i : Int, (0 ≤ i ∧ i < cx.items.len) ∧ (i < cx.declared ∧
        lang.binding_of? (cx.items.nth i) (lang.module_depth cx) b = true)) ∨
      lang.imported? cx.module_imports (lang.module_depth cx) b = true) ∨
      ∃ i : Int, (0 ≤ i ∧ i < cx.prelude.len) ∧ lang.binding_of? (cx.prelude.nth i) (lang.module_depth cx + 2) b = true := by
  unfold lang.in_scope?
  rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
  simp only [and_assoc]

theorem module_depth_eq (cx : Fren.Core.Context String) :
    lang.module_depth (toContext cx) = (cx.moduleDepth : Int) := by
  simp only [lang.module_depth, toContext, Fren.Core.Context.moduleDepth, Fren.Seq.len_eq, Fren.Seq.toList_ofList,
    List.length_map]
  split <;> omega

-- The scope that `Context.bindings` lists is the one `lang::in_scope?` states.
theorem mem_bindings (cx : Fren.Core.Context String) (b : Binding String String) :
    b ∈ cx.bindings ↔ lang.in_scope? (toContext cx) (toBinding b) = true := by
  rw [in_scope_def, module_depth_eq]
  simp only [Fren.Core.Context.bindings, List.mem_append]
  refine or_congr (or_congr (or_congr (or_congr (or_congr ?_ ?_) ?_) ?_) ?_) ?_
  · rw [show (toContext cx).locals = Fren.Seq.ofList (cx.locals.map toLocal) from rfl,
      exists_nth cx.locals toLocal (fun i x => x.visible? = true ∧ lang.binding_of? x.declaration
        ((Fren.Seq.ofList (cx.locals.map toLocal)).len - 1 - i) (toBinding b) = true)]
    simp only [List.mem_filterMap, List.mem_finRange, true_and]
    refine exists_congr fun i => ?_
    rw [show (toLocal cx.locals[i]).declaration = toDeclared cx.locals[i].declaration from rfl,
      show (toLocal cx.locals[i]).visible? = cx.locals[i].visible from rfl, binding_of_iff]
    have hi := i.isLt
    cases cx.locals[i].visible <;> simp [at_eq] <;> omega
  · rw [show (toContext cx).builtins = Fren.Seq.ofList (cx.builtins.map id) by simp [toContext],
      exists_nth cx.builtins id (fun _ x => (toBinding b).kind = lang.BindingKind.Builtin ∧ (toBinding b).name = x ∧
        (toBinding b).target = x ∧ ((toBinding b).depth : Int) = (toContext cx).locals.len), mem_map_fin]
    refine exists_congr fun i => ?_
    rcases b with ⟨bn, bk, bt, bd⟩
    simp only [toBinding, toContext, Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map, id]
    constructor
    · intro h; cases h; simp [toBindingKind]
    · rintro ⟨hk, rfl, rfl, hd⟩
      have : bk = .builtin := by cases bk <;> simp_all [toBindingKind]
      subst this; simp; omega
  · rw [show (toContext cx).component_imports = Fren.Seq.ofList (cx.componentImports.map toImport) from rfl,
      show (toContext cx).component? = cx.component from rfl,
      show (toContext cx).locals.len = (cx.locals.length : Int) by simp [toContext]]
    rw [show ((cx.locals.length : Int) + 1) = ((cx.locals.length + 1 : Nat) : Int) by omega, imported_iff]
    cases cx.component
    · simp
    · exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  · rw [show (toContext cx).items = Fren.Seq.ofList (cx.items.map toDeclared) from rfl,
      show (toContext cx).declared = cx.declared from rfl,
      exists_nth cx.items toDeclared (fun i x => i < (cx.declared : Int) ∧
        lang.binding_of? x (cx.moduleDepth : Int) (toBinding b) = true)]
    simp only [List.mem_filterMap, List.mem_finRange, true_and]
    refine exists_congr fun i => ?_
    rw [binding_of_iff]
    by_cases h : i.val < cx.declared <;> simp [h, at_eq] <;> omega
  · rw [show (toContext cx).module_imports = Fren.Seq.ofList (cx.moduleImports.map toImport) from rfl, imported_iff]
  · rw [show (toContext cx).prelude = Fren.Seq.ofList (cx.prelude.map toDeclared) from rfl,
      exists_nth cx.prelude toDeclared (fun _ x => lang.binding_of? x ((cx.moduleDepth : Int) + 2) (toBinding b) = true),
      mem_map_fin]
    refine exists_congr fun i => ?_
    rw [binding_of_iff, at_eq]
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h1, h2, h3, by omega⟩

-- For every context and binding: `Context.bindings`, which both front ends
-- build their scopes with, lists exactly the bindings that
-- `lang::context_scope` says are in scope.
impl context_scope: lang::context_scope for (cx : Fren.Core.Context String) (b : Binding String String) {
  context := toContext cx,
  binding := toBinding b,
  listed? := decide (b ∈ cx.bindings),
} by
  intro cx b _
  refine ⟨?_, trivial⟩
  simp only [lang.context_scope.defs, lang.context_scope.def.listed?]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_bindings]

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

-- For every declaration: where it is declared, its name, and whether it has
-- `!`, through the scope `Context.bindings` lists (`context_scope`),
-- `hiddenBy` and the check that both front ends call (`Table.hidden?`).
impl shadowing: lang::shadowing for (cx : Fren.Core.Context String) (n : String) (b : Bool) {
  bindings := Fren.FinSet.ofList (cx.bindings.map toBinding),
  name := n,
  bang? := b,
  hides? := (Fren.Core.hiddenBy cx.bindings n).isSome,
  accepted? := (Fren.Core.checkShadowing (.mkSimple n) ((Fren.Core.hiddenBy cx.bindings n).map (·.target)) b).isOk,
} by
  intro cx n b _
  obtain ⟨hd, he⟩ := scope cx.bindings n (fun _ _ => Nat.zero_le _)
  refine ⟨_, _, _, _, rfl, ?_, ⟨⟨rfl, rfl⟩, hd, fun _ _ => Nat.zero_le _, he⟩⟩
  simp only [lang.shadowing.ensures, lang.shadowing.ensure.rule]
  cases Fren.Core.hiddenBy cx.bindings n <;> cases b <;>
    simp [Fren.Core.checkShadowing, Fren.Core.shadowingAccepted, Except.isOk, Except.toBool] <;> rfl

/-- What an identifier in a pattern is, as the spec writes it. -/
def toPatternName : Fren.Core.PatternName → lang.PatternName
  | .boolLiteral => .BoolLiteral
  | .variant => .Variant
  | .binder => .Binder

-- For every identifier of one segment, not applied, in a pattern, and where
-- it is written: both front ends and the evaluator read it with
-- `patternName` and `namesVariant` over the items and imports that
-- `Context.bindings` lists (`Table.namesVariant?`).
impl pattern_name: lang::pattern_name for (cx : Fren.Core.Context String) (n : String) (b : Bool) {
  items := Fren.FinSet.ofList (cx.itemScope.bindings.map toBinding),
  name := n,
  bang? := b,
  bool_word? := n == "true" || n == "false",
  variant? := Fren.Core.namesVariant cx.itemScope.bindings n,
  reading := toPatternName (Fren.Core.patternName (n == "true" || n == "false") b
    (Fren.Core.namesVariant cx.itemScope.bindings n)),
} by
  intro cx n b _
  obtain ⟨hd, he⟩ := scope cx.itemScope.bindings n (fun _ _ => Nat.zero_le _)
  refine ⟨_, _, _, _, ⟨?_, ?_⟩, ?_, ⟨⟨rfl, rfl⟩, hd, fun _ _ => Nat.zero_le _, he⟩⟩
  · simp only [lang.pattern_name.def.bool_word?]
    rw [Bool.eq_iff_iff]
    simp only [Fren.Str.lit, Fren.FinSet.mem_insert, Fren.FinSet.mem_singleton, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
  · simp only [lang.pattern_name.def.variant?]
    unfold Fren.Core.namesVariant
    cases lookup cx.itemScope.bindings n <;> simp [toLookup, lang.Lookup.Found.x0, namesVariant_eq]
  · simp only [lang.pattern_name.ensures, lang.pattern_name.ensure.rule]
    generalize (n == "true" || n == "false") = w
    generalize Fren.Core.namesVariant cx.itemScope.bindings n = v
    cases w <;> cases b <;> cases v <;> rfl

-- For every binder of a pattern test, and every place where its name is
-- mentioned: both front ends put the binder among the locals there exactly
-- where `binderVisible` holds (`test_scope`), which is the local's
-- `visible?`.
impl test_local: lang::test_local for (d : Fren.Core.Declared String) (c : Fren.Core.TestContext) (n t : Nat)
    (st : Fren.Core.TestSite) {
  declaration := toDeclared d,
  context := toTestContext c,
  operands := n,
  test_at := t,
  site := toSite st,
  entry := ⟨toDeclared d, Fren.Core.binderVisible c t n st⟩,
} by
  intro d c n t st ha
  have hts : lang.test_scope.assumes (toTestContext c) n t (toSite st) (Fren.Core.binderVisible c t n st)
      (Fren.Core.testBinds c t n) := by
    exact ⟨ha.1, ha.2.1⟩
  exact ⟨_, _, _, _, _, _, rfl, trivial, by simp, hts, test_scope c n t st hts⟩

end Fren.Impls
