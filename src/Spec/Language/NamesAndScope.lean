import Fren.Impl
import Fren.Literate
import Fren.Trace
import FrenAstToHir
import Spec.Language.Types

open Fren.Lang

#fren_md "NamesAndScope.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.NamesAndScope

open spec.types spec.names
open Spec.Language.Types (lookup_bound lookup_none)

/-! ## Scopes -/

theorem local_bound (scope : Snoc String) (name : String) (level : Int)
    (h : resolve_local scope name = some level) : lookup _ scope level = some name := by
  induction scope with
  | Empty => simp [resolve_local] at h
  | Extend earlier newest ih =>
    simp only [resolve_local] at h
    split at h
    · rename_i eq
      simp at h
      simp [lookup, ← h, eq]
    · have found := ih h
      have bound := lookup_bound earlier level name found
      have : level ≠ length _ earlier := by omega
      simp [lookup, this, found]

theorem local_lt (scope : Snoc String) (name : String) (level : Int)
    (h : resolve_local scope name = some level) : 0 ≤ level ∧ level < length _ scope :=
  lookup_bound scope level name (local_bound scope name level h)

theorem local_nearest (scope : Snoc String) (name : String) (level other : Int)
    (h : resolve_local scope name = some level) (later : level < other) :
    lookup _ scope other ≠ some name := by
  induction scope with
  | Empty => simp [resolve_local] at h
  | Extend earlier newest ih =>
    simp only [resolve_local] at h
    split at h
    · simp at h
      have outside : ¬ (0 ≤ other ∧ other < length _ earlier) := by omega
      have : other ≠ length _ earlier := by omega
      simp [lookup, this, lookup_none earlier other outside]
    · rename_i ne
      by_cases at_newest : other = length _ earlier
      · simp [lookup, at_newest, ne]
      · simpa [lookup, at_newest] using ih h

theorem local_complete (scope : Snoc String) (name : String) (other : Int)
    (h : resolve_local scope name = none) : lookup _ scope other ≠ some name := by
  induction scope with
  | Empty => simp [lookup]
  | Extend earlier newest ih =>
    simp only [resolve_local] at h
    split at h
    · simp at h
    · rename_i ne
      by_cases at_newest : other = length _ earlier
      · simp [lookup, at_newest, ne]
      · simpa [lookup, at_newest] using ih h

theorem insert_name_length (scope : Snoc String) (cutoff : Int) (extra : String)
    (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope) :
    length _ (insert_name scope cutoff extra) = length _ scope + 1 := by
  induction scope with
  | Empty =>
    have : cutoff = 0 := by simp [length] at h1; omega
    simp [insert_name, this, length]
  | Extend earlier name ih =>
    simp only [insert_name]
    split
    · simp [length]
    · rename_i ne
      simp only [length] at h1 ⊢
      rw [ih (by omega)]

theorem local_weakens (scope : Snoc String) (cutoff : Int) (extra name : String)
    (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope) (ne : name ≠ extra) :
    resolve_local (insert_name scope cutoff extra) name
      = shifted (resolve_local scope name) cutoff := by
  have ne' : extra ≠ name := fun eq => ne eq.symm
  induction scope with
  | Empty =>
    have : cutoff = 0 := by simp [length] at h1; omega
    simp [insert_name, this, resolve_local, ne']
  | Extend earlier newest ih =>
    simp only [insert_name]
    split
    · rename_i at_end
      simp only [resolve_local, if_neg ne']
      cases found : (if newest = name then some (↑(length _ earlier) : Int) else resolve_local earlier name) with
      | none => rfl
      | some level =>
        have bound := local_lt (.Extend earlier newest) name level (by simpa [resolve_local] using found)
        simp only [length] at bound
        have : ¬ level ≥ cutoff := by omega
        simp [shift, this]
    · rename_i not_end
      simp only [length] at h1
      have h1' : cutoff ≤ length _ earlier := by omega
      simp only [resolve_local]
      split
      · have : (↑(length _ earlier) : Int) ≥ cutoff := by omega
        simp [insert_name_length earlier cutoff extra h0 h1', shift, this]
      · exact ih h1'

/-- A scope as the resolver holds it: nearest first. -/
def nearestFirst : Snoc String → List String
  | .Empty => []
  | .Extend earlier newest => newest :: nearestFirst earlier

theorem nearest_converse (scope : Snoc String) (name : String) :
    (FrenAstToHir.nearest (nearestFirst scope) name).map Int.ofNat
      = match resolve_local scope name with
        | some level => some (↑(length _ scope) - 1 - level)
        | none => none := by
  induction scope with
  | Empty => simp [nearestFirst, FrenAstToHir.nearest, resolve_local]
  | Extend earlier newest ih =>
    simp only [nearestFirst, FrenAstToHir.nearest, resolve_local, length]
    split
    · simp
    · cases found : resolve_local earlier name with
      | none => simp [found] at ih; simp [ih]
      | some level =>
        simp [found] at ih
        obtain ⟨index, hi, eq⟩ := ih
        simp [hi]
        omega

/-! ## Tables -/

theorem resolve_params_length (env : Env) (params : Snoc Param) (ctx : Snoc Ty)
    (h : resolve_params env params = some ctx) :
    length _ ctx = length _ (param_names params) := by
  induction params generalizing ctx with
  | Empty => simp [resolve_params] at h; simp [← h, param_names, length]
  | Extend earlier param ih =>
    simp only [resolve_params] at h
    split at h
    · rename_i earlierCtx ty he _
      simp at h
      simp [← h, param_names, length, ih earlierCtx he]
    · simp at h

theorem item_target_cases (symb : Snoc Entry) (item : Fren.Seq String) :
    item_target symb item = none ∨ item_target symb item = some (.Item item) := by
  simp only [item_target]
  split <;> simp

theorem head_local (env : Env) (scope : Snoc String) (name : String) (level : Int)
    (h : head env scope name = some (.Local level)) : resolve_local scope name = some level := by
  simp only [head] at h
  split at h
  · rename_i found eq
    simp at h
    simp [eq, h]
  · split at h
    · rename_i target eq
      rcases item_target_cases env.symb (child (module_of env) name) with none | item
      · simp [none] at eq
      · simp [item] at eq
        simp [← eq] at h
    · split at h <;> simp at h

theorem descend_not_local (env : Env) (target : Target) (name : String) (level : Int) :
    descend env target name ≠ some (.Local level) := by
  simp only [descend]
  split
  · simp
  · rcases item_target_cases env.symb (child (module_of env) name) with h | h <;> simp [h]
  · split
    · rename_i item _ _ _
      rcases item_target_cases env.symb (child item name) with h | h <;> simp [h]
    · simp

theorem path_target_local (env : Env) (scope : Snoc String) (path : Path) (level : Int)
    (h : path_target env scope path = some (.Local level)) :
    0 ≤ level ∧ level < length _ scope := by
  cases path with
  | Name name =>
    simp only [path_target] at h
    exact local_lt scope name level (head_local env scope name level h)
  | Member qualifier name =>
    simp only [path_target] at h
    split at h
    · exact absurd h (descend_not_local env _ name level)
    · simp at h

theorem layer_local (env : Env) (scope : Snoc String) (form : SrcF Int) (level : Int)
    (h : resolve_layer Int env scope form = some (.Local level)) :
    0 ≤ level ∧ level < length _ scope := by
  cases form with
  | Name path =>
    simp only [resolve_layer, value_form] at h
    split at h
    · rename_i found eq
      simp at h
      exact path_target_local env scope path level (by simpa [h] using eq)
    · split at h <;> simp at h
    · simp at h
  | Call path args => simp only [resolve_layer] at h; split at h <;> simp at h
  | Let name annotation value body => simp only [resolve_layer] at h; split at h <;> simp at h
  | Match scrutinee arms => simp only [resolve_layer] at h; split at h <;> simp at h
  | _ => simp [resolve_layer] at h

theorem rows_aligned (env : Env) (rows : Snoc SrcRow) (forms : Snoc (ExprF Int))
    (h : resolve_rows env rows = some forms) : length _ forms = length _ rows := by
  induction rows generalizing forms with
  | Empty => simp [resolve_rows] at h; simp [← h, length]
  | Extend earlier row ih =>
    simp only [resolve_rows] at h
    split at h
    · rename_i resolved form he _
      split at h
      · simp at h
        simp [← h, length, ih resolved he]
      · simp at h
    · simp at h

theorem rows_scoped (env : Env) (rows : Snoc SrcRow) (forms : Snoc (ExprF Int))
    (position : Int) (row : SrcRow) (level : Int)
    (h : resolve_rows env rows = some forms) (hr : lookup _ rows position = some row)
    (hf : lookup _ forms position = some (.Local level)) :
    0 ≤ level ∧ level < length _ row.scope := by
  induction rows generalizing forms with
  | Empty => simp [lookup] at hr
  | Extend earlier last ih =>
    simp only [resolve_rows] at h
    split at h
    · rename_i resolved form he hl
      split at h
      · simp at h
        subst h
        have aligned := rows_aligned env earlier resolved he
        simp only [lookup, aligned] at hr hf
        split at hr
        · rename_i at_last
          simp [at_last] at hf
          simp at hr
          subst hr
          exact layer_local env last.scope last.form level (by simpa [hf] using hl)
        · rename_i not_last
          simp [not_last] at hf
          exact ih resolved he hr hf
      · simp at h
    · simp at h

/-! ## Weakening -/

/-- The shift of a target: only a local has a level. -/
def shiftTarget (cutoff : Int) : Target → Target
  | .Local level => .Local (shift level cutoff)
  | target => target

theorem head_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra name : String)
    (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope) (ne : name ≠ extra) :
    head env (insert_name scope cutoff extra) name
      = (head env scope name).map (shiftTarget cutoff) := by
  simp only [head, local_weakens scope cutoff extra name h0 h1 ne]
  cases resolve_local scope name with
  | some level => simp [shiftTarget]
  | none =>
    rcases item_target_cases env.symb (child (module_of env) name) with h | h
    · simp only [h]; split <;> simp [shiftTarget]
    · simp [h, shiftTarget]

theorem descend_shift (env : Env) (target : Target) (cutoff : Int) (name : String) :
    descend env (shiftTarget cutoff target) name
      = (descend env target name).map (shiftTarget cutoff) := by
  cases target with
  | Local level => simp [descend, shiftTarget]
  | Module =>
    simp only [descend, shiftTarget]
    rcases item_target_cases env.symb (child (module_of env) name) with h | h <;> simp [h, shiftTarget]
  | Item item =>
    simp only [descend, shiftTarget]
    split
    · rcases item_target_cases env.symb (child item name) with h | h <;> simp [h, shiftTarget]
    · simp

theorem path_target_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    path_target env (insert_name scope cutoff extra) path
      = (path_target env scope path).map (shiftTarget cutoff) := by
  induction path with
  | Name name => exact head_weakens env scope cutoff extra name h0 h1 (by simpa [path_head] using ne)
  | Member qualifier name ih =>
    simp only [path_target, ih (by simpa [path_head] using ne)]
    cases path_target env scope qualifier with
    | none => simp
    | some target => simp [descend_shift]

theorem value_form_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    value_form Int env (insert_name scope cutoff extra) path
      = shifted_form (value_form Int env scope path) cutoff := by
  simp only [value_form, path_target_weakens env scope cutoff extra path h0 h1 ne]
  cases path_target env scope path with
  | none => simp [shifted_form]
  | some target =>
    cases target with
    | Local level => simp [shiftTarget, shifted_form, shift_form]
    | Module => simp [shiftTarget, shifted_form]
    | Item item =>
      simp only [Option.map, shiftTarget]
      split <;> simp [shifted_form, shift_form]

theorem callee_item_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    callee_item env (insert_name scope cutoff extra) path = callee_item env scope path := by
  simp only [callee_item, path_target_weakens env scope cutoff extra path h0 h1 ne]
  cases path_target env scope path with
  | none => simp
  | some target => cases target <;> simp [shiftTarget]

theorem pattern_item_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (path : Path) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : path_head path ≠ extra) :
    pattern_item env (insert_name scope cutoff extra) path = pattern_item env scope path := by
  simp only [pattern_item, path_target_weakens env scope cutoff extra path h0 h1 ne]
  cases path_target env scope path with
  | none => simp
  | some target => cases target <;> simp [shiftTarget]

theorem resolve_arms_weakens (env : Env) (scope : Snoc String) (cutoff : Int) (extra : String)
    (arms : Snoc (SrcArm Int)) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : arms_mention? arms extra = false) :
    resolve_arms Int env (insert_name scope cutoff extra) arms = resolve_arms Int env scope arms := by
  induction arms with
  | Empty => simp [resolve_arms]
  | Extend earlier arm ih =>
    simp [arms_mention?] at ne
    simp only [resolve_arms, ih ne.2,
      pattern_item_weakens env scope cutoff extra arm.pattern h0 h1 ne.1]

theorem layer_weakens (env : Env) (scope : Snoc String) (form : SrcF Int) (cutoff : Int)
    (extra : String) (h0 : 0 ≤ cutoff) (h1 : cutoff ≤ length _ scope)
    (ne : mentions? form extra = false) :
    resolve_layer Int env (insert_name scope cutoff extra) form
      = shifted_form (resolve_layer Int env scope form) cutoff := by
  cases form with
  | Name path =>
    simp [mentions?, fren_spec] at ne
    simpa [resolve_layer] using value_form_weakens env scope cutoff extra path h0 h1 ne
  | Call path args =>
    simp [mentions?, fren_spec] at ne
    simp only [resolve_layer, callee_item_weakens env scope cutoff extra path h0 h1 ne]
    cases callee_item env scope path <;> simp [shifted_form, shift_form]
  | Match scrutinee arms =>
    simp [mentions?, fren_spec] at ne
    simp only [resolve_layer, resolve_arms_weakens env scope cutoff extra arms h0 h1 ne]
    cases resolve_arms Int env scope arms <;> simp [shifted_form, shift_form]
  | Let name annotation value body =>
    simp only [resolve_layer]
    cases resolve_annotation env annotation <;> simp [shifted_form, shift_form]
  | _ => simp [resolve_layer, shifted_form, shift_form]

/-! ## Bound items -/

theorem value_form_constructor (env : Env) (scope : Snoc String) (path : Path)
    (item : Fren.Seq String) (h : value_form Int env scope path = some (.Constructor item)) :
    ∃ owner, entry env.symb item = some (.Constructor owner) := by
  simp only [value_form] at h
  split at h
  · simp at h
  · split at h
    · rename_i found _ _ owner eq
      simp at h
      exact ⟨owner, by simpa [h] using eq⟩
    · simp at h
  · simp at h

theorem callee_item_function (env : Env) (scope : Snoc String) (path : Path)
    (item : Fren.Seq String) (h : callee_item env scope path = some item) :
    ∃ sig, entry env.symb item = some (.Function sig) := by
  simp only [callee_item] at h
  split at h
  · split at h
    · rename_i found _ _ sig eq
      simp at h
      exact ⟨sig, by simpa [h] using eq⟩
    · simp at h
  · simp at h

theorem pattern_item_constructor (env : Env) (scope : Snoc String) (path : Path)
    (item : Fren.Seq String) (h : pattern_item env scope path = some item) :
    ∃ owner, entry env.symb item = some (.Constructor owner) := by
  simp only [pattern_item] at h
  split at h
  · split at h
    · rename_i found _ _ owner eq
      simp at h
      exact ⟨owner, by simpa [h] using eq⟩
    · simp at h
  · simp at h

theorem layer_constructor (env : Env) (scope : Snoc String) (form : SrcF Int)
    (item : Fren.Seq String) (h : resolve_layer Int env scope form = some (.Constructor item)) :
    ∃ owner, entry env.symb item = some (.Constructor owner) := by
  cases form with
  | Name path => exact value_form_constructor env scope path item (by simpa [resolve_layer] using h)
  | Call path args => simp only [resolve_layer] at h; split at h <;> simp at h
  | Let name annotation value body => simp only [resolve_layer] at h; split at h <;> simp at h
  | Match scrutinee arms => simp only [resolve_layer] at h; split at h <;> simp at h
  | _ => simp [resolve_layer] at h

theorem layer_callee (env : Env) (scope : Snoc String) (form : SrcF Int)
    (item : Fren.Seq String) (args : Snoc Int)
    (h : resolve_layer Int env scope form = some (.Call item args)) :
    ∃ sig, entry env.symb item = some (.Function sig) := by
  cases form with
  | Name path =>
    simp only [resolve_layer, value_form] at h
    split at h
    · simp at h
    · split at h <;> simp at h
    · simp at h
  | Call path args =>
    simp only [resolve_layer] at h
    split at h
    · rename_i found eq
      simp at h
      exact callee_item_function env scope path item (by simpa [h.1] using eq)
    · simp at h
  | Let name annotation value body => simp only [resolve_layer] at h; split at h <;> simp at h
  | Match scrutinee arms => simp only [resolve_layer] at h; split at h <;> simp at h
  | _ => simp [resolve_layer] at h

end Spec.Language.NamesAndScope

pub mod spec::names

open spec.types spec.names in
impl local_binding_proof: local_binding for (scope : Snoc String) (name : String)
    (level other : Int) {
  scope := scope, name := name, level := level, other := other, holds? := true
} by
  intro scope name level other _
  simp only [local_binding.ensures, local_binding.ensure.output, local_binding.ensure.bound,
    local_binding.ensure.nearest, local_binding.ensure.complete]
  exact ⟨trivial, Spec.Language.NamesAndScope.local_bound scope name level,
    fun h => Spec.Language.NamesAndScope.local_nearest scope name level other h.1 h.2,
    Spec.Language.NamesAndScope.local_complete scope name other⟩

open spec.types spec.names in
impl local_weakening_proof: local_weakening for (scope : Snoc String) (cutoff : Int)
    (extra name : String) {
  scope := scope, cutoff := cutoff, extra := extra, name := name, holds? := true
} by
  intro scope cutoff extra name _
  simp only [local_weakening.ensures, local_weakening.ensure.output, local_weakening.ensure.shifted]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.NamesAndScope.local_weakens scope cutoff extra name h.1.1 h.1.2 h.2

open spec.types spec.names in
impl nearest_index_production: nearest_index for (scope : Snoc String) (name : String) {
  scope := scope, name := name,
  index := (FrenAstToHir.nearest (Spec.Language.NamesAndScope.nearestFirst scope) name).map Int.ofNat
} by
  intro scope name _
  simp only [nearest_index.ensures, nearest_index.ensure.converse]
  rw [Spec.Language.NamesAndScope.nearest_converse]
  cases resolve_local scope name <;> simp [fren_spec]

open spec.names in
impl same_name_production: same_name for (first second : String) {
  first := first, second := second, same? := FrenAstToHir.sameName first second
} by
  intro first second _
  simp [same_name.ensures, same_name.ensure.meaning, FrenAstToHir.sameName]

open spec.types spec.names in
impl parameters_parallel_proof: parameters_parallel for (env : Env) (params : Snoc Param)
    (result : spec.names.TypeName) (sig : Sig) {
  env := env, params := params, result := result, sig := sig, holds? := true
} by
  intro env params result sig _
  simp only [parameters_parallel.ensures, parameters_parallel.ensure.output,
    parameters_parallel.ensure.parallel]
  refine ⟨trivial, ?_⟩
  intro h
  simp only [signature] at h
  split at h
  · rename_i ctx ty hc _
    simp at h
    simp [← h, Spec.Language.NamesAndScope.resolve_params_length env params ctx hc]
  · simp at h

open spec.types spec.names in
impl names_worked_examples_proof: worked_examples { holds? := true } by
  intro _
  simp only [spec.names.worked_examples.ensures, spec.names.worked_examples.ensure.output,
    spec.names.worked_examples.ensure.valid]
  refine ⟨trivial, ?_⟩
  decide

open spec.types spec.names in
impl names_table_scoping_proof: table_scoping for (env : Env) (rows : Snoc SrcRow)
    (forms : Snoc (ExprF Int)) (position : Int) (row : SrcRow) (level : Int) {
  env := env, rows := rows, forms := forms, position := position, row := row, level := level,
  holds? := true
} by
  intro env rows forms position row level _
  simp only [spec.names.table_scoping.ensures, spec.names.table_scoping.ensure.output,
    spec.names.table_scoping.ensure.aligned, spec.names.table_scoping.ensure.in_scope]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    rw [Spec.Language.NamesAndScope.rows_aligned env rows forms h]
  · intro h
    exact Spec.Language.NamesAndScope.rows_scoped env rows forms position row level h.1.1 h.1.2 h.2

open spec.types spec.names in
impl names_rejected_proof: rejected for (parent : Fren.Seq String) (module name variant : String)
    (first second : Snoc String) (ty : spec.names.TypeName) (body : Snoc SrcRow) {
  parent := parent, module := module, name := name, variant := variant, first := first,
  second := second, ty := ty, body := body, holds? := true
} by
  intro parent module name variant first second ty body _
  simp [spec.names.rejected.ensures, spec.names.rejected.ensure.output,
    spec.names.rejected.ensure.duplicate, spec.names.rejected.ensure.repeated_variant,
    spec.names.rejected.ensure.reserved_name, spec.names.rejected.ensure.repeated_parameter, collect, names_ok?, distinct?, item_names, decl_name,
    resolve_local, decl_names_ok?, decls_names_ok?, param_names, reserved?, fren_spec]

open spec.types spec.names in
impl names_layer_weakening_proof: layer_weakening for (env : Env) (scope : Snoc String)
    (form : SrcF Int) (cutoff : Int) (extra : String) {
  env := env, scope := scope, form := form, cutoff := cutoff, extra := extra, holds? := true
} by
  intro env scope form cutoff extra _
  simp only [spec.names.layer_weakening.ensures, spec.names.layer_weakening.ensure.output,
    spec.names.layer_weakening.ensure.shifted]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.NamesAndScope.layer_weakens env scope form cutoff extra h.1.1 h.1.2
    (Bool.eq_false_iff.mpr h.2)

open spec.types spec.names in
impl bound_items_proof: bound_items for (env : Env) (scope : Snoc String) (form : SrcF Int)
    (path : Path) (args : Snoc Int) (item : Fren.Seq String) {
  env := env, scope := scope, form := form, path := path, args := args, item := item,
  holds? := true
} by
  intro env scope form path args item _
  simp only [bound_items.ensures, bound_items.ensure.output, bound_items.ensure.constructor,
    bound_items.ensure.function, bound_items.ensure.pattern]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨owner, eq⟩ := Spec.Language.NamesAndScope.layer_constructor env scope form item h
    simp [eq, fren_spec]
  · intro h
    obtain ⟨sig, eq⟩ := Spec.Language.NamesAndScope.layer_callee env scope form item args h
    simp [eq, fren_spec]
  · intro h
    obtain ⟨owner, eq⟩ := Spec.Language.NamesAndScope.pattern_item_constructor env scope path item h
    simp [eq, fren_spec]

open spec.types spec.names in
impl siblings_proof: siblings for (rows : Snoc SrcRow) (scope : Snoc String) (name : String)
    (annotation : Option spec.names.TypeName) (op : BinaryOp) (first second : Int) (row : SrcRow) {
  rows := rows, scope := scope, name := name, annotation := annotation, op := op,
  first := first, second := second, row := row, holds? := true
} by
  intro rows scope name annotation op first second row _
  simp only [siblings.ensures, siblings.ensure.output, siblings.ensure.value,
    siblings.ensure.operand]
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    have c := h.1
    simp [children_scoped?, has_scope?, h.2, fren_spec] at c
    exact c.1
  · intro h
    have c := h.1
    simp [children_scoped?, has_scope?, h.2, fren_spec] at c
    exact c.2

pub mod spec::resolution

interp resolved := fun env scope rows => (spec.names.resolve_expression env scope rows).getD default
interp resolves? := fun env scope rows forms =>
    decide (spec.names.resolve_expression env scope rows = some forms) by
  intro env scope rows forms
  simp only [spec.resolution.resolves?.function, spec.resolution.resolves?.aligned,
    spec.resolution.resolved]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp at h; simp [h]
  · simp at h
    cases rows with
    | Empty => simp [spec.names.resolve_expression] at h
    | Extend earlier root =>
      simp only [spec.names.resolve_expression] at h
      split at h
      · exact Spec.Language.NamesAndScope.rows_aligned env _ forms h
      · simp at h

set_option fren.requireEvidence "trusted" in
#fren_trace
