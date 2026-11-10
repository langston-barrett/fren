import Spec.Compiler.Thir

/-!
# Admission and the type pass

The walking checker `FrenHirToThir.infer` is sound for the declarative
judgments of the THIR chapter on every expression in which each call has a
name as its callee. A successful traversal of such an expression gives its
meaning (`HasValue` or `HasCallable`), its postorder occurrence table
(`OccurrenceOrder`), and both directions of the correspondence between the
table and the expression's descendants.

`HasValue.call` types a call only when its callee is a name, while the
checker also follows a callee through parentheses. The parser writes no other
callee, but no theorem says so yet. `NamedCallees` states that fact, and the
theorems for whole programs take it as their one hypothesis. Conversely,
`OccurrenceTyping` implies it.
-/

namespace Spec.Compiler.Thir
open FrenModule FrenAst FrenHirToThir

/-! ## Equality of tokens

The derived Boolean equality of a token decides equality. The checker compares
a reference's context with the typed context by it. -/

theorem role_eq {a b : Role} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem kind_eq {a b : LexicalKind} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem file_eq {a b : FrenSource.FileId} (h : (a == b) = true) : a = b := by
  cases a; cases b
  simp only [BEq.beq, FrenSource.instBEqFileId.beq, decide_eq_true_eq] at h
  rw [h]

theorem span_eq {a b : FrenSource.Span} (h : (a == b) = true) : a = b := by
  cases a; cases b
  simp only [BEq.beq, FrenSource.instBEqSpan.beq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hf, hs, he⟩ := h
  rw [file_eq hf, hs, he]

theorem token_eq {a b : Token} (h : (a == b) = true) : a = b := by
  cases a; cases b
  simp only [BEq.beq, instBEqToken.beq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, ht, hsp, hk⟩ := h
  rw [hs, ht, span_eq hsp, kind_eq hk]

theorem tokens_eq : ∀ {a b : List Token}, (a == b) = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [List.cons_beq_cons, Bool.and_eq_true] at h
    rw [token_eq h.1, tokens_eq h.2]

/-! ## Results of the checker's monad -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem value_ok {res : Inferred} {span : FrenSource.Span} {ty : FrenExpr.Ty}
    (h : res.value span = .ok ty) : res.type = .value ty := by
  unfold Inferred.value at h
  split at h
  · rename_i t ht
    cases h
    exact ht
  · cases h

theorem reference_ok {input : Resolved} {token : Token} {role : Role} {ref : Reference}
    (h : reference input token role = .ok ref) :
    input.referenceAt token.slice = some ref ∧ ref.role = role := by
  unfold reference at h
  split at h
  · rename_i found hf
    split at h
    · rename_i same
      cases h
      exact ⟨hf, role_eq same⟩
    · cases h
  · cases h

theorem signatureAt_id {sigs : Array Signature} {id : FrenBase.ItemId} {sig : Signature}
    (h : signatureAt sigs id = some sig) : sig.id = id := by
  unfold signatureAt at h
  have found := Array.find?_some h
  exact (FrenBase.ItemId.beq_eq_true_iff _ _).mp found

theorem exists_mem_of_isEmpty_false {α : Type} {xs : Array α} (h : xs.isEmpty = false) :
    ∃ x, x ∈ xs.toList := by
  obtain ⟨l⟩ := xs
  cases l with
  | nil => cases h
  | cons x _ => exact ⟨x, List.mem_cons_self⟩

/-! ## Uniqueness of the declarative judgments -/

theorem selects_target {r : Resolved} {ctx : TypeContext} {p : Path} {role : Role}
    {a b : Target} (ha : Selects r ctx p role a) (hb : Selects r ctx p role b) : a = b := by
  obtain ⟨ra, hra, _, rfl, _⟩ := ha
  obtain ⟨rb, hrb, _, rfl, _⟩ := hb
  rw [hra] at hrb
  cases hrb
  rfl

theorem hasValue_unique {r : Resolved} {sigs : Array Signature} {ctx : TypeContext}
    {e : Expr} {a b : FrenExpr.Ty}
    (ha : HasValue r sigs ctx e a) (hb : HasValue r sigs ctx e b) : a = b := by
  induction ha generalizing b with
  | bool => cases hb; rfl
  | integer => cases hb; rfl
  | «local» sel ht =>
    cases hb with
    | «local» sel' ht' =>
      cases selects_target sel sel'
      unfold FrenBase.Binding.HasType at ht ht'
      rw [ht] at ht'
      cases ht'
      rfl
    | constructor sel' _ => cases selects_target sel sel'
  | constructor sel ct =>
    cases hb with
    | «local» sel' _ => cases selects_target sel sel'
    | constructor sel' ct' =>
      cases selects_target sel sel'
      rw [ct] at ct'
      cases ct'
      rfl
  | paren _ ih => cases hb with | paren h => exact ih h
  | unary _ hu ih =>
    cases hb with
    | unary h hu' =>
      cases ih h
      rw [hu] at hu'
      cases hu'
      rfl
  | binary _ _ ho ihl ihr =>
    cases hb with
    | binary hl hr ho' =>
      cases ihl hl
      cases ihr hr
      rw [ho] at ho'
      cases ho'
      rfl
  | call sel sa _ _ _ =>
    cases hb with
    | call sel' sa' _ _ =>
      have same := selects_target sel sel'
      injection same with same
      rw [same, sa'] at sa
      cases sa
      rfl
  | ifE _ _ _ _ ihy _ => cases hb with | ifE _ hy _ => exact ihy hy
  | letE _ _ _ ihv ihb =>
    cases hb with
    | letE hv _ hb' =>
      cases ihv hv
      exact ihb hb'
  | matchE _ ne _ _ _ ih =>
    cases hb with
    | matchE _ _ _ bodies =>
      obtain ⟨arm, mem⟩ := exists_mem_of_isEmpty_false ne
      exact ih arm mem (bodies arm mem)

/-! ## Descendants -/

theorem atContext_prepend {r : Resolved} {sigs : Array Signature} {ctx cc c' : TypeContext}
    {e ce e' : Expr} (step : ChildContext r sigs ctx e cc ce)
    (rest : AtContext r sigs cc ce c' e') : AtContext r sigs ctx e c' e' := by
  induction rest with
  | root => exact .child .root step
  | child _ next ih => exact .child ih next

theorem atContext_cases {r : Resolved} {sigs : Array Signature} {ctx c' : TypeContext}
    {e e' : Expr} (h : AtContext r sigs ctx e c' e') :
    (c' = ctx ∧ e' = e) ∨
      ∃ cc ce, ChildContext r sigs ctx e cc ce ∧ AtContext r sigs cc ce c' e' := by
  induction h with
  | root => exact .inl ⟨rfl, rfl⟩
  | child _ step ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨cc, ce, first, rest⟩
    · exact .inr ⟨_, _, step, .root⟩
    · exact .inr ⟨cc, ce, first, .child rest step⟩

theorem written_child {r : Resolved} {sigs : Array Signature} {ctx : TypeContext} {e : Expr}
    {children : List (TypeContext × Expr)} (wc : WrittenChildren r sigs ctx e children) :
    ∀ ch ∈ children, ChildContext r sigs ctx e ch.1 ch.2 := by
  intro ch mem
  cases wc with
  | bool => cases mem
  | integer => cases mem
  | name => cases mem
  | paren => cases List.mem_singleton.mp mem; exact .paren
  | unary => cases List.mem_singleton.mp mem; exact .unary
  | binary =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact .binaryLeft
    · exact .binaryRight
  | call =>
    simp only [List.mem_cons, List.mem_map] at mem
    rcases mem with rfl | ⟨a, ha, rfl⟩
    · exact .callee
    · exact .argument ha
  | ifE =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact .condition
    · exact .thenBranch
    · exact .elseBranch
  | letE hv =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact .letValue
    · exact .letBody hv
  | matchE =>
    simp only [List.mem_cons, List.mem_map] at mem
    rcases mem with rfl | ⟨a, ha, rfl⟩
    · exact .scrutinee
    · exact .armBody ha

theorem child_written {r : Resolved} {sigs : Array Signature} {ctx cc : TypeContext}
    {e ce : Expr} {children : List (TypeContext × Expr)}
    (wc : WrittenChildren r sigs ctx e children) (step : ChildContext r sigs ctx e cc ce) :
    (cc, ce) ∈ children := by
  cases step with
  | paren => cases wc; exact List.mem_singleton.mpr rfl
  | unary => cases wc; exact List.mem_singleton.mpr rfl
  | binaryLeft => cases wc; exact List.mem_cons_self
  | binaryRight => cases wc; exact List.mem_cons_of_mem _ List.mem_cons_self
  | callee => cases wc; exact List.mem_cons_self
  | argument ha => cases wc; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, ha, rfl⟩)
  | condition => cases wc; exact List.mem_cons_self
  | thenBranch => cases wc; exact List.mem_cons_of_mem _ List.mem_cons_self
  | elseBranch =>
    cases wc; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | letValue => cases wc; exact List.mem_cons_self
  | letBody hv =>
    cases wc with
    | letE hv' =>
      cases hasValue_unique hv hv'
      exact List.mem_cons_of_mem _ List.mem_cons_self
  | scrutinee => cases wc; exact List.mem_cons_self
  | armBody ha => cases wc; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, ha, rfl⟩)

/-! ## Occurrence tables -/

/-- The table of one expression: its postorder, and both directions of the
correspondence between its entries and the expression's descendants. -/
def Table (r : Resolved) (sigs : Array Signature) (ctx : TypeContext) (e : Expr)
    (occs : List TypedOccurrence) : Prop :=
  OccurrenceOrder r sigs ctx e occs ∧
  (∀ o ∈ occs, AtContext r sigs ctx e o.context o.expression ∧ OccurrenceMeaning r sigs o) ∧
  (∀ c' e', AtContext r sigs ctx e c' e' →
    ∃ o ∈ occs, o.expression = e' ∧ o.context = c' ∧ OccurrenceMeaning r sigs o)

/-- The concatenated tables of a list of sibling expressions. -/
def Forest (r : Resolved) (sigs : Array Signature) (children : List (TypeContext × Expr))
    (occs : List TypedOccurrence) : Prop :=
  OccurrenceForest r sigs children occs ∧
  (∀ o ∈ occs, ∃ ch ∈ children,
    AtContext r sigs ch.1 ch.2 o.context o.expression ∧ OccurrenceMeaning r sigs o) ∧
  (∀ ch ∈ children, ∀ c' e', AtContext r sigs ch.1 ch.2 c' e' →
    ∃ o ∈ occs, o.expression = e' ∧ o.context = c' ∧ OccurrenceMeaning r sigs o)

theorem forest_nil {r : Resolved} {sigs : Array Signature} : Forest r sigs [] [] := by
  refine ⟨.nil, ?_, ?_⟩
  · intro _ h; cases h
  · intro _ h; cases h

theorem occurrenceForest_snoc {r : Resolved} {sigs : Array Signature} {c : TypeContext}
    {e : Expr} {t : List TypedOccurrence} (last : OccurrenceOrder r sigs c e t) :
    ∀ {children : List (TypeContext × Expr)} {occs : List TypedOccurrence},
      OccurrenceForest r sigs children occs →
      OccurrenceForest r sigs (children ++ [(c, e)]) (occs ++ t)
  | [], _, h => by
    cases h
    have := OccurrenceForest.cons last .nil
    rwa [List.append_nil] at this
  | _ :: _, _, h => by
    cases h with
    | cons first rest =>
      rw [List.append_assoc]
      exact .cons first (occurrenceForest_snoc last rest)

theorem forest_snoc {r : Resolved} {sigs : Array Signature} {c : TypeContext} {e : Expr}
    {t occs : List TypedOccurrence} {children : List (TypeContext × Expr)}
    (forest : Forest r sigs children occs) (last : Table r sigs c e t) :
    Forest r sigs (children ++ [(c, e)]) (occs ++ t) := by
  refine ⟨occurrenceForest_snoc last.1 forest.1, ?_, ?_⟩
  · intro o mem
    rcases List.mem_append.mp mem with mem | mem
    · obtain ⟨ch, hch, h⟩ := forest.2.1 o mem
      exact ⟨ch, List.mem_append_left _ hch, h⟩
    · exact ⟨(c, e), List.mem_append_right _ (List.mem_singleton.mpr rfl), last.2.1 o mem⟩
  · intro ch mem c' e' at'
    rcases List.mem_append.mp mem with mem | mem
    · obtain ⟨o, ho, h⟩ := forest.2.2 ch mem c' e' at'
      exact ⟨o, List.mem_append_left _ ho, h⟩
    · cases List.mem_singleton.mp mem
      obtain ⟨o, ho, h⟩ := last.2.2 c' e' at'
      exact ⟨o, List.mem_append_right _ ho, h⟩

theorem table_node {r : Resolved} {sigs : Array Signature} {ctx : TypeContext} {e : Expr}
    {children : List (TypeContext × Expr)} {occs : List TypedOccurrence} {ty : ExpressionType}
    (wc : WrittenChildren r sigs ctx e children) (forest : Forest r sigs children occs)
    (meaning : OccurrenceMeaning r sigs ⟨e, ctx, ty⟩) :
    Table r sigs ctx e (occs ++ [⟨e, ctx, ty⟩]) := by
  refine ⟨.node wc forest.1, ?_, ?_⟩
  · intro o mem
    rcases List.mem_append.mp mem with mem | mem
    · obtain ⟨ch, hch, at', m⟩ := forest.2.1 o mem
      exact ⟨atContext_prepend (written_child wc ch hch) at', m⟩
    · cases List.mem_singleton.mp mem
      exact ⟨.root, meaning⟩
  · intro c' e' at'
    rcases atContext_cases at' with ⟨rfl, rfl⟩ | ⟨cc, ce, step, rest⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl, rfl, meaning⟩
    · obtain ⟨o, ho, h⟩ := forest.2.2 _ (child_written wc step) c' e' rest
      exact ⟨o, List.mem_append_left _ ho, h⟩

/-! ## Loops of the checker -/

/-- A successful loop over a list keeps an invariant that every successful
step re-establishes for the elements read so far. -/
theorem forIn_invariant {ε α σ : Type} (P : List α → σ → Prop) (f : α → σ → Except ε (ForInStep σ)) :
    ∀ (xs pre : List α) (init out : σ), forIn xs init f = .ok out → P pre init →
      (∀ done x rest s next, pre ++ xs = done ++ x :: rest → P done s → f x s = .ok next →
        ∃ s', next = .yield s' ∧ P (done ++ [x]) s') →
      P (pre ++ xs) out
  | [], pre, init, out, h, h0, _ => by
    cases h
    rwa [List.append_nil]
  | x :: xs, pre, init, out, h, h0, step => by
    rw [List.forIn_cons] at h
    obtain ⟨next, hx, hrest⟩ := bind_ok h
    obtain ⟨s', rfl, hs⟩ := step pre x xs init next rfl h0 hx
    have := forIn_invariant P f xs (pre ++ [x]) s' out hrest hs (fun done y rest s next eq =>
      step done y rest s next (by rw [← eq, List.append_assoc]; rfl))
    rwa [List.append_assoc] at this

/-- A successful loop over `[:n]` keeps an invariant indexed by the count of
completed steps. -/
theorem forIn_range_invariant {ε σ : Type} (P : Nat → σ → Prop) (n : Nat)
    (f : Nat → σ → Except ε (ForInStep σ)) (init out : σ)
    (h : forIn [:n] init f = .ok out) (h0 : P 0 init)
    (step : ∀ k s next, k < n → P k s → f k s = .ok next →
      ∃ s', next = .yield s' ∧ P (k + 1) s') : P n out := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have size : List.range' ([:n] : Std.Legacy.Range).start ([:n] : Std.Legacy.Range).size
      ([:n] : Std.Legacy.Range).step = List.range' 0 n := by
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  rw [size] at h
  have inv := forIn_invariant (fun pre s => P pre.length s) f (List.range' 0 n) [] init out h h0
    (fun done x rest s next eq hp hx => by
      have len := congrArg List.length eq
      have at' := congrArg (fun l => l[done.length]?) eq
      simp only [List.nil_append, List.length_range', List.length_append, List.length_cons,
        Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, getElem?_pos, Std.le_refl,
        List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero] at len at'
      obtain ⟨_, value⟩ := List.getElem?_eq_some_iff.mp at'
      rw [List.getElem_range'] at value
      have index : x = done.length := by omega
      subst index
      rw [List.length_append]
      exact step _ s next (by omega) hp hx)
  simpa only [List.nil_append, List.length_range'] using inv

/-! ## Soundness of the checker's traversal -/

/-- Every call below the expression has a name as its callee. -/
def Named (r : Resolved) (sigs : Array Signature) (ctx : TypeContext) (e : Expr) : Prop :=
  ∀ c' f o args commas c, AtContext r sigs ctx e c' (.call f o args commas c) →
    ∃ path, f = .name path

theorem Named.child {r : Resolved} {sigs : Array Signature} {ctx cc : TypeContext} {e ce : Expr}
    (named : Named r sigs ctx e) (step : ChildContext r sigs ctx e cc ce) :
    Named r sigs cc ce :=
  fun c' f o args commas c at' => named c' f o args commas c (atContext_prepend step at')

/-- What a successful traversal of `e` in `ctx` establishes. -/
def Sound (r : Resolved) (sigs : Array Signature) (ctx : TypeContext) (e : Expr)
    (res : Inferred) : Prop :=
  OccurrenceMeaning r sigs ⟨e, ctx, res.type⟩ ∧ Table r sigs ctx e res.occurrences.toList

theorem Sound.value {r : Resolved} {sigs : Array Signature} {ctx : TypeContext} {e : Expr}
    {res : Inferred} {ty : FrenExpr.Ty} (s : Sound r sigs ctx e res)
    (h : res.type = .value ty) : HasValue r sigs ctx e ty := by
  have m := s.1
  rw [h] at m
  exact m

theorem pure_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : a = b := by
  cases h
  rfl

theorem node_sound {r : Resolved} {sigs : Array Signature} {ctx : TypeContext} {e : Expr}
    {children : List (TypeContext × Expr)} {occs : Array TypedOccurrence} {ty : ExpressionType}
    (wc : WrittenChildren r sigs ctx e children) (forest : Forest r sigs children occs.toList)
    (meaning : OccurrenceMeaning r sigs ⟨e, ctx, ty⟩) :
    Sound r sigs ctx e ⟨ty, occs.push ⟨e, ctx, ty⟩⟩ := by
  refine ⟨meaning, ?_⟩
  rw [Array.toList_push]
  exact table_node wc forest meaning

theorem forest_one {r : Resolved} {sigs : Array Signature} {c : TypeContext} {e : Expr}
    {t : List TypedOccurrence} (a : Table r sigs c e t) : Forest r sigs [(c, e)] t :=
  forest_snoc forest_nil a

theorem localType_some {ctx : TypeContext} {i : Nat} {ty : FrenExpr.Ty}
    (h : localType ctx i = some ty) : ∃ token, FrenBase.Binding.HasType ctx i (token, ty) := by
  unfold localType at h
  obtain ⟨⟨token, ty'⟩, found, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨token, found⟩

theorem meaning_paren {r : Resolved} {sigs : Array Signature} {ctx : TypeContext} {e : Expr}
    {o c : Token} {ty : ExpressionType} (m : OccurrenceMeaning r sigs ⟨e, ctx, ty⟩) :
    OccurrenceMeaning r sigs ⟨.paren o e c, ctx, ty⟩ := by
  cases ty with
  | value _ => exact HasValue.paren m
  | callable _ => exact HasCallable.paren m

/-- The induction hypothesis of soundness, for one unit less of depth. -/
abbrev Below (r : Resolved) (sigs : Array Signature) (fuel : Nat) : Prop :=
  ∀ ctx e cal res, infer fuel r sigs ctx e cal = .ok res → Named r sigs ctx e →
    Sound r sigs ctx e res

theorem name_sound {r : Resolved} {sigs : Array Signature} {fuel : Nat} {ctx : TypeContext}
    {path : Path} {cal : Bool} {res : Inferred}
    (h : infer (fuel + 1) r sigs ctx (.name path) cal = .ok res) :
    Sound r sigs ctx (.name path) res := by
  simp only [infer] at h
  obtain ⟨ref, href, h⟩ := bind_ok h
  obtain ⟨found, role⟩ := reference_ok href
  split at h
  case isFalse => cases h
  rename_i same
  have sel : ∀ target, ref.target = target → Selects r ctx path .expression target :=
    fun _ eq => ⟨ref, found, role, eq, tokens_eq same⟩
  have constructor : ∀ id ty, ref.target = .item id → constructorType r id = some ty →
      Sound r sigs ctx (.name path) ⟨.value ty, #[].push ⟨.name path, ctx, .value ty⟩⟩ :=
    fun id ty eq ct => node_sound .name forest_nil (HasValue.constructor (sel _ eq) ct)
  split at h
  · rename_i i target
    split at h
    · rename_i ty hl
      cases pure_ok h
      obtain ⟨token, typed⟩ := localType_some hl
      exact node_sound .name forest_nil (HasValue.local (sel _ target) typed)
    · cases h
  · rename_i id target
    split at h
    · split at h
      · rename_i sig hs
        cases pure_ok h
        cases signatureAt_id hs
        exact node_sound .name forest_nil (HasCallable.name (sel _ target) hs)
      · split at h
        · rename_i ty ct
          cases pure_ok h
          exact constructor id ty target ct
        · cases h
    · split at h
      · rename_i ty ct
        cases pure_ok h
        exact constructor id ty target ct
      · cases h
  · cases h

theorem call_sound {r : Resolved} {sigs : Array Signature} {fuel : Nat} {ctx : TypeContext}
    {callee : Expr} {o c : Token} {args : Array Expr} {commas : Array Token} {cal : Bool}
    {res : Inferred} (ih : Below r sigs fuel)
    (h : infer (fuel + 1) r sigs ctx (.call callee o args commas c) cal = .ok res)
    (named : Named r sigs ctx (.call callee o args commas c)) :
    Sound r sigs ctx (.call callee o args commas c) res := by
  simp only [infer] at h
  obtain ⟨c1, hc, h⟩ := bind_ok h
  have sc := ih _ _ _ _ hc (named.child .callee)
  split at h
  case h_2 => cases h
  rename_i sig heq
  split at h
  case isFalse => cases h
  rename_i hsize
  obtain ⟨nodes, hloop, h⟩ := bind_ok h
  cases pure_ok h
  obtain ⟨path, rfl⟩ := named _ _ _ _ _ _ .root
  have hcallee : HasCallable r sigs ctx (.name path) sig := by
    have m := sc.1
    rw [heq] at m
    exact m
  have inv := forIn_range_invariant
    (fun k (s : Array TypedOccurrence) =>
      Forest r sigs ((ctx, Expr.name path) :: (args.toList.take k).map (ctx, ·)) s.toList ∧
      ∀ i (hi : i < args.size) (hp : i < sig.parameters.size), i < k →
        HasValue r sigs ctx args[i] sig.parameters[i].type)
    args.size _ _ _ hloop ⟨forest_one sc.2, fun _ _ _ lt => absurd lt (Nat.not_lt_zero _)⟩
    (by
      intro k s next lt ⟨forest, typed⟩ hstep
      split at hstep
      case h_2 => cases hstep
      rename_i arg harg
      obtain ⟨r1, hr, hstep⟩ := bind_ok hstep
      obtain ⟨ty, hty, hstep⟩ := bind_ok hstep
      split at hstep
      case h_2 => cases hstep
      rename_i param hparam
      obtain ⟨_, hreq, hstep⟩ := bind_ok hstep
      cases pure_ok hstep
      cases (requireType_iff _ _ _).mp hreq
      have mem : arg ∈ args.toList := by
        rw [← Array.getElem?_toList] at harg
        exact List.mem_of_getElem? harg
      have sa := ih _ _ _ _ hr (named.child (.argument mem))
      refine ⟨_, rfl, ?_, ?_⟩
      · rw [Array.toList_append, List.take_add_one, Array.getElem?_toList, harg]
        simpa only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
          List.cons_append] using forest_snoc forest sa.2
      · intro i hi hp le
        rcases Nat.lt_succ_iff_lt_or_eq.mp le with lt' | rfl
        · exact typed i hi hp lt'
        · have ea : args[i] = arg := by
            rw [Array.getElem?_eq_getElem hi] at harg
            exact Option.some.inj harg
          have ep : sig.parameters[i] = param := by
            rw [Array.getElem?_eq_getElem hp] at hparam
            exact Option.some.inj hparam
          rw [ea, ep]
          exact sa.value (value_ok hty))
  obtain ⟨forest, typed⟩ := inv
  rw [List.take_of_length_le (Nat.le_of_eq Array.length_toList)] at forest
  cases hcallee with
  | name sel hs =>
    exact node_sound .call forest
      (HasValue.call sel hs (beq_iff_eq.mp hsize) (fun i hi hp => typed i hi hp hi))

theorem match_sound {r : Resolved} {sigs : Array Signature} {fuel : Nat} {ctx : TypeContext}
    {scrutinee : Expr} {m o c : Token} {arms : Array (Path × Token × Expr × Option Token)}
    {cal : Bool} {res : Inferred} (ih : Below r sigs fuel)
    (h : infer (fuel + 1) r sigs ctx (.matchE m scrutinee o arms c) cal = .ok res)
    (named : Named r sigs ctx (.matchE m scrutinee o arms c)) :
    Sound r sigs ctx (.matchE m scrutinee o arms c) res := by
  simp only [infer] at h
  obtain ⟨s1, hs, h⟩ := bind_ok h
  have ss := ih _ _ _ _ hs (named.child .scrutinee)
  obtain ⟨st, hst, h⟩ := bind_ok h
  have scrutineeTyped := ss.value (value_ok hst)
  split at h
  case h_2 => cases h
  rename_i owner
  obtain ⟨final, hloop, h⟩ := bind_ok h
  split at h
  case h_2 => cases h
  rename_i out hout
  cases pure_ok h
  rw [← Array.forIn_toList] at hloop
  have inv := forIn_invariant
    (fun pre (s : Option FrenExpr.Ty × Array TypedOccurrence) =>
      Forest r sigs ((ctx, scrutinee) :: pre.map (fun arm => (ctx, arm.2.2.1))) s.snd.toList ∧
      (∀ arm ∈ pre, ∃ id, Selects r ctx arm.1 .pattern (.item id) ∧
        constructorType r id = some (.enum owner)) ∧
      (∀ arm ∈ pre, ∃ t, s.fst = some t ∧ HasValue r sigs ctx arm.2.2.1 t) ∧
      (pre = [] → s.fst = none))
    _ arms.toList [] _ _ hloop
    (by
      refine ⟨forest_one ss.2, ?_, ?_, fun _ => rfl⟩
      · intro _ h; cases h
      · intro _ h; cases h)
    (by
      intro done x rest s next eq ⟨forest, patterns, bodies, _⟩ hstep
      have mem : x ∈ arms.toList := by
        rw [List.nil_append] at eq
        rw [eq]
        exact List.mem_append_right _ List.mem_cons_self
      obtain ⟨ref, href, hstep⟩ := bind_ok hstep
      obtain ⟨found, role⟩ := reference_ok href
      split at hstep
      case isFalse => cases hstep
      rename_i same
      split at hstep
      case h_2 => cases hstep
      rename_i id target
      split at hstep
      case h_2 => cases hstep
      rename_i pt ct
      obtain ⟨_, hreq, hstep⟩ := bind_ok hstep
      rw [(requireType_iff _ _ _).mp hreq] at ct
      obtain ⟨b, hb, hstep⟩ := bind_ok hstep
      obtain ⟨bt, hbt, hstep⟩ := bind_ok hstep
      have sb := ih _ _ _ _ hb (named.child (.armBody mem))
      have typed := sb.value (value_ok hbt)
      have pattern : ∃ id, Selects r ctx x.1 .pattern (.item id) ∧
          constructorType r id = some (.enum owner) :=
        ⟨id, ⟨ref, found, role, target, tokens_eq same⟩, ct⟩
      have grown : Forest r sigs
          ((ctx, scrutinee) :: (done ++ [x]).map (fun arm => (ctx, arm.2.2.1)))
          (s.snd ++ b.occurrences).toList := by
        rw [Array.toList_append]
        simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append]
          using forest_snoc forest sb.2
      have patterns' : ∀ arm ∈ done ++ [x], ∃ id, Selects r ctx arm.1 .pattern (.item id) ∧
          constructorType r id = some (.enum owner) := by
        intro arm hm
        rcases List.mem_append.mp hm with hm | hm
        · exact patterns arm hm
        · cases List.mem_singleton.mp hm
          exact pattern
      have nonempty : done ++ [x] = [] → ∀ t : Option FrenExpr.Ty, t = none :=
        fun h => absurd h (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
      split at hstep
      · rename_i expected hexp
        obtain ⟨_, hreq', hstep⟩ := bind_ok hstep
        cases pure_ok hstep
        cases (requireType_iff _ _ _).mp hreq'
        refine ⟨_, rfl, grown, patterns', ?_, fun h => nonempty h _⟩
        intro arm hm
        rcases List.mem_append.mp hm with hm | hm
        · exact bodies arm hm
        · cases List.mem_singleton.mp hm
          exact ⟨_, hexp, typed⟩
      · rename_i hnone
        cases pure_ok hstep
        refine ⟨_, rfl, grown, patterns', ?_, fun h => nonempty h _⟩
        intro arm hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨t, ht, _⟩ := bodies arm hm
          exact absurd ht (hnone t)
        · cases List.mem_singleton.mp hm
          exact ⟨_, rfl, typed⟩)
  obtain ⟨forest, patterns, bodies, empty⟩ := inv
  rw [List.nil_append] at forest patterns bodies empty
  have nonempty : arms.isEmpty = false := by
    cases hl : arms.toList with
    | nil =>
      rw [empty hl] at hout
      cases hout
    | cons x rest =>
      obtain ⟨l⟩ := arms
      cases hl
      rfl
  refine node_sound .matchE forest (HasValue.matchE scrutineeTyped nonempty patterns ?_)
  intro arm hm
  obtain ⟨t, ht, typed⟩ := bodies arm hm
  rw [hout] at ht
  cases ht
  exact typed

/-- A successful traversal types the expression, and its table is the exact
postorder of the expression's descendants, each entry with its meaning. -/
theorem infer_sound {r : Resolved} {sigs : Array Signature} :
    ∀ fuel : Nat, Below r sigs fuel
  | 0, _, _, _, _, h, _ => by
    simp only [infer] at h
    cases h
  | fuel + 1, ctx, e, cal, res, h, named => by
    have ih : Below r sigs fuel := infer_sound fuel
    cases e with
    | name path => exact name_sound h
    | bool t v =>
      simp only [infer] at h
      cases pure_ok h
      exact node_sound .bool forest_nil HasValue.bool
    | integer t v =>
      simp only [infer] at h
      cases pure_ok h
      exact node_sound .integer forest_nil HasValue.integer
    | paren o body c =>
      simp only [infer] at h
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases pure_ok h
      have sb := ih _ _ _ _ hb (named.child .paren)
      exact node_sound .paren (forest_one sb.2) (meaning_paren sb.1)
    | unary t op body =>
      simp only [infer] at h
      obtain ⟨b, hb, h⟩ := bind_ok h
      obtain ⟨ty, hty, h⟩ := bind_ok h
      have sb := ih _ _ _ _ hb (named.child .unary)
      split at h
      · rename_i out hop
        cases pure_ok h
        exact node_sound .unary (forest_one sb.2) (HasValue.unary (sb.value (value_ok hty)) hop)
      · obtain ⟨_, _, h⟩ := bind_ok h
        cases h
    | binary left t op right =>
      simp only [infer] at h
      obtain ⟨l, hl, h⟩ := bind_ok h
      obtain ⟨lt, hlt, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨rr, hr, h⟩ := bind_ok h
      obtain ⟨rt, hrt, h⟩ := bind_ok h
      have sl := ih _ _ _ _ hl (named.child .binaryLeft)
      have sr := ih _ _ _ _ hr (named.child .binaryRight)
      split at h
      · rename_i out hop
        cases pure_ok h
        refine node_sound .binary ?_
          (HasValue.binary (sl.value (value_ok hlt)) (sr.value (value_ok hrt)) hop)
        rw [Array.toList_append]
        exact forest_snoc (forest_one sl.2) sr.2
      · obtain ⟨_, _, h⟩ := bind_ok h
        cases h
    | call callee o args commas c => exact call_sound ih h named
    | ifE i condition t yes e no =>
      simp only [infer] at h
      obtain ⟨cr, hc, h⟩ := bind_ok h
      obtain ⟨cty, hcty, h⟩ := bind_ok h
      obtain ⟨_, hbool, h⟩ := bind_ok h
      obtain ⟨y, hy, h⟩ := bind_ok h
      obtain ⟨yt, hyt, h⟩ := bind_ok h
      obtain ⟨n, hn, h⟩ := bind_ok h
      obtain ⟨nt, hnt, h⟩ := bind_ok h
      obtain ⟨_, hsame, h⟩ := bind_ok h
      cases pure_ok h
      cases (requireType_iff _ _ _).mp hbool
      cases (requireType_iff _ _ _).mp hsame
      have sc := ih _ _ _ _ hc (named.child .condition)
      have sy := ih _ _ _ _ hy (named.child .thenBranch)
      have sn := ih _ _ _ _ hn (named.child .elseBranch)
      refine node_sound .ifE ?_ (HasValue.ifE (sc.value (value_ok hcty))
        (sy.value (value_ok hyt)) (sn.value (value_ok hnt)))
      rw [Array.toList_append, Array.toList_append]
      exact forest_snoc (forest_snoc (forest_one sc.2) sy.2) sn.2
    | letE l name assign value i body =>
      simp only [infer] at h
      obtain ⟨v, hv, h⟩ := bind_ok h
      obtain ⟨vt, hvt, h⟩ := bind_ok h
      obtain ⟨_, hsuffix, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      obtain ⟨bt, hbt, h⟩ := bind_ok h
      cases pure_ok h
      have sv := ih _ _ _ _ hv (named.child .letValue)
      have valueTyped := sv.value (value_ok hvt)
      have sb := ih _ _ _ _ hb (named.child (.letBody valueTyped))
      refine node_sound (.letE valueTyped) ?_
        (HasValue.letE valueTyped hsuffix (sb.value (value_ok hbt)))
      rw [Array.toList_append]
      exact forest_snoc (forest_one sv.2) sb.2
    | matchE m scrutinee o arms c => exact match_sound ih h named

/-! ## Bodies

The body loop of the type pass pushes one entry per function body and per
expectation member. Each entry records the declaration it came from and the
successful traversal of its expression. -/

/-- What the body loop establishes for an entry it pushes. -/
def Checked (input : Resolved) (sigs : Array Signature) (body : TypedBody) : Prop :=
  DeclaresBody input sigs body.owner body.member body.expression body.context body.type ∧
  ∃ fuel res, infer fuel input sigs body.context body.expression false = .ok res ∧
    res.type = .value body.type ∧ res.occurrences = body.occurrences

theorem checked_push {input : Resolved} {sigs : Array Signature} {acc : Array TypedBody}
    {new : TypedBody} (inv : ∀ body ∈ acc.toList, Checked input sigs body)
    (h : Checked input sigs new) : ∀ body ∈ (acc.push new).toList, Checked input sigs body := by
  intro body hb
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact inv body hb
  · exact h

theorem mem_of_split {α : Type} {xs done rest : List α} {x : α}
    (eq : [] ++ xs = done ++ x :: rest) : x ∈ xs := by
  rw [List.nil_append] at eq
  rw [eq]
  exact List.mem_append_right _ List.mem_cons_self

theorem bodies_checked {input : Resolved} {sigs : Array Signature} {out : Array TypedBody}
    (h : bodies input sigs = .ok out) : ∀ body ∈ out.toList, Checked input sigs body := by
  simp only [bodies] at h
  split at h
  · rename_i decls root
    obtain ⟨acc, hloop, h⟩ := bind_ok h
    cases pure_ok h
    rw [← Array.forIn_toList] at hloop
    refine forIn_invariant (fun _ acc => ∀ body ∈ acc.toList, Checked input sigs body) _
      decls.toList [] #[] _ hloop (fun _ hb => nomatch hb) ?_
    intro done decl rest s next eq inv hstep
    have mem : decl ∈ decls.toList := mem_of_split eq
    split at hstep
    · split at hstep
      · rename_i sig hsig
        obtain ⟨res, hres, hstep⟩ := bind_ok hstep
        obtain ⟨ty, hty, hstep⟩ := bind_ok hstep
        obtain ⟨_, hreq, hstep⟩ := bind_ok hstep
        refine ⟨_, (pure_ok hstep).symm, checked_push inv ⟨?_, _, res, hres, value_ok hty, rfl⟩⟩
        have declared := DeclaresBody.function root mem hsig
        rw [signatureAt_id hsig, ← (requireType_iff _ _ _).mp hreq] at declared
        exact declared
      · obtain ⟨_, hthrow, _⟩ := bind_ok hstep
        cases hthrow
    · rename_i keyword name params openToken members closeToken
      obtain ⟨typedParams, hparams, hstep⟩ := bind_ok hstep
      obtain ⟨acc', hinner, hstep⟩ := bind_ok hstep
      refine ⟨_, (pure_ok hstep).symm, ?_⟩
      rw [← Array.forIn_toList] at hinner
      refine forIn_invariant (fun _ acc => ∀ body ∈ acc.toList, Checked input sigs body) _
        members.toList [] s acc' hinner inv ?_
      intro done' m rest' s' next' eq' inv' hm
      obtain ⟨res, hres, hm⟩ := bind_ok hm
      obtain ⟨ty, hty, hm⟩ := bind_ok hm
      obtain ⟨_, hreq, hm⟩ := bind_ok hm
      refine ⟨_, (pure_ok hm).symm, checked_push inv' ⟨?_, _, res, hres, value_ok hty, rfl⟩⟩
      have declared := DeclaresBody.member (sigs := sigs) root mem (mem_of_split eq') hparams
      rw [← (requireType_iff _ _ _).mp hreq] at declared
      exact declared
    · exact ⟨_, (pure_ok hstep).symm, inv⟩
  · cases h

/-- A produced program keeps its input, and its bodies are those of the body loop. -/
theorem produces_bodies {input : Resolved} {out : Typed} (h : Produces input out) :
    out.resolved = input ∧ bodies input out.signatures = .ok out.bodies := by
  have retained := (check_retains input out h).1
  simp only [Produces, FrenHirToThir.check] at h
  obtain ⟨admitted, hadmit, h⟩ := bind_ok h
  have same := typeResolved_retains _ _ h
  simp only [typeResolved] at h
  obtain ⟨sigs, _, h⟩ := bind_ok h
  obtain ⟨typedBodies, hbodies, h⟩ := bind_ok h
  cases pure_ok h
  rw [← same, retained] at hbodies
  exact ⟨retained, hbodies⟩

/-! ## Whole programs -/

/-- Every body of a produced program has a declaration. This is the first half
of `BodyInventory`. -/
theorem bodies_declared {input : Resolved} {out : Typed} (h : Produces input out) :
    ∀ body ∈ out.bodies.toList,
      DeclaresBody input out.signatures body.owner body.member body.expression body.context
        body.type :=
  fun body hb => (bodies_checked (produces_bodies h).2 body hb).1

theorem body_sound {input : Resolved} {out : Typed} (h : Produces input out)
    (named : NamedCallees input out) : ∀ body ∈ out.bodies.toList,
      HasValue input out.signatures body.context body.expression body.type ∧
      Table input out.signatures body.context body.expression body.occurrences.toList := by
  intro body hb
  obtain ⟨_, fuel, res, hres, hty, hoccs⟩ := bodies_checked (produces_bodies h).2 body hb
  have sound := infer_sound fuel _ _ _ _ hres (named body hb)
  rw [← hoccs]
  exact ⟨sound.value hty, sound.2⟩

theorem body_typing {input : Resolved} {out : Typed} (h : Produces input out)
    (named : NamedCallees input out) : BodyTyping input out :=
  fun body hb => (body_sound h named body hb).1

theorem occurrence_inventory {input : Resolved} {out : Typed} (h : Produces input out)
    (named : NamedCallees input out) : OccurrenceInventory input out :=
  fun body hb => (body_sound h named body hb).2.1

theorem occurrence_typing {input : Resolved} {out : Typed} (h : Produces input out)
    (named : NamedCallees input out) : OccurrenceTyping input out :=
  ⟨fun body hb => (body_sound h named body hb).2.2.2,
    fun body hb => (body_sound h named body hb).2.2.1⟩

/-- The typed table of a body has an entry for each call, and a call has a
value only when its callee is a name. -/
theorem named_callees {input : Resolved} {out : Typed} (typing : OccurrenceTyping input out) :
    NamedCallees input out := by
  intro body hb ctx callee o args commas c at'
  obtain ⟨occurrence, _, expression, _, meaning⟩ := typing.1 body hb ctx _ at'
  unfold OccurrenceMeaning at meaning
  split at meaning
  · rw [expression] at meaning
    cases meaning
    exact ⟨_, rfl⟩
  · rw [expression] at meaning
    cases meaning

end Spec.Compiler.Thir
