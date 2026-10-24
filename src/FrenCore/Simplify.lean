/-!
# Simpler `Bool` expressions, proved

The rules of `nonminimal_bool` (`Reqs/Lint#simpler-bool-expressions`) over a
model of expressions (`Ex`), with a proof that the simpler form means what
the expression means (`Ex.simp_eval`).

The lint decides with `Ex.simplerForm`, which looks at an expression's
operands and theirs, and builds the text of the simpler form from the
`Shape` it gives. That the text parses as the expression `Ex.simp` builds is
not proved.
-/

namespace Fren.Core

/-- A comparison operator (`lint::Comparison`). -/
inductive Comparison where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving Inhabited, BEq, DecidableEq, Repr

def Comparison.all : Array Comparison := #[.eq, .ne, .lt, .le, .gt, .ge]

def Comparison.op : Comparison → String
  | .eq => "="
  | .ne => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

def Comparison.ofOp? (op : String) : Option Comparison := Comparison.all.find? (·.op == op)

/-- The comparison that holds exactly when `c` does not (`lint::complement`). -/
def Comparison.complement : Comparison → Comparison
  | .eq => .ne
  | .ne => .eq
  | .lt => .ge
  | .ge => .lt
  | .gt => .le
  | .le => .gt

/-- Whether the simpler form of a comparison with a literal is `not A`
(`lint::literal_comparison`), from whether the operator is `=` or `iff`
and whether the literal is `true`. -/
def literalNegated (equal literal : Bool) : Bool := equal != literal

/-- A binary operator. -/
inductive BinOp where
  | iff
  | or
  | and
  | cmp (c : Comparison)
  | add
  | sub
  | mul
  deriving Inhabited, BEq, DecidableEq, Repr

def BinOp.ofOp? : String → Option BinOp
  | "iff" => some .iff
  | "or" => some .or
  | "and" => some .and
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | op => (Comparison.ofOp? op).map .cmp

/-- An expression, as `nonminimal_bool` sees it. An atom, such as a path or
a number, is an operand it does not look inside. -/
inductive Ex where
  | atom (i : Nat)
  | lit (b : Bool)
  | not (a : Ex)
  | neg (a : Ex)
  | bin (op : BinOp) (a b : Ex)
  /-- `when c, d`, or `unless c, d` if `negated`. -/
  | when (negated : Bool) (c d : Ex)
  | ite (c a b : Ex)
  deriving Inhabited, Repr

/-! ## Meaning -/

/-- A value: a `Bool`, an `Int`, or a variant, numbered within its enum. -/
inductive Val where
  | bool (b : Bool)
  | int (i : Int)
  | variant (enum i : Nat)
  deriving DecidableEq, Repr

def Val.sameType : Val → Val → Bool
  | .bool _, .bool _ | .int _, .int _ => true
  | .variant e _, .variant e' _ => e == e'
  | _, _ => false

def notV : Option Val → Option Val
  | some (.bool b) => some (.bool !b)
  | _ => none

def negV : Option Val → Option Val
  | some (.int i) => some (.int (-i))
  | _ => none

def cmpV (c : Comparison) (x y : Val) : Option Val :=
  match c, x, y with
  | .eq, x, y => if x.sameType y then some (.bool (decide (x = y))) else none
  | .ne, x, y => if x.sameType y then some (.bool (decide (x ≠ y))) else none
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .gt, .int a, .int b => some (.bool (decide (a > b)))
  | .ge, .int a, .int b => some (.bool (decide (a ≥ b)))
  | _, _, _ => none

def binV (op : BinOp) : Option Val → Option Val → Option Val
  | some x, some y =>
    match op, x, y with
    | .iff, .bool a, .bool b => some (.bool (a == b))
    | .or, .bool a, .bool b => some (.bool (a || b))
    | .and, .bool a, .bool b => some (.bool (a && b))
    | .cmp c, x, y => cmpV c x y
    | .add, .int a, .int b => some (.int (a + b))
    | .sub, .int a, .int b => some (.int (a - b))
    | .mul, .int a, .int b => some (.int (a * b))
    | _, _, _ => none
  | _, _ => none

def whenV (negated : Bool) : Option Val → Option Val → Option Val
  | some (.bool c), some (.bool d) => some (.bool ((if negated then c else !c) || d))
  | _, _ => none

def iteV : Option Val → Option Val → Option Val → Option Val
  | some (.bool true), a, _ => a
  | some (.bool false), _, b => b
  | _, _, _ => none

/-- The value of an expression, where atom `i` has the value `ρ i`; `none`
if it has none, as when the types of its operands are wrong. -/
def Ex.eval (ρ : Nat → Val) : Ex → Option Val
  | .atom i => some (ρ i)
  | .lit b => some (.bool b)
  | .not a => notV (a.eval ρ)
  | .neg a => negV (a.eval ρ)
  | .bin op a b => binV op (a.eval ρ) (b.eval ρ)
  | .when n c d => whenV n (c.eval ρ) (d.eval ρ)
  | .ite c a b => iteV (c.eval ρ) (a.eval ρ) (b.eval ρ)

/-! ## Rules -/

/-- An operand of an expression, or an operand of one of its operands. -/
inductive Pick where
  | kid (i : Nat)
  | grandkid (i j : Nat)
  deriving Inhabited, Repr

/-- The simpler form of an expression, in terms of its operands. -/
inductive Shape where
  | same (p : Pick)
  | not (p : Pick)
  | cmp (c : Comparison) (a b : Pick)
  deriving Inhabited, Repr

/-- For `iff`, `=` and `!=`: whether the operator holds when its operands
are equal. -/
def BinOp.literalOp? : BinOp → Option Bool
  | .iff | .cmp .eq => some true
  | .cmp .ne => some false
  | _ => none

/-- The simpler form of `a op b`, with `equal` from `BinOp.literalOp?`, if
one of `a` and `b` is a literal (`lint::literal_comparison`), and the
literal. -/
def literalShape (equal : Bool) (a b : Ex) (pa pb : Pick) : Option (Bool × Shape) :=
  match b, a with
  | .lit l, _ => some (l, if literalNegated equal l then .not pa else .same pa)
  | _, .lit l => some (l, if literalNegated equal l then .not pb else .same pb)
  | _, _ => none

/-- The simpler form of `e`, if it has one, and a label for the message
(`Reqs/Lint#simpler-bool-expressions`). -/
def Ex.simplerForm : Ex → Option (String × Shape)
  | .bin op a b => do
    let equal ← op.literalOp?
    let (l, s) ← literalShape equal a b (.kid 0) (.kid 1)
    return (s!"comparison with `{l}`", s)
  | .not (.not _) => some ("double negation", .same (.grandkid 0 0))
  | .not (.bin (.cmp c) a b) =>
    -- The complement of a comparison with a literal is one too.
    let s := match (BinOp.cmp c.complement).literalOp? >>= fun eq => literalShape eq a b (.grandkid 0 0) (.grandkid 0 1) with
      | some (_, s) => s
      | none => .cmp c.complement (.grandkid 0 0) (.grandkid 0 1)
    some (s!"negated `{c.op}`", s)
  | .ite _ (.lit true) (.lit false) => some ("`if` that gives `true` or `false`", .same (.kid 0))
  | .ite _ (.lit false) (.lit true) => some ("`if` that gives `false` or `true`", .not (.kid 0))
  | _ => none

/-- An operand, from the operands `rs`, each with its own. -/
def Pick.get (rs : Array (Ex × Array Ex)) : Pick → Ex
  | .kid i => (rs[i]?.map (·.1)).getD (.lit false)
  | .grandkid i j => ((rs[i]?.map (·.2)).getD #[])[j]?.getD (.lit false)

def Shape.build (rs : Array (Ex × Array Ex)) : Shape → Ex
  | .same p => p.get rs
  | .not p => .not (p.get rs)
  | .cmp c a b => .bin (.cmp c) (a.get rs) (b.get rs)

/-- `e`'s operands replaced by `kids`. -/
def Ex.withKids (e : Ex) (kids : Array Ex) : Ex :=
  let k (i : Nat) := kids[i]?.getD (.lit false)
  match e with
  | .atom i => .atom i
  | .lit b => .lit b
  | .not _ => .not (k 0)
  | .neg _ => .neg (k 0)
  | .bin op _ _ => .bin op (k 0) (k 1)
  | .when n _ _ => .when n (k 0) (k 1)
  | .ite _ _ _ => .ite (k 0) (k 1) (k 2)

/-- `e` simplified, and its operands simplified: the operands first, then
`e` by its rules, from what it is as written. -/
def Ex.simp : Ex → Ex × Array Ex
  | .atom i => (.atom i, #[])
  | .lit b => (.lit b, #[])
  | e@(.not a) => finish e #[a.simp]
  | e@(.neg a) => finish e #[a.simp]
  | e@(.bin _ a b) => finish e #[a.simp, b.simp]
  | e@(.when _ c d) => finish e #[c.simp, d.simp]
  | e@(.ite c a b) => finish e #[c.simp, a.simp, b.simp]
where
  finish (e : Ex) (rs : Array (Ex × Array Ex)) : Ex × Array Ex :=
    let kids := rs.map (·.1)
    match e.simplerForm with
    | some (_, s) => (s.build rs, kids)
    | none => (e.withKids kids, kids)

/-! ## Proof -/

/-- `o'` has the value of `o`, if `o` has one. -/
def Refines (o o' : Option Val) : Prop := ∀ v, o = some v → o' = some v

infix:50 " ⊑ " => Refines

theorem Refines.refl (o : Option Val) : o ⊑ o := fun _ h => h

theorem Refines.trans {a b c : Option Val} (h₁ : a ⊑ b) (h₂ : b ⊑ c) : a ⊑ c :=
  fun v h => h₂ v (h₁ v h)

theorem notV_mono {a a' : Option Val} (h : a ⊑ a') : notV a ⊑ notV a' := by
  intro v hv
  match a, hv with
  | some (.bool b), hv => rw [h _ rfl]; exact hv

theorem negV_mono {a a' : Option Val} (h : a ⊑ a') : negV a ⊑ negV a' := by
  intro v hv
  match a, hv with
  | some (.int i), hv => rw [h _ rfl]; exact hv

theorem binV_mono (op : BinOp) {a a' b b' : Option Val} (ha : a ⊑ a') (hb : b ⊑ b') :
    binV op a b ⊑ binV op a' b' := by
  intro v hv
  match a, b, hv with
  | some x, some y, hv => rw [ha _ rfl, hb _ rfl]; exact hv

theorem whenV_mono (n : Bool) {a a' b b' : Option Val} (ha : a ⊑ a') (hb : b ⊑ b') :
    whenV n a b ⊑ whenV n a' b' := by
  intro v hv
  match a, b, hv with
  | some (.bool c), some (.bool d), hv => rw [ha _ rfl, hb _ rfl]; exact hv

theorem iteV_mono {c c' a a' b b' : Option Val} (hc : c ⊑ c') (ha : a ⊑ a') (hb : b ⊑ b') :
    iteV c a b ⊑ iteV c' a' b' := by
  intro v hv
  match c, hv with
  | some (.bool true), hv => rw [hc _ rfl]; exact ha _ hv
  | some (.bool false), hv => rw [hc _ rfl]; exact hb _ hv

theorem notV_notV (a : Option Val) : notV (notV a) ⊑ a := by
  intro v hv
  match a, hv with
  | some (.bool b), hv => simp [notV] at hv; rw [← hv]

theorem binV_lit_right (op : BinOp) (equal : Bool) (h : op.literalOp? = some equal) (x : Option Val) (l : Bool) :
    binV op x (some (.bool l)) ⊑ (if literalNegated equal l then notV x else x) := by
  intro v hv
  rcases x with _ | x
  · simp [binV] at hv
  rcases op with _ | _ | _ | c | _ | _ | _ <;> simp [BinOp.literalOp?] at h
  · subst h; cases x <;> cases l <;> simp_all [binV, literalNegated, notV]
  · cases c <;> simp at h <;> subst h <;>
      cases x <;> cases l <;> simp_all [binV, cmpV, Val.sameType, literalNegated, notV]

theorem binV_lit_left (op : BinOp) (equal : Bool) (h : op.literalOp? = some equal) (y : Option Val) (l : Bool) :
    binV op (some (.bool l)) y ⊑ (if literalNegated equal l then notV y else y) := by
  intro v hv
  rcases y with _ | y
  · simp [binV] at hv
  rcases op with _ | _ | _ | c | _ | _ | _ <;> simp [BinOp.literalOp?] at h
  · subst h; cases y <;> cases l <;> simp_all [binV, literalNegated, notV]
  · cases c <;> simp at h <;> subst h <;>
      cases y <;> cases l <;> simp_all [binV, cmpV, Val.sameType, literalNegated, notV] <;> (try subst_vars) <;> simp_all [eq_comm]

theorem literalShape_spec (op : BinOp) (equal : Bool) (heq : op.literalOp? = some equal)
    {a b : Ex} {pa pb : Pick} {l : Bool} {s : Shape} (hs : literalShape equal a b pa pb = some (l, s))
    (ρ : Nat → Val) (rs : Array (Ex × Array Ex))
    (ha : a.eval ρ ⊑ (pa.get rs).eval ρ) (hb : b.eval ρ ⊑ (pb.get rs).eval ρ) :
    binV op (a.eval ρ) (b.eval ρ) ⊑ (s.build rs).eval ρ := by
  unfold literalShape at hs
  split at hs <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
  · obtain ⟨rfl, rfl⟩ := hs
    rename_i l
    refine (binV_lit_right op equal heq _ l).trans ?_
    cases literalNegated equal l <;> simp [Shape.build, Ex.eval]
    · exact ha
    · exact notV_mono ha
  · obtain ⟨rfl, rfl⟩ := hs
    rename_i l _
    refine (binV_lit_left op equal heq _ l).trans ?_
    cases literalNegated equal l <;> simp [Shape.build, Ex.eval]
    · exact hb
    · exact notV_mono hb

theorem notV_cmpV (c : Comparison) (x y : Option Val) :
    notV (binV (.cmp c) x y) ⊑ binV (.cmp c.complement) x y := by
  intro v hv
  rcases x with _ | x <;> rcases y with _ | y <;> simp [binV, notV] at hv ⊢
  cases c <;> cases x <;> cases y <;> simp [cmpV, Comparison.complement, Val.sameType] at hv ⊢ <;>
    (try split at hv) <;> (try split) <;>
    all_goals first
      | omega
      | (simp_all; done)
      | (simp_all; omega)
      | (subst_vars; rename_i a b; by_cases h : a < b <;> by_cases h2 : b < a <;> simp [h, h2] <;> omega)

theorem iteV_true_false (c : Option Val) : iteV c (some (.bool true)) (some (.bool false)) ⊑ c := by
  intro v hv
  match c, hv with
  | some (.bool true), hv => simpa [iteV] using hv
  | some (.bool false), hv => simpa [iteV] using hv

theorem iteV_false_true (c : Option Val) : iteV c (some (.bool false)) (some (.bool true)) ⊑ notV c := by
  intro v hv
  match c, hv with
  | some (.bool true), hv => simpa [iteV, notV] using hv
  | some (.bool false), hv => simpa [iteV, notV] using hv

theorem finish_snd (e : Ex) (rs : Array (Ex × Array Ex)) : (Ex.simp.finish e rs).2 = rs.map (·.1) := by
  unfold Ex.simp.finish; split <;> rfl

/-- The operands of an expression. -/
def Ex.kids : Ex → List Ex
  | .atom _ | .lit _ => []
  | .not a | .neg a => [a]
  | .bin _ a b | .when _ a b => [a, b]
  | .ite c a b => [c, a, b]

theorem simp_good (ρ : Nat → Val) (e : Ex) :
    e.eval ρ ⊑ e.simp.1.eval ρ ∧ ∀ k ∈ e.kids, k.eval ρ ⊑ k.simp.1.eval ρ := by
  induction e with
  | atom i => exact ⟨Refines.refl _, by simp [Ex.kids]⟩
  | lit b => exact ⟨Refines.refl _, by simp [Ex.kids]⟩
  | not a ih =>
    refine ⟨?_, by simpa [Ex.kids] using ih.1⟩
    simp only [Ex.simp]
    cases hsf : (Ex.not a).simplerForm with
    | none =>
      simp only [Ex.simp.finish, hsf, Ex.withKids]
      simpa [Ex.eval] using notV_mono ih.1
    | some r =>
      obtain ⟨lbl, s⟩ := r
      simp only [Ex.simp.finish, hsf]
      cases a with
      | not g =>
        simp [Ex.simplerForm] at hsf
        obtain ⟨-, rfl⟩ := hsf
        simp only [Shape.build, Pick.get, Ex.simp]
        simpa [Ex.eval, finish_snd] using (notV_notV _).trans (ih.2 g (by simp [Ex.kids]))
      | bin op p q =>
        cases op with
        | cmp c =>
          simp only [Ex.simplerForm, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨-, rfl⟩ := hsf
          have hp := ih.2 p (by simp [Ex.kids])
          have hq := ih.2 q (by simp [Ex.kids])
          simp only [Ex.eval]
          refine (notV_cmpV c _ _).trans ?_
          split
          · rename_i s' hl
            cases hlo : (BinOp.cmp c.complement).literalOp? with
            | none => simp [hlo] at hl
            | some eq =>
              simp only [hlo, Option.bind_eq_bind, Option.bind_some] at hl
              exact literalShape_spec _ eq hlo hl ρ _
                (by simpa [Pick.get, Ex.simp, finish_snd] using hp)
                (by simpa [Pick.get, Ex.simp, finish_snd] using hq)
          · simp only [Shape.build, Pick.get, Ex.simp, Ex.eval]
            simpa [finish_snd] using binV_mono _ hp hq
        | _ => simp [Ex.simplerForm] at hsf
      | _ => simp [Ex.simplerForm] at hsf
  | neg a ih =>
    refine ⟨?_, by simpa [Ex.kids] using ih.1⟩
    simp only [Ex.simp, Ex.simp.finish, Ex.simplerForm, Ex.withKids]
    simpa [Ex.eval] using negV_mono ih.1
  | bin op a b iha ihb =>
    refine ⟨?_, by simp [Ex.kids]; exact ⟨iha.1, ihb.1⟩⟩
    simp only [Ex.simp]
    cases hsf : (Ex.bin op a b).simplerForm with
    | none =>
      simp only [Ex.simp.finish, hsf, Ex.withKids]
      simpa [Ex.eval] using binV_mono op iha.1 ihb.1
    | some r =>
      obtain ⟨lbl, s⟩ := r
      simp only [Ex.simp.finish, hsf]
      simp only [Ex.simplerForm] at hsf
      cases hlo : op.literalOp? with
      | none => simp [hlo] at hsf
      | some eq =>
        cases hls : literalShape eq a b (.kid 0) (.kid 1) with
        | none => simp [hlo, hls] at hsf
        | some ls =>
          obtain ⟨l, s'⟩ := ls
          simp [hlo, hls] at hsf
          obtain ⟨-, rfl⟩ := hsf
          exact literalShape_spec op eq hlo hls ρ _ (by simpa [Pick.get] using iha.1) (by simpa [Pick.get] using ihb.1)
  | when n c d ihc ihd =>
    refine ⟨?_, by simp [Ex.kids]; exact ⟨ihc.1, ihd.1⟩⟩
    simp only [Ex.simp, Ex.simp.finish, Ex.simplerForm, Ex.withKids]
    simpa [Ex.eval] using whenV_mono n ihc.1 ihd.1
  | ite c a b ihc iha ihb =>
    refine ⟨?_, by simp [Ex.kids]; exact ⟨ihc.1, iha.1, ihb.1⟩⟩
    simp only [Ex.simp]
    cases hsf : (Ex.ite c a b).simplerForm with
    | none =>
      simp only [Ex.simp.finish, hsf, Ex.withKids]
      simpa [Ex.eval] using iteV_mono ihc.1 iha.1 ihb.1
    | some r =>
      obtain ⟨lbl, s⟩ := r
      simp only [Ex.simp.finish, hsf]
      rcases a with _ | ⟨_ | _⟩ | _ | _ | _ | _ | _ <;> rcases b with _ | ⟨_ | _⟩ | _ | _ | _ | _ | _ <;>
        simp [Ex.simplerForm] at hsf <;> obtain ⟨-, rfl⟩ := hsf <;> simp only [Ex.eval, Shape.build, Pick.get]
      · simpa using (iteV_false_true _).trans (notV_mono ihc.1)
      · simpa using (iteV_true_false _).trans ihc.1

/-- The simpler form means what the expression means: if `e` has a value,
`e.simp.1` has the same one. -/
theorem Ex.simp_eval (ρ : Nat → Val) (e : Ex) : e.eval ρ ⊑ e.simp.1.eval ρ := (simp_good ρ e).1

end Fren.Core
