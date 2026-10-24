/-!
# Rewriting expressions, proved

The rules of `nonminimal_bool` (`Reqs/Lint#simpler-bool-expressions`) and
of the lints on conditionals (`Reqs/Lint#conditionals`) over a model of
expressions (`Ex`), with a proof that the rewritten form means what the
expression means (`Ex.simp_eval`).

Each lint decides with `Ex.simplerForm`, which looks at an expression's
operands and theirs, and builds the text of the rewritten form from the
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

def BinOp.op : BinOp → String
  | .iff => "iff"
  | .or => "or"
  | .and => "and"
  | .cmp c => c.op
  | .add => "+"
  | .sub => "-"
  | .mul => "*"

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

/-- `if c then a else b`, which has a value only if both branches have
values of the same type, as the type checker requires. -/
def iteV : Option Val → Option Val → Option Val → Option Val
  | some (.bool c), some a, some b => if a.sameType b then some (if c then a else b) else none
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

/-- A lint whose rules rewrite an expression: `nonminimal_bool`
(`Reqs/Lint#simpler-bool-expressions`) and the lints on conditionals
(`Reqs/Lint#conditionals`). -/
inductive ExLint where
  | nonminimalBool
  | unlessNot
  | collapsibleWhen
  | ifNotElse
  deriving Inhabited, BEq, DecidableEq, Repr

def ExLint.all : Array ExLint := #[.nonminimalBool, .unlessNot, .collapsibleWhen, .ifNotElse]

/-- An operand of an expression, or an operand of one of its operands. -/
inductive Pick where
  | kid (i : Nat)
  | grandkid (i j : Nat)
  deriving Inhabited, Repr

/-- The rewritten form of an expression, in terms of its operands. -/
inductive Shape where
  | same (p : Pick)
  | not (a : Shape)
  | bin (op : BinOp) (a b : Shape)
  /-- `when c, d`, or `unless c, d` if `negated`. -/
  | when (negated : Bool) (c d : Shape)
  | ite (c a b : Shape)
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
  | .lit l, _ => some (l, if literalNegated equal l then .not (.same pa) else .same pa)
  | _, .lit l => some (l, if literalNegated equal l then .not (.same pb) else .same pb)
  | _, _ => none

/-- The simpler form of `e` by the rules of `nonminimal_bool`, if it has
one, and a label for the message (`Reqs/Lint#simpler-bool-expressions`). -/
def Ex.nonminimal : Ex → Option (String × Shape)
  | .bin op a b => do
    let equal ← op.literalOp?
    let (l, s) ← literalShape equal a b (.kid 0) (.kid 1)
    return (s!"comparison with `{l}`", s)
  | .not (.not _) => some ("double negation", .same (.grandkid 0 0))
  | .not (.bin (.cmp c) a b) =>
    -- The complement of a comparison with a literal is one too.
    let s := match (BinOp.cmp c.complement).literalOp? >>= fun eq => literalShape eq a b (.grandkid 0 0) (.grandkid 0 1) with
      | some (_, s) => s
      | none => .bin (.cmp c.complement) (.same (.grandkid 0 0)) (.same (.grandkid 0 1))
    some (s!"negated `{c.op}`", s)
  | .ite _ (.lit true) (.lit false) => some ("`if` that gives `true` or `false`", .same (.kid 0))
  | .ite _ (.lit false) (.lit true) => some ("`if` that gives `false` or `true`", .not (.same (.kid 0)))
  | .ite _ _ (.lit false) => some ("`if` with `else false`", .bin .and (.same (.kid 0)) (.same (.kid 1)))
  | .ite _ (.lit true) _ => some ("`if` with `then true`", .bin .or (.same (.kid 0)) (.same (.kid 2)))
  | .ite _ (.lit false) _ => some ("`if` with `then false`", .bin .and (.not (.same (.kid 0))) (.same (.kid 2)))
  | .ite _ _ (.lit true) => some ("`if` with `else true`", .bin .or (.not (.same (.kid 0))) (.same (.kid 1)))
  | _ => none

/-- The outermost operator of an operand, as the lints on conditionals see
it (`lint::Head`). -/
inductive Head where
  | not
  | unequal
  | ite
  | when
  | unless
  | other
  deriving Inhabited, DecidableEq, Repr

def Ex.head : Ex → Head
  | .not _ => .not
  | .bin op _ _ => if op = .cmp .ne then .unequal else .other
  | .ite .. => .ite
  | .when n .. => if n then .unless else .when
  | _ => .other

/-- Whether an operand is written as a negation: `not A` or `a != b`. -/
def Head.negation (h : Head) : Bool := h == .not || h == .unequal

/-- Whether `unless_not` fires on `when c, d`, or on `unless c, d` if
`negated`, from `c` (`lint::unless_not`). -/
def unlessNot (negated : Bool) (c : Head) : Bool := negated && c.negation

/-- Whether `collapsible_when` fires on `when c, d`, or on `unless c, d` if
`negated`, from `d` (`lint::collapsible_when`). -/
def collapsibleWhen (negated : Bool) (d : Head) : Bool := d == if negated then .unless else .when

/-- Whether `if_not_else` fires on `if c then a else b`, from `c` and `b`
(`lint::if_not_else`). -/
def ifNotElse (c b : Head) : Bool := c.negation && b != .ite

/-- For the condition `c`, operand 0, written as a negation: the condition
it negates. -/
def negatedCond : Ex → Option Shape
  | .not _ => some (.same (.grandkid 0 0))
  | .bin (.cmp .ne) _ _ => some (.bin (.cmp .eq) (.same (.grandkid 0 0)) (.same (.grandkid 0 1)))
  | _ => none

/-- A condition written as a negation has one it negates, so the lints on
conditionals fire exactly when `unlessNot` and `ifNotElse` say. -/
theorem negatedCond_isSome (c : Ex) (h : c.head.negation) : (negatedCond c).isSome := by
  cases c <;> simp [Ex.head, Head.negation, negatedCond] at h ⊢ <;> split at h <;> simp_all

/-- The form of `e` by the rule of `unless_not`: `unless not A, D` is
`when A, D`. -/
def Ex.unlessNotForm : Ex → Option (String × Shape)
  | .when n c _ =>
    if unlessNot n c.head then (negatedCond c).map fun s => ("negated condition", .when false s (.same (.kid 1)))
    else none
  | _ => none

/-- The form of `e` by the rule of `collapsible_when`: `when A, when B, D`
is `when A and B, D`, and `unless A, unless B, D` is `unless A or B, D`. -/
def Ex.collapsibleForm : Ex → Option (String × Shape)
  | .when n _ d =>
    if collapsibleWhen n d.head then
      some (s!"nested `{if n then "unless" else "when"}`",
        .when n (.bin (if n then .or else .and) (.same (.kid 0)) (.same (.grandkid 1 0))) (.same (.grandkid 1 1)))
    else none
  | _ => none

/-- The form of `e` by the rule of `if_not_else`: `if not C then A else B`
is `if C then B else A`. -/
def Ex.ifNotElseForm : Ex → Option (String × Shape)
  | .ite c _ b =>
    if ifNotElse c.head b.head then (negatedCond c).map fun s => ("negated condition", .ite s (.same (.kid 2)) (.same (.kid 1)))
    else none
  | _ => none

/-- The form of `e` by the rules of `l`, if they rewrite it, and a label
for the message. -/
def Ex.simplerForm (l : ExLint) (e : Ex) : Option (String × Shape) :=
  match l with
  | .nonminimalBool => e.nonminimal
  | .unlessNot => e.unlessNotForm
  | .collapsibleWhen => e.collapsibleForm
  | .ifNotElse => e.ifNotElseForm

/-- The operands of an expression. -/
def Ex.kids : Ex → List Ex
  | .atom _ | .lit _ => []
  | .not a | .neg a => [a]
  | .bin _ a b | .when _ a b => [a, b]
  | .ite c a b => [c, a, b]

/-- An operand of `e`, or of one of its operands. -/
def Ex.pick (e : Ex) : Pick → Ex
  | .kid i => e.kids.getD i (.lit false)
  | .grandkid i j => (e.kids.getD i (.lit false)).kids.getD j (.lit false)

/-- An operand, from the operands `rs`, each with its own. -/
def Pick.get (rs : Array (Ex × Array Ex)) : Pick → Ex
  | .kid i => (rs[i]?.map (·.1)).getD (.lit false)
  | .grandkid i j => ((rs[i]?.map (·.2)).getD #[])[j]?.getD (.lit false)

/-- The expression of a shape, with the operands `f` picks. -/
def Shape.build (f : Pick → Ex) : Shape → Ex
  | .same p => f p
  | .not a => .not (a.build f)
  | .bin op a b => .bin op (a.build f) (b.build f)
  | .when n c d => .when n (c.build f) (d.build f)
  | .ite c a b => .ite (c.build f) (a.build f) (b.build f)

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

/-- `e` rewritten by the rules of `l`, and its operands rewritten: the
operands first, then `e` by the rules, from what it is as written. -/
def Ex.simp (l : ExLint) : Ex → Ex × Array Ex
  | e@(.atom _) => finish e #[]
  | e@(.lit _) => finish e #[]
  | e@(.not a) => finish e #[a.simp l]
  | e@(.neg a) => finish e #[a.simp l]
  | e@(.bin _ a b) => finish e #[a.simp l, b.simp l]
  | e@(.when _ c d) => finish e #[c.simp l, d.simp l]
  | e@(.ite c a b) => finish e #[c.simp l, a.simp l, b.simp l]
where
  finish (e : Ex) (rs : Array (Ex × Array Ex)) : Ex × Array Ex :=
    let kids := rs.map (·.1)
    match e.simplerForm l with
    | some (_, s) => (s.build (·.get rs), kids)
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
  match c, a, b, hv with
  | some (.bool _), some _, some _, hv => rw [hc _ rfl, ha _ rfl, hb _ rfl]; exact hv

theorem Shape.build_mono (ρ : Nat → Val) {f g : Pick → Ex} (h : ∀ p, (f p).eval ρ ⊑ (g p).eval ρ) (s : Shape) :
    (s.build f).eval ρ ⊑ (s.build g).eval ρ := by
  induction s with
  | same p => exact h p
  | not a ih => exact notV_mono ih
  | bin op a b iha ihb => exact binV_mono op iha ihb
  | when n c d ihc ihd => exact whenV_mono n ihc ihd
  | ite c a b ihc iha ihb => exact iteV_mono ihc iha ihb

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
    (ρ : Nat → Val) (f : Pick → Ex) (ha : f pa = a) (hb : f pb = b) :
    binV op (a.eval ρ) (b.eval ρ) ⊑ (s.build f).eval ρ := by
  unfold literalShape at hs
  split at hs <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
  · obtain ⟨rfl, rfl⟩ := hs
    rename_i l
    refine (binV_lit_right op equal heq _ l).trans ?_
    cases literalNegated equal l <;> simp [Shape.build, Ex.eval, ha] <;> exact Refines.refl _
  · obtain ⟨rfl, rfl⟩ := hs
    rename_i l _
    refine (binV_lit_left op equal heq _ l).trans ?_
    cases literalNegated equal l <;> simp [Shape.build, Ex.eval, hb] <;> exact Refines.refl _

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

/-- `a != b` is `not (a = b)`. -/
theorem binV_ne (x y : Option Val) : binV (.cmp .ne) x y = notV (binV (.cmp .eq) x y) := by
  rcases x with _ | x <;> rcases y with _ | y <;> simp [binV, cmpV, notV]
  split <;> simp

/-- An `if` whose branches are `Bool` literals or its condition. -/
theorem iteV_bool (c a b : Option Val) (v : Val) (h : iteV c a b = some v) :
    ∃ x, c = some (.bool x) ∧ ∃ y, a = some y ∧ ∃ z, b = some z ∧ y.sameType z ∧ v = if x then y else z := by
  match c, a, b, h with
  | some (.bool x), some y, some z, h =>
    simp only [iteV] at h
    split at h
    · simp at h; exact ⟨x, rfl, y, rfl, z, rfl, by assumption, h.symm⟩
    · simp at h

theorem iteV_true_false (c : Option Val) : iteV c (some (.bool true)) (some (.bool false)) ⊑ c := by
  intro v hv
  obtain ⟨x, rfl, y, ha, z, hb, -, rfl⟩ := iteV_bool _ _ _ _ hv
  cases ha; cases hb; cases x <;> rfl

theorem iteV_false_true (c : Option Val) : iteV c (some (.bool false)) (some (.bool true)) ⊑ notV c := by
  intro v hv
  obtain ⟨x, rfl, y, ha, z, hb, -, rfl⟩ := iteV_bool _ _ _ _ hv
  cases ha; cases hb; cases x <;> rfl

theorem iteV_else_false (c a : Option Val) : iteV c a (some (.bool false)) ⊑ binV .and c a := by
  intro v hv
  obtain ⟨x, rfl, y, rfl, z, hb, hy, rfl⟩ := iteV_bool _ _ _ _ hv
  cases hb
  cases y <;> simp [Val.sameType] at hy; cases x <;> simp [binV]

theorem iteV_then_true (c b : Option Val) : iteV c (some (.bool true)) b ⊑ binV .or c b := by
  intro v hv
  obtain ⟨x, rfl, y, ha, z, rfl, hz, rfl⟩ := iteV_bool _ _ _ _ hv
  cases ha
  cases z <;> simp [Val.sameType] at hz; cases x <;> simp [binV]

theorem iteV_then_false (c b : Option Val) : iteV c (some (.bool false)) b ⊑ binV .and (notV c) b := by
  intro v hv
  obtain ⟨x, rfl, y, ha, z, rfl, hz, rfl⟩ := iteV_bool _ _ _ _ hv
  cases ha
  cases z <;> simp [Val.sameType] at hz; cases x <;> simp [binV, notV]

theorem iteV_else_true (c a : Option Val) : iteV c a (some (.bool true)) ⊑ binV .or (notV c) a := by
  intro v hv
  obtain ⟨x, rfl, y, rfl, z, hb, hy, rfl⟩ := iteV_bool _ _ _ _ hv
  cases hb
  cases y <;> simp [Val.sameType] at hy; cases x <;> simp [binV, notV]

theorem Val.sameType_comm (a b : Val) : a.sameType b = b.sameType a := by
  cases a <;> cases b <;> simp only [Val.sameType]
  exact Bool.beq_comm

/-- Negating the condition of `if` and swapping its branches. -/
theorem iteV_negate {c c' : Option Val} (h : c ⊑ notV c') (a b : Option Val) : iteV c a b ⊑ iteV c' b a := by
  intro v hv
  obtain ⟨x, rfl, y, rfl, z, rfl, hyz, rfl⟩ := iteV_bool _ _ _ _ hv
  have hc := h _ rfl
  match c', hc with
  | some (.bool x'), hc =>
    simp only [notV, Option.some.injEq, Val.bool.injEq] at hc
    subst hc
    rw [Val.sameType_comm] at hyz
    cases x' <;> simp [iteV, hyz]

/-- Negating the condition of `unless`, which makes it `when`. -/
theorem whenV_negate {c c' : Option Val} (h : c ⊑ notV c') (d : Option Val) : whenV true c d ⊑ whenV false c' d := by
  intro v hv
  match c, d, hv with
  | some (.bool x), some (.bool _), hv =>
    match c', h _ rfl with
    | some (.bool x'), hc => simp [notV] at hc; subst hc; simpa [whenV] using hv

/-- `when a, when b, d` is `when a and b, d`, and `unless a, unless b, d`
is `unless a or b, d`. -/
theorem whenV_collapse (n : Bool) (a b d : Option Val) :
    whenV n a (whenV n b d) ⊑ whenV n (binV (if n then .or else .and) a b) d := by
  intro v hv
  match a, b, d, hv with
  | some (.bool x), some (.bool y), some (.bool z), hv =>
    cases n <;> cases x <;> cases y <;> simpa [whenV, binV] using hv

theorem negatedCond_spec {c : Ex} {s : Shape} (h : negatedCond c = some s) (ρ : Nat → Val) (f : Pick → Ex)
    (hf : ∀ j, f (.grandkid 0 j) = c.kids.getD j (.lit false)) : c.eval ρ ⊑ notV ((s.build f).eval ρ) := by
  unfold negatedCond at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · rename_i a
    have := hf 0
    simp [Ex.kids] at this
    simp [Shape.build, Ex.eval, this]
    exact Refines.refl _
  · rename_i a b
    have h0 := hf 0
    have h1 := hf 1
    simp [Ex.kids] at h0 h1
    simp [Shape.build, Ex.eval, h0, h1, binV_ne]
    exact Refines.refl _

theorem nonminimal_sound {e : Ex} {lbl : String} {s : Shape} (h : e.nonminimal = some (lbl, s)) (ρ : Nat → Val) :
    e.eval ρ ⊑ (s.build e.pick).eval ρ := by
  unfold Ex.nonminimal at h
  split at h
  · rename_i op a b
    cases hlo : op.literalOp? with
    | none => simp [hlo] at h
    | some eq =>
      cases hls : literalShape eq a b (.kid 0) (.kid 1) with
      | none => simp [hlo, hls] at h
      | some ls =>
        obtain ⟨l, s'⟩ := ls
        simp [hlo, hls] at h
        obtain ⟨-, rfl⟩ := h
        exact literalShape_spec op eq hlo hls ρ _ rfl rfl
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact notV_notV _
  · rename_i c a b
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine (notV_cmpV c _ _).trans ?_
    split
    · rename_i s' hl
      cases hlo : (BinOp.cmp c.complement).literalOp? with
      | none => simp [hlo] at hl
      | some eq =>
        simp only [hlo, Option.bind_eq_bind, Option.bind_some] at hl
        exact literalShape_spec _ eq hlo hl ρ _ rfl rfl
    · exact Refines.refl _
  all_goals first
    | (simp at h; done)
    | obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · exact iteV_true_false _
  · exact iteV_false_true _
  · exact iteV_else_false _ _
  · exact iteV_then_true _ _
  · exact iteV_then_false _ _
  · exact iteV_else_true _ _

theorem simplerForm_sound (l : ExLint) {e : Ex} {lbl : String} {s : Shape} (h : e.simplerForm l = some (lbl, s))
    (ρ : Nat → Val) : e.eval ρ ⊑ (s.build e.pick).eval ρ := by
  cases l with
  | nonminimalBool => exact nonminimal_sound h ρ
  | unlessNot =>
    simp only [Ex.simplerForm, Ex.unlessNotForm] at h
    split at h
    · rename_i n c d
      split at h
      · rename_i hu
        simp only [unlessNot, Bool.and_eq_true] at hu
        obtain ⟨rfl, -⟩ := hu
        cases hc : negatedCond c with
        | none => simp [hc] at h
        | some s' =>
          simp [hc] at h
          obtain ⟨-, rfl⟩ := h
          exact whenV_negate (negatedCond_spec hc ρ _ fun _ => rfl) _
      · simp at h
    · simp at h
  | collapsibleWhen =>
    simp only [Ex.simplerForm, Ex.collapsibleForm] at h
    split at h
    · rename_i n c d
      split at h
      · rename_i hc
        simp at h
        obtain ⟨-, rfl⟩ := h
        cases d with
        | when n' b d' =>
          have : n' = n := by cases n <;> cases n' <;> simp_all [collapsibleWhen, Ex.head]
          subst this
          exact whenV_collapse n' _ _ _
        | _ => cases n <;> simp [collapsibleWhen, Ex.head] at hc <;> (split at hc <;> simp at hc)
      · simp at h
    · simp at h
  | ifNotElse =>
    simp only [Ex.simplerForm, Ex.ifNotElseForm] at h
    split at h
    · rename_i c a b
      split at h
      · cases hc : negatedCond c with
        | none => simp [hc] at h
        | some s' =>
          simp [hc] at h
          obtain ⟨-, rfl⟩ := h
          exact iteV_negate (negatedCond_spec hc ρ _ fun _ => rfl) _ _
      · simp at h
    · simp at h

theorem finish_snd (l : ExLint) (e : Ex) (rs : Array (Ex × Array Ex)) :
    (Ex.simp.finish l e rs).2 = rs.map (·.1) := by
  unfold Ex.simp.finish; split <;> rfl

theorem simp_eq (l : ExLint) (e : Ex) : e.simp l = Ex.simp.finish l e (e.kids.map (·.simp l)).toArray := by
  cases e <;> rfl

theorem withKids_sound (ρ : Nat → Val) (l : ExLint) (e : Ex) (hk : ∀ k ∈ e.kids, k.eval ρ ⊑ (k.simp l).1.eval ρ) :
    e.eval ρ ⊑ (e.withKids ((e.kids.map (·.simp l)).toArray.map (·.1))).eval ρ := by
  cases e <;> simp [Ex.kids, Ex.withKids, Ex.eval] at hk ⊢
  all_goals first
    | exact Refines.refl _
    | exact notV_mono hk
    | exact negV_mono hk
    | exact binV_mono _ hk.1 hk.2
    | exact whenV_mono _ hk.1 hk.2
    | exact iteV_mono hk.1 hk.2.1 hk.2.2

theorem get_refines (ρ : Nat → Val) (l : ExLint) (e : Ex) (hk : ∀ k ∈ e.kids, k.eval ρ ⊑ (k.simp l).1.eval ρ)
    (hg : ∀ k ∈ e.kids, ∀ g ∈ k.kids, g.eval ρ ⊑ (g.simp l).1.eval ρ) (p : Pick) :
    (e.pick p).eval ρ ⊑ (p.get (e.kids.map (·.simp l)).toArray).eval ρ := by
  cases p with
  | kid i =>
    simp only [Ex.pick, Pick.get, List.getD_eq_getElem?_getD, List.getElem?_toArray, List.getElem?_map]
    cases h : e.kids[i]? with
    | none => exact Refines.refl _
    | some k => exact hk k (List.mem_of_getElem? h)
  | grandkid i j =>
    simp only [Ex.pick, Pick.get, List.getD_eq_getElem?_getD, List.getElem?_toArray, List.getElem?_map]
    cases h : e.kids[i]? with
    | none => simp [Ex.kids]; exact Refines.refl _
    | some k =>
      simp only [Option.map_some, Option.getD_some, simp_eq l k, finish_snd, List.map_toArray, List.map_map,
        List.getElem?_toArray, List.getElem?_map]
      cases h' : k.kids[j]? with
      | none => exact Refines.refl _
      | some g =>
        have := hg k (List.mem_of_getElem? h) g (List.mem_of_getElem? h')
        simpa [simp_eq l g] using this

theorem simp_good (ρ : Nat → Val) (l : ExLint) (e : Ex) :
    e.eval ρ ⊑ (e.simp l).1.eval ρ ∧ ∀ k ∈ e.kids, k.eval ρ ⊑ (k.simp l).1.eval ρ := by
  have main (e : Ex) (ih : ∀ k ∈ e.kids, k.eval ρ ⊑ (k.simp l).1.eval ρ ∧ ∀ g ∈ k.kids, g.eval ρ ⊑ (g.simp l).1.eval ρ) :
      e.eval ρ ⊑ (e.simp l).1.eval ρ ∧ ∀ k ∈ e.kids, k.eval ρ ⊑ (k.simp l).1.eval ρ := by
    have hk k h := (ih k h).1
    refine ⟨?_, hk⟩
    rw [simp_eq]
    unfold Ex.simp.finish
    split
    · rename_i lbl s h
      exact (simplerForm_sound l h ρ).trans (Shape.build_mono ρ (get_refines ρ l e hk fun k h => (ih k h).2) s)
    · exact withKids_sound ρ l e hk
  induction e with
  | atom | lit => exact main _ (by simp [Ex.kids])
  | not a ih | neg a ih => exact main _ (by simpa [Ex.kids] using ih)
  | bin _ a b iha ihb | when _ a b iha ihb => exact main _ (by simp [Ex.kids]; exact ⟨iha, ihb⟩)
  | ite c a b ihc iha ihb => exact main _ (by simp [Ex.kids]; exact ⟨ihc, iha, ihb⟩)

/-- The rewritten form means what the expression means: if `e` has a
value, `(e.simp l).1` has the same one. -/
theorem Ex.simp_eval (ρ : Nat → Val) (l : ExLint) (e : Ex) : e.eval ρ ⊑ (e.simp l).1.eval ρ := (simp_good ρ l e).1

end Fren.Core
