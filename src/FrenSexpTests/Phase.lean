module

public import FrenSexp
meta import FrenSexp

namespace Fren.SexpTests.Phase

open Sexp

-- There are deliberately no codecs for Phase itself.
private inductive Phase where
  | raw | checked

private structure Stamp where
  number : Nat
  deriving BEq, ToSexp, FromSexp

-- Reducible, so ordinary Lean instance search computes Ann at concrete phases.
private abbrev Ann : Phase → Type
  | .raw => Unit
  | .checked => Stamp

-- A single nonrecursive layer: R is a child value, never a recursive knot.
private inductive Layer (p : Phase) (R : Type u) where
  | empty
  | lit (value : Nat) (annotation : Ann p)
  | link (child : R) (children : Array R) (extra : Option R) (annotation : Ann p)
  deriving ToSexp, FromSexp

private instance [BEq R] [BEq (Ann p)] : BEq (Layer p R) where
  beq
    | .empty, .empty => true
    | .lit n a, .lit m b => n == m && a == b
    | .link r rs x a, .link s ss y b => r == s && rs == ss && x == y && a == b
    | _, _ => false

private structure PhasePair (p : Phase) (α : Type u) (β : Type v) where
  left : α
  right : Option β
  annotation : Ann p
  deriving ToSexp, FromSexp

-- Universes of the supplied fields stay arbitrary and independent. These are
-- elaboration contracts, not roundtrip claims about arbitrary supplied codecs.
example {p : Phase} {R : Type u} [ToSexp R] [ToSexp (Ann p)] :
    ToSexp (Layer p R) := inferInstance
example {p : Phase} {R : Type u} [FromSexp R] [FromSexp (Ann p)] :
    FromSexp (Layer p R) := inferInstance
example {p : Phase} {α : Type u} {β : Type v}
    [ToSexp α] [ToSexp β] [ToSexp (Ann p)] : ToSexp (PhasePair p α β) := inferInstance
example {p : Phase} {α : Type u} {β : Type v}
    [FromSexp α] [FromSexp β] [FromSexp (Ann p)] : FromSexp (PhasePair p α β) := inferInstance
-- Supplying the codecs of the actual fields is sufficient even without a
-- codec for the type parameter β itself.
example {p : Phase} {α : Type u} {β : Type v}
    [ToSexp α] [ToSexp (Option β)] [ToSexp (Ann p)] :
    ToSexp (PhasePair p α β) := inferInstance
example {p : Phase} {α : Type u} {β : Type v}
    [FromSexp α] [FromSexp (Option β)] [FromSexp (Ann p)] :
    FromSexp (PhasePair p α β) := inferInstance
example : ToSexp (Layer .raw Nat) := inferInstance
example : FromSexp (Layer .checked String) := inferInstance

private structure Phantom (p : Phase) where
  value : Nat
  deriving ToSexp, FromSexp

example {p : Phase} : ToSexp (Phantom p) := inferInstance
example {p : Phase} : FromSexp (Phantom p) := inferInstance

-- Hidden uniform parameters, including those in a computed field type, must
-- remain tied to the target's p when the instance binders are generated.
private abbrev HiddenAnn {p : Phase} := Ann p

private structure Hidden {p : Phase} (R : Type u) where
  child : R
  annotation : HiddenAnn (p := p)
  deriving ToSexp, FromSexp

example {p : Phase} {R : Type u} [ToSexp R] [ToSexp (Ann p)] :
    ToSexp (Hidden (p := p) R) := inferInstance
example {p : Phase} {R : Type u} [FromSexp R] [FromSexp (Ann p)] :
    FromSexp (Hidden (p := p) R) := inferInstance
example : ToSexp (Hidden (p := .raw) Nat) := inferInstance
example : FromSexp (Hidden (p := .checked) Nat) := inferInstance

-- A uniform parameter is not a constructor-refined phase index.
private inductive Refined : Phase → Type where
  | raw : Refined .raw
  | checked (n : Nat) : Refined .checked

/-- error: S-expression deriving supports only nonrecursive, nonmutual types without indices -/
#guard_msgs in
deriving instance ToSexp for Refined

/-- error: S-expression deriving supports only nonrecursive, nonmutual types without indices -/
#guard_msgs in
deriving instance FromSexp for Refined

private def ensure (ok : Bool) (message : String) : Except String Unit :=
  if ok then .ok () else .error message

private def fixture [ToSexp α] [FromSexp α] [BEq α] (value : α) (text : String) :
    Except String Unit := do
  ensure (encode value == text) s!"phase canonical wire: {text}"
  match fromSexp (toSexp value), decode (α := α) text with
  | .ok direct, .ok parsed =>
    ensure (direct == value && parsed == value) s!"phase roundtrip: {text}"
  | _, _ => .error s!"phase parse: {text}"

-- Check the semantic path and the text position separately against literals.
private def bad [FromSexp α] (_ : α → α) (text : String) (path : List Nat)
    (position : Position) (expected : String) : Except String Unit := do
  match parse text with
  | .error _ => .error "phase malformed fixture is not syntactically valid"
  | .ok sexp =>
    match fromSexp (α := α) sexp with
    | .error e =>
      ensure (e.path == path && e.expected == expected) s!"phase semantic error: {repr e}"
    | .ok _ => .error s!"phase accepted: {text}"
  match decode (α := α) text with
  | .error e =>
    ensure (e.position == position && e.expected == expected) s!"phase positioned error: {repr e}"
  | .ok _ => .error s!"phase accepted positioned: {text}"

-- A field may mention an earlier field syntactically without depending on it.
-- The generated constraints must erase n while keeping α and its universe free.
private abbrev Drop (_n : Nat) (α : Type u) := α

private structure ErasedDependency (α : Type u) where
  n : Nat
  data : Drop n α
  deriving BEq, ToSexp, FromSexp

example {α : Type u} [ToSexp α] : ToSexp (ErasedDependency α) := inferInstance
example {α : Type u} [FromSexp α] : FromSexp (ErasedDependency α) := inferInstance

-- Dropping a field dependency must stop before unfolding the uniform phase
-- family. This retains the ordinary supplied-field-codec conformance contract.
private structure ErasedPhase (p : Phase) (α : Type u) (β : Type v) where
  n : Nat
  data : Drop n α
  extra : Drop n (Drop n (Option β))
  annotation : Drop n (Ann p)
  deriving ToSexp, FromSexp

example {p : Phase} {α : Type u} {β : Type v}
    [ToSexp α] [ToSexp β] [ToSexp (Ann p)] : ToSexp (ErasedPhase p α β) := inferInstance
example {p : Phase} {α : Type u} {β : Type v}
    [FromSexp α] [FromSexp β] [FromSexp (Ann p)] : FromSexp (ErasedPhase p α β) := inferInstance

private def tests : Except String Unit := do
  fixture (Layer.empty : Layer .raw Nat) "empty"
  fixture (Layer.empty : Layer .checked Nat) "empty"
  fixture (Layer.lit 7 () : Layer .raw Nat) "(lit 7 unit)"
  fixture (Layer.lit 7 ⟨9⟩ : Layer .checked Nat) "(lit 7 (stamp 9))"
  fixture (Layer.link 1 #[2, 3] (some 4) () : Layer .raw Nat)
    "(link 1 (2 3) (some 4) unit)"
  fixture (Layer.link 1 #[2, 3] (some 4) ⟨9⟩ : Layer .checked Nat)
    "(link 1 (2 3) (some 4) (stamp 9))"
  fixture (Layer.link "é" #[] none () : Layer .raw String)
    "(link \"é\" () none unit)"
  fixture (Layer.link "é" #[] none ⟨0⟩ : Layer .checked String)
    "(link \"é\" () none (stamp 0))"
  let hiddenRaw : Hidden (p := .raw) Nat := ⟨6, ()⟩
  let hiddenChecked : Hidden (p := .checked) Nat := ⟨6, ⟨8⟩⟩
  ensure (encode hiddenRaw == "(hidden 6 unit)" &&
    encode hiddenChecked == "(hidden 6 (stamp 8))") "hidden phase wire"
  match fromSexp (α := Hidden (p := .raw) Nat) (toSexp hiddenRaw),
      decode (α := Hidden (p := .raw) Nat) "(hidden 6 unit)" with
  | .ok direct, .ok parsed =>
    ensure (direct.child == 6 && parsed.child == 6) "hidden raw roundtrip"
  | _, _ => .error "hidden raw parse"
  match fromSexp (α := Hidden (p := .checked) Nat) (toSexp hiddenChecked),
      decode (α := Hidden (p := .checked) Nat) "(hidden 6 (stamp 8))" with
  | .ok direct, .ok parsed =>
    ensure (direct.child == 6 && parsed.child == 6 &&
      direct.annotation.number == 8 && parsed.annotation.number == 8) "hidden checked roundtrip"
  | _, _ => .error "hidden checked parse"
  -- Each finite case uses lawful Unit/Stamp/Nat codecs and an independent wire.
  for n in [:24] do
    fixture (Layer.link n #[n + 1] none () : Layer .raw Nat)
      s!"(link {n} ({n + 1}) none unit)"
    fixture (Layer.link n #[n + 1] none ⟨n + 2⟩ : Layer .checked Nat)
      s!"(link {n} ({n + 1}) none (stamp {n + 2}))"
  bad (id : Layer .raw Nat → _) "(lit 7 (stamp 9))" [2]
    { byteOffset := 7, column := 8 } "unit"
  bad (id : Layer .checked Nat → _) "(lit 7 unit)" [2]
    { byteOffset := 7, column := 8 } "a constructor tag: stamp"
  bad (id : Layer .raw Nat → _) "(lit 7)" [] {} "lit with exactly 2 fields"
  bad (id : Layer .checked Nat → _) "(lit 7 (stamp 9) unit)" [] {}
    "lit with exactly 2 fields"
  bad (id : Layer .raw Nat → _) "(other 7 unit)" [0]
    { byteOffset := 1, column := 2 } "a constructor tag: empty, lit, link"
  bad (id : Layer .checked Nat → _) "(other 7 (stamp 9))" [0]
    { byteOffset := 1, column := 2 } "a constructor tag: empty, lit, link"
  bad (id : Layer .checked Nat → _) "(link 1 (2 nope) none (stamp 9))" [2, 1]
    { byteOffset := 11, column := 12 } "a natural numeral"
  bad (id : Layer .raw Nat → _) "(link 1 () (some nope) unit)" [3, 1]
    { byteOffset := 17, column := 18 } "a natural numeral"
  bad (id : Layer .checked String → _) "(link \"é\" () none\n (stamp nope))" [4, 1]
    { byteOffset := 27, line := 2, column := 9 } "a natural numeral"

/-- Lawful test codecs in two higher universes, mixed with computed Type-0 Ann. -/
private structure Elevated : Type (u + 1) where
  number : Nat
  deriving ToSexp, FromSexp

private def universeTests : Except String Unit := do
  let raw : PhasePair .raw Elevated.{0} Elevated.{1} := ⟨⟨11⟩, some ⟨29⟩, ()⟩
  let checked : PhasePair .checked Elevated.{0} Elevated.{1} := ⟨⟨11⟩, some ⟨29⟩, ⟨53⟩⟩
  ensure (encode raw == "(phase_pair (elevated 11) (some (elevated 29)) unit)")
    "raw independent universe wire"
  ensure (encode checked == "(phase_pair (elevated 11) (some (elevated 29)) (stamp 53))")
    "checked independent universe wire"
  for input in [toSexp raw, (← parse (encode raw) |>.mapError toString)] do
    match fromSexp (α := PhasePair .raw Elevated.{0} Elevated.{1}) input with
    | .ok x =>
      ensure (x.left.number == 11 && x.right.map (·.number) == some 29)
        "raw independent universe roundtrip"
    | .error _ => .error "raw independent universe decode"
  for input in [toSexp checked, (← parse (encode checked) |>.mapError toString)] do
    match fromSexp (α := PhasePair .checked Elevated.{0} Elevated.{1}) input with
    | .ok x => ensure (x.left.number == 11 && x.right.map (·.number) == some 29 &&
        x.annotation.number == 53) "checked independent universe roundtrip"
    | .error _ => .error "checked independent universe decode"

private def erasedPhaseFixture {p : Phase} [ToSexp (Ann p)] [FromSexp (Ann p)]
    [BEq (Ann p)] (annotation : Ann p) (text : String) : Except String Unit := do
  let value : ErasedPhase p Elevated.{0} Elevated.{1} :=
    ⟨3, ⟨7⟩, some ⟨11⟩, annotation⟩
  ensure (encode value == text) "erased phase independent universe wire"
  match fromSexp (α := ErasedPhase p Elevated.{0} Elevated.{1}) (toSexp value),
      decode (α := ErasedPhase p Elevated.{0} Elevated.{1}) text with
  | .ok direct, .ok parsed =>
    for x in [direct, parsed] do
      ensure (x.n == 3 && x.data.number == 7 && x.extra.map (·.number) == some 11 &&
        x.annotation == annotation) "erased phase roundtrip fields"
  | _, _ => .error "erased phase parse"

private def erasedTests : Except String Unit := do
  fixture (ErasedDependency.mk 3 7) "(erased_dependency 3 7)"
  erasedPhaseFixture (p := .raw) ()
    "(erased_phase 3 (elevated 7) (some (elevated 11)) unit)"
  erasedPhaseFixture (p := .checked) ⟨13⟩
    "(erased_phase 3 (elevated 7) (some (elevated 11)) (stamp 13))"
  bad (id : ErasedDependency Nat → _) "(erased_dependency 3 nope)" [2]
    { byteOffset := 21, column := 22 } "a natural numeral"
  bad (id : ErasedDependency Nat → _) "(erased_dependency 3)" [] {}
    "erased_dependency with exactly 2 fields"
  bad (id : ErasedPhase .raw Nat Bool → _) "(erased_phase 3 7 (some true) (stamp 13))" [4]
    { byteOffset := 30, column := 31 } "unit"
  bad (id : ErasedPhase .checked Nat Bool → _) "(erased_phase 3 7 (some true) unit)" [4]
    { byteOffset := 30, column := 31 } "a constructor tag: stamp"

public def run : IO Unit := do
  match tests *> universeTests *> erasedTests with
  | .ok () => IO.println "S-expression phase deriving tests passed"
  | .error e => throw (IO.userError e)

#eval run

end Fren.SexpTests.Phase
