module

public import FrenSexp
meta import FrenSexp

namespace Fren.SexpTests

open Sexp

private inductive Mode where
  | toBV | ofNat2 | ABC
  deriving BEq, Repr, ToSexp, FromSexp

private inductive Packet (α : Type u) where
  | empty
  | one (value : α)
  | header (count : Nat) (label : String) (enabled : Bool)
  deriving BEq, Repr, ToSexp, FromSexp

private structure ParseHeader (α : Type u) (β : Type v) where
  label : String
  values : Array α
  extra : Option β
  marker : Unit
  deriving BEq, Repr, ToSexp, FromSexp

/-- Elaboration contracts for the actual generated declarations. Universe
parameters remain arbitrary and independent; these are instance conformance
checks, not roundtrip proofs for arbitrary supplied field codecs. -/
example {α : Type u} [ToSexp α] : ToSexp (Packet α) := inferInstance
example {α : Type u} [FromSexp α] : FromSexp (Packet α) := inferInstance
example {α : Type u} {β : Type v} [ToSexp α] [ToSexp β] :
    ToSexp (ParseHeader α β) := inferInstance
example {α : Type u} {β : Type v} [FromSexp α] [FromSexp β] :
    FromSexp (ParseHeader α β) := inferInstance

-- Test-only lawful field codecs. Explicit Except operations preserve the lift's
-- universe; the Nat codec independently determines its wire representation.
private instance : ToSexp (ULift.{u} Nat) := ⟨fun n => toSexp n.down⟩
private instance : FromSexp (ULift.{u} Nat) :=
  ⟨fun value => Except.map ULift.up (fromSexp (α := Nat) value)⟩

private def universeTests : Except String Unit :=
  let value : Packet (ULift.{1} Nat) := .one ⟨37⟩
  if encode value != "(one 37)" then .error "higher-universe constructor wire"
  else match fromSexp (α := Packet (ULift.{1} Nat)) (toSexp value),
      decode (α := Packet (ULift.{1} Nat)) "(one 37)" with
  | .ok (.one direct), .ok (.one parsed) =>
    if direct.down != 37 || parsed.down != 37 then .error "higher-universe constructor roundtrip"
    else
      -- Independent Type-1 and Type-2 fields, mixed with Type-0 String/Unit.
      let record : ParseHeader (ULift.{1} Nat) (ULift.{2} Nat) :=
        ⟨"higher", #[⟨11⟩, ⟨29⟩], some ⟨53⟩, ()⟩
      let text := "(parse_header \"higher\" (11 29) (some 53) unit)"
      if encode record != text then .error "higher-universe record wire"
      else match fromSexp (α := ParseHeader (ULift.{1} Nat) (ULift.{2} Nat)) (toSexp record),
          decode (α := ParseHeader (ULift.{1} Nat) (ULift.{2} Nat)) text with
      | .ok direct, .ok parsed =>
        if direct.values.map (·.down) != #[11, 29] ||
            parsed.values.map (·.down) != #[11, 29] ||
            direct.extra.map (·.down) != some 53 || parsed.extra.map (·.down) != some 53 ||
            direct.label != "higher" || parsed.label != "higher" then
          .error "higher-universe record roundtrip"
        else match decode (α := Packet (ULift.{1} Nat)) "(one nope)",
            decode (α := ParseHeader (ULift.{1} Nat) (ULift.{2} Nat))
              "(parse_header \"higher\" (11 29) (some nope) unit)" with
        | .error ctorError, .error recordError =>
          if ctorError.expected == "a natural numeral" &&
              ctorError.position == { byteOffset := 5, column := 6 } &&
              recordError.expected == "a natural numeral" &&
              recordError.position == { byteOffset := 37, column := 38 } then
            match decode (α := Packet (ULift.{1} Nat)) "empty",
                decode (α := Packet (ULift.{1} Nat)) "(header 8 \"label\" true)" with
            | .ok .empty, .ok (.header 8 "label" true) => .ok ()
            | _, _ => .error "higher-universe nullary/Type-0 payload branch"
          else .error "higher-universe malformed field location"
        | _, _ => .error "accepted higher-universe malformed field"
      | _, _ => .error "higher-universe record parse"
  | _, _ => .error "higher-universe constructor parse"

private structure EmptyPacket where
  deriving BEq, Repr, ToSexp, FromSexp

private structure NamedCounts where
  counts : Std.HashMap Lean.Name Nat
  mode : Mode
  deriving ToSexp, FromSexp

private inductive EncodeOnly where
  | value (n : Nat)
  deriving ToSexp

private inductive DecodeOnly where
  | value (n : Nat)
  deriving FromSexp

private inductive Collision where
  | fooBar | foo_bar

/-- error: S-expression constructor tag collision: foo_bar -/
#guard_msgs in
deriving instance ToSexp for Collision

/-- error: S-expression constructor tag collision: foo_bar -/
#guard_msgs in
deriving instance FromSexp for Collision

private structure FunctionField where
  value : Nat → Nat

/-- error: S-expression deriving: unsupported function field 1 of Fren.SexpTests.FunctionField.mk -/
#guard_msgs in
deriving instance ToSexp for FunctionField

/-- error: S-expression deriving: unsupported function field 1 of Fren.SexpTests.FunctionField.mk -/
#guard_msgs in
deriving instance FromSexp for FunctionField

private inductive Recursive where
  | leaf | next (child : Recursive)

/-- error: S-expression deriving supports only nonrecursive, nonmutual types without indices -/
#guard_msgs in
deriving instance FromSexp for Recursive

private inductive Indexed : Nat → Type where
  | zero : Indexed 0

/-- error: S-expression deriving supports only nonrecursive, nonmutual types without indices -/
#guard_msgs in
deriving instance ToSexp for Indexed

private structure ValueParameter (n : Nat) where
  value : Fin n

deriving instance ToSexp, FromSexp for ValueParameter

-- This exact former rejection now requires only the field codec, not a codec
-- for the uniform Nat value n itself.
example {n : Nat} [ToSexp (Fin n)] : ToSexp (ValueParameter n) := inferInstance
example {n : Nat} [FromSexp (Fin n)] : FromSexp (ValueParameter n) := inferInstance

private structure DependentField where
  count : Nat
  value : Fin count

/-- error: S-expression deriving: unsupported dependent field 2 of Fren.SexpTests.DependentField.mk -/
#guard_msgs in
deriving instance FromSexp for DependentField

/-- error: S-expression deriving: unsupported dependent field 2 of Fren.SexpTests.DependentField.mk -/
#guard_msgs in
deriving instance ToSexp for DependentField

private structure ProofField where
  valid : True

/-- error: S-expression deriving: unsupported proof field 1 of Fren.SexpTests.ProofField.mk -/
#guard_msgs in
deriving instance ToSexp for ProofField

private structure HigherKinded (f : Type → Type) where
  value : f Nat

/-- error: S-expression deriving: unsupported higher-kinded or proof parameter -/
#guard_msgs in
deriving instance ToSexp for HigherKinded

/-- error: S-expression deriving: unsupported higher-kinded or proof parameter -/
#guard_msgs in
deriving instance FromSexp for HigherKinded

private structure ProofParameter (h : True) where
  value : Nat

/-- error: S-expression deriving: unsupported higher-kinded or proof parameter -/
#guard_msgs in
deriving instance ToSexp for ProofParameter

/-- error: S-expression deriving: unsupported higher-kinded or proof parameter -/
#guard_msgs in
deriving instance FromSexp for ProofParameter

private inductive Nested where
  | node (children : Array Nested)

/-- error: S-expression deriving supports only nonrecursive, nonmutual types without indices -/
#guard_msgs in
deriving instance FromSexp for Nested

mutual
  private inductive First where
    | second (value : Second)
  private inductive Second where
    | first (value : First)
end

/-- error: S-expression deriving supports only nonrecursive, nonmutual types without indices -/
#guard_msgs in
deriving instance ToSexp for First

private inductive ImplicitPayload where
  | value {count : Nat} (label : String)
  deriving BEq, ToSexp, FromSexp

private def ensure (ok : Bool) (message : String) : Except String Unit :=
  if ok then pure () else .error message

private def roundTrip [ToSexp α] [FromSexp α] [BEq α] (value : α) : Except String Unit := do
  let text := encode value
  match fromSexp (toSexp value), decode (α := α) text with
  | .ok direct, .ok parsed => ensure (direct == value && parsed == value) s!"roundtrip: {text}"
  | _, _ => .error s!"roundtrip failed: {text}"

private def rejects [FromSexp α] (_ : α → α) (text : String) : Except String Unit :=
  match decode (α := α) text with
  | .ok _ => .error s!"accepted malformed input: {text}"
  | .error _ => pure ()

private def derivationTests : Except String Unit := do
  for mode in [Mode.toBV, .ofNat2, .ABC] do roundTrip mode
  ensure (encode Mode.toBV == "to_bv" && encode Mode.ofNat2 == "of_nat2" &&
    encode Mode.ABC == "abc") "canonical constructor tags"
  ensure (encode (Packet.empty : Packet Nat) == "empty") "bare nullary constructor"
  ensure (encode (Packet.one () : Packet Unit) == "(one unit)") "Unit payload remains present"
  roundTrip (Packet.one true)
  roundTrip (Packet.one "true")
  rejects (id : Packet Bool → Packet Bool) "(one 1)"
  ensure (encode (Packet.header 2 "é" true : Packet Nat) == "(header 2 \"é\" true)")
    "payload declaration order"
  ensure (encode (EmptyPacket.mk) == "empty_packet") "nullary structure type tag"
  roundTrip EmptyPacket.mk
  let implicitValue := ImplicitPayload.value (count := 4) "label"
  roundTrip implicitValue
  ensure (encode implicitValue == "(value 4 \"label\")") "implicit constructor field order"
  for n in [:40] do
    roundTrip (Packet.empty : Packet Nat)
    roundTrip (Packet.one n)
    roundTrip (Packet.one (some #[n, n + 1]))
    roundTrip (Packet.header n s!"label {n}" (n % 2 == 0) : Packet String)
    let record : ParseHeader Nat (Packet String) :=
      ⟨s!"header {n}", #[n, n + 1], some (.one "payload"), ()⟩
    roundTrip record
    roundTrip ({ record with values := #[], extra := none } : ParseHeader Nat (Packet String))
  let record : ParseHeader Nat (Packet String) := ⟨"x", #[1, 2], some (.one "y"), ()⟩
  ensure (encode record == "(parse_header \"x\" (1 2) (some (one \"y\")) unit)")
    "structure type tag and field order"
  ensure (encode (EncodeOnly.value 3) == "(value 3)") "ToSexp alone"
  match decode (α := DecodeOnly) "(value 3)" with
  | .ok (.value 3) => pure ()
  | _ => .error "FromSexp alone"
  let map : NamedCounts := ⟨Std.HashMap.ofArray #[( `a, 1), (`b, 2)], .toBV⟩
  ensure (encode map == "(named_counts ((a 1) (b 2)) to_bv)") "existing Name/map codecs"
  match decode (α := NamedCounts) (encode map) with
  | .ok parsed => ensure (parsed.counts.size == 2 && parsed.counts[`a]? == some 1 &&
      parsed.counts[`b]? == some 2 && parsed.mode == .toBV) "derived map roundtrip"
  | .error _ => .error "derived map parse"
  for text in ["(empty)", "(empty 1)", "one", "(one)", "(one 1 2)", "(one true)",
      "(header 1 \"x\")", "(header 1 \"x\" true 0)", "(header \"1\" \"x\" true)",
      "(header 1 x true)", "(header 1 \"x\" 1)", "other", "(other 1)", "()",
      "(\"one\" 1)", "\"empty\""] do
    rejects (id : Packet Nat → Packet Nat) text
  for text in ["mk", "(mk)", "(empty_packet)", "(empty_packet 1)"] do
    rejects (id : EmptyPacket → EmptyPacket) text
  for text in ["parse_header", "(parse_header \"x\" () none)",
      "(parse_header \"x\" () none unit 1)", "(mk \"x\" () none unit)"] do
    rejects (id : ParseHeader Nat String → ParseHeader Nat String) text
  let malformed := "(parse_header\n \"é\" (1 nope) none unit)"
  match parse malformed with
  | .error _ => .error "malformed typed fixture should be syntactically valid"
  | .ok sexp =>
    match fromSexp (α := ParseHeader Nat String) sexp with
    | .error e =>
      ensure (e.path == [2, 1] && e.expected == "a natural numeral")
        "derived array child error path"
    | .ok _ => .error "accepted bad derived array field"
  match decode (α := ParseHeader Nat String) malformed with
  | .error e => ensure (e.position == { byteOffset := 23, line := 2, column := 9 } &&
      e.expected == "a natural numeral") s!"positioned derived child: {repr e}"
  | .ok _ => .error "accepted bad positioned field"
  match decode (α := Packet Nat) "(other 1)" with
  | .error e => ensure (e.position == { byteOffset := 1, column := 2 } &&
      e.expected == "a constructor tag: empty, one, header") "unknown tag position/choices"
  | .ok _ => .error "accepted unknown tag"
  match decode (α := ParseHeader Nat (Packet Nat))
      "(parse_header \"x\" () (some (one nope)) unit)" with
  | .error e => ensure (e.position == { byteOffset := 32, column := 33 } &&
      e.expected == "a natural numeral") s!"nested derived child position: {repr e}"
  | .ok _ => .error "accepted bad nested derived payload"

/-- Finite executable contracts, run at build time and by the compiled Fren2 driver.
These checks are tests of the actual derived instances, not universal proofs. -/
public def runDerive : IO Unit := do
  match derivationTests *> universeTests with
  | .ok () => IO.println "S-expression deriving tests passed"
  | .error e => throw (IO.userError e)

#eval runDerive

end Fren.SexpTests
