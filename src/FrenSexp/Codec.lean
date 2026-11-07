module

public import FrenSexp.Text

public section

namespace Fren

class ToSexp (α : Type u) where
  toSexp : α → Sexp

class FromSexp (α : Type u) where
  fromSexp : Sexp → Except Sexp.DecodeError α

export ToSexp (toSexp)
export FromSexp (fromSexp)

namespace Sexp

universe u v
variable {α : Type u} {κ : Type u} {ν : Type v}

def expected (description : String) : Except DecodeError α :=
  .error { expected := description }

/-- Prefix a child index to a decoding failure's path. -/
def atChild (index : Nat) (result : Except DecodeError α) : Except DecodeError α :=
  result.mapError fun e => { e with path := index :: e.path }

def encode [ToSexp α] (value : α) : String := render (toSexp value)

/-- Both syntax and type errors use actual text coordinates. A codec's error
path selects the offending child, including inside arrays and maps. -/
def decode [FromSexp α] (text : String) : Except ParseError α :=
  match parseLocated text with
  | .error e => .error e
  | .ok parsed => (fromSexp parsed.value).mapError fun e =>
      { position := parsed.locations.at e.path, expected := e.expected }

instance : ToSexp Sexp := ⟨id⟩
instance : FromSexp Sexp := ⟨pure⟩

instance : ToSexp Unit := ⟨fun _ => symbol "unit"⟩
instance : FromSexp Unit where
  fromSexp
    | .atom a => if a.val == "unit" then pure () else expected "unit"
    | _ => expected "unit"

instance : ToSexp Nat := ⟨fun n => symbol (toString n)⟩
instance : FromSexp Nat where
  fromSexp
    | .atom a =>
      if a.val.all Char.isDigit then
        match a.val.toNat? with
        | some n => pure n
        | none => expected "a natural numeral"
      else expected "a natural numeral"
    | _ => expected "a natural numeral"

instance : ToSexp Int := ⟨fun n => symbol (toString n)⟩
instance : FromSexp Int where
  fromSexp
    | .atom a =>
      let digits := if a.val.startsWith "-" then (a.val.drop 1).toString else a.val
      if !digits.isEmpty && digits.all Char.isDigit then
        match a.val.toInt? with
        | some n => pure n
        | none => expected "an integer numeral"
      else expected "an integer numeral"
    | _ => expected "an integer numeral"

instance : ToSexp Bool := ⟨fun b => symbol (if b then "true" else "false")⟩
instance : FromSexp Bool where
  fromSexp
    | .atom a => match a.val with
      | "true" => pure true
      | "false" => pure false
      | _ => expected "true or false"
    | _ => expected "true or false"

instance : ToSexp String := ⟨Sexp.string⟩
instance : FromSexp String where
  fromSexp
    | .string s => pure s
    | _ => expected "a string"

instance [ToSexp α] : ToSexp (Option α) where
  toSexp
    | none => symbol "none"
    | some x => .list #[symbol "some", toSexp x]

instance [FromSexp α] : FromSexp (Option α) where
  fromSexp
    | .atom a => if a.val == "none" then pure none else expected "none or (some value)"
    | .list #[.atom a, x] =>
      if a.val == "some" then some <$> atChild 1 (fromSexp x)
      else atChild 0 (expected "some")
    | _ => expected "none or (some value)"

instance [ToSexp α] : ToSexp (Array α) := ⟨fun xs => .list (xs.map toSexp)⟩
instance [FromSexp α] : FromSexp (Array α) where
  fromSexp
    | .list xs => xs.mapIdxM fun i x => atChild i (fromSexp x)
    | _ => expected "a list of array elements"

/-- Compare UTF-8 bytes, without locale or rendered-width collation. -/
def byteLess (a b : String) : Bool := Id.run do
  let a := a.toUTF8
  let b := b.toUTF8
  for i in [:min a.size b.size] do
    if a[i]! != b[i]! then return a[i]! < b[i]!
  return a.size < b.size

instance [BEq κ] [Hashable κ] [ToSexp κ] [ToSexp ν] :
    ToSexp (Std.HashMap κ ν) where
  toSexp map := Id.run do
    let entries := map.toArray.map fun (key, value) =>
      let k := toSexp key
      let v := toSexp value
      (render k, render v, Sexp.list #[k, v])
    let entries := entries.qsort fun a b =>
      byteLess a.1 b.1 || (a.1 == b.1 && byteLess a.2.1 b.2.1)
    return .list (entries.map (·.2.2))

instance [BEq κ] [Hashable κ] [FromSexp κ] [FromSexp ν] :
    FromSexp (Std.HashMap κ ν) where
  fromSexp
    | .list entries => do
      let mut map : Std.HashMap κ ν := Std.HashMap.emptyWithCapacity
      for i in [:entries.size] do
        let pair : Except DecodeError (κ × ν) :=
          match entries[i]! with
          | .list #[key, value] =>
            match atChild 0 (fromSexp (α := κ) key) with
            | .error e => .error e
            | .ok key =>
              if map.contains key then atChild 0 (expected "a unique map key")
              else match atChild 1 (fromSexp (α := ν) value) with
                | .error e => .error e
                | .ok value => .ok (key, value)
          | _ => expected "a (key value) pair"
        let (key, value) ← atChild i pair
        map := map.insert key value
      return map
    | _ => expected "a list of (key value) pairs"

end Sexp
end Fren
