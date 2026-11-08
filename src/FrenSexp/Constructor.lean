module

public import FrenSexp.Codec

public section

namespace Fren.Sexp

/-- Read a type-directed constructor tag. Lists point tag errors at child zero. -/
def readConstructorTag : Sexp → Except DecodeError String
  | .atom tag => pure tag.val
  | .list xs => match xs[0]? with
    | some (Sexp.atom tag) => pure tag.val
    | _ => atChild 0 (expected "a constructor tag")
  | _ => expected "a constructor tag"

/-- Unknown list tags point to the head; unknown bare tags point to the atom. -/
def unknownConstructor (value : Sexp) (tags : String) : Except DecodeError α :=
  let error := expected ("a constructor tag: " ++ tags)
  match value with
  | .list _ => atChild 0 error
  | _ => error

/-- The caller has selected the tag. Nullary constructors require a bare atom;
payload constructors require exactly their declared number of fields. Returned
arrays retain the tag at index zero, so field error paths use wire indices. -/
def readConstructorFields (value : Sexp) (tag : String) (arity : Nat) :
    Except DecodeError (Array Sexp) :=
  match value with
  | .atom a =>
    if arity == 0 && a.val == tag then pure #[]
    else expected s!"{tag} with exactly {arity} fields"
  | .list xs =>
    if arity == 0 then expected ("the bare constructor tag " ++ tag)
    else if xs.size == arity + 1 then
      match xs[0]? with
      | some (Sexp.atom a) =>
        if a.val == tag then pure xs else atChild 0 (expected tag)
      | _ => atChild 0 (expected tag)
    else expected s!"{tag} with exactly {arity} fields"
  | _ => expected ("the constructor " ++ tag)

end Fren.Sexp
