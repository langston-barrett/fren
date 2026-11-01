-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Evidence
import FrenCore.Names
-- keep-sorted end

/-!
# Traits (`Reqs/Lang/Traits`)

What both front ends share of a trait: the name of its carrier, which
members it accepts (`lang::trait_member`), and their messages. Each front
end elaborates a trait's methods as uninterpreted functions, its carrier
as an abstract type, and its expectations as global expectations whose
checks have the trait's laws among their hypotheses (`Comp.laws`).
-/

namespace Fren.Core

open Lean (Name)

/-- The name of a trait's carrier within it. -/
def selfName : Name := `Self

/-- What a member of a trait is, as written (`lang::MemberKind`). -/
inductive TraitMember where
  /-- An uninterpreted function: a method. -/
  | method
  | law
  /-- A global expectation, in either form. -/
  | expectation
  /-- A function with a body, which would be a default method. -/
  | definedFunction
  /-- Any other item, which `what` describes, as "procedures". -/
  | other (what : String)
  deriving Inhabited, BEq, Repr

/-- Whether a trait accepts a member (`lang::trait_member`): a method, a
law or an expectation, written without `pub` and without `use`s in its
block; a method also without type parameters. -/
def traitMemberAccepted (m : TraitMember) (isPub generic uses : Bool) : Bool :=
  (m matches .method | .law | .expectation) && !isPub && !generic && !uses

/-- Why a trait does not accept a member, if it does not
(`lang::trait_member`), with the message of the error `F0222`. -/
def traitMemberMsg? (trait : Name) (m : TraitMember) (isPub generic uses : Bool) : Option Msg :=
  if traitMemberAccepted m isPub generic uses then none
  else
    let note := "note: a trait has methods, which are functions without a body, laws and expectations"
    let t := showPath trait
    some <| match m with
    | .definedFunction =>
      { code? := some "F0222", headline := s!"a method of trait `{t}` has no body, for now"
        label? := some "a function with a body"
        notes := #[note, "note: default methods are not part of Fren yet"] }
    | .other what =>
      { code? := some "F0222", headline := s!"a trait has no {what}", label? := some "not a member of a trait"
        notes := #[note, "help: declare it outside the trait"] }
    | _ =>
      if isPub then
        { code? := some "F0222", headline := s!"a member of trait `{t}` is not written `pub`"
          label? := some "`pub` here"
          notes := #["note: a trait's members are visible where the trait is"] }
      else if generic then
        { code? := some "F0222", headline := s!"a method of trait `{t}` has no type parameters, for now"
          label? := some "type parameters"
          notes := #[note] }
      else
        { code? := some "F0222", headline := s!"a member of trait `{t}` has no `use`, for now"
          label? := some "a `use` in a member's block"
          notes := #["note: a member's block sees the trait's names and its module's",
            "help: write the `use` in the module, before the trait"] }

/-- `fren.evidence` set to testing or enumeration, `value`, for an
expectation of a trait (`F0215`): its checks are the solver's, since an
interpretation that testing or enumeration picks need not meet the laws. -/
def traitEvidenceMsg (value : String) : Msg :=
  let m := itemEvidenceMsg "an expectation of a trait" value
  { m with notes := #["note: an interpretation that testing or enumeration picks need not meet the trait's laws"] ++ m.notes }

/-- A member of a trait, or its carrier, declared again. -/
def dupTraitMemberMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"`{n}` is defined multiple times in this trait", label? := some "defined again here"
    notes := #["note: a trait's carrier `Self`, methods, laws and expectations share one namespace"] }

end Fren.Core
