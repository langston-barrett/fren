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

/-- When a member is elaborated, which orders the messages about the
members (`lang::trait_member_phase`): the methods first, then the laws,
then the expectations, each in the order written. A member of another kind
is reported, and no other member is. -/
def TraitMember.phase : TraitMember → Nat
  | .method => 0
  | .law => 1
  | .expectation => 2
  | _ => 3

/-- The positions of the members `ms`, in the order in which both front
ends elaborate them (`TraitMember.phase`). -/
def traitOrder (ms : Array TraitMember) : Array Nat :=
  #[0, 1, 2].flatMap fun p => (Array.range ms.size).filter fun i => (ms[i]!).phase == p

/-- What the checks of an expectation, or of a law, see of how they are
asked (`lang::CheckFlags`): whether every construct is in the decidable
core, whether `undecidable` is an error in it, and whether its queries set
`fmf-bound`. -/
structure CheckFlags where
  inCore : Bool := true
  denied : Bool := false
  fmfBound : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- An expectation's flags with those of one law of its trait among its
hypotheses (`lang::law_flags`). Its queries set `fmf-bound` where its own
constructs or a law's do. -/
def CheckFlags.withLaw (e law : CheckFlags) : CheckFlags :=
  { inCore := e.inCore && law.inCore, denied := e.denied || law.denied, fmfBound := e.fmfBound || law.fmfBound }

/-- An expectation's flags with those of every law of its trait. -/
def CheckFlags.withLaws (e : CheckFlags) (laws : Array CheckFlags) : CheckFlags := laws.foldl CheckFlags.withLaw e

/-- Whether an expectation of a trait accepts its evidence setting
(`lang::trait_expectation_evidence`): its checks are the solver's, so
neither testing nor enumeration. -/
def traitEvidenceAccepted (tested enumerated : Bool) : Bool := !tested && !enumerated

/-- `fren.evidence` set to testing or enumeration, `value`, for an
expectation of a trait (`F0215`): its checks are the solver's, since an
interpretation that testing or enumeration picks need not meet the laws. -/
def traitEvidenceMsg (value : String) : Msg :=
  let m := itemEvidenceMsg "an expectation of a trait" value
  { m with notes := #["note: an interpretation that testing or enumeration picks need not meet the trait's laws"] ++ m.notes }

/-- The error of an expectation of a trait whose checks are set to testing
or enumeration (`traitEvidenceAccepted`), if they are. -/
def traitEvidenceMsg? (tested enumerated : Bool) : Option Msg :=
  if traitEvidenceAccepted tested enumerated then none
  else some (traitEvidenceMsg (if tested then "random" else "enumerated"))

/-- A setting of `option` to `value`, as written, before a law, which has
no checks of its own to set (`F0215`): `fren.evidence` or
`fren.enumeration.size`. Lint settings are accepted. -/
def lawSettingMsg? (option value : String) : Option Msg :=
  if option == "fren.evidence" || option == "fren.enumeration.size" then
    some { code? := some "F0215", headline := s!"`{option}` cannot be set to `{value}` for a law"
           label? := some "a law has no checks of its own"
           notes := #["note: a law is a hypothesis of its trait's expectations, whose checks the setting would set",
             "help: set it before an expectation instead"] }
  else none

/-- The first of the settings before a law, outermost first, each its
option and its value as written, that a law does not take
(`lawSettingMsg?`), by its position, with its message. Both front ends
check the whole list, before any setting is in effect. -/
def lawSettingsMsg? (settings : List (String × String)) : Option (Nat × Msg) :=
  (settings.zipIdx.findSome? fun ((o, v), k) => (lawSettingMsg? o v).map (k, ·))

/-- A member of a trait, or its carrier, declared again. -/
def dupTraitMemberMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"`{n}` is defined multiple times in this trait", label? := some "defined again here"
    notes := #["note: a trait's carrier `Self`, methods, laws and expectations share one namespace"] }

end Fren.Core
