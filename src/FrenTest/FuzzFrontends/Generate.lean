-- keep-sorted start
import FrenTest.FuzzDatatypeElements
import FrenTest.FuzzFrontends.Confirmed
import FrenTest.FuzzFrontends.Decidable
import FrenTest.FuzzFrontends.Enumeration
import FrenTest.FuzzFrontends.FactScopes
import FrenTest.FuzzFrontends.InductionCandidates
import FrenTest.FuzzFrontends.InductionForms
import FrenTest.FuzzFrontends.Keywords
import FrenTest.FuzzFrontends.Mode
import FrenTest.FuzzFrontends.Scrutinees
import FrenTest.FuzzFrontends.SetCard
import FrenTest.FuzzFrontends.SetCardFallback
import FrenTest.FuzzFrontends.Unfoldings
import FrenTest.FuzzFrontends.Wide
import FrenTest.FuzzGenericFunctions
import FrenTest.FuzzRecursion
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends

/-- The generator of `--keywords`' following item (`Wide.genKeywordsTail`),
split off the seed, so that its draws leave `genKeywords`' unchanged. -/
def tailRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6b77⟩

/-- The generator of `--keywords`' grammar errors (`Wide.genKeywordsGrammar`),
split off the seed too. -/
def grammarRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6772⟩

/-- The generator of `--keywords`' item of each kind (`Wide.genKeywordsItem`),
split off the seed too. -/
def itemRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6974⟩

/-- The generator of `--induction-candidates` (`Wide.inductionCandidates`),
split off the seed so that its draws leave the other modes unchanged. -/
def inductionRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x6963⟩

/-- The generator of `--unfoldings` (`Wide.unfoldings`), split off the
seed so that its draws leave the other modes unchanged. -/
def unfoldingRngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0x756e⟩

def Mode.spec (m : Mode) (seed : Nat) : String :=
  if m.confirmArguments then Id.run (Wide.genConfirmedArguments.run' (rngOf seed))
  else if m.genericFunctions then Id.run (FuzzGenericFunctions.spec.run' (rngOf seed))
  else if m.setCardFallback then Id.run (Wide.genSetCardFallback.run' (rngOf seed))
  else if m.setCard then Id.run (Wide.genSetCard.run' (rngOf seed))
  else if m.enumerationObligations || m.enumerationRelations then
    Id.run ((Wide.enumerationObligations m.enumerationRelations).run' (rngOf seed))
  else if m.keywords then
    let block := Id.run (Wide.genKeywords.run' (rngOf seed))
    let spec := Id.run ((Wide.genKeywordsGrammar block).run' (grammarRngOf seed)) ++
      Id.run ((Wide.genKeywordsTail block).run' (tailRngOf seed))
    -- The item of `Wide.genKeywordsItem` after the declarations that
    -- `genKeywords` writes first.
    let decls := "pub proc spec(x: Int): (v: Int) { ensure e: v = x }\n"
    match spec.splitOn decls with
    | [before, after] => before ++ decls ++ Id.run (Wide.genKeywordsItem.run' (itemRngOf seed)) ++ after
    | _ => spec
  else if m.inductionCandidates then Id.run (Wide.inductionCandidates.run' (inductionRngOf seed))
  else if m.unfoldings then Id.run (Wide.unfoldings.run' (unfoldingRngOf seed))
  else
    Id.run ((if m.decidable then Wide.genDecidable
      else if m.inductionForms then Wide.inductionForms else if m.inductions then Wide.inductions
      else if m.scrutinees then Wide.duplicateScrutineeGroup
      else if m.factScopes then Wide.factScopes else if m.confirm || m.confirmMatches then Wide.genConfirmed m.confirmMatches
      else if m.sites then Wide.genSites else if m.guards then Wide.genGuards
      else if m.datatypeElements then FuzzDatatypeElements.spec
      else if m.recursionPositions then FuzzRecursion.gen
      else Wide.genWide m.avoidKnown).run' (rngOf seed))

/-- The cuts of the spec of `seed` (`Wide.genWideCuts`), each shorter than
the next; `--confirm` keeps the prefix before `Wide.confirmedSorts`;
`--confirm-matches` also keeps the entire original confirmation spec;
`--confirm-arguments` keeps main's prefix before its ignored-argument tail.
none for `--guards`, `--sites`, `--inductions`, `--induction-forms`,
`--keywords` and `--recursion-positions`. The empty prefix of
`--scrutinees`, `--fact-scopes`, `--induction-candidates`, `--decidable`,
`--enumeration-obligations`, `--unfoldings`, `--datatype-elements`,
`--generic-functions`, `--set-card` and `--set-card-fallback` makes any
static error a group error: these generators, like appended groups,
promise to add none.
`--enumeration-relations` keeps the original enumeration spec as its
prefix, so its additional cases must add no static error either. -/
def Mode.cuts (m : Mode) (seed : Nat) : Array String :=
  if m.confirmArguments then #[Id.run (Wide.genConfirmedPrefix.run' (rngOf seed))] else
  if m.genericFunctions then #[""] else
  if m.enumerationRelations then #[Id.run ((Wide.enumerationObligationCases false).run' (rngOf seed))] else
  if (m.confirm || m.confirmMatches) && !m.setCard && !m.setCardFallback && !m.decidable && !m.enumerationObligations && !m.unfoldings then
    let base := Id.run (Wide.genConfirmedBase.run' (rngOf seed))
    if m.confirmMatches then #[base, Id.run ((Wide.genConfirmed false).run' (rngOf seed))] else #[base]
  else if m.setCard || m.setCardFallback || m.scrutinees || m.factScopes || m.inductionCandidates || m.decidable || m.enumerationObligations || m.unfoldings || m.datatypeElements then #[""] else if m.guards || m.sites || m.inductions || m.inductionForms || m.keywords || m.recursionPositions then #[] else
    (Id.run ((Wide.genWideCuts m.avoidKnown).run' (rngOf seed))).2

-- The selected generator and its static-error check use the same priority.
#guard ({ genericFunctions := true, enumerationRelations := true } : Mode).cuts 0 == #[""]

end FrenTest.FuzzFrontends
