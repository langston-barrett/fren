-- keep-sorted start
import Lean
-- keep-sorted end

open Lean

namespace FrenTest.FuzzFrontends

/-- The generator modes selected by command-line flags. Each specialized
mode generates specs of the constructs described by its field; otherwise
`Wide.genWide` generates a mix, optionally avoiding known differences. -/
structure Mode where
  avoidKnown : Bool := false
  guards : Bool := false
  /-- Specs of `Wide.sitesProc`s alone (`Wide.genSites`). -/
  sites : Bool := false
  /-- Specs of what the confirmation of models evaluates
  (`Wide.genConfirmed`). -/
  confirm : Bool := false
  /-- Multi-scrutinee lints alone (`Wide.duplicateScrutineeGroup`). -/
  scrutinees : Bool := false
  /-- Specs of global expectations over recursive enumerations alone
  (`Wide.inductions`). -/
  inductions : Bool := false
  /-- Specs of the forms in which the front ends read a candidate for
  induction (`Wide.inductionForms`). -/
  inductionForms : Bool := false
  /-- Specs of a clause written with the other block's keyword
  (`Wide.genKeywords`). -/
  keywords : Bool := false
  /-- Query-local transitive fact closure (`Wide.factScopes`). -/
  factScopes : Bool := false
  /-- Specs of induction-candidate types, argument forms and comparisons
  (`Wide.inductionCandidates`). -/
  inductionCandidates : Bool := false
  /-- Procedures in the decidable core of strings, sets, relations and sequences. -/
  decidable : Bool := false
  /-- Specs of call-input obligations with two named parts, predicate leaves
  with inherited evidence and whole-predicate check locations
  (`Wide.enumerationObligations`). -/
  enumerationObligations : Bool := false
  /-- Append nested relation cases after the original enumeration cases. -/
  enumerationRelations : Bool := false
  /-- Specs of claims that induction proves only by unfolding more than
  one step (`Wide.unfoldings`). -/
  unfoldings : Bool := false
  /-- Collection payloads and fields of generic datatypes. -/
  datatypeElements : Bool := false
  /-- Type arguments and whole generic function instances. -/
  genericFunctions : Bool := false
  /-- Finite set cardinalities and #820's regression seeds. -/
  setCard : Bool := false
  /-- Cardinalities beyond the expansion bound or of unlisted types. -/
  setCardFallback : Bool := false
  /-- Singleton structural-group clients, including isolated invalid uses. -/
  recursionPositions : Bool := false
  /-- Simultaneous structural groups of two or three functions. -/
  mutualGroups : Bool := false
  deriving BEq

def Mode.args (m : Mode) : Array String :=
  (if m.avoidKnown then #["--avoid-known"] else #[]) ++ (if m.guards then #["--guards"] else #[]) ++
    (if m.sites then #["--sites"] else #[]) ++ (if m.confirm then #["--confirm"] else #[]) ++
    (if m.scrutinees then #["--scrutinees"] else #[]) ++
    (if m.inductions then #["--inductions"] else #[]) ++ (if m.inductionForms then #["--induction-forms"] else #[]) ++
    (if m.keywords then #["--keywords"] else #[]) ++
    (if m.factScopes then #["--fact-scopes"] else #[]) ++
    (if m.inductionCandidates then #["--induction-candidates"] else #[]) ++
    (if m.decidable then #["--decidable"] else #[]) ++
    (if m.enumerationObligations then #["--enumeration-obligations"] else #[]) ++
    (if m.enumerationRelations then #["--enumeration-relations"] else #[]) ++
    (if m.unfoldings then #["--unfoldings"] else #[]) ++
    (if m.datatypeElements then #["--datatype-elements"] else #[]) ++
    (if m.genericFunctions then #["--generic-functions"] else #[]) ++
    (if m.setCard then #["--set-card"] else #[]) ++
    (if m.setCardFallback then #["--set-card-fallback"] else #[]) ++
    (if m.recursionPositions then #["--recursion-positions"] else #[]) ++
    (if m.mutualGroups then #["--mutual-groups"] else #[])

def flags (m : Mode) : String := String.join (m.args.toList.map (" " ++ ·))

/-- The mode of the flags `args`, if they are only flags of a mode. -/
def Mode.ofArgs? (args : List String) : Option Mode :=
  if args.all (· ∈ ["--avoid-known", "--guards", "--sites", "--confirm", "--scrutinees", "--inductions", "--induction-forms",
      "--keywords", "--fact-scopes", "--induction-candidates", "--decidable", "--enumeration-obligations", "--enumeration-relations", "--unfoldings", "--datatype-elements", "--generic-functions", "--set-card", "--set-card-fallback", "--recursion-positions", "--mutual-groups"]) then
    some { avoidKnown := args.contains "--avoid-known", guards := args.contains "--guards", sites := args.contains "--sites",
           confirm := args.contains "--confirm", scrutinees := args.contains "--scrutinees"
           inductions := args.contains "--inductions", inductionForms := args.contains "--induction-forms"
           keywords := args.contains "--keywords", factScopes := args.contains "--fact-scopes"
           inductionCandidates := args.contains "--induction-candidates"
           decidable := args.contains "--decidable"
           enumerationObligations := args.contains "--enumeration-obligations"
           enumerationRelations := args.contains "--enumeration-relations"
           unfoldings := args.contains "--unfoldings", datatypeElements := args.contains "--datatype-elements"
           genericFunctions := args.contains "--generic-functions"
           setCard := args.contains "--set-card", setCardFallback := args.contains "--set-card-fallback", recursionPositions := args.contains "--recursion-positions", mutualGroups := args.contains "--mutual-groups" }
  else none

/-- The mode as Lean writes it in `knownDifferences`. -/
def Mode.lean (m : Mode) : String :=
  let fields := (if m.avoidKnown then ["avoidKnown := true"] else []) ++ (if m.guards then ["guards := true"] else []) ++
    (if m.sites then ["sites := true"] else []) ++ (if m.confirm then ["confirm := true"] else []) ++
    (if m.scrutinees then ["scrutinees := true"] else []) ++
    (if m.inductions then ["inductions := true"] else []) ++ (if m.inductionForms then ["inductionForms := true"] else []) ++
    (if m.keywords then ["keywords := true"] else []) ++
    (if m.factScopes then ["factScopes := true"] else []) ++
    (if m.inductionCandidates then ["inductionCandidates := true"] else []) ++
    (if m.decidable then ["decidable := true"] else []) ++
    (if m.enumerationObligations then ["enumerationObligations := true"] else []) ++
    (if m.enumerationRelations then ["enumerationRelations := true"] else []) ++
    (if m.unfoldings then ["unfoldings := true"] else []) ++
    (if m.datatypeElements then ["datatypeElements := true"] else []) ++
    (if m.genericFunctions then ["genericFunctions := true"] else []) ++
    (if m.setCard then ["setCard := true"] else []) ++
    (if m.setCardFallback then ["setCardFallback := true"] else []) ++
    (if m.recursionPositions then ["recursionPositions := true"] else []) ++
    (if m.mutualGroups then ["mutualGroups := true"] else [])
  if fields.isEmpty then "{}" else "{ " ++ ", ".intercalate fields ++ " }"

end FrenTest.FuzzFrontends
